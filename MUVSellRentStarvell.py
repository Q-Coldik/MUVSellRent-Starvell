"""
MUVSell Rent (Starvell) — плагин Starvell Cardinal: перепродажа аренды и оффлайн-активации Steam-аккаунтов
с muvsell.store на Starvell.

Один лот на игру в Steam → «Аккаунты с играми» → «Аренда», 1 шт = 1 час. Покупатель оплачивает N штук → плагин
арендует аккаунт на MUVSell на N часов через API (списывает ваш баланс MUVSell по цене сайта) и присылает логин
и пароль в чат заказа. Код Steam Guard — по команде !код. Разница цен — ваш заработок.
Оффлайн-игры — лот на игру в «Аккаунты с играми» → «Продажа»: 1 шт = игра навсегда на общем аккаунте MUVSell.

Установка: положите файл в папку plugins/ Starvell Cardinal (или загрузите через «🧩 Плагины») и перезапустите бота.
Меню плагина — команда /muvsell. API-ключ: muvsell.store → Профиль → API.
"""
from __future__ import annotations

import asyncio
import functools
import hashlib
import html
import http.client
import io
import json
import logging
import math
import os
import re
import shutil
import threading
import time
import urllib.error
import urllib.request
from datetime import datetime, timedelta, timezone

from aiogram import F
from aiogram.filters import Command, StateFilter
from aiogram.fsm.context import FSMContext
from aiogram.fsm.state import State, StatesGroup
from aiogram.types import CallbackQuery, InlineKeyboardButton, InlineKeyboardMarkup, Message

try:
    from aiogram.types import LinkPreviewOptions
    _NOPREV = {"link_preview_options": LinkPreviewOptions(is_disabled=True)}
except ImportError:  # aiogram < 3.3
    _NOPREV = {"disable_web_page_preview": True}

# NAME / VERSION / DESCRIPTION / CHANGELOG / COMPAT — по одной строке: их читает сайт (/api/plugins)
NAME = "MUVSell Rent (Starvell)"
VERSION = "0.1.0"
DESCRIPTION = "Перепродажа аренды и оффлайн-активации Steam-аккаунтов MUVSell на Starvell: аренда — лот на игру в «Аккаунты с играми» → «Аренда» (1 шт = 1 час), оффлайн-игры навсегда — в «Продажа»; автовыдача, коды Steam Guard, продления, автовыставление, лот аренды выключается, пока нет свободных аккаунтов, цены, статистика."
CHANGELOG = "Первая версия для Starvell Cardinal: аренда — лоты в Steam → «Аккаунты с играми» → «Аренда», один на игру, 1 шт = 1 час (цена часа = цена MUVSell × (1 + наценка)); оффлайн-активация — лоты в «Аккаунты с играми» → «Продажа», игра навсегда на общем аккаунте, 1 шт = 1 аккаунт (до 10 за заказ), !офлайн и коды Steam Guard; картинка игры в лоте; автовыдача; лот аренды выключается, пока на MUVSell нет свободных аккаунтов, и включается сам (оффлайн-лоты всегда в продаже); новые игры MUVSell выставляются сами; дубли удаляются; !код, !время, !данные, !помощь, !продление, !кик, !пароль; пересчёт цен, бонус за отзыв, возврат завершает аренду, автовозврат, статистика и прибыль."
COMPAT = "Starvell Cardinal 0.3.25"
AUTHOR = "@MUVSell"
UUID = "0d54ae12-1362-4d4c-96b2-738e2f5c4768"
SETTINGS_PAGE = False

SITE = "https://muvsell.store"
MIRROR = "https://cold-band-9582.manimanimanimani4444.workers.dev"  # Cloudflare Worker → SITE (только /api и /downloads)
API_BASE = SITE + "/api/v1"
SELF_URL = SITE + "/downloads/MUVSellRentStarvell.py"

# Starvell: Steam (игра 16) → «Аккаунты с играми» (213) → «Аренда» (796); фильтры категории «Регион» и «Уровень»
SV_SITE = "https://starvell.com"
SV_API = SV_SITE + "/api"
CAT_ID, SUB_ID, SALE_SUB = 213, 796, 795   # «Аренда» — аренда по часам, «Продажа» — оффлайн-активация навсегда
METHOD_FILTER = "6dd29bda-d05e-4c2e-ad34-23841422df58"  # «Способ получения» (обязателен в «Продаже»)
METHOD_FULL = "e979aa19-05af-4c41-a50c-d08ae071ee82"    # «Полный доступ» — входят по логину и паролю
OFF_MAX_QTY = 10       # оффлайн-лот: больше стольких аккаунтов за один заказ не выдаём (остаток лота такой же)
REGION_FILTER = "deff758c-583e-41af-b60c-3fc8a13c4bab"
REGIONS = {"other": ("a85ec0dc-281c-4f86-8a81-ae2bb20b26ee", "Другой регион"),
           "ru": ("1655b1d8-1d5c-4a13-8064-4bdd3628acf7", "Россия"),
           "kz": ("d10bd3bb-06e0-4d4a-9aae-9a34b3db6d08", "Казахстан")}
LEVEL_FILTER = "99c56500-3ad7-4e19-93af-cda50bb5366b"
TITLE_MAX, DESC_MAX = 100, 2500
REVIEW_MIN_RUB = 25    # отзыв на Starvell можно оставить к заказу от 25 ₽ (minPriceForReviewEnabled)

MAX_HOURS = 720        # одна аренда или продление на MUVSell
TIMEOUT = 25
SV_DELAY = 0.7         # пауза между запросами к Starvell — QRATOR не любит частые
CREATE_DELAY = 3.0     # пауза между созданием лотов
RELIST_WAIT = 5        # через столько секунд после продажи лот пополняется (Starvell уменьшил остаток)
UPDATE_EVERY = 1800
RESYNC_EVERY = 600
ORDER_CHECK_SEC = 600  # статус заказа активной аренды (возврат, отзыв) — не чаще
MISSED_SEC = 6 * 3600  # заказ, оплаченный при выключенном боте, выдаётся при запуске, если ему не больше стольких сек
TAG_RX = re.compile(r"\brentS-(\d+)\b")

log = logging.getLogger("Plugins.MUVSellRent")
DATA_DIR = os.path.join("storage", "plugins", UUID)
SELF_PATH = os.path.abspath(__file__)
esc = html.escape
PREFIX = "[MUVSell Rent]"

TEXTS = {  # сообщения покупателю в чат заказа
    "delivery": ("🎮 {game} — аккаунт готов!\n\n"
                 "👤 Логин: {login}\n🔑 Пароль: {password}\n"
                 "⏳ Срок: {hours} ч. — до {expires}\n\n"
                 "🔐 Код Steam Guard — {guard}\n⌛ Сколько осталось — !время\n📋 Все команды — !помощь\n\n"
                 "🔄 Продлить этот же аккаунт: напишите {word}, затем купите нужное число часов этой игры.\n"
                 "🛒 Без {word} новая покупка выдаст другой аккаунт. Хорошей игры! 🎯"),
    "extended": ("✅ Готово! Аренда {game} продлена на {hours} ч.\n"
                 "👤 Аккаунт тот же: {login} — вход без изменений.\n🕒 Играйте до {expires}"),
    "ext_offer": ("🔄 Продление {login} — {game}\n\n"
                  "В течение {minutes} мин. купите нужное число часов (1 шт = 1 час) — время добавится к этому же "
                  "аккаунту:\n{links}"),
    "ext_none": "😔 Сейчас лот {game} снят с продажи — продавец уже в курсе и поможет с продлением.",
    "review_offer": ("🎁 Небольшой подарок: подтвердите заказ и оставьте отзыв на {stars}★ — "
                     "и мы бесплатно добавим {bonus} ч. к аренде, пока она идёт."),
    "review_bonus": "💚 Спасибо за отзыв! Аренда {login} продлена на {hours} ч. в подарок.\n🕒 Играйте до {expires}",
    "kick_ok": ("🚪 Готово — все чужие сессии на {login} закрываются (обычно до минуты).\n"
                "Аренда {game} идёт дальше, просто войдите заново."),
    "kick_fail": "⚠️ Не получилось завершить сессии {login}: {reason}",
    "pass_wait": "🔑 Меняю пароль на {login}… Новый пришлю сюда через 1–3 минуты.",
    "pass_ok": ("🔐 Пароль обновлён!\n\n🎮 {game}\n👤 Логин: {login}\n🔑 Новый пароль: {password}\n\n"
                "Срок аренды не изменился. Код Steam Guard — {guard}"),
    "pass_fail": "⚠️ Сменить пароль {login} не удалось: {reason}",
    "code": "🔐 Код Steam Guard для {login}: {code}\n⏱ Действует ещё ~{ttl} сек. — вводите сразу.",
    "code_which": "👥 У вас несколько аккаунтов — уточните логин: {cmd} логин\n{logins}",
    "code_fail": "⚠️ Код сейчас не получить — продавец уже в курсе и поможет вручную.",
    "time_left": "⌛ {game} ({login}): осталось {left} — до {expires}",
    "creds": "👤 {game}\nЛогин: {login}\nПароль: {password}\n🕒 До {expires}",
    "help": "📋 Команды для вашей аренды:\n{commands}",
    "warn": ("⏳ Аренда {game} ({login}) закончится через {left} ({expires}).\n"
             "Продлить этот же аккаунт: напишите {word}."),
    "ended": ("🏁 Аренда {game} ({login}) завершена — доступ к аккаунту закрыт.\n"
              "Спасибо, что были с нами! Понравилось — будем рады отзыву 💚"),
    "no_rental": "🔎 Не вижу у вас активной аренды. Если только что оплатили — подождите минуту и повторите.",
    "problem": "⚠️ Автовыдача не сработала — продавец уже получил уведомление и скоро всё выдаст вручную. Спасибо за терпение!",
    "off_delivery": ("💿 {game} — игра навсегда, аккаунт готов!\n\n"
                     "👤 Логин: {login}\n🔑 Пароль: {password}\n\n"
                     "Как играть:\n1️⃣ Войдите в Steam с этими данными. Код Steam Guard — {guard} {login}\n"
                     "2️⃣ Установите {game} и один раз запустите её.\n"
                     "3️⃣ Steam → «Перейти в автономный режим» — и играйте оффлайн сколько угодно.\n\n"
                     "⚠️ Аккаунт общий: не меняйте пароль, почту и настройки и не выходите из автономного режима без "
                     "нужды.\n📋 Данные ещё раз — !офлайн"),
    "off_creds": "💿 {game}\nЛогин: {login}\nПароль: {password}\nКод Steam Guard — {guard} {login}",
    "off_none": "🔎 Не вижу у вас оффлайн-игр. Если только что оплатили — подождите минуту и повторите.",
    "off_code_limit": "⏳ Код для {login} сейчас не выдать: {reason}",
    "off_no_guard": "🔓 Для {login} код Steam Guard не нужен — входите только по логину и паролю.",
}
TEXTS_EN = {
    "delivery": ("🎮 {game} — your account is ready!\n\n"
                 "👤 Login: {login}\n🔑 Password: {password}\n"
                 "⏳ Time: {hours} h — until {expires}\n\n"
                 "🔐 Steam Guard code — {guard}\n⌛ Time left — !time\n📋 All commands — !help\n\n"
                 "🔄 To extend this account: type {word}, then buy the hours you need for this game.\n"
                 "🛒 Without {word} a new purchase gives you a different account. Have fun! 🎯"),
    "extended": ("✅ Done! Your {game} rental is extended by {hours} h.\n"
                 "👤 Same account: {login} — log in as before.\n🕒 Play until {expires}"),
    "ext_offer": ("🔄 Extending {login} — {game}\n\n"
                  "Within {minutes} min buy the hours you need (1 pc = 1 hour) and the time is added to this same "
                  "account:\n{links}"),
    "ext_none": "😔 The {game} offer is not on sale right now — the seller has been notified and will help.",
    "review_offer": ("🎁 A small gift: confirm the order and leave a {stars}★ review — we'll add {bonus} h to your "
                     "rental for free while it's active."),
    "review_bonus": "💚 Thanks for the review! Your {login} rental is extended by {hours} h as a gift.\n🕒 Play until {expires}",
    "kick_ok": ("🚪 Done — all other sessions on {login} are being closed (usually within a minute).\n"
                "Your {game} rental continues, just log in again."),
    "kick_fail": "⚠️ Couldn't end the sessions on {login}. Please try again later or contact the seller.",
    "pass_wait": "🔑 Changing the password on {login}… I'll send the new one here in 1–3 minutes.",
    "pass_ok": ("🔐 Password updated!\n\n🎮 {game}\n👤 Login: {login}\n🔑 New password: {password}\n\n"
                "Your rental time hasn't changed. Steam Guard code — {guard}"),
    "pass_fail": "⚠️ Couldn't change the password on {login}. The seller has been notified and will help.",
    "code": "🔐 Steam Guard code for {login}: {code}\n⏱ Valid for ~{ttl} more sec. — enter it right away.",
    "code_which": "👥 You have several accounts — please add the login: {cmd} login\n{logins}",
    "code_fail": "⚠️ Can't get the code right now — the seller has been notified and will help manually.",
    "time_left": "⌛ {game} ({login}): {left} left — until {expires}",
    "creds": "👤 {game}\nLogin: {login}\nPassword: {password}\n🕒 Until {expires}",
    "help": "📋 Commands for your rental:\n{commands}",
    "warn": "⏳ Your {game} rental ({login}) ends in {left} ({expires}).\nTo extend this account, type {word}.",
    "ended": ("🏁 Your {game} rental ({login}) has ended — access to the account is closed.\n"
              "Thanks for choosing us! If you enjoyed it, we'd love a review 💚"),
    "no_rental": "🔎 I don't see an active rental for you. If you've just paid, wait a minute and try again.",
    "problem": "⚠️ Auto-delivery failed — the seller has been notified and will deliver manually soon. Thanks for your patience!",
    "off_delivery": ("💿 {game} — lifetime game, your account is ready!\n\n"
                     "👤 Login: {login}\n🔑 Password: {password}\n\n"
                     "How to play:\n1️⃣ Log in to Steam with these details. Steam Guard code — {guard} {login}\n"
                     "2️⃣ Install {game} and launch it once.\n"
                     "3️⃣ Steam → \"Go Offline\" — then play offline as long as you like.\n\n"
                     "⚠️ The account is shared: don't change the password, email or settings, and don't leave offline mode "
                     "unless you need to.\n📋 Details again — !offline"),
    "off_creds": "💿 {game}\nLogin: {login}\nPassword: {password}\nSteam Guard code — {guard} {login}",
    "off_none": "🔎 I don't see any offline games for you. If you've just paid, wait a minute and try again.",
    "off_code_limit": "⏳ Can't give a code for {login} right now: the daily code limit is reached. Please try later.",
    "off_no_guard": "🔓 {login} doesn't need a Steam Guard code — just log in with the login and password.",
}
ITEM_TEXTS = {  # шаблоны лотов: {game} — игра, {commands} — команды, {guard}, {word}
    "title": "{game} | Аренда Steam | 1 шт = 1 час | Автовыдача ⚡",
    "desc": ("🎮 Лицензионный Steam-аккаунт {game} в аренду.\n"
             "⏱ 1 шт = 1 час: сколько штук купите — на столько часов и аренда (24 шт = сутки).\n"
             "⚡ Логин и пароль придут в чат заказа сами, сразу после оплаты — круглосуточно.\n"
             "🔐 Код Steam Guard — командой {guard} в чате.\n\n"
             "📋 Команды в чате заказа:\n{commands}\n\n"
             "🔄 Продлить тот же аккаунт: напишите {word} в чате, потом купите нужное число часов этой игры — время "
             "добавится к нему. Без {word} новая покупка выдаст другой аккаунт.\n"
             "⏳ Когда срок выйдет, доступ закроется автоматически."),
    "off_title": "{game} | Steam оффлайн-активация | Навсегда | Автовыдача ⚡",
    "off_desc": ("💿 {game} навсегда — оффлайн-активация на общем Steam-аккаунте.\n"
                 "⚡ Логин и пароль придут в чат заказа сами, сразу после оплаты — круглосуточно.\n\n"
                 "Как играть:\n1️⃣ Войдите в Steam с полученными данными. Код Steam Guard — командой {guard} в чате.\n"
                 "2️⃣ Установите игру и один раз запустите её.\n"
                 "3️⃣ Steam → «Перейти в автономный режим» — и играйте оффлайн без ограничений по времени.\n\n"
                 "⚠️ Аккаунт общий, без почты: не меняйте пароль, почту и настройки. Онлайн-режим и мультиплеер "
                 "не гарантируются — только одиночная игра в автономном режиме.\n"
                 "📋 Данные ещё раз — команда !офлайн в чате заказа."),
}

NOTIFY_CATS = {
    "sales": "🆕 Продажи и продления", "stock": "📦 Выключение и включение по наличию", "prices": "💰 Изменение цен",
    "items": "🔁 Лоты: создание, дубли, ошибки", "ended": "⏳ Завершение аренды", "refunds": "💸 Возвраты",
    "bonus": "🎁 Бонус за отзыв", "commands": "🧰 Команды покупателя (!кик, !пароль)",
    "errors": "🚨 Ошибки и сбои",
}

DEFAULTS = {
    "enabled": True,
    "api_key": "",
    "pay": "rub",               # rub | usd | auto
    "proxy": "",                # прокси до MUVSell (http://логин:пароль@ip:порт), пусто — напрямую или через зеркало
    "markup": 100,              # наценка к цене часа MUVSell, %
    "off_markup": 100,          # наценка к цене оффлайн-игры MUVSell, %
    "known_off": None,          # оффлайн-игры MUVSell, о которых уже знаем (новые — выставить или сообщить)
    "fee": 0,                   # комиссия Starvell с продавца, % (сейчас платит покупатель сверху)
    "min_price": 1,             # цена часа не ниже, ₽
    "max_hours": 720,           # остаток лота — столько часов можно купить за раз
    "region": "other",
    "images": True,             # картинка игры в лоте
    "auto_new": True,           # новые игры MUVSell выставлять сразу
    "known_games": None,
    "auto_refund": False,       # нет аккаунтов или баланса MUVSell — вернуть деньги сразу
    "hide_no_stock": True,      # выключать лот игры, пока на MUVSell нет свободных аккаунтов
    "reprice": True,
    "price_min": 30,
    "poll_sec": 60,
    "notify_end": True,
    "warn_min": 30,
    "ext_cmd": True,
    "ext_word": "!продление",
    "ext_minutes": 30,
    "code_word": "!код",
    "en_msgs": True,
    "buyer_cmds": True,
    "review_bonus": False,
    "bonus_hours": 2,
    "bonus_stars": 5,
    "auto_update": True,
    "tz": 3,
    "texts": {},
    "item_texts": {},
    "notify": {},
    "next_id": 1001,
}
PARAMS = {  # ключ: (подпись, пояснение, дробное, мин, макс)
    "markup": ("Наценка, %", "Цена часа = цена часа MUVSell × (1 + наценка%). Долгие аренды MUVSell продаёт со "
                             "скидкой, так что с них вы получаете ещё больше.", True, 0, 5000),
    "off_markup": ("Наценка оффлайн, %", "Цена оффлайн-лота = цена игры навсегда на MUVSell × (1 + наценка%).",
                   True, 0, 5000),
    "min_price": ("Мин. цена лота, ₽", "Дешевле цена часа (и оффлайн-лота) не опустится.", True, 0.01, 100000),
    "fee": ("Комиссия Starvell, %", "Сколько Starvell удерживает с продавца (сейчас 0 — комиссию платит покупатель "
                                    "сверху). Цена делится на (1 − комиссия).", True, 0, 60),
    "max_hours": ("Часов за раз, макс.", "Остаток лота: больше стольких часов в одном заказе не купить.", False, 1, MAX_HOURS),
    "warn_min": ("Предупреждать за, мин", "За сколько минут до конца аренды написать покупателю (0 — не писать).", False, 0, 1440),
    "ext_minutes": ("Окно продления, мин", "Сколько минут после !продление покупка этой игры продлевает аккаунт.", False, 5, 1440),
    "bonus_hours": ("Бонус за отзыв, ч", "Сколько часов добавить к аренде за отзыв (с вашего баланса MUVSell).", False, 1, 48),
    "bonus_stars": ("Нужно звёзд", "Отзыв с такой оценкой и выше даёт бонус.", False, 1, 5),
    "price_min": ("Пересчёт цен, мин", "Как часто сверять цены лотов с ценами MUVSell.", False, 5, 1440),
    "poll_sec": ("Фоновая проверка, сек", "Как часто проверять окончания аренд и наличие (не меньше 20).", False, 20, 3600),
    "tz": ("Часовой пояс", "Смещение от UTC для времени окончания (3 = МСК).", False, -12, 14),
}
TOGGLES = {
    "auto_refund": "💸 Автовозврат, если выдать нельзя",
    "hide_no_stock": "📦 Выключать лоты без наличия",
    "reprice": "💰 Пересчитывать цены",
    "images": "🖼 Картинка игры в лоте",
    "auto_new": "🆕 Сразу выставлять новые игры",
    "notify_end": "🏁 Писать об окончании аренды",
    "ext_cmd": "🔄 Команда продления",
    "buyer_cmds": "🧰 !кик и !пароль",
    "en_msgs": "🇬🇧 Отвечать по-английски",
    "review_bonus": "🎁 Бонус за отзыв",
    "auto_update": "⬆️ Скачивать обновления",
}
PERIODS = {"today": "Сегодня", "7": "7 дней", "30": "30 дней", "all": "Всё время"}

S: dict = {}       # настройки
MAPS: list = []    # лоты: {id, game_id, game, offer_id, public_id, name, price, active, hidden, off, markup, err, old_ids}
RENT: dict = {}    # id покупателя Starvell → [аренды]
DONE: list = []    # обработанные заказы
SALES: list = []   # журнал: {ts, deal, buyer, game_id, game, hours, map, rid, rev, fee, cost, kind, refunded}
EXT: dict = {}     # id покупателя → ждём покупку для продления: {rid, game_id, until}
OBUY: dict = {}    # id покупателя → [оффлайн-покупки: {id, number, game_id, game, login, guard, deal, chat, map, ts}]

_H = {"bot": None, "sv": None, "loop": None, "pm": None}  # объекты Starvell Cardinal (из BIND_TO_INIT)
_lock = threading.RLock()
_stop = threading.Event()
_sv_lock = threading.Lock()
_notified: dict = {}
_relisting: set = set()
_relist_again: set = set()  # пока лот обновлялся, пришла ещё продажа — обновить снова
_state = {"gen": 0, "running": 0, "job": None, "update": None, "sv_last": 0.0, "down": {}}
_cache = {"api": None, "products": (0.0, None), "bal": (0.0, None), "off": (0.0, None)}


# ---------------------------------------------------------------- хранение

def _file(name: str) -> str:
    return os.path.join(DATA_DIR, name + ".json")


def _load(name: str, default):
    try:
        with open(_file(name), encoding="utf-8") as f:
            data = json.load(f)
        return data if isinstance(data, type(default)) else default
    except FileNotFoundError:
        return default
    except Exception as e:
        log.error(f"{PREFIX} не читается {name}.json: {e}")
        return default


def _save(name: str):
    data = {"settings": S, "items": MAPS, "rentals": RENT, "handled": DONE, "sales": SALES, "ext": EXT,
            "offbuys": OBUY}[name]
    with _lock:
        try:
            tmp = _file(name) + ".tmp"
            with open(tmp, "w", encoding="utf-8") as f:
                json.dump(data, f, ensure_ascii=False, indent=1)
            os.replace(tmp, _file(name))
        except Exception as e:
            log.error(f"{PREFIX} не сохраняется {name}.json: {e}")


def _load_all():
    os.makedirs(os.path.join(DATA_DIR, "covers"), exist_ok=True)
    saved = _load("settings", {})
    S.clear()
    S.update({**DEFAULTS, **saved})
    S["notify"] = {**{k: True for k in NOTIFY_CATS}, **(saved.get("notify") or {})}
    for key in ("texts", "item_texts"):
        S[key] = dict(S.get(key) or {})
    MAPS[:] = _load("items", [])
    RENT.clear()
    RENT.update(_load("rentals", {}))
    DONE[:] = _load("handled", [])
    SALES[:] = _load("sales", [])
    EXT.clear()
    EXT.update(_load("ext", {}))
    OBUY.clear()
    OBUY.update(_load("offbuys", {}))


def _bg(fn, *args):
    threading.Thread(target=_safe_call, args=(fn,) + args, daemon=True).start()


def _safe_call(fn, *args):
    try:
        fn(*args)
    except Exception:
        log.exception(f"{PREFIX} {getattr(fn, '__name__', fn)}")


def _plugin_on() -> bool:
    pm = _H.get("pm")
    p = getattr(pm, "plugins", {}).get(UUID) if pm else None
    return p is None or bool(getattr(p, "enabled", True))


def _on() -> bool:
    return bool(_H.get("sv") and _plugin_on() and S.get("enabled"))


# ---------------------------------------------------------------- мелочи

def _code_word() -> str:
    return S.get("code_word") or "!код"


def _ext_word() -> str:
    return S.get("ext_word") or "!продление"


def _lang(who) -> str:
    if not S.get("en_msgs"):
        return "ru"
    if not isinstance(who, dict):
        key = str(who or "")
        who = max((RENT.get(key) or []) + (OBUY.get(key) or []), key=lambda r: r.get("ts") or r.get("exp") or 0,
                   default={})
    return "en" if who.get("lang") == "en" else "ru"


def _set_lang(buyer_id: str, cmd: str):
    lang = "en" if re.fullmatch(r"!?[a-z]+", cmd) else "ru"
    changed = [r for r in RENT.get(buyer_id, []) if r.get("lang", "ru") != lang]
    offs = [p for p in OBUY.get(buyer_id, []) if p.get("lang", "ru") != lang]
    for r in changed + offs:
        r["lang"] = lang
    if changed:
        _save("rentals")
    if offs:
        _save("offbuys")


def _t(key: str, lang: str = "ru", **kw) -> str:
    text = (TEXTS_EN.get(key) if lang == "en" else None) or (S.get("texts") or {}).get(key) or TEXTS[key]
    kw.setdefault("guard", "!code" if lang == "en" and _code_word() == "!код" else _code_word())
    kw.setdefault("word", "!extend" if lang == "en" else _ext_word())
    for k, v in kw.items():
        text = text.replace("{" + k + "}", str(v))
    return text


def _ts(iso) -> float:
    try:
        return datetime.fromisoformat(str(iso).replace("Z", "+00:00")).timestamp()
    except (TypeError, ValueError):
        return 0.0


def _tz():
    return timezone(timedelta(hours=int(S.get("tz", 3) or 0)))


def _when(ts: float, lang: str = "ru") -> str:
    off = int(S.get("tz", 3) or 0)
    label = ("MSK" if lang == "en" else "МСК") if off == 3 else f"UTC{off:+d}"
    return datetime.fromtimestamp(ts, _tz()).strftime("%d.%m.%Y %H:%M ") + label


def _plural(n: int, one: str, few: str, many: str) -> str:
    n1, n10 = n % 10, n % 100
    return one if n1 == 1 and n10 != 11 else few if 2 <= n1 <= 4 and not 12 <= n10 <= 14 else many


def _parse_hours(text: str, top: int = MAX_HOURS) -> list:
    """«24, 3д, 7d» → [24, 72, 168]; дни — с «д»/«d», остальное — часы."""
    out = set()
    for n, unit in re.findall(r"(\d+)\s*(д|d|ч|h)?", (text or "").lower()):
        h = int(n) * (24 if unit in ("д", "d") else 1)
        if 1 <= h <= top:
            out.add(h)
    return sorted(out)


def _left(sec: float) -> str:
    m = max(0, int(sec // 60))
    d, h, m = m // 1440, m % 1440 // 60, m % 60
    return f"{d}д {h}ч" if d else f"{h}ч {m}м" if h else f"{m}м"


def _left_text(sec: float, lang: str = "ru") -> str:
    m = max(1, int(sec // 60))
    d, h, m = m // 1440, m % 1440 // 60, m % 60
    en = lang == "en"
    days = f"{d} day" + ("s" if d > 1 else "") if en else f"{d} " + _plural(d, "день", "дня", "дней")
    parts = ([days] if d else []) + ([f"{h} h" if en else f"{h} ч."] if h else []) \
        + ([f"{m} min" if en else f"{m} мин."] if m and not d else [])
    return " ".join(parts)


def _num(v) -> str:
    return f"{float(v):g}"


def _rub(v) -> str:
    return f"{float(v):,.2f}".replace(",", " ").rstrip("0").rstrip(".") + "₽"


def _onoff(v) -> str:
    return "✅" if v else "❌"


def _okey(m: dict):
    """Чем адресовать лот в API Starvell: publicId, иначе числовой id."""
    return m.get("public_id") or m.get("offer_id")


def _link(m: dict) -> str:
    return f"{SV_SITE}/offers/{_okey(m)}" if _okey(m) else ""


# ---------------------------------------------------------------- API MUVSell (urllib: requests в Starvell Cardinal нет)

ERRORS = {400: "bad_request", 401: "bad_key", 402: "balance", 403: "forbidden", 404: "not_found", 409: "no_stock",
          429: "wait"}
HUMAN = {
    "bad_key": "неверный API-ключ MUVSell",
    "no_key": "API-ключ MUVSell не задан",
    "balance": "недостаточно средств на балансе MUVSell",
    "no_stock": "на MUVSell нет свободных аккаунтов",
    "not_found": "игра или аренда не найдена на MUVSell",
    "forbidden": "ключ не привязан к аккаунту или аккаунт заблокирован",
    "bad_request": "MUVSell отклонил запрос",
    "wait": "слишком часто",
    "no_account": "аренда создана, но аккаунт не выдан — выдайте вручную с сайта",
    "net": "нет связи с MUVSell ни напрямую, ни через запасной адрес",
}
ROUTE_DOWN_SEC = 600


class _Resp:
    def __init__(self, status: int, content: bytes):
        self.status_code, self.content = status, content or b""
        self.ok = 200 <= status < 400

    def json(self):
        return json.loads(self.content.decode("utf-8") or "null")


def _open(method: str, url: str, body=None, headers=None, proxy=None, timeout=TIMEOUT) -> _Resp:
    opener = urllib.request.build_opener(urllib.request.ProxyHandler({"http": proxy, "https": proxy} if proxy else {}))
    data = json.dumps(body).encode("utf-8") if body is not None else None
    req = urllib.request.Request(url, data=data, method=method, headers=dict(headers or {}))
    if data is not None:
        req.add_header("Content-Type", "application/json")
    try:
        with opener.open(req, timeout=timeout) as r:
            return _Resp(r.status, r.read())
    except urllib.error.HTTPError as e:
        try:
            return _Resp(e.code, e.read())
        finally:
            e.close()


def _unsent(e) -> bool:
    """URLError поднимается до ответа сервера (соединение, отправка) — запрос точно не обработан."""
    return isinstance(e, urllib.error.URLError)


def _repeatable(method: str, body) -> bool:
    return method == "GET" or bool(isinstance(body, dict) and body.get("requestId"))


def _proxy() -> "str | None":
    p = (S.get("proxy") or "").strip()
    if not p:
        return None
    scheme, _, rest = p.rpartition("://")
    parts = rest.split(":")
    if "@" not in rest and len(parts) == 4:  # ip:порт:логин:пароль
        rest = f"{parts[2]}:{parts[3]}@{parts[0]}:{parts[1]}"
    return f"{scheme or 'http'}://{rest}"


def _req(method: str, url: str, body=None, headers=None, timeout=TIMEOUT) -> _Resp:
    """Прокси из настроек → напрямую → зеркало на Cloudflare. POST без requestId идёт дальше, только если не ушёл."""
    px = _proxy()
    routes = ([("px", url, px)] if px else []) + [("direct", url, None)]
    if MIRROR and url.startswith(SITE):
        routes.append(("mirror", MIRROR + url[len(SITE):], None))
    live = [r for r in routes if time.time() >= _state["down"].get(r[0], 0)] or routes
    for i, (name, u, proxy) in enumerate(live):
        try:
            return _open(method, u, body, headers, proxy, timeout)
        except (OSError, http.client.HTTPException) as e:
            if i == len(live) - 1 or not (_repeatable(method, body) or _unsent(e)):
                raise
            if not _unsent(e):  # ответа не дождались — маршрут жив, просто медленный
                continue
            _state["down"][name] = time.time() + ROUTE_DOWN_SEC
            log.warning(f"{PREFIX} маршрут {name} к MUVSell не отвечает ({str(e)[-120:]}) — иду следующим")


class Api:
    def __init__(self, key: str):
        self.headers = {"X-API-Key": key, "Accept": "application/json", "User-Agent": f"MUVSellRentStarvell/{VERSION}"}
        self.error = ""

    def call(self, method: str, path: str, body=None, tries: int = 3):
        retry = _repeatable(method, body)
        for attempt in range(tries):
            try:
                r = _req(method, API_BASE + path, body, self.headers)
            except (OSError, http.client.HTTPException) as e:
                self.error = str(e)[-200:]
                if not retry or attempt == tries - 1:
                    return None, "net"
                time.sleep(2)
                continue
            try:
                data = r.json()
            except ValueError:
                data = {}
            if r.ok:
                self.error = ""
                return (data if data is not None else {}), None
            self.error = str((data.get("error") if isinstance(data, dict) else "") or f"HTTP {r.status_code}")[:200]
            if r.status_code == 429 and attempt < tries - 1 and not re.search(r"через|уже", self.error):
                time.sleep(5)
                continue
            if r.status_code >= 500 and retry and attempt < tries - 1:
                time.sleep(2)
                continue
            return None, ERRORS.get(r.status_code, f"http_{r.status_code}")
        return None, "net"

    def balance(self):
        return self.call("GET", "/account/balance")

    def products(self):
        data, err = self.call("GET", "/rental/products")
        return (data.get("products") or [] if data else None), err

    def paid(self, path: str, body: dict):
        data, err = self.call("POST", path, body)
        if err == "balance" and S.get("pay") == "auto":
            data, err = self.call("POST", path, {**body, "payWith": "usd" if body["payWith"] == "rub" else "rub"})
        return data, err

    def rent(self, game_id: str, hours: int, comment: str, request_id: str):
        return self.paid("/rental/create", {"items": [{"gameId": game_id, "durationKey": f"{hours}h", "qty": 1}],
                                            "payWith": _pay(), "comment": comment, "requestId": request_id})

    def extend(self, rental_id: str, hours: int, request_id: str):
        return self.paid(f"/rental/{rental_id}/extend",
                         {"durationKey": f"{hours}h", "payWith": _pay(), "requestId": request_id})

    def rental(self, rental_id: str):
        return self.call("GET", f"/rental/{rental_id}")

    def codes(self, rental_id: str):
        return self.call("GET", f"/rental/{rental_id}/code")

    def kick(self, rental_id: str):
        return self.call("POST", f"/rental/{rental_id}/full-logout", {})

    def change_password(self, rental_id: str):
        return self.call("POST", f"/rental/{rental_id}/change-password", {})

    def terminate(self, rental_id: str):
        return self.call("POST", f"/rental/{rental_id}/terminate", {})

    def offline_catalog(self):
        data, err = self.call("GET", "/offline/catalog")
        return (data.get("games") or [] if data else None), err

    def offline_buy(self, game_id: str, buyer_ref: str, request_id: str, only_new: bool = False):
        """Игра навсегда для покупателя buyer_ref. Повтор с тем же request_id — та же покупка без второго списания.
        only_new — только аккаунт, которого у покупателя ещё нет (иначе 409 без списания)."""
        return self.paid("/offline/buy", {"gameId": game_id, "buyerRef": buyer_ref, "requestId": request_id,
                                          "payWith": _pay(), "onlyNew": only_new})

    def offline_purchase(self, purchase_id: str):
        return self.call("GET", f"/offline/purchases/{purchase_id}")

    def offline_code(self, purchase_id: str):
        return self.call("GET", f"/offline/purchases/{purchase_id}/code")


def _api() -> "Api | None":
    key = S.get("api_key") or ""
    if not key:
        return None
    if not _cache["api"] or _cache["api"][0] != key:
        _cache["api"] = (key, Api(key))
    return _cache["api"][1]


def _human(err, api=None) -> str:
    text = HUMAN.get(err, err or "неизвестная ошибка")
    detail = getattr(api, "error", "")
    return f"{text}: {detail}" if detail else text


def _balance(force: bool = False):
    ts, data = _cache["bal"]
    api = _api()
    if api and (force or data is None or time.time() - ts > 60):
        fresh, _ = api.balance()
        if fresh:
            _cache["bal"] = (time.time(), fresh)
            data = fresh
    return data


def _pay() -> str:
    mode = S.get("pay", "rub")
    if mode != "auto":
        return mode
    return "rub" if float((_balance() or {}).get("balanceRub") or 0) > 0 else "usd"


def _bal_text(data) -> str:
    if not data:
        return "—"
    return f"{_rub(data.get('balanceRub') or 0)} / ${_num(data.get('balanceUsd') or 0)}"


def _products(force: bool = False):
    api = _api()
    if not api:
        return None
    ts, data = _cache["products"]
    if force or data is None or time.time() - ts > 300:
        fresh, _ = api.products()
        if fresh is not None:
            _cache["products"] = (time.time(), fresh)
            data = fresh
    return data


def _prod(game_id: str, fresh: bool = False):
    return next((p for p in _products(fresh) or [] if p["id"] == game_id), None)


def _stock_map(prods) -> dict:
    return {p["id"]: int(p.get("inStock") or 0) if p.get("available") else 0 for p in prods or []}


def _hour_cost(prod: dict) -> float:
    """Цена часа MUVSell — самая дорогая за час (срок 1 ч): долгие сроки MUVSell продаёт со скидкой."""
    if prod.get("pricePerHourRub") is not None:
        return float(prod["pricePerHourRub"])
    one = next((p for p in prod.get("prices") or [] if p.get("hours") == 1 and p.get("priceRub") is not None), None)
    return float(one["priceRub"]) if one else 0.0


def _off_games(force: bool = False):
    """Каталог оффлайн-игр MUVSell: [{id, name, image, priceRub, inStock}]; None — нет ключа или связи."""
    api = _api()
    if not api:
        return None
    ts, data = _cache["off"]
    if force or data is None or time.time() - ts > 300:
        fresh, _ = api.offline_catalog()
        if fresh is not None:
            _cache["off"] = (time.time(), fresh)
            data = fresh
    return data


def _oprod(game_id: str, fresh: bool = False):
    return next((g for g in _off_games(fresh) or [] if str(g["id"]) == str(game_id)), None)


def _is_off(m) -> bool:
    return bool(m) and m.get("kind") == "off"


def _mprod(m: dict, fresh: bool = False):
    """Товар MUVSell привязки: оффлайн-игра или игра для аренды."""
    return _oprod(m["game_id"], fresh) if _is_off(m) else _prod(m["game_id"], fresh)


def _markup(m: "dict | None" = None, off: bool = False) -> float:
    if m and m.get("markup") is not None:
        return float(m["markup"])
    return float(S.get("off_markup" if off or _is_off(m) else "markup") or 0)


def _fee() -> float:
    return min(0.9, max(0.0, float(S.get("fee") or 0) / 100))


def _price(prod: dict, m: "dict | None" = None, off: bool = False) -> float:
    """Цена 1 шт на Starvell, копейки вверх: час аренды или оффлайн-игра навсегда."""
    off = off or _is_off(m)
    base = float(prod.get("priceRub") or 0) if off else _hour_cost(prod)
    value = base * (1 + _markup(m, off) / 100) / (1 - _fee())
    return max(float(S.get("min_price") or 0.01), math.ceil(round(value * 100, 6)) / 100)


def _net(price) -> float:
    return round(float(price or 0) * (1 - _fee()), 2)


def _avail(m: "dict | None" = None) -> int:
    if _is_off(m):
        return OFF_MAX_QTY
    return max(1, min(MAX_HOURS, int(S.get("max_hours") or MAX_HOURS)))


# ---------------------------------------------------------------- Starvell и Telegram

class SvError(Exception):
    def __init__(self, status: int, message: str, code: str = ""):
        super().__init__(f"{message} (HTTP {status}{', ' + code if code else ''})")
        self.status, self.message, self.code = status, message, code


def _svc():
    return _H.get("sv")


def _run(coro, timeout: float = 90):
    """Корутина в цикле бота из рабочего потока (сессия aiohttp Starvell Cardinal живёт в его цикле)."""
    loop = _H.get("loop")
    if not (loop and loop.is_running()):
        coro.close()
        raise RuntimeError("бот Starvell ещё не запущен")
    return asyncio.run_coroutine_threadsafe(coro, loop).result(timeout)


def _paced(fn):
    with _sv_lock:
        wait = SV_DELAY - (time.time() - _state["sv_last"])
        if wait > 0:
            time.sleep(wait)
        try:
            return fn()
        finally:
            _state["sv_last"] = time.time()


def _sv_call(name: str, *args, tries: int = 2):
    """Метод StarvellService (get_order_details, send_message, refund_order…) из рабочего потока."""
    err = None
    for attempt in range(tries):
        try:
            return _paced(lambda: _run(getattr(_svc(), name)(*args)))
        except Exception as e:
            err = e
        if attempt < tries - 1:
            time.sleep(3)
    raise err


async def _araw(method: str, path: str, body=None, image=None):
    """Один запрос к API Starvell сессией бота (куки, заголовки браузера) без повторов → (статус, JSON).
    Повтор создания лота сделал бы дубль, поэтому post_json бота (он повторяет) здесь не годится."""
    sess = _svc().api.session
    if getattr(sess, "_session", None) is None:
        await sess.start()
    try:
        from api.rate_limiter import throttle
        await throttle()
    except Exception:
        pass
    headers = sess._get_headers(f"{SV_SITE}/account/sells", None)
    kw = {}
    if image is not None:
        import aiohttp
        form = aiohttp.FormData()
        form.add_field("images", image[0], filename=image[1], content_type=image[2])
        kw["data"] = form
    elif body is not None:
        headers["content-type"] = "application/json"
        kw["json"] = body
    async with sess._session.request(method, SV_API + path, headers=headers, cookies=sess._get_cookies(True), **kw) as r:
        text = await r.text()
        status = r.status
    try:
        data = json.loads(text) if text.strip() else {}
    except ValueError:
        data = {"message": re.sub(r"\s+", " ", text)[:200]}
    return status, data


def _sv_post(path: str, body=None, image=None):
    status, data = _paced(lambda: _run(_araw("POST", path, body, image)))
    if status >= 400:
        d = data if isinstance(data, dict) else {}
        extra = d.get("extra") if isinstance(d.get("extra"), dict) else {}
        msg = d.get("message") or d.get("error") or f"HTTP {status}"
        if isinstance(msg, list):
            msg = "; ".join(str(x) for x in msg)
        raise SvError(status, str(msg)[:300], str(extra.get("code") or d.get("code") or ""))
    if isinstance(data, dict) and "data" in data and len(data) <= 3:
        data = data["data"]
    return data


def _sv_err(e) -> str:
    if isinstance(e, SvError) and (e.code == "KYC_REQUIRED" or "KYC" in e.message):
        return "Starvell требует пройти верификацию (KYC) — пройдите её на сайте и повторите"
    if isinstance(e, SvError) and e.status in (401, 403):
        return f"Starvell не пустил ({e.status}) — обновите session_cookie бота (/session_cookie)"
    return re.sub(r"\s+", " ", str(e))[:300] or type(e).__name__


def _send(chat_id, text: str) -> bool:
    if not (_svc() and chat_id and text):
        return False
    try:
        _sv_call("send_message", str(chat_id), text)
        return True
    except Exception as e:
        log.error(f"{PREFIX} сообщение в чат {chat_id} не отправлено: {e}")
        return False


def _kb(*rows) -> InlineKeyboardMarkup:
    """Ряды кнопок: (текст, действие) — колбэк плагина, (текст, "url:…") — ссылка."""
    out = []
    for row in rows:
        if not row:
            continue
        if isinstance(row, tuple):
            row = [row]
        out.append([InlineKeyboardButton(text=t, url=d[4:]) if d.startswith("url:")
                    else InlineKeyboardButton(text=t, callback_data=f"{P}:{d}") for t, d in row])
    return InlineKeyboardMarkup(inline_keyboard=out)


def _tg_run(coro):
    loop = _H.get("loop")
    if not (_H.get("bot") and loop and loop.is_running()):
        coro.close()
        return None
    return asyncio.run_coroutine_threadsafe(coro, loop)


def _admins() -> list:
    try:
        from bot.core.config import BotConfig
        return list(BotConfig.ADMIN_IDS() or [])
    except Exception:
        return []


def _notify(text: str, order_id=None, dedup: "str | None" = None, kb=None, cat: str = "errors"):
    """Сообщение админам бота в Telegram. dedup — одно и то же не чаще раза в 10 минут."""
    if dedup:
        if time.time() - _notified.get(dedup, 0) < 600:
            return
        _notified[dedup] = time.time()
    log.info(f"{PREFIX} {re.sub('<[^>]+>', '', re.sub(r'<tg-spoiler>.*?</tg-spoiler>', '***', text, flags=re.S))}")
    if not (S.get("notify") or {}).get(cat, True):
        return
    if order_id and kb is None:
        kb = _kb(("🔗 Открыть заказ", f"url:{SV_SITE}/order/{order_id}"))
    bot = _H.get("bot")
    if not bot:
        return
    for uid in _admins():
        _tg_run(bot.send_message(uid, f"<b>{esc(NAME)}</b>\n{text}", parse_mode="HTML", reply_markup=kb, **_NOPREV))


# ---------------------------------------------------------------- лоты Starvell

def _commands_text(lang: str = "ru", off: bool = False, rent: bool = True) -> str:
    """Команды покупателя: off — есть оффлайн-игры (!офлайн), rent — есть аренды (время, продление, кик, пароль)."""
    en = lang == "en"
    code = ("!code" if _code_word() == "!код" else _code_word()) if en else _code_word()
    lines = [f"• {code} — Steam Guard code" if en else f"• {code} — код Steam Guard"]
    if rent:
        lines += ["• !time — time left", "• !data — login and password again"] if en else             ["• !время — сколько осталось", "• !данные — логин и пароль ещё раз"]
        if S.get("ext_cmd"):
            lines.append("• !extend — extend this same account" if en else f"• {_ext_word()} — продлить этот же аккаунт")
        if S.get("buyer_cmds"):
            lines += ["• !kick — kick everyone else out of the account", "• !password — change the password"] if en                 else ["• !кик — выкинуть всех чужих из аккаунта", "• !пароль — сменить пароль"]
    if off:
        lines.append("• !offline — your lifetime (offline) games again" if en else
                     "• !офлайн — данные оффлайн-игр ещё раз")
    return "\n".join(lines)


def _item_tpl(key: str) -> str:
    return (S.get("item_texts") or {}).get(key) or ITEM_TEXTS[key]


def _item_texts(game: str, map_id: str, off: bool = False) -> tuple:
    fill = {"commands": _commands_text(), "guard": _code_word(), "word": _ext_word()}
    pre = "off_" if off else ""

    def render(tpl: str, name: str) -> str:
        for k, v in {**fill, "game": name}.items():
            tpl = tpl.replace("{" + k + "}", str(v))
        return tpl

    title = re.sub(r"\s+", " ", render(_item_tpl(pre + "title"), game)).strip()
    if len(title) > TITLE_MAX:  # длинное название игры — укорачиваем его, а не хвост с «1 шт = 1 час»
        cut = max(8, len(game) - (len(title) - TITLE_MAX) - 1)
        title = re.sub(r"\s+", " ", render(_item_tpl(pre + "title"), game[:cut].rstrip() + "…")).strip()[:TITLE_MAX]
    tag = f"\n\nrentS-{map_id[1:]}"  # метка: по ней плагин узнаёт свой лот в заказе
    return title, render(_item_tpl(pre + "desc"), game).strip()[:DESC_MAX - len(tag)] + tag


def _ckey(game_id: str, off: bool = False) -> str:
    """Ключ картинки: у оффлайн-игр свои (id — Steam App ID, могут совпасть с id игр аренды)."""
    return f"off-{game_id}" if off else str(game_id)


def _cover_path(game_id: str) -> str:
    os.makedirs(os.path.join(DATA_DIR, "covers"), exist_ok=True)
    return os.path.join(DATA_DIR, "covers", re.sub(r"[^\w-]", "_", game_id) + ".img")


def _img_type(data: bytes) -> "str | None":
    if data[:3] == b"\xff\xd8\xff":
        return "image/jpeg"
    if data[:8] == b"\x89PNG\r\n\x1a\n":
        return "image/png"
    if data[:4] == b"RIFF" and data[8:12] == b"WEBP":
        return "image/webp"
    return None


def _cover(game_id: str):
    """Картинка лота (байты): своя из Telegram или картинка игры с muvsell.store. None — без картинки.
    game_id — ключ из _ckey: «off-…» — оффлайн-игра."""
    path = _cover_path(game_id)
    try:
        if os.path.isfile(path) and os.path.getsize(path) > 1000:
            with open(path, "rb") as f:
                return f.read()
        off = game_id.startswith("off-")
        url = ((_oprod(game_id[4:]) if off else _prod(game_id)) or {}).get("image")
        if not url:
            return None
        r = _req("GET", url, headers={"User-Agent": f"MUVSellRentStarvell/{VERSION}"})
        if not r.ok or len(r.content) < 1000 or not _img_type(r.content):
            return None
        with open(path, "wb") as f:
            f.write(r.content)
        return r.content
    except Exception as e:
        log.warning(f"{PREFIX} картинка {game_id}: {e}")
        return None


def _upload_cover(m: dict) -> "str | None":
    data = _cover(_ckey(m["game_id"], _is_off(m)))
    if not data:
        return "нет картинки игры"
    kind = _img_type(data) or "image/jpeg"
    try:
        _sv_post(f"/offers/{_okey(m)}/images/upload", image=(data, "cover." + kind.split("/")[1], kind))
    except Exception as e:
        return _sv_err(e)
    return None


def _payload(m: dict, prod: dict, price: float, active: bool) -> dict:
    off = _is_off(m)
    title, desc = _item_texts(m["game"], m["id"], off)
    region = REGIONS.get(S.get("region")) or REGIONS["other"]
    attrs = [{"id": REGION_FILTER, "optionId": region[0]}]
    if off:
        attrs.append({"id": METHOD_FILTER, "optionId": METHOD_FULL})
    return {"type": "LOT", "categoryId": CAT_ID, "subCategoryId": SALE_SUB if off else SUB_ID, "price": f"{price:.2f}",
            "isActive": active, "availability": _avail(m), "goods": [], "goodsInstruction": None,
            "tags": ["оффлайн", "навсегда", "steam", "автовыдача"] if off else ["аренда", "steam", "автовыдача"],
            "postPaymentMessage": None, "instantDelivery": False, "autoDelivery": False,
            "descriptions": {"rus": {"briefDescription": title, "description": desc}},
            "basicAttributes": attrs, "numericAttributes": [{"id": LEVEL_FILTER, "numericValue": 0}], "deliveryTime": None}


def _room(m: dict, fresh: bool = False) -> bool:
    """Держать ли лот игры включённым: на MUVSell есть свободный аккаунт (иначе покупателю выдать нечего).
    Оффлайн-лот всегда в продаже: оффлайн-аккаунт продаётся сколько угодно раз."""
    if not S.get("hide_no_stock") or _is_off(m):
        return True
    prods = _products(force=fresh)
    if prods is None:  # MUVSell не ответил — не выключаем вслепую
        return True
    return _stock_map(prods).get(m["game_id"], 0) > 0


def _new_map(prod: dict, off: bool = False) -> dict:
    with _lock:
        mid = f"S{int(S.get('next_id') or 1001)}"
        S["next_id"] = int(mid[1:]) + 1
        m = {"id": mid, "kind": "off" if off else "rent", "game_id": str(prod["id"]),
             "game": prod.get("name") or str(prod["id"]), "offer_id": None,
             "public_id": None, "name": None, "price": 0, "active": False, "hidden": None, "off": False,
             "markup": None, "err": "", "old_ids": [], "created": time.time()}
        MAPS.append(m)
    _save("settings")
    _save("items")
    return m


def _keep_old(m: dict):
    old = [str(x) for x in (m.get("offer_id"), m.get("public_id")) if x]
    if old:
        m["old_ids"] = (old + [i for i in m.get("old_ids") or [] if i not in old])[:20]


def _create_offer(m: dict, active: "bool | None" = None) -> "str | None":
    """Создаёт лот привязки. → None или текст ошибки."""
    prod = _mprod(m)
    if not _svc():
        return "бот Starvell ещё не запущен"
    if not prod:
        return "игры нет в каталоге MUVSell (или нет ключа/связи)"
    active = _room(m) if active is None else active
    price = _price(prod, m)
    body = _payload(m, prod, price, active)
    try:
        res = _sv_post("/offers/create", body)
    except Exception as e:
        m["err"] = f"создание: {_sv_err(e)}"
        _save("items")
        return m["err"]
    res = res if isinstance(res, dict) else {}
    oid, pub = res.get("id"), res.get("publicId")
    if not (oid or pub):
        m["err"] = f"создание: Starvell не вернул id лота ({str(res)[:120]})"
        _save("items")
        return m["err"]
    _keep_old(m)
    m.update(offer_id=str(oid) if oid else None, public_id=str(pub) if pub else None,
             name=body["descriptions"]["rus"]["briefDescription"], price=price, active=active,
             hidden=None if active else "stock", err="", at=time.time())
    _save("items")
    if S.get("images"):
        err = _upload_cover(m)
        if err:
            log.warning(f"{PREFIX} картинка лота {_mlabel(m)} не загружена: {err}")
    return None


def _remove_offer(m: dict) -> "str | None":
    if not _okey(m):
        return None
    try:
        _sv_post(f"/offers/{_okey(m)}/delete")
    except SvError as e:
        if e.status != 404:
            return _sv_err(e)
    except Exception as e:
        return _sv_err(e)
    _keep_old(m)
    m.update(offer_id=None, public_id=None, active=False)
    _save("items")
    return None


def _patch(m: dict, active: bool, price: "float | None" = None) -> "str | None":
    """Включить/выключить лот и поправить остаток и цену — без модерации. → None или ошибка."""
    price = float(price if price is not None else m.get("price") or 0) or None
    if price is None:
        prod = _mprod(m)
        if not prod:
            return "игры нет в каталоге MUVSell"
        price = _price(prod, m)
    try:
        _sv_post(f"/offers/{_okey(m)}/partial-update", {"availability": _avail(m), "price": f"{price:.2f}",
                                                        "minOrderCurrencyAmount": None, "isActive": bool(active)})
    except Exception as e:
        return _sv_err(e)
    m.update(active=bool(active), price=price, hidden=None if active or m.get("off") else "stock", err="")
    _save("items")
    return None


def _offer_list(page) -> list:
    if isinstance(page, list):
        return page
    if isinstance(page, dict):
        for key in ("offers", "items", "data", "list"):
            if isinstance(page.get(key), list):
                return page[key]
    return []


def _sub_of(o: dict):
    return o.get("subCategoryId") or (o.get("subCategory") or {}).get("id")


def _my_offers() -> list:
    out, offset = [], 0
    for _ in range(30):
        page = _offer_list(_sv_post("/offers/list-my", {"categoryId": CAT_ID, "limit": 100, "offset": offset}))
        out += page
        if len(page) < 100:
            break
        offset += 100
    return [o for o in out if _sub_of(o) in (None, SUB_ID, SALE_SUB)]


def _o_title(o: dict) -> str:
    rus = (o.get("descriptions") or {}).get("rus") or {}
    return str(rus.get("briefDescription") or o.get("title") or o.get("name") or "")


def _o_ids(o: dict) -> set:
    return {str(x) for x in (o.get("id"), o.get("publicId")) if x}


def _find(m: dict, offers: list):
    mine = {str(x) for x in (m.get("offer_id"), m.get("public_id")) if x}
    return next((o for o in offers if mine & _o_ids(o)), None) if mine else None


def _rebind(m: dict, o: dict):
    _keep_old(m)
    m.update(offer_id=str(o["id"]) if o.get("id") else None, public_id=str(o["publicId"]) if o.get("publicId") else None,
             active=bool(o.get("isActive")), err="")
    _save("items")


def _ensure(m: dict, offers: list, fresh: bool = False) -> str:
    """Лот привязки: есть на Starvell, включён, пока есть аккаунты, остаток полный, цена верная. → что сделано."""
    if m.get("off"):
        return ""
    o = _find(m, offers)
    if o is None:
        taken = {i for x in MAPS for i in (x.get("offer_id"), x.get("public_id")) if i}
        alt = next((x for x in offers if m.get("name") and _o_title(x) == m["name"] and not (_o_ids(x) & taken)), None)
        if alt:
            _rebind(m, alt)
            o = alt
        else:
            had = bool(_okey(m))
            _keep_old(m)
            m.update(offer_id=None, public_id=None, active=False)
            err = _create_offer(m)
            return f"ошибка: {err}" if err else ("пересоздан" if had else "создан")
    want = _room(m, fresh)
    prod = _mprod(m)
    try:
        cur_price = float(str(o.get("price") or 0).replace(",", "."))
    except ValueError:
        cur_price = 0.0
    price = _price(prod, m) if prod and S.get("reprice") else (cur_price or float(m.get("price") or 0))
    stale = bool(o.get("isActive")) != want or abs(cur_price - price) >= 0.005 \
        or (want and int(o.get("availability") or 0) < _avail(m))
    if not stale:
        if m.get("active") != want or m.get("price") != price or m.get("hidden") != (None if want else "stock"):
            m.update(active=want, price=price, hidden=None if want else "stock")
            _save("items")
        return ""
    err = _patch(m, want, price)
    if err:
        m["err"] = f"обновление: {err}"
        _save("items")
        return f"ошибка: {err}"
    return "включён" if want and not o.get("isActive") else "выключен" if not want and o.get("isActive") else "обновлён"


def _after_sale(m: dict):
    """Starvell уменьшил остаток на купленные часы — пополняем; аккаунтов не осталось — выключаем лот."""
    with _lock:
        if m["id"] in _relisting:  # лот уже обновляется — пусть после этого обновится ещё раз, с этой продажей
            _relist_again.add(m["id"])
            return
        _relisting.add(m["id"])
    try:
        while True:
            time.sleep(RELIST_WAIT)
            if m.get("off") or not _okey(m):
                return
            want = _room(m, fresh=True)  # наличие — свежее: только что ушёл аккаунт
            err = _patch(m, want)
            if err:
                _notify(f"⚠️ Лот {esc(_mlabel(m))} после продажи не обновлён: {esc(err)}. Попробую на сверке.",
                        dedup=f"relist:{m['id']}", cat="items")
            elif not want:
                _notify(f"📦 {esc(_mlabel(m))}: свободных аккаунтов на MUVSell не осталось — лот выключен, "
                        "включу, когда появятся.", dedup=f"wait:{m['id']}", cat="stock")
            with _lock:
                if m["id"] not in _relist_again:
                    _relisting.discard(m["id"])
                    return
                _relist_again.discard(m["id"])
    finally:
        with _lock:
            _relisting.discard(m["id"])
            _relist_again.discard(m["id"])


def _mlabel(m: dict) -> str:
    return f"{m.get('game', '?')} навсегда" if _is_off(m) else str(m.get("game", "?"))


def _map(mid):
    return next((m for m in MAPS if m["id"] == mid), None)


def _match_order(order: dict) -> "dict | None":
    det = order.get("offerDetails") or order.get("offer") or {}
    det = det if isinstance(det, dict) else {}
    ids = {str(x) for x in (order.get("offerId"), order.get("offerPublicId"), det.get("id"), det.get("publicId")) if x}
    m = next((m for m in MAPS if ids & ({str(x) for x in (m.get("offer_id"), m.get("public_id")) if x}
                                        | set(m.get("old_ids") or []))), None) if ids else None
    rus = (det.get("descriptions") or {}).get("rus") or {}
    if not m:
        tag = TAG_RX.search(str(rus.get("description") or ""))
        m = _map(f"S{tag.group(1)}") if tag else None
    if not m:
        brief = rus.get("briefDescription")
        m = next((x for x in MAPS if brief and x.get("name") == brief), None)
    return m


# ---------------------------------------------------------------- журнал продаж и аренды

def _sale(kind: str, rec: dict, hours: int, cost: float, deal_id=None, rev: float = 0, refunded: bool = False):
    with _lock:
        first = deal_id and not any(s.get("deal") == deal_id for s in SALES)
        SALES.append({"ts": time.time(), "deal": deal_id, "buyer": rec.get("buyer") or "", "game_id": rec.get("game_id", ""),
                      "game": rec.get("game", "?"), "hours": int(hours or 0), "map": rec.get("map"), "rid": rec.get("id"),
                      "rev": round(float(rev or 0), 2) if first else 0.0, "fee": _fee(), "cost": round(float(cost or 0), 2),
                      "kind": kind, "refunded": refunded})
        del SALES[:-20000]
    _save("sales")


def _active(buyer_id: str) -> list:
    now = time.time()
    return [r for r in RENT.get(str(buyer_id), []) if r.get("exp", 0) > now]


def _all_active() -> list:
    now = time.time()
    return sorted((r for lst in list(RENT.values()) for r in lst if r.get("exp", 0) > now), key=lambda r: r["exp"])


def _rec(rid: str):
    return next((r for lst in list(RENT.values()) for r in lst if str(r.get("id")) == str(rid)), None)


def _acc_of(data, login: str) -> dict:
    rental = (data or {}).get("rental") or {}
    return next((a for it in rental.get("items") or [] for a in it.get("accounts") or []
                 if str(a.get("login", "")).lower() == login.lower()), {})


def _add_hours(api: Api, rec: dict, hours: int, key: str):
    added, cost, err = 0, 0.0, None
    while added < hours:
        step = min(hours - added, MAX_HOURS)
        data, err = api.extend(rec["id"], step, f"{key}:{added}")
        if err:
            break
        rec["exp"] = _ts(data.get("endsAt")) or rec["exp"]
        cost += float(data.get("cost") or 0)
        added += step
    if added:
        rec["warned"] = False
        _save("rentals")
    return added, err, cost


def _new_rental(api: Api, m: dict, ctx: dict, hours: int):
    """Арендует аккаунт на MUVSell и выдаёт покупателю. → (аренда, None) или (None, ошибка)."""
    oid = ctx["deal"]
    first = min(hours, MAX_HOURS)
    # ник покупателя на MUVSell не шлём — чужие ПДн; requestId — один заказ не купит две аренды даже при повторе
    data, err = api.rent(m["game_id"], first, f"Starvell #{oid[-8:]}", f"sv-{oid}")
    if err:
        return None, err
    rental = data.get("rental") or {}
    acc = next((a for it in rental.get("items") or [] for a in it.get("accounts") or []), None)
    if not acc:
        return None, "no_account"
    rec = {"id": rental["id"], "number": rental.get("number"), "game_id": m["game_id"], "game": m["game"],
           "login": acc.get("login", ""), "exp": _ts(rental.get("endsAt")), "deal": oid, "buyer": ctx["buyer"],
           "buyer_id": ctx["buyer_id"], "chat": ctx["chat"], "map": m.get("id"), "bonus": False, "ended": False,
           "lang": _lang(ctx["buyer_id"]), "rev": ctx["rev"]}
    with _lock:
        RENT.setdefault(ctx["buyer_id"], []).append(rec)
    _save("rentals")
    cost = float(rental.get("totalRub") or 0)
    if hours > first:
        _, _, more = _add_hours(api, rec, hours - first, f"sv-{oid}-rest")
        cost += more
    _sale("new", rec, hours, cost, oid, ctx["rev"])
    lang = rec["lang"]
    hint = "\n\n🇬🇧 English? Type !help" if lang == "ru" and S.get("en_msgs") else ""
    if not _send(ctx["chat"], _t("delivery", lang, game=m["game"], login=rec["login"], password=acc.get("password", ""),
                                 hours=hours, expires=_when(rec["exp"], lang)) + hint):
        _notify(f"⚠️ Покупателю <b>{esc(ctx['buyer'])}</b> не ушли данные аккаунта — отправьте в чат заказа вручную: "
                f"логин <code>{esc(rec['login'])}</code>, пароль <tg-spoiler>{esc(acc.get('password', ''))}</tg-spoiler>",
                oid)
    if S.get("review_bonus") and ctx["rev"] >= REVIEW_MIN_RUB:
        _send(ctx["chat"], _t("review_offer", lang, bonus=S.get("bonus_hours"), stars=S.get("bonus_stars")))
    _notify(f"✅ Выдан <code>{esc(rec['login'])}</code> — {esc(m['game'])}, {hours} ч → <b>{esc(ctx['buyer'])}</b> "
            f"(аренда №{rec['number']}, {_rub(ctx['rev'])})", oid, cat="sales")
    return rec, None


def _extend(api: Api, rec: dict, hours: int, chat_id, deal_id=None, text: str = "extended", kind: str = "ext",
            rev: float = 0):
    key = f"sv-{deal_id}-{kind}" if deal_id else f"adm-{os.urandom(6).hex()}"
    added, err, cost = _add_hours(api, rec, hours, key)
    if not added:
        return err
    _sale(kind, rec, added, cost, deal_id, rev)
    lang = _lang(rec)
    _send(chat_id, _t(text, lang, login=rec["login"], game=rec["game"], hours=added, expires=_when(rec["exp"], lang)))
    if kind == "ext":
        _notify(f"✅ Продлён <code>{esc(rec['login'])}</code> — {esc(rec['game'])}, +{added} ч", deal_id, cat="sales")
    return None


def _fail(ctx: dict, err, api=None, m=None):
    oid = ctx["deal"]
    if ctx.get("late"):  # заказ из простоя могли уже обслужить вручную — решает продавец
        return _notify(f"⚠️ Заказ от <b>{esc(ctx['buyer'])}</b> из простоя выдать не удалось: {esc(_human(err, api))}. "
                       "Проверьте чат: выдайте вручную или оформите возврат.", oid)
    _send(ctx["chat"], _t("problem", _lang(ctx["buyer_id"])))
    refund = bool(S.get("auto_refund")) and err in ("no_stock", "balance")
    _notify(f"❌ Не удалось выдать аренду{' ' + esc(_mlabel(m)) if m else ''} покупателю <b>{esc(ctx['buyer'])}</b>: "
            f"{esc(_human(err, api))}" + ("\n💸 Оформляю возврат." if refund else ""), oid)
    if refund:
        try:
            _sv_call("refund_order", oid, tries=1)
        except Exception as e:
            return _notify(f"⚠️ Возврат не прошёл: <code>{esc(_sv_err(e))}</code>", oid)
        if m:
            _sale("offline" if _is_off(m) else "new",
                  {"game_id": m["game_id"], "game": m["game"], "map": m["id"], "buyer": ctx["buyer"]},
                  0 if _is_off(m) else ctx["hours"], 0, oid, ctx["rev"], True)
        _notify("💸 Возврат по заказу оформлен.", oid, cat="refunds")


def _order_page(oid: str) -> dict:
    res = _sv_call("get_order_details", oid) or {}
    return res.get("pageProps") or res if isinstance(res, dict) else {}


def _process_order(oid: str, chat_hint=None, base: "dict | None" = None, late: bool = False):
    oid = str(oid or "")
    with _lock:
        if not oid or oid in DONE:
            return
        DONE.append(oid)
        del DONE[:-2000]
    _save("handled")
    if not _on():
        return
    order, chat_id, page_err = dict(base or {}), chat_hint, None
    for attempt in range(3):  # в событии заказа нет ни лота, ни количества — берём со страницы заказа
        try:
            pp = _order_page(oid)
            order.update(pp.get("order") or {})
            chat_id = (pp.get("chat") or {}).get("id") or chat_id
            page_err = None
            break
        except Exception as e:
            page_err = e
            time.sleep(3)
    m = _match_order(order)
    if not m:
        if page_err and not base:
            _notify(f"⚠️ Не удалось открыть заказ, чтобы понять, MUVSell ли это: <code>{esc(_sv_err(page_err))}</code>. "
                    "Если это аренда — выдайте вручную.", oid, dedup=f"page:{oid}")
        return  # не наш лот — обычный заказ
    buyer = order.get("buyer") or order.get("user") or {}
    buyer = buyer if isinstance(buyer, dict) else {}
    buyer_id = str(order.get("buyerId") or buyer.get("id") or "")
    hours = max(1, int(order.get("quantity") or 1))
    ctx = {"deal": oid, "buyer": str(buyer.get("username") or buyer.get("nickname") or buyer_id), "buyer_id": buyer_id,
           "chat": chat_id, "rev": float(order.get("basePrice") or 0) / 100, "late": late, "hours": hours}
    if not ctx["chat"] and buyer_id:
        try:
            ctx["chat"] = _sv_call("find_chat_by_user_id", buyer_id)
        except Exception:
            pass
    try:
        return _process_off(m, ctx) if _is_off(m) else _process_rent(m, ctx)
    finally:  # пополнить лот — когда аккаунт уже выдан: наличие на MUVSell тогда уже без него
        _bg(_after_sale, m)


def _process_rent(m: dict, ctx: dict):
    oid, buyer_id, hours = ctx["deal"], ctx["buyer_id"], ctx["hours"]
    log.info(f"{PREFIX} заказ {oid}: {m['game']} {hours} ч, покупатель {ctx['buyer']}")
    api = _api()
    if not api:
        return _fail(ctx, "no_key", None, m)
    ext = EXT.get(buyer_id)
    rec = _rec(ext["rid"]) if ext and ext.get("game_id") == m["game_id"] and ext.get("until", 0) > time.time() else None
    if rec:
        with _lock:
            EXT.pop(buyer_id, None)
        _save("ext")
        if rec.get("exp", 0) > time.time():
            err = _extend(api, rec, hours, ctx["chat"], oid, rev=ctx["rev"])
            if not err:
                return None
            if err not in ("bad_request", "not_found"):
                return _fail(ctx, err, api, m)
    rec, err = _new_rental(api, m, ctx, hours)
    if not rec:
        return _fail(ctx, err, api, m)
    return None


def _buyer_ref(ctx: dict) -> str:
    """Метка покупателя для MUVSell (buyerRef): ID на Starvell, без ника — ник не шлём, это чужие ПДн."""
    if re.fullmatch(r"[A-Za-z0-9._:-]{1,100}", ctx.get("buyer_id") or ""):
        return f"sv:{ctx['buyer_id']}"
    return "svn:" + hashlib.sha256(str(ctx.get("buyer") or "").lower().encode()).hexdigest()[:24]


def _process_off(m: dict, ctx: dict):
    """Оффлайн-лот: покупаем игру навсегда на MUVSell (по аккаунту на штуку заказа) и присылаем данные.
    requestId sv-<заказ>-off-<n>: повтор после перезапуска вернёт те же покупки без второго списания."""
    oid = ctx["deal"]
    api = _api()
    if not api:
        return _fail(ctx, "no_key", None, m)
    qty = ctx["hours"]
    n = min(qty, OFF_MAX_QTY)
    log.info(f"{PREFIX} заказ {oid}: оффлайн {m['game']} × {qty}, покупатель {ctx['buyer']}")
    got, err, ref = [], None, _buyer_ref(ctx)
    for i in range(1, n + 1):
        data, err = api.offline_buy(m["game_id"], ref, f"sv-{oid}-off-{i}", only_new=i > 1)
        p = (data or {}).get("purchase") or {}
        if not err and not p.get("login"):
            err = "no_account"
        if err:
            break
        got.append(p)
    if not got:
        return _fail(ctx, err, api, m)
    lang = _lang(ctx["buyer_id"])
    with _lock:
        lst = OBUY.setdefault(ctx["buyer_id"], [])
        for p in got:
            if not any(x.get("id") == p["id"] for x in lst):
                lst.append({"id": p["id"], "number": p.get("number"), "game_id": m["game_id"], "game": m["game"],
                            "login": p["login"], "guard": bool(p.get("guard")), "deal": oid, "chat": ctx["chat"],
                            "map": m["id"], "buyer": ctx["buyer"], "ts": time.time(), "lang": lang})
        del lst[:-200]
    _save("offbuys")
    _sale("offline", {"game_id": m["game_id"], "game": m["game"], "map": m["id"], "id": got[0]["id"],
                      "buyer": ctx["buyer"]}, 0, sum(float(p.get("priceRub") or 0) for p in got), oid, ctx["rev"])
    hint = "\n\n🇬🇧 English? Type !help" if lang == "ru" and S.get("en_msgs") else ""
    for p in got:
        if not _send(ctx["chat"], _t("off_delivery", lang, game=m["game"], login=p["login"],
                                     password=p.get("password", "")) + hint):
            _notify(f"⚠️ Покупателю <b>{esc(ctx['buyer'])}</b> не ушли данные оффлайн-игры — отправьте в чат заказа "
                    f"вручную: логин <code>{esc(p['login'])}</code>, пароль "
                    f"<tg-spoiler>{esc(p.get('password', ''))}</tg-spoiler>", oid)
        hint = ""
    if err:
        _notify(f"⚠️ Заказ на {qty} шт.: выдано {len(got)} — дальше не вышло: {esc(_human(err, api))}. "
                "Остальное выдайте вручную или оформите частичный возврат.", oid)
    elif qty > n:
        _notify(f"⚠️ Заказ на {qty} шт.: за один заказ выдаю не больше {n} аккаунтов. Остальное — вручную или "
                "частичный возврат.", oid)
    _notify(f"✅ Оффлайн: {esc(m['game'])} навсегда → <b>{esc(ctx['buyer'])}</b> (" + ", ".join(
        f"<code>{esc(p['login'])}</code>" for p in got) + f", {_rub(ctx['rev'])})", oid, cat="sales")
    return None


def _end_refunded(deal_id):
    live = [r for lst in list(RENT.values()) for r in lst
            if r.get("deal") == deal_id and not r.get("ended") and r.get("exp", 0) > time.time()]
    api = _api()
    for r in live:
        err = api.terminate(r["id"])[1] if api else "no_key"
        if err:
            _notify(f"⚠️ Возврат по заказу, а аренду <code>{esc(r['login'])}</code> завершить не удалось: "
                    f"{esc(_human(err, api))}. Завершите её в «👥 Аренды».", deal_id, cat="refunds")
            continue
        r.update(exp=time.time(), ended=True)
        _notify(f"⛔ Аренда <code>{esc(r['login'])}</code> завершена — по заказу возврат.", deal_id, cat="refunds")
    if live:
        _save("rentals")
    hit = [s for s in SALES if s.get("deal") == deal_id and not s.get("refunded")]
    for s in hit:
        s["refunded"] = True
    if hit:
        _save("sales")
        _notify(f"↩️ Возврат по заказу ({esc(hit[0].get('buyer') or '')}, {esc(hit[0].get('game') or '')}).", deal_id,
                cat="refunds")


def _on_review(rec: dict, review: dict):
    try:
        rating = int(float(review.get("rating") or review.get("stars") or 0))
    except (TypeError, ValueError):
        rating = 0
    if not S.get("review_bonus") or rec.get("bonus") or rec.get("exp", 0) <= time.time():
        return
    if rating < int(S.get("bonus_stars") or 5):
        return
    rec["bonus"] = True  # до продления — изменённый отзыв второй бонус не даст
    _save("rentals")
    api, hours = _api(), int(S.get("bonus_hours") or 2)
    err = _extend(api, rec, hours, rec["chat"], rec["deal"], "review_bonus", "bonus") if api else "no_key"
    if err:
        return _notify(f"⚠️ Бонус за отзыв не начислен: {esc(_human(err, api))}", rec["deal"])
    _notify(f"🎁 <code>{esc(rec['login'])}</code> +{hours} ч за отзыв {rating}★.", rec["deal"], cat="bonus")


def _check_orders():
    """Заказы активных аренд: возврат — завершить аренду, отзыв — бонус. Событий об этом Starvell Cardinal не даёт."""
    now, done = time.time(), 0
    for r in _all_active():
        if done >= 10:
            break
        if not r.get("deal") or r.get("ended") or now - r.get("checked", 0) < ORDER_CHECK_SEC:
            continue
        done += 1
        r["checked"] = now
        try:
            pp = _order_page(r["deal"])
        except Exception as e:
            log.debug(f"{PREFIX} заказ {r['deal']}: {e}")
            continue
        order = pp.get("order") or {}
        if str(order.get("status") or "").upper() == "REFUND":
            _end_refunded(r["deal"])
            continue
        review = pp.get("review") or order.get("review")
        if isinstance(review, dict) and (review.get("rating") or review.get("stars")):
            _on_review(r, review)
    if done:
        _save("rentals")
    # оффлайн-заказы первых 3 суток: возврат на Starvell — отметить в статистике (MUVSell за оффлайн деньги не вернёт)
    seen, offs = set(), 0
    for p in [p for lst in list(OBUY.values()) for p in lst]:
        if offs >= 5:
            break
        if not p.get("deal") or p["deal"] in seen or p.get("refunded") or now - p.get("ts", 0) > 3 * 86400                 or now - p.get("checked", 0) < ORDER_CHECK_SEC:
            continue
        seen.add(p["deal"])
        offs += 1
        p["checked"] = now
        try:
            status = str((_order_page(p["deal"]).get("order") or {}).get("status") or "").upper()
        except Exception as e:
            log.debug(f"{PREFIX} заказ {p['deal']}: {e}")
            continue
        if status == "REFUND":
            for x in [x for lst in list(OBUY.values()) for x in lst if x.get("deal") == p["deal"]]:
                x["refunded"] = True
            _end_refunded(p["deal"])
    if offs:
        _save("offbuys")


def _catch_up():
    """Заказы, оплаченные, пока бот не работал: при первом опросе бот их только запоминает, плагинам не передаёт."""
    if not _on():
        return
    try:
        orders = _sv_call("get_all_orders", "CREATED")
    except Exception as e:
        return log.warning(f"{PREFIX} заказы при запуске: {e}")
    for o in orders or []:
        oid = str(o.get("id") or "")
        if not oid or oid in DONE or not _match_order(o):
            continue
        age = time.time() - _ts(o.get("createdAt")) if _ts(o.get("createdAt")) else None
        if age is not None and age <= MISSED_SEC:
            _notify("📦 Заказ оплачен, пока бот не работал, — выдаю.", oid)
            _process_order(oid, None, o, late=True)
            continue
        with _lock:
            DONE.append(oid)
        _save("handled")
        buyer = o.get("user") or o.get("buyer") or {}
        _notify(f"⚠️ Заказ от <b>{esc(str(buyer.get('username') or o.get('buyerId') or ''))}</b> оплачен "
                + (f"{_left(age)} назад, " if age is not None else "") + "пока бот не работал. Выдавать задним числом "
                "не стал — проверьте чат: выдайте вручную или оформите возврат.", oid)


# ---------------------------------------------------------------- команды покупателя

def _guard(api: Api, rec: dict):
    data, _ = api.codes(rec["id"])
    return next((c for c in (data or {}).get("codes") or []
                 if str(c.get("login", "")).lower() == rec["login"].lower()), None)


def _pick_rec(chat_id, buyer_id: str, arg: str, cmd: str):
    rs, lang = [r for r in _active(buyer_id) if not arg or r["login"].lower() == arg.lower()], _lang(buyer_id)
    if not rs:
        _send(chat_id, _t("no_rental", lang))
        return None
    if len(rs) > 1:
        if lang == "en":
            cmd = {"!код": "!code", "!кик": "!kick", "!пароль": "!password"}.get(cmd, "!extend" if cmd == _ext_word() else cmd)
        _send(chat_id, _t("code_which", lang, cmd=cmd, logins="\n".join(f"• {r['login']}" for r in rs)))
        return None
    return rs[0]


def _offs(buyer_id: str, arg: str = "") -> list:
    """Оффлайн-покупки покупателя (по логину — если указан), один логин — один раз, новые первыми."""
    seen, out = set(), []
    for p in reversed(OBUY.get(str(buyer_id), [])):
        key = p["login"].lower()
        if key in seen or p.get("refunded") or (arg and key != arg.lower()):
            continue
        seen.add(key)
        out.append(p)
    return out


def _off_code(chat_id, buyer_id: str, p: dict):
    api, lang = _api(), _lang(buyer_id)
    data, err = api.offline_code(p["id"]) if api else (None, "no_key")
    if data and int(data.get("expiresIn") or 30) < 5:  # код вот-вот сменится — ждём свежий
        time.sleep(int(data["expiresIn"]) + 1)
        data, err = api.offline_code(p["id"])
    if data and data.get("code"):
        return _send(chat_id, _t("code", lang, login=p["login"], code=data["code"], ttl=data.get("expiresIn", 30)))
    reason = api.error if api else ""
    if err == "wait":
        return _send(chat_id, _t("off_code_limit", lang, login=p["login"], reason=reason))
    if err == "no_stock" and re.search(r"нет Steam Guard", reason or ""):
        return _send(chat_id, _t("off_no_guard", lang, login=p["login"]))
    _send(chat_id, _t("code_fail", lang))
    _notify(f"⚠️ Не удалось получить код Steam Guard оффлайн-игры <code>{esc(p['login'])}</code>: "
            f"{esc(_human(err or 'no_key', api))}", p.get("deal"), dedup=f"offcode:{p['id']}")


def _cmd_offline(chat_id, buyer_id: str, arg: str):
    """!офлайн [логин] — данные оффлайн-игр ещё раз (пароль — актуальный с MUVSell)."""
    lang, api = _lang(buyer_id), _api()
    offs = _offs(buyer_id, arg)
    if not offs:
        return _send(chat_id, _t("off_none", lang))
    for p in offs[:5]:
        data = api.offline_purchase(p["id"])[0] if api else None
        pw = ((data or {}).get("purchase") or {}).get("password")
        _send(chat_id, _t("off_creds", lang, game=p["game"], login=p["login"],
                          password=pw or ("— ask the seller" if lang == "en" else "— напишите продавцу")))


def _cmd_code(chat_id, buyer_id: str, arg: str):
    offs = _offs(buyer_id, arg)
    if offs:  # оффлайн-игра: по логину, или единственный аккаунт покупателя вместе с арендами
        rs = [r for r in _active(buyer_id) if not arg or r["login"].lower() == arg.lower()]
        if len(offs) + len(rs) > 1:
            lang = _lang(buyer_id)
            cmd = "!code" if lang == "en" and _code_word() == "!код" else _code_word()
            return _send(chat_id, _t("code_which", lang, cmd=cmd, logins="\n".join(f"• {x['login']}" for x in rs + offs)))
        if not rs:
            return _off_code(chat_id, buyer_id, offs[0])
    rec = _pick_rec(chat_id, buyer_id, arg, _code_word())
    if not rec:
        return
    api = _api()
    code = _guard(api, rec) if api else None
    if code and int(code.get("expiresIn") or 30) < 5:  # код вот-вот сменится — ждём свежий
        time.sleep(int(code["expiresIn"]) + 1)
        code = _guard(api, rec)
    if not code:
        _send(chat_id, _t("code_fail", _lang(buyer_id)))
        return _notify(f"⚠️ Не удалось получить код Steam Guard для <code>{esc(rec['login'])}</code>: "
                       f"{esc(_human('no_key') if not api else api.error or 'у аккаунта нет maFile')}", rec.get("deal"),
                       dedup=f"code:{rec['id']}")
    _send(chat_id, _t("code", _lang(buyer_id), login=rec["login"], code=code["code"], ttl=code.get("expiresIn", 30)))


def _cmd_time(chat_id, buyer_id: str, arg: str):
    rs, lang = _active(buyer_id), _lang(buyer_id)
    if not rs:
        return _send(chat_id, _t("no_rental", lang))
    _send(chat_id, "\n".join(_t("time_left", lang, game=r["game"], login=r["login"],
                                left=_left_text(r["exp"] - time.time(), lang), expires=_when(r["exp"], lang))
                             for r in rs))


def _cmd_creds(chat_id, buyer_id: str, arg: str):
    rs, lang = [r for r in _active(buyer_id) if not arg or r["login"].lower() == arg.lower()], _lang(buyer_id)
    if not rs:
        return _send(chat_id, _t("no_rental", lang))
    api = _api()
    for r in rs:
        pw = _acc_of(api.rental(r["id"])[0], r["login"]).get("password") if api else None
        _send(chat_id, _t("creds", lang, game=r["game"], login=r["login"],
                          password=pw or ("— ask the seller" if lang == "en" else "— напишите продавцу"),
                          expires=_when(r["exp"], lang)))


def _cmd_help(chat_id, buyer_id: str, arg: str):
    lang = _lang(buyer_id)
    _send(chat_id, _t("help", lang, commands=_commands_text(lang, bool(_offs(buyer_id)), bool(RENT.get(buyer_id)))))


def _cmd_ext(chat_id, buyer_id: str, arg: str):
    """!продление [логин] — следующая покупка этой игры в течение окна продлит тот же аккаунт."""
    rec = _pick_rec(chat_id, buyer_id, arg.split()[0] if arg.split() else "", _ext_word())
    if not rec:
        return
    lang = _lang(buyer_id)
    m = next((m for m in MAPS if m["game_id"] == rec["game_id"] and not _is_off(m) and _okey(m) and m.get("active")
              and not m.get("off")), None)
    if not m:
        _send(chat_id, _t("ext_none", lang, game=rec["game"]))
        return _notify(f"⚠️ <b>{esc(rec.get('buyer') or '')}</b> хочет продлить {esc(rec['game'])}, а лот этой игры "
                       f"выключен — продлите в «👥 Аренды».", rec.get("deal"), dedup=f"extnone:{rec['id']}")
    minutes = max(5, int(S.get("ext_minutes") or 30))
    with _lock:
        EXT[str(buyer_id)] = {"rid": rec["id"], "game_id": rec["game_id"], "until": time.time() + minutes * 60}
    _save("ext")
    links = f"• {_rub(m['price'])} / {'hour' if lang == 'en' else 'час'}: {_link(m)}"
    _send(chat_id, _t("ext_offer", lang, login=rec["login"], game=rec["game"], minutes=minutes, links=links))


def _cmd_kick(chat_id, buyer_id: str, arg: str):
    rec, api = _pick_rec(chat_id, buyer_id, arg, "!кик"), _api()
    if not rec or not api:
        return
    _, err = api.kick(rec["id"])
    if err:
        return _send(chat_id, _t("kick_fail", _lang(buyer_id), login=rec["login"], reason=api.error or _human(err)))
    _send(chat_id, _t("kick_ok", _lang(buyer_id), login=rec["login"], game=rec["game"]))
    _notify(f"🚪 <b>{esc(rec.get('buyer') or '')}</b> выкинул сессии <code>{esc(rec['login'])}</code>.", rec.get("deal"),
            cat="commands")


def _change_password(api: Api, rec: dict, chat_id) -> "str | None":
    lang = _lang(rec)
    old = _acc_of(api.rental(rec["id"])[0], rec["login"]).get("password")
    _, err = api.change_password(rec["id"])
    if err:
        reason = api.error or _human(err)
        _send(chat_id, _t("pass_fail", lang, login=rec["login"], reason=reason))
        return reason
    _send(chat_id, _t("pass_wait", lang, login=rec["login"]))

    def wait():
        for _ in range(30):
            if _stop.wait(10):
                return
            pw = _acc_of(api.rental(rec["id"])[0], rec["login"]).get("password")
            if pw and pw != old:
                _send(chat_id, _t("pass_ok", lang, game=rec["game"], login=rec["login"], password=pw))
                return _notify(f"🔑 Пароль <code>{esc(rec['login'])}</code> сменён, новый отправлен покупателю.",
                               rec.get("deal"), cat="commands")
        _send(chat_id, _t("pass_fail", lang, login=rec["login"], reason="смена затянулась, продавец уже уведомлён"))
        _notify(f"⚠️ Смена пароля <code>{esc(rec['login'])}</code> не завершилась за 5 минут — проверьте на сайте.",
                rec.get("deal"))
    _bg(wait)
    return None


def _cmd_password(chat_id, buyer_id: str, arg: str):
    rec, api = _pick_rec(chat_id, buyer_id, arg, "!пароль"), _api()
    if rec and api:
        _change_password(api, rec, chat_id)


BUYER_COMMANDS = [  # (синонимы, обработчик(chat_id, buyer_id, arg), включена ли)
    (("!код", "!code", "!гуард", "!guard", "!sg"), _cmd_code, lambda: _code_word() == "!код"),
    (("!время", "!срок", "!time"), _cmd_time, lambda: True),
    (("!данные", "!логин", "!data", "!acc"), _cmd_creds, lambda: True),
    (("!помощь", "!команды", "!help", "!commands"), _cmd_help, lambda: True),
    (("!extend", "!продлить", "!продли"), _cmd_ext, lambda: S.get("ext_cmd")),
    (("!кик", "!kick", "!выкинуть"), _cmd_kick, lambda: S.get("buyer_cmds")),
    (("!пароль", "!password", "!pass"), _cmd_password, lambda: S.get("buyer_cmds")),
    (("!офлайн", "!оффлайн", "!offline"), _cmd_offline, lambda: True),
]


def _on_command(chat_id, buyer_id: str, text: str):
    cmd, _, arg = (text or "").strip().partition(" ")
    cmd, arg = cmd.lower(), arg.strip()
    if buyer_id not in RENT and buyer_id not in OBUY:  # плагин ему ничего не выдавал — молчим
        return
    if cmd == _code_word().lower():
        handler = _cmd_code
    elif S.get("ext_cmd") and cmd == _ext_word().lower():
        handler = _cmd_ext
    else:
        handler = next((h for names, h, enabled in BUYER_COMMANDS if cmd in names and enabled()), None)
    if handler:
        _set_lang(buyer_id, cmd)
        _bg(handler, chat_id, buyer_id, arg)


# ---------------------------------------------------------------- события Starvell Cardinal

async def on_new_order(order_data: dict, starvell_service=None, **kw):
    try:
        if _on() and order_data.get("id"):
            _bg(_process_order, order_data["id"], order_data.get("chat_id"))  # MUVSell и Starvell отвечают секундами
    except Exception:
        log.exception(f"{PREFIX} новый заказ")


async def on_new_message(message_data: dict, starvell_service=None, **kw):
    try:
        if not _on() or message_data.get("is_own"):
            return
        text = str(message_data.get("content") or "").strip()
        author = str(message_data.get("author") or "")
        if author and (text.startswith("!") or text.lower().partition(" ")[0] == _code_word().lower()):
            _on_command(message_data.get("chat_id"), author, text)
    except Exception:
        log.exception(f"{PREFIX} сообщение")


# ---------------------------------------------------------------- фон

def _end_notices():
    now, api = time.time(), _api()
    for key, lst in list(RENT.items()):
        for r in list(lst):
            if r.get("ended") or not r.get("exp"):
                continue
            left = r["exp"] - now
            if 0 < left <= float(S.get("warn_min") or 0) * 60 and not r.get("warned"):
                r["warned"] = True
                _save("rentals")
                lang = _lang(r)
                _send(r.get("chat"), _t("warn", lang, game=r["game"], login=r["login"], left=_left_text(left, lang),
                                        expires=_when(r["exp"], lang)))
            if left > 0:
                continue
            if api:  # продлить могли и на сайте — сверяемся, прежде чем прощаться
                data, err = api.rental(r["id"])
                if err in ("net", "wait") or str(err).startswith("http_5"):
                    continue
                rental = (data or {}).get("rental") or {}
                if rental.get("status") == "active" and _ts(rental.get("endsAt")) > now:
                    r["exp"] = _ts(rental.get("endsAt"))
                    _save("rentals")
                    continue
            r["ended"] = True
            _save("rentals")
            if S.get("notify_end"):
                _send(r.get("chat"), _t("ended", _lang(r), game=r["game"], login=r["login"]))
            _notify(f"⌛️ Аренда закончилась: <code>{esc(r['login'])}</code> — {esc(r['game'])} "
                    f"({esc(r.get('buyer') or '')})", cat="ended")


def _cleanup():
    cutoff, changed = time.time() - 86400, False
    with _lock:
        for key in list(RENT):
            keep = [r for r in RENT[key] if r.get("exp", 0) > cutoff]
            changed = changed or len(keep) != len(RENT[key])
            if keep:
                RENT[key] = keep
            else:
                del RENT[key]
        old = [k for k, e in EXT.items() if e.get("until", 0) < time.time()]
        for k in old:
            del EXT[k]
    if changed:
        _save("rentals")
    if old:
        _save("ext")


def _sync_stock():
    """Лот аренды включён, пока на MUVSell есть свободные аккаунты: кончились — выключить, появились — включить.
    Оффлайн-лоты не трогает: оффлайн-аккаунт продаётся сколько угодно раз."""
    if not S.get("hide_no_stock"):
        return
    maps = [m for m in MAPS if _okey(m) and not _is_off(m) and not m.get("off") and m["id"] not in _relisting]
    if not maps:
        return
    prods = _products(force=True)
    if prods is None:
        return  # MUVSell не ответил — лоты не трогаем
    stock, off, on = _stock_map(prods), [], []
    for m in maps:
        want = stock.get(m["game_id"], 0) > 0
        if want == bool(m.get("active")):
            continue
        err = _patch(m, want)
        if err:
            _notify(f"⚠️ Лот {esc(_mlabel(m))} не {'включён' if want else 'выключен'}: {esc(err)}",
                    dedup=f"stock:{m['id']}", cat="stock")
            continue
        (on if want else off).append(_mlabel(m))
    if off:
        _notify("📦 На MUVSell нет свободных аккаунтов — выключены лоты: " + esc(", ".join(off))
                + ". Включу, когда освободятся.", cat="stock")
    if on:
        _notify("✅ Аккаунты освободились — снова в продаже: " + esc(", ".join(on)), cat="stock")


def _sync_prices():
    maps = [m for m in MAPS if _okey(m) and not m.get("off")]
    prods = {p["id"]: p for p in (_products(force=True) if any(not _is_off(m) for m in maps) else None) or []}
    offs = {str(g["id"]): g for g in (_off_games(force=True) if any(_is_off(m) for m in maps) else None) or []}
    changed = []
    for m in maps:
        prod = offs.get(str(m["game_id"])) if _is_off(m) else prods.get(m["game_id"])
        if not prod:
            continue
        price = _price(prod, m)
        if abs(price - float(m.get("price") or 0)) < 0.005:
            continue
        old = m.get("price")
        err = _patch(m, bool(m.get("active")), price)
        if err:
            _notify(f"⚠️ Цена {esc(_mlabel(m))} не обновилась: <code>{esc(err)}</code>", dedup=f"price:{m['id']}")
            continue
        changed.append(f"{_mlabel(m)}: {_rub(old or 0)} → {_rub(price)}" + ("" if _is_off(m) else " за час"))
    if changed:
        _notify("💰 Цены обновлены:\n" + esc("\n".join(changed[:30])), cat="prices")


def _resync():
    """Сверка с Starvell: удалённые лоты — создать снова, дубли — удалить, остаток, цена и включённость — как надо."""
    try:
        offers = _my_offers()
    except Exception as e:
        return log.warning(f"{PREFIX} сверка лотов: {_sv_err(e)}")
    present = {i for m in MAPS if _find(m, offers) for i in (m.get("offer_id"), m.get("public_id")) if i}
    names = {m["name"]: m for m in MAPS if m.get("name") and _find(m, offers)}
    dups = [o for o in offers if _o_title(o) in names and not (_o_ids(o) & present)]
    removed = []
    for o in dups[:10]:
        try:
            _sv_post(f"/offers/{o.get('publicId') or o.get('id')}/delete")
            removed.append(_mlabel(names[_o_title(o)]))
            offers.remove(o)
        except Exception as e:
            log.warning(f"{PREFIX} дубль {o.get('id')} не удалён: {e}")
    if removed:
        _notify("🧹 Удалены дубли лотов: " + esc(", ".join(removed)) + ".", dedup="dups", cat="items")
    checks = 0
    for m in [m for m in MAPS if not m.get("off")]:
        if m["id"] in _relisting or checks >= 10:
            continue
        if not _find(m, offers) and time.time() < m.get("retry_at", 0):
            continue
        res = _ensure(m, offers)
        if not res:
            continue
        checks += 1
        if res.startswith("ошибка"):
            m["retry_at"] = time.time() + 1800
            _save("items")
            _notify(f"⚠️ {esc(_mlabel(m))}: {esc(res)}", dedup=f"fix:{m['id']}", cat="items")
        else:
            log.info(f"{PREFIX} {_mlabel(m)}: {res}")


def _vt(v) -> tuple:
    return tuple(int(x) for x in re.findall(r"\d+", str(v or ""))) or (0,)


def _check_update():
    try:
        r = _req("GET", SELF_URL, timeout=60)
        if not r.ok:
            return
        code = r.content.decode("utf-8")
        ver = (re.search(r'^VERSION = "(.*)"$', code, re.M) or [None, ""])[1]
        if _vt(ver) <= _vt(VERSION) or ver == _state["update"] or "BIND_TO_NEW_ORDER" not in code:
            return
        notes = (re.search(r'^CHANGELOG = "(.*)"$', code, re.M) or [None, ""])[1]
        if S.get("auto_update"):
            shutil.copy2(SELF_PATH, SELF_PATH + ".bak")
            with open(SELF_PATH + ".new", "w", encoding="utf-8", newline="\n") as f:
                f.write(code)
            os.replace(SELF_PATH + ".new", SELF_PATH)
        _state["update"] = ver
        _notify(f"⬆️ {'Загружена' if S.get('auto_update') else 'Вышла'} версия <b>v{esc(ver)}</b> (сейчас v{VERSION})."
                + (f"\n\n<b>Что нового:</b>\n{esc(notes[-1500:])}" if notes else "")
                + ("\n\nПерезапустите бота, чтобы применить." if S.get("auto_update")
                   else f"\n\nСкачать: {SELF_URL}"), cat="errors")
    except Exception as e:
        log.warning(f"{PREFIX} проверка обновлений: {e}")


def _loop(gen: int):
    started, caught = time.time(), False
    last = {"resync": 0.0, "price": time.time(), "update": 0.0}
    while not _stop.wait(max(20, int(S.get("poll_sec") or 60))):
        if gen != _state["gen"]:
            return
        if not _on():
            continue
        try:
            if not caught and time.time() - started > 60:
                caught = True
                _catch_up()
            _end_notices()
            _cleanup()
            _check_orders()
            if not _state["job"]:
                if time.time() - last["resync"] > RESYNC_EVERY:
                    last["resync"] = time.time()
                    _resync()
                    _new_games()
                _sync_stock()
                if S.get("reprice") and time.time() - last["price"] > max(5, int(S.get("price_min") or 30)) * 60:
                    last["price"] = time.time()
                    _sync_prices()
            if time.time() - last["update"] > UPDATE_EVERY:
                last["update"] = time.time()
                _check_update()
        except Exception:
            log.exception(f"{PREFIX} фоновая проверка")


def _start():
    with _lock:
        if _state["running"] == _state["gen"] and _state["gen"]:
            return
        _state["gen"] += 1
        _state["running"] = _state["gen"]
        _stop.clear()
        threading.Thread(target=_loop, args=(_state["gen"],), daemon=True, name="muvsell-rent-sv").start()


# ---------------------------------------------------------------- автовыставление

def _plan(game_ids=None, off: bool = False) -> list:
    """Игры MUVSell без лота (по одному лоту на игру). off — оффлайн-игры; у их элементов метка _off."""
    have = {str(m["game_id"]) for m in MAPS if _is_off(m) == off}
    ids = None if game_ids is None else {str(x) for x in game_ids}
    if off:
        src = [{**g, "_off": True} for g in _off_games() or []]
    else:
        src = [p for p in _products() or [] if p.get("available")]
    prods = [p for p in src if str(p["id"]) not in have and (ids is None or str(p["id"]) in ids)]
    return sorted(prods, key=lambda p: p.get("name", ""))


def _tg_edit(chat_id, msg_id, text: str, kb=None):
    bot = _H.get("bot")
    if bot and chat_id and msg_id:
        _tg_run(bot.edit_message_text(text=text, chat_id=chat_id, message_id=msg_id, reply_markup=kb,
                                      parse_mode="HTML", **_NOPREV))


def _run_create(chat_id, msg_id, plan: list):
    _state["job"] = "create"
    ok, fails, streak, waiting = 0, [], 0, 0
    try:
        for i, prod in enumerate(plan, 1):
            if not _on():
                break
            _tg_edit(chat_id, msg_id, f"🚀 Выставляю лоты: {i}/{len(plan)}\n✅ {ok} · 📦 {waiting} · ❌ {len(fails)}\n"
                                      f"Сейчас: {esc(prod.get('name', ''))}")
            m = _new_map(prod, bool(prod.get("_off")))
            err = _create_offer(m)
            if err:
                fails.append(f"{_mlabel(m)}: {err}")
                streak += 1
                if streak >= 3:  # три отказа подряд — лимит, KYC или куки, дальше не ломимся
                    break
            else:
                ok += 1
                streak = 0
                if m.get("hidden"):
                    waiting += 1
            time.sleep(CREATE_DELAY)
    finally:
        _state["job"] = None
    text = f"🏁 Готово: выставлено {ok} из {len(plan)}."
    if waiting:
        text += f"\n📦 Выключены до появления свободных аккаунтов на MUVSell: {waiting} — включу сам."
    if fails:
        text += "\n\n❌ Ошибки:\n" + esc("\n".join(fails[-10:]))
        if streak >= 3:
            text += "\n\n⏸ Три ошибки подряд — остановился. Остальное выставит повторный запуск."
    if chat_id:
        _tg_edit(chat_id, msg_id, text, _kb(("📦 Лоты", "items:0"), ("⬅️ Меню", "main")))
    else:  # запуск из фона (новые игры) — итог уведомлением
        _notify(text, cat="items")


def _new_games():
    """Новые игры на MUVSell (аренда и оффлайн): выставить сразу (auto_new) или прислать кнопку «Выставить»."""
    for off in (False, True):
        key = "known_off" if off else "known_games"
        if off:
            prods = _off_games()
            ids = {str(g["id"]) for g in prods or []}
        else:
            prods = _products()
            ids = {p["id"] for p in prods or [] if p.get("available")}
        if not prods:
            continue
        known = S.get(key)
        if not isinstance(known, list):  # первый запуск: всё, что уже есть, выставляется вручную
            S[key] = sorted(ids)
            _save("settings")
            continue
        new = [p for p in prods if str(p["id"]) in ids - set(known)]
        if not new:
            continue
        S[key] = sorted(set(known) | ids)
        _save("settings")
        what = "оффлайн-игры" if off else "игры"
        names = esc(", ".join(p.get("name", str(p["id"])) for p in new[:20]))
        plan = _plan([p["id"] for p in new], off)
        if S.get("auto_new") and plan and not _state["job"]:
            _notify(f"🆕 На MUVSell новые {what}: {names} — выставляю на Starvell.", cat="items")
            _run_create(None, None, plan)
            continue
        act = "ocreate" if off else "gcreate"
        _notify(f"🆕 На MUVSell новые {what}: {names}.", cat="items",
                kb=_kb(*[(f"🚀 Выставить {p.get('name', '')[:30]}", f"{act}:{p['id']}") for p in new[:8]]))


# ---------------------------------------------------------------- Telegram: экраны

P = "mvs"
PER = 8


class MvsStates(StatesGroup):
    waiting = State()


def scr(text: str, kb=None):
    return ("s", text, kb)


def alert(text: str):
    return ("a", text)


def ask(key: str, arg: str, prompt: str, back: str = "main"):
    return ("ask", key, arg, prompt, back)


def _pages(items: list, page, prefix: str):
    page = max(0, int(page or 0))
    pages = max(1, math.ceil(len(items) / PER))
    page = min(page, pages - 1)
    nav = []
    if pages > 1:
        nav = [("◀️", f"{prefix}:{(page - 1) % pages}"), (f"{page + 1}/{pages}", f"{prefix}:{page}"),
               ("▶️", f"{prefix}:{(page + 1) % pages}")]
    return items[page * PER:(page + 1) * PER], nav, page


def _m_icon(m: dict) -> str:
    if m.get("off"):
        return "⏸"
    if not _okey(m) or m.get("err"):
        return "❗"
    if m.get("hidden"):
        return "📦"
    return "🟢" if m.get("active") else "⚪"


def scr_main(*_):
    api = _api()
    bal = _balance() if api else None
    live = sum(1 for m in MAPS if m.get("active") and _okey(m) and not m.get("off"))
    hidden = sum(1 for m in MAPS if m.get("hidden") and not m.get("off"))
    bad = sum(1 for m in MAPS if not m.get("off") and (m.get("err") or not _okey(m)))
    me = (getattr(_svc(), "last_user_info", None) or {}).get("user") or {}
    lines = [f"<b>🎮 {esc(NAME)}</b> v{VERSION}", "",
             f"Автовыдача: {_onoff(S.get('enabled'))}",
             f"API-ключ MUVSell: {'задан' if api else '❗ не задан — ⚙️ Настройки'}",
             f"Баланс MUVSell: {_bal_text(bal)}" if api else "",
             f"Starvell: {esc(str(me.get('username') or me.get('nickname') or ('подключён' if _svc() else 'бот ещё не запущен')))}",
             f"Лотов: {live} в продаже из {len(MAPS)}" + (f", выключено без наличия: {hidden}" if hidden else "")
             + (f", с ошибкой: {bad}" if bad else ""),
             f"Активных аренд: {len(_all_active())}"]
    if _state["job"]:
        lines.append("⏳ Идёт выставление лотов…")
    if _state["update"]:
        lines.append(f"⬆️ Загружена v{esc(_state['update'])} — перезапустите бота.")
    return scr("\n".join(x for x in lines if x != ""), _kb(
        (("⏸ Выключить автовыдачу" if S.get("enabled") else "▶️ Включить автовыдачу"), "toggle:enabled:main"),
        [("🚀 Аренда: игры", "games:0"), ("💿 Оффлайн: игры", "ogames:0")],
        ("📦 Лоты", "items:0"),
        [("👥 Аренды", "rentals:0"), ("📊 Статистика", "stats:all")],
        [("⚙️ Настройки", "set"), ("🔄 Сверить сейчас", "sync")],
        ("✖️ Закрыть", "close")))


def scr_games(page="0", *_):
    prods = _products()
    if prods is None:
        return scr("❗ Нет связи с MUVSell или не задан API-ключ.", _kb(("⚙️ Настройки", "set"), ("⬅️ Меню", "main")))
    prods = sorted(prods, key=lambda p: p.get("name", ""))
    have = {m["game_id"] for m in MAPS if not _is_off(m)}
    chunk, nav, page = _pages(prods, page, "games")
    rows = [(f"{'✅' if p['id'] in have else '➕' if p.get('available') else '⛔'} "
             f"{p.get('name', '')[:28]} · {int(p.get('inStock') or 0)} акк.", f"game:{p['id']}") for p in chunk]
    todo = len(_plan())
    return scr(f"<b>🚀 Выставить игры</b>\nОдин лот на игру, 1 шт = 1 час, до {_avail()} ч за заказ.\n"
               f"Без лота: {todo} игр.\n\n✅ — лот есть, ➕ — можно выставить, ⛔ — нет цены.",
               _kb(*rows, nav, (f"🚀 Выставить все ({todo})", "createall") if todo else None,
                   ("⬅️ Меню", "main")))


def scr_game(gid, *_):
    prod = _prod(gid)
    if not prod:
        return alert("Игры нет в каталоге MUVSell.")
    own = os.path.isfile(_cover_path(gid)) and os.path.getsize(_cover_path(gid)) > 1000
    m = next((x for x in MAPS if x["game_id"] == gid and not _is_off(x)), None)
    price, cost = _price(prod, m), _hour_cost(prod)
    lines = [f"<b>{esc(prod.get('name', ''))}</b>",
             f"Свободно аккаунтов: {int(prod.get('inStock') or 0)}",
             f"Цена часа: {_rub(price)} (вам {_rub(_net(price))}, MUVSell {_rub(cost)})",
             f"Сутки: {_rub(price * 24)} (MUVSell за сутки дешевле — скидка за срок)",
             "Картинка: " + ("своя" if own else "картинка игры с MUVSell" if prod.get("image") else "нет"),
             f"Лот: {_m_icon(m)} {'в продаже' if m.get('active') else 'выключен'}" if m else "Лот: ещё не выставлен"]
    return scr("\n".join(lines), _kb(
        ("📦 Открыть лот", f"item:{m['id']}") if m else ("🚀 Выставить", f"gcreate:{gid}"),
        ("🖼 Картинка", f"in:cover:{gid}"), ("⬅️ К играм", "games:0")))


def _job(ctx, plan):
    if _state["job"]:
        return alert("Выставление уже идёт.")
    if not plan:
        return alert("Выставлять нечего.")
    if not _svc():
        return alert("Бот Starvell ещё не запущен.")
    _state["job"] = "create"
    threading.Thread(target=_safe_call, args=(_run_create, ctx["chat"], ctx["msg"], plan), daemon=True).start()
    return scr(f"🚀 Выставляю {len(plan)} лотов — по одному в {int(CREATE_DELAY)} сек…")


def act_createall(arg, ctx):
    plan = _plan()
    return scr(f"Выставить <b>{len(plan)}</b> лотов (по одному на игру)? Это ~"
               f"{math.ceil(len(plan) * (CREATE_DELAY + 3) / 60)} мин.",
               _kb([("✅ Да", "createall_yes"), ("❌ Нет", "games:0")]))


def act_createall_yes(arg, ctx):
    return _job(ctx, _plan())


def act_gcreate(gid, ctx):
    return _job(ctx, _plan([gid]))


def scr_ogames(page="0", *_):
    games = _off_games()
    if games is None:
        return scr("❗ Нет связи с MUVSell или не задан API-ключ.", _kb(("⚙️ Настройки", "set"), ("⬅️ Меню", "main")))
    games = sorted(games, key=lambda g: g.get("name", ""))
    have = {str(m["game_id"]) for m in MAPS if _is_off(m)}
    chunk, nav, page = _pages(games, page, "ogames")
    rows = [(f"{'✅' if str(g['id']) in have else '➕'} {g.get('name', '')[:26]} · "
             f"{_rub(_price(g, None, True))}", f"ogame:{g['id']}") for g in chunk]
    todo = len(_plan(off=True))
    return scr("<b>💿 Оффлайн-активация</b>\nИгра навсегда на общем аккаунте, в Starvell → «Аккаунты с играми» → "
               f"«Продажа». 1 шт = 1 аккаунт, до {OFF_MAX_QTY} за заказ.\nМожно выставить: {todo} игр.\n\n"
               "✅ — лот есть, ➕ — можно выставить.",
               _kb(*rows, nav, (f"🚀 Выставить все ({todo})", "ocreateall") if todo else None, ("⬅️ Меню", "main")))


def scr_ogame(gid, *_):
    g = _oprod(gid)
    if not g:
        return alert("Игры нет в оффлайн-каталоге MUVSell.")
    key = _ckey(gid, True)
    own = os.path.isfile(_cover_path(key)) and os.path.getsize(_cover_path(key)) > 1000
    m = next((x for x in MAPS if _is_off(x) and str(x["game_id"]) == str(gid)), None)
    price = _price(g, m, True)
    lines = [f"<b>💿 {esc(g.get('name', ''))}</b> — навсегда",
             f"Цена лота: {_rub(price)} (вам {_rub(_net(price))}, MUVSell {_rub(g.get('priceRub') or 0)})",
             "Картинка: " + ("своя" if own else "картинка игры с MUVSell" if g.get("image") else "нет"),
             f"Лот: {_m_icon(m)} {'в продаже' if m.get('active') else 'выключен'}" if m else "Лот: ещё не выставлен"]
    return scr("\n".join(lines), _kb(
        ("📦 Открыть лот", f"item:{m['id']}") if m else ("🚀 Выставить", f"ocreate:{gid}"),
        ("🖼 Картинка", f"in:cover:{key}"), ("⬅️ К оффлайн-играм", "ogames:0")))


def act_ocreateall(arg, ctx):
    plan = _plan(off=True)
    return scr(f"Выставить <b>{len(plan)}</b> оффлайн-лотов (по одному на игру)? Это ~"
               f"{math.ceil(len(plan) * (CREATE_DELAY + 3) / 60)} мин.",
               _kb([("✅ Да", "ocreateall_yes"), ("❌ Нет", "ogames:0")]))


def act_ocreateall_yes(arg, ctx):
    return _job(ctx, _plan(off=True))


def act_ocreate(gid, ctx):
    return _job(ctx, _plan([gid], True))


def scr_items(page="0", *_):
    maps = sorted(MAPS, key=lambda m: m.get("game", ""))
    if not maps:
        return scr("Лотов пока нет — выставьте игры.", _kb(("🚀 Выставить игры", "games:0"), ("⬅️ Меню", "main")))
    chunk, nav, page = _pages(maps, page, "items")
    rows = [(f"{_m_icon(m)} {'💿 ' if _is_off(m) else ''}{m['game'][:26]} · "
             f"{_rub(m['price']) if m.get('price') else '—'}{'' if _is_off(m) else '/ч'}", f"item:{m['id']}")
            for m in chunk]
    return scr("<b>📦 Лоты</b>\n🟢 в продаже · 📦 выключен без наличия · ⚪ выключен · ⏸ выключен вами · ❗ ошибка",
               _kb(*rows, nav, ("⬅️ Меню", "main")))


def scr_item(mid, *_):
    m = _map(mid)
    if not m:
        return alert("Лот не найден.")
    sold = [s for s in SALES if s.get("map") == mid and s.get("kind") in ("new", "offline") and not s.get("refunded")]
    lines = [f"<b>{esc(_mlabel(m))}</b> ({m['id']})",
             f"Статус: {_m_icon(m)} " + ("выключен вами" if m.get("off") else "в продаже" if m.get("active")
                                         else "выключен: нет свободных аккаунтов" if m.get("hidden") else "выключен"),
             f"{'Цена' if _is_off(m) else 'Цена часа'}: {_rub(m['price']) if m.get('price') else '—'} · "
             f"наценка {_num(_markup(m))}%" + (" (своя)" if m.get("markup") is not None else ""),
             f"Продаж: {len(sold)}" + ("" if _is_off(m) else f", часов: {sum(int(s.get('hours') or 0) for s in sold)}")]
    if m.get("err"):
        lines.append(f"⚠️ {esc(m['err'])}")
    link = _link(m)
    return scr("\n".join(lines), _kb(
        ("🔗 Открыть на Starvell", f"url:{link}") if link else None,
        [("🔁 Пересоздать", f"itre:{mid}"), ("💰 Наценка", f"itmk:{mid}")],
        [("▶️ Включить" if m.get("off") else "⏸ Выключить", f"itoff:{mid}"), ("🗑 Удалить", f"itdel:{mid}")],
        ("⬅️ К лотам", "items:0")))


def act_itre(mid, ctx):
    m = _map(mid)
    if not m:
        return alert("Лот не найден.")
    old = dict(m)
    m.update(offer_id=None, public_id=None, off=False)
    err = _create_offer(m)
    if err:
        m.update(offer_id=old.get("offer_id"), public_id=old.get("public_id"), off=old.get("off"))
        _save("items")
        return alert(f"Не вышло: {err}"[:190])
    if _okey(old):
        _remove_offer(old)
    return ("as", "Пересоздан.", *scr_item(mid)[1:])


def act_itoff(mid, ctx):
    m = _map(mid)
    if not m:
        return alert("Лот не найден.")
    if m.get("off"):
        m["off"] = False
        err = _patch(m, _room(m, fresh=True)) if _okey(m) else _create_offer(m)
        if err:
            _save("items")
            return alert(f"Включён, но Starvell не принял: {err}"[:190])
    else:
        if _okey(m):
            m["off"] = True
            err = _patch(m, False)
            if err:
                m["off"] = False
                return alert(f"Starvell не выключил лот: {err}"[:190])
        m.update(off=True, hidden=None)
    _save("items")
    return scr_item(mid)


def act_itdel(mid, ctx):
    return scr("Удалить лот со Starvell и из плагина?", _kb([("🗑 Да", f"itdel_yes:{mid}"), ("❌ Нет", f"item:{mid}")]))


def act_itdel_yes(mid, ctx):
    m = _map(mid)
    if not m:
        return scr_items()
    err = _remove_offer(m)
    if err:
        return alert(f"Starvell не удалил лот: {err}"[:190])
    with _lock:
        MAPS[:] = [x for x in MAPS if x["id"] != mid]
        known = S.get("known_off" if _is_off(m) else "known_games")
        if isinstance(known, list) and m["game_id"] not in known:
            known.append(m["game_id"])  # удалённую вручную игру автовыставление не вернёт
    _save("items")
    _save("settings")
    return ("as", "Удалён.", *scr_items()[1:])


def scr_rentals(page="0", *_):
    rs = _all_active()
    if not rs:
        return scr("Активных аренд нет.", _kb(("⬅️ Меню", "main")))
    chunk, nav, page = _pages(rs, page, "rentals")
    rows = [(f"{r['game'][:20]} · {r['login']} · {_left(r['exp'] - time.time())}", f"rent:{r['id']}") for r in chunk]
    return scr(f"<b>👥 Активные аренды: {len(rs)}</b>", _kb(*rows, nav, ("⬅️ Меню", "main")))


def scr_rental(rid, *_):
    r = _rec(rid)
    if not r:
        return alert("Аренда не найдена.")
    return scr(f"<b>{esc(r['game'])}</b> — <code>{esc(r['login'])}</code>\nПокупатель: {esc(r.get('buyer') or '')}\n"
               f"До: {_when(r['exp'])} (осталось {_left(r['exp'] - time.time())})\nАренда MUVSell №{r.get('number')}",
               _kb(("🔗 Заказ", f"url:{SV_SITE}/order/{r['deal']}") if r.get("deal") else None,
                   [("🔐 Код", f"rcode:{rid}"), ("🚪 Выкинуть сессии", f"rkick:{rid}")],
                   [("➕ Продлить", f"rext:{rid}"), ("⛔ Завершить", f"rend:{rid}")],
                   ("⬅️ К арендам", "rentals:0")))


def act_rcode(rid, ctx):
    r, api = _rec(rid), _api()
    code = _guard(api, r) if r and api else None
    return alert(f"Код {code['code']} (ещё ~{code.get('expiresIn', 30)} сек.)" if code else "Код не получен.")


def act_rkick(rid, ctx):
    r, api = _rec(rid), _api()
    if not r or not api:
        return alert("Нет аренды или ключа.")
    _, err = api.kick(rid)
    return alert("Сессии завершаются." if not err else f"Не вышло: {_human(err, api)}"[:190])


def act_rext(rid, ctx):
    return ask("rext", rid, "На сколько продлить? Часы или дни с «д» (например <code>3</code> или <code>2д</code>).",
               f"rent:{rid}")


def act_rend(rid, ctx):
    return scr("Завершить аренду досрочно? Деньги MUVSell не вернёт.", _kb([("⛔ Да", f"rend_yes:{rid}"), ("❌ Нет", f"rent:{rid}")]))


def act_rend_yes(rid, ctx):
    r, api = _rec(rid), _api()
    if not r or not api:
        return alert("Нет аренды или ключа.")
    _, err = api.terminate(rid)
    if err:
        return alert(f"Не вышло: {_human(err, api)}"[:190])
    r.update(exp=time.time(), ended=True)
    _save("rentals")
    return ("as", "Аренда завершена.", *scr_rentals()[1:])


def _period(p: str) -> float:
    if p == "today":
        now = datetime.now(_tz())
        return now.replace(hour=0, minute=0, second=0, microsecond=0).timestamp()
    return 0.0 if p == "all" else time.time() - int(p) * 86400


def scr_stats(p="all", *_):
    since = _period(p if p in PERIODS else "all")
    lst = [s for s in SALES if s["ts"] >= since]
    ok = [s for s in lst if not s.get("refunded")]
    rev = sum(s["rev"] for s in ok)
    net = sum(s["rev"] * (1 - float(s.get("fee", _fee()))) for s in ok)
    cost = sum(s["cost"] for s in lst)
    games = {}
    for s in ok:
        games[s["game"]] = games.get(s["game"], 0) + 1
    top = sorted(games.items(), key=lambda x: -x[1])[:8]
    text = (f"<b>📊 Статистика — {PERIODS.get(p, p)}</b>\n\n"
            f"Продаж: {sum(1 for s in ok if s['kind'] == 'new')} · оффлайн: {sum(1 for s in ok if s['kind'] == 'offline')} · "
            f"продлений: {sum(1 for s in ok if s['kind'] == 'ext')} · "
            f"возвратов: {sum(1 for s in lst if s.get('refunded'))}\n"
            f"Продано часов: {sum(int(s.get('hours') or 0) for s in ok if s['kind'] in ('new', 'ext'))}\n"
            f"Выручка: {_rub(rev)} (на руки {_rub(net)})\n"
            f"Расход MUVSell: {_rub(cost)}\n<b>Прибыль: {_rub(net - cost)}</b>")
    if top:
        text += "\n\n🏆 " + esc(", ".join(f"{g} — {n}" for g, n in top))
    return scr(text, _kb([(("• " if k == p else "") + v, f"stats:{k}") for k, v in PERIODS.items()], ("⬅️ Меню", "main")))


def scr_set(*_):
    lines = ["<b>⚙️ Настройки</b>", f"API-ключ: {'••••' + S['api_key'][-4:] if S.get('api_key') else 'не задан'}",
             f"Оплата на MUVSell: {S.get('pay')}", f"Регион в лотах: {(REGIONS.get(S.get('region')) or REGIONS['other'])[1]}",
             f"Прокси до MUVSell: {'задан' if S.get('proxy') else 'нет'}"]
    lines += [f"{label}: {_num(S.get(k))}" for k, (label, *_r) in PARAMS.items()]
    toggles = [(f"{_onoff(S.get(k))} {label[2:]}", f"toggle:{k}:set") for k, label in TOGGLES.items()]
    return scr("\n".join(lines), _kb(
        [("🔑 API-ключ", "in:key"), ("💳 Оплата", "pay")],
        [("🌍 Регион", "region"), ("🌐 Прокси", "in:proxy")],
        *[toggles[i:i + 2] for i in range(0, len(toggles), 2)],
        [("🔢 Числа", "params"), ("🔔 Уведомления", "ntf")],
        [("📝 Тексты лотов", "itexts"), ("💬 Команды", "words")],
        ("⬅️ Меню", "main")))


def scr_params(*_):
    rows = [(f"{label}: {_num(S.get(k))}", f"in:param:{k}") for k, (label, *_r) in PARAMS.items()]
    return scr("<b>🔢 Числа</b> — нажмите, чтобы изменить.", _kb(*rows, ("⬅️ Настройки", "set")))


def scr_ntf(*_):
    rows = [(f"{_onoff(S['notify'].get(k, True))} {label}", f"ntf_t:{k}") for k, label in NOTIFY_CATS.items()]
    return scr("<b>🔔 Уведомления в Telegram</b>", _kb(*rows, ("⬅️ Настройки", "set")))


def act_ntf_t(cat, ctx):
    S["notify"][cat] = not S["notify"].get(cat, True)
    _save("settings")
    return scr_ntf()


def scr_itexts(*_):
    title, desc = _item_texts("Counter-Strike 2", "S1001")
    otitle, odesc = _item_texts("Cuphead", "S1002", True)
    return scr(f"<b>📝 Тексты лотов</b>\nПеременные: {{game}} {{commands}} {{guard}} {{word}}. Метка rentS-… "
               f"дописывается сама. Название — до {TITLE_MAX} символов.\n\n<b>Аренда — название:</b>\n{esc(title)}\n\n"
               f"<b>Аренда — описание:</b>\n{esc(desc[:900])}\n\n<b>💿 Оффлайн — название:</b>\n{esc(otitle)}\n\n"
               f"<b>💿 Оффлайн — описание:</b>\n{esc(odesc[:900])}\n\nНовые тексты — у новых и пересозданных лотов.",
               _kb([("🏷 Название", "in:tpl:title"), ("📄 Описание", "in:tpl:desc")],
                   [("💿 Название", "in:tpl:off_title"), ("💿 Описание", "in:tpl:off_desc")],
                   ("↩️ Стандартные", "tpl_reset"), ("⬅️ Настройки", "set")))


def act_tpl_reset(arg, ctx):
    S["item_texts"] = {}
    _save("settings")
    return scr_itexts()


def scr_words(*_):
    return scr(f"<b>💬 Команды покупателя</b>\nКод Steam Guard: {esc(_code_word())}\nПродление: {esc(_ext_word())}",
               _kb([("🔐 Команда кода", "in:code_word"), ("🔄 Команда продления", "in:ext_word")], ("⬅️ Настройки", "set")))


def act_pay(arg, ctx):
    S["pay"] = {"rub": "usd", "usd": "auto"}.get(S.get("pay"), "rub")
    _save("settings")
    return scr_set()


def act_region(arg, ctx):
    keys = list(REGIONS)
    S["region"] = keys[(keys.index(S.get("region")) + 1) % len(keys)] if S.get("region") in keys else keys[0]
    _save("settings")
    return ("as", "Регион — у новых и пересозданных лотов.", *scr_set()[1:])


def act_toggle(arg, ctx):
    key, _, back = arg.partition(":")
    if key in TOGGLES or key == "enabled":
        S[key] = not S.get(key)
        _save("settings")
    return scr_main() if back == "main" else scr_set()


def act_sync(arg, ctx):
    if _state["job"]:
        return alert("Идёт выставление — сверю после.")
    if not _svc():
        return alert("Бот Starvell ещё не запущен.")

    def run():
        _state["job"] = "sync"
        try:
            _resync()
            _sync_stock()
        finally:
            _state["job"] = None
        _tg_edit(ctx["chat"], ctx["msg"], "✅ Сверка со Starvell закончена.", _kb(("📦 Лоты", "items:0"), ("⬅️ Меню", "main")))
    _bg(run)
    return scr("🔄 Сверяю лоты со Starvell…")


def act_close(arg, ctx):
    return ("del",)


INPUT_PROMPTS = {
    "key": "🔑 Пришлите API-ключ MUVSell (muvsell.store → Профиль → API).",
    "proxy": "🌐 Прокси до MUVSell: <code>http://логин:пароль@ip:порт</code> или <code>ip:порт:логин:пароль</code>. «-» — без прокси.",
    "code_word": "🔐 Команда кода Steam Guard (например <code>!код</code> или <code>код</code>).",
    "ext_word": "🔄 Команда продления (например <code>!продление</code>).",
}


def act_in(arg, ctx):
    key, _, sub = arg.partition(":")
    if key == "param":
        label, hint, *_r = PARAMS[sub]
        return ask("param", sub, f"<b>{esc(label)}</b>\n{esc(hint)}\nСейчас: {_num(S.get(sub))}", "params")
    if key == "tpl":
        return ask("tpl", sub, f"Пришлите новый шаблон ({'оффлайн, ' if sub.startswith('off_') else ''}"
                                f"{'название' if sub.endswith('title') else 'описание'}).", "itexts")
    if key == "itmk":
        return ask("itmk", sub, "Наценка этого лота, %. «-» — общая.", f"item:{sub}")
    if key == "cover":
        off = sub.startswith("off-")
        name = ((_oprod(sub[4:]) if off else _prod(sub)) or {}).get("name", sub)
        return ask("cover", sub, f"🖼 Пришлите картинку для лота <b>{esc(name)}</b> (фото или файл jpg/png).\n"
                                 "Она будет у новых и пересозданных лотов.", _cover_back(sub))
    return ask(key, "", INPUT_PROMPTS[key], "set")


def _cover_back(key: str) -> str:
    return f"ogame:{key[4:]}" if key.startswith("off-") else f"game:{key}"


async def _save_cover(message: Message, gid: str):
    doc = message.document if message.document and (message.document.mime_type or "").startswith("image/") else None
    src = message.photo[-1] if message.photo else doc
    again = _kb(("🖼 Ещё раз", f"in:cover:{gid}"), ("⬅️ К игре", _cover_back(gid)))
    if not src:
        return scr("❌ Нужна картинка — фото или файл jpg/png.", again)
    buf = io.BytesIO()
    await message.bot.download(src, destination=buf)
    data = buf.getvalue()
    if len(data) < 1000 or not _img_type(data):
        return scr("❌ Это не jpg, png или webp.", again)
    with open(_cover_path(gid), "wb") as f:
        f.write(data)
    return scr("✅ Картинка сохранена. Она будет у новых и пересозданных лотов этой игры "
               "(пересоздать — в «📦 Лоты» → лот → «🔁 Пересоздать»).", _kb(("⬅️ К игре", _cover_back(gid))))


def act_itmk(mid, ctx):
    return act_in(f"itmk:{mid}", ctx)


def in_value(key: str, arg: str, text: str):
    text = (text or "").strip()
    if key == "key":
        api = Api(text)
        _, err = api.balance()
        if err in ("bad_key", "forbidden"):
            return scr(f"❌ {esc(_human(err, api))}", _kb(("🔑 Ещё раз", "in:key"), ("⬅️ Настройки", "set")))
        S["api_key"] = text
        _cache["products"] = (0.0, None)
        _save("settings")
        return scr("✅ Ключ сохранён." + (f"\n⚠️ Проверить не удалось: {esc(_human(err, api))}" if err else ""),
                   _kb(("⬅️ Настройки", "set")))
    if key == "proxy":
        S["proxy"] = "" if text in ("-", "") else text
        _state["down"].clear()
    elif key in ("code_word", "ext_word"):
        if not text or " " in text:
            return scr("❌ Одно слово без пробелов.", _kb(("⬅️ Настройки", "words")))
        S[key] = text.lower()
    elif key == "param":
        label, hint, frac, lo, hi = PARAMS[arg]
        try:
            v = float(text.replace(",", "."))
        except ValueError:
            v = None
        if v is None or not lo <= v <= hi:
            return scr(f"❌ Нужно число от {_num(lo)} до {_num(hi)}.", _kb(("🔢 Ещё раз", f"in:param:{arg}"), ("⬅️ Числа", "params")))
        S[arg] = v if frac else int(v)
        _save("settings")
        return scr_params()
    elif key == "tpl":
        if len(text) < 10:
            return scr("❌ Слишком коротко.", _kb(("⬅️ Тексты", "itexts")))
        S["item_texts"][arg] = text
        _save("settings")
        return scr_itexts()
    elif key == "itmk":
        m = _map(arg)
        if not m:
            return scr("Лот не найден.", _kb(("⬅️ Лоты", "items:0")))
        try:
            m["markup"] = None if text == "-" else float(text.replace(",", "."))
        except ValueError:
            return scr("❌ Нужно число.", _kb(("⬅️ Лот", f"item:{arg}")))
        _save("items")
        prod = _mprod(m)
        if prod and _okey(m) and not m.get("off"):
            err = _patch(m, bool(m.get("active")), _price(prod, m))
            if err:
                return scr(f"⚠️ Наценка сохранена, но цена на Starvell не обновилась: {esc(err)}", _kb(("⬅️ Лот", f"item:{arg}")))
        return scr_item(arg)
    elif key == "rext":
        r, api = _rec(arg), _api()
        hours = _parse_hours(text, MAX_HOURS * 4)
        if not r or not api or not hours:
            return scr("❌ Нет аренды, ключа или срока.", _kb(("⬅️ Аренды", "rentals:0")))
        err = _extend(api, r, hours[0], r.get("chat"), None, kind="adm")
        return scr(f"❌ {esc(_human(err, api))}" if err else f"✅ Продлено на {hours[0]} ч.", _kb(("⬅️ Аренда", f"rent:{arg}")))
    _save("settings")
    return scr_set()


SCREENS = {"main": scr_main, "games": scr_games, "game": scr_game, "ogames": scr_ogames, "ogame": scr_ogame, "items": scr_items, "item": scr_item,
           "rentals": scr_rentals, "rent": scr_rental, "stats": scr_stats, "set": scr_set, "params": scr_params,
           "ntf": scr_ntf, "itexts": scr_itexts, "words": scr_words}
ACTIONS = {"createall": act_createall, "createall_yes": act_createall_yes, "gcreate": act_gcreate,
           "ocreateall": act_ocreateall, "ocreateall_yes": act_ocreateall_yes, "ocreate": act_ocreate, "itre": act_itre,
           "itoff": act_itoff, "itdel": act_itdel, "itdel_yes": act_itdel_yes, "itmk": act_itmk, "rcode": act_rcode,
           "rkick": act_rkick, "rext": act_rext, "rend": act_rend, "rend_yes": act_rend_yes, "ntf_t": act_ntf_t,
           "tpl_reset": act_tpl_reset, "pay": act_pay, "region": act_region, "toggle": act_toggle, "sync": act_sync,
           "close": act_close, "in": act_in}


def _allowed(user_id) -> bool:
    return _plugin_on() and user_id in _admins()


async def _thread(fn, *args):
    return await asyncio.get_running_loop().run_in_executor(None, functools.partial(fn, *args))  # без to_thread: Python 3.8


async def _show(res, call: "CallbackQuery | None" = None, message: "Message | None" = None,
                state: "FSMContext | None" = None):
    kind = res[0]
    if kind == "a":
        if call:
            await call.answer(res[1][:200], show_alert=True)
        return
    if kind == "del":
        if call:
            await call.answer()
            try:
                await call.message.delete()
            except Exception:
                pass
        return
    if kind == "ask":
        _, key, arg, prompt, back = res
        await state.set_state(MvsStates.waiting)
        await state.update_data(mvs_key=key, mvs_arg=arg)
        res = scr(prompt, _kb(("❌ Отмена", back)))
    elif kind == "as":
        if call:
            await call.answer(res[1][:200])
        res = scr(res[2], res[3])
    _, text, kb = res
    if call:
        try:
            await call.answer()
        except Exception:
            pass
        try:
            await call.message.edit_text(text, reply_markup=kb, parse_mode="HTML", **_NOPREV)
            return
        except Exception as e:
            if "not modified" in str(e):
                return
        message = call.message
    await message.answer(text, reply_markup=kb, parse_mode="HTML", **_NOPREV)


async def tg_menu(message: Message, state: FSMContext):
    if not _allowed(message.from_user.id):
        return
    await state.set_state(None)
    await _show(await _thread(scr_main), message=message, state=state)


async def tg_callback(call: CallbackQuery, state: FSMContext):
    if not _allowed(call.from_user.id):
        return await call.answer()
    _, _, rest = call.data.partition(":")
    name, _, arg = rest.partition(":")
    ctx = {"uid": call.from_user.id, "chat": call.message.chat.id, "msg": call.message.message_id}
    await state.set_state(None)
    try:
        if name in SCREENS:
            res = await _thread(SCREENS[name], arg)
        elif name in ACTIONS:
            res = await _thread(ACTIONS[name], arg, ctx)
        else:
            return await call.answer()
    except Exception as e:
        log.exception(f"{PREFIX} меню {call.data}")
        return await call.answer(f"Ошибка: {e}"[:200], show_alert=True)
    await _show(res, call=call, state=state)


async def tg_input(message: Message, state: FSMContext):
    if not _allowed(message.from_user.id):
        return
    data = await state.get_data()
    await state.set_state(None)
    try:
        if data.get("mvs_key") == "cover":
            res = await _save_cover(message, data.get("mvs_arg", ""))
        else:
            res = await _thread(in_value, data.get("mvs_key", ""), data.get("mvs_arg", ""), message.text or "")
    except Exception as e:
        log.exception(f"{PREFIX} ввод")
        res = scr(f"❌ Ошибка: {esc(str(e)[:200])}", _kb(("⬅️ Меню", "main")))
    if data.get("mvs_key") == "key":
        try:
            await message.delete()  # ключ не оставляем в переписке
        except Exception:
            pass
    await _show(res, message=message, state=state)


# ---------------------------------------------------------------- подключение к боту

async def on_init(bot, starvell, db, plugin_manager):
    _H.update(bot=bot, sv=starvell, loop=asyncio.get_running_loop(), pm=plugin_manager)
    _load_all()
    _start()
    log.info(f"{PREFIX} плагин v{VERSION} запущен, лотов: {len(MAPS)}, активных аренд: {len(_all_active())}")
    try:
        from aiogram.types import BotCommand
        cmds = [c for c in await bot.get_my_commands() if c.command != "muvsell"]
        await bot.set_my_commands(cmds + [BotCommand(command="muvsell", description="🎮 MUVSell Rent")])
    except Exception:
        pass


async def on_stop(*_):
    _state["gen"] += 1  # фоновый цикл закончится на следующем шаге
    _state["running"] = 0
    _stop.set()


def on_delete():
    _state["gen"] += 1
    _state["running"] = 0
    _stop.set()


BIND_TO_INIT = [on_init]
BIND_TO_STOP = [on_stop]
BIND_TO_NEW_ORDER = [on_new_order]
BIND_TO_NEW_MESSAGE = [on_new_message]
BIND_TO_DELETE = on_delete
COMMANDS = {"muvsell": {"handler": tg_menu, "description": "🎮 MUVSell Rent — меню", "filters": [Command("muvsell")]}}
CALLBACKS = {"muvsell_menu": {"handler": tg_callback, "filter": F.data.startswith(f"{P}:")}}
TEXT_HANDLERS = {"muvsell_input": {"handler": tg_input, "filter": StateFilter(MvsStates.waiting)}}
