import telebot
from telebot.types import InlineKeyboardMarkup, InlineKeyboardButton, ReplyKeyboardMarkup, KeyboardButton
import pandas as pd
import datetime
import time
import requests
import urllib3
import sqlite3
import os
import glob
import shutil
import tempfile
import html
from threading import Thread
from functools import wraps
from bs4 import BeautifulSoup
import urllib.parse
import docx
import re
from dotenv import load_dotenv

load_dotenv()

urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

# --- настройки ---
BOT_TOKEN = os.getenv('BOT_TOKEN')
bot = telebot.TeleBot(BOT_TOKEN, threaded=False)

ADMIN_ID = int(os.getenv('ADMIN_ID'))
# Для системных сообщений можно указать отдельный канал в ENV.
LOG_CHAT_ID = int(os.getenv('LOG_CHAT_ID')) if os.getenv('LOG_CHAT_ID') else ADMIN_ID
SCHEDULE_PAGE_URL = "https://rguk.ru/students/schedule/"
SCHEDULES_DIR = 'schedules_folder'
RETAKES_DIR = 'retakes_folder'
DB_PATH = 'users_vuz.db'

# Базы данных в памяти и кэши
schedule_db = {}
retake_db = {}
group_to_file = {}
all_rooms_cache = []
all_teachers_cache = []
global_update_time_sch = ""
global_update_time_ret = ""
is_updating = False

# Константы
DAY_NAMES = {0: 'понедельник', 1: 'вторник', 2: 'среда', 3: 'четверг', 4: 'пятница', 5: 'суббота', 6: 'воскресенье'}
DAY_SHORTS = {0: 'ПН', 1: 'ВТ', 2: 'СР', 3: 'ЧТ', 4: 'ПТ', 5: 'СБ'}

TYPE_EXPAND = {
    'пр': 'практика', 'лек': 'лекция', 'прак': 'практика',
    'лаб': 'лабораторная', 'сем': 'семинар', 'конс': 'консультация',
    'экз': 'экзамен', 'зач': 'зачёт',
}

_MONTHS = {
    "января": 1, "февраля": 2, "марта": 3, "апреля": 4, "мая": 5, "июня": 6,
    "июля": 7, "августа": 8, "сентября": 9, "октября": 10, "ноября": 11, "декабря": 12
}

_DAYS_OF_WEEK = {
    "пн": 0, "понедельник": 0, "вт": 1, "вторник": 1, "ср": 2, "среда": 2, "среду": 2,
    "чт": 3, "четверг": 3, "пт": 4, "пятница": 4, "пятницу": 4, "сб": 5, "суббота": 5,
    "субботу": 5, "вс": 6, "воскресенье": 6
}

_WORD_TO_NUM = {
    "одну": 1, "одной": 1, "одна": 1, "один": 1, "две": 2, "два": 2, "двух": 2,
    "три": 3, "трёх": 3, "трех": 3, "четыре": 4, "четырёх": 4, "четырех": 4,
    "пять": 5, "пяти": 5, "шесть": 6, "шести": 6, "семь": 7, "семи": 7,
    "восемь": 8, "восьми": 8, "девять": 9, "девяти": 9, "десять": 10, "десяти": 10,
}

_REJECTED_TEACHERS = ("преподаватель кафедры", "препод. кафедры")

LESSON_SLOTS = [
    ("1️⃣", "09:15", "10:45"),
    ("2️⃣", "10:50", "12:20"),
    ("3️⃣", "12:25", "13:55"),
    ("4️⃣", "14:25", "15:55"),
    ("5️⃣", "16:05", "17:35"),
    ("6️⃣", "17:40", "19:10"),
    ("7️⃣", "19:25", "20:55"),
]


# --- вспомогательные функции ---

def log_to_admin(text):
    print(text, flush=True)
    try:
        bot.send_message(LOG_CHAT_ID, f"<code>[system]</code> {text}", parse_mode='HTML')
    except Exception as error:
        print(f"ошибка отправки лога в Telegram: {error}", flush=True)


def get_target_date():
    now = datetime.datetime.now()
    if now.hour >= 21:
        return now.date() + datetime.timedelta(days=1)
    return now.date()


def get_warnings(target_date):
    now = datetime.datetime.now()
    warnings = []
    if now.hour >= 21 and target_date == now.date() + datetime.timedelta(days=1):
        warnings.append("<i>⚠️ показывается расписание на завтра</i>")
    if (target_date - now.date()).days >= 7:
        warnings.append("<i>⚠️ показывается расписание более чем на неделю вперёд. оно ещё может поменяться</i>")
    return "\n".join(warnings) + "\n\n" if warnings else ""


def get_update_time(group_key):
    try:
        path = group_to_file.get(group_key.lower())
        if path and os.path.exists(path):
            dt = datetime.datetime.fromtimestamp(os.path.getmtime(path))
            return f"🕒 данные от: {dt.strftime('%d.%m %H:%M')}"
    except Exception:
        pass
    return ""


def get_lesson_number(time_str, source_number=None):
    source = re.fullmatch(r"([1-9]\d*)(?:\.0)?", str(source_number).strip())
    if source:
        number = int(source[1])
        label = f"{number}️⃣" if number < 10 else ("🔟" if number == 10 else str(number))
        return f"{label} пара"
    t = str(time_str).replace(' ', '').replace('.', ':')
    m = {
        "09:15": "1️⃣", "09:10": "1️⃣", "10:50": "2️⃣", "12:25": "3️⃣", "12:50": "3️⃣",
        "14:25": "4️⃣", "14:30": "4️⃣", "16:05": "5️⃣", "16:10": "5️⃣", "17:40": "6️⃣",
        "17:50": "6️⃣", "19:05": "7️⃣", "19:25": "7️⃣", "20:30": "8️⃣", "21:00": "8️⃣"
    }
    for s, e in m.items():
        if t.startswith(s): return f"{e} пара"
    return "🔹 пара"


def get_week_type(date):
    # Учебный год начинается в сентябре (для дат до августа считаем прошлый год)
    start_year = date.year if date.month >= 8 else date.year - 1
    ref = datetime.date(start_year, 9, 1)
    diff = (date - datetime.timedelta(days=date.weekday()) - (ref - datetime.timedelta(days=ref.weekday()))).days // 7
    return "нечетная" if diff % 2 == 0 else "четная"


def extract_row_lesson(row, wt):
    """Извлекает и нормализует данные о паре из строки таблицы расписания."""
    if row.index[0] == 'Дата':
        sub, tea, room, tp = (
            row['Дисциплина'], row['Преподаватель'], row['Аудитория'], row['Тип']
        )
    elif wt == "нечетная":
        sub, tea, room, tp = row.iloc[6], row.iloc[5], row.iloc[3], row.iloc[4]
    else:
        sub, tea, tp, room = row.iloc[7], row.iloc[8], row.iloc[9], row.iloc[10]

    r_str = str(room).strip() if not pd.isna(room) else ""
    if r_str.endswith('.0'):
        r_str = r_str[:-2]

    return {
        'sub': str(sub).strip().lower() if not pd.isna(sub) and str(sub).strip() else "",
        'tea': str(tea).strip().lower() if not pd.isna(tea) else "",
        'room': r_str,
        'type': str(tp).strip() if not pd.isna(tp) else ""
    }


def _rows_for_date(df, date):
    """Выбирает занятия на календарную дату или на день недельного расписания."""
    if df.columns[0] == 'Дата':
        return df[df['Дата'] == date]
    return df[df.iloc[:, 0] == DAY_SHORTS.get(date.weekday())]


def _lesson_rows(day_df):
    """Определяет половинки до фильтрации по предмету, преподавателю или аудитории."""
    entries, slots = [], {}
    for (_, row), number in zip(day_df.iterrows(), day_df.iloc[:, 1].ffill()):
        tm = str(row.iloc[2]).strip()
        num = get_lesson_number(tm, number)
        match = re.fullmatch(r"(\d{1,2})[:.](\d{2})\s*[-–—]\s*(\d{1,2})[:.](\d{2})", tm)
        span = None
        if match:
            h1, m1, h2, m2 = map(int, match.groups())
            if h1 < 24 and h2 < 24 and m1 < 60 and m2 < 60:
                span = (h1 * 60 + m1, h2 * 60 + m2)
                slots.setdefault(num, set()).add(span)
        entries.append((row, num, span))

    for row, num, span in entries:
        half = None
        if span and span[1] - span[0] in (40, 45) and not num.startswith("🔹"):
            ranges = sorted(slots[num])
            if (len(ranges) == 2 and ranges[0][1] == ranges[1][0]
                    and ranges[0][1] - ranges[0][0] == ranges[1][1] - ranges[1][0]):
                half = ranges.index(span) + 1
            else:
                # В календарных таблицах пустая половинка может отсутствовать.
                start, end = span
                for candidate, index in ((start, 1), (start - (end - start), 2)):
                    if get_lesson_number(f"{candidate // 60:02}:{candidate % 60:02}") == num:
                        half = index
                        break
        yield row, {'num': num, 'half': half}


def _lesson_heading(num, half=None):
    title = num.removeprefix("🔹 ")
    return f"{title} · {half}-я половина" if half else title


def merge_lesson_halves(lessons, match_keys=()):
    """Объединяет смежные половинки с одинаковыми данными занятия и дополнительными match_keys."""
    merged = []
    can_m = True
    for c in lessons:
        item = c.copy() if isinstance(c, dict) else c
        if not merged:
            merged.append(item)
            continue
        p = merged[-1]
        is_match = all(p.get(k) == item.get(k) for k in ('sub', 'room', 'tea', 'type', 'date', *match_keys))
        t1, _, end = p['time'].partition('-')
        start, _, t2 = item['time'].partition('-')
        adjacent = bool(end and t2) and end.strip() == start.strip()
        if 'half' in p or 'half' in item:
            halves = p.get('half') == 1 and item.get('half') == 2 and p['num'] == item['num']
        else:
            halves = not p['num'].startswith("🔹") and item['num'].startswith("🔹")
        if is_match and adjacent and halves and can_m:
            p['time'] = f"{t1}-{t2}"
            if 'half' in p: p['half'] = None
            can_m = False
        else:
            merged.append(item)
            can_m = True
    return merged


def _format_lesson_body(sub, type_str="", tea="", room=""):
    """Форматирует тело карточки занятия без заголовка."""
    res = f"📚 <b>{sub}</b>\n"
    if type_str: res += f"  📝 {TYPE_EXPAND.get(type_str.lower(), type_str)}\n"
    if tea: res += f"  👨‍🏫 {tea}\n"
    if room: res += f"  🚪 {room}\n"
    return res + "\n"


def _resolve_year(day, month):
    now = datetime.datetime.now().date()
    target = datetime.date(now.year, month, day)
    return datetime.date(now.year - 1, month, day) if (target - now).days > 180 else target


def parse_user_date(text: str) -> datetime.date | None:
    """Распознает дату из строки: дни недели, относительные смещения, словесные и числовые даты."""
    if not text:
        return None
    text_lower = text.strip().lower()

    parts = text_lower.split()
    target_wd = None
    has_next = False
    weeks_offset = 0

    for word in parts:
        if word in _DAYS_OF_WEEK:
            target_wd = _DAYS_OF_WEEK[word]

    for word in parts:
        if word in ["след", "след.", "следующий", "следующая", "следующую"]:
            has_next = True
        elif "прошл" in word:
            prefix = word.split("прошл")[0]
            poza_count = prefix.count("поза") if prefix else 0
            weeks_offset = -(1 + poza_count)

    for i, word in enumerate(parts):
        if word == "через":
            for j in range(i + 1, len(parts)):
                if parts[j].isdigit():
                    weeks_offset = int(parts[j])
                    break
                elif parts[j] in _WORD_TO_NUM:
                    weeks_offset = _WORD_TO_NUM[parts[j]]
                    break
                elif parts[j] in ("неделю", "нед", "нед."):
                    weeks_offset = 1
                    break
        elif word == "назад":
            num_found = 0
            for j in range(i - 1, -1, -1):
                if parts[j].isdigit():
                    num_found = int(parts[j])
                    break
                elif parts[j] in _WORD_TO_NUM:
                    num_found = _WORD_TO_NUM[parts[j]]
                    break
                elif parts[j] in ("неделю", "нед", "нед.", "недель", "недели"):
                    if j > 0:
                        continue
                    else:
                        num_found = 1
                        break
            if num_found == 0:
                num_found = 1
            weeks_offset = -num_found

    # 0. формат: дни недели (пн, след вт, ср через 2 недели, пт неделю назад)
    if target_wd is not None:
        now = datetime.datetime.now().date()
        today_wd = now.weekday()
        days_diff = target_wd - today_wd
        if has_next:
            days_diff += 7
        if weeks_offset != 0:
            days_diff += weeks_offset * 7
        return now + datetime.timedelta(days=days_diff)

    # 1. формат: 15 марта 2026
    if len(parts) == 3 and parts[1] in _MONTHS and parts[0].isdigit() and parts[2].isdigit():
        return datetime.date(int(parts[2]), _MONTHS[parts[1]], int(parts[0]))

    # 2. формат: 15 марта
    if len(parts) == 2 and parts[1] in _MONTHS and parts[0].isdigit():
        day, month = int(parts[0]), _MONTHS[parts[1]]
        return _resolve_year(day, month)

    # 3. форматы с точкой (15.03.2026 или 15.03)
    if "." in text_lower:
        dot_parts = [dp for dp in text_lower.split(".") if dp.isdigit()]
        if len(dot_parts) == 3:
            d, m_num, y = map(int, dot_parts)
            if y < 100: y += 2000
            return datetime.date(y, m_num, d)
        elif len(dot_parts) == 2:
            day, month = map(int, dot_parts)
            return _resolve_year(day, month)

    return None


def get_schedule_view(target_type, target, date):
    """Единый диспетчер для формирования текста расписания и клавиатуры навигации."""
    prefix = get_warnings(date)
    if target_type == 'r':
        text = prefix + generate_room_text(target, date)
    elif target_type == 't':
        text = prefix + generate_teacher_text(target, date)
    else:
        target_type = 'd'
        text = prefix + generate_text(target, date)
    kb = InlineKeyboardMarkup()
    kb.row(
        InlineKeyboardButton("⬅️", callback_data=f"{target_type}|{target}|{date - datetime.timedelta(days=1)}"),
        InlineKeyboardButton("📅", callback_data=f"c|{target_type}|{target}"),
        InlineKeyboardButton("➡️", callback_data=f"{target_type}|{target}|{date + datetime.timedelta(days=1)}")
    )
    return text, kb


def update_caches():
    """Обновляет кэш аудиторий, преподавателей и времени обновления файлов."""
    global all_rooms_cache, all_teachers_cache, global_update_time_sch, global_update_time_ret
    rooms = set()
    teachers = set()
    for df in schedule_db.values():
        if df.columns[0] == 'Дата':
            room_columns = [df['Аудитория']]
            teacher_columns = [df['Преподаватель']]
        else:
            room_columns = [df.iloc[:, index] for index in (3, 10) if index < len(df.columns)]
            teacher_columns = [df.iloc[:, index] for index in (5, 8) if index < len(df.columns)]
        for values in room_columns:
            try:
                for val in values.dropna().unique():
                    r = str(val).strip()
                    if r.endswith('.0'): r = r[:-2]
                    if r and r.lower() != 'nan':
                        rooms.add(r)
            except Exception:
                continue
        for values in teacher_columns:
            try:
                for n in values.dropna().unique():
                    t = str(n).strip()
                    if t and t.lower() != 'nan':
                        teachers.add(t)
            except Exception:
                continue
    all_rooms_cache = sorted(rooms)
    all_teachers_cache = sorted(teachers)

    sch_files = glob.glob(os.path.join(SCHEDULES_DIR, "*.xlsx"))
    if sch_files:
        latest = max(os.path.getmtime(f) for f in sch_files)
        global_update_time_sch = f"🕒 база обновлена: {datetime.datetime.fromtimestamp(latest).strftime('%d.%m %H:%M')}"
    else:
        global_update_time_sch = ""

    ret_files = glob.glob(os.path.join(RETAKES_DIR, "*"))
    if ret_files:
        latest = max(os.path.getmtime(f) for f in ret_files)
        global_update_time_ret = f"🕒 база обновлена: {datetime.datetime.fromtimestamp(latest).strftime('%d.%m %H:%M')}"
    else:
        global_update_time_ret = ""


# --- клавиатуры ---

def main_kb():
    kb = ReplyKeyboardMarkup(resize_keyboard=True)
    kb.row(KeyboardButton("📅 моё расписание"))
    kb.row(KeyboardButton("👩‍🎓 расписание преподавателя"), KeyboardButton("🚪 поиск аудитории"))
    kb.row(KeyboardButton("📄 график пересдач"))
    kb.row(KeyboardButton("🔄 сменить группу"))
    return kb


def cancel_kb():
    kb = ReplyKeyboardMarkup(resize_keyboard=True)
    kb.add(KeyboardButton("❌ отмена"))
    return kb


def make_selection_kb(items, prefix, max_items=15):
    kb = InlineKeyboardMarkup()
    for item in sorted(items)[:max_items]:
        kb.add(InlineKeyboardButton(item.lower(), callback_data=f"{prefix}|{item}"))
    return kb


# --- скрейпер ---

def get_all_schedule_links():
    links = set()
    try:
        response = requests.get(SCHEDULE_PAGE_URL, timeout=20, verify=False)
        if response.status_code == 200:
            soup = BeautifulSoup(response.text, 'html.parser')
            for a in soup.find_all('a', href=True):
                href = a['href']
                if 'view.officeapps.live.com' in href:
                    params = urllib.parse.parse_qs(urllib.parse.urlparse(href).query)
                    actual_url = params['src'][0] if 'src' in params else None
                else:
                    actual_url = urllib.parse.urljoin(SCHEDULE_PAGE_URL, href)

                if actual_url:
                    url_lower = urllib.parse.unquote(actual_url.lower())
                    if (url_lower.endswith('.xlsx') or url_lower.endswith('.docx')) and (
                            'курс' in url_lower or 'повтор' in url_lower or 'пересдач' in url_lower):
                        links.add(actual_url)
        return list(links)
    except Exception as e:
        log_to_admin(f"ошибка скрейпинга: {e}")
        return []


# --- работа с бд ---

def _db(sql, params=(), fetch=None):
    with sqlite3.connect(DB_PATH) as conn:
        cur = conn.execute(sql, params)
        if fetch == "one": return cur.fetchone()
        if fetch == "all": return cur.fetchall()


def init_db():
    _db("CREATE TABLE IF NOT EXISTS users (user_id INTEGER PRIMARY KEY, group_name TEXT)")


def set_user_group(user_id, group_name):
    _db("REPLACE INTO users (user_id, group_name) VALUES (?, ?)", (user_id, group_name.lower()))


def get_user_group(user_id):
    res = _db("SELECT group_name FROM users WHERE user_id = ?", (user_id,), fetch="one")
    return res[0] if res else None


def get_all_users():
    return [r[0] for r in _db("SELECT user_id FROM users", fetch="all")]


def delete_user(user_id):
    _db("DELETE FROM users WHERE user_id = ?", (user_id,))


# --- парсинг данных ---

def process_retake_df(df):
    col_map = {}
    for col in df.columns:
        c = str(col).lower()
        if 'групп' in c:
            col_map['group'] = col
        elif 'дисцип' in c:
            col_map['sub'] = col
        elif 'преподав' in c or 'фамилия' in c:
            col_map['tea'] = col
        elif 'дат' in c:
            col_map['date'] = col
        elif 'врем' in c:
            col_map['time'] = col
        elif 'ауд' in c:
            col_map['room'] = col
        elif 'вид' in c or 'тип' in c:
            col_map['type'] = col

    if 'group' not in col_map: return
    df[col_map['group']] = df[col_map['group']].replace(r'^\s*$', None, regex=True).ffill()

    for _, row in df.iterrows():
        group_val = str(row[col_map['group']]).strip()
        if pd.isna(row[col_map['group']]) or not group_val or group_val.lower() == 'nan': continue

        groups = re.findall(r'[а-яёa-z]{2,5}-\d{3}', group_val.lower())
        if not groups:
            groups = [g.strip().lower() for g in re.split(r'[,\n\s]+', group_val) if '-' in g]

        tm = str(row[col_map.get('time')]).strip() if 'time' in col_map else ''

        entry = {
            'sub': str(row[col_map.get('sub')]).strip().lower() if 'sub' in col_map else '',
            'tea': str(row[col_map.get('tea')]).strip().lower() if 'tea' in col_map else '',
            'date': str(row[col_map.get('date')]).strip() if 'date' in col_map else '',
            'time': tm,
            'room': str(row[col_map.get('room')]).strip() if 'room' in col_map else '',
            'type': str(row[col_map.get('type')]).strip() if 'type' in col_map else '',
            'num': get_lesson_number(tm)
        }

        for k in entry:
            if entry[k].lower() == 'nan': entry[k] = ''

        for g in groups:
            if g not in retake_db:
                retake_db[g] = []
            retake_db[g].append(entry)


def load_retakes_from_local():
    global retake_db
    retake_db.clear()
    files = glob.glob(os.path.join(RETAKES_DIR, "*"))
    for filepath in files:
        try:
            if filepath.endswith('.xlsx'):
                df_raw = pd.read_excel(filepath, header=None)
                mask = df_raw.apply(lambda r: r.astype(str).str.contains('групп', case=False, na=False).any(), axis=1)
                if mask.any():
                    h_idx = df_raw[mask].index[0]
                    df = pd.read_excel(filepath, header=h_idx)
                    df = df.dropna(how='all')
                    process_retake_df(df)
            elif filepath.endswith('.docx'):
                doc = docx.Document(filepath)
                for table in doc.tables:
                    header = None
                    data = []
                    for row in table.rows:
                        row_data = [cell.text.strip().replace('\n', ' ') for cell in row.cells]
                        if header is None:
                            if any('групп' in c.lower() for c in row_data):
                                header = [c.lower() if c else f'col_{i}' for i, c in enumerate(row_data)]
                        else:
                            if any(row_data):
                                if len(row_data) < len(header):
                                    row_data.extend([''] * (len(header) - len(row_data)))
                                elif len(row_data) > len(header):
                                    row_data = row_data[:len(header)]
                                data.append(row_data)
                    if header and data:
                        df = pd.DataFrame(data, columns=header)
                        process_retake_df(df)
        except Exception:
            pass


_DATED_HEADER_ALIASES = {
    'Дата': ('дата', 'дата занятия', 'дата занятий'),
    '№ пары': ('№ пары', 'номер пары', '№ занятия', 'номер занятия'),
    'Время': ('время', 'время занятия', 'время проведения'),
    'Дисциплина': ('дисциплина', 'наименование дисциплины', 'предмет'),
    'Преподаватель': ('преподаватель', 'фио преподавателя', 'ф и о преподавателя'),
    'Аудитория': ('ауд', 'аудитория', 'кабинет'),
    'Тип': ('вид уч занятий', 'вид учебных занятий', 'вид занятия',
            'тип учебных занятий', 'тип занятия', 'тип'),
    'Адрес': ('адрес проведения', 'адрес', 'место проведения'),
}


def _normalized_schedule_header(value):
    if pd.isna(value):
        return ''
    name = str(value).casefold().replace('ё', 'е')
    return re.sub(r'\s+', ' ', re.sub(r'[.,:;]+', ' ', name)).strip()


def _dated_column_map(headers):
    """Определяет назначение столбцов по заголовкам, независимо от их порядка."""
    source_names = {_normalized_schedule_header(value): value for value in headers}
    mapping = {}
    for field, aliases in _DATED_HEADER_ALIASES.items():
        for alias in aliases:
            original = source_names.get(alias)
            if original is not None:
                mapping[field] = original
                break
    return mapping


def _dated_schedule_header(df_raw):
    """Находит заголовок календарного листа после неудачи недельного поиска."""
    required = {'Дата', '№ пары', 'Время'}
    for index, row in df_raw.iterrows():
        if required.issubset(_dated_column_map(row).keys()):
            return index
    return None


def _dated_schedule_date(value):
    if isinstance(value, (datetime.date, datetime.datetime, pd.Timestamp)) and not pd.isna(value):
        return value.date() if isinstance(value, (datetime.datetime, pd.Timestamp)) else value
    if isinstance(value, str):
        text = value.strip()
        for pattern, date_format in (
            (r'\d{1,2}\.\d{1,2}\.\d{4}', '%d.%m.%Y'),
            (r'\d{1,2}/\d{1,2}/\d{4}', '%d/%m/%Y'),
            (r'\d{4}-\d{1,2}-\d{1,2}', '%Y-%m-%d'),
        ):
            if re.fullmatch(pattern, text):
                try:
                    return datetime.datetime.strptime(text, date_format).date()
                except ValueError:
                    return None
    return None


def _read_dated_schedule(xls, sheet, header_index):
    """Приводит разные порядки колонок расписаний по датам к общему виду."""
    source = pd.read_excel(xls, sheet_name=sheet, header=header_index)
    columns = _dated_column_map(source.columns)
    required = ('Дата', '№ пары', 'Время', 'Дисциплина', 'Преподаватель', 'Аудитория', 'Тип')
    missing = [field for field in required if field not in columns]
    if missing:
        raise ValueError('в расписании по датам не найдены колонки: ' + ', '.join(missing))

    lessons = []
    current_date = None
    for _, row in source.iterrows():
        date_value = row[columns['Дата']]
        if pd.notna(date_value):
            current_date = _dated_schedule_date(date_value)
        subject = row[columns['Дисциплина']]
        if current_date is None or pd.isna(subject) or not str(subject).strip():
            continue
        lesson_time = row[columns['Время']]
        if pd.isna(lesson_time) or not re.match(r'^\s*\d{1,2}[:.]\d{2}\s*[-–]\s*\d{1,2}[:.]\d{2}', str(lesson_time)):
            continue
        lessons.append({
            'Дата': current_date,
            '№ пары': row[columns['№ пары']],
            'Время': str(lesson_time).strip(),
            'Дисциплина': subject,
            'Преподаватель': row[columns['Преподаватель']],
            'Аудитория': row[columns['Аудитория']],
            'Тип': row[columns['Тип']],
            'Адрес': row[columns['Адрес']] if 'Адрес' in columns else None,
        })

    if not lessons:
        raise ValueError('в расписании по датам не найдено занятий с корректной датой и временем')

    return pd.DataFrame(
        lessons,
        columns=['Дата', '№ пары', 'Время', 'Дисциплина', 'Преподаватель', 'Аудитория', 'Тип', 'Адрес'],
    )


def _load_schedules_from_dir(directory):
    """Читает XLSX из каталога и возвращает базу вместе с ошибками чтения.

    Ошибка одного файла или листа не прерывает обработку остальных. Эта
    функция не отправляет сообщения сама: вызывающий код формирует один
    итоговый отчёт после завершения обновления.
    """
    temp_db, temp_mapping = {}, {}
    errors = []
    files = sorted(glob.glob(os.path.join(directory, "*.xlsx")))

    if not files:
        return temp_db, temp_mapping, ["не найдено ни одного файла расписания"]

    for filepath in files:
        recognized_sheets = 0
        try:
            xls = pd.ExcelFile(filepath, engine='openpyxl')
        except Exception as error:
            errors.append(
                f"не удалось открыть файл {os.path.basename(filepath)}: {error}"
            )
            continue

        try:
            errors_before_file = len(errors)
            for sheet in xls.sheet_names:
                try:
                    df_raw = pd.read_excel(xls, sheet_name=sheet, header=None)
                    mask = df_raw.apply(
                        lambda row: row.astype(str).str.contains('день недели', case=False, na=False).any(),
                        axis=1,
                    )
                    if not mask.any():
                        dated_header = _dated_schedule_header(df_raw)
                        if dated_header is None:
                            errors.append(
                                f"лист «{sheet}» в файле {os.path.basename(filepath)} "
                                "пропущен: не найдена строка заголовков с колонкой «День недели»"
                            )
                            continue
                        df = _read_dated_schedule(xls, sheet, dated_header)
                    else:
                        header_index = df_raw[mask].index[0]
                        df = pd.read_excel(xls, sheet_name=sheet, header=header_index)
                        df = df.dropna(how='all', axis=1)
                        day_column = df.columns[0]
                        df[day_column] = df[day_column].astype(str).str.strip().str.upper()
                        df.loc[~df[day_column].isin(['ПН', 'ВТ', 'СР', 'ЧТ', 'ПТ', 'СБ']), day_column] = None
                        df[day_column] = df[day_column].ffill()
                    group_key = sheet.strip().lower()
                    temp_db[group_key], temp_mapping[group_key] = df, filepath
                    recognized_sheets += 1
                except Exception as error:
                    errors.append(
                        f"лист «{sheet}» в файле {os.path.basename(filepath)} "
                        f"пропущен: {error}"
                    )

            if not recognized_sheets and len(errors) == errors_before_file:
                errors.append(
                    f"в файле {os.path.basename(filepath)} не распознано ни одного листа расписания"
                )
        finally:
            xls.close()

    return temp_db, temp_mapping, errors


def _unique_errors(errors):
    return list(dict.fromkeys(errors))


def _format_schedule_update_report(
    group_count,
    errors,
    downloaded_schedules=None,
    downloaded_retakes=None,
    preserved_groups=0,
):
    """Возвращает HTML-безопасный отчёт, который помещается в Telegram."""
    lines = [
        "🏁 <b>база расписаний обновлена</b>",
        f"👥 групп в базе: <b>{group_count}</b>",
    ]
    if downloaded_schedules is not None:
        lines.append(
            f"📥 скачано: {downloaded_schedules} расписаний, "
            f"{downloaded_retakes} пересдач"
        )
    if preserved_groups:
        lines.append(f"🛡️ сохранено из предыдущей базы: <b>{preserved_groups}</b>")

    errors = _unique_errors(errors)
    if not errors:
        return "\n".join(lines + ["✅ ошибок чтения нет."])

    lines.extend(["", f"⚠️ <b>пропущены файлы и листы: {len(errors)}</b>"])
    report = "\n".join(lines)
    max_length = 3800  # log_to_admin добавляет служебный HTML-префикс.
    for index, error in enumerate(errors):
        escaped_error = html.escape(str(error), quote=False)
        if len(escaped_error) > 500:
            escaped_error = f"{escaped_error[:497]}…"
        entry = f"\n• {escaped_error}"
        if len(report) + len(entry) <= max_length:
            report += entry
            continue

        omitted = len(errors) - index
        suffix = f"\n• … и ещё {omitted}"
        return f"{report[:max_length - len(suffix)]}{suffix}"
    return report


def _write_preserved_groups(filepath, groups):
    """Записывает снимок групп в XLSX, если исходный файл уже недоступен."""
    used_sheet_names = set()
    with pd.ExcelWriter(filepath, engine='openpyxl') as writer:
        for index, group in enumerate(groups):
            sheet_name = group[:31]
            while sheet_name in used_sheet_names:
                suffix = f"-{index}"
                sheet_name = f"{group[:31 - len(suffix)]}{suffix}"
            used_sheet_names.add(sheet_name)
            schedule_db[group].to_excel(writer, sheet_name=sheet_name, index=False)


def _academic_years_from_dates(df):
    if df.columns[0] != 'Дата':
        return set()
    return {
        date.year if date.month >= 8 else date.year - 1
        for value in df['Дата']
        if (date := _dated_schedule_date(value)) is not None
    }


def _academic_year_for_schedule(df):
    """Использует только даты занятий: имя файла может означать год набора."""
    years = _academic_years_from_dates(df)
    return next(iter(years)) if len(years) == 1 else None


def _fresh_academic_year(fresh_db):
    years = set().union(*(_academic_years_from_dates(df) for df in fresh_db.values()))
    return next(iter(years)) if len(years) == 1 else None


def _preserve_missing_schedules(staged_schedules, fresh_db, fresh_mapping):
    """Сохраняет недостающие после ошибок группы в staging и проверяет их.

    Скопированные файлы получают имя с ``!``: при следующем запуске они будут
    прочитаны раньше свежих файлов с числовым префиксом, поэтому свежие данные
    для одной и той же группы всегда имеют приоритет.
    """
    new_year = _fresh_academic_year(fresh_db)
    missing_groups = sorted(
        group for group in set(schedule_db) - set(fresh_db)
        if new_year is None or (
            old_year := _academic_year_for_schedule(schedule_db[group])
        ) is None or old_year >= new_year
    )
    discarded_old_groups = (set(schedule_db) - set(fresh_db)) - set(missing_groups)
    if not missing_groups:
        return fresh_db, fresh_mapping, [], 0

    copied_sources = {}
    groups_without_copy = []
    for group in missing_groups:
        source = group_to_file.get(group)
        destination = copied_sources.get(source)
        if not discarded_old_groups and destination is None and source and os.path.isfile(source):
            destination = os.path.join(
                staged_schedules,
                f"!preserved-{len(copied_sources):03d}-{os.path.basename(source)}",
            )
            try:
                shutil.copy2(source, destination)
            except Exception:
                destination = None
            copied_sources[source] = destination

        if destination:
            continue
        groups_without_copy.append(group)

    if groups_without_copy:
        _write_preserved_groups(
            os.path.join(staged_schedules, "!preserved-memory.xlsx"),
            groups_without_copy,
        )

    verified_db, verified_mapping, verification_errors = _load_schedules_from_dir(staged_schedules)
    unresolved_groups = [group for group in missing_groups if group not in verified_db]
    if unresolved_groups:
        _write_preserved_groups(
            os.path.join(staged_schedules, "!preserved-recovery.xlsx"),
            unresolved_groups,
        )
        verified_db, verified_mapping, recovery_errors = _load_schedules_from_dir(staged_schedules)
        verification_errors.extend(recovery_errors)
        unresolved_groups = [group for group in missing_groups if group not in verified_db]

    if unresolved_groups:
        raise RuntimeError(
            "не удалось сохранить группы для следующего запуска: "
            + ", ".join(unresolved_groups)
        )

    return verified_db, verified_mapping, _unique_errors(verification_errors), len(missing_groups)


def load_from_local():
    """Публикует локальные расписания или скачивает базу при первом запуске."""
    global schedule_db, group_to_file, is_updating
    is_updating = True
    try:
        temp_db, temp_mapping, errors = _load_schedules_from_dir(SCHEDULES_DIR)
        if not temp_db:
            if not any(os.path.exists(path) for path in (SCHEDULES_DIR, RETAKES_DIR)):
                log_to_admin("📥 локальные данные отсутствуют: выполняю первоначальную загрузку")
                return download_schedules()
            log_to_admin("⚠️ база расписаний не обновлена: не распознано ни одной группы")
            return False

        schedule_db, group_to_file = temp_db, temp_mapping
        load_retakes_from_local()
        update_caches()
        log_to_admin(_format_schedule_update_report(len(schedule_db), errors))
        return True
    finally:
        is_updating = False


def _is_retake_url(url):
    filename = urllib.parse.unquote(urllib.parse.urlparse(url).path).lower()
    return any(word in filename for word in ('повтор', 'пересдач', 'аттестац'))


def _download_filename(url, index):
    filename = os.path.basename(urllib.parse.unquote(urllib.parse.urlparse(url).path))
    if not filename:
        raise ValueError("в ссылке нет имени файла")
    return f"{index:03d}_{filename}"


def _replace_data_directories(staging_dir):
    """Подменяет оба каталога и восстанавливает старые данные при сбое."""
    replacements = []
    for real_dir in (SCHEDULES_DIR, RETAKES_DIR):
        name = os.path.basename(os.path.normpath(real_dir))
        replacements.append((real_dir, os.path.join(staging_dir, name)))

    completed = []
    try:
        for real_dir, staged_dir in replacements:
            backup_dir = f"{real_dir}.backup-{os.path.basename(staging_dir)}"
            had_old_dir = os.path.exists(real_dir)
            if had_old_dir:
                os.rename(real_dir, backup_dir)
            try:
                os.rename(staged_dir, real_dir)
            except Exception:
                if had_old_dir and os.path.exists(backup_dir):
                    os.rename(backup_dir, real_dir)
                raise
            completed.append((real_dir, staged_dir, backup_dir, had_old_dir))
    except Exception:
        for real_dir, staged_dir, backup_dir, had_old_dir in reversed(completed):
            if os.path.exists(real_dir):
                os.rename(real_dir, staged_dir)
            if had_old_dir and os.path.exists(backup_dir):
                os.rename(backup_dir, real_dir)
        raise
    else:
        for _, _, backup_dir, had_old_dir in completed:
            if had_old_dir and os.path.exists(backup_dir):
                shutil.rmtree(backup_dir, ignore_errors=True)


def download_schedules():
    """Скачивает полный набор и публикует распознанные расписания.

    Ошибочные файлы и листы не отменяют обновление. В этом случае группы,
    которых нет в свежих данных, сохраняются из опубликованной базы в staging.
    """
    global schedule_db, group_to_file, is_updating
    is_updating = True
    staging_dir = None
    try:
        log_to_admin("🔄 запуск полного обновления базы")
        urls = get_all_schedule_links()
        schedule_urls = [url for url in urls if not _is_retake_url(url)]
        if not schedule_urls:
            log_to_admin("⚠️ не найдено ссылок на расписание; текущая база сохранена")
            return False

        parent_dir = os.path.dirname(os.path.abspath(SCHEDULES_DIR))
        staging_dir = tempfile.mkdtemp(prefix='rgukbot-update-', dir=parent_dir)
        staged_schedules = os.path.join(staging_dir, os.path.basename(os.path.normpath(SCHEDULES_DIR)))
        staged_retakes = os.path.join(staging_dir, os.path.basename(os.path.normpath(RETAKES_DIR)))
        os.makedirs(staged_schedules)
        os.makedirs(staged_retakes)

        failed_urls = []
        downloaded_schedules = 0
        downloaded_retakes = 0
        log_to_admin(f"📥 начинаю скачивание {len(urls)} файлов расписаний и пересдач")
        for index, url in enumerate(urls):
            is_retake = _is_retake_url(url)
            target_dir = staged_retakes if is_retake else staged_schedules
            try:
                response = requests.get(url, timeout=25, verify=False)
                if response.status_code != 200:
                    raise RuntimeError(f"HTTP {response.status_code}")
                if not response.content:
                    raise RuntimeError("получен пустой файл")
                filename = _download_filename(url, index)
                with open(os.path.join(target_dir, filename), 'wb') as file:
                    file.write(response.content)
                if is_retake:
                    downloaded_retakes += 1
                else:
                    downloaded_schedules += 1
            except Exception as error:
                failed_urls.append(url)
                log_to_admin(f"⚠️ не удалось скачать {url}: {error}")

        if failed_urls or downloaded_schedules != len(schedule_urls):
            log_to_admin(
                "⚠️ набор расписаний скачан не полностью; текущая база и файлы сохранены "
                f"({len(failed_urls)} ошибок)"
            )
            return False

        temp_db, temp_mapping, errors = _load_schedules_from_dir(staged_schedules)
        if not temp_db:
            log_to_admin(
                "⚠️ новый набор расписаний не опубликован: не распознано ни одной группы; "
                "текущая база и файлы сохранены"
            )
            return False

        preserved_groups = 0
        if errors:
            temp_db, temp_mapping, preservation_errors, preserved_groups = _preserve_missing_schedules(
                staged_schedules,
                temp_db,
                temp_mapping,
            )
            errors = _unique_errors(errors + preservation_errors)

        if not temp_db:
            log_to_admin("⚠️ новый набор расписаний не опубликован: не распознано ни одной группы")
            return False

        _replace_data_directories(staging_dir)
        final_mapping = {
            group: os.path.join(SCHEDULES_DIR, os.path.basename(filepath))
            for group, filepath in temp_mapping.items()
        }
        schedule_db, group_to_file = temp_db, final_mapping
        load_retakes_from_local()
        update_caches()
        log_to_admin(
            _format_schedule_update_report(
                len(schedule_db),
                errors,
                downloaded_schedules=downloaded_schedules,
                downloaded_retakes=downloaded_retakes,
                preserved_groups=preserved_groups,
            )
        )
        return True
    except Exception as error:
        log_to_admin(f"⚠️ обновление базы отменено: {error}. Текущие данные сохранены")
        return False
    finally:
        if staging_dir and os.path.exists(staging_dir):
            shutil.rmtree(staging_dir, ignore_errors=True)
        is_updating = False


def midnight_updater():
    while True:
        now = datetime.datetime.now()
        target = datetime.datetime.combine(now.date() + datetime.timedelta(days=1), datetime.time(0, 0, 5))
        time.sleep((target - now).total_seconds())
        download_schedules()


# --- генерация расписания ---

def generate_text(group, date):
    df = schedule_db.get(group.lower())
    if df is None: return "❌ группа не найдена"
    wt = get_week_type(date)
    header = f"📅 {DAY_NAMES[date.weekday()]}, {date.strftime('%d.%m.%Y')}\n🔄 {wt} неделя\nгруппа: {group.lower()}\n\n"
    footer = f"\n\n<i>{get_update_time(group)}</i>"
    if date.weekday() == 6 and df.columns[0] != 'Дата':
        return header + "🎉 выходной" + footer

    day_df = _rows_for_date(df, date)
    if day_df.empty: return header + "🏖 пар нет" + footer

    lessons = []
    for row, position in _lesson_rows(day_df):
        try:
            tm = str(row.iloc[2]).strip()
            if len(tm) < 5 or 'nan' in tm.lower(): continue
            info = extract_row_lesson(row, wt)
            if not info['sub']: continue
            lessons.append({'time': tm, **position, **info})
        except Exception:
            continue

    merged = merge_lesson_halves(lessons)
    if not merged: return header + "🏖 пар нет" + footer

    res = ""
    for l in merged:
        res += f"{_lesson_heading(l['num'], l['half'])} ({l['time']})\n"
        res += _format_lesson_body(l['sub'], l['type'], l['tea'], l['room'])
    return header + res.strip() + footer


def generate_retakes_text(group):
    entries = retake_db.get(group.lower())
    if not entries:
        return "график пересдач для твоей группы не был найден. к сожалению, формат графиков пересдач не унифицирован и файл с ним часто бывает в формате .pdf, с чем этот бот работать не умеет, поэтому посети сайт https://rguk.ru/students/schedule/ и поищи свой график там"

    entries_sorted = sorted(entries, key=lambda x: (x['date'], x['time']))
    merged = merge_lesson_halves(entries_sorted)

    res = f"📑 <b>расписание пересдач для группы {group.lower()}:</b>\n\n"
    for l in merged:
        res += f"📅 {l['date']} | ⏰ {l['time']}\n"
        res += _format_lesson_body(l['sub'], l['type'], l['tea'], l['room'])

    footer = f"<i>{global_update_time_ret}</i>"
    return res + footer


def generate_teacher_text(teacher_full_name, date):
    if teacher_full_name.lower() in _REJECTED_TEACHERS:
        return "❌ не смешно"
    wt = get_week_type(date)
    all_merged_lessons = []
    teacher_lower = teacher_full_name.strip().lower()

    for gr, df in schedule_db.items():
        day_df = _rows_for_date(df, date)
        group_lessons = []
        for row, position in _lesson_rows(day_df):
            try:
                info = extract_row_lesson(row, wt)
                if info['tea'] != teacher_lower: continue
                tm = str(row.iloc[2]).strip()
                if len(tm) < 5: continue
                group_lessons.append({'time': tm, **position, 'sub': info['sub'],
                                      'room': info['room'], 'type': info['type'], 'group': gr})
            except Exception:
                continue
        merged_grp = merge_lesson_halves(group_lessons)
        all_merged_lessons.extend(merged_grp)

    header = f"👨‍🏫 <b>{teacher_full_name.lower()}</b>\n📅 {DAY_NAMES[date.weekday()]}, {date.strftime('%d.%m.%Y')}\n🔄 {wt} неделя\n\n"
    footer = f"\n\n<i>{global_update_time_sch}</i>"
    if not all_merged_lessons: return header + "занятий не найдено" + footer

    grouped = {}
    for m in all_merged_lessons:
        key = (m['time'], m['num'], m['half'], m['sub'], m['room'], m['type'])
        if key not in grouped: grouped[key] = set()
        grouped[key].add(m['group'])

    res = ""
    for (tm, num, half, sub, room, tp), groups in sorted(grouped.items(), key=lambda item: item[0][0]):
        res += f"{_lesson_heading(num, half)} ({tm}) — гр. {', '.join(sorted(groups))}\n"
        res += _format_lesson_body(sub, tp, room=room)
    return header + res.strip() + footer


def generate_room_text(room, date):
    wt = get_week_type(date)
    header = (f"🚪 аудитория: <b>{room.lower()}</b>\n"
              f"📅 {DAY_NAMES[date.weekday()]}, {date.strftime('%d.%m.%Y')}\n"
              f"🔄 {wt} неделя\n\n")
    footer = f"\n\n<i>{global_update_time_sch}</i>"

    if date.weekday() == 6 and not any(
        df.columns[0] == 'Дата' and not _rows_for_date(df, date).empty
        for df in schedule_db.values()
    ):
        return header + "🎉 выходной — аудитория свободна весь день" + footer

    room_lower = room.strip().lower()
    grouped = {}
    for gr, df in schedule_db.items():
        day_df = _rows_for_date(df, date)
        for row, position in _lesson_rows(day_df):
            try:
                tm = str(row.iloc[2]).strip()
                if len(tm) < 5 or 'nan' in tm.lower():
                    continue
                info = extract_row_lesson(row, wt)
                if info['room'].lower() != room_lower or not info['sub']:
                    continue
                key = (tm, position['num'], position['half'], info['sub'], info['tea'], info['type'])
                if key not in grouped:
                    grouped[key] = {'time': tm, **position,
                                    'sub': info['sub'], 'tea': info['tea'],
                                    'type': info['type'], 'groups': set()}
                grouped[key]['groups'].add(gr)
            except Exception:
                continue

    flat = sorted(grouped.values(), key=lambda x: x['time'])
    merged = merge_lesson_halves(flat, ('groups',))

    occupied_slot_nums = set()
    for l in merged:
        for i, (emoji, _, _) in enumerate(LESSON_SLOTS):
            if l['num'].startswith(emoji):
                occupied_slot_nums.add(i)

    res = ""
    if merged:
        res += "<b>занято:</b>\n\n"
        for l in merged:
            groups_str = ", ".join(sorted(l['groups']))
            res += f"{_lesson_heading(l['num'], l['half'])} ({l['time']}) — гр. {groups_str}\n"
            res += _format_lesson_body(l['sub'], l['type'], tea=l['tea'])

    free_slots = [s for i, s in enumerate(LESSON_SLOTS) if i not in occupied_slot_nums]
    if free_slots:
        res += "<b>свободна:</b>\n\n"
        for emoji, start, end in free_slots:
            res += f"{emoji} {start} – {end}\n"
    elif merged:
        res += "⚠️ аудитория занята все пары"
    else:
        res += "✅ аудитория свободна весь день"

    return header + res.strip() + footer


# --- обработчики бота ---

def _check_cancel(m, text):
    if m.text.lower() == "❌ отмена":
        bot.send_message(m.chat.id, text, reply_markup=main_kb())
        return True
    return False


def admin_only(denial=None):
    def decorate(func):
        @wraps(func)
        def wrapper(m):
            if m.from_user.id == ADMIN_ID:
                return func(m)
            if denial:
                bot.send_message(m.chat.id, denial)
        return wrapper
    return decorate


@bot.message_handler(func=lambda m: is_updating)
def bot_blocked(m):
    bot.send_message(m.chat.id, "⏳ идет обновление базы данных, пожалуйста, подожди")


@bot.message_handler(commands=['info'])
@admin_only()
def admin_info(m):
    files_sch = os.listdir(SCHEDULES_DIR) if os.path.exists(SCHEDULES_DIR) else []
    files_ret = os.listdir(RETAKES_DIR) if os.path.exists(RETAKES_DIR) else []

    f_text_sch = "\n".join([f"📄 {f}" for f in files_sch]) if files_sch else "пусто"
    f_text_ret = "\n".join([f"📑 {f}" for f in files_ret]) if files_ret else "пусто"

    text = (f"📊 <b>инфо:</b>\n👥 юзеров: {len(get_all_users())}\n"
            f"📚 групп (основа): {len(schedule_db)}\n"
            f"📚 групп (пересдачи): {len(retake_db)}\n\n"
            f"📁 <b>основные файлы:</b>\n{f_text_sch}\n\n"
            f"📁 <b>файлы пересдач:</b>\n{f_text_ret}")
    bot.send_message(m.chat.id, text, parse_mode='HTML')


@bot.message_handler(commands=['achtung'])
@admin_only("⛔️ у тебя нет прав на использование этой команды")
def admin_broadcast(m):
    text = m.text.replace('/achtung', '').strip()
    if not text:
        help_text = ("ты не ввел текст для рассылки\n\n"
                     "использование: /achtung <текст>\n"
                     "примеры использования html:\n"
                     "<b>жирный</b>\n"
                     "<i>курсив</i>\n"
                     "<u>подчеркнутый</u>\n"
                     "<s>зачеркнутый</s>\n"
                     "<tg-spoiler>спойлер</tg-spoiler>\n"
                     "<a href='http://example.com'>ссылка</a>\n"
                     "внимание: теги обязательно закрывать!")
        bot.send_message(m.chat.id, help_text)
        return

    users = get_all_users()
    success_count = 0
    bot.send_message(m.chat.id, f"начинаю рассылку для {len(users)} пользователей")

    for user_id in users:
        try:
            bot.send_message(user_id, text, parse_mode='HTML')
            success_count += 1
            time.sleep(0.05)
        except Exception:
            delete_user(user_id)

    bot.send_message(m.chat.id, f"✅ рассылка завершена, доставлено: {success_count} из {len(users)}")


@bot.message_handler(commands=['update'])
@admin_only()
def admin_update(m):
    bot.send_message(m.chat.id, "🔄 запуск обновления")
    Thread(target=download_schedules, daemon=True).start()


@bot.message_handler(commands=['delete'])
def delete_cmd(m):
    bot.send_message(m.chat.id,
                     "❗ перед удалением связки: ты всегда можешь ввести /start, чтобы начать работу с ботом снова")
    delete_user(m.from_user.id)
    bot.send_message(m.chat.id, "✅ данные успешно удалены")


@bot.message_handler(func=lambda m: m.text.lower() == "📄 график пересдач")
def search_retakes(m):
    g = get_user_group(m.from_user.id)
    if not g:
        bot.send_message(m.chat.id, "❗ сначала выбери группу")
        return
    text = generate_retakes_text(g)
    bot.send_message(m.chat.id, text, parse_mode='HTML')


@bot.message_handler(func=lambda m: m.text.lower() == "👩‍🎓 расписание преподавателя")
def teacher_search_start(m):
    msg = bot.send_message(m.chat.id, "📝 введи фамилию преподавателя:", reply_markup=cancel_kb())
    bot.register_next_step_handler(msg, teacher_name_filter)


def _entity_search_filter(m, view_type):
    if _check_cancel(m, "❌ поиск отменен"): return
    q = m.text.strip().lower()
    if view_type == 't':
        if q in _REJECTED_TEACHERS:
            bot.send_message(m.chat.id, "❌ не смешно", reply_markup=main_kb())
            return
        cache, min_len, prefix, limit = all_teachers_cache, 3, "teach_sel", 10
        next_step = teacher_name_filter
        short_text, noun, found_word = "❌ минимум 3 буквы", "преподаватель", "найден"
    else:
        cache, min_len, prefix, limit = all_rooms_cache, 1, "room_sel", 15
        next_step = process_room_search
        short_text, noun, found_word = "❌ введи хотя бы 1 символ", "аудитория", "найдена"
    if len(q) < min_len:
        msg = bot.send_message(m.chat.id, short_text, reply_markup=cancel_kb())
        bot.register_next_step_handler(msg, next_step)
        return

    found = [value for value in cache if q in value.lower()]
    if view_type == 'r': found.sort()
    if not found:
        bot.send_message(m.chat.id, f"❌ {noun} не {found_word}", reply_markup=main_kb())
    elif len(found) > 1:
        kb = make_selection_kb(found, prefix, max_items=limit)
        bot.send_message(m.chat.id, "❗ найдено несколько, выбери:", reply_markup=cancel_kb())
        bot.send_message(m.chat.id, "варианты:", reply_markup=kb)
        bot.register_next_step_handler(m, next_step)
    else:
        bot.clear_step_handler_by_chat_id(m.chat.id)
        bot.send_message(m.chat.id, f"✅ {noun} {found_word}", reply_markup=main_kb())
        text, kb = get_schedule_view(view_type, found[0], get_target_date())
        bot.send_message(m.chat.id, text, parse_mode='HTML', reply_markup=kb)


def teacher_name_filter(m):
    _entity_search_filter(m, 't')


def _entity_sel_callback(c, view_type):
    bot.answer_callback_query(c.id)
    bot.clear_step_handler_by_chat_id(c.message.chat.id)
    name = c.data.split('|')[1]
    if view_type == 't' and name.lower() in _REJECTED_TEACHERS:
        bot.send_message(c.message.chat.id, "❌ не смешно", reply_markup=main_kb())
        return
    selected = "✅ расписание выбрано" if view_type == 't' else "✅ аудитория выбрана"
    bot.send_message(c.message.chat.id, selected, reply_markup=main_kb())
    text, kb = get_schedule_view(view_type, name, get_target_date())
    bot.send_message(c.message.chat.id, text, parse_mode='HTML', reply_markup=kb)


@bot.callback_query_handler(func=lambda c: c.data.startswith('teach_sel|'))
def teacher_sel_callback(c):
    _entity_sel_callback(c, 't')


@bot.callback_query_handler(func=lambda c: c.data.startswith('c|'))
def custom_date_cb(c):
    bot.answer_callback_query(c.id)
    _, p, target = c.data.split('|')
    msg = bot.send_message(c.message.chat.id,
                           "📝 введи дату или день недели цифрами или словами:\n\n<i>('след вт', 'пт через 2 недели', 'ср неделю назад')</i>",
                           parse_mode='HTML',
                           reply_markup=cancel_kb())
    bot.register_next_step_handler(msg, process_custom_date, p, target)


def process_custom_date(m, p, target):
    if _check_cancel(m, "❌ поиск по дате отменен"): return

    date = parse_user_date(m.text)
    if date:
        bot.send_message(m.chat.id, "🔖 расписание на указанную дату:", reply_markup=main_kb())
        text, kb = get_schedule_view(p, target, date)
        bot.send_message(m.chat.id, text, parse_mode='HTML', reply_markup=kb)
    else:
        msg = bot.send_message(m.chat.id,
                               "❌ неверный формат или дата.\n\nвведи дату заново либо нажми отмена.",
                               reply_markup=cancel_kb())
        bot.register_next_step_handler(msg, process_custom_date, p, target)


@bot.message_handler(func=lambda m: m.text.lower() == "🔄 сменить группу")
def change_grp(m):
    msg = bot.send_message(m.chat.id, "📝 напиши название новой группы:", reply_markup=cancel_kb())
    bot.register_next_step_handler(msg, handle_group_input)


def handle_group_input(m):
    if _check_cancel(m, "❌ отменено"): return
    text = m.text.strip().lower()
    found = next((k for k in schedule_db if k.replace("-", "") == text.replace("-", "")), None)
    if found:
        set_user_group(m.from_user.id, found)
        bot.send_message(m.chat.id, f"✅ группа {found} сохранена", reply_markup=main_kb())
        text, kb = get_schedule_view('d', found, get_target_date())
        bot.send_message(m.chat.id, text, parse_mode='HTML', reply_markup=kb)
    else:
        bot.send_message(m.chat.id, "😢 группа не найдена, попробуй еще раз через меню", reply_markup=main_kb())


@bot.message_handler(func=lambda m: m.text.lower() == "📅 моё расписание")
def my_sched(m):
    g = get_user_group(m.from_user.id)
    if not g:
        bot.send_message(m.chat.id, "❗ сначала выбери группу")
        return
    text, kb = get_schedule_view('d', g, get_target_date())
    bot.send_message(m.chat.id, text, parse_mode='HTML', reply_markup=kb)


@bot.callback_query_handler(func=lambda c: c.data.startswith(('d|', 't|', 'r|')))
def nav_cb_handler(c):
    m, t, d_s = c.data.split('|')
    date = datetime.datetime.strptime(d_s, '%Y-%m-%d').date()
    text, kb = get_schedule_view(m, t, date)
    try:
        bot.edit_message_text(text, c.message.chat.id, c.message.message_id, reply_markup=kb, parse_mode='HTML')
    except Exception:
        pass


@bot.message_handler(commands=['start'])
def start(m):
    msg = (f"привет! 👋\n\nэтот <b>неофициальный</b> бот показывает расписание для студентов ргу им. косыгина\n\n"
           f"просто <b>напиши название своей группы</b> (например: эби-124) и я тебя запомню!\n\n\n\n"
           f"<i>⚠️ внимание: бот сохраняет связку твоего id и выбранной группы. ты можешь удалить свои данные в любой момент с помощью команды /delete.</i>")
    bot.send_message(m.chat.id, msg, parse_mode='HTML', reply_markup=main_kb())


@bot.message_handler(func=lambda m: m.text.lower() == "🚪 поиск аудитории")
def room_search_start(m):
    msg = bot.send_message(m.chat.id, "📝 введи номер аудитории:", reply_markup=cancel_kb())
    bot.register_next_step_handler(msg, process_room_search)


def process_room_search(m):
    _entity_search_filter(m, 'r')


@bot.callback_query_handler(func=lambda c: c.data.startswith('room_sel|'))
def room_sel_callback(c):
    _entity_sel_callback(c, 'r')


@bot.message_handler(func=lambda m: True)
def last_handle(m):
    handle_group_input(m)


# --- запуск ---
if __name__ == '__main__':
    log_to_admin("⏳ бот готовится к запуску…")
    init_db()
    load_from_local()

    Thread(target=midnight_updater, daemon=True).start()

    print("бот запущен и готов к работе!")
    while True:
        try:
            bot.polling(none_stop=True, interval=0, timeout=20)
        except Exception as e:
            print(f"[{datetime.datetime.now()}] ошибка подключения: {e}")
            time.sleep(5)
            print("попытка переподключения...")
