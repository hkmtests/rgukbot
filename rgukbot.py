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
from threading import Thread
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
SCHEDULE_PAGE_URL = "https://rguk.ru/students/schedule/"
SCHEDULES_DIR = 'schedules_folder'
RETAKES_DIR = 'retakes_folder'
DB_PATH = 'users_vuz.db'

# --- базы данных ---
schedule_db = {}
retake_db = {}
group_to_file = {}
all_rooms_cache = []
all_teachers_cache = []
global_update_time_sch = ""
global_update_time_ret = ""
is_updating = False

# --- константы ---
DAY_NAMES = {0: 'понедельник', 1: 'вторник', 2: 'среда', 3: 'четверг', 4: 'пятница', 5: 'суббота', 6: 'воскресенье'}
DAY_SHORTS = {0: 'ПН', 1: 'ВТ', 2: 'СР', 3: 'ЧТ', 4: 'ПТ', 5: 'СБ'}

TYPE_EXPAND = {
    'пр': 'практика', 'лек': 'лекция', 'прак': 'практика',
    'лаб': 'лабораторная', 'сем': 'семинар', 'конс': 'консультация',
    'экз': 'экзамен', 'зач': 'зачёт',
}

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
        bot.send_message(ADMIN_ID, f"<code>[system]</code> {text}", parse_mode='HTML')
    except Exception:
        pass


def get_update_time_global():
    return global_update_time_sch


def get_update_time_global_retakes():
    return global_update_time_ret


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


def get_lesson_number(time_str):
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
    if wt == "нечетная":
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


def merge_lesson_halves(lessons, match_keys=('sub', 'room')):
    """Объединяет половинки пар (например, 1️⃣ и 🔹) в один диапазон времени."""
    merged = []
    can_m = True
    for c in lessons:
        item = c.copy() if isinstance(c, dict) else c
        if not merged:
            merged.append(item)
            continue
        p = merged[-1]
        is_match = all(p.get(k) == item.get(k) for k in match_keys)
        if is_match and not p['num'].startswith("🔹") and item['num'].startswith("🔹") and can_m:
            t1 = p['time'].split('-')[0] if '-' in p['time'] else p['time']
            t2 = item['time'].split('-')[1] if '-' in item['time'] else item['time']
            p['time'] = f"{t1}-{t2}"
            can_m = False
        else:
            merged.append(item)
            can_m = True
    return merged


def parse_user_date(text: str) -> datetime.date | None:
    """Распознает дату из строки: дни недели, относительные смещения, словесные и числовые даты."""
    if not text:
        return None
    text_lower = text.strip().lower()

    months = {
        "января": 1, "февраля": 2, "марта": 3, "апреля": 4, "мая": 5, "июня": 6,
        "июля": 7, "августа": 8, "сентября": 9, "октября": 10, "ноября": 11, "декабря": 12
    }

    days_of_week = {
        "пн": 0, "понедельник": 0, "вт": 1, "вторник": 1, "ср": 2, "среда": 2, "среду": 2,
        "чт": 3, "четверг": 3, "пт": 4, "пятница": 4, "пятницу": 4, "сб": 5, "суббота": 5,
        "субботу": 5, "вс": 6, "воскресенье": 6
    }

    parts = text_lower.split()
    target_wd = None
    has_next = False
    weeks_offset = 0

    word_to_num = {
        "одну": 1, "одной": 1, "одна": 1, "один": 1, "две": 2, "два": 2, "двух": 2,
        "три": 3, "трёх": 3, "трех": 3, "четыре": 4, "четырёх": 4, "четырех": 4,
        "пять": 5, "пяти": 5, "шесть": 6, "шести": 6, "семь": 7, "семи": 7,
        "восемь": 8, "восьми": 8, "девять": 9, "девяти": 9, "десять": 10, "десяти": 10,
    }

    for word in parts:
        if word in days_of_week:
            target_wd = days_of_week[word]

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
                elif parts[j] in word_to_num:
                    weeks_offset = word_to_num[parts[j]]
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
                elif parts[j] in word_to_num:
                    num_found = word_to_num[parts[j]]
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
    if len(parts) == 3 and parts[1] in months and parts[0].isdigit() and parts[2].isdigit():
        return datetime.date(int(parts[2]), months[parts[1]], int(parts[0]))

    # 2. формат: 15 марта
    if len(parts) == 2 and parts[1] in months and parts[0].isdigit():
        day, month = int(parts[0]), months[parts[1]]
        now = datetime.datetime.now().date()
        target_date = datetime.date(now.year, month, day)
        if (target_date - now).days > 180:
            target_date = datetime.date(now.year - 1, month, day)
        return target_date

    # 3. форматы с точкой (15.03.2026 или 15.03)
    if "." in text_lower:
        dot_parts = [dp for dp in text_lower.split(".") if dp.isdigit()]
        if len(dot_parts) == 3:
            d, m_num, y = map(int, dot_parts)
            if y < 100: y += 2000
            return datetime.date(y, m_num, d)
        elif len(dot_parts) == 2:
            day, month = map(int, dot_parts)
            now = datetime.datetime.now().date()
            target_date = datetime.date(now.year, month, day)
            if (target_date - now).days > 180:
                target_date = datetime.date(now.year - 1, month, day)
            return target_date

    return None


def get_schedule_view(target_type, target, date):
    """Единый диспетчер для формирования текста расписания и клавиатуры навигации."""
    prefix = get_warnings(date)
    if target_type == 'r':
        text = prefix + generate_room_text(target, date)
        kb = nav_kb(target, date, is_room=True)
    elif target_type == 't':
        text = prefix + generate_teacher_text(target, date)
        kb = nav_kb(target, date, is_teacher=True)
    else:
        text = prefix + generate_text(target, date)
        kb = nav_kb(target, date)
    return text, kb


def get_all_rooms():
    return all_rooms_cache


def update_caches():
    """Обновляет кэш аудиторий, преподавателей и времени обновления файлов."""
    global all_rooms_cache, all_teachers_cache, global_update_time_sch, global_update_time_ret
    rooms = set()
    teachers = set()
    for df in schedule_db.values():
        for col_idx in [3, 10]:
            try:
                for val in df.iloc[:, col_idx].dropna().unique():
                    r = str(val).strip()
                    if r.endswith('.0'): r = r[:-2]
                    if r and r.lower() != 'nan':
                        rooms.add(r)
            except Exception:
                continue
        for col_idx in [5, 8]:
            try:
                for n in df.iloc[:, col_idx].dropna().unique():
                    t = str(n).strip()
                    if t and t.lower() != 'nan':
                        teachers.add(t)
            except Exception:
                continue
    all_rooms_cache = sorted(list(rooms))
    all_teachers_cache = sorted(list(teachers))

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


def nav_kb(target, date, is_teacher=False, is_room=False):
    kb = InlineKeyboardMarkup()
    p = "r" if is_room else ("t" if is_teacher else "d")
    kb.row(
        InlineKeyboardButton("⬅️", callback_data=f"{p}|{target}|{date - datetime.timedelta(days=1)}"),
        InlineKeyboardButton("📅", callback_data=f"c|{p}|{target}"),
        InlineKeyboardButton("➡️", callback_data=f"{p}|{target}|{date + datetime.timedelta(days=1)}")
    )
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

def init_db():
    with sqlite3.connect(DB_PATH) as conn:
        conn.execute("""CREATE TABLE IF NOT EXISTS users (
                            user_id INTEGER PRIMARY KEY,
                            group_name TEXT
                        )""")


def set_user_group(user_id, group_name):
    with sqlite3.connect(DB_PATH) as conn:
        conn.execute("REPLACE INTO users (user_id, group_name) VALUES (?, ?)", (user_id, group_name.lower()))


def get_user_group(user_id):
    with sqlite3.connect(DB_PATH) as conn:
        res = conn.execute("SELECT group_name FROM users WHERE user_id = ?", (user_id,)).fetchone()
        return res[0] if res else None


def get_all_users():
    with sqlite3.connect(DB_PATH) as conn:
        return [r[0] for r in conn.execute("SELECT user_id FROM users").fetchall()]


def delete_user(user_id):
    with sqlite3.connect(DB_PATH) as conn:
        conn.execute("DELETE FROM users WHERE user_id = ?", (user_id,))


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


def load_from_local():
    global schedule_db, group_to_file, is_updating
    is_updating = True
    temp_db, temp_mapping = {}, {}
    files = glob.glob(os.path.join(SCHEDULES_DIR, "*.xlsx"))

    if not files:
        is_updating = False
        return False

    log_to_admin(f"📂 загрузка данных из {len(files)} файлов")
    for filepath in files:
        try:
            xls = pd.ExcelFile(filepath, engine='openpyxl')
            for sheet in xls.sheet_names:
                try:
                    df_raw = pd.read_excel(xls, sheet_name=sheet, header=None)
                    mask = df_raw.apply(lambda r: r.astype(str).str.contains('день недели', case=False, na=False).any(), axis=1)
                    if not mask.any(): continue
                    h_idx = df_raw[mask].index[0]
                    df = pd.read_excel(xls, sheet_name=sheet, header=h_idx)
                    df = df.dropna(how='all', axis=1)
                    d_col = df.columns[0]
                    df[d_col] = df[d_col].astype(str).str.strip().str.upper()
                    df.loc[~df[d_col].isin(['ПН', 'ВТ', 'СР', 'ЧТ', 'ПТ', 'СБ']), d_col] = None
                    df[d_col] = df[d_col].ffill()
                    group_key = sheet.strip().lower()
                    temp_db[group_key], temp_mapping[group_key] = df, filepath
                except Exception:
                    continue
        except Exception:
            continue

    if temp_db:
        schedule_db, group_to_file = temp_db, temp_mapping
        log_to_admin(f"🏁 база обновлена! групп: {len(schedule_db)}")

    load_retakes_from_local()
    update_caches()
    is_updating = False
    return True


def download_schedules():
    global is_updating, schedule_db, group_to_file, retake_db
    is_updating = True
    log_to_admin("🔄 запуск полного обновления базы")
    schedule_db.clear()
    group_to_file.clear()
    retake_db.clear()

    for d in [SCHEDULES_DIR, RETAKES_DIR]:
        os.makedirs(d, exist_ok=True)
        for f in glob.glob(os.path.join(d, "*")):
            try:
                os.remove(f)
            except Exception:
                pass

    urls = get_all_schedule_links()
    sch_count = 0
    ret_count = 0

    log_to_admin("📥 начинаю скачивание файлов расписаний и пересдач")
    for url in urls:
        filename = urllib.parse.unquote(url.split('/')[-1])
        is_retake = any(w in filename.lower() for w in ('повтор', 'пересдач', 'аттестац'))
        target_dir = RETAKES_DIR if is_retake else SCHEDULES_DIR
        try:
            resp = requests.get(url, timeout=25, verify=False)
            if resp.status_code == 200:
                with open(os.path.join(target_dir, filename), 'wb') as f:
                    f.write(resp.content)
                if is_retake:
                    ret_count += 1
                else:
                    sch_count += 1
        except Exception:
            pass

    log_to_admin(f"✅ скачано: {sch_count} расписаний, {ret_count} пересдач")
    load_from_local()


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
    if date.weekday() == 6: return header + "🎉 выходной" + footer

    day_df = df[df[df.columns[0]] == DAY_SHORTS.get(date.weekday())]
    if day_df.empty: return header + "🏖 пар нет" + footer

    lessons = []
    for _, row in day_df.iterrows():
        try:
            tm = str(row.iloc[2]).strip()
            if len(tm) < 5 or 'nan' in tm.lower(): continue
            info = extract_row_lesson(row, wt)
            if not info['sub']: continue
            lessons.append({'time': tm, 'num': get_lesson_number(tm), **info})
        except Exception:
            continue

    merged = merge_lesson_halves(lessons, ('sub', 'room'))
    if not merged: return header + "🏖 пар нет" + footer

    res = ""
    for l in merged:
        res += f"{l['num']} ({l['time']})\n📚 <b>{l['sub']}</b>\n"
        if l['type']: res += f"  📝 {TYPE_EXPAND.get(l['type'].lower(), l['type'])}\n"
        if l['tea']:  res += f"  👨‍🏫 {l['tea']}\n"
        if l['room']: res += f"  🚪 {l['room']}\n"
        res += "\n"
    return header + res.strip() + footer


def generate_retakes_text(group):
    entries = retake_db.get(group.lower())
    if not entries:
        return "график пересдач для твоей группы не был найден. к сожалению, формат графиков пересдач не унифицирован и файл с ним часто бывает в формате .pdf, с чем этот бот работать не умеет, поэтому посети сайт https://rguk.ru/students/schedule/ и поищи свой график там"

    entries_sorted = sorted(entries, key=lambda x: (x['date'], x['time']))
    merged = merge_lesson_halves(entries_sorted, ('date', 'sub', 'room'))

    res = f"📑 <b>расписание пересдач для группы {group.lower()}:</b>\n\n"
    for l in merged:
        res += f"📅 {l['date']} | ⏰ {l['time']}\n📚 <b>{l['sub']}</b>\n"
        if l['type']: res += f"  📝 {TYPE_EXPAND.get(l['type'].lower(), l['type'])}\n"
        if l['tea']:  res += f"  👨‍🏫 {l['tea']}\n"
        if l['room']: res += f"  🚪 {l['room']}\n"
        res += "\n"

    footer = f"<i>{get_update_time_global_retakes()}</i>"
    return res + footer


def generate_teacher_text(teacher_full_name, date):
    if teacher_full_name.lower() in ("преподаватель кафедры", "препод. кафедры"):
        return "❌ не смешно"
    wt = get_week_type(date)
    all_merged_lessons = []
    teacher_lower = teacher_full_name.strip().lower()

    for gr, df in schedule_db.items():
        day_df = df[df[df.columns[0]] == DAY_SHORTS.get(date.weekday())]
        group_lessons = []
        for _, row in day_df.iterrows():
            try:
                info = extract_row_lesson(row, wt)
                if info['tea'] != teacher_lower: continue
                tm = str(row.iloc[2]).strip()
                if len(tm) < 5: continue
                group_lessons.append({'time': tm, 'num': get_lesson_number(tm), 'sub': info['sub'],
                                      'room': info['room'], 'type': info['type'], 'group': gr})
            except Exception:
                continue
        merged_grp = merge_lesson_halves(group_lessons, ('sub', 'room'))
        all_merged_lessons.extend(merged_grp)

    header = f"👨‍🏫 <b>{teacher_full_name.lower()}</b>\n📅 {DAY_NAMES[date.weekday()]}, {date.strftime('%d.%m.%Y')}\n🔄 {wt} неделя\n\n"
    footer = f"\n\n<i>{get_update_time_global()}</i>"
    if not all_merged_lessons: return header + "занятий не найдено" + footer

    grouped = {}
    for m in all_merged_lessons:
        key = (m['time'], m['num'], m['sub'], m['room'], m['type'])
        if key not in grouped: grouped[key] = set()
        grouped[key].add(m['group'])

    flat = sorted(
        [{'time': k[0], 'num': k[1], 'sub': k[2], 'room': k[3], 'type': k[4], 'groups': sorted(list(g))}
         for k, g in grouped.items()], key=lambda x: x['time'])
    res = ""
    for l in flat:
        res += f"{l['num']} ({l['time']}) — гр. {', '.join(l['groups'])}\n📚 <b>{l['sub']}</b>\n"
        if l['type']: res += f"  📝 {TYPE_EXPAND.get(l['type'].lower(), l['type'])}\n"
        if l['room']: res += f"  🚪 {l['room']}\n"
        res += "\n"
    return header + res.strip() + footer


def generate_room_text(room, date):
    wt = get_week_type(date)
    header = (f"🚪 аудитория: <b>{room.lower()}</b>\n"
              f"📅 {DAY_NAMES[date.weekday()]}, {date.strftime('%d.%m.%Y')}\n"
              f"🔄 {wt} неделя\n\n")
    footer = f"\n\n<i>{get_update_time_global()}</i>"

    if date.weekday() == 6:
        return header + "🎉 выходной — аудитория свободна весь день" + footer

    room_lower = room.strip().lower()
    occupied = []
    for gr, df in schedule_db.items():
        day_df = df[df[df.columns[0]] == DAY_SHORTS.get(date.weekday())]
        for _, row in day_df.iterrows():
            try:
                tm = str(row.iloc[2]).strip()
                if len(tm) < 5 or 'nan' in tm.lower():
                    continue
                info = extract_row_lesson(row, wt)
                if info['room'].lower() != room_lower or not info['sub']:
                    continue
                occupied.append({
                    'time': tm,
                    'num': get_lesson_number(tm),
                    'sub': info['sub'],
                    'tea': info['tea'],
                    'type': info['type'],
                    'group': gr
                })
            except Exception:
                continue

    grouped = {}
    for o in occupied:
        key = (o['time'], o['sub'], o['tea'], o['type'])
        if key not in grouped:
            grouped[key] = {'time': o['time'], 'num': o['num'], 'sub': o['sub'],
                            'tea': o['tea'], 'type': o['type'], 'groups': set()}
        grouped[key]['groups'].add(o['group'])

    flat = sorted(grouped.values(), key=lambda x: x['time'])
    merged = merge_lesson_halves(flat, ('tea', 'type', 'groups'))

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
            tp = TYPE_EXPAND.get(l['type'].lower(), l['type']) if l['type'] else ""
            res += f"{l['num']} ({l['time']}) — гр. {groups_str}\n📚 <b>{l['sub']}</b>\n"
            if tp:
                res += f"  📝 {tp}\n"
            if l['tea']:
                res += f"  👨‍🏫 {l['tea']}\n"
            res += "\n"

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

@bot.message_handler(func=lambda m: is_updating)
def bot_blocked(m):
    bot.send_message(m.chat.id, "⏳ идет обновление базы данных, пожалуйста, подожди")


@bot.message_handler(commands=['info'])
def admin_info(m):
    if m.from_user.id != ADMIN_ID: return
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
def admin_broadcast(m):
    if m.from_user.id == ADMIN_ID:
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
    else:
        bot.send_message(m.chat.id, "⛔️ у тебя нет прав на использование этой команды")


@bot.message_handler(commands=['update'])
def admin_update(m):
    if m.from_user.id == ADMIN_ID:
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


def teacher_name_filter(m):
    if m.text.lower() == "❌ отмена":
        bot.send_message(m.chat.id, "❌ поиск отменен", reply_markup=main_kb())
        return
    q = m.text.strip().lower()
    if q in ("преподаватель кафедры", "препод. кафедры"):
        bot.send_message(m.chat.id, "❌ не смешно", reply_markup=main_kb())
        return
    if len(q) < 3:
        msg = bot.send_message(m.chat.id, "❌ минимум 3 буквы", reply_markup=cancel_kb())
        bot.register_next_step_handler(msg, teacher_name_filter)
        return

    found = [t for t in all_teachers_cache if q in t.lower()]
    if not found:
        bot.send_message(m.chat.id, "❌ преподаватель не найден", reply_markup=main_kb())
    elif len(found) > 1:
        kb = make_selection_kb(found, "teach_sel", max_items=10)
        bot.send_message(m.chat.id, "❗ найдено несколько, выбери:", reply_markup=cancel_kb())
        bot.send_message(m.chat.id, "варианты:", reply_markup=kb)
        bot.register_next_step_handler(m, teacher_name_filter)
    else:
        bot.clear_step_handler_by_chat_id(m.chat.id)
        teacher = found[0]
        bot.send_message(m.chat.id, "✅ преподаватель найден", reply_markup=main_kb())
        text, kb = get_schedule_view('t', teacher, get_target_date())
        bot.send_message(m.chat.id, text, parse_mode='HTML', reply_markup=kb)


@bot.callback_query_handler(func=lambda c: c.data.startswith('teach_sel|'))
def teacher_sel_callback(c):
    bot.answer_callback_query(c.id)
    bot.clear_step_handler_by_chat_id(c.message.chat.id)
    name = c.data.split('|')[1]
    if name.lower() in ("преподаватель кафедры", "препод. кафедры"):
        bot.send_message(c.message.chat.id, "❌ не смешно", reply_markup=main_kb())
        return
    bot.send_message(c.message.chat.id, "✅ расписание выбрано", reply_markup=main_kb())
    text, kb = get_schedule_view('t', name, get_target_date())
    bot.send_message(c.message.chat.id, text, parse_mode='HTML', reply_markup=kb)


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
    if m.text.lower() == "❌ отмена":
        bot.send_message(m.chat.id, "❌ поиск по дате отменен", reply_markup=main_kb())
        return

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
    if m.text.lower() == "❌ отмена":
        bot.send_message(m.chat.id, "❌ отменено", reply_markup=main_kb())
        return
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
    if m.text.lower() == "❌ отмена":
        bot.send_message(m.chat.id, "❌ поиск отменен", reply_markup=main_kb())
        return
    q = m.text.strip().lower()
    if len(q) < 1:
        msg = bot.send_message(m.chat.id, "❌ введи хотя бы 1 символ", reply_markup=cancel_kb())
        bot.register_next_step_handler(msg, process_room_search)
        return

    all_rooms = get_all_rooms()
    found = sorted([r for r in all_rooms if q in r.lower()])

    if not found:
        bot.send_message(m.chat.id, "❌ аудитория не найдена", reply_markup=main_kb())
    elif len(found) > 1:
        kb = make_selection_kb(found, "room_sel", max_items=15)
        bot.send_message(m.chat.id, "❗ найдено несколько, выбери:", reply_markup=cancel_kb())
        bot.send_message(m.chat.id, "варианты:", reply_markup=kb)
        bot.register_next_step_handler(m, process_room_search)
    else:
        bot.clear_step_handler_by_chat_id(m.chat.id)
        room = found[0]
        bot.send_message(m.chat.id, "✅ аудитория найдена", reply_markup=main_kb())
        text, kb = get_schedule_view('r', room, get_target_date())
        bot.send_message(m.chat.id, text, parse_mode='HTML', reply_markup=kb)


@bot.callback_query_handler(func=lambda c: c.data.startswith('room_sel|'))
def room_sel_callback(c):
    bot.answer_callback_query(c.id)
    bot.clear_step_handler_by_chat_id(c.message.chat.id)
    room = c.data.split('|')[1]
    bot.send_message(c.message.chat.id, "✅ аудитория выбрана", reply_markup=main_kb())
    text, kb = get_schedule_view('r', room, get_target_date())
    bot.send_message(c.message.chat.id, text, parse_mode='HTML', reply_markup=kb)


@bot.message_handler(func=lambda m: True)
def last_handle(m):
    handle_group_input(m)


# --- запуск ---
if __name__ == '__main__':
    init_db()
    for d in [SCHEDULES_DIR, RETAKES_DIR]:
        os.makedirs(d, exist_ok=True)

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
