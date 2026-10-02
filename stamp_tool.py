# -*- coding: utf-8 -*-
"""
批次自動蓋章小工具
====================
功能：
  - 批次讀取一個資料夾內的 PDF / JPG / PNG 檔案
  - 可以同時設定「多個章」（例如：組長章 + 主任章），每個章可以各自指定位置、
    大小；如果兩個章選了同一個角落，程式會自動把它們排成一排，不會疊在一起。
  - 每個章可以：
      (a) 使用你準備好的印章圖片檔（JPG/PNG，白底或去背都可以）
      (b) 直接用文字自動產生一個紅框印章（不用自己做圖），可以填：
            單位/科別（選填，會印在最上面一行，字距較開）
            職稱（選填）
            姓名（必填，字會比較大）
  - PDF 只蓋在「最後一頁」；圖片檔會蓋在整張圖片上。
  - 「固定位置」：直接貼齊你選的位置邊緣，速度快、行為固定。
    「智慧偵測」：在附近範圍內自動找最空白處（但若多個章共用同一位置，
    會自動改用固定排列，不做智慧偵測，以確保排列整齊不重疊）。
  - 可以在章的正下方印上時間（月/日 時:分）。
  - 蓋完章的原始檔可以自動搬到指定資料夾，避免下次重複蓋章。
  - 所有設定都會自動記住，下次開啟程式會自動帶入。

使用方式：
  1. 安裝套件（第一次使用才需要）：pip install -r requirements.txt
  2. 執行：python stamp_tool.py
  3. 在視窗中設定資料夾、新增章，按「開始批次蓋章」即可。

作者：為內部行政作業自動化而寫
"""

import os
import re
import sys
import json
import shutil
import threading
import traceback
import urllib.request
import urllib.parse
import urllib.error
from datetime import datetime
from collections import OrderedDict

import numpy as np
from PIL import Image, ImageDraw, ImageFont

try:
    import tkinter as tk
    from tkinter import ttk, filedialog, messagebox
    TKINTER_AVAILABLE = True
except ImportError:
    TKINTER_AVAILABLE = False

try:
    import pymupdf as fitz  # PyMuPDF（新版套件名稱）
except ImportError:
    try:
        import fitz  # PyMuPDF（舊版相容名稱）
    except ImportError:
        fitz = None


# ============================================================
# 基本設定 / 常數
# ============================================================
SUPPORTED_IMG_EXT = {".jpg", ".jpeg", ".png"}
SUPPORTED_PDF_EXT = {".pdf"}

SUFFIX_PRESETS = ["組長核章", "主任核章", "自訂"]

POSITION_CHOICES = [
    ("bottom_right", "右下角（預設）"),
    ("bottom_center", "中央下方"),
    ("bottom_left", "左下角"),
    ("top_left", "左上角"),
    ("top_center", "中央上方"),
    ("top_right", "右上角"),
]
POSITION_LABEL_TO_CODE = {label: code for code, label in POSITION_CHOICES}
POSITION_CODE_TO_LABEL = {code: label for code, label in POSITION_CHOICES}
DEFAULT_POSITION = "bottom_right"

MODE_CHOICES = [
    ("fixed", "固定位置（直接貼齊邊緣，不偵測內容）"),
    ("smart", "智慧偵測（自動找附近最空白處，但可能誤判）"),
]
MODE_LABEL_TO_CODE = {label: code for code, label in MODE_CHOICES}
MODE_CODE_TO_LABEL = {code: label for code, label in MODE_CHOICES}
DEFAULT_MODE = "fixed"

# 時間戳記預設顏色（跟印章紅色一致）
TIMESTAMP_DEFAULT_COLOR = (224, 24, 24)


def format_stamp_timestamp(custom_text=None):
    """
    產生要印在章下方的時間文字。
    custom_text 有填的話直接用那段文字（使用者手動指定）；
    沒填就自動用「民國年/月/日 時:分」，例如 115/09/26 14:35。
    """
    if custom_text and custom_text.strip():
        return custom_text.strip()
    now = datetime.now()
    minguo_year = now.year - 1911
    return f"{minguo_year}/{now.month:02d}/{now.day:02d} {now.hour:02d}:{now.minute:02d}"

# 設定檔：跟執行檔（或程式）放在同一個資料夾，記住上次用過的選項
if getattr(sys, "frozen", False):
    _BASE_DIR = os.path.dirname(sys.executable)
else:
    _BASE_DIR = os.path.dirname(os.path.abspath(__file__))
CONFIG_PATH = os.path.join(_BASE_DIR, "stamp_tool_settings.json")

# 院內員工資料 API（依實際環境可在介面上修改）
DEFAULT_API_URL = "http://hq-sso2-nvm/IWS/AJAX/getEmpInfo"


def fetch_employee_info(emp_no, api_url=DEFAULT_API_URL, timeout=6):
    """
    呼叫院內 API，用員工編號查詢員工資料。
    回傳整筆資料的 dict（例如 emp_name、emp_birth...）；
    查不到人或連線失敗時丟出例外，訊息可直接顯示給使用者看。
    """
    emp_no = (emp_no or "").strip()
    if not emp_no:
        raise ValueError("請輸入員工編號")

    url = api_url.strip() + "?" + urllib.parse.urlencode({"emp_no": emp_no})
    try:
        with urllib.request.urlopen(url, timeout=timeout) as resp:
            raw = resp.read().decode("utf-8-sig", errors="replace")
    except urllib.error.URLError as e:
        raise RuntimeError(f"連線院內 API 失敗：{e.reason}") from e
    except Exception as e:
        raise RuntimeError(f"連線院內 API 失敗：{e}") from e

    try:
        data = json.loads(raw)
    except Exception as e:
        raise RuntimeError(f"院內 API 回傳的內容不是預期的 JSON 格式：{e}") from e

    if data.get("status") != "success":
        raise RuntimeError(data.get("msg") or "查無此員工編號")
    rows = data.get("rows") or []
    if not rows:
        raise RuntimeError("查無此員工編號")
    row = rows[0]
    if not (row.get("emp_name") or "").strip():
        raise RuntimeError("院內 API 沒有回傳姓名")
    return row


def format_minguo_birthdate(text):
    """
    把使用者輸入的出生年月日（西元或民國，用 / - . 分隔，或直接輸入 7/8 碼
    數字）轉成院內 API 慣用的民國年格式：3 碼民國年 + 2 碼月 + 2 碼日
    （例如 0910911 代表民國 91 年 09 月 11 日）。
    """
    text = (text or "").strip()
    if not text:
        raise ValueError("請輸入出生年月日")

    digits_only = re.sub(r"\D", "", text)
    parts = re.split(r"[/\-.]", text)

    if len(parts) == 3 and all(p.strip() for p in parts):
        y, m, d = (int(p) for p in parts)
    elif len(digits_only) == 8:  # 西元8碼 YYYYMMDD
        y, m, d = int(digits_only[:4]), int(digits_only[4:6]), int(digits_only[6:8])
    elif len(digits_only) == 7:  # 民國7碼 YYYMMDD
        y, m, d = int(digits_only[:3]), int(digits_only[3:5]), int(digits_only[5:7])
    else:
        raise ValueError("出生年月日格式看不懂，請用「1990/01/01」或「079/01/01」這樣的格式")

    if y >= 1000:  # 西元年，轉換成民國年
        y -= 1911
    if not (1 <= m <= 12 and 1 <= d <= 31):
        raise ValueError("出生年月日的月份或日期看起來不對，請確認")
    return f"{y:03d}{m:02d}{d:02d}"


def load_settings():
    try:
        with open(CONFIG_PATH, "r", encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        return {}


def save_settings(data):
    try:
        with open(CONFIG_PATH, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False, indent=2)
    except Exception:
        pass


# ============================================================
# 字型
# ============================================================
def get_ascii_font(size):
    """給時間戳記用（只有數字/符號），不需要中文字型"""
    for name in ("arial.ttf", "Arial.ttf", "DejaVuSans.ttf",
                 "LiberationSans-Regular.ttf"):
        try:
            return ImageFont.truetype(name, size)
        except Exception:
            continue
    return ImageFont.load_default()


# 常見中文字型名稱（Windows 會自動去 %WINDIR%\Fonts 找同名檔案）
_CJK_FONT_CANDIDATES = [
    "kaiu.ttf",      # 標楷體 DFKai-SB（繁中 Windows 必有，印章慣用字體）
    "biaokai.ttc", "Kaiti SC", "Kaiti TC", "Kaiti TC Regular",  # macOS 對應字型
    "mingliu.ttc",   # 細明體
    "msjh.ttc", "MSJH.TTC",   # 微軟正黑體
    "simsun.ttc",    # 新細明體
    "msyh.ttc",      # 微軟雅黑
    "PingFang.ttc",  # macOS
    # 下面這幾個是 Linux 常見路徑，主要給開發/測試用（Serif 較接近楷體筆劃）
    "/usr/share/fonts/opentype/noto/NotoSerifCJK-Regular.ttc",
    "/usr/share/fonts/opentype/noto/NotoSansCJK-Regular.ttc",
    "/usr/share/fonts/truetype/wqy/wqy-zenhei.ttc",
]


def get_cjk_font(size, custom_font_path=None):
    """
    找一個可以顯示中文的字型。優先使用使用者指定的字型檔，找不到再依序
    嘗試常見的中文字型名稱。都找不到就回傳 None（呼叫端要自己處理）。
    """
    candidates = []
    if custom_font_path:
        candidates.append(custom_font_path)
    candidates.extend(_CJK_FONT_CANDIDATES)

    for path in candidates:
        if not path:
            continue
        try:
            return ImageFont.truetype(path, size)
        except Exception:
            continue
    return None


# ============================================================
# 印章圖片：去除白色背景
# ============================================================
def load_stamp_rgba(stamp_path, white_thresh=225, feather=35):
    """讀取章的圖片，回傳去除白底後的 RGBA 影像"""
    img = Image.open(stamp_path).convert("RGBA")
    arr = np.array(img).astype(np.float32)
    rgb = arr[:, :, :3]
    whiteness = rgb.min(axis=2)

    alpha = np.ones(whiteness.shape, dtype=np.float32) * 255.0
    alpha[whiteness >= white_thresh] = 0.0
    low = white_thresh - feather
    mask_mid = (whiteness > low) & (whiteness < white_thresh)
    alpha[mask_mid] = (white_thresh - whiteness[mask_mid]) / feather * 255.0

    if img.mode == "RGBA":
        orig_alpha = arr[:, :, 3]
        alpha = np.minimum(alpha, orig_alpha)

    arr[:, :, 3] = np.clip(alpha, 0, 255)
    return Image.fromarray(arr.astype(np.uint8), mode="RGBA")


# ============================================================
# 文字自動產生章（不用準備圖片檔）
# ============================================================
def _draw_spaced_text(draw, text, x, y_top, font, fill, extra_gap=0.5, align="center"):
    """
    畫一行文字，字與字之間留一點間距。
    align="center": x 視為水平置中點；align="left": x 視為文字最左邊起點。
    回傳 (這行文字高度, 這行文字總寬度)。
    """
    if not text:
        return 0, 0
    infos = []
    for ch in text:
        bbox = draw.textbbox((0, 0), ch, font=font)
        infos.append((ch, bbox[2] - bbox[0], bbox[1], bbox[3]))
    gap = max(1, int(font.size * extra_gap))
    total_w = sum(w for _, w, _, _ in infos) + gap * (len(infos) - 1)
    cur_x = (x - total_w // 2) if align == "center" else x
    max_h = max((b3 - b1) for _, _, b1, b3 in infos)
    for ch, w, b1, b3 in infos:
        draw.text((cur_x, y_top - b1), ch, font=font, fill=fill)
        cur_x += w + gap
    return max_h, total_w


def _draw_justified_text(draw, text, x_left, slot_pitch, slot_count, y_top, font, fill):
    """
    畫一行文字，用『固定網格』對齊：網格共有 slot_count 格（例如 3 格），
    相鄰兩格起始位置的間距是 slot_pitch。第一個字在第 0 格、最後一個字在第
    slot_count-1 格，中間依字數等分內插。這樣不管這行是 2 個字還是 3 個字，
    都是用同一套網格位置，才能讓不同行之間真正對齊（如果改用「依每個字實際
    墨色寬度」計算間距，會因為不同字筆劃疏密不同、墨色寬度略有差異，導致
    看起來對不齊）。
    只有一個字時就直接靠左。
    回傳這行文字的高度。
    """
    if not text:
        return 0
    infos = []
    for ch in text:
        bbox = draw.textbbox((0, 0), ch, font=font)
        infos.append((ch, bbox[1], bbox[3]))
    max_h = max((b3 - b1) for _, b1, b3 in infos)

    k = len(infos)
    if k == 1:
        ch, b1, b3 = infos[0]
        draw.text((x_left, y_top - b1), ch, font=font, fill=fill)
        return max_h

    for j, (ch, b1, b3) in enumerate(infos):
        pos_slot = j * (slot_count - 1) / (k - 1)
        x = x_left + pos_slot * slot_pitch
        draw.text((x, y_top - b1), ch, font=font, fill=fill)
    return max_h


def generate_text_stamp(unit="", title="", name="", custom_font_path=None,
                         color=(224, 24, 24), canvas_size=None, border=9):
    """
    產生一個紅框文字章（RGBA，透明背景）。版面：
      - 左側：單位/科別、職稱，字較小、靠左排列（由上到下堆疊）
      - 右側：姓名，字較大，盡量撐滿章的高度
      - 如果單位、職稱都沒填，姓名會置中並撐滿整個章
    """
    name = (name or "").strip()
    title = (title or "").strip()
    unit = (unit or "").strip()
    if not name:
        raise ValueError("文字章至少需要輸入姓名")

    test_font = get_cjk_font(20, custom_font_path)
    if test_font is None:
        raise RuntimeError(
            "找不到可用的中文字型，無法產生文字章。"
            "請在「自訂中文字型檔」欄位指定一個 .ttf/.otf 字型檔，"
            "或改用準備好的印章圖片檔。")

    # 章的外框比例固定不變（不因為左側是 1 行或 2 行而改變），
    # 行數變化改成調整「左側文字的字級大小」來塞進同樣大小的框裡
    if canvas_size is None:
        canvas_size = (640, 210)

    W, H = canvas_size
    img = Image.new("RGBA", (W, H), (255, 255, 255, 0))
    draw = ImageDraw.Draw(img)
    fill = color + (255,)

    draw.rectangle([border // 2, border // 2, W - 1 - border // 2, H - 1 - border // 2],
                    outline=fill, width=border)

    pad = border + int(H * 0.05)
    inner_left, inner_right = pad, W - pad
    inner_top, inner_bottom = pad, H - pad
    avail_w = inner_right - inner_left
    avail_h = inner_bottom - inner_top

    def _fit_name(font_size, max_w):
        """把姓名的字級縮小到能放進 max_w 內，回傳 (font, bbox, width)"""
        font = get_cjk_font(font_size, custom_font_path)
        bbox = draw.textbbox((0, 0), name, font=font)
        w = bbox[2] - bbox[0]
        if w > max_w and w > 0:
            scale = (max_w / w) * 0.97
            font_size = max(14, int(font_size * scale))
            font = get_cjk_font(font_size, custom_font_path)
            bbox = draw.textbbox((0, 0), name, font=font)
            w = bbox[2] - bbox[0]
        return font, bbox, w

    has_left_block = bool(unit or title)

    if not has_left_block:
        # 沒有單位/職稱：姓名置中，盡量撐滿整個章
        name_font, bbox_n, n_w = _fit_name(int(avail_h * 0.92), avail_w * 0.96)
        n_h = bbox_n[3] - bbox_n[1]
        cx, cy = W // 2, H // 2
        tx = cx - n_w // 2 - bbox_n[0]
        ty = cy - n_h // 2 - bbox_n[1]
        draw.text((tx, ty), name, font=name_font, fill=fill)
        return img

    # 有單位/職稱：左欄放單位+職稱（靠左、由上到下），右欄放姓名（大字）
    lines = [t for t in (unit, title) if t]
    n_lines = len(lines) if lines else 1

    # 姓名的字級（右側基準），左側「單行 3 個字」的職稱要跟這個一樣大
    name_ref_font_size = int(avail_h * 0.92)

    if n_lines <= 1:
        small_font_size = name_ref_font_size
    else:
        # 兩行職稱時字級要明顯放大（不是隨便縮到塞得下就好）
        small_font_size = max(12, int(avail_h * 0.40))
    small_font = get_cjk_font(small_font_size, custom_font_path)

    # 欄寬不是固定比例，而是依內容計算：以「3 個字」為基準寬度，
    # 這樣單行 3 個字剛好自然填滿欄寬、2 個字兩端對齊時中間自然空出一格；
    # 如果某一行字數比 3 多（例如「醫事放射師」5 個字），欄寬跟著加大
    slot_count = max(3, max((len(line) for line in lines), default=3))
    sample_char = max((c for line in lines for c in line),
                       key=lambda c: draw.textbbox((0, 0), c, font=small_font)[2]
                       - draw.textbbox((0, 0), c, font=small_font)[0])
    cbbox = draw.textbbox((0, 0), sample_char, font=small_font)
    avg_char_w = cbbox[2] - cbbox[0]
    char_gap = avg_char_w * 0.15
    slot_pitch = avg_char_w + char_gap  # 相鄰兩個字起始位置的間距
    left_col_w = int(slot_count * avg_char_w + (slot_count - 1) * char_gap)

    # 左欄最多只能佔用可用寬度的 55%，避免壓縮到姓名的空間；
    # 超過的話依比例縮小字級重新計算
    max_left_col_w = int(avail_w * 0.55)
    if left_col_w > max_left_col_w:
        scale = (max_left_col_w / left_col_w) * 0.98
        small_font_size = max(10, int(small_font_size * scale))
        small_font = get_cjk_font(small_font_size, custom_font_path)
        cbbox = draw.textbbox((0, 0), sample_char, font=small_font)
        avg_char_w = cbbox[2] - cbbox[0]
        char_gap = avg_char_w * 0.15
        slot_pitch = avg_char_w + char_gap
        left_col_w = int(slot_count * avg_char_w + (slot_count - 1) * char_gap)

    col_gap = 0  # 左右兩欄中間完全不留間距
    left_x = inner_left
    right_x0 = inner_left + left_col_w + col_gap
    # 右側（姓名跟外框之間）多留一點空間，不要頂到邊
    right_margin = int(avail_w * 0.05)
    right_w = max(20, inner_right - right_x0 - right_margin)

    # 每一行也各自檢查寬度（例如兩行職稱其中一行特別長），超出就再縮小
    max_line_w = 0
    for line in lines:
        bbox = draw.textbbox((0, 0), line, font=small_font)
        max_line_w = max(max_line_w, bbox[2] - bbox[0])
    if max_line_w > left_col_w and max_line_w > 0:
        scale = (left_col_w / max_line_w) * 0.97
        small_font_size = max(8, int(small_font_size * scale))
        small_font = get_cjk_font(small_font_size, custom_font_path)

    line_gap = int(small_font_size * 0.15)

    heights = [draw.textbbox((0, 0), line, font=small_font)[3] -
               draw.textbbox((0, 0), line, font=small_font)[1] for line in lines]
    total_left_h = sum(heights) + line_gap * (len(lines) - 1) if lines else 0
    cur_y = inner_top + (avail_h - total_left_h) // 2

    for line, lh in zip(lines, heights):
        _draw_justified_text(draw, line, left_x, slot_pitch, slot_count, cur_y, small_font, fill)
        cur_y += lh + line_gap

    # -- 右欄：姓名，盡量撐滿章的高度，在右欄範圍內水平置中 --
    name_font, bbox_n, n_w = _fit_name(name_ref_font_size, right_w * 0.96)
    n_h = bbox_n[3] - bbox_n[1]
    name_cx = right_x0 + right_w // 2
    name_cy = inner_top + avail_h // 2
    tx = name_cx - n_w // 2 - bbox_n[0]
    ty = name_cy - n_h // 2 - bbox_n[1]
    draw.text((tx, ty), name, font=name_font, fill=fill)

    return img


def _bleed_ink_color(rgba):
    """
    把印章圖片裡『半透明/全透明像素』的 RGB 值，填成印章本身（不透明部分）的
    平均顏色。

    為什麼要做：透明區域底下的 RGB 值通常是白色或黑色，縮放或合成時如果檢視器
    沒有做「依透明度加權」的處理，這些顏色會被混進邊緣——PDF 檢視器常常因此
    讓邊緣變深、PIL 縮放則常讓邊緣變淺，造成 PDF 與 PNG 看起來顏色不一致。
    把透明像素的 RGB 也填成印章顏色後，不管誰來縮放/合成，結果都只會是
    「同樣的紅色 + 不同透明度」，顏色就會一致。
    """
    arr = np.array(rgba.convert("RGBA"))
    alpha = arr[:, :, 3]
    opaque = alpha >= 200
    if not opaque.any():
        return rgba
    fill = np.round(arr[:, :, :3][opaque].mean(axis=0)).astype(np.uint8)
    partial = alpha < 255
    arr[partial, :3] = fill
    return Image.fromarray(arr, "RGBA")


def resolve_stamp_entry(entry, custom_font_path=None):
    """把 GUI 上設定的一筆『章』資料，轉成實際的 RGBA 印章圖片"""
    if entry.get("source") == "text":
        img = generate_text_stamp(
            unit=entry.get("unit", ""),
            title=entry.get("title", ""),
            name=entry.get("name", ""),
            custom_font_path=custom_font_path,
        )
    else:
        path = entry.get("image_path", "")
        if not path or not os.path.isfile(path):
            raise FileNotFoundError(f"找不到印章圖片: {path}")
        img = load_stamp_rgba(path)
    return _bleed_ink_color(img)


def stamp_entry_label(entry):
    if entry.get("source") == "text":
        parts = [entry.get("unit", ""), entry.get("title", ""), entry.get("name", "")]
        return "".join(p for p in parts if p) or "(文字章)"
    return os.path.basename(entry.get("image_path", "")) or "(圖片章)"


# ============================================================
# 空白偵測 / 固定位置 / 多章排列
# ============================================================
def find_blank_position(gray_arr, region_box, stamp_w, stamp_h,
                         step=12, min_score=0.80):
    H, W = gray_arr.shape
    x0, y0, x1, y1 = region_box
    x0, y0 = max(0, x0), max(0, y0)
    x1, y1 = min(W, x1), min(H, y1)

    max_x = max(x0, x1 - stamp_w)
    max_y = max(y0, y1 - stamp_h)

    best_score = -1.0
    best_pos = (max_x, max_y)

    y = y0
    while y <= max_y:
        x = x0
        while x <= max_x:
            window = gray_arr[y:y + stamp_h, x:x + stamp_w]
            if window.size > 0:
                score = float(np.mean(window > 235))
                if score > best_score:
                    best_score = score
                    best_pos = (x, y)
            x += step
        y += step

    return best_pos[0], best_pos[1], max(best_score, 0.0)


def get_search_region(width, height, position=DEFAULT_POSITION,
                       region_ratio_w=0.35, region_ratio_h=0.28,
                       margin_ratio=0.02):
    margin_x = int(width * margin_ratio)
    margin_y = int(height * margin_ratio)
    region_w = int(width * region_ratio_w)
    region_h = int(height * region_ratio_h)
    cx = width // 2

    if position not in POSITION_CODE_TO_LABEL:
        position = DEFAULT_POSITION

    if position.startswith("bottom"):
        y1 = height - margin_y
        y0 = max(0, y1 - region_h)
    else:
        y0 = margin_y
        y1 = min(height, y0 + region_h)

    if position.endswith("right"):
        x1 = width - margin_x
        x0 = max(0, x1 - region_w)
    elif position.endswith("left"):
        x0 = margin_x
        x1 = min(width, x0 + region_w)
    else:
        x0 = max(0, cx - region_w // 2)
        x1 = min(width, cx + region_w // 2)

    return x0, y0, x1, y1


def get_pdf_content_boxes(page):
    """
    讀取 PDF 頁面上『實際有內容』的區域（文字、線條/圖形），回傳一堆
    (x0,y0,x1,y1) 矩形（單位: point）。用來判斷某個區域是否真的空白，
    比單純看渲染後圖片的顏色更準確、也不受掃描雜訊影響。

    注意：
    - 圖形部分刻意取每一筆繪圖動作（線段/矩形/曲線）『自己』的邊界，而不是
      整個路徑（例如一整張表格的框線＋格線，或一條彎曲折線圖）的外框邊界，
      否則格子裡其實是空的表格、或只是細線的折線圖，會被誤判成整塊都有內容。
    - 白色填色的矩形（例如整頁的白色背景）視為空白，不算佔用內容。
    - 內嵌圖片（例如圖表）刻意不列入這裡的「嚴格內容」清單：圖片內部往往
      有大片真正空白的背景，那部分交給「實際渲染顏色」（gray）判斷，
      不要把整張圖片的外框都當成滿版佔用，否則圖表空白處會被誤擋。
    """
    boxes = []
    try:
        for w_ in page.get_text("words"):
            boxes.append((w_[0], w_[1], w_[2], w_[3]))
    except Exception:
        pass
    try:
        for d in page.get_drawings():
            fill_color = d.get("fill")
            is_filled = fill_color is not None and not (
                all(c >= 0.92 for c in fill_color) if fill_color else False)
            line_w = max(0.5, d.get("width") or 1.0)
            for item in d.get("items", []):
                op = item[0]
                try:
                    if op == "l":
                        p1, p2 = item[1], item[2]
                        xs, ys = [p1.x, p2.x], [p1.y, p2.y]
                        boxes.append((min(xs) - 1, min(ys) - 1, max(xs) + 1, max(ys) + 1))
                    elif op == "re":
                        r = item[1]
                        if is_filled:
                            boxes.append((r.x0, r.y0, r.x1, r.y1))
                        else:
                            lw = line_w
                            boxes.append((r.x0 - lw, r.y0 - lw, r.x1 + lw, r.y0 + lw))
                            boxes.append((r.x0 - lw, r.y1 - lw, r.x1 + lw, r.y1 + lw))
                            boxes.append((r.x0 - lw, r.y0 - lw, r.x0 + lw, r.y1 + lw))
                            boxes.append((r.x1 - lw, r.y0 - lw, r.x1 + lw, r.y1 + lw))
                    elif op in ("c", "qu"):
                        pts = [(p.x, p.y) for p in item[1:] if hasattr(p, "x")]
                        if pts:
                            xs = [p[0] for p in pts]
                            ys = [p[1] for p in pts]
                            boxes.append((min(xs) - 1, min(ys) - 1, max(xs) + 1, max(ys) + 1))
                except Exception:
                    continue
    except Exception:
        pass
    return boxes


def _rect_intersection_area(a, b):
    x0, y0 = max(a[0], b[0]), max(a[1], b[1])
    x1, y1 = min(a[2], b[2]), min(a[3], b[3])
    if x1 <= x0 or y1 <= y0:
        return 0.0
    return (x1 - x0) * (y1 - y0)


def _content_free_score(rect, content_boxes):
    """回傳 rect 這塊區域『沒有被實際內容佔用』的比例，1.0 代表完全空白"""
    rect_area = max(1e-6, (rect[2] - rect[0]) * (rect[3] - rect[1]))
    occupied = 0.0
    for cb in content_boxes:
        occupied += _rect_intersection_area(rect, cb)
    occupied = min(occupied, rect_area)
    return 1.0 - occupied / rect_area


def layout_custom_stamps(canvas_w, canvas_h, indexed_specs,
                          content_boxes=None, gray=None, log=print):
    """
    處理 position=='custom' 的章：使用 spec 裡的 custom_x_pct/custom_y_pct
    （畫布寬高的百分比）當作精確位置。

    - content_boxes（PDF 文字/圖形的實際座標，point 空間）跟 gray（圖片/
      頁面像素）可以同時提供：兩種判斷方式都必須認為夠空白才算數（取較
      保守的分數），避免其中一種方法的誤判掩蓋掉另一種方法正確抓到的重疊。
    - 如果該處剛好有內容重疊，會自動在附近（±12% 畫布範圍）就近找一個真正
      空白的位置；附近還是找不到，最後會搜尋「整頁」最空白的地方。
    - indexed_specs: [(原始index, spec), ...]
    - 回傳: {原始index: {'x','y','w','h','score'}}
    """
    results = {}
    placed_boxes = list(content_boxes) if content_boxes is not None else []

    def score_at(rx, ry, w, h):
        rect = (rx, ry, rx + w, ry + h)
        scores = []
        if content_boxes is not None:
            scores.append(_content_free_score(rect, placed_boxes))
        if gray is not None:
            window = gray[int(ry):int(ry + h), int(rx):int(rx + w)]
            if window.size > 0:
                scores.append(float(np.mean(window > 235)))
        if not scores:
            return 1.0
        return min(scores)

    for orig_i, spec in indexed_specs:
        w = max(20, int(canvas_w * spec["width_ratio"]))
        ratio = w / spec["rgba"].width
        h = max(20, int(spec["rgba"].height * ratio))

        x_pct = spec.get("custom_x_pct", 75) / 100.0
        y_pct = spec.get("custom_y_pct", 80) / 100.0
        x0 = int(max(0, min(int(canvas_w * x_pct), canvas_w - w)))
        y0 = int(max(0, min(int(canvas_h * y_pct), canvas_h - h)))

        base_score = score_at(x0, y0, w, h)
        best_score, best_x, best_y = base_score, x0, y0
        label = spec.get("label", "章")

        if base_score < 0.85:
            radius_x = max(1, int(canvas_w * 0.12))
            radius_y = max(1, int(canvas_h * 0.12))
            step = max(4, int(canvas_w * 0.01))
            for dy in range(-radius_y, radius_y + 1, step):
                for dx in range(-radius_x, radius_x + 1, step):
                    rx = int(max(0, min(x0 + dx, canvas_w - w)))
                    ry = int(max(0, min(y0 + dy, canvas_h - h)))
                    s = score_at(rx, ry, w, h)
                    if s > best_score:
                        best_score, best_x, best_y = s, rx, ry

            if best_score >= 0.85:
                log(f"    [{label}] 自訂座標處有內容重疊（空白分數 {base_score:.2f}），"
                    f"已自動就近調整到較空白處（分數 {best_score:.2f}）")
            else:
                step2 = max(6, int(canvas_w * 0.02))
                for ry in range(0, int(canvas_h - h) + 1, step2):
                    for rx in range(0, int(canvas_w - w) + 1, step2):
                        s = score_at(rx, ry, w, h)
                        if s > best_score:
                            best_score, best_x, best_y = s, rx, ry
                if best_score >= 0.85:
                    log(f"    [{label}] 自訂座標附近都有內容重疊，已改在全頁搜尋到"
                        f"的最空白處蓋章（分數 {best_score:.2f}），位置可能跟指定的不一樣，"
                        f"建議之後手動調整這個章的 X/Y% 設定")
                else:
                    log(f"    [{label}] 整頁幾乎都是滿版內容（最好分數僅 {best_score:.2f}），"
                        f"找不到理想的空白處，已蓋在相對最空白的位置，建議檢查蓋章效果")

        results[orig_i] = {"x": best_x, "y": best_y, "w": w, "h": h, "score": best_score}
        placed_boxes.append((best_x, best_y, best_x + w, best_y + h))

    return results


def layout_stamps_in_strip(strip_w, stamp_specs, ts_reserve=0, log=print):
    """
    在『新增的空白區域』裡幫章排版。因為這塊區域本來就是全新加上去的空白，
    不需要判斷版面內容、不會壓到任何文字。

    stamp_specs 的 position 只取水平方向的意義（靠左/置中/靠右，或 custom
    的 custom_x_pct），垂直方向一律在這塊新區域裡置中。

    - 'offset_index' + 'stack_direction'：分次蓋章時，後面的章可以選擇跟
      同一水平錨點的章排在右邊（'right'，預設）或下面（'down'）。
    - ts_reserve：每個章下方要留給時間戳記文字的高度（沒開時間戳記就是 0），
      往下疊的章之間會各自預留這塊空間，避免疊在一起。

    回傳: (strip_h, results)
      strip_h：這塊新區域需要的高度
      results：對應每個 stamp_specs 的 {'x','y','w','h'}（相對於這塊新區域
               左上角 (0,0)）
    """
    n = len(stamp_specs)
    sized = []
    for spec in stamp_specs:
        w = max(20, int(strip_w * spec["width_ratio"]))
        ratio = w / spec["rgba"].width
        h = max(20, int(spec["rgba"].height * ratio))
        sized.append((w, h))

    margin_x = int(strip_w * 0.025)
    gap = max(4, int(strip_w * 0.015))
    if ts_reserve:
        # 時間戳記文字通常比章本身寬，並排的章之間要多留一點空間，
        # 避免兩個章下方的時間文字互相重疊
        gap = max(gap, int(strip_w * 0.05))

    groups = OrderedDict()
    for idx, spec in enumerate(stamp_specs):
        if spec.get("position") == "custom":
            key = ("custom", idx)
        else:
            pos = spec.get("position", DEFAULT_POSITION)
            anchor = ("left" if pos.endswith("left") else
                      "right" if pos.endswith("right") else "center")
            key = ("anchor", anchor)
        groups.setdefault(key, []).append(idx)

    def split_group(idxs):
        down_idxs = [i for i in idxs if (stamp_specs[i].get("stack_direction") == "down"
                                          and stamp_specs[i].get("offset_index", 0) > 0)]
        row_idxs = [i for i in idxs if i not in down_idxs]
        return row_idxs, down_idxs

    def group_content_height(idxs):
        """這一組（橫排列 + 下疊列）總共需要的高度，含每個章自己的時間戳記空間"""
        row_idxs, down_idxs = split_group(idxs)
        row_h = max((sized[i][1] for i in row_idxs), default=0)
        row_total_h = (row_h + ts_reserve) if row_idxs else 0
        if down_idxs:
            down_total = (sum(sized[i][1] + ts_reserve for i in down_idxs)
                          + gap * (len(down_idxs) - 1))
            return (row_total_h + gap + down_total) if row_idxs else down_total
        return row_total_h

    strip_content_h = max((group_content_height(idxs) for idxs in groups.values()), default=20)
    pad_y = int(strip_content_h * 0.18) + 6
    strip_h = strip_content_h + pad_y * 2

    results = [None] * n

    for key, idxs in groups.items():
        idxs_sorted = sorted(idxs, key=lambda i: stamp_specs[i].get("offset_index", 0))
        row_idxs, down_idxs = split_group(idxs_sorted)

        if key[0] == "custom":
            x_pct = stamp_specs[idxs[0]].get("custom_x_pct", 75) / 100.0
            base_anchor_x = int(strip_w * x_pct)
            anchor = "custom"
        else:
            anchor = key[1]

        total_w = (sum(sized[i][0] for i in row_idxs) + gap * (len(row_idxs) - 1)
                   if row_idxs else 0)
        if anchor == "left":
            start_x = margin_x
        elif anchor == "right":
            start_x = strip_w - margin_x - total_w
        elif anchor == "custom":
            start_x = base_anchor_x
        else:
            start_x = strip_w // 2 - total_w // 2
        start_x = max(0, start_x)

        this_group_h = group_content_height(idxs)
        row_top = pad_y + (strip_content_h - this_group_h) // 2
        row_h = max((sized[i][1] for i in row_idxs), default=0)

        cur_x = start_x
        for i in row_idxs:
            w, h = sized[i]
            x = min(max(0, cur_x), max(0, strip_w - w))
            y = row_top + (row_h - h) // 2
            results[i] = {"x": x, "y": y, "w": w, "h": h, "score": None}
            cur_x += w + gap

        if down_idxs:
            if row_idxs:
                row_x = results[row_idxs[0]]["x"]
                row_w = results[row_idxs[0]]["w"]
                cur_y = row_top + row_h + ts_reserve + gap
            else:
                row_x = start_x
                row_w = 0
                cur_y = row_top
            for i in down_idxs:
                w, h = sized[i]
                if anchor == "right":
                    x = row_x + row_w - w  # 跟上面章的右邊緣對齊
                elif anchor == "left":
                    x = row_x  # 跟上面章的左邊緣對齊
                else:  # center / custom：跟上面章的水平中心對齊
                    x = row_x + row_w // 2 - w // 2
                x = min(max(0, x), max(0, strip_w - w))
                results[i] = {"x": x, "y": cur_y, "w": w, "h": h, "score": None}
                cur_y += h + ts_reserve + gap

        if len(idxs) > 1:
            log(f"    (新增的空白區域) 有 {len(idxs)} 個章排在一起")

    return strip_h, results


def extend_image_with_blank_strip(img, strip_h):
    """在圖片最下面加上一塊白色空白區域，回傳 (新圖片, 空白區域的起始 y)"""
    W, H = img.size
    new_img = Image.new("RGB", (W, H + strip_h), "white")
    new_img.paste(img, (0, 0))
    return new_img, H


def extend_pdf_page_with_blank_strip(page, strip_h_pt):
    """
    在 PDF 最後一頁的下方加上一塊空白區域（延伸 mediabox，不會移動原本的
    內容）。回傳空白區域的起始 y（point，沿用 fitz 慣用的左上角座標系統）。
    """
    orig_h = page.rect.height
    mb = page.mediabox
    new_mb = fitz.Rect(mb.x0, mb.y0 - strip_h_pt, mb.x1, mb.y1)
    page.set_mediabox(new_mb)
    return orig_h


def layout_stamps(canvas_w, canvas_h, stamp_specs, mode=DEFAULT_MODE,
                   gray=None, add_timestamp=False, log=print):
    """
    stamp_specs: [{'rgba':RGBA影像, 'width_ratio':0.14, 'position':'bottom_right',
                   'label':'組長章', 'offset_index':0}, ...]
    回傳同樣長度的 list，每個元素為 {'x','y','w','h','score'}

    - 同一次批次裡，多個章若共用同一個 position，會自動排成一排、互不重疊。
    - 'offset_index'：用於「分次蓋章」情境（例如組長蓋完存檔，再交給主任執行
      第二次蓋章）。每個章各自獨立設定「這個位置前面已經有幾個章」，程式會
      依此手動往內側多讓開幾格，避免跟上一個人已經蓋好、但這次執行看不到的
      章重疊。
    - add_timestamp 為 True 時，蓋在「下方」的章會自動多留一點底部空間，
      避免章下方要印的時間文字被圖片邊緣切到。
    """
    groups = OrderedDict()
    for i, spec in enumerate(stamp_specs):
        groups.setdefault(spec["position"], []).append(i)

    results = [None] * len(stamp_specs)
    margin_x = int(canvas_w * 0.03)
    margin_y = int(canvas_h * 0.03)
    gap = max(4, int(canvas_w * 0.015))

    for pos, idxs in groups.items():
        sized = []
        for i in idxs:
            spec = stamp_specs[i]
            w = max(20, int(canvas_w * spec["width_ratio"]))
            ratio = w / spec["rgba"].width
            h = max(20, int(spec["rgba"].height * ratio))
            offset_index = max(0, int(spec.get("offset_index", 0)))
            sized.append((i, w, h, offset_index))

        # 下方的章，若要印時間戳記，額外預留一點底部空間，避免文字被切到
        bottom_reserve = 0
        if add_timestamp and pos.startswith("bottom"):
            ref_w = max(w for _, w, _, _ in sized)
            bottom_reserve = int(max(14, int(ref_w * 0.16)) * 1.6)

        if len(sized) == 1 and sized[0][3] == 0 and mode == "smart" and gray is not None:
            i, w, h, _ = sized[0]
            region = get_search_region(canvas_w, canvas_h, position=pos)
            if bottom_reserve:
                region = (region[0], region[1], region[2],
                          max(region[1] + h, region[3] - bottom_reserve))
            x, y, score = find_blank_position(gray, region, w, h)
            results[i] = {"x": x, "y": y, "w": w, "h": h, "score": score}
            continue

        total_w = sum(w for _, w, _, _ in sized) + gap * (len(sized) - 1)
        # 手動位移：以第一個章的寬度當作一格的參考大小，往內側多讓開幾格
        lead_slots = max(off for _, _, _, off in sized)
        lead_w = lead_slots * (sized[0][1] + gap) if lead_slots else 0

        if pos.endswith("left"):
            start_x = margin_x + lead_w
        elif pos.endswith("right"):
            start_x = canvas_w - margin_x - total_w - lead_w
        else:
            start_x = canvas_w // 2 - total_w // 2 - lead_w
        start_x = max(0, start_x)

        cur_x = start_x
        for i, w, h, _ in sized:
            if pos.startswith("bottom"):
                y = canvas_h - margin_y - bottom_reserve - h
            else:
                y = margin_y
            x = min(max(0, cur_x), max(0, canvas_w - w))
            results[i] = {"x": x, "y": y, "w": w, "h": h, "score": None}
            cur_x += w + gap

        if len(sized) > 1:
            log(f"    ({POSITION_CODE_TO_LABEL.get(pos, pos)}) 有 {len(sized)} 個章，"
                f"已自動排成一排，避免互相重疊")
        elif lead_slots:
            log(f"    ({POSITION_CODE_TO_LABEL.get(pos, pos)}) 手動讓開 {lead_slots} 格"
                f"（避免跟上一次已蓋好的章重疊）")

    return results


# ============================================================
# 蓋章：圖片檔
# ============================================================
def stamp_image_file(input_path, output_path, stamps,
                      mode=DEFAULT_MODE, add_timestamp=False,
                      timestamp_text=None, timestamp_color=TIMESTAMP_DEFAULT_COLOR,
                      extend_blank=False, log=print):
    img = Image.open(input_path).convert("RGB")
    W, H = img.size

    ts_text = format_stamp_timestamp(timestamp_text) if add_timestamp else None

    if extend_blank:
        # 直接在圖片最下面加一塊全新的空白區域來蓋章，保證不會壓到原本的內容，
        # 不需要判斷版面
        ts_reserve = 0
        if ts_text:
            sample_font_size = max(14, int(W * 0.16 * 0.14))
            ts_reserve = int(sample_font_size * 1.8)
        strip_h, layout = layout_stamps_in_strip(W, stamps, ts_reserve=ts_reserve, log=log)
        img, strip_y0 = extend_image_with_blank_strip(img, strip_h)
        W, H = img.size
        draw = ImageDraw.Draw(img)
        for spec, info in zip(stamps, layout):
            x, w, h = info["x"], info["w"], info["h"]
            y = strip_y0 + info["y"]
            resized = spec["rgba"].resize((w, h), Image.LANCZOS)
            img.paste(resized, (x, y), resized)
            if ts_text:
                font_size = max(14, int(w * 0.16))
                font = get_ascii_font(font_size)
                bbox = draw.textbbox((0, 0), ts_text, font=font)
                tw, th = bbox[2] - bbox[0], bbox[3] - bbox[1]
                tx = x + (w - tw) // 2
                ty = y + h + max(2, int(h * 0.03))
                tx = max(0, min(tx, W - tw))
                ty = min(ty, H - th)
                draw.text((tx, ty), ts_text, fill=timestamp_color, font=font)

        ext = os.path.splitext(output_path)[1].lower()
        if ext in (".jpg", ".jpeg"):
            img.save(output_path, quality=95)
        else:
            img.save(output_path)
        return True

    custom_idx = [i for i, s in enumerate(stamps) if s.get("position") == "custom"]
    preset_idx = [i for i in range(len(stamps)) if i not in custom_idx]

    gray = np.array(img.convert("L")) if (mode == "smart" or custom_idx) else None
    layout = [None] * len(stamps)

    if custom_idx:
        indexed = [(i, stamps[i]) for i in custom_idx]
        custom_results = layout_custom_stamps(W, H, indexed, gray=gray, log=log)
        for i, r in custom_results.items():
            layout[i] = r

    if preset_idx:
        preset_specs = [stamps[i] for i in preset_idx]
        preset_layout = layout_stamps(W, H, preset_specs, mode=mode, gray=gray,
                                       add_timestamp=add_timestamp, log=log)
        for local_i, orig_i in enumerate(preset_idx):
            layout[orig_i] = preset_layout[local_i]

    for spec, info in zip(stamps, layout):
        x, y, w, h = info["x"], info["y"], info["w"], info["h"]
        resized = spec["rgba"].resize((w, h), Image.LANCZOS)
        img.paste(resized, (x, y), resized)

        if info.get("score") is not None:
            log(f"    [{spec['label']}] 空白分數: {info['score']:.2f}")

        if ts_text:
            draw = ImageDraw.Draw(img)
            font_size = max(14, int(w * 0.16))
            font = get_ascii_font(font_size)
            bbox = draw.textbbox((0, 0), ts_text, font=font)
            tw, th = bbox[2] - bbox[0], bbox[3] - bbox[1]
            tx = x + (w - tw) // 2
            ty = y + h + max(2, int(h * 0.03))
            tx = max(0, min(tx, W - tw))
            ty = min(ty, H - th)
            draw.text((tx, ty), ts_text, fill=timestamp_color, font=font)

    ext = os.path.splitext(output_path)[1].lower()
    if ext in (".jpg", ".jpeg"):
        img.save(output_path, quality=95)
    else:
        img.save(output_path)
    return True


# ============================================================
# 蓋章：PDF（只蓋最後一頁）
# ============================================================
def _stamp_png_for_pdf(page, rgba, rect, scale=3):
    """
    把章圖片轉成『不透明』的 RGB 圖片再嵌入 PDF，避免各家 PDF 檢視器對
    「帶透明度圖片」縮放/合成方式不同（有的邊緣會變深、有的變淺），造成
    PDF 跟 PNG 輸出的章顏色看起來不一致。

    做法：先依章在頁面上的實際大小（放大 scale 倍以保持清晰度）縮放，再壓平在
    該處頁面的底色上（通常是白色；如果該處底色明顯不是白色，就取該處的中位數
    顏色當底色）。這跟 PNG/JPG 輸出「直接壓在文件像素上」的效果一致。
    """
    tw = max(1, int(round(rect.width * scale)))
    th = max(1, int(round(rect.height * scale)))
    resized = rgba.resize((tw, th), Image.LANCZOS)

    bg = (255, 255, 255)
    try:
        pm = page.get_pixmap(matrix=fitz.Matrix(1, 1), clip=rect,
                              colorspace=fitz.csRGB, alpha=False)
        arr = np.frombuffer(pm.samples, dtype=np.uint8).reshape(pm.height, pm.width, 3)
        med = tuple(int(v) for v in np.median(arr.reshape(-1, 3), axis=0))
        if min(med) < 235:  # 底色明顯不是白色，才改用該處實際底色
            bg = med
    except Exception:
        pass

    base = Image.new("RGB", resized.size, bg)
    base.paste(resized, (0, 0), resized)
    return base


def stamp_pdf_file(input_path, output_path, stamps,
                    mode=DEFAULT_MODE, add_timestamp=False,
                    timestamp_text=None, timestamp_color=TIMESTAMP_DEFAULT_COLOR,
                    extend_blank=False, render_zoom=1.5, log=print):
    if fitz is None:
        raise RuntimeError("尚未安裝 PyMuPDF，請先執行: pip install PyMuPDF")

    doc = fitz.open(input_path)
    if doc.page_count == 0:
        raise RuntimeError("PDF 沒有任何頁面")

    page = doc[-1]
    page_rect = page.rect
    ts_text = format_stamp_timestamp(timestamp_text) if add_timestamp else None

    if extend_blank:
        # 直接在最後一頁下方延伸出一塊全新的空白區域來蓋章，
        # 保證不會壓到原本的內容，不需要判斷版面
        ts_reserve = 0
        if ts_text:
            sample_font_size = max(8, min(14, page_rect.width * 0.16 * 0.15))
            ts_reserve = sample_font_size * 1.8
        strip_h, layout = layout_stamps_in_strip(page_rect.width, stamps, ts_reserve=ts_reserve, log=log)
        strip_y0 = extend_pdf_page_with_blank_strip(page, strip_h)

        tmp_paths = []
        try:
            for spec, info in zip(stamps, layout):
                x_pt, w_pt, h_pt = info["x"], info["w"], info["h"]
                y_pt = strip_y0 + info["y"]
                rect = fitz.Rect(x_pt, y_pt, x_pt + w_pt, y_pt + h_pt)
                tmp_path = output_path + f"._stamp_tmp_{len(tmp_paths)}.png"
                _stamp_png_for_pdf(page, spec["rgba"], rect).save(tmp_path)
                tmp_paths.append(tmp_path)
                page.insert_image(rect, filename=tmp_path, overlay=True)

                if ts_text:
                    font_size = max(8, min(14, w_pt * 0.15))
                    text_w = fitz.get_text_length(ts_text, fontname="helv", fontsize=font_size)
                    tx = x_pt + (w_pt - text_w) / 2
                    ty = y_pt + h_pt + font_size * 1.1
                    ty = min(ty, page.rect.height - 2)
                    tx = max(0, min(tx, page_rect.width - text_w))
                    page.insert_text((tx, ty), ts_text, fontname="helv", fontsize=font_size,
                                      color=tuple(c / 255.0 for c in timestamp_color))

            doc.save(output_path, garbage=4, deflate=True)
        finally:
            doc.close()
            for p in tmp_paths:
                if os.path.exists(p):
                    os.remove(p)
        return True

    custom_idx = [i for i, s in enumerate(stamps) if s.get("position") == "custom"]
    preset_idx = [i for i in range(len(stamps)) if i not in custom_idx]

    layout_pt = [None] * len(stamps)  # 最終統一用 point（頁面實際座標）儲存位置

    if custom_idx:
        content_boxes = get_pdf_content_boxes(page)
        # 額外渲染一張 zoom=1.0 的灰階圖（1 point = 1 pixel，跟頁面 point
        # 座標完全對齊），跟文字/圖形座標互相驗證
        pix_pt = page.get_pixmap(matrix=fitz.Matrix(1.0, 1.0), colorspace=fitz.csGRAY)
        gray_pt = np.frombuffer(pix_pt.samples, dtype=np.uint8).reshape(
            pix_pt.height, pix_pt.width)
        indexed = [(i, stamps[i]) for i in custom_idx]
        custom_results = layout_custom_stamps(
            page_rect.width, page_rect.height, indexed,
            content_boxes=content_boxes, gray=gray_pt, log=log)
        for i, r in custom_results.items():
            layout_pt[i] = r

    if preset_idx:
        preset_specs = [stamps[i] for i in preset_idx]
        gray = None
        if mode == "smart":
            mat = fitz.Matrix(render_zoom, render_zoom)
            pix = page.get_pixmap(matrix=mat, colorspace=fitz.csGRAY)
            gray = np.frombuffer(pix.samples, dtype=np.uint8).reshape(pix.height, pix.width)
            canvas_w, canvas_h = pix.width, pix.height
            scale = 1.0 / render_zoom
        else:
            canvas_w, canvas_h = page_rect.width, page_rect.height
            scale = 1.0

        preset_layout = layout_stamps(canvas_w, canvas_h, preset_specs, mode=mode,
                                       gray=gray, add_timestamp=add_timestamp, log=log)
        for local_i, orig_i in enumerate(preset_idx):
            info = preset_layout[local_i]
            layout_pt[orig_i] = {
                "x": info["x"] * scale, "y": info["y"] * scale,
                "w": info["w"] * scale, "h": info["h"] * scale,
                "score": info["score"],
            }

    tmp_paths = []
    try:
        for spec, info in zip(stamps, layout_pt):
            x_pt, y_pt, w_pt, h_pt = info["x"], info["y"], info["w"], info["h"]

            if info.get("score") is not None:
                log(f"    [{spec['label']}] 最後一頁空白分數: {info['score']:.2f}")

            rect = fitz.Rect(x_pt, y_pt, x_pt + w_pt, y_pt + h_pt)
            tmp_path = output_path + f"._stamp_tmp_{len(tmp_paths)}.png"
            _stamp_png_for_pdf(page, spec["rgba"], rect).save(tmp_path)
            tmp_paths.append(tmp_path)
            page.insert_image(rect, filename=tmp_path, overlay=True)

            if ts_text:
                font_size = max(8, min(14, w_pt * 0.15))
                text_w = fitz.get_text_length(ts_text, fontname="helv", fontsize=font_size)
                tx = x_pt + (w_pt - text_w) / 2
                ty = y_pt + h_pt + font_size * 1.1
                ty = min(ty, page_rect.height - 2)
                tx = max(0, min(tx, page_rect.width - text_w))
                page.insert_text((tx, ty), ts_text, fontname="helv",
                                  fontsize=font_size,
                                  color=tuple(c / 255.0 for c in timestamp_color))

        doc.save(output_path, garbage=4, deflate=True)
    finally:
        doc.close()
        for p in tmp_paths:
            if os.path.exists(p):
                os.remove(p)

    return True


# ============================================================
# 批次處理主邏輯
# ============================================================
def _unique_dest_path(dest_dir, filename):
    base, ext = os.path.splitext(filename)
    candidate = os.path.join(dest_dir, filename)
    n = 1
    while os.path.exists(candidate):
        candidate = os.path.join(dest_dir, f"{base}_{n}{ext}")
        n += 1
    return candidate


def batch_process(input_dir, stamp_entries, output_dir,
                   mode=DEFAULT_MODE, suffix="已蓋章",
                   add_timestamp=False, timestamp_text=None,
                   timestamp_color=TIMESTAMP_DEFAULT_COLOR,
                   extend_blank=False,
                   processed_dir=None,
                   custom_font_path=None,
                   log=print, progress_cb=None):
    if not stamp_entries:
        log("尚未設定任何章，請先新增至少一個章。")
        return 0, 0

    resolved_stamps = []
    for entry in stamp_entries:
        rgba = resolve_stamp_entry(entry, custom_font_path=custom_font_path)
        resolved_stamps.append({
            "rgba": rgba,
            "width_ratio": entry.get("width_pct", 14) / 100.0,
            "position": entry.get("position", DEFAULT_POSITION),
            "offset_index": entry.get("offset_index", 0),
            "stack_direction": entry.get("stack_direction", "right"),
            "custom_x_pct": entry.get("custom_x_pct", 75),
            "custom_y_pct": entry.get("custom_y_pct", 80),
            "label": stamp_entry_label(entry),
        })

    os.makedirs(output_dir, exist_ok=True)
    if processed_dir:
        os.makedirs(processed_dir, exist_ok=True)

    stamp_image_paths = {
        os.path.abspath(e["image_path"])
        for e in stamp_entries if e.get("source") != "text" and e.get("image_path")
    }
    files = sorted(
        f for f in os.listdir(input_dir)
        if os.path.splitext(f)[1].lower() in (SUPPORTED_IMG_EXT | SUPPORTED_PDF_EXT)
        and os.path.abspath(os.path.join(input_dir, f)) not in stamp_image_paths
    )

    total = len(files)
    if total == 0:
        log("找不到任何 PDF / JPG / PNG 檔案（可能都已經蓋過章、被搬走了）。")
        return 0, 0

    ok_count = 0
    fail_count = 0

    for i, filename in enumerate(files, 1):
        input_path = os.path.join(input_dir, filename)
        name, ext = os.path.splitext(filename)
        out_name = f"{name}_{suffix}{ext}"
        output_path = os.path.join(output_dir, out_name)

        log(f"[{i}/{total}] 處理中: {filename}")
        try:
            if ext.lower() in SUPPORTED_PDF_EXT:
                stamp_pdf_file(input_path, output_path, resolved_stamps,
                                mode=mode, add_timestamp=add_timestamp,
                                timestamp_text=timestamp_text,
                                timestamp_color=timestamp_color,
                                extend_blank=extend_blank, log=log)
            else:
                stamp_image_file(input_path, output_path, resolved_stamps,
                                  mode=mode, add_timestamp=add_timestamp,
                                  timestamp_text=timestamp_text,
                                  timestamp_color=timestamp_color,
                                  extend_blank=extend_blank, log=log)
            log(f"    ✔ 完成 -> {out_name}")

            if processed_dir:
                dest = _unique_dest_path(processed_dir, filename)
                shutil.move(input_path, dest)
                log(f"    📁 原始檔已搬到: {os.path.basename(dest)}")

            ok_count += 1
        except Exception as e:
            log(f"    ✘ 失敗: {e}")
            fail_count += 1

        if progress_cb:
            progress_cb(i, total)

    log("-" * 40)
    log(f"完成！成功 {ok_count} 個，失敗 {fail_count} 個。")
    return ok_count, fail_count


# ============================================================
# GUI
# ============================================================
class AddStampDialog:
    """新增/編輯一個章的小視窗"""

    def __init__(self, parent, on_save, existing=None):
        self.on_save = on_save
        self.win = tk.Toplevel(parent)
        self.win.title("新增章" if existing is None else "編輯章")
        self.win.resizable(False, False)
        self.win.transient(parent)
        self.win.grab_set()

        pad = {"padx": 10, "pady": 5}
        e = existing or {}

        self.source = tk.StringVar(value=e.get("source", "image"))
        self.image_path = tk.StringVar(value=e.get("image_path", ""))
        self.unit = tk.StringVar(value=e.get("unit", ""))
        self.title_ = tk.StringVar(value=e.get("title", ""))
        self.name = tk.StringVar(value=e.get("name", ""))
        self.width_pct = tk.IntVar(value=e.get("width_pct", 14))
        self.offset_index = tk.IntVar(value=e.get("offset_index", 0))
        self.stack_direction_label = tk.StringVar(
            value="下方" if e.get("stack_direction") == "down" else "右方")
        self.use_custom_pos = tk.BooleanVar(value=(e.get("position") == "custom"))
        self.custom_x_pct = tk.IntVar(value=e.get("custom_x_pct", 75))
        self.custom_y_pct = tk.IntVar(value=e.get("custom_y_pct", 80))
        self.position_label = tk.StringVar(
            value=POSITION_CODE_TO_LABEL.get(e.get("position", DEFAULT_POSITION),
                                              POSITION_CHOICES[0][1]))

        row = 0
        ttk.Label(self.win, text="章的來源：").grid(row=row, column=0, sticky="w", **pad)
        src_frm = ttk.Frame(self.win)
        src_frm.grid(row=row, column=1, columnspan=2, sticky="w")
        ttk.Radiobutton(src_frm, text="使用圖片檔", variable=self.source,
                         value="image", command=self._refresh).pack(side="left")
        ttk.Radiobutton(src_frm, text="文字自動產生", variable=self.source,
                         value="text", command=self._refresh).pack(side="left", padx=10)

        row += 1
        self.image_row = row
        ttk.Label(self.win, text="印章圖片：").grid(row=row, column=0, sticky="w", **pad)
        self.image_entry = ttk.Entry(self.win, textvariable=self.image_path, width=38)
        self.image_entry.grid(row=row, column=1, sticky="w")
        self.image_btn = ttk.Button(self.win, text="選擇圖片", command=self._choose_image)
        self.image_btn.grid(row=row, column=2, padx=6)

        row += 1
        self.unit_row = row
        ttk.Label(self.win, text="單位/科別（選填，例：藥劑科）：").grid(
            row=row, column=0, sticky="w", **pad)
        self.unit_entry = ttk.Entry(self.win, textvariable=self.unit, width=20)
        self.unit_entry.grid(row=row, column=1, sticky="w")

        row += 1
        self.title_row = row
        ttk.Label(self.win, text="職稱（選填，例：院聘主任）：").grid(
            row=row, column=0, sticky="w", **pad)
        self.title_entry = ttk.Entry(self.win, textvariable=self.title_, width=20)
        self.title_entry.grid(row=row, column=1, sticky="w")

        row += 1
        self.name_row = row
        ttk.Label(self.win, text="姓名（必填，例：方喬玲）：").grid(
            row=row, column=0, sticky="w", **pad)
        self.name_entry = ttk.Entry(self.win, textvariable=self.name, width=20)
        self.name_entry.grid(row=row, column=1, sticky="w")

        row += 1
        ttk.Label(self.win, text="蓋章位置：").grid(row=row, column=0, sticky="w", **pad)
        self.position_combo = ttk.Combobox(
            self.win, textvariable=self.position_label, state="readonly",
            width=16, values=[l for _, l in POSITION_CHOICES])
        self.position_combo.grid(row=row, column=1, sticky="w")

        row += 1
        custom_frm = ttk.Frame(self.win)
        custom_frm.grid(row=row, column=0, columnspan=3, sticky="w", padx=10)
        self.custom_check = ttk.Checkbutton(
            custom_frm, text="改用自訂精確座標（適合固定格式、常常收到的報表）",
            variable=self.use_custom_pos, command=self._refresh_position_mode)
        self.custom_check.pack(side="left")

        row += 1
        coord_frm = ttk.Frame(self.win)
        coord_frm.grid(row=row, column=0, columnspan=3, sticky="w", padx=30)
        ttk.Label(coord_frm, text="X（左邊算起的%）：").pack(side="left")
        self.x_spin = ttk.Spinbox(coord_frm, from_=0, to=95, textvariable=self.custom_x_pct, width=5)
        self.x_spin.pack(side="left")
        ttk.Label(coord_frm, text="　Y（上面算起的%）：").pack(side="left")
        self.y_spin = ttk.Spinbox(coord_frm, from_=0, to=95, textvariable=self.custom_y_pct, width=5)
        self.y_spin.pack(side="left")

        row += 1
        ttk.Label(
            self.win,
            text="（X/Y 是章的左上角要落在文件的第幾% 位置，例如 X=75、Y=80 大約\n"
                 "　落在右下角附近。程式會先試這個位置，如果剛好疊到文字/圖表內容，\n"
                 "　會自動在附近微調到真正空白處。）",
            foreground="#777", justify="left").grid(
            row=row, column=0, columnspan=3, sticky="w", padx=10)

        row += 1
        ttk.Label(self.win, text="章的大小（佔文件寬度%）：").grid(
            row=row, column=0, sticky="w", **pad)
        ttk.Spinbox(self.win, from_=5, to=40, textvariable=self.width_pct,
                    width=6).grid(row=row, column=1, sticky="w")

        row += 1
        ttk.Label(self.win, text="這個位置前面已經有幾個章：").grid(
            row=row, column=0, sticky="w", **pad)
        ttk.Spinbox(self.win, from_=0, to=5, textvariable=self.offset_index,
                    width=6).grid(row=row, column=1, sticky="w")

        row += 1
        ttk.Label(self.win, text="跟前面的章疊放方向：").grid(
            row=row, column=0, sticky="w", **pad)
        ttk.Combobox(self.win, textvariable=self.stack_direction_label, state="readonly",
                     width=8, values=["右方", "下方"]).grid(row=row, column=1, sticky="w")

        row += 1
        ttk.Label(
            self.win,
            text="（分次蓋章才需要設：例如組長先蓋存檔，主任拿到檔案後另外執行本程式，\n"
                 "　只設定主任自己的章，這裡填「1」讓主任的章自動排在組長章的右方或\n"
                 "　下方，不會跟組長已經蓋好、但這次看不到的章重疊。同一次批次一起蓋\n"
                 "　則留 0。）",
            foreground="#777", justify="left").grid(
            row=row, column=0, columnspan=3, sticky="w", padx=10)

        row += 1
        btn_frm = ttk.Frame(self.win)
        btn_frm.grid(row=row, column=0, columnspan=3, pady=12)
        ttk.Button(btn_frm, text="確定", command=self._save).pack(side="left", padx=6)
        ttk.Button(btn_frm, text="取消", command=self.win.destroy).pack(side="left", padx=6)

        self._refresh()
        self._refresh_position_mode()

    def _refresh_position_mode(self):
        use_custom = self.use_custom_pos.get()
        self.position_combo.configure(state="disabled" if use_custom else "readonly")
        self.x_spin.configure(state="normal" if use_custom else "disabled")
        self.y_spin.configure(state="normal" if use_custom else "disabled")

    def _refresh(self):
        is_image = self.source.get() == "image"
        state_img = "normal" if is_image else "disabled"
        state_txt = "disabled" if is_image else "normal"
        self.image_entry.configure(state=state_img)
        self.image_btn.configure(state=state_img)
        self.unit_entry.configure(state=state_txt)
        self.title_entry.configure(state=state_txt)
        self.name_entry.configure(state=state_txt)

    def _choose_image(self):
        f = filedialog.askopenfilename(
            title="選擇印章圖片",
            filetypes=[("圖片檔", "*.jpg *.jpeg *.png"), ("所有檔案", "*.*")])
        if f:
            self.image_path.set(f)

    def _save(self):
        source = self.source.get()
        if source == "image":
            if not self.image_path.get().strip() or not os.path.isfile(self.image_path.get().strip()):
                messagebox.showerror("錯誤", "請選擇有效的印章圖片檔")
                return
        else:
            if not self.name.get().strip():
                messagebox.showerror("錯誤", "文字章至少要填姓名")
                return

        entry = {
            "source": source,
            "image_path": self.image_path.get().strip(),
            "unit": self.unit.get().strip(),
            "title": self.title_.get().strip(),
            "name": self.name.get().strip(),
            "width_pct": self.width_pct.get(),
            "offset_index": self.offset_index.get(),
            "stack_direction": "down" if self.stack_direction_label.get() == "下方" else "right",
            "position": ("custom" if self.use_custom_pos.get() else
                         POSITION_LABEL_TO_CODE.get(self.position_label.get(), DEFAULT_POSITION)),
            "custom_x_pct": self.custom_x_pct.get(),
            "custom_y_pct": self.custom_y_pct.get(),
        }
        self.on_save(entry)
        self.win.destroy()


class VerifyIdentityDialog:
    """
    蓋章前的身分驗證視窗：輸入員工編號 + 出生年月日，呼叫院內 API 查詢員工
    資料，核對查到的姓名跟出生年月日（emp_birth，民國年格式）是否都跟這個
    章一致，兩項都符合才能蓋章。
    """

    def __init__(self, parent, stamp_label, expected_name, api_url):
        self.expected_name = expected_name
        self.api_url = api_url
        self.result = None  # 'ok' | 'skip' | 'abort'
        self.verified_emp_no = None
        self.verified_birthdate = None

        self.win = tk.Toplevel(parent)
        self.win.title("蓋章前身分驗證")
        self.win.resizable(False, False)
        self.win.transient(parent)
        self.win.grab_set()
        self.win.protocol("WM_DELETE_WINDOW", self._on_abort)

        pad = {"padx": 10, "pady": 5}

        ttk.Label(self.win, text=f"即將蓋章：{stamp_label}（章上姓名：{expected_name}）",
                  font=("", 10, "bold")).grid(row=0, column=0, columnspan=3, sticky="w", **pad)

        self.emp_no = tk.StringVar()
        self.birthdate = tk.StringVar()

        ttk.Label(self.win, text="員工編號：").grid(row=1, column=0, sticky="w", **pad)
        self.emp_entry = ttk.Entry(self.win, textvariable=self.emp_no, width=16)
        self.emp_entry.grid(row=1, column=1, sticky="w")

        ttk.Label(self.win, text="出生年月日（例：1990/01/01）：").grid(
            row=2, column=0, sticky="w", **pad)
        ttk.Entry(self.win, textvariable=self.birthdate, width=16).grid(
            row=2, column=1, sticky="w")

        self.status_label = ttk.Label(self.win, text="", foreground="#555", wraplength=360,
                                       justify="left")
        self.status_label.grid(row=3, column=0, columnspan=3, sticky="w", padx=10, pady=(4, 4))

        btn_frm = ttk.Frame(self.win)
        btn_frm.grid(row=4, column=0, columnspan=3, pady=10)
        self.verify_btn = ttk.Button(btn_frm, text="查詢並比對", command=self._verify)
        self.verify_btn.pack(side="left", padx=4)
        self.confirm_btn = ttk.Button(btn_frm, text="比對成功，蓋這個章",
                                       command=self._on_confirm, state="disabled")
        self.confirm_btn.pack(side="left", padx=4)
        ttk.Button(btn_frm, text="跳過這個章", command=self._on_skip).pack(side="left", padx=4)
        ttk.Button(btn_frm, text="取消全部", command=self._on_abort).pack(side="left", padx=4)

        self.emp_entry.focus_set()

    def _verify(self):
        emp_no = self.emp_no.get().strip()
        birthdate_input = self.birthdate.get().strip()
        if not emp_no:
            self.status_label.configure(text="請輸入員工編號", foreground="#c00")
            return
        if not birthdate_input:
            self.status_label.configure(text="請輸入出生年月日", foreground="#c00")
            return

        try:
            expected_birth = format_minguo_birthdate(birthdate_input)
        except ValueError as e:
            self.status_label.configure(text=str(e), foreground="#c00")
            return

        self.verify_btn.configure(state="disabled")
        self.status_label.configure(text="查詢中...", foreground="#555")
        self.win.update_idletasks()

        try:
            info = fetch_employee_info(emp_no, self.api_url)
        except Exception as e:
            self.status_label.configure(text=f"查詢失敗：{e}", foreground="#c00")
            self.verify_btn.configure(state="normal")
            self.confirm_btn.configure(state="disabled")
            return

        self.verify_btn.configure(state="normal")
        actual_name = (info.get("emp_name") or "").strip()
        actual_birth = (info.get("emp_birth") or "").strip()

        name_ok = actual_name == self.expected_name
        birth_ok = actual_birth == expected_birth

        if name_ok and birth_ok:
            self.status_label.configure(
                text=f"✔ 查到「{actual_name}」，姓名與出生年月日都核對相符，可以蓋章。",
                foreground="#080")
            self.confirm_btn.configure(state="normal")
            self.verified_emp_no = emp_no
            self.verified_birthdate = birthdate_input
        else:
            problems = []
            if not name_ok:
                problems.append(f"查到姓名「{actual_name}」，跟章上姓名「{self.expected_name}」不一致")
            if not birth_ok:
                problems.append("出生年月日不一致")
            self.status_label.configure(
                text="✘ " + "；".join(problems) + "，不能蓋這個章。", foreground="#c00")
            self.confirm_btn.configure(state="disabled")

    def _on_confirm(self):
        self.result = "ok"
        self.win.destroy()

    def _on_skip(self):
        self.result = "skip"
        self.win.destroy()

    def _on_abort(self):
        self.result = "abort"
        self.win.destroy()



    def __init__(self, root):
        self.root = root
        root.title("批次自動蓋章工具")
        root.geometry("720x960")
        root.resizable(False, False)

        pad = {"padx": 10, "pady": 6}
        settings = load_settings()

        self.input_dir = tk.StringVar(value=settings.get("input_dir", ""))
        self.output_dir = tk.StringVar(value=settings.get("output_dir", ""))
        self.processed_dir = tk.StringVar(value=settings.get("processed_dir", ""))
        self.mode_label = tk.StringVar(
            value=settings.get("mode_label", MODE_CHOICES[0][1]))
        self.suffix_choice = tk.StringVar(
            value=settings.get("suffix_choice", SUFFIX_PRESETS[0]))
        self.suffix_custom = tk.StringVar(
            value=settings.get("suffix_custom", "已蓋章"))
        self.add_timestamp = tk.BooleanVar(value=settings.get("add_timestamp", False))
        self.timestamp_text = tk.StringVar(value=settings.get("timestamp_text", ""))
        self.extend_blank = tk.BooleanVar(value=settings.get("extend_blank", False))
        self.api_verify_enabled = tk.BooleanVar(value=settings.get("api_verify_enabled", False))
        self.api_url = tk.StringVar(value=settings.get("api_url", DEFAULT_API_URL))
        self.custom_font_path = tk.StringVar(value=settings.get("custom_font_path", ""))
        self.stamp_entries = settings.get("stamp_entries", [])

        frm = ttk.Frame(root)
        frm.pack(fill="both", expand=True)

        # ① 輸入資料夾
        ttk.Label(frm, text="① 待蓋章資料夾（同仁交來的 PDF/JPG/PNG）：").grid(
            row=0, column=0, sticky="w", **pad)
        ttk.Entry(frm, textvariable=self.input_dir, width=58).grid(
            row=1, column=0, sticky="w", padx=10)
        ttk.Button(frm, text="選擇資料夾", command=self.choose_input_dir).grid(
            row=1, column=1, padx=6)

        # ② 輸出資料夾
        ttk.Label(frm, text="② 輸出資料夾（蓋好章的檔案存放處）：").grid(
            row=2, column=0, sticky="w", **pad)
        ttk.Entry(frm, textvariable=self.output_dir, width=58).grid(
            row=3, column=0, sticky="w", padx=10)
        ttk.Button(frm, text="選擇資料夾", command=self.choose_output_dir).grid(
            row=3, column=1, padx=6)

        # ③ 章清單
        ttk.Label(frm, text="③ 蓋章清單（可新增多個章，例如組長章＋主任章）：").grid(
            row=4, column=0, columnspan=2, sticky="w", padx=10, pady=(10, 0))
        list_frm = ttk.Frame(frm)
        list_frm.grid(row=5, column=0, columnspan=2, sticky="w", padx=10)
        self.stamp_listbox = tk.Listbox(list_frm, width=76, height=5)
        self.stamp_listbox.pack(side="left")
        btn_col = ttk.Frame(list_frm)
        btn_col.pack(side="left", padx=6)
        ttk.Button(btn_col, text="新增章", command=self.add_stamp).pack(fill="x", pady=2)
        ttk.Button(btn_col, text="刪除選取", command=self.remove_stamp).pack(fill="x", pady=2)
        ttk.Button(btn_col, text="上移", command=self.move_stamp_up).pack(fill="x", pady=2)
        ttk.Button(btn_col, text="下移", command=self.move_stamp_down).pack(fill="x", pady=2)

        # ④ 蓋章方式
        mode_frm = ttk.Frame(frm)
        mode_frm.grid(row=6, column=0, columnspan=2, sticky="w", padx=10, pady=(10, 0))
        ttk.Label(mode_frm, text="④ 蓋章方式：").pack(side="left")
        ttk.Combobox(mode_frm, textvariable=self.mode_label, state="readonly",
                     width=34, values=[l for _, l in MODE_CHOICES]).pack(side="left", padx=6)

        # ⑤ 檔名後綴
        suffix_frm = ttk.Frame(frm)
        suffix_frm.grid(row=7, column=0, columnspan=2, sticky="w", padx=10, pady=(6, 0))
        ttk.Label(suffix_frm, text="⑤ 檔名後綴：").pack(side="left")
        suffix_combo = ttk.Combobox(suffix_frm, textvariable=self.suffix_choice,
                                     state="readonly", width=10, values=SUFFIX_PRESETS)
        suffix_combo.pack(side="left", padx=6)
        self.suffix_entry = ttk.Entry(suffix_frm, textvariable=self.suffix_custom, width=14)
        self.suffix_entry.pack(side="left", padx=(4, 0))
        suffix_combo.bind("<<ComboboxSelected>>", lambda e: self._update_suffix_entry_state())
        self._update_suffix_entry_state()

        # ⑥ 時間戳記
        ts_frm = ttk.Frame(frm)
        ts_frm.grid(row=8, column=0, columnspan=2, sticky="w", padx=10, pady=(6, 0))
        ttk.Checkbutton(
            ts_frm, text="⑥ 每個章的正下方印上時間（民國年/月/日 時:分，例如 115/09/26 14:35）",
            variable=self.add_timestamp).pack(side="left")

        ts_custom_frm = ttk.Frame(frm)
        ts_custom_frm.grid(row=9, column=0, columnspan=2, sticky="w", padx=30, pady=(2, 0))
        ttk.Label(ts_custom_frm, text="自訂時間文字（留空=自動使用目前時間）：").pack(side="left")
        ttk.Entry(ts_custom_frm, textvariable=self.timestamp_text, width=20).pack(side="left", padx=4)

        # ⑦ 新增空白區域蓋章
        extend_frm = ttk.Frame(frm)
        extend_frm.grid(row=10, column=0, columnspan=2, sticky="w", padx=10, pady=(6, 0))
        ttk.Checkbutton(
            extend_frm,
            text="⑦ 在文件最下方新增一塊空白區域蓋章（不佔用原內容、保證不壓字，不需要判斷版面）",
            variable=self.extend_blank).pack(side="left")

        # ⑧ 原始檔搬移
        ttk.Label(frm, text="⑧ 已核章的原始檔搬到（留空則不搬移）：").grid(
            row=11, column=0, sticky="w", padx=10, pady=(10, 0))
        ttk.Entry(frm, textvariable=self.processed_dir, width=58).grid(
            row=12, column=0, sticky="w", padx=10)
        ttk.Button(frm, text="選擇資料夾", command=self.choose_processed_dir).grid(
            row=12, column=1, padx=6)

        # ⑨ 自訂中文字型
        ttk.Label(frm, text="⑨ 自訂中文字型檔（用「文字自動產生」章時才需要，留空自動偵測）：").grid(
            row=13, column=0, sticky="w", padx=10, pady=(10, 0))
        ttk.Entry(frm, textvariable=self.custom_font_path, width=58).grid(
            row=14, column=0, sticky="w", padx=10)
        ttk.Button(frm, text="選擇字型檔", command=self.choose_font).grid(
            row=14, column=1, padx=6)

        # ⑩ 院內 API 身分驗證
        api_frm = ttk.Frame(frm)
        api_frm.grid(row=15, column=0, columnspan=2, sticky="w", padx=10, pady=(10, 0))
        ttk.Checkbutton(
            api_frm,
            text="⑩ 按「開始批次蓋章」前，先用院內 API 核對員工編號對應的姓名跟章上姓名是否一致",
            variable=self.api_verify_enabled).pack(side="left")

        ttk.Label(frm, text="API 網址：").grid(row=16, column=0, sticky="w", padx=10)
        ttk.Entry(frm, textvariable=self.api_url, width=58).grid(
            row=17, column=0, sticky="w", padx=10)

        note = ("說明：\n"
                "・PDF 只會蓋在「最後一頁」；圖片檔會蓋在整張圖片上。\n"
                "・如果有兩個章選了同一個位置，程式會自動把它們排成一排，不會疊在一起。\n"
                "・「固定位置」會直接貼齊邊緣；「智慧偵測」在單一章時會找附近最空白處，\n"
                "  多章共用同位置時會自動改用固定排列。\n"
                "・勾選⑦後，位置設定只會決定靠左/置中/靠右，蓋在新加的空白區域裡，\n"
                "  不會再判斷版面內容。\n"
                "・勾選⑩後，只會核對「文字自動產生」章（有填姓名的章）；圖片章不會核對。\n"
                "  院內 API 查到的姓名跟出生年月日都要跟章上設定一致，才能蓋這個章。\n"
                "・原始檔本身內容不會被修改，設定內容下次開啟會自動記住。")
        ttk.Label(frm, text=note, foreground="#555").grid(
            row=18, column=0, columnspan=2, sticky="w", padx=10, pady=(10, 0))

        self.start_btn = ttk.Button(frm, text="開始批次蓋章", command=self.start)
        self.start_btn.grid(row=19, column=0, columnspan=2, pady=10)

        self.progress = ttk.Progressbar(frm, length=640, mode="determinate")
        self.progress.grid(row=20, column=0, columnspan=2, padx=10)

        self.log_box = tk.Text(frm, height=8, width=82, state="disabled", bg="#f7f7f7")
        self.log_box.grid(row=21, column=0, columnspan=2, padx=10, pady=10)

        self._refresh_stamp_listbox()

        if fitz is None:
            self.log("⚠ 尚未安裝 PyMuPDF，PDF 功能無法使用。"
                      "請先在命令列執行: pip install PyMuPDF")

    # -------- 章清單 --------
    def _refresh_stamp_listbox(self):
        self.stamp_listbox.delete(0, "end")
        for e in self.stamp_entries:
            src = "文字章" if e.get("source") == "text" else "圖片章"
            label = stamp_entry_label(e)
            if e.get("position") == "custom":
                pos = f"自訂座標({e.get('custom_x_pct', 75)}%,{e.get('custom_y_pct', 80)}%)"
            else:
                pos = POSITION_CODE_TO_LABEL.get(e.get("position"), "")
            off = e.get("offset_index", 0)
            direction_txt = "下方" if e.get("stack_direction") == "down" else "右方"
            off_txt = f"　讓開:{off}格({direction_txt})" if off else ""
            self.stamp_listbox.insert(
                "end", f"[{src}] {label}　位置:{pos}　大小:{e.get('width_pct')}%{off_txt}")

    def add_stamp(self):
        def on_save(entry):
            self.stamp_entries.append(entry)
            self._refresh_stamp_listbox()
        AddStampDialog(self.root, on_save)

    def remove_stamp(self):
        sel = self.stamp_listbox.curselection()
        if not sel:
            return
        idx = sel[0]
        del self.stamp_entries[idx]
        self._refresh_stamp_listbox()

    def move_stamp_up(self):
        sel = self.stamp_listbox.curselection()
        if not sel or sel[0] == 0:
            return
        idx = sel[0]
        self.stamp_entries[idx - 1], self.stamp_entries[idx] = (
            self.stamp_entries[idx], self.stamp_entries[idx - 1])
        self._refresh_stamp_listbox()
        self.stamp_listbox.selection_set(idx - 1)

    def move_stamp_down(self):
        sel = self.stamp_listbox.curselection()
        if not sel or sel[0] >= len(self.stamp_entries) - 1:
            return
        idx = sel[0]
        self.stamp_entries[idx + 1], self.stamp_entries[idx] = (
            self.stamp_entries[idx], self.stamp_entries[idx + 1])
        self._refresh_stamp_listbox()
        self.stamp_listbox.selection_set(idx + 1)

    # -------- 後綴輸入框啟用/停用 --------
    def _update_suffix_entry_state(self):
        if self.suffix_choice.get() == "自訂":
            self.suffix_entry.configure(state="normal")
        else:
            self.suffix_entry.configure(state="disabled")

    def _resolve_suffix(self):
        choice = self.suffix_choice.get()
        if choice == "自訂":
            text = self.suffix_custom.get().strip()
            return text if text else "已蓋章"
        return choice

    # -------- 選擇檔案/資料夾 --------
    def choose_input_dir(self):
        d = filedialog.askdirectory(title="選擇待蓋章資料夾")
        if d:
            self.input_dir.set(d)

    def choose_output_dir(self):
        d = filedialog.askdirectory(title="選擇輸出資料夾")
        if d:
            self.output_dir.set(d)

    def choose_processed_dir(self):
        d = filedialog.askdirectory(title="選擇已核章原始檔要搬去的資料夾")
        if d:
            self.processed_dir.set(d)

    def choose_font(self):
        f = filedialog.askopenfilename(
            title="選擇中文字型檔",
            filetypes=[("字型檔", "*.ttf *.ttc *.otf"), ("所有檔案", "*.*")])
        if f:
            self.custom_font_path.set(f)

    # -------- 記錄訊息 --------
    def log(self, msg):
        def _append():
            self.log_box.configure(state="normal")
            ts = datetime.now().strftime("%H:%M:%S")
            self.log_box.insert("end", f"[{ts}] {msg}\n")
            self.log_box.see("end")
            self.log_box.configure(state="disabled")
        self.root.after(0, _append)

    def set_progress(self, i, total):
        def _set():
            self.progress["maximum"] = total
            self.progress["value"] = i
        self.root.after(0, _set)

    # -------- 開始處理 --------
    def start(self):
        input_dir = self.input_dir.get().strip()
        output_dir = self.output_dir.get().strip()

        if not input_dir or not os.path.isdir(input_dir):
            messagebox.showerror("錯誤", "請選擇有效的待蓋章資料夾")
            return
        if not output_dir:
            messagebox.showerror("錯誤", "請選擇輸出資料夾")
            return
        if os.path.abspath(input_dir) == os.path.abspath(output_dir):
            messagebox.showerror("錯誤", "輸出資料夾請不要跟待蓋章資料夾相同")
            return
        if not self.stamp_entries:
            messagebox.showerror("錯誤", "請至少新增一個章")
            return

        processed_dir = self.processed_dir.get().strip()
        if processed_dir:
            if os.path.abspath(processed_dir) == os.path.abspath(input_dir):
                messagebox.showerror("錯誤", "「原始檔搬移資料夾」請不要跟待蓋章資料夾相同")
                return
            if os.path.abspath(processed_dir) == os.path.abspath(output_dir):
                messagebox.showerror("錯誤", "「原始檔搬移資料夾」請不要跟輸出資料夾相同")
                return

        stamp_entries = list(self.stamp_entries)
        stamp_entries_for_run = stamp_entries

        if self.api_verify_enabled.get():
            api_url = self.api_url.get().strip() or DEFAULT_API_URL
            filtered = []
            for entry in stamp_entries:
                if entry.get("source") == "text" and entry.get("name"):
                    label = stamp_entry_label(entry)
                    dlg = VerifyIdentityDialog(self.root, label, entry.get("name"), api_url)
                    self.root.wait_window(dlg.win)
                    if dlg.result == "abort":
                        return
                    if dlg.result == "ok":
                        filtered.append(entry)
                    # result == "skip"：這次不蓋這個章，但保留在清單裡供下次使用
                else:
                    filtered.append(entry)
            if not filtered:
                messagebox.showerror("錯誤", "所有章這次都被跳過了，沒有章可以蓋")
                return
            stamp_entries_for_run = filtered

        self.start_btn.configure(state="disabled")
        self.log_box.configure(state="normal")
        self.log_box.delete("1.0", "end")
        self.log_box.configure(state="disabled")

        mode_code = MODE_LABEL_TO_CODE.get(self.mode_label.get(), DEFAULT_MODE)
        suffix = self._resolve_suffix()
        add_timestamp = self.add_timestamp.get()
        timestamp_text = self.timestamp_text.get().strip() or None
        extend_blank = self.extend_blank.get()
        custom_font_path = self.custom_font_path.get().strip() or None

        save_settings({
            "input_dir": input_dir,
            "output_dir": output_dir,
            "processed_dir": processed_dir,
            "mode_label": self.mode_label.get(),
            "suffix_choice": self.suffix_choice.get(),
            "suffix_custom": self.suffix_custom.get(),
            "add_timestamp": add_timestamp,
            "timestamp_text": self.timestamp_text.get().strip(),
            "extend_blank": extend_blank,
            "custom_font_path": self.custom_font_path.get().strip(),
            "stamp_entries": stamp_entries,
            "api_verify_enabled": self.api_verify_enabled.get(),
            "api_url": self.api_url.get().strip(),
        })

        def worker():
            try:
                batch_process(
                    input_dir, stamp_entries_for_run, output_dir,
                    mode=mode_code,
                    suffix=suffix,
                    add_timestamp=add_timestamp,
                    timestamp_text=timestamp_text,
                    extend_blank=extend_blank,
                    processed_dir=processed_dir or None,
                    custom_font_path=custom_font_path,
                    log=self.log,
                    progress_cb=self.set_progress,
                )
            except Exception as e:
                self.log(f"發生錯誤: {e}")
                self.log(traceback.format_exc())
            finally:
                self.root.after(0, lambda: self.start_btn.configure(state="normal"))

        threading.Thread(target=worker, daemon=True).start()


def main():
    if not TKINTER_AVAILABLE:
        print("找不到 tkinter 模組，無法開啟視窗介面。\n"
              "Windows 版 Python 安裝時通常已內建 tkinter；\n"
              "若是 Linux，請執行: sudo apt install python3-tk 後再試一次。")
        sys.exit(1)
    root = tk.Tk()
    app = StampApp(root)
    root.mainloop()


if __name__ == "__main__":
    main()
