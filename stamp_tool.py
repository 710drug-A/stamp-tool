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
import sys
import json
import shutil
import threading
import traceback
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

# 設定檔：跟執行檔（或程式）放在同一個資料夾，記住上次用過的選項
if getattr(sys, "frozen", False):
    _BASE_DIR = os.path.dirname(sys.executable)
else:
    _BASE_DIR = os.path.dirname(os.path.abspath(__file__))
CONFIG_PATH = os.path.join(_BASE_DIR, "stamp_tool_settings.json")


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
    "mingliu.ttc",   # 細明體（繁中 Windows 必有）
    "kaiu.ttf",      # 標楷體 DFKai-SB
    "msjh.ttc", "MSJH.TTC",   # 微軟正黑體
    "simsun.ttc",    # 新細明體
    "msyh.ttc",      # 微軟雅黑
    "PingFang.ttc",  # macOS
    # 下面這幾個是 Linux 常見路徑，主要給開發/測試用
    "/usr/share/fonts/opentype/noto/NotoSansCJK-Regular.ttc",
    "/usr/share/fonts/opentype/noto/NotoSerifCJK-Regular.ttc",
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


def generate_text_stamp(unit="", title="", name="", custom_font_path=None,
                         color=(200, 0, 0), canvas_size=(640, 260), border=9):
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

    W, H = canvas_size
    img = Image.new("RGBA", (W, H), (255, 255, 255, 0))
    draw = ImageDraw.Draw(img)
    fill = color + (255,)

    draw.rectangle([border // 2, border // 2, W - 1 - border // 2, H - 1 - border // 2],
                    outline=fill, width=border)

    pad = border + int(H * 0.08)
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
    left_col_w = int(avail_w * 0.40)
    col_gap = int(avail_w * 0.035)
    left_x = inner_left
    right_x0 = inner_left + left_col_w + col_gap
    right_w = max(20, inner_right - right_x0)

    # -- 左欄：單位（上）、職稱（下），靠左對齊，整體垂直置中 --
    small_font_size = max(12, int(avail_h * 0.19))
    small_font = get_cjk_font(small_font_size, custom_font_path)
    lines = [t for t in (unit, title) if t]
    line_gap = int(small_font_size * 0.35)

    heights = [draw.textbbox((0, 0), line, font=small_font)[3] -
               draw.textbbox((0, 0), line, font=small_font)[1] for line in lines]
    total_left_h = sum(heights) + line_gap * (len(lines) - 1)
    cur_y = inner_top + (avail_h - total_left_h) // 2

    for line, lh in zip(lines, heights):
        _draw_spaced_text(draw, line, left_x, cur_y, small_font, fill,
                           extra_gap=0.5, align="left")
        cur_y += lh + line_gap

    # -- 右欄：姓名，盡量撐滿章的高度，在右欄範圍內水平置中 --
    name_font, bbox_n, n_w = _fit_name(int(avail_h * 0.92), right_w * 0.96)
    n_h = bbox_n[3] - bbox_n[1]
    name_cx = right_x0 + right_w // 2
    name_cy = inner_top + avail_h // 2
    tx = name_cx - n_w // 2 - bbox_n[0]
    ty = name_cy - n_h // 2 - bbox_n[1]
    draw.text((tx, ty), name, font=name_font, fill=fill)

    return img


def resolve_stamp_entry(entry, custom_font_path=None):
    """把 GUI 上設定的一筆『章』資料，轉成實際的 RGBA 印章圖片"""
    if entry.get("source") == "text":
        return generate_text_stamp(
            unit=entry.get("unit", ""),
            title=entry.get("title", ""),
            name=entry.get("name", ""),
            custom_font_path=custom_font_path,
        )
    else:
        path = entry.get("image_path", "")
        if not path or not os.path.isfile(path):
            raise FileNotFoundError(f"找不到印章圖片: {path}")
        return load_stamp_rgba(path)


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
                      mode=DEFAULT_MODE, add_timestamp=False, log=print):
    img = Image.open(input_path).convert("RGB")
    W, H = img.size

    gray = np.array(img.convert("L")) if mode == "smart" else None
    layout = layout_stamps(W, H, stamps, mode=mode, gray=gray,
                            add_timestamp=add_timestamp, log=log)

    ts_text = datetime.now().strftime("%m/%d %H:%M") if add_timestamp else None

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
            draw.text((tx, ty), ts_text, fill=(180, 0, 0), font=font)

    ext = os.path.splitext(output_path)[1].lower()
    if ext in (".jpg", ".jpeg"):
        img.save(output_path, quality=95)
    else:
        img.save(output_path)
    return True


# ============================================================
# 蓋章：PDF（只蓋最後一頁）
# ============================================================
def stamp_pdf_file(input_path, output_path, stamps,
                    mode=DEFAULT_MODE, add_timestamp=False,
                    render_zoom=1.5, log=print):
    if fitz is None:
        raise RuntimeError("尚未安裝 PyMuPDF，請先執行: pip install PyMuPDF")

    doc = fitz.open(input_path)
    if doc.page_count == 0:
        raise RuntimeError("PDF 沒有任何頁面")

    page = doc[-1]
    page_rect = page.rect

    gray = None
    if mode == "smart":
        mat = fitz.Matrix(render_zoom, render_zoom)
        pix = page.get_pixmap(matrix=mat, colorspace=fitz.csGRAY)
        gray = np.frombuffer(pix.samples, dtype=np.uint8).reshape(pix.height, pix.width)
        canvas_w, canvas_h = pix.width, pix.height
    else:
        canvas_w, canvas_h = page_rect.width, page_rect.height

    layout = layout_stamps(canvas_w, canvas_h, stamps, mode=mode, gray=gray,
                           add_timestamp=add_timestamp, log=log)

    scale = (1.0 / render_zoom) if (mode == "smart") else 1.0
    ts_text = datetime.now().strftime("%m/%d %H:%M") if add_timestamp else None

    tmp_paths = []
    try:
        for spec, info in zip(stamps, layout):
            x_pt = info["x"] * scale
            y_pt = info["y"] * scale
            w_pt = info["w"] * scale
            h_pt = info["h"] * scale

            if info.get("score") is not None:
                log(f"    [{spec['label']}] 最後一頁空白分數: {info['score']:.2f}")

            rect = fitz.Rect(x_pt, y_pt, x_pt + w_pt, y_pt + h_pt)
            tmp_path = output_path + f"._stamp_tmp_{len(tmp_paths)}.png"
            spec["rgba"].save(tmp_path)
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
                                  fontsize=font_size, color=(0.7, 0, 0))

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
                   add_timestamp=False, processed_dir=None,
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
                                mode=mode, add_timestamp=add_timestamp, log=log)
            else:
                stamp_image_file(input_path, output_path, resolved_stamps,
                                  mode=mode, add_timestamp=add_timestamp, log=log)
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
        ttk.Combobox(self.win, textvariable=self.position_label, state="readonly",
                     width=16, values=[l for _, l in POSITION_CHOICES]).grid(
            row=row, column=1, sticky="w")

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
        ttk.Label(
            self.win,
            text="（分次蓋章才需要設：例如組長先蓋存檔，主任拿到檔案後另外執行本程式，\n"
                 "　只設定主任自己的章，這裡填「1」讓主任的章自動往內讓開一格，\n"
                 "　不會跟組長已經蓋好、但這次看不到的章重疊。同一次批次一起蓋則留 0。）",
            foreground="#777", justify="left").grid(
            row=row, column=0, columnspan=3, sticky="w", padx=10)

        row += 1
        btn_frm = ttk.Frame(self.win)
        btn_frm.grid(row=row, column=0, columnspan=3, pady=12)
        ttk.Button(btn_frm, text="確定", command=self._save).pack(side="left", padx=6)
        ttk.Button(btn_frm, text="取消", command=self.win.destroy).pack(side="left", padx=6)

        self._refresh()

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
            "position": POSITION_LABEL_TO_CODE.get(
                self.position_label.get(), DEFAULT_POSITION),
        }
        self.on_save(entry)
        self.win.destroy()


class StampApp:
    def __init__(self, root):
        self.root = root
        root.title("批次自動蓋章工具")
        root.geometry("700x760")
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
            ts_frm, text="⑥ 每個章的正下方印上時間（格式：月/日 時:分，例如 09/10 14:35）",
            variable=self.add_timestamp).pack(side="left")

        # ⑦ 原始檔搬移
        ttk.Label(frm, text="⑦ 已核章的原始檔搬到（留空則不搬移）：").grid(
            row=9, column=0, sticky="w", padx=10, pady=(10, 0))
        ttk.Entry(frm, textvariable=self.processed_dir, width=58).grid(
            row=10, column=0, sticky="w", padx=10)
        ttk.Button(frm, text="選擇資料夾", command=self.choose_processed_dir).grid(
            row=10, column=1, padx=6)

        # ⑧ 自訂中文字型
        ttk.Label(frm, text="⑧ 自訂中文字型檔（用「文字自動產生」章時才需要，留空自動偵測）：").grid(
            row=11, column=0, sticky="w", padx=10, pady=(10, 0))
        ttk.Entry(frm, textvariable=self.custom_font_path, width=58).grid(
            row=12, column=0, sticky="w", padx=10)
        ttk.Button(frm, text="選擇字型檔", command=self.choose_font).grid(
            row=12, column=1, padx=6)

        note = ("說明：\n"
                "・PDF 只會蓋在「最後一頁」；圖片檔會蓋在整張圖片上。\n"
                "・如果有兩個章選了同一個位置，程式會自動把它們排成一排，不會疊在一起。\n"
                "・「固定位置」會直接貼齊邊緣；「智慧偵測」在單一章時會找附近最空白處，\n"
                "  多章共用同位置時會自動改用固定排列。\n"
                "・原始檔本身內容不會被修改，設定內容下次開啟會自動記住。")
        ttk.Label(frm, text=note, foreground="#555").grid(
            row=13, column=0, columnspan=2, sticky="w", padx=10, pady=(10, 0))

        self.start_btn = ttk.Button(frm, text="開始批次蓋章", command=self.start)
        self.start_btn.grid(row=14, column=0, columnspan=2, pady=10)

        self.progress = ttk.Progressbar(frm, length=640, mode="determinate")
        self.progress.grid(row=15, column=0, columnspan=2, padx=10)

        self.log_box = tk.Text(frm, height=8, width=82, state="disabled", bg="#f7f7f7")
        self.log_box.grid(row=16, column=0, columnspan=2, padx=10, pady=10)

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
            pos = POSITION_CODE_TO_LABEL.get(e.get("position"), "")
            off = e.get("offset_index", 0)
            off_txt = f"　讓開:{off}格" if off else ""
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

        self.start_btn.configure(state="disabled")
        self.log_box.configure(state="normal")
        self.log_box.delete("1.0", "end")
        self.log_box.configure(state="disabled")

        mode_code = MODE_LABEL_TO_CODE.get(self.mode_label.get(), DEFAULT_MODE)
        suffix = self._resolve_suffix()
        add_timestamp = self.add_timestamp.get()
        custom_font_path = self.custom_font_path.get().strip() or None
        stamp_entries = list(self.stamp_entries)

        save_settings({
            "input_dir": input_dir,
            "output_dir": output_dir,
            "processed_dir": processed_dir,
            "mode_label": self.mode_label.get(),
            "suffix_choice": self.suffix_choice.get(),
            "suffix_custom": self.suffix_custom.get(),
            "add_timestamp": add_timestamp,
            "custom_font_path": self.custom_font_path.get().strip(),
            "stamp_entries": stamp_entries,
        })

        def worker():
            try:
                batch_process(
                    input_dir, stamp_entries, output_dir,
                    mode=mode_code,
                    suffix=suffix,
                    add_timestamp=add_timestamp,
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
