# -*- coding: utf-8 -*-
"""
批次自動蓋章小工具
====================
功能：
  - 批次讀取一個資料夾內的 PDF / JPG / PNG 檔案
  - 自動把「主管章」蓋上去
      - 圖片檔 (jpg/png)：蓋在整張圖片上
      - PDF：只蓋在「最後一頁」
  - 「智慧空白偵測」：在右下角一塊範圍內，自動尋找最空白（最少文字/線條）的
    位置來放章，避免蓋到文字、簽名或表格線上。若範圍內找不到夠空白的地方，
    會退回到固定的右下角位置，確保一定蓋得上去。
  - 自動把章圖片的白色背景去除，只保留印章本體，蓋上去不會有白色方塊。

使用方式：
  1. 安裝套件（第一次使用才需要）：
         pip install -r requirements.txt
  2. 執行：
         python stamp_tool.py
  3. 在視窗中選擇：
         - 待蓋章的資料夾（同仁交來的 PDF/JPG/PNG 放這裡）
         - 主管章的圖片（建議用去背 PNG，也支援一般 JPG 白底章）
         - 輸出資料夾（蓋好章的檔案會存在這裡，不會覆蓋原始檔）
     按下「開始批次蓋章」即可。

作者：為內部行政作業自動化而寫
"""

import os
import sys
import threading
import traceback
from datetime import datetime

import numpy as np
from PIL import Image

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


SUPPORTED_IMG_EXT = {".jpg", ".jpeg", ".png"}
SUPPORTED_PDF_EXT = {".pdf"}

# 檔名後綴的常用選項（GUI 下拉選單），選「自訂」時會另外顯示一個輸入框
SUFFIX_PRESETS = ["組長核章", "主任核章", "自訂"]

# 設定檔：跟執行檔（或程式）放在同一個資料夾，記住上次用過的選項
if getattr(sys, "frozen", False):
    _BASE_DIR = os.path.dirname(sys.executable)
else:
    _BASE_DIR = os.path.dirname(os.path.abspath(__file__))
CONFIG_PATH = os.path.join(_BASE_DIR, "stamp_tool_settings.json")


def load_settings():
    """讀取上次儲存的設定，讀不到或格式錯誤就回傳空字典（用預設值）"""
    try:
        import json
        with open(CONFIG_PATH, "r", encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        return {}


def save_settings(data):
    """把目前的設定存成 JSON，方便下次開啟時自動帶入"""
    try:
        import json
        with open(CONFIG_PATH, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False, indent=2)
    except Exception:
        pass  # 存檔失敗也不影響蓋章功能，安靜略過即可


# ----------------------------------------------------------------------
# 章圖片處理：把白色背景去除，變成透明背景的印章
# ----------------------------------------------------------------------
def load_stamp_rgba(stamp_path, white_thresh=225, feather=35):
    """
    讀取章的圖片，回傳去除白底後的 RGBA 影像 (PIL Image)。
    white_thresh: 判斷為「白色」的門檻，越接近 255 越嚴格。
    feather:      邊緣柔化的寬度，避免印章邊緣出現鋸齒白邊。
    """
    img = Image.open(stamp_path).convert("RGBA")
    arr = np.array(img).astype(np.float32)
    rgb = arr[:, :, :3]
    # whiteness：三個色版中最小值越大代表越接近白色
    whiteness = rgb.min(axis=2)

    alpha = np.ones(whiteness.shape, dtype=np.float32) * 255.0
    # 完全視為白色 -> 全透明
    alpha[whiteness >= white_thresh] = 0.0
    # 介於 (white_thresh - feather) ~ white_thresh 之間 -> 線性漸層，柔化邊緣
    low = white_thresh - feather
    mask_mid = (whiteness > low) & (whiteness < white_thresh)
    alpha[mask_mid] = (white_thresh - whiteness[mask_mid]) / feather * 255.0

    # 如果圖片本身已經有透明通道，取兩者最小值（保留原本的去背效果）
    if img.mode == "RGBA":
        orig_alpha = arr[:, :, 3]
        alpha = np.minimum(alpha, orig_alpha)

    arr[:, :, 3] = np.clip(alpha, 0, 255)
    return Image.fromarray(arr.astype(np.uint8), mode="RGBA")


# ----------------------------------------------------------------------
# 智慧空白偵測：在指定搜尋範圍內，找出最「空白」的位置來放章
# ----------------------------------------------------------------------
def find_blank_position(gray_arr, region_box, stamp_w, stamp_h,
                         step=12, min_score=0.80):
    """
    gray_arr:   整張頁面/圖片的灰階 numpy 陣列 (H, W)，數值 0~255
    region_box: (x0, y0, x1, y1) 搜尋範圍（像素座標）
    stamp_w/h:  印章要貼上去的寬高（像素）
    step:       滑動視窗的步進（像素），越小越精準但越慢
    min_score:  可接受的最低「空白分數」(0~1)，低於此值視為找不到理想位置

    回傳: (best_x, best_y, best_score)  -> 印章左上角座標 + 該位置的空白分數
    """
    H, W = gray_arr.shape
    x0, y0, x1, y1 = region_box
    x0, y0 = max(0, x0), max(0, y0)
    x1, y1 = min(W, x1), min(H, y1)

    # 若搜尋範圍比印章還小，直接夾到邊界內
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
                # 空白分數 = 接近白色(>235)的像素比例
                score = float(np.mean(window > 235))
                if score > best_score:
                    best_score = score
                    best_pos = (x, y)
            x += step
        y += step

    return best_pos[0], best_pos[1], max(best_score, 0.0)


# 支援的蓋章位置代碼，及對應的中文顯示名稱（GUI 下拉選單會用到）
POSITION_CHOICES = [
    ("bottom_right", "右下角（預設）"),
    ("bottom_center", "中央下方"),
    ("bottom_left", "左下角"),
    ("top_left", "左上角"),
    ("top_center", "中央上方"),
    ("top_right", "右上角"),
]
POSITION_LABEL_TO_CODE = {label: code for code, label in POSITION_CHOICES}
DEFAULT_POSITION = "bottom_right"


def get_search_region(width, height, position=DEFAULT_POSITION,
                       region_ratio_w=0.35, region_ratio_h=0.28,
                       margin_ratio=0.02):
    """
    依照指定的位置代碼，回傳搜尋範圍 (x0, y0, x1, y1)，並留一點邊界避免蓋到
    紙張邊緣。position 可為：
        bottom_right / bottom_center / bottom_left /
        top_right    / top_center    / top_left
    """
    margin_x = int(width * margin_ratio)
    margin_y = int(height * margin_ratio)
    region_w = int(width * region_ratio_w)
    region_h = int(height * region_ratio_h)
    cx = width // 2

    if position not in {c for c, _ in POSITION_CHOICES}:
        position = DEFAULT_POSITION

    # 先決定垂直方向 (上/下)
    if position.startswith("bottom"):
        y1 = height - margin_y
        y0 = max(0, y1 - region_h)
    else:  # top_*
        y0 = margin_y
        y1 = min(height, y0 + region_h)

    # 再決定水平方向 (左/中/右)
    if position.endswith("right"):
        x1 = width - margin_x
        x0 = max(0, x1 - region_w)
    elif position.endswith("left"):
        x0 = margin_x
        x1 = min(width, x0 + region_w)
    else:  # *_center
        x0 = max(0, cx - region_w // 2)
        x1 = min(width, cx + region_w // 2)

    return x0, y0, x1, y1


def get_fixed_position(width, height, stamp_w, stamp_h,
                        position=DEFAULT_POSITION, margin_ratio=0.03):
    """
    不做任何空白偵測，直接依照位置代碼算出印章左上角座標（貼齊邊緣 + 一點邊界）。
    """
    margin_x = int(width * margin_ratio)
    margin_y = int(height * margin_ratio)
    cx = width // 2

    if position not in {c for c, _ in POSITION_CHOICES}:
        position = DEFAULT_POSITION

    if position.startswith("bottom"):
        y = height - margin_y - stamp_h
    else:  # top_*
        y = margin_y

    if position.endswith("right"):
        x = width - margin_x - stamp_w
    elif position.endswith("left"):
        x = margin_x
    else:  # *_center
        x = cx - stamp_w // 2

    x = max(0, min(x, width - stamp_w))
    y = max(0, min(y, height - stamp_h))
    return x, y


# 蓋章模式：fixed = 直接貼在固定位置（不偵測，速度快、行為可預期）
#           smart = 在該位置附近的範圍內自動找最空白處（可能誤判表格/文字）
MODE_CHOICES = [
    ("fixed", "固定位置（直接貼齊邊緣，不偵測內容）"),
    ("smart", "智慧偵測（自動找附近最空白處，但可能誤判）"),
]
MODE_LABEL_TO_CODE = {label: code for code, label in MODE_CHOICES}
DEFAULT_MODE = "fixed"


# ----------------------------------------------------------------------
# 處理圖片檔 (jpg / png)
# ----------------------------------------------------------------------
def stamp_image_file(input_path, output_path, stamp_rgba,
                      stamp_width_ratio=0.14, position=DEFAULT_POSITION,
                      mode=DEFAULT_MODE, log=print):
    img = Image.open(input_path).convert("RGB")
    W, H = img.size

    stamp_w = max(20, int(W * stamp_width_ratio))
    ratio = stamp_w / stamp_rgba.width
    stamp_h = max(20, int(stamp_rgba.height * ratio))
    resized_stamp = stamp_rgba.resize((stamp_w, stamp_h), Image.LANCZOS)

    if mode == "smart":
        gray = np.array(img.convert("L"))
        region = get_search_region(W, H, position=position)
        x, y, score = find_blank_position(gray, region, stamp_w, stamp_h)
        log(f"    空白分數: {score:.2f}（越接近 1 代表該處越空白）")
    else:
        x, y = get_fixed_position(W, H, stamp_w, stamp_h, position=position)

    img.paste(resized_stamp, (x, y), resized_stamp)

    ext = os.path.splitext(output_path)[1].lower()
    if ext in (".jpg", ".jpeg"):
        img.save(output_path, quality=95)
    else:
        img.save(output_path)

    return True


# ----------------------------------------------------------------------
# 處理 PDF 檔（只蓋最後一頁）
# ----------------------------------------------------------------------
def stamp_pdf_file(input_path, output_path, stamp_rgba,
                    stamp_width_ratio=0.14, position=DEFAULT_POSITION,
                    mode=DEFAULT_MODE, render_zoom=1.5, log=print):
    if fitz is None:
        raise RuntimeError("尚未安裝 PyMuPDF，請先執行: pip install PyMuPDF")

    doc = fitz.open(input_path)
    if doc.page_count == 0:
        raise RuntimeError("PDF 沒有任何頁面")

    page = doc[-1]  # 最後一頁
    page_rect = page.rect  # 單位: point (1/72 英吋)

    if mode == "smart":
        # 智慧模式：把最後一頁渲染成圖片來分析空白區域
        mat = fitz.Matrix(render_zoom, render_zoom)
        pix = page.get_pixmap(matrix=mat, colorspace=fitz.csGRAY)
        gray = np.frombuffer(pix.samples, dtype=np.uint8).reshape(pix.height, pix.width)

        stamp_w_px = max(20, int(pix.width * stamp_width_ratio))
        ratio = stamp_w_px / stamp_rgba.width
        stamp_h_px = max(20, int(stamp_rgba.height * ratio))

        region = get_search_region(pix.width, pix.height, position=position)
        x_px, y_px, score = find_blank_position(gray, region, stamp_w_px, stamp_h_px)

        scale = 1.0 / render_zoom
        x_pt = x_px * scale
        y_pt = y_px * scale
        w_pt = stamp_w_px * scale
        h_pt = stamp_h_px * scale
        log(f"    最後一頁空白分數: {score:.2f}（越接近 1 代表該處越空白）")
    else:
        # 固定模式：直接依照頁面尺寸(point)算出貼齊邊緣的座標，不做渲染分析
        w_pt = page_rect.width * stamp_width_ratio
        ratio = w_pt / stamp_rgba.width
        h_pt = stamp_rgba.height * ratio
        x_pt, y_pt = get_fixed_position(
            page_rect.width, page_rect.height, w_pt, h_pt, position=position)

    rect = fitz.Rect(x_pt, y_pt, x_pt + w_pt, y_pt + h_pt)

    # 把 RGBA 印章存成暫存 PNG 供 insert_image 使用
    tmp_stamp_path = output_path + "._stamp_tmp.png"
    stamp_rgba.save(tmp_stamp_path)
    try:
        page.insert_image(rect, filename=tmp_stamp_path, overlay=True)
        doc.save(output_path, garbage=4, deflate=True)
    finally:
        doc.close()
        if os.path.exists(tmp_stamp_path):
            os.remove(tmp_stamp_path)

    return True


# ----------------------------------------------------------------------
# 批次處理主邏輯
# ----------------------------------------------------------------------
def batch_process(input_dir, stamp_path, output_dir,
                   stamp_width_ratio=0.14, position=DEFAULT_POSITION,
                   mode=DEFAULT_MODE, suffix="已蓋章",
                   log=print, progress_cb=None):
    stamp_rgba = load_stamp_rgba(stamp_path)
    os.makedirs(output_dir, exist_ok=True)

    stamp_abs = os.path.abspath(stamp_path)
    files = sorted(
        f for f in os.listdir(input_dir)
        if os.path.splitext(f)[1].lower() in (SUPPORTED_IMG_EXT | SUPPORTED_PDF_EXT)
        and os.path.abspath(os.path.join(input_dir, f)) != stamp_abs
    )

    total = len(files)
    if total == 0:
        log("找不到任何 PDF / JPG / PNG 檔案。")
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
                stamp_pdf_file(input_path, output_path, stamp_rgba,
                                stamp_width_ratio, position=position,
                                mode=mode, log=log)
            else:
                stamp_image_file(input_path, output_path, stamp_rgba,
                                  stamp_width_ratio, position=position,
                                  mode=mode, log=log)
            log(f"    ✔ 完成 -> {out_name}")
            ok_count += 1
        except Exception as e:
            log(f"    ✘ 失敗: {e}")
            fail_count += 1

        if progress_cb:
            progress_cb(i, total)

    log("-" * 40)
    log(f"完成！成功 {ok_count} 個，失敗 {fail_count} 個。")
    return ok_count, fail_count


# ----------------------------------------------------------------------
# GUI
# ----------------------------------------------------------------------
class StampApp:
    def __init__(self, root):
        self.root = root
        root.title("批次自動蓋章工具")
        root.geometry("640x640")
        root.resizable(False, False)

        pad = {"padx": 10, "pady": 6}

        settings = load_settings()

        self.input_dir = tk.StringVar(value=settings.get("input_dir", ""))
        self.stamp_path = tk.StringVar(value=settings.get("stamp_path", ""))
        self.output_dir = tk.StringVar(value=settings.get("output_dir", ""))
        self.stamp_width_pct = tk.IntVar(value=settings.get("stamp_width_pct", 14))
        self.position_label = tk.StringVar(
            value=settings.get("position_label", POSITION_CHOICES[0][1]))
        self.mode_label = tk.StringVar(
            value=settings.get("mode_label", MODE_CHOICES[0][1]))
        self.suffix_choice = tk.StringVar(
            value=settings.get("suffix_choice", SUFFIX_PRESETS[0]))
        self.suffix_custom = tk.StringVar(
            value=settings.get("suffix_custom", "已蓋章"))

        frm = ttk.Frame(root)
        frm.pack(fill="both", expand=True)

        # 輸入資料夾
        ttk.Label(frm, text="① 待蓋章資料夾（同仁交來的 PDF/JPG/PNG）：").grid(
            row=0, column=0, sticky="w", **pad)
        ttk.Entry(frm, textvariable=self.input_dir, width=55).grid(
            row=1, column=0, sticky="w", padx=10)
        ttk.Button(frm, text="選擇資料夾", command=self.choose_input_dir).grid(
            row=1, column=1, padx=6)

        # 章圖片
        ttk.Label(frm, text="② 主管章圖片（建議用去背 PNG，一般 JPG 白底章也可以）：").grid(
            row=2, column=0, sticky="w", **pad)
        ttk.Entry(frm, textvariable=self.stamp_path, width=55).grid(
            row=3, column=0, sticky="w", padx=10)
        ttk.Button(frm, text="選擇圖片", command=self.choose_stamp).grid(
            row=3, column=1, padx=6)

        # 輸出資料夾
        ttk.Label(frm, text="③ 輸出資料夾（蓋好章的檔案存放處，不會覆蓋原始檔）：").grid(
            row=4, column=0, sticky="w", **pad)
        ttk.Entry(frm, textvariable=self.output_dir, width=55).grid(
            row=5, column=0, sticky="w", padx=10)
        ttk.Button(frm, text="選擇資料夾", command=self.choose_output_dir).grid(
            row=5, column=1, padx=6)

        # 章大小設定
        size_frm = ttk.Frame(frm)
        size_frm.grid(row=6, column=0, columnspan=2, sticky="w", padx=10, pady=(10, 0))
        ttk.Label(size_frm, text="④ 章的大小（佔文件寬度的百分比，預設 14%）：").pack(side="left")
        ttk.Spinbox(size_frm, from_=5, to=40, textvariable=self.stamp_width_pct,
                    width=5).pack(side="left", padx=6)

        # 蓋章位置設定
        pos_frm = ttk.Frame(frm)
        pos_frm.grid(row=7, column=0, columnspan=2, sticky="w", padx=10, pady=(6, 0))
        ttk.Label(pos_frm, text="⑤ 蓋章位置（預設右下角，可自行更改）：").pack(side="left")
        pos_combo = ttk.Combobox(
            pos_frm, textvariable=self.position_label, state="readonly",
            width=14, values=[label for _, label in POSITION_CHOICES])
        pos_combo.pack(side="left", padx=6)

        # 蓋章模式設定
        mode_frm = ttk.Frame(frm)
        mode_frm.grid(row=8, column=0, columnspan=2, sticky="w", padx=10, pady=(6, 0))
        ttk.Label(mode_frm, text="⑥ 蓋章方式：").pack(side="left")
        mode_combo = ttk.Combobox(
            mode_frm, textvariable=self.mode_label, state="readonly",
            width=34, values=[label for _, label in MODE_CHOICES])
        mode_combo.pack(side="left", padx=6)

        # 檔名後綴設定
        suffix_frm = ttk.Frame(frm)
        suffix_frm.grid(row=9, column=0, columnspan=2, sticky="w", padx=10, pady=(6, 0))
        ttk.Label(suffix_frm, text="⑦ 檔名後綴（例：文件_組長核章.pdf）：").pack(side="left")
        suffix_combo = ttk.Combobox(
            suffix_frm, textvariable=self.suffix_choice, state="readonly",
            width=10, values=SUFFIX_PRESETS)
        suffix_combo.pack(side="left", padx=6)
        self.suffix_entry = ttk.Entry(
            suffix_frm, textvariable=self.suffix_custom, width=14)
        self.suffix_entry.pack(side="left", padx=(4, 0))
        suffix_combo.bind("<<ComboboxSelected>>", lambda e: self._update_suffix_entry_state())
        self._update_suffix_entry_state()

        # 說明文字
        note = ("說明：\n"
                "・PDF 只會蓋在「最後一頁」；圖片檔會蓋在整張圖片上。\n"
                "・「固定位置」會直接貼齊你選的位置邊緣；「智慧偵測」則會在附近找最空白處，\n"
                "  但版面複雜（如表格）時可能誤判，效果不理想可改回固定位置。\n"
                "・原始檔案不會被修改，設定內容下次開啟會自動記住。")
        ttk.Label(frm, text=note, foreground="#555").grid(
            row=10, column=0, columnspan=2, sticky="w", padx=10, pady=(10, 0))

        # 開始按鈕
        self.start_btn = ttk.Button(frm, text="開始批次蓋章", command=self.start)
        self.start_btn.grid(row=11, column=0, columnspan=2, pady=12)

        # 進度條
        self.progress = ttk.Progressbar(frm, length=600, mode="determinate")
        self.progress.grid(row=12, column=0, columnspan=2, padx=10)

        # 紀錄視窗
        self.log_box = tk.Text(frm, height=10, width=76, state="disabled",
                                bg="#f7f7f7")
        self.log_box.grid(row=13, column=0, columnspan=2, padx=10, pady=10)

        if fitz is None:
            self.log("⚠ 尚未安裝 PyMuPDF，PDF 功能無法使用。"
                      "請先在命令列執行: pip install PyMuPDF")

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

    def choose_stamp(self):
        f = filedialog.askopenfilename(
            title="選擇主管章圖片",
            filetypes=[("圖片檔", "*.jpg *.jpeg *.png"), ("所有檔案", "*.*")])
        if f:
            self.stamp_path.set(f)

    def choose_output_dir(self):
        d = filedialog.askdirectory(title="選擇輸出資料夾")
        if d:
            self.output_dir.set(d)

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
        stamp_path = self.stamp_path.get().strip()
        output_dir = self.output_dir.get().strip()

        if not input_dir or not os.path.isdir(input_dir):
            messagebox.showerror("錯誤", "請選擇有效的待蓋章資料夾")
            return
        if not stamp_path or not os.path.isfile(stamp_path):
            messagebox.showerror("錯誤", "請選擇有效的主管章圖片")
            return
        if not output_dir:
            messagebox.showerror("錯誤", "請選擇輸出資料夾")
            return
        if os.path.abspath(input_dir) == os.path.abspath(output_dir):
            messagebox.showerror("錯誤", "輸出資料夾請不要跟待蓋章資料夾相同，避免混淆原始檔")
            return

        self.start_btn.configure(state="disabled")
        self.log_box.configure(state="normal")
        self.log_box.delete("1.0", "end")
        self.log_box.configure(state="disabled")

        width_ratio = self.stamp_width_pct.get() / 100.0
        position_code = POSITION_LABEL_TO_CODE.get(
            self.position_label.get(), DEFAULT_POSITION)
        mode_code = MODE_LABEL_TO_CODE.get(self.mode_label.get(), DEFAULT_MODE)
        suffix = self._resolve_suffix()

        # 記住這次的設定，下次開啟自動帶入
        save_settings({
            "input_dir": input_dir,
            "stamp_path": stamp_path,
            "output_dir": output_dir,
            "stamp_width_pct": self.stamp_width_pct.get(),
            "position_label": self.position_label.get(),
            "mode_label": self.mode_label.get(),
            "suffix_choice": self.suffix_choice.get(),
            "suffix_custom": self.suffix_custom.get(),
        })

        def worker():
            try:
                batch_process(
                    input_dir, stamp_path, output_dir,
                    stamp_width_ratio=width_ratio,
                    position=position_code,
                    mode=mode_code,
                    suffix=suffix,
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
