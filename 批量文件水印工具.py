# -*- coding: utf-8 -*-
"""
批量文件水印工具 · V3

功能：
- 递归扫描输入文件夹内的图片和 MP4 视频
- 文字水印 / 图片水印
- 图片与视频分别设置水印大小
- 文字水印透明度、描边、阴影
- 图片水印透明度
- 单个水印 / 满屏平铺水印
- 45° 旋转水印
- 保留原文件名、目录层级；不修改源文件
- 支持中文路径、空格及 Windows 路径

依赖：
    pip install Pillow imageio-ffmpeg

说明：
- 视频使用 FFmpeg 处理。程序通过 FFmpeg 提取视频实际显示方向下的首帧，
  按该帧的精确宽高生成同尺寸 PNG 水印画布，再以 1:1 叠加，避免水印被拉伸。
"""

from __future__ import annotations

import os
import queue
import re
import shutil
import subprocess
import tempfile
import threading
import traceback
from dataclasses import dataclass
from pathlib import Path
from typing import Optional

import tkinter as tk
import tkinter.font as tkfont
from tkinter import colorchooser, filedialog, messagebox, ttk
from tkinter.scrolledtext import ScrolledText

from PIL import Image, ImageDraw, ImageFilter, ImageFont, ImageOps


APP_TITLE = "批量文件水印工具 V3"

# ---------------------------------------------------------------------------
# 窗口与界面外观：需要调整窗口大小或全局字体时，优先修改这里
# ---------------------------------------------------------------------------
WINDOW_GEOMETRY = "1240x1040"       # 初始窗口宽 x 高（像素）
WINDOW_MIN_WIDTH = 820              # 窗口最小宽度；较窄时第三、第五部分会自动换行
WINDOW_MIN_HEIGHT = 780             # 窗口最小高度
UI_FONT_SCALE = 0.8                 # 相对 V2 字体缩小 20%
UI_BASE_FONT_SIZE = round(18 * UI_FONT_SCALE)  # 普通控件字体：约 14 px
UI_TITLE_FONT_SIZE = round(31 * UI_FONT_SCALE) # 页面标题：约 25 px
UI_LOG_FONT_SIZE = round(18 * UI_FONT_SCALE)   # 日志字体：约 14 px

# 描边按 1080p 画面作为统一参考尺度。
# 同一素材以不同分辨率显示时，描边随画面像素面积开方缩放，视觉粗细更接近。
STROKE_REFERENCE_WIDTH = 1920
STROKE_REFERENCE_HEIGHT = 1080
IMAGE_EXTENSIONS = {".png", ".jpg", ".jpeg", ".webp", ".bmp", ".tif", ".tiff"}
VIDEO_EXTENSIONS = {".mp4"}
SUPPORTED_EXTENSIONS = IMAGE_EXTENSIONS | VIDEO_EXTENSIONS

POSITION_LABELS = {
    "左上": "top_left",
    "顶部居中": "top_center",
    "右上": "top_right",
    "左侧居中": "middle_left",
    "正中央": "center",
    "右侧居中": "middle_right",
    "左下": "bottom_left",
    "底部居中": "bottom_center",
    "右下": "bottom_right",
}


@dataclass
class WatermarkSettings:
    mode: str
    text: str = ""
    watermark_image: str = ""
    font_path: str = ""

    text_color: str = "#FFFFFF"
    text_opacity: int = 80
    image_opacity: int = 80

    # 图片和视频分别设置水印宽度百分比
    image_size_percent: int = 20
    video_size_percent: int = 20

    position: str = "bottom_right"
    margin_percent: float = 2.0

    stroke_enabled: bool = False
    stroke_width: int = 3
    stroke_color: str = "#000000"

    shadow_enabled: bool = False
    shadow_color: str = "#000000"
    shadow_offset_x: int = 4
    shadow_offset_y: int = 4
    shadow_blur: int = 3

    tile_enabled: bool = False
    tile_gap_percent: int = 100
    rotate_45: bool = False


# ---------------------------------------------------------------------------
# 路径与字体
# ---------------------------------------------------------------------------


def path_is_inside(child: Path, parent: Path) -> bool:
    try:
        child.resolve().relative_to(parent.resolve())
        return True
    except (ValueError, OSError):
        return False


def find_default_font() -> str:
    candidates: list[Path] = []
    if os.name == "nt":
        windir = Path(os.environ.get("WINDIR", r"C:\Windows"))
        candidates.extend([
            windir / "Fonts" / "msyh.ttc",       # 微软雅黑
            windir / "Fonts" / "msyh.ttf",
            windir / "Fonts" / "simhei.ttf",     # 黑体
            windir / "Fonts" / "simsun.ttc",     # 宋体
            windir / "Fonts" / "Deng.ttf",       # 等线
            windir / "Fonts" / "arial.ttf",
        ])
    elif os.sys.platform == "darwin":
        candidates.extend([
            Path("/System/Library/Fonts/PingFang.ttc"),
            Path("/System/Library/Fonts/STHeiti Medium.ttc"),
            Path("/System/Library/Fonts/Supplemental/Arial Unicode.ttf"),
        ])
    else:
        candidates.extend([
            Path("/usr/share/fonts/opentype/noto/NotoSansCJK-Regular.ttc"),
            Path("/usr/share/fonts/truetype/noto/NotoSansCJK-Regular.ttc"),
            Path("/usr/share/fonts/truetype/wqy/wqy-microhei.ttc"),
            Path("/usr/share/fonts/truetype/arphic/uming.ttc"),
            Path("/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf"),
        ])

    for candidate in candidates:
        if candidate.is_file():
            return str(candidate)
    return ""


def load_font(font_path: str, size: int) -> ImageFont.FreeTypeFont | ImageFont.ImageFont:
    if font_path:
        font_file = Path(font_path)
        if not font_file.is_file():
            raise RuntimeError(f"找不到字体文件：{font_path}")
        try:
            return ImageFont.truetype(str(font_file), size=max(1, int(size)))
        except Exception as exc:
            raise RuntimeError(f"无法读取所选字体：{font_path}\n{exc}") from exc

    detected = find_default_font()
    if detected:
        try:
            return ImageFont.truetype(detected, size=max(1, int(size)))
        except Exception:
            pass
    return ImageFont.load_default()


def parse_hex_color(value: str) -> tuple[int, int, int]:
    value = value.strip().lstrip("#")
    if len(value) != 6:
        raise ValueError("颜色格式不正确，请使用 #FFFFFF 这样的六位十六进制颜色。")
    try:
        return tuple(int(value[i:i + 2], 16) for i in (0, 2, 4))  # type: ignore[return-value]
    except ValueError as exc:
        raise ValueError("颜色格式不正确，请使用 #FFFFFF 这样的六位十六进制颜色。") from exc


# ---------------------------------------------------------------------------
# 水印图层生成
# ---------------------------------------------------------------------------


def _measure_text(text: str, font: ImageFont.ImageFont) -> tuple[int, int]:
    probe = Image.new("RGBA", (8, 8), (0, 0, 0, 0))
    bbox = ImageDraw.Draw(probe).textbbox((0, 0), text, font=font)
    return max(1, bbox[2] - bbox[0]), max(1, bbox[3] - bbox[1])


def create_text_stamp(
    settings: WatermarkSettings,
    target_width: int,
    effect_scale: float = 1.0,
) -> Image.Image:
    """
    按目标最终像素宽度生成文字图层。

    effect_scale 以 1080p 为 1.0，对描边和阴影参数按画面像素面积开方缩放，
    让不同分辨率的图片/视频在常见等比例预览尺寸下保持近似的视觉粗细。
    """
    text = settings.text.strip()
    if not text:
        raise ValueError("请先输入文字水印内容。")

    target_width = max(1, int(target_width))
    reference_font_size = 240
    reference_font = load_font(settings.font_path, reference_font_size)
    try:
        ref_width, _ = _measure_text(text, reference_font)
    except (UnicodeEncodeError, OSError) as exc:
        raise RuntimeError(
            "当前字体无法正常显示这段文字。请在‘字体文件’处选择支持中文的 .ttf、.ttc 或 .otf 字体。\n"
            "Windows 通常可以选择 C:\\Windows\\Fonts\\msyh.ttc（微软雅黑）。"
        ) from exc

    scale_factor = target_width / max(1, ref_width)
    actual_font_size = max(1, round(reference_font_size * scale_factor))
    font = load_font(settings.font_path, actual_font_size)

    # 以 1920x1080 为基准分辨率。比如 4K（像素面积为 4 倍）描边宽度乘 2；
    # 720p 则约乘 0.67。这样不同分辨率媒体缩放到同一预览尺寸时，视觉描边更一致。
    stroke_width = (
        max(1, round(int(settings.stroke_width) * max(0.1, effect_scale)))
        if settings.stroke_enabled else 0
    )
    alpha = max(0, min(255, round(settings.text_opacity * 255 / 100)))
    text_rgb = parse_hex_color(settings.text_color)
    stroke_rgb = parse_hex_color(settings.stroke_color)
    shadow_rgb = parse_hex_color(settings.shadow_color)

    probe = Image.new("RGBA", (8, 8), (0, 0, 0, 0))
    draw_probe = ImageDraw.Draw(probe)
    bbox = draw_probe.textbbox((0, 0), text, font=font, stroke_width=stroke_width)

    shadow_blur = max(0, round(int(settings.shadow_blur) * effect_scale)) if settings.shadow_enabled else 0
    offset_x = round(int(settings.shadow_offset_x) * effect_scale) if settings.shadow_enabled else 0
    offset_y = round(int(settings.shadow_offset_y) * effect_scale) if settings.shadow_enabled else 0
    shadow_padding = shadow_blur * 3 + max(abs(offset_x), abs(offset_y)) if settings.shadow_enabled else 0
    padding = max(8, stroke_width + 5, shadow_padding + 5)

    text_width = max(1, bbox[2] - bbox[0])
    text_height = max(1, bbox[3] - bbox[1])
    layer = Image.new(
        "RGBA",
        (text_width + padding * 2, text_height + padding * 2),
        (0, 0, 0, 0),
    )
    text_xy = (padding - bbox[0], padding - bbox[1])

    if settings.shadow_enabled and alpha > 0:
        shadow_layer = Image.new("RGBA", layer.size, (0, 0, 0, 0))
        shadow_draw = ImageDraw.Draw(shadow_layer)
        shadow_draw.text(
            (text_xy[0] + offset_x, text_xy[1] + offset_y),
            text,
            font=font,
            fill=(*shadow_rgb, alpha),
        )
        if shadow_blur > 0:
            shadow_layer = shadow_layer.filter(ImageFilter.GaussianBlur(radius=shadow_blur))
        layer.alpha_composite(shadow_layer)

    draw = ImageDraw.Draw(layer)
    draw.text(
        text_xy,
        text,
        font=font,
        fill=(*text_rgb, alpha),
        stroke_width=stroke_width,
        stroke_fill=(*stroke_rgb, alpha) if stroke_width > 0 else None,
    )
    return layer


def create_image_stamp(settings: WatermarkSettings, target_width: int) -> Image.Image:
    path = Path(settings.watermark_image)
    if not path.is_file():
        raise ValueError("请选择有效的图片水印文件。")
    try:
        with Image.open(path) as source:
            stamp = ImageOps.exif_transpose(source).convert("RGBA")
    except Exception as exc:
        raise RuntimeError(f"无法打开水印图片：{path}\n{exc}") from exc

    target_width = max(1, int(target_width))
    target_height = max(1, round(stamp.height * target_width / max(1, stamp.width)))
    stamp = stamp.resize((target_width, target_height), Image.Resampling.LANCZOS)
    alpha_factor = max(0, min(255, round(settings.image_opacity * 255 / 100)))
    alpha = stamp.getchannel("A").point(lambda value: round(value * alpha_factor / 255))
    stamp.putalpha(alpha)
    return stamp


def create_watermark_stamp(
    settings: WatermarkSettings,
    canvas_width: int,
    canvas_height: int,
    media_kind: str,
) -> Image.Image:
    if canvas_width <= 0 or canvas_height <= 0:
        raise ValueError("画面尺寸无效。")
    size_percent = settings.video_size_percent if media_kind == "video" else settings.image_size_percent
    target_width = max(1, round(canvas_width * size_percent / 100))

    # 采用画面像素总量的平方根作为缩放比例，不依赖横屏/竖屏方向。
    # 1080p 为 1.0；4K 为 2.0；720p 约为 0.67。
    reference_pixels = STROKE_REFERENCE_WIDTH * STROKE_REFERENCE_HEIGHT
    effect_scale = (canvas_width * canvas_height / reference_pixels) ** 0.5

    if settings.mode == "text":
        stamp = create_text_stamp(settings, target_width, effect_scale=effect_scale)
    else:
        stamp = create_image_stamp(settings, target_width)

    if settings.rotate_45:
        # expand=True 保留旋转后超出原边界的部分，避免水印被裁切。
        stamp = stamp.rotate(45, resample=Image.Resampling.BICUBIC, expand=True)
    return stamp


def calculate_position(
    canvas_width: int,
    canvas_height: int,
    watermark_width: int,
    watermark_height: int,
    position: str,
    margin_x: int,
    margin_y: int,
) -> tuple[int, int]:
    positions = {
        "top_left": (margin_x, margin_y),
        "top_center": ((canvas_width - watermark_width) // 2, margin_y),
        "top_right": (canvas_width - watermark_width - margin_x, margin_y),
        "middle_left": (margin_x, (canvas_height - watermark_height) // 2),
        "center": ((canvas_width - watermark_width) // 2, (canvas_height - watermark_height) // 2),
        "middle_right": (canvas_width - watermark_width - margin_x, (canvas_height - watermark_height) // 2),
        "bottom_left": (margin_x, canvas_height - watermark_height - margin_y),
        "bottom_center": ((canvas_width - watermark_width) // 2, canvas_height - watermark_height - margin_y),
        "bottom_right": (canvas_width - watermark_width - margin_x, canvas_height - watermark_height - margin_y),
    }
    x, y = positions.get(position, positions["bottom_right"])
    x = max(0, min(x, max(0, canvas_width - watermark_width)))
    y = max(0, min(y, max(0, canvas_height - watermark_height)))
    return x, y


def create_overlay_canvas(
    settings: WatermarkSettings,
    canvas_width: int,
    canvas_height: int,
    media_kind: str,
) -> Image.Image:
    """生成与目标媒体同宽高的透明水印画布，图片和视频使用完全相同的排版逻辑。"""
    stamp = create_watermark_stamp(settings, canvas_width, canvas_height, media_kind)
    overlay = Image.new("RGBA", (canvas_width, canvas_height), (0, 0, 0, 0))

    if settings.tile_enabled:
        gap_ratio = max(0, settings.tile_gap_percent) / 100.0
        step_x = max(1, stamp.width + round(stamp.width * gap_ratio))
        step_y = max(1, stamp.height + round(stamp.height * gap_ratio))
        # 从负坐标开始铺设，确保画面边缘也有水印。
        row_index = 0
        y = -stamp.height
        max_stamps = 12000
        count = 0
        while y < canvas_height + stamp.height and count < max_stamps:
            offset_x = step_x // 2 if row_index % 2 else 0
            x = -stamp.width + offset_x
            while x < canvas_width + stamp.width and count < max_stamps:
                overlay.alpha_composite(stamp, (x, y))
                x += step_x
                count += 1
            y += step_y
            row_index += 1
        if count >= max_stamps:
            raise ValueError("平铺水印数量过多。请增大水印间距或减小水印尺寸。")
    else:
        margin_x = round(canvas_width * settings.margin_percent / 100)
        margin_y = round(canvas_height * settings.margin_percent / 100)
        x, y = calculate_position(
            canvas_width,
            canvas_height,
            stamp.width,
            stamp.height,
            settings.position,
            margin_x,
            margin_y,
        )
        overlay.alpha_composite(stamp, (x, y))

    return overlay


# ---------------------------------------------------------------------------
# 图片处理
# ---------------------------------------------------------------------------


def apply_watermark_to_image(input_path: Path, output_path: Path, settings: WatermarkSettings) -> None:
    with Image.open(input_path) as opened:
        if getattr(opened, "is_animated", False) and getattr(opened, "n_frames", 1) > 1:
            raise RuntimeError("检测到动态图片（多帧 WebP/TIFF），当前版本仅处理静态图片，已跳过以避免丢失动画。")
        base = ImageOps.exif_transpose(opened).convert("RGBA")

    overlay = create_overlay_canvas(settings, base.width, base.height, "image")
    base.alpha_composite(overlay)

    output_path.parent.mkdir(parents=True, exist_ok=True)
    suffix = input_path.suffix.lower()
    image_format = {
        ".jpg": "JPEG", ".jpeg": "JPEG", ".png": "PNG", ".webp": "WEBP",
        ".bmp": "BMP", ".tif": "TIFF", ".tiff": "TIFF",
    }.get(suffix)
    if image_format is None:
        raise RuntimeError(f"不支持的图片格式：{suffix}")

    temp_path = output_path.with_name(output_path.stem + ".__watermark_tmp__" + output_path.suffix)
    try:
        if image_format == "JPEG":
            base.convert("RGB").save(temp_path, format="JPEG", quality=95, subsampling=0, optimize=True)
        elif image_format == "WEBP":
            base.save(temp_path, format="WEBP", quality=95, method=6)
        elif image_format == "PNG":
            base.save(temp_path, format="PNG", optimize=True)
        elif image_format == "TIFF":
            base.save(temp_path, format="TIFF", compression="tiff_lzw")
        else:
            base.convert("RGB").save(temp_path, format="BMP")
        temp_path.replace(output_path)
    finally:
        if temp_path.exists():
            try:
                temp_path.unlink()
            except OSError:
                pass


# ---------------------------------------------------------------------------
# FFmpeg 视频处理
# ---------------------------------------------------------------------------


def get_ffmpeg_path() -> str:
    app_dir = Path(__file__).resolve().parent
    local_candidates = [app_dir / "ffmpeg.exe", app_dir / "ffmpeg"]
    for candidate in local_candidates:
        if candidate.is_file():
            return str(candidate)

    from_path = shutil.which("ffmpeg")
    if from_path:
        return from_path

    try:
        import imageio_ffmpeg
        return imageio_ffmpeg.get_ffmpeg_exe()
    except Exception as exc:
        raise RuntimeError(
            "没有找到 FFmpeg。请先运行‘安装依赖.bat’，或将 ffmpeg.exe 放到本程序同一文件夹。"
        ) from exc


def _run_ffmpeg_capture(command: list[str]) -> subprocess.CompletedProcess:
    creationflags = getattr(subprocess, "CREATE_NO_WINDOW", 0) if os.name == "nt" else 0
    return subprocess.run(
        command,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        encoding="utf-8",
        errors="replace",
        creationflags=creationflags,
        check=False,
    )


def extract_video_first_frame(ffmpeg: str, input_path: Path, frame_path: Path) -> tuple[int, int]:
    """提取首帧以获取 FFmpeg 自动旋转后的视频实际画面尺寸。"""
    command = [
        ffmpeg, "-hide_banner", "-loglevel", "error", "-y",
        "-i", str(input_path),
        "-frames:v", "1",
        str(frame_path),
    ]
    result = _run_ffmpeg_capture(command)
    if result.returncode != 0 or not frame_path.is_file():
        raise RuntimeError(f"无法读取视频首帧，无法确定视频尺寸：\n{(result.stderr or '')[-1800:]}")
    try:
        with Image.open(frame_path) as frame:
            return frame.width, frame.height
    except Exception as exc:
        raise RuntimeError(f"读取视频尺寸失败：{exc}") from exc


def run_ffmpeg_watermark(
    ffmpeg: str,
    input_path: Path,
    output_path: Path,
    settings: WatermarkSettings,
    cancel_event: threading.Event,
) -> None:
    output_path.parent.mkdir(parents=True, exist_ok=True)
    temp_output = output_path.with_name(output_path.stem + ".__watermark_tmp__" + output_path.suffix)
    if temp_output.exists():
        try:
            temp_output.unlink()
        except OSError:
            pass

    with tempfile.TemporaryDirectory(prefix="batch_watermark_video_") as temp_dir_name:
        temp_dir = Path(temp_dir_name)
        frame_path = temp_dir / "video_first_frame.png"
        overlay_path = temp_dir / "watermark_full_frame.png"

        frame_width, frame_height = extract_video_first_frame(ffmpeg, input_path, frame_path)
        overlay = create_overlay_canvas(settings, frame_width, frame_height, "video")
        overlay.save(overlay_path, format="PNG", optimize=False)

        # 不再使用 scale2ref。叠加层本身已按视频实际宽高生成，按 1:1 像素叠加，
        # 因而不会出现文字水印纵向被拉长或横向压扁的问题。
        filter_graph = "[0:v:0][1:v:0]overlay=x=0:y=0:format=auto:shortest=1,format=yuv420p[v]"
        base_command = [
            ffmpeg, "-hide_banner", "-loglevel", "error", "-y",
            "-i", str(input_path),
            "-loop", "1", "-i", str(overlay_path),
            "-filter_complex", filter_graph,
            "-map", "[v]", "-map", "0:a?", "-map_metadata", "0",
            "-c:v", "libx264", "-preset", "medium", "-crf", "20",
            "-pix_fmt", "yuv420p",
            "-movflags", "+faststart",
        ]
        commands = [
            base_command + ["-c:a", "copy", str(temp_output)],
            base_command + ["-c:a", "aac", "-b:a", "192k", str(temp_output)],
        ]

        last_error = ""
        for attempt, command in enumerate(commands, start=1):
            if cancel_event.is_set():
                raise InterruptedError("用户停止了处理。")
            if temp_output.exists():
                try:
                    temp_output.unlink()
                except OSError:
                    pass

            creationflags = getattr(subprocess, "CREATE_NO_WINDOW", 0) if os.name == "nt" else 0
            process = subprocess.Popen(
                command,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                encoding="utf-8",
                errors="replace",
                creationflags=creationflags,
            )
            while process.poll() is None:
                if cancel_event.wait(0.2):
                    process.kill()
                    try:
                        process.communicate(timeout=3)
                    except Exception:
                        pass
                    raise InterruptedError("用户停止了处理。")

            _stdout, stderr = process.communicate()
            if process.returncode == 0 and temp_output.exists() and temp_output.stat().st_size > 0:
                temp_output.replace(output_path)
                return

            last_error = (stderr or "FFmpeg 未生成有效输出文件。")[-2500:]
            if attempt == 1:
                continue

        if temp_output.exists():
            try:
                temp_output.unlink()
            except OSError:
                pass
        raise RuntimeError(f"FFmpeg 处理失败：\n{last_error}")


# ---------------------------------------------------------------------------
# 批量任务
# ---------------------------------------------------------------------------


def collect_media_files(input_root: Path, output_root: Path, excluded_file: Optional[Path] = None) -> list[Path]:
    files: list[Path] = []
    input_root = input_root.resolve()
    output_root = output_root.resolve()
    excluded = excluded_file.resolve() if excluded_file else None
    output_is_inside_input = output_root != input_root and path_is_inside(output_root, input_root)

    for current, dirnames, filenames in os.walk(input_root):
        current_path = Path(current)
        if output_is_inside_input:
            dirnames[:] = [
                dirname for dirname in dirnames
                if not path_is_inside(current_path / dirname, output_root)
            ]
        for filename in filenames:
            file_path = current_path / filename
            if file_path.suffix.lower() not in SUPPORTED_EXTENSIONS:
                continue
            try:
                resolved = file_path.resolve()
                if excluded is not None and resolved == excluded:
                    continue
                if output_is_inside_input and path_is_inside(resolved, output_root):
                    continue
            except OSError:
                continue
            files.append(file_path)

    files.sort(key=lambda path: str(path).casefold())
    return files


class BatchWorker(threading.Thread):
    def __init__(
        self,
        input_root: Path,
        output_root: Path,
        settings: WatermarkSettings,
        overwrite: bool,
        log_queue: queue.Queue,
        cancel_event: threading.Event,
    ) -> None:
        super().__init__(daemon=True)
        self.input_root = input_root
        self.output_root = output_root
        self.settings = settings
        self.overwrite = overwrite
        self.log_queue = log_queue
        self.cancel_event = cancel_event

    def send(self, kind: str, payload=None) -> None:
        self.log_queue.put((kind, payload))

    def run(self) -> None:
        success = failed = skipped = 0
        try:
            excluded = Path(self.settings.watermark_image) if self.settings.mode == "image" else None
            media_files = collect_media_files(self.input_root, self.output_root, excluded)
            if not media_files:
                self.send("log", "没有找到支持的图片或 MP4 视频文件。")
                self.send("done", {"success": 0, "failed": 0, "skipped": 0, "cancelled": False})
                return

            self.send("log", f"扫描完成：找到 {len(media_files)} 个待处理文件。")
            ffmpeg = None
            if any(path.suffix.lower() in VIDEO_EXTENSIONS for path in media_files):
                ffmpeg = get_ffmpeg_path()
                self.send("log", f"视频处理引擎：{ffmpeg}")

            total = len(media_files)
            for index, source in enumerate(media_files, start=1):
                if self.cancel_event.is_set():
                    break
                relative = source.relative_to(self.input_root)
                target = self.output_root / relative
                self.send("progress", {"current": index, "total": total, "name": relative.as_posix()})

                if target.exists() and not self.overwrite:
                    skipped += 1
                    self.send("log", f"[跳过] 输出文件已存在：{relative}")
                    continue

                try:
                    if source.suffix.lower() in IMAGE_EXTENSIONS:
                        apply_watermark_to_image(source, target, self.settings)
                    elif source.suffix.lower() in VIDEO_EXTENSIONS:
                        assert ffmpeg is not None
                        run_ffmpeg_watermark(ffmpeg, source, target, self.settings, self.cancel_event)
                    else:
                        skipped += 1
                        continue
                    success += 1
                    self.send("log", f"[完成] {relative}")
                except InterruptedError:
                    self.send("log", "收到停止指令，已停止后续文件处理。")
                    break
                except Exception as exc:
                    failed += 1
                    self.send("log", f"[失败] {relative}\n       原因：{exc}")

            self.send("done", {
                "success": success,
                "failed": failed,
                "skipped": skipped,
                "cancelled": self.cancel_event.is_set(),
            })
        except Exception as exc:
            self.send("fatal", f"任务无法启动：{exc}\n{traceback.format_exc(limit=4)}")
            self.send("done", {
                "success": success,
                "failed": failed,
                "skipped": skipped,
                "cancelled": self.cancel_event.is_set(),
            })


# ---------------------------------------------------------------------------
# Tkinter 界面
# ---------------------------------------------------------------------------


class WatermarkApp:
    def __init__(self, root: tk.Tk) -> None:
        self.root = root
        self.root.title(APP_TITLE)
        # 页面初始大小和最小大小由文件顶部的 WINDOW_* 常量统一控制。
        self.root.geometry(WINDOW_GEOMETRY)
        self.root.minsize(WINDOW_MIN_WIDTH, WINDOW_MIN_HEIGHT)

        self._apply_large_fonts()

        self.log_queue: queue.Queue = queue.Queue()
        self.cancel_event = threading.Event()
        self.worker: Optional[BatchWorker] = None
        self.default_font = find_default_font()

        self.input_var = tk.StringVar()
        self.output_var = tk.StringVar()
        self.mode_var = tk.StringVar(value="text")
        self.text_var = tk.StringVar()
        self.image_var = tk.StringVar()
        self.font_var = tk.StringVar(value=self.default_font)

        self.text_color_var = tk.StringVar(value="#FFFFFF")
        self.text_opacity_var = tk.IntVar(value=80)
        self.image_opacity_var = tk.IntVar(value=80)
        self.image_size_var = tk.IntVar(value=20)
        self.video_size_var = tk.IntVar(value=20)
        self.position_var = tk.StringVar(value="右下")
        self.margin_var = tk.DoubleVar(value=2.0)

        self.stroke_enabled_var = tk.BooleanVar(value=False)
        self.stroke_width_var = tk.IntVar(value=3)
        self.stroke_color_var = tk.StringVar(value="#000000")

        self.shadow_enabled_var = tk.BooleanVar(value=False)
        self.shadow_color_var = tk.StringVar(value="#000000")
        self.shadow_x_var = tk.IntVar(value=4)
        self.shadow_y_var = tk.IntVar(value=4)
        self.shadow_blur_var = tk.IntVar(value=3)

        self.tile_enabled_var = tk.BooleanVar(value=False)
        self.tile_gap_var = tk.IntVar(value=100)
        self.rotate_var = tk.BooleanVar(value=False)

        self._build_scrollable_area()
        self._build_ui()
        self._update_mode_controls()
        self._update_effect_controls()
        self.root.after(120, self._poll_queue)
        self.root.protocol("WM_DELETE_WINDOW", self._on_close)

    def _apply_large_fonts(self) -> None:
        """全局字体按 V2 的实际字号统一缩小 20%，避免局部遗漏。"""
        family = "Microsoft YaHei UI" if os.name == "nt" else "TkDefaultFont"
        for name in (
            "TkDefaultFont", "TkTextFont", "TkFixedFont", "TkMenuFont",
            "TkHeadingFont", "TkCaptionFont", "TkSmallCaptionFont", "TkIconFont",
            "TkTooltipFont",
        ):
            try:
                font = tkfont.nametofont(name)
                old_size = int(font.cget("size"))
                previous_v2_size = max(14, abs(old_size) * 2)
                new_size = max(11, round(previous_v2_size * UI_FONT_SCALE))
                if old_size < 0:
                    new_size = -new_size
                font.configure(size=new_size, family=family if name != "TkFixedFont" else "Consolas")
            except Exception:
                pass

        style = ttk.Style(self.root)
        style.configure(".", font=(family, UI_BASE_FONT_SIZE))
        style.configure("TButton", padding=(10, 6))
        style.configure("TEntry", padding=(6, 5))
        style.configure("TCombobox", padding=(6, 5))
        style.configure("TLabelframe.Label", font=(family, UI_BASE_FONT_SIZE, "bold"))
        style.configure("TCheckbutton", padding=(2, 3))
        style.configure("TRadiobutton", padding=(2, 3))

    def _build_scrollable_area(self) -> None:
        shell = ttk.Frame(self.root)
        shell.pack(fill="both", expand=True)
        self.canvas = tk.Canvas(shell, highlightthickness=0, borderwidth=0)
        scrollbar = ttk.Scrollbar(shell, orient="vertical", command=self.canvas.yview)
        self.canvas.configure(yscrollcommand=scrollbar.set)
        scrollbar.pack(side="right", fill="y")
        self.canvas.pack(side="left", fill="both", expand=True)

        self.outer = ttk.Frame(self.canvas, padding=18)
        self.canvas_window = self.canvas.create_window((0, 0), window=self.outer, anchor="nw")
        self.outer.bind("<Configure>", self._on_content_configure)
        self.canvas.bind("<Configure>", self._on_canvas_configure)
        self.canvas.bind_all("<MouseWheel>", self._on_mousewheel)
        self.canvas.bind_all("<Button-4>", lambda _event: self.canvas.yview_scroll(-2, "units"))
        self.canvas.bind_all("<Button-5>", lambda _event: self.canvas.yview_scroll(2, "units"))

    def _on_content_configure(self, _event=None) -> None:
        self.canvas.configure(scrollregion=self.canvas.bbox("all"))

    def _on_canvas_configure(self, event) -> None:
        self.canvas.itemconfigure(self.canvas_window, width=event.width)

    def _on_mousewheel(self, event) -> None:
        if getattr(event, "delta", 0):
            self.canvas.yview_scroll(int(-event.delta / 120), "units")

    def _make_responsive_row(self, parent, min_column_width: int = 340, pady: int = 4):
        """创建可换行的控件流容器；窗口变窄时自动将控件组排到下一行。"""
        row = ttk.Frame(parent)
        row.pack(fill="x", expand=True, pady=pady)
        row._responsive_groups = []
        row._responsive_min_column_width = max(180, int(min_column_width))
        row._responsive_columns = None
        row.bind("<Configure>", lambda event, target=row: self._reflow_responsive_row(target))
        return row

    def _add_responsive_group(self, row):
        """向自适应行添加一个控件组。组内控件可继续使用 pack(side='left')。"""
        group = ttk.Frame(row)
        row._responsive_groups.append(group)
        self.root.after_idle(lambda target=row: self._reflow_responsive_row(target))
        return group

    def _reflow_responsive_row(self, row) -> None:
        groups = getattr(row, "_responsive_groups", None)
        if not groups:
            return
        available_width = max(1, row.winfo_width())
        min_width = row._responsive_min_column_width
        # 预留组间距，避免刚好贴边时出现控件挤压。
        columns = max(1, min(len(groups), (available_width + 20) // (min_width + 20)))
        if row._responsive_columns == columns:
            return
        row._responsive_columns = columns
        for column in range(len(groups)):
            row.grid_columnconfigure(column, weight=0, uniform="")
        for column in range(columns):
            row.grid_columnconfigure(column, weight=1, uniform=f"responsive_{id(row)}")
        for index, group in enumerate(groups):
            group.grid(
                row=index // columns,
                column=index % columns,
                sticky="w",
                padx=(0, 18),
                pady=(2, 5),
            )

    def _bind_responsive_wrap(self, widget, container, padding: int = 24) -> None:
        """让说明文字的换行宽度跟随容器，而不是使用固定像素宽度。"""
        def update_wrap(event=None):
            width = container.winfo_width() if event is None else event.width
            widget.configure(wraplength=max(140, int(width) - padding))

        container.bind("<Configure>", update_wrap, add="+")
        self.root.after_idle(update_wrap)

    def _build_ui(self) -> None:
        title = ttk.Label(self.outer, text="批量文件水印工具", font=("Microsoft YaHei UI", UI_TITLE_FONT_SIZE, "bold"))
        title.pack(anchor="w")
        subtitle = ttk.Label(
            self.outer,
            text="递归处理图片与 MP4 · 文字/图片水印 · 保留原文件名和目录结构 · 不修改源文件",
            foreground="#555555",
            wraplength=1120,
        )
        subtitle.pack(anchor="w", fill="x", pady=(3, 16))
        self._bind_responsive_wrap(subtitle, self.outer, padding=36)

        folder_frame = ttk.LabelFrame(self.outer, text="一、输入与输出", padding=14)
        folder_frame.pack(fill="x", pady=(0, 12))
        self._add_path_row(folder_frame, "输入文件夹：", self.input_var, self._choose_input, 0)
        self._add_path_row(folder_frame, "输出文件夹：", self.output_var, self._choose_output, 1)

        watermark_frame = ttk.LabelFrame(self.outer, text="二、水印内容", padding=14)
        watermark_frame.pack(fill="x", pady=(0, 12))

        mode_row = ttk.Frame(watermark_frame)
        mode_row.pack(fill="x", pady=(0, 10))
        ttk.Label(mode_row, text="水印类型：", width=12).pack(side="left")
        ttk.Radiobutton(
            mode_row, text="文字水印", variable=self.mode_var, value="text",
            command=self._update_mode_controls,
        ).pack(side="left", padx=(0, 24))
        ttk.Radiobutton(
            mode_row, text="图片水印", variable=self.mode_var, value="image",
            command=self._update_mode_controls,
        ).pack(side="left")

        self.text_row = ttk.Frame(watermark_frame)
        self.text_row.pack(fill="x", pady=4)
        ttk.Label(self.text_row, text="水印文字：", width=12).pack(side="left")
        self.text_entry = ttk.Entry(self.text_row, textvariable=self.text_var)
        self.text_entry.pack(side="left", fill="x", expand=True)

        self.image_row = ttk.Frame(watermark_frame)
        self.image_row.pack(fill="x", pady=4)
        ttk.Label(self.image_row, text="水印图片：", width=12).pack(side="left")
        self.image_entry = ttk.Entry(self.image_row, textvariable=self.image_var)
        self.image_entry.pack(side="left", fill="x", expand=True)
        self.image_button = ttk.Button(self.image_row, text="选择图片", command=self._choose_watermark_image)
        self.image_button.pack(side="left", padx=(8, 0))

        self.font_row = ttk.Frame(watermark_frame)
        self.font_row.pack(fill="x", pady=4)
        ttk.Label(self.font_row, text="字体文件：", width=12).pack(side="left")
        self.font_entry = ttk.Entry(self.font_row, textvariable=self.font_var)
        self.font_entry.pack(side="left", fill="x", expand=True)
        self.font_button = ttk.Button(self.font_row, text="选择字体", command=self._choose_font)
        self.font_button.pack(side="left", padx=(8, 0))

        font_help = ttk.Label(
            watermark_frame,
            text="字体文件就是字体本身（例如微软雅黑、黑体、宋体对应的 .ttf / .ttc / .otf 文件），不是普通文本文件。",
            foreground="#555555",
            wraplength=900,
        )
        font_help.pack(anchor="w", padx=(112, 0), fill="x", pady=(0, 6))
        self._bind_responsive_wrap(font_help, watermark_frame, padding=150)

        self.text_color_row = ttk.Frame(watermark_frame)
        self.text_color_row.pack(fill="x", pady=4)
        ttk.Label(self.text_color_row, text="文字颜色：", width=12).pack(side="left")
        self.text_color_button = ttk.Button(
            self.text_color_row,
            text=self.text_color_var.get(),
            command=lambda: self._choose_color(self.text_color_var, self.text_color_button, "选择文字颜色"),
        )
        self.text_color_button.pack(side="left")

        effects_frame = ttk.LabelFrame(self.outer, text="三、文字效果（仅文字水印）", padding=14)
        effects_frame.pack(fill="x", pady=(0, 12))

        # 每个设置组独立布局，容器宽度不足时自动换到下一行。
        self.stroke_row = self._make_responsive_row(effects_frame, min_column_width=300, pady=2)
        stroke_toggle_group = self._add_responsive_group(self.stroke_row)
        self.stroke_check = ttk.Checkbutton(
            stroke_toggle_group, text="开启文字描边", variable=self.stroke_enabled_var,
            command=self._update_effect_controls,
        )
        self.stroke_check.pack(side="left")

        stroke_width_group = self._add_responsive_group(self.stroke_row)
        ttk.Label(stroke_width_group, text="描边粗细（1080p基准）：").pack(side="left")
        self.stroke_width_spin = ttk.Spinbox(
            stroke_width_group, from_=1, to=20, textvariable=self.stroke_width_var, width=6
        )
        self.stroke_width_spin.pack(side="left", padx=(4, 0))

        stroke_color_group = self._add_responsive_group(self.stroke_row)
        ttk.Label(stroke_color_group, text="描边颜色：").pack(side="left")
        self.stroke_color_button = ttk.Button(
            stroke_color_group, text=self.stroke_color_var.get(),
            command=lambda: self._choose_color(self.stroke_color_var, self.stroke_color_button, "选择描边颜色"),
        )
        self.stroke_color_button.pack(side="left", padx=(4, 0))

        self.shadow_row = self._make_responsive_row(effects_frame, min_column_width=260, pady=2)
        shadow_toggle_group = self._add_responsive_group(self.shadow_row)
        self.shadow_check = ttk.Checkbutton(
            shadow_toggle_group, text="开启文字阴影", variable=self.shadow_enabled_var,
            command=self._update_effect_controls,
        )
        self.shadow_check.pack(side="left")

        shadow_color_group = self._add_responsive_group(self.shadow_row)
        ttk.Label(shadow_color_group, text="阴影颜色：").pack(side="left")
        self.shadow_color_button = ttk.Button(
            shadow_color_group, text=self.shadow_color_var.get(),
            command=lambda: self._choose_color(self.shadow_color_var, self.shadow_color_button, "选择阴影颜色"),
        )
        self.shadow_color_button.pack(side="left", padx=(4, 0))

        shadow_offset_group = self._add_responsive_group(self.shadow_row)
        ttk.Label(shadow_offset_group, text="偏移 X：").pack(side="left")
        self.shadow_x_spin = ttk.Spinbox(
            shadow_offset_group, from_=-50, to=50, textvariable=self.shadow_x_var, width=5
        )
        self.shadow_x_spin.pack(side="left", padx=(4, 10))
        ttk.Label(shadow_offset_group, text="Y：").pack(side="left")
        self.shadow_y_spin = ttk.Spinbox(
            shadow_offset_group, from_=-50, to=50, textvariable=self.shadow_y_var, width=5
        )
        self.shadow_y_spin.pack(side="left", padx=(4, 0))

        shadow_blur_group = self._add_responsive_group(self.shadow_row)
        ttk.Label(shadow_blur_group, text="模糊：").pack(side="left")
        self.shadow_blur_spin = ttk.Spinbox(
            shadow_blur_group, from_=0, to=30, textvariable=self.shadow_blur_var, width=5
        )
        self.shadow_blur_spin.pack(side="left", padx=(4, 0))

        style_frame = ttk.LabelFrame(self.outer, text="四、水印大小与透明度", padding=14)
        style_frame.pack(fill="x", pady=(0, 12))

        self._add_slider_row(style_frame, "图片水印宽度：", self.image_size_var, 5, 80, "%")
        self._add_slider_row(style_frame, "视频水印宽度：", self.video_size_var, 5, 80, "%")
        self._add_slider_row(style_frame, "文字水印透明度：", self.text_opacity_var, 0, 100, "%")
        self._add_slider_row(style_frame, "图片水印透明度：", self.image_opacity_var, 0, 100, "%")

        position_frame = ttk.LabelFrame(self.outer, text="五、水印位置与铺设方式", padding=14)
        position_frame.pack(fill="x", pady=(0, 12))

        pos_row = self._make_responsive_row(position_frame, min_column_width=340, pady=2)
        position_group = self._add_responsive_group(pos_row)
        ttk.Label(position_group, text="单个水印位置：").pack(side="left")
        self.position_box = ttk.Combobox(
            position_group, textvariable=self.position_var, state="readonly", width=16,
            values=list(POSITION_LABELS.keys()),
        )
        self.position_box.pack(side="left", padx=(4, 0))

        margin_group = self._add_responsive_group(pos_row)
        ttk.Label(margin_group, text="边距：").pack(side="left")
        self.margin_spin = ttk.Spinbox(
            margin_group, from_=0, to=20, increment=0.5, textvariable=self.margin_var, width=7
        )
        self.margin_spin.pack(side="left", padx=(4, 5))
        ttk.Label(margin_group, text="%（相对画面宽高）").pack(side="left")

        tile_row = self._make_responsive_row(position_frame, min_column_width=300, pady=2)
        tile_toggle_group = self._add_responsive_group(tile_row)
        self.tile_check = ttk.Checkbutton(
            tile_toggle_group, text="开启满屏平铺水印", variable=self.tile_enabled_var,
        )
        self.tile_check.pack(side="left")

        tile_gap_group = self._add_responsive_group(tile_row)
        ttk.Label(tile_gap_group, text="水印间距：").pack(side="left")
        self.tile_gap_spin = ttk.Spinbox(
            tile_gap_group, from_=0, to=500, increment=10, textvariable=self.tile_gap_var, width=7
        )
        self.tile_gap_spin.pack(side="left", padx=(4, 5))
        ttk.Label(tile_gap_group, text="%（相对于水印自身宽高）").pack(side="left")

        tile_help = ttk.Label(
            position_frame,
            text="间距数值越大，水印越稀疏。开启满屏模式后，单个水印位置设置不生效。",
            foreground="#555555",
            wraplength=900,
        )
        tile_help.pack(anchor="w", fill="x", pady=(0, 4))
        self._bind_responsive_wrap(tile_help, position_frame, padding=36)

        rotate_row = self._make_responsive_row(position_frame, min_column_width=300, pady=2)
        rotate_toggle_group = self._add_responsive_group(rotate_row)
        ttk.Checkbutton(
            rotate_toggle_group, text="水印倾斜 45°", variable=self.rotate_var,
        ).pack(side="left")

        rotate_help = ttk.Label(
            position_frame,
            text="适用于文字水印和图片水印；取消勾选则保持水平。",
            foreground="#555555",
            wraplength=900,
        )
        rotate_help.pack(anchor="w", fill="x", pady=(0, 4))
        self._bind_responsive_wrap(rotate_help, position_frame, padding=36)

        note = ttk.Label(
            position_frame,
            text="说明：图片和视频使用各自的水印宽度百分比。窗口变窄时，本部分设置项会自动换行。",
            foreground="#555555",
            wraplength=900,
        )
        note.pack(anchor="w", fill="x", pady=(6, 0))
        self._bind_responsive_wrap(note, position_frame, padding=36)

        action_row = ttk.Frame(self.outer)
        action_row.pack(fill="x", pady=(2, 10))
        self.start_button = ttk.Button(action_row, text="开始批量添加水印", command=self._start)
        self.start_button.pack(side="left")
        self.stop_button = ttk.Button(action_row, text="停止", command=self._stop, state="disabled")
        self.stop_button.pack(side="left", padx=(10, 0))
        self.progress_label = ttk.Label(action_row, text="等待开始")
        self.progress_label.pack(side="right")

        self.progress = ttk.Progressbar(self.outer, mode="determinate", maximum=100)
        self.progress.pack(fill="x", pady=(0, 12))

        log_frame = ttk.LabelFrame(self.outer, text="处理日志", padding=12)
        log_frame.pack(fill="both", expand=True)
        self.log_text = ScrolledText(log_frame, height=12, wrap="word", font=("Consolas", UI_LOG_FONT_SIZE))
        self.log_text.pack(fill="both", expand=True)
        self.log_text.configure(state="disabled")

        footer = ttk.Label(
            self.outer,
            text="支持：PNG / JPG / JPEG / WEBP / BMP / TIF / TIFF / MP4。输出文件名和相对目录结构与输入保持一致。已有输出文件可选择覆盖或跳过。",
            foreground="#555555",
            wraplength=900,
        )
        footer.pack(anchor="w", fill="x", pady=(10, 4))
        self._bind_responsive_wrap(footer, self.outer, padding=36)

    def _add_path_row(self, parent, label, variable, command, row) -> None:
        frame = ttk.Frame(parent)
        frame.grid(row=row, column=0, sticky="ew", pady=5)
        parent.columnconfigure(0, weight=1)
        ttk.Label(frame, text=label, width=14).pack(side="left")
        entry = ttk.Entry(frame, textvariable=variable)
        entry.pack(side="left", fill="x", expand=True)
        ttk.Button(frame, text="浏览…", command=command).pack(side="left", padx=(8, 0))

    def _add_slider_row(self, parent, label, variable, minimum, maximum, suffix) -> None:
        row = ttk.Frame(parent)
        row.pack(fill="x", pady=5)
        ttk.Label(row, text=label, width=18).pack(side="left")
        value_label = ttk.Label(row, text=f"{int(variable.get())}{suffix}", width=8, anchor="e")
        value_label.pack(side="right")
        slider = ttk.Scale(row, from_=minimum, to=maximum, orient="horizontal")
        slider.pack(side="left", fill="x", expand=True, padx=(0, 12))
        # 先设置初始值，再绑定 command，避免初始化时回调访问尚未创建的标签。
        slider.set(variable.get())
        slider.configure(command=lambda value, var=variable, label_widget=value_label, unit=suffix:
                          self._on_slider(value, var, label_widget, unit))

    def _on_slider(self, value, variable, label_widget, suffix) -> None:
        number = int(float(value))
        variable.set(number)
        label_widget.configure(text=f"{number}{suffix}")

    def _choose_input(self) -> None:
        path = filedialog.askdirectory(title="选择需要添加水印的输入文件夹")
        if path:
            self.input_var.set(path)
            if not self.output_var.get().strip():
                source = Path(path)
                self.output_var.set(str(source.parent / (source.name + "_水印输出")))

    def _choose_output(self) -> None:
        path = filedialog.askdirectory(title="选择水印文件输出文件夹")
        if path:
            self.output_var.set(path)

    def _choose_watermark_image(self) -> None:
        path = filedialog.askopenfilename(
            title="选择图片水印",
            filetypes=[("图片文件", "*.png *.jpg *.jpeg *.webp *.bmp *.tif *.tiff"), ("所有文件", "*.*")],
        )
        if path:
            self.image_var.set(path)

    def _choose_font(self) -> None:
        path = filedialog.askopenfilename(
            title="选择字体文件（建议选择支持中文的字体）",
            filetypes=[("字体文件", "*.ttf *.ttc *.otf"), ("所有文件", "*.*")],
        )
        if path:
            self.font_var.set(path)

    def _choose_color(self, variable: tk.StringVar, button: ttk.Button, title: str) -> None:
        selected = colorchooser.askcolor(color=variable.get(), title=title, parent=self.root)
        if selected and selected[1]:
            color = selected[1].upper()
            variable.set(color)
            button.configure(text=color)

    def _update_mode_controls(self) -> None:
        is_text = self.mode_var.get() == "text"
        text_state = "normal" if is_text else "disabled"
        image_state = "disabled" if is_text else "normal"
        for widget in (self.text_entry, self.font_entry, self.font_button, self.text_color_button):
            widget.configure(state=text_state)
        for widget in (self.image_entry, self.image_button):
            widget.configure(state=image_state)
        self._update_effect_controls()

    def _update_effect_controls(self) -> None:
        is_text = self.mode_var.get() == "text"
        stroke_on = is_text and self.stroke_enabled_var.get()
        shadow_on = is_text and self.shadow_enabled_var.get()
        self.stroke_check.configure(state="normal" if is_text else "disabled")
        self.stroke_width_spin.configure(state="normal" if stroke_on else "disabled")
        self.stroke_color_button.configure(state="normal" if stroke_on else "disabled")
        self.shadow_check.configure(state="normal" if is_text else "disabled")
        for widget in (self.shadow_color_button, self.shadow_x_spin, self.shadow_y_spin, self.shadow_blur_spin):
            widget.configure(state="normal" if shadow_on else "disabled")

    def _get_settings(self) -> WatermarkSettings:
        mode = self.mode_var.get()
        settings = WatermarkSettings(
            mode=mode,
            text=self.text_var.get().strip(),
            watermark_image=self.image_var.get().strip(),
            font_path=self.font_var.get().strip(),
            text_color=self.text_color_var.get(),
            text_opacity=int(self.text_opacity_var.get()),
            image_opacity=int(self.image_opacity_var.get()),
            image_size_percent=int(self.image_size_var.get()),
            video_size_percent=int(self.video_size_var.get()),
            position=POSITION_LABELS.get(self.position_var.get(), "bottom_right"),
            margin_percent=float(self.margin_var.get()),
            stroke_enabled=bool(self.stroke_enabled_var.get()),
            stroke_width=int(self.stroke_width_var.get()),
            stroke_color=self.stroke_color_var.get(),
            shadow_enabled=bool(self.shadow_enabled_var.get()),
            shadow_color=self.shadow_color_var.get(),
            shadow_offset_x=int(self.shadow_x_var.get()),
            shadow_offset_y=int(self.shadow_y_var.get()),
            shadow_blur=int(self.shadow_blur_var.get()),
            tile_enabled=bool(self.tile_enabled_var.get()),
            tile_gap_percent=int(self.tile_gap_var.get()),
            rotate_45=bool(self.rotate_var.get()),
        )

        if mode == "text" and not settings.text:
            raise ValueError("请填写文字水印内容。")
        if mode == "image":
            if not settings.watermark_image or not Path(settings.watermark_image).is_file():
                raise ValueError("请选择有效的图片水印文件。")
        if settings.font_path and not Path(settings.font_path).is_file():
            raise ValueError("所选字体文件不存在，请重新选择字体。")
        if not (0 <= settings.margin_percent <= 20):
            raise ValueError("边距应在 0% 到 20% 之间。")
        if not (0 <= settings.tile_gap_percent <= 500):
            raise ValueError("水印间距应在 0% 到 500% 之间。")
        if settings.stroke_width < 1 or settings.stroke_width > 20:
            raise ValueError("描边粗细应在 1 到 20（1080p参考像素）之间。")
        if settings.shadow_blur < 0 or settings.shadow_blur > 30:
            raise ValueError("阴影模糊值应在 0 到 30 之间。")
        parse_hex_color(settings.text_color)
        parse_hex_color(settings.stroke_color)
        parse_hex_color(settings.shadow_color)
        return settings

    def _start(self) -> None:
        if self.worker is not None and self.worker.is_alive():
            return
        try:
            input_text = self.input_var.get().strip()
            output_text = self.output_var.get().strip()
            if not input_text:
                raise ValueError("请选择输入文件夹。")
            if not output_text:
                raise ValueError("请选择输出文件夹。")
            input_root = Path(input_text).expanduser().resolve()
            output_root = Path(output_text).expanduser().resolve()
            if not input_root.is_dir():
                raise ValueError("请选择有效的输入文件夹。")
            if input_root == output_root:
                raise ValueError("输入文件夹和输出文件夹不能是同一个目录，以免覆盖原文件。")
            settings = self._get_settings()
        except Exception as exc:
            messagebox.showerror("设置有误", str(exc), parent=self.root)
            return

        files = collect_media_files(
            input_root,
            output_root,
            Path(settings.watermark_image) if settings.mode == "image" else None,
        )
        if not files:
            messagebox.showinfo("没有可处理文件", "输入文件夹及其子文件夹中没有找到支持的图片或 MP4 视频。", parent=self.root)
            return

        existing_count = sum(1 for source in files if (output_root / source.relative_to(input_root)).exists())
        overwrite = False
        if existing_count:
            overwrite = messagebox.askyesno(
                "发现同名输出文件",
                f"输出目录中已有 {existing_count} 个同名文件。\n\n"
                "选择‘是’：覆盖已有输出文件。\n"
                "选择‘否’：跳过这些已存在的输出文件。\n\n"
                "输入目录中的原文件始终不会被修改。",
                parent=self.root,
            )

        output_root.mkdir(parents=True, exist_ok=True)
        self.cancel_event.clear()
        self.progress.configure(value=0, maximum=len(files))
        self.progress_label.configure(text=f"准备处理 {len(files)} 个文件")
        self.start_button.configure(state="disabled")
        self.stop_button.configure(state="normal")
        self._append_log("=" * 70)
        self._append_log(f"输入目录：{input_root}")
        self._append_log(f"输出目录：{output_root}")
        self._append_log(f"水印类型：{'文字水印' if settings.mode == 'text' else '图片水印'}")
        self._append_log(f"图片水印宽度：{settings.image_size_percent}%；视频水印宽度：{settings.video_size_percent}%")
        if settings.mode == "text" and settings.stroke_enabled:
            self._append_log(f"文字描边：{settings.stroke_width}（1080p参考像素），按输出画面分辨率自动适配")
        self._append_log(f"满屏平铺：{'开启' if settings.tile_enabled else '关闭'}；45°旋转：{'开启' if settings.rotate_45 else '关闭'}")
        self._append_log(f"扫描到 {len(files)} 个文件，开始处理……")

        self.worker = BatchWorker(
            input_root, output_root, settings, overwrite, self.log_queue, self.cancel_event
        )
        self.worker.start()

    def _append_log(self, message: str) -> None:
        self.log_text.configure(state="normal")
        self.log_text.insert("end", message + "\n")
        self.log_text.see("end")
        self.log_text.configure(state="disabled")

    def _stop(self) -> None:
        if self.worker is not None and self.worker.is_alive():
            self.cancel_event.set()
            self.stop_button.configure(state="disabled")
            self.progress_label.configure(text="正在停止……")
            self._append_log("已请求停止，当前正在处理的视频会尽快中止。")

    def _poll_queue(self) -> None:
        try:
            while True:
                kind, payload = self.log_queue.get_nowait()
                if kind == "log":
                    self._append_log(str(payload))
                elif kind == "progress":
                    current = payload["current"]
                    total = payload["total"]
                    self.progress.configure(maximum=total, value=current - 1)
                    self.progress_label.configure(text=f"正在处理 {current}/{total}：{payload['name']}")
                elif kind == "fatal":
                    self._append_log(str(payload))
                elif kind == "done":
                    if not payload["cancelled"]:
                        self.progress.configure(value=self.progress["maximum"])
                    summary = (
                        f"处理结束：成功 {payload['success']} 个，失败 {payload['failed']} 个，"
                        f"跳过 {payload['skipped']} 个。"
                    )
                    if payload["cancelled"]:
                        summary += "（任务已停止）"
                    self._append_log(summary)
                    self.progress_label.configure(text="已停止" if payload["cancelled"] else "处理完成")
                    self.start_button.configure(state="normal")
                    self.stop_button.configure(state="disabled")
                    if not payload["cancelled"]:
                        messagebox.showinfo("批量处理完成", summary, parent=self.root)
        except queue.Empty:
            pass
        self.root.after(120, self._poll_queue)

    def _on_close(self) -> None:
        if self.worker is not None and self.worker.is_alive():
            if not messagebox.askyesno("任务正在运行", "当前批量任务仍在运行，确定要停止并关闭吗？", parent=self.root):
                return
            self.cancel_event.set()
        self.root.destroy()


def main() -> None:
    # Windows DPI 感知应尽量在创建 Tk 根窗口之前设置。
    if os.name == "nt":
        try:
            from ctypes import windll
            windll.shcore.SetProcessDpiAwareness(1)
        except Exception:
            pass

    root = tk.Tk()
    WatermarkApp(root)
    root.mainloop()


if __name__ == "__main__":
    main()
