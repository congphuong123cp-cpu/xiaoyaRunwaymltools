# -*- coding: utf-8 -*-
"""
RunwayML Video Generation Plugin

Target platform: app.runwayml.com / api.dev.runwayml.com

Features:
- Dual-mode: API mode (official REST API) and Playwright mode (web automation)
- Image-to-video, text-to-video, video-to-video generation
- Async task creation, polling, and result download
- Account pool with API key rotation
- File upload for local images via RunwayML upload API

Architecture adapted from Jimeng Dreamina plugin:
- Same generate(context) entry point
- Same _SiteProfile / _TaskRuntime pattern
- Same account pool / cookie management
- Same progress callback / logging infrastructure
"""

from __future__ import annotations

import base64
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import threading
import time
import traceback
import tempfile
import uuid
import zipfile
from dataclasses import asdict, dataclass
from datetime import datetime
from pathlib import Path
from typing import Any
from urllib.parse import urljoin

import requests

CORE_DIR = Path(__file__).resolve().parent
if str(CORE_DIR) not in sys.path:
    sys.path.insert(0, str(CORE_DIR))
PLUGIN_ROOT_DIR = CORE_DIR.parent
DATA_DIR = PLUGIN_ROOT_DIR / "data"
DATA_DIR.mkdir(parents=True, exist_ok=True)
RUNTIME_ROOT_DIR = PLUGIN_ROOT_DIR / "runtime"

plugin_dir = RUNTIME_ROOT_DIR / "chrome_buffer" / "runwayml_global"
PY_DEPS_DIR = plugin_dir / ".runwayml_pydeps"
_PW_BROWSERS_DIR = plugin_dir / ".runwayml_playwright_browsers"

try:
    PY_DEPS_DIR.mkdir(parents=True, exist_ok=True)
except Exception:
    pass
try:
    _PW_BROWSERS_DIR.mkdir(parents=True, exist_ok=True)
except Exception:
    pass
if str(PY_DEPS_DIR) not in sys.path:
    sys.path.insert(0, str(PY_DEPS_DIR))

os.environ["PLAYWRIGHT_BROWSERS_PATH"] = str(_PW_BROWSERS_DIR)

account_pool_file = str(CORE_DIR / "runwayml_api_keys.txt")

_PLUGIN_FILE = __file__
_LOG_FILE = plugin_dir / "runwayml_plugin_debug.log"
_ENV_LOGGED = False
_TASK_TAG = ""
_LOG_ROTATE_BYTES = 20 * 1024 * 1024
_PLUGIN_VERSION = "2026.06.06.3"
_UPDATE_REPO = "congphuong123cp-cpu/xiaoyaRunwaymltools"
_UPDATE_VERSION_URL = f"https://raw.githubusercontent.com/{_UPDATE_REPO}/main/version.json"
_UPDATE_ARCHIVE_URL = f"https://github.com/{_UPDATE_REPO}/archive/refs/heads/main.zip"

RUNWAYML_API_BASE = "https://api.dev.runwayml.com/v1"
RUNWAYML_WEB_BASE = "https://app.runwayml.com"
RUNWAYML_API_VERSION = "2024-11-06"


@dataclass(frozen=True)
class _SiteProfile:
    key: str
    base_url: str
    api_base: str
    login_url: str
    generate_url: str
    domains: tuple[str, ...]
    display_name: str


_SITE_PROFILES: dict[str, _SiteProfile] = {
    "runwayml": _SiteProfile(
        key="runwayml",
        base_url=RUNWAYML_WEB_BASE,
        api_base=RUNWAYML_API_BASE,
        login_url=f"{RUNWAYML_WEB_BASE}/",
        generate_url=f"{RUNWAYML_WEB_BASE}/",
        domains=("runwayml.com", ".runwayml.com"),
        display_name="RunwayML",
    ),
}

_DEFAULT_SITE_PROFILE_KEY = "runwayml"

_PRECHECK_TEST_PROMPT = "测试是否有可用通道，Generate按钮蓝色代表可执行，灰色代表通道已满！"
_PRECHECK_MAX_WAIT_SECONDS = 50 * 60
_PRECHECK_POLL_INTERVAL_MS = 10 * 1000
_CAPACITY_COOLDOWN_SECONDS = 600
_ERROR_CONFIRM_INTERVAL_SECONDS = 10
_MIN_RESULT_ACCEPT_SECONDS = 30


def _is_manual_close_error(msg: str) -> bool:
    lower = str(msg or "").lower()
    return (
        "target closed" in lower
        or "target page" in lower and "closed" in lower
        or "browser closed" in lower
        or "browser has been closed" in lower
        or "context closed" in lower
        or "page closed" in lower
        or "has been closed" in lower
        or "手动关闭" in msg
        or "被关闭" in msg
        or "已关闭" in msg
    )


def _is_prompt_policy_error(msg: str) -> bool:
    lower = str(msg or "").lower()
    if _is_runway_technical_glitch(msg):
        return False
    return (
        "违规" in msg
        or "usage policy" in lower
        or "safety policy" in lower
        or "prompt violation" in lower
        or "violation" in lower
        or "violates" in lower
        or "blocked by seedance" in lower
        or "request was blocked" in lower
    )


def _is_runway_technical_glitch(msg: str) -> bool:
    lower = str(msg or "").lower()
    return (
        "technical glitch" in lower
        or "nothing to do with your prompt" in lower
        or "credits have been refunded" in lower
        or "try again and it should work" in lower
    )


def _contains_prompt_policy_signal(text: str) -> bool:
    lower = str(text or "").lower()
    if not lower or _is_runway_technical_glitch(lower):
        return False
    explicit_keywords = [
        "violate our usage policy",
        "violates our usage policy",
        "safety policy",
        "usage policy",
        "prompt violation",
        "sexually explicit",
        "inappropriate content",
        "account suspension",
        "blocked by seedance",
        "request was blocked",
        "nsfw",
        "违规",
        "使用政策",
        "内容政策",
        "敏感",
        "审核",
    ]
    return any(kw in lower for kw in explicit_keywords)
@dataclass
class _TaskRuntime:
    task_id: str
    viewer_index: int
    unique_name: str
    generation_round: int
    output_position: int
    site_profile: str
    worker_id: str
    profile_dir: str
    port: int
    account_alias: str
    cookie_header: str = ""
    submit_id: str = ""
    status: str = "queued"
    output_path: str = ""


_TASK_RUNTIME_LOCK = threading.Lock()
_TASK_RUNTIME_BY_ID: dict[str, _TaskRuntime] = {}
_TASK_ID_BY_SUBMIT_ID: dict[str, str] = {}
_ACCOUNT_POOL_LOCK = threading.Lock()
_ACCOUNT_IN_USE: dict[str, str] = {}


def _safe_int(value: Any, default: int = 0) -> int:
    try:
        return int(value)
    except (TypeError, ValueError):
        return default


def _sanitize_token(text: Any, max_len: int = 64) -> str:
    s = str(text or "").strip()
    if not s:
        return ""
    s = re.sub(r"[^0-9A-Za-z_-]+", "_", s)
    s = re.sub(r"_+", "_", s).strip("_")
    if len(s) > max_len:
        s = s[:max_len].rstrip("_")
    return s


def _rotate_log_if_needed() -> None:
    try:
        if (not _LOG_FILE.exists()) or (_LOG_FILE.stat().st_size <= _LOG_ROTATE_BYTES):
            return
        ts = datetime.now().strftime("%Y%m%d_%H%M%S")
        rotated = plugin_dir / f"runwayml_plugin_debug_{ts}.log"
        try:
            os.replace(str(_LOG_FILE), str(rotated))
        except Exception:
            try:
                _LOG_FILE.write_text("", encoding="utf-8")
            except Exception:
                pass
    except Exception:
        pass


def _log(message: str, exc: Exception | None = None, level: str = "INFO") -> None:
    ts = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    lvl = str(level or "INFO").upper()
    tag = f"{_TASK_TAG} " if _TASK_TAG else ""
    line = f"[{ts}][{lvl}] {tag}{message}"
    if exc is not None:
        line += f" | EXC: {type(exc).__name__}: {exc}"
    try:
        _rotate_log_if_needed()
        with open(_LOG_FILE, "a", encoding="utf-8") as f:
            f.write(line + "\n")
    except Exception:
        pass
    try:
        print(line, flush=True)
    except Exception:
        pass


def _log_exc(message: str) -> None:
    try:
        tb = traceback.format_exc()
    except Exception:
        tb = ""
    _log(message, level="ERROR")
    if tb:
        for line in tb.splitlines():
            _log(line, level="ERROR")


def _set_task_tag(context: dict) -> str:
    global _TASK_TAG
    old = _TASK_TAG
    try:
        viewer_index = _safe_int(context.get("viewer_index"), 0)
        unique_name = str(context.get("unique_name") or context.get("unique_id") or "").strip()
        unique_name = re.sub(r"[^0-9A-Za-z_-]+", "_", unique_name)[:24].strip("_")
        generation_round = _safe_int(context.get("generation_round"), 0)
        output_position = context.get("output_position")
        position = 0
        if isinstance(output_position, list) and output_position:
            position = _safe_int(output_position[0], 0)
        elif output_position is not None:
            position = _safe_int(output_position, 0)
        _TASK_TAG = f"[{viewer_index:04d}_{unique_name or 'task'}_{generation_round}_{position}]"
    except Exception:
        _TASK_TAG = "[task]"
    return old


def _mask_secret(value: str, keep: int = 6) -> str:
    if not value:
        return ""
    s = str(value)
    if len(s) <= keep * 2:
        return "*" * len(s)
    return f"{s[:keep]}...{s[-keep:]}"


def _safe_progress(context: dict, message: str, progress: int | None = None) -> None:
    if message:
        for prefix in ("Playwright: ", "RunwayML API: ", "RunwayML: "):
            if message.startswith(prefix):
                message = message[len(prefix):]
                break

    cb = context.get("progress_callback")
    if not cb:
        return
    try:
        if progress is None:
            cb(message)
            return
        try:
            cb(message, int(progress))
        except TypeError:
            cb(message)
    except Exception as exc:
        _log(f"progress callback failed: {exc}")


def _dismiss_promotional_popups(page: Any, progress_card: Any = None) -> None:
    """
    Detects and dismisses various promotional popups and modal windows
    that might appear on runwayml.com (e.g. 'Earn credits with quests', 'What's new', etc.)
    without relying on arbitrary double clicks.
    """
    if not page:
        return
    try:
        if page.is_closed():
            return
    except Exception:
        return

    popups = [
        {
            "name": "Earn credits with quests panel",
            "detect": "div:has-text('Earn credits with quests')",
            "close": [
                "div:has-text('Earn credits with quests') button:has(svg)",
                "div:has-text('Earn credits with quests') button",
                "div:has-text('Earn credits with quests') [class*='close' i]",
                "div:has-text('Earn credits with quests') svg",
                "div:has-text('Earn credits with quests') [role='button']",
            ]
        },
        {
            "name": "What's new / release notes",
            "detect": 'div:has-text("What\'s new")',
            "close": [
                'div:has-text("What\'s new") button:has(svg)',
                'div:has-text("What\'s new") button',
                'div:has-text("What\'s new") [class*="close" i]',
            ]
        },
        {
            "name": "General promotional overlay",
            "detect": "[class*='Modal' i]",
            "close": [
                "[class*='Modal' i] button[class*='close' i]",
                "[class*='Modal' i] [class*='close' i]",
                "button[aria-label*='close' i]",
            ]
        },
        {
            "name": "Standard popover / dialog",
            "detect": "[role='dialog']",
            "close": [
                "[role='dialog'] button[aria-label*='close' i]",
                "[role='dialog'] [class*='close' i]",
                "[role='dialog'] button",
            ]
        }
    ]

    for item in popups:
        try:
            detector = page.locator(item["detect"]).first
            if detector.is_visible(timeout=100):
                _log(f"playwright: POPUP DETECTED - {item['name']}")
                clicked = False
                for close_sel in item["close"]:
                    try:
                        btn = page.locator(close_sel).first
                        if btn.is_visible(timeout=100):
                            _log(f"playwright: attempting to click close selector: {close_sel}")
                            btn.click(timeout=1000)
                            page.wait_for_timeout(500)
                            clicked = True
                            break
                    except Exception:
                        pass
                
                if not clicked:
                    try:
                        x_btn = detector.locator("button, [role='button'], svg").all()
                        for el in x_btn:
                            try:
                                if el.is_visible(timeout=100):
                                    txt = el.inner_text().strip().lower()
                                    aria = str(el.get_attribute("aria-label") or "").lower()
                                    cls = str(el.get_attribute("class") or "").lower()
                                    if txt == "x" or "close" in aria or "close" in cls or "dismiss" in aria or el.locator("svg").count() > 0:
                                        _log(f"playwright: fallback clicking close element with class={cls} aria={aria}")
                                        el.click(timeout=1000)
                                        page.wait_for_timeout(500)
                                        clicked = True
                                        break
                            except Exception:
                                pass
                    except Exception:
                        pass
                
                if clicked:
                    _log(f"playwright: POPUP DISMISSED - {item['name']}")
                    if progress_card:
                        progress_card.update(
                            f"拦截到推广弹窗并无情拒绝！🙅‍♂️ 继续冲！({item['name'][:24]})",
                            "info",
                            f"🛡️ 拦截成功 | {progress_card.account_label}"
                        )
        except Exception as e:
            _log(f"playwright: error during popup dismissal of {item['name']}: {e}", level="WARN")




def _is_page_settled(page: Any) -> bool:
    try:
        if (page.locator('[data-testid="select-base-model"]').first.is_visible(timeout=100) or
            page.locator('[role="textbox"]').first.is_visible(timeout=100) or
            page.locator('textarea').first.is_visible(timeout=100) or
            page.locator('button[aria-label="Reference"]').first.is_visible(timeout=100) or
            page.locator('button:has-text("Generate"), button[class*="generate" i]').first.is_visible(timeout=100) or
            page.locator('[placeholder*="Describe" i]').first.is_visible(timeout=100) or
            page.locator('[class*="editor" i]').first.is_visible(timeout=100)):
            return True
    except Exception:
        pass
    return False

def _check_policy_violation(page: Any) -> None:
    """
    Checks only action-level visible errors for prompt/usage policy violations.
    Historical generation cards may contain old failed messages, so they must not
    be used to fail the current running task.
    """
    err_text = _read_prompt_policy_error(page)
    if err_text:
        raise Exception(f"PLUGIN_ERROR:::提示词违规被拦截: {err_text}")


def _read_prompt_policy_error(page: Any) -> str:
    if not page:
        return ""
    try:
        if page.is_closed():
            return ""
    except Exception:
        return ""

    try:
        # Look only for visible toast/dialog/alert errors. Do not scan generic
        # cards/assets/previews, because Runway keeps old failed cards on screen.
        error_selectors = [
            '[class*="toast" i][class*="error" i]',
            '[class*="error" i][class*="message" i]',
            '[role="alert"]',
            '[class*="Modal" i]',
            '[class*="modal" i]',
            '[class*="dialog" i]',
        ]
        for sel in error_selectors:
            try:
                locs = page.locator(sel).all()
                for loc in locs:
                    if loc.is_visible(timeout=100):
                        txt = loc.inner_text().strip()
                        if not txt:
                            continue
                        if _is_runway_technical_glitch(txt):
                            _log(f"playwright: Runway technical glitch observed, not treating as prompt policy: {txt[:180]}", level="WARN")
                            continue
                        if _contains_prompt_policy_signal(txt):
                            return txt
            except Exception as e:
                continue

    except Exception as exc:
        _log(f"playwright: policy error scan failed: {exc}", level="DEBUG")
    return ""


def _read_runway_technical_glitch(page: Any) -> str:
    if not page:
        return ""
    try:
        if page.is_closed():
            return ""
    except Exception:
        return ""

    try:
        # Same action-level surfaces as policy checks. Avoid generation history/cards.
        error_selectors = [
            '[class*="toast" i][class*="error" i]',
            '[class*="error" i][class*="message" i]',
            '[role="alert"]',
            '[class*="Modal" i]',
            '[class*="modal" i]',
            '[class*="dialog" i]',
        ]
        for sel in error_selectors:
            try:
                locs = page.locator(sel).all()
                for loc in locs:
                    if loc.is_visible(timeout=100):
                        txt = loc.inner_text().strip()
                        if txt and _is_runway_technical_glitch(txt):
                            return txt
            except Exception:
                continue
    except Exception as exc:
        _log(f"playwright: technical glitch scan failed: {exc}", level="DEBUG")
    return ""


def _page_has_generation_activity(page: Any) -> bool:
    if not page:
        return False
    try:
        if page.is_closed():
            return False
    except Exception:
        return False
    active_selectors = [
        'text=/queued|processing|generating|rendering|in progress|排队|生成中|渲染中|处理中/i',
        '[class*="progress" i]',
        '[class*="percent" i]',
        '[data-testid*="progress" i]',
        '[role="progressbar"]',
    ]
    for sel in active_selectors:
        try:
            locs = page.locator(sel).all()
            for loc in locs[:8]:
                try:
                    if loc.is_visible(timeout=100):
                        return True
                except Exception:
                    continue
        except Exception:
            continue
    return False


def _extract_runway_task_id(body: Any) -> str:
    if not isinstance(body, dict):
        return ""
    direct = body.get("id") or body.get("taskId") or body.get("task_id") or body.get("uuid")
    if direct:
        return str(direct)
    for key in ("task", "data", "result"):
        obj = body.get(key)
        if isinstance(obj, dict):
            tid = obj.get("id") or obj.get("taskId") or obj.get("task_id") or obj.get("uuid")
            if tid:
                return str(tid)
    return ""


def _extract_runway_task_status(body: Any) -> str:
    if not isinstance(body, dict):
        return ""
    for key in ("status", "state", "progressText"):
        value = body.get(key)
        if value:
            return str(value)
    for key in ("task", "data", "result"):
        obj = body.get(key)
        if isinstance(obj, dict):
            status = _extract_runway_task_status(obj)
            if status:
                return status
    return ""


def _extract_http_urls_from_body(value: Any) -> list[str]:
    found: list[str] = []

    def walk(item: Any) -> None:
        if isinstance(item, str):
            if item.startswith(("http://", "https://")):
                found.append(item)
            else:
                for match in re.findall(r"https?://[^\s\"'<>]+", item):
                    found.append(match.rstrip(").,;"))
        elif isinstance(item, list):
            for child in item:
                walk(child)
        elif isinstance(item, dict):
            for child in item.values():
                walk(child)

    walk(value)
    deduped: list[str] = []
    seen: set[str] = set()
    for url in found:
        if url and url not in seen:
            seen.add(url)
            deduped.append(url)
    return deduped


def _extract_runway_video_urls_from_body(body: Any) -> list[str]:
    urls = _extract_http_urls_from_body(body)
    likely: list[str] = []
    for url in urls:
        lower = url.lower()
        if (
            ".mp4" in lower
            or ".mov" in lower
            or ("runway-task-artifacts" in lower and not lower.split("?")[0].endswith((".jpg", ".jpeg", ".png", ".webp", ".gif")))
            or "download" in lower
        ):
            likely.append(url)
    return likely


def _body_mentions_task_ids(body: Any, task_ids: list[str]) -> bool:
    ids = [str(tid) for tid in task_ids if tid]
    if not ids:
        return False
    try:
        text = json.dumps(body, ensure_ascii=False)
    except Exception:
        text = str(body)
    return any(tid in text for tid in ids)


def _save_error_confirmation_screenshot(page: Any, prefix: str) -> None:
    try:
        ts = datetime.now().strftime("%Y%m%d_%H%M%S")
        safe_prefix = re.sub(r"[^0-9A-Za-z_-]+", "_", str(prefix or "error")).strip("_") or "error"
        out_png = str(plugin_dir / f"_debug_{safe_prefix}_{ts}.png")
        page.screenshot(path=out_png, full_page=True)
        _log(f"playwright: saved confirmed error screenshot: {out_png}", level="WARN")
    except Exception as exc:
        _log(f"playwright: failed to save confirmed error screenshot: {exc}", level="WARN")


def _confirm_policy_violation(page: Any, state: dict[str, Any], required_count: int = 3) -> None:
    err_text = _read_prompt_policy_error(page)
    if not err_text:
        state.clear()
        return
    if _page_has_generation_activity(page):
        _log(f"playwright: policy-like error ignored because page still shows active generation/queue: {err_text[:180]}", level="WARN")
        state.clear()
        return
    key = re.sub(r"\s+", " ", err_text.strip().lower())[:180]
    now = time.time()
    if state.get("key") == key:
        last_count_at = float(state.get("last_count_at") or 0)
        if last_count_at and now - last_count_at < _ERROR_CONFIRM_INTERVAL_SECONDS:
            return
        state["count"] = int(state.get("count") or 0) + 1
    else:
        state["key"] = key
        state["count"] = 1
        state["text"] = err_text
    state["last_count_at"] = now
    _log(f"playwright: policy-like error confirmation {state['count']}/{required_count}: {err_text[:180]}", level="WARN")
    if int(state.get("count") or 0) >= required_count:
        _save_error_confirmation_screenshot(page, "policy_confirm")
        raise Exception(f"PLUGIN_ERROR:::提示词违规被拦截: {state.get('text') or err_text}")


def _confirm_runway_technical_glitch(page: Any, state: dict[str, Any], required_count: int = 3, known_started: bool = False) -> None:
    err_text = _read_runway_technical_glitch(page)
    if not err_text:
        state.clear()
        return
    if known_started:
        _log(f"playwright: Runway technical glitch observed after generation already started; keeping browser alive and continuing: {err_text[:180]}", level="WARN")
        state.clear()
        return
    if _page_has_generation_activity(page):
        _log(f"playwright: Runway technical glitch ignored because page still shows active generation/queue: {err_text[:180]}", level="WARN")
        state.clear()
        return
    key = re.sub(r"\s+", " ", err_text.strip().lower())[:180]
    now = time.time()
    if state.get("key") == key:
        last_count_at = float(state.get("last_count_at") or 0)
        if last_count_at and now - last_count_at < _ERROR_CONFIRM_INTERVAL_SECONDS:
            return
        state["count"] = int(state.get("count") or 0) + 1
    else:
        state["key"] = key
        state["count"] = 1
        state["text"] = err_text
    state["last_count_at"] = now
    _log(f"playwright: technical glitch confirmation {state['count']}/{required_count}: {err_text[:180]}", level="WARN")
    if int(state.get("count") or 0) >= required_count:
        _save_error_confirmation_screenshot(page, "technical_glitch_confirm")
        _log("playwright: technical glitch confirmed but left in observe-only mode; continuing to wait for video/progress/timeout", level="WARN")
        state.clear()


def _get_site_profile(params: dict[str, Any] | None = None, context: dict[str, Any] | None = None) -> _SiteProfile:
    raw = ""
    if isinstance(params, dict):
        raw = str(params.get("site_profile") or "").strip().lower()
    if (not raw) and isinstance(context, dict):
        raw = str(context.get("site_profile") or "").strip().lower()
    if raw in _SITE_PROFILES:
        return _SITE_PROFILES[raw]
    return _SITE_PROFILES[_DEFAULT_SITE_PROFILE_KEY]


def _make_task_id(context: dict, site_profile: _SiteProfile) -> str:
    viewer_index = _safe_int(context.get("viewer_index"), 0)
    unique_name = _sanitize_token(context.get("unique_name") or context.get("unique_id") or "task", max_len=32) or "task"
    generation_round = _safe_int(context.get("generation_round"), 0)
    output_position = context.get("output_position")
    position = 0
    if isinstance(output_position, list) and output_position:
        position = _safe_int(output_position[0], 0)
    elif output_position is not None:
        position = _safe_int(output_position, 0)
    seed_src = f"{site_profile.key}|{viewer_index}|{unique_name}|{generation_round}|{position}|{time.time_ns()}"
    suffix = hashlib.sha1(seed_src.encode("utf-8", "ignore")).hexdigest()[:10]
    return f"{site_profile.key}_{viewer_index:04d}_{unique_name}_{generation_round}_{position}_{suffix}"


def _register_task_runtime(runtime: _TaskRuntime) -> None:
    with _TASK_RUNTIME_LOCK:
        existing = _TASK_RUNTIME_BY_ID.get(runtime.task_id)
        if existing is not None:
            raise Exception(f"PLUGIN_ERROR:::重复的 task_id: {runtime.task_id}")
        _TASK_RUNTIME_BY_ID[runtime.task_id] = runtime


def _update_task_runtime(task_id: str, **changes: Any) -> None:
    with _TASK_RUNTIME_LOCK:
        runtime = _TASK_RUNTIME_BY_ID.get(task_id)
        if not runtime:
            return
        for key, value in changes.items():
            if hasattr(runtime, key):
                setattr(runtime, key, value)


def _snapshot_task_runtime(task_id: str) -> dict[str, Any]:
    with _TASK_RUNTIME_LOCK:
        runtime = _TASK_RUNTIME_BY_ID.get(task_id)
        if not runtime:
            return {}
        return asdict(runtime)


def _release_task_runtime(task_id: str) -> None:
    with _TASK_RUNTIME_LOCK:
        _TASK_RUNTIME_BY_ID.pop(task_id, None)


def _normalize_account_entry(raw: Any, site_profile: _SiteProfile) -> dict[str, Any] | None:
    if isinstance(raw, str):
        raw = raw.strip()
        if not raw:
            return None
        if raw.startswith("#") or raw.startswith("//"):
            return None
        if raw.startswith("{"):
            try:
                parsed = json.loads(raw)
                if isinstance(parsed, dict):
                    return _normalize_account_entry(parsed, site_profile)
            except (json.JSONDecodeError, ValueError):
                pass
        sep = "----" if "----" in raw else "|"
        parts = [p.strip() for p in raw.split(sep)]
        if sep == "----" and len(parts) >= 2:
            alias = parts[0] if len(parts) >= 3 else ""
            email = parts[-2] if len(parts) >= 3 else parts[0]
            password = parts[-1] if len(parts) >= 3 else parts[1]
            if not alias:
                alias = email.split("@")[0] if "@" in email else email[:8]
            return {
                "api_key": "",
                "alias": alias,
                "email": email,
                "password": password,
                "paid_required": False,
                "success_done": False,
            }
        api_key = parts[0] if parts else raw
        alias = parts[1] if len(parts) > 1 else ""
        return {
            "api_key": api_key,
            "alias": alias or api_key[:8],
            "paid_required": False,
            "success_done": False,
        }
    if isinstance(raw, dict):
        api_key = str(raw.get("api_key") or raw.get("key") or raw.get("token") or "").strip()
        if not api_key:
            email = str(raw.get("email") or "").strip()
            password = str(raw.get("password") or raw.get("password_enc") or "").strip()
            if email and password:
                alias = str(raw.get("alias") or email.split("@")[0])
                return {
                    "api_key": "",
                    "alias": alias,
                    "email": email,
                    "password": password,
                    "paid_required": bool(raw.get("paid_required", False)),
                    "success_done": bool(raw.get("success_done", False)),
                }
            return None
        return {
            "api_key": api_key,
            "alias": str(raw.get("alias") or api_key[:8]),
            "paid_required": bool(raw.get("paid_required", False)),
            "success_done": bool(raw.get("success_done", False)),
        }
    return None


def _load_account_pool(params: dict[str, Any], site_profile: _SiteProfile) -> list[dict[str, Any]]:
    pool_path = _normalize_pool_path(params.get("account_pool_path") or account_pool_file)
    if not pool_path or not os.path.isfile(pool_path):
        return []
    try:
        with open(pool_path, "r", encoding="utf-8") as f:
            lines = f.readlines()
    except Exception:
        return []
    accounts: list[dict[str, Any]] = []
    for line in lines:
        entry = _normalize_account_entry(line, site_profile)
        if entry is not None:
            accounts.append(entry)
    return accounts


def _normalize_pool_path(path: Any) -> str:
    raw = str(path or "").strip().strip('"')
    if not raw:
        return ""
    try:
        return str(Path(raw).expanduser())
    except Exception:
        return raw


def _get_current_pool_path() -> str:
    return _normalize_pool_path(_GLOBAL_PARAMS.get("account_pool_path") or account_pool_file)


def _set_current_pool_path(path: Any, persist: bool = True) -> str:
    normalized = _normalize_pool_path(path)
    if not normalized:
        return _get_current_pool_path()
    _GLOBAL_PARAMS["account_pool_path"] = normalized
    if persist:
        try:
            update_plugin_param(_PLUGIN_FILE, "account_pool_path", normalized)
        except Exception:
            pass
    return normalized


def _apply_action_pool_path(data: Any) -> str:
    if isinstance(data, dict):
        raw_path = data.get("account_pool_path") or data.get("pool_path")
        if raw_path:
            return _set_current_pool_path(raw_path, persist=True)
    return _get_current_pool_path()


def _has_active_browser_or_scheduler_work() -> bool:
    try:
        if _TASK_SCHEDULER.running_count > 0 or _TASK_SCHEDULER.queued_count > 0:
            return True
    except Exception:
        pass
    try:
        with _BROWSER_POOL._lock:
            for slot in _BROWSER_POOL._slots.values():
                if slot.is_alive and slot.is_busy:
                    return True
    except Exception:
        pass
    return False


def _safe_reload_accounts(reason: str = "") -> tuple[int, bool, str]:
    site_profile = _get_site_profile(params=_GLOBAL_PARAMS)
    if _has_active_browser_or_scheduler_work():
        msg = "当前有任务或浏览器正在运行，账号池文件已保存，但暂不重载账号管理器，避免影响正在执行的任务。"
        if reason:
            _log(f"AccountManager: deferred reload ({reason}) because active work exists", level="WARN")
        with _ACCOUNT_MGR._lock:
            return len(_ACCOUNT_MGR._slots), False, msg
    total = _ACCOUNT_MGR.force_reload(_GLOBAL_PARAMS, site_profile)
    return total, True, "账号池已重新加载"


def _parse_pool_line(line: str) -> dict[str, Any] | None:
    raw = line.strip()
    if not raw or raw.startswith("#") or raw.startswith("//"):
        return None
    return _normalize_account_entry(raw, _get_site_profile())



def _read_all_accounts_from_file() -> list[dict[str, Any]]:
    path = _get_current_pool_path()
    if not path or not os.path.isfile(path):
        return []
    try:
        with open(path, "r", encoding="utf-8") as f:
            results = []
            for line in f:
                entry = _parse_pool_line(line)
                if entry and (entry.get("email") or entry.get("api_key")):
                    results.append(entry)
            return results
    except Exception as e:
        _log(f"read pool file error: {e}", level="ERROR")
        return []


def _add_account_to_pool_file(email: str, password: str) -> tuple[bool, str]:
    path = _get_current_pool_path()
    if not path:
        return False, "请先设置账号池文件路径"
    email = str(email or "").strip()
    password = str(password or "").strip()
    if not email or not password:
        return False, "邮箱和密码不能为空"
    alias = email.split("@")[0] if "@" in email else email
    existing = _read_all_accounts_from_file()
    for acc in existing:
        existing_email = str(acc.get("email") or "").strip().lower()
        if existing_email == email.strip().lower():
            return False, f"邮箱 '{email}' 已存在于账号池文件中"
    try:
        os.makedirs(os.path.dirname(path) or ".", exist_ok=True)
        needs_newline = os.path.isfile(path) and os.path.getsize(path) > 0
        with open(path, "a", encoding="utf-8") as f:
            if needs_newline:
                f.write("\n")
            f.write(f"{email}----{password}")
        _log(f"added account to pool file: {alias} ({email})")
        return True, f"账号 {email} 已写入账号池"
    except Exception as e:
        _log(f"write pool file error: {e}", level="ERROR")
        return False, f"写入账号池失败: {e}"


def _remove_account_from_pool_file(alias_or_email: str) -> tuple[bool, str]:
    path = _get_current_pool_path()
    if not path or not os.path.isfile(path):
        return False, "账号池文件不存在"
    target = alias_or_email.strip().lower()
    target_key = re.sub(r"[^0-9a-zA-Z@._-]+", "", target).lower()
    try:
        with open(path, "r", encoding="utf-8") as f:
            lines = f.readlines()
        removed = False
        new_lines = []
        for line in lines:
            entry = _parse_pool_line(line)
            if entry is None:
                new_lines.append(line)
                continue
            line_email = str(entry.get("email") or "").strip().lower()
            line_alias = str(entry.get("alias") or "").strip().lower()
            line_prefix = line_email.split("@")[0] if "@" in line_email else ""
            candidates = {
                line_email,
                line_alias,
                line_prefix,
                re.sub(r"[^0-9a-zA-Z@._-]+", "", line_email).lower(),
                re.sub(r"[^0-9a-zA-Z@._-]+", "", line_alias).lower(),
                re.sub(r"[^0-9a-zA-Z@._-]+", "", line_prefix).lower(),
            }
            if target in candidates or target_key in candidates:
                removed = True
                continue
            new_lines.append(line)
        if not removed:
            return False, f"未找到账号 '{alias_or_email}'"
        with open(path, "w", encoding="utf-8") as f:
            f.writelines(new_lines)
        _log(f"removed account from pool file: {alias_or_email}")
        return True, f"账号 {alias_or_email} 已从账号池删除"
    except Exception as e:
        _log(f"remove from pool file error: {e}", level="ERROR")
        return False, f"删除账号失败: {e}"


def _acquire_account_record(params: dict[str, Any], site_profile: _SiteProfile, worker_id: str) -> dict[str, Any] | None:
    accounts = _load_account_pool(params, site_profile)
    if not accounts:
        api_key = str(params.get("api_key") or "").strip()
        if api_key:
            return _normalize_account_entry({"api_key": api_key, "alias": "direct_key"}, site_profile)
        return None
    with _ACCOUNT_POOL_LOCK:
        for account in accounts:
            key = str(account.get("api_key") or "")
            if not key:
                continue
            if key in _ACCOUNT_IN_USE:
                continue
            if account.get("paid_required") and not params.get("use_paid_accounts", False):
                continue
            _ACCOUNT_IN_USE[key] = worker_id
            return account
    return None


def _release_account_record(account: dict[str, Any] | None) -> None:
    if account is None:
        return
    key = str(account.get("api_key") or "")
    if not key:
        return
    with _ACCOUNT_POOL_LOCK:
        _ACCOUNT_IN_USE.pop(key, None)


def _extract_prompt_text(context: dict[str, Any]) -> tuple[str, str]:
    prompt = str(context.get("prompt") or context.get("text") or "").strip()
    source = ""
    if prompt:
        source = "context.prompt"
    if not prompt:
        prompt = str(context.get("negative_prompt") or "").strip()
        if prompt:
            source = "context.negative_prompt"
    return prompt, source


def _parse_prompt_override_params(prompt: str) -> tuple[str, str | None, int | None]:
    ratio_override = None
    duration_override = None
    
    # Match any bracket block: 【...】 or [...] or {...} or (...)
    pattern = r'([【\[\{\(])([^】\]\}\)]+?)[】\]\}\)]'
    matches = list(re.finditer(pattern, prompt))
    if not matches:
        return prompt, ratio_override, duration_override
        
    for match in reversed(matches):
        block_text = match.group(2)
        
        # Validate if this block is strictly a parameter block
        # Step 1: Remove all digits, spaces, and punctuation (both EN and CN, and custom separators like pipes)
        cleaned = re.sub(r'[0-9\s:,，：\.\-\_sS/\\*#;；\|]', '', block_text)
        
        # Step 2: Remove known parameter keywords
        allowed_keywords = ['画幅', '比例', '时长', '时间', '秒', 'ratio', 'aspect', 'duration']
        for kw in allowed_keywords:
            cleaned = cleaned.replace(kw, '')
            
        # If there are other characters left, it is descriptive prompt content, not a parameter block!
        if cleaned.strip():
            # Skip this bracket block and look for others
            continue
            
        has_param = False
        
        # 1. Parse ratio: e.g. 16:9, 9:16, 1:1, etc.
        ratio_m = re.search(r'([0-9]+\s*[:：]\s*[0-9]+)', block_text)
        temp_text = block_text
        if ratio_m:
            ratio_override = ratio_m.group(1).replace('：', ':').replace(' ', '')
            has_param = True
            temp_text = temp_text.replace(ratio_m.group(0), '')
            
        # 2. Parse duration: e.g. 时长: 15, 15秒, 5s, 10S
        dur_m1 = re.search(r'(?:时长|时间)\s*[:：]?\s*([0-9]+)', temp_text)
        if dur_m1:
            duration_override = int(dur_m1.group(1))
            has_param = True
        else:
            dur_m2 = re.search(r'([0-9]+)\s*(?:秒|[sS])', temp_text)
            if dur_m2:
                duration_override = int(dur_m2.group(1))
                has_param = True
            elif ratio_override and re.search(r'^\s*[,，]?\s*([0-9]+)\s*$', temp_text):
                dur_m3 = re.search(r'([0-9]+)', temp_text)
                if dur_m3:
                    duration_override = int(dur_m3.group(1))
                    has_param = True
                    
        if has_param:
            start, end = match.span()
            prompt = (prompt[:start] + prompt[end:]).strip()
            # Only process the last matching parameter block to avoid multiple removals
            break
            
    return prompt, ratio_override, duration_override


def _norm_path(v: Any) -> str | None:
    if not v:
        return None
    s = str(v).strip()
    if not s:
        return None
    s = os.path.expandvars(os.path.expanduser(s))
    if s.startswith("file://"):
        s = s[7:]
    s = os.path.abspath(s)
    return s if os.path.exists(s) else None


def _guess_mime_type(path: str) -> str:
    ext = os.path.splitext(path)[1].lower()
    mime_map = {
        ".png": "image/png",
        ".jpg": "image/jpeg",
        ".jpeg": "image/jpeg",
        ".webp": "image/webp",
        ".gif": "image/gif",
        ".mp4": "video/mp4",
        ".mov": "video/quicktime",
        ".avi": "video/x-msvideo",
    }
    return mime_map.get(ext, "application/octet-stream")


def _file_to_data_url(path: str) -> str:
    mime = _guess_mime_type(path)
    with open(path, "rb") as f:
        data = f.read()
    encoded = base64.b64encode(data).decode("ascii")
    return f"data:{mime};base64,{encoded}"


def _image_to_public_url(path: str, api_key: str, api_base: str) -> str | None:
    if path.startswith(("http://", "https://")):
        return path
    if path.startswith("runway://"):
        return path
    mime = _guess_mime_type(path)
    filename = os.path.basename(path)
    try:
        init_resp = requests.post(
            f"{api_base}/uploads",
            headers={
                "Authorization": f"Bearer {api_key}",
                "Content-Type": "application/json",
                "Accept": "application/json",
                "X-Runway-Version": RUNWAYML_API_VERSION,
            },
            json={
                "filename": filename,
                "type": "ephemeral",
            },
            timeout=60,
        )
        init_resp.raise_for_status()
        init_data = init_resp.json()
        upload_url = init_data.get("uploadUrl") or init_data.get("upload_url")
        fields = init_data.get("fields") or {}
        runway_uri = init_data.get("runwayUri") or init_data.get("runway_uri")
        if not upload_url:
            _log(f"upload: no uploadUrl in response: {init_data}", level="WARN")
            return None
        with open(path, "rb") as f:
            file_data = f.read()
        multipart_fields = dict(fields)
        multipart_fields["file"] = (filename, file_data, mime)
        put_resp = requests.post(
            upload_url,
            files=multipart_fields,
            timeout=120,
        )
        put_resp.raise_for_status()
        if runway_uri:
            _log(f"upload: ephemeral upload success: {runway_uri}")
            return runway_uri
        _log(f"upload: upload completed but no runwayUri returned", level="WARN")
        return None
    except Exception as exc:
        _log(f"upload: failed to upload {path}: {exc}", level="WARN")
        return None


class RunwayMLClient:
    def __init__(self, api_key: str, api_base: str = RUNWAYML_API_BASE):
        self.api_key = api_key
        self.api_base = api_base.rstrip("/")
        self.session = requests.Session()
        self.session.headers.update({
            "Authorization": f"Bearer {self.api_key}",
            "Content-Type": "application/json",
            "Accept": "application/json",
            "X-Runway-Version": RUNWAYML_API_VERSION,
            "User-Agent": "RunwayML-Plugin/1.0",
        })

    def _request(self, method: str, endpoint: str, **kwargs) -> requests.Response:
        url = f"{self.api_base}/{endpoint.lstrip('/')}"
        kwargs.setdefault("timeout", 60)
        resp = self.session.request(method, url, **kwargs)
        return resp

    def create_image_to_video(
        self,
        prompt_image: str | list[dict[str, str]],
        prompt_text: str = "",
        model: str = "gen4_turbo",
        duration: int = 5,
        ratio: str = "1280:720",
        seed: int | None = None,
        content_moderation: dict[str, Any] | None = None,
    ) -> dict[str, Any]:
        payload: dict[str, Any] = {
            "model": model,
            "promptText": prompt_text or " ",
            "duration": duration,
            "ratio": ratio,
        }
        if isinstance(prompt_image, str):
            payload["promptImage"] = prompt_image
        elif isinstance(prompt_image, list):
            payload["promptImage"] = prompt_image
        if seed is not None:
            payload["seed"] = seed
        if content_moderation:
            payload["contentModeration"] = content_moderation
        resp = self._request("POST", "/image_to_video", json=payload)
        resp.raise_for_status()
        return resp.json()

    def create_text_to_video(
        self,
        prompt_text: str,
        model: str = "gen4.5",
        duration: int = 5,
        ratio: str = "1280:720",
        seed: int | None = None,
        content_moderation: dict[str, Any] | None = None,
    ) -> dict[str, Any]:
        payload: dict[str, Any] = {
            "model": model,
            "promptText": prompt_text,
            "duration": duration,
            "ratio": ratio,
        }
        if seed is not None:
            payload["seed"] = seed
        if content_moderation:
            payload["contentModeration"] = content_moderation
        resp = self._request("POST", "/text_to_video", json=payload)
        resp.raise_for_status()
        return resp.json()

    def create_video_to_video(
        self,
        video_uri: str,
        prompt_text: str = "",
        model: str = "gen4_aleph",
        seed: int | None = None,
        references: list[dict[str, str]] | None = None,
        content_moderation: dict[str, Any] | None = None,
    ) -> dict[str, Any]:
        payload: dict[str, Any] = {
            "model": model,
            "videoUri": video_uri,
            "promptText": prompt_text or " ",
        }
        if seed is not None:
            payload["seed"] = seed
        if references:
            payload["references"] = references
        if content_moderation:
            payload["contentModeration"] = content_moderation
        resp = self._request("POST", "/video_to_video", json=payload)
        resp.raise_for_status()
        return resp.json()

    def create_text_to_image(
        self,
        prompt_text: str,
        model: str = "gen4_image",
        ratio: str = "1360:768",
        reference_images: list[dict[str, str]] | None = None,
        seed: int | None = None,
        content_moderation: dict[str, Any] | None = None,
    ) -> dict[str, Any]:
        payload: dict[str, Any] = {
            "model": model,
            "promptText": prompt_text,
            "ratio": ratio,
        }
        if reference_images:
            payload["referenceImages"] = reference_images
        if seed is not None:
            payload["seed"] = seed
        if content_moderation:
            payload["contentModeration"] = content_moderation
        resp = self._request("POST", "/text_to_image", json=payload)
        resp.raise_for_status()
        return resp.json()

    def create_character_performance(
        self,
        character: dict[str, str],
        performance_video: str,
        model: str = "act_two",
        seed: int | None = None,
    ) -> dict[str, Any]:
        payload: dict[str, Any] = {
            "model": model,
            "character": character,
            "performanceVideo": performance_video,
        }
        if seed is not None:
            payload["seed"] = seed
        resp = self._request("POST", "/character_performance", json=payload)
        resp.raise_for_status()
        return resp.json()

    def get_task(self, task_id: str) -> dict[str, Any]:
        resp = self._request("GET", f"/tasks/{task_id}")
        resp.raise_for_status()
        return resp.json()

    def delete_task(self, task_id: str) -> dict[str, Any]:
        resp = self._request("DELETE", f"/tasks/{task_id}")
        resp.raise_for_status()
        return resp.json()

    def poll_task_until_complete(
        self,
        task_id: str,
        timeout_s: int = 900,
        poll_interval_s: float = 5.0,
        progress_callback: Any = None,
    ) -> dict[str, Any]:
        deadline = time.time() + max(30, timeout_s)
        last_status = None
        while time.time() < deadline:
            try:
                task = self.get_task(task_id)
            except Exception as exc:
                _log(f"poll: get_task failed for {task_id}: {exc}", level="WARN")
                time.sleep(poll_interval_s)
                continue
            status = str(task.get("status") or "").strip().lower()
            if status != last_status:
                _log(f"poll: task {task_id} status: {status}")
                last_status = status
            if status in ("succeeded", "complete", "completed", "done"):
                if progress_callback:
                    try:
                        progress_callback("生成完成", 100)
                    except Exception:
                        pass
                return task
            if status in ("failed", "error", "cancelled", "canceled"):
                error_msg = task.get("error") or task.get("failure") or task.get("message") or "任务失败"
                raise Exception(f"PLUGIN_ERROR:::RunwayML 任务失败: {error_msg} (status={status})")
            if status in ("running", "processing", "in_progress", "pending", "queued", "queueing"):
                progress = task.get("progress")
                pct = None
                if isinstance(progress, (int, float)):
                    if 0.0 < progress <= 1.0:
                        pct = int(progress * 100)
                    elif progress > 1.0:
                        pct = int(progress)
                if pct is not None:
                    pct = min(99, max(1, pct))
                    if progress_callback:
                        try:
                            progress_callback("生成中", pct)
                        except Exception:
                            pass
                elif progress_callback:
                    try:
                        if status in ("queued", "queueing"):
                            progress_callback("排队中", 10)
                        else:
                            progress_callback("生成中", 50)
                    except Exception:
                        pass
            time.sleep(poll_interval_s)
        raise Exception(f"PLUGIN_ERROR:::RunwayML 任务超时: task_id={task_id} timeout={timeout_s}s")

    def upload_file(self, file_path: str) -> str | None:
        return _image_to_public_url(file_path, self.api_key, self.api_base)


def _generate_via_api(
    context: dict,
    params: dict[str, Any],
    prompt: str,
    first_path: str | None,
    end_path: str | None,
    video_path: str | None,
    model: str,
    duration_s: int,
    ratio: str,
    timeout_s: int,
    seed: int | None,
    api_key: str,
    api_base: str,
    generation_type: str = "image_to_video",
) -> str:
    client = RunwayMLClient(api_key, api_base)
    task_id = str(context.get("task_id") or "").strip()

    def _progress(msg: str, pct: int | None = None) -> None:
        _safe_progress(context, msg, pct)

    _progress("RunwayML API: 准备上传资源")

    prompt_images: list[dict[str, str]] = []
    if first_path:
        _progress("RunwayML API: 上传首帧图片")
        first_url = client.upload_file(first_path)
        if not first_url:
            if first_path.startswith(("http://", "https://", "runway://")):
                first_url = first_path
            else:
                raise Exception(f"PLUGIN_ERROR:::首帧图片上传失败: {first_path}")
        prompt_images.append({"uri": first_url, "position": "first"})
        _log(f"API: first frame uploaded: {_mask_secret(first_url, 10)}")

    if end_path:
        _progress("RunwayML API: 上传尾帧图片")
        end_url = client.upload_file(end_path)
        if not end_url:
            if end_path.startswith(("http://", "https://", "runway://")):
                end_url = end_path
            else:
                raise Exception(f"PLUGIN_ERROR:::尾帧图片上传失败: {end_path}")
        prompt_images.append({"uri": end_url, "position": "last"})
        _log(f"API: end frame uploaded: {_mask_secret(end_url, 10)}")

    _progress("RunwayML API: 创建生成任务")

    result: dict[str, Any]

    if generation_type == "character_performance":
        _progress("RunwayML API: 上传角色图片和表演视频")
        character_url = client.upload_file(first_path) if first_path else None
        if not character_url and first_path:
            if first_path.startswith(("http://", "https://", "runway://")):
                character_url = first_path
        if not character_url:
            raise Exception(f"PLUGIN_ERROR:::角色图片上传失败: {first_path}")
        performance_url = client.upload_file(video_path) if video_path else None
        if not performance_url and video_path:
            if video_path.startswith(("http://", "https://", "runway://")):
                performance_url = video_path
        if not performance_url:
            raise Exception(f"PLUGIN_ERROR:::表演视频上传失败: {video_path}")
        result = client.create_character_performance(
            character={"uri": character_url},
            performance_video=performance_url,
            model=model,
            seed=seed,
        )
    elif generation_type == "text_to_image":
        if not prompt:
            raise Exception("PLUGIN_ERROR:::text_to_image 模式需要提供提示词")
        ref_images: list[dict[str, str]] | None = None
        if prompt_images:
            ref_images = [{"uri": img["uri"], "tag": img.get("tag", f"ref{i}")} for i, img in enumerate(prompt_images)]
        result = client.create_text_to_image(
            prompt_text=prompt,
            model=model,
            ratio=ratio,
            reference_images=ref_images,
            seed=seed,
        )
    elif video_path:
        _progress("RunwayML API: 上传参考视频")
        video_url = client.upload_file(video_path)
        if not video_url:
            if video_path.startswith(("http://", "https://", "runway://")):
                video_url = video_path
            else:
                raise Exception(f"PLUGIN_ERROR:::参考视频上传失败: {video_path}")
        result = client.create_video_to_video(
            video_uri=video_url,
            prompt_text=prompt,
            model=model,
            seed=seed,
        )
    elif prompt_images:
        result = client.create_image_to_video(
            prompt_image=prompt_images if len(prompt_images) > 1 else prompt_images[0]["uri"],
            prompt_text=prompt,
            model=model,
            duration=duration_s,
            ratio=ratio,
            seed=seed,
        )
    else:
        if not prompt:
            raise Exception("PLUGIN_ERROR:::文生视频模式需要提供提示词")
        result = client.create_text_to_video(
            prompt_text=prompt,
            model=model,
            duration=duration_s,
            ratio=ratio,
            seed=seed,
        )

    runway_task_id = str(result.get("id") or "").strip()
    if not runway_task_id:
        raise Exception(f"PLUGIN_ERROR:::RunwayML 创建任务失败: {result}")
    _log(f"API: task created: {runway_task_id}")

    if task_id:
        _update_task_runtime(task_id, submit_id=runway_task_id, status="generating")
    context["submit_id"] = runway_task_id

    _progress("RunwayML API: 等待生成结果")
    completed = client.poll_task_until_complete(
        runway_task_id,
        timeout_s=timeout_s,
        poll_interval_s=5.0,
        progress_callback=_progress,
    )

    output_list = completed.get("output") or []
    video_url = None
    if isinstance(output_list, list) and output_list:
        for item in output_list:
            if isinstance(item, list) and len(item) >= 1:
                candidate = str(item[0]).strip()
                if candidate.startswith("http"):
                    video_url = candidate
                    break
            elif isinstance(item, str) and item.startswith("http"):
                video_url = item
                break
    if not video_url:
        artifacts = completed.get("artifacts") or []
        if isinstance(artifacts, list) and artifacts:
            for artifact in artifacts:
                if isinstance(artifact, dict):
                    url = artifact.get("url") or artifact.get("src") or ""
                    if url.startswith("http"):
                        video_url = url
                        break
    if not video_url:
        video_url = completed.get("video_url") or completed.get("url") or ""
    if not video_url or not str(video_url).startswith("http"):
        raise Exception(f"PLUGIN_ERROR:::RunwayML 任务完成但未获取到视频URL: {completed}")

    _log(f"API: video url: {_mask_secret(str(video_url), 15)}")
    return str(video_url)


# ═══════════════════════════════════════════════════════════════════════════════
# Module 1: Account Manager — 多账号管理，并发任务数限制，轮询分配
# ═══════════════════════════════════════════════════════════════════════════════

_MAX_CONCURRENT_PER_ACCOUNT = 2
_ACCOUNT_COOLDOWN_SECONDS = 60


@dataclass
class _AccountSlot:
    alias: str
    api_key: str
    email: str = ""
    password_enc: str = ""
    cookie_header: str = ""
    storage_state_path: str = ""
    active_tasks: int = 0
    total_tasks: int = 0
    failed_tasks: int = 0
    last_used_ts: float = 0.0
    last_error_ts: float = 0.0
    last_error_msg: str = ""
    cooldown_until: float = 0.0
    is_premium: bool = False
    team_name: str = ""
    disabled: bool = False
    interactive_task_id: str | None = None

    @property
    def available_slots(self) -> int:
        return max(0, _MAX_CONCURRENT_PER_ACCOUNT - self.active_tasks)

    @property
    def is_available(self) -> bool:
        if self.disabled:
            return False
        if self.cooldown_until > time.time():
            return False
        return True


class _AccountManager:
    def __init__(self) -> None:
        self._lock = threading.RLock()
        self._slots: dict[str, _AccountSlot] = {}
        self._key_to_alias: dict[str, str] = {}
        self._round_robin_idx: int = 0

    def load_from_pool(self, params: dict[str, Any], site_profile: _SiteProfile) -> int:
        accounts = _load_account_pool(params, site_profile)
        api_key_direct = str(params.get("api_key") or "").strip()
        if api_key_direct and not any(a.get("api_key") == api_key_direct for a in accounts):
            accounts.append({"api_key": api_key_direct, "alias": "direct_key"})
        if not accounts and not self._slots:
            return 0
        with self._lock:
            if self._slots:
                self._apply_disabled_state()
                return len(self._slots)
            self._slots.clear()
            self._key_to_alias.clear()
            for raw in accounts:
                key = str(raw.get("api_key") or "").strip()
                email = str(raw.get("email") or "").strip()
                password = str(raw.get("password_enc") or raw.get("password") or "").strip()
                if not key and not (email and password):
                    continue
                alias = str(raw.get("alias") or key[:8] or email.split("@")[0] if email else "")
                if not alias:
                    continue
                slot = _AccountSlot(
                    alias=alias,
                    api_key=key,
                    email=email,
                    password_enc=password,
                    cookie_header=str(raw.get("cookie_header") or raw.get("cookie") or "").strip(),
                    storage_state_path=str(raw.get("storage_state_path") or raw.get("storage_state") or "").strip(),
                    is_premium=bool(raw.get("is_premium") or raw.get("paid_required") or False),
                )
                self._slots[alias] = slot
                if key:
                    self._key_to_alias[key] = alias
            self._apply_disabled_state()
            self._round_robin_idx = 0
        _log(f"AccountManager: loaded {len(self._slots)} accounts from pool")
        return len(self._slots)

    def load_from_vault(self) -> int:
        aliases = _CREDENTIAL_VAULT.list_aliases()
        if not aliases:
            _log("AccountManager: no credentials in vault")
            return 0
        added = 0
        updated = 0
        with self._lock:
            for alias in aliases:
                cred = _CREDENTIAL_VAULT.get_credential(alias)
                if not cred or not cred.get("email") or not cred.get("password"):
                    _log(f"AccountManager: vault alias '{alias}' missing email/password, skipping", level="WARN")
                    continue
                storage_dir = str(DATA_DIR / "storage_states") if DATA_DIR.exists() else ""
                state_path = ""
                if storage_dir:
                    candidate = os.path.join(storage_dir, f"{alias}_state.json")
                    if os.path.isfile(candidate):
                        state_path = candidate
                if alias in self._slots:
                    existing = self._slots[alias]
                    existing.email = cred["email"]
                    existing.password_enc = cred["password"]
                    existing.storage_state_path = state_path
                    updated += 1
                    _log(f"AccountManager: updated vault account alias={alias}")
                else:
                    slot = _AccountSlot(
                        alias=alias,
                        api_key="",
                        email=cred["email"],
                        password_enc=cred["password"],
                        storage_state_path=state_path,
                    )
                    self._slots[alias] = slot
                    added += 1
                    _log(f"AccountManager: loaded vault account alias={alias}")
            self._apply_disabled_state()
            self._round_robin_idx = 0
        _log(f"AccountManager: vault loaded {added} new + {updated} updated, total={len(self._slots)}")
        return added

    def _apply_disabled_state(self):
        for alias, slot in self._slots.items():
            slot.disabled = alias in _DISABLED_ACCOUNTS

    def sync_disabled_state(self) -> None:
        _load_disabled_accounts()
        with self._lock:
            self._apply_disabled_state()
        _log(f"AccountManager: synced disabled state, disabled={list(_DISABLED_ACCOUNTS)}")

    def force_reload(self, params: dict[str, Any], site_profile: _SiteProfile) -> int:
        with self._lock:
            self._slots.clear()
            self._key_to_alias.clear()
        count = self.load_from_pool(params, site_profile)
        vault_count = self.load_from_vault()
        self.sync_disabled_state()
        return count + vault_count

    def set_disabled(self, alias: str, disabled: bool) -> None:
        global _DISABLED_ACCOUNTS
        with self._lock:
            slot = self._slots.get(alias)
            if slot:
                slot.disabled = disabled
        if disabled:
            _DISABLED_ACCOUNTS.add(alias)
        else:
            _DISABLED_ACCOUNTS.discard(alias)
        _save_disabled_accounts()
        _log(f"AccountManager: {alias} {'disabled' if disabled else 'enabled'}")

    def get_disabled_aliases(self) -> list[str]:
        with self._lock:
            return [a for a, s in self._slots.items() if s.disabled]

    def acquire(self, worker_id: str, prefer_alias: str = "", exclude_aliases: list[str] | None = None, exclude_teams: list[str] | None = None) -> _AccountSlot | None:
        with self._lock:
            _exclude = set(exclude_aliases or [])
            _exclude_teams = set(exclude_teams or [])
            for alias_in_slots, slot_in_slots in self._slots.items():
                actual_disabled = alias_in_slots in _DISABLED_ACCOUNTS
                if slot_in_slots.disabled != actual_disabled:
                    _log(f"AccountManager: FIXUP slot.disabled for {alias_in_slots}: {slot_in_slots.disabled} -> {actual_disabled}", level="WARN")
                    slot_in_slots.disabled = actual_disabled
            if prefer_alias and prefer_alias in self._slots and prefer_alias not in _exclude:
                slot = self._slots[prefer_alias]
                if slot.is_available and (not slot.team_name or slot.team_name not in _exclude_teams):
                    slot.active_tasks += 1
                    slot.total_tasks += 1
                    slot.last_used_ts = time.time()
                    _log(f"AccountManager: acquired {slot.alias} (preferred) for {worker_id}, active={slot.active_tasks}")
                    return slot
            aliases = list(self._slots.keys())
            if not aliases:
                return None
            start = self._round_robin_idx % len(aliases)
            for i in range(len(aliases)):
                idx = (start + i) % len(aliases)
                alias = aliases[idx]
                if alias in _exclude:
                    continue
                slot = self._slots[alias]
                if not slot.is_available:
                    if slot.disabled:
                        _log(f"AccountManager: skipping {alias} - disabled")
                    continue
                if slot.team_name and slot.team_name in _exclude_teams:
                    _log(f"AccountManager: skipping {alias} - same team '{slot.team_name}' as failed account")
                    continue
                slot.active_tasks += 1
                slot.total_tasks += 1
                slot.last_used_ts = time.time()
                self._round_robin_idx = idx + 1
                _log(f"AccountManager: acquired {slot.alias} for {worker_id}, active={slot.active_tasks}")
                return slot
            _log(f"AccountManager: no available account for {worker_id} (total={len(aliases)}, disabled={[a for a,s in self._slots.items() if s.disabled]})", level="WARN")
            return None

    def release(self, alias: str, success: bool = True, error_msg: str = "", task_id: str = "") -> None:
        with self._lock:
            slot = self._slots.get(alias)
            if not slot:
                return
            slot.active_tasks = max(0, slot.active_tasks - 1)
            if task_id and slot.interactive_task_id == task_id:
                slot.interactive_task_id = None
            elif not task_id or slot.active_tasks == 0:
                slot.interactive_task_id = None
            if not success:
                slot.failed_tasks += 1
                slot.last_error_ts = time.time()
                slot.last_error_msg = error_msg[:200]
            _log(f"AccountManager: released {alias}, active={slot.active_tasks}, interactive_task_id={slot.interactive_task_id}, success={success}")

    def get_slot(self, alias: str) -> _AccountSlot | None:
        with self._lock:
            return self._slots.get(alias)

    def get_slot_by_key(self, api_key: str) -> _AccountSlot | None:
        with self._lock:
            alias = self._key_to_alias.get(api_key)
            if alias:
                return self._slots.get(alias)
            return None

    def status_summary(self) -> list[dict[str, Any]]:
        with self._lock:
            result = []
            browsers_by_alias = {}
            try:
                with _BROWSER_POOL._lock:
                    for s in _BROWSER_POOL._slots.values():
                        if s.is_alive:
                            browsers_by_alias[s.account_alias] = browsers_by_alias.get(s.account_alias, 0) + 1
            except Exception:
                pass
            for alias, slot in self._slots.items():
                result.append({
                    "alias": alias,
                    "active_tasks": slot.active_tasks,
                    "available_slots": slot.available_slots,
                    "total_tasks": slot.total_tasks,
                    "failed_tasks": slot.failed_tasks,
                    "is_available": slot.is_available,
                    "cooldown_remaining": max(0, slot.cooldown_until - time.time()),
                    "is_premium": slot.is_premium,
                    "disabled": slot.disabled,
                    "browsers_count": browsers_by_alias.get(alias, 0),
                })
            return result


    def wait_for_available(self, timeout_s: float = 120, poll_interval: float = 2.0) -> _AccountSlot | None:
        deadline = time.time() + timeout_s
        while time.time() < deadline:
            with self._lock:
                for alias, slot in self._slots.items():
                    actual_disabled = alias in _DISABLED_ACCOUNTS
                    if slot.disabled != actual_disabled:
                        slot.disabled = actual_disabled
                    if slot.is_available:
                        return slot
            time.sleep(poll_interval)
        return None


_ACCOUNT_MGR = _AccountManager()


# ═══════════════════════════════════════════════════════════════════════════════
# Module 2: Task Monitor — 视频任务状态轮询、生命周期数据记录
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class _TaskLifecycle:
    task_id: str
    submit_id: str = ""
    account_alias: str = ""
    model: str = ""
    generation_type: str = ""
    status: str = "created"
    created_at: float = 0.0
    submitted_at: float = 0.0
    estimated_complete_at: float = 0.0
    completed_at: float = 0.0
    output_url: str = ""
    output_path: str = ""
    error_message: str = ""
    progress_pct: float = 0.0
    retry_count: int = 0

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)

    def elapsed_seconds(self) -> float:
        end = self.completed_at or time.time()
        return max(0, end - self.created_at)


class _TaskMonitor:
    def __init__(self) -> None:
        self._lock = threading.Lock()
        self._lifecycles: dict[str, _TaskLifecycle] = {}
        self._submit_to_task: dict[str, str] = {}
        self._poll_thread: threading.Thread | None = None
        self._stop_event = threading.Event()
        self._poll_interval: float = 10.0
        self._on_complete_callbacks: list[Any] = []

    def register(self, lifecycle: _TaskLifecycle) -> None:
        with self._lock:
            self._lifecycles[lifecycle.task_id] = lifecycle
            if lifecycle.submit_id:
                self._submit_to_task[lifecycle.submit_id] = lifecycle.task_id
        _log(f"TaskMonitor: registered {lifecycle.task_id} submit={lifecycle.submit_id}")

    def update(self, task_id: str, **kwargs: Any) -> None:
        with self._lock:
            lc = self._lifecycles.get(task_id)
            if not lc:
                return
            for k, v in kwargs.items():
                if hasattr(lc, k):
                    setattr(lc, k, v)

    def get(self, task_id: str) -> _TaskLifecycle | None:
        with self._lock:
            return self._lifecycles.get(task_id)

    def get_by_submit_id(self, submit_id: str) -> _TaskLifecycle | None:
        with self._lock:
            tid = self._submit_to_task.get(submit_id)
            if tid:
                return self._lifecycles.get(tid)
            return None

    def remove(self, task_id: str) -> None:
        with self._lock:
            lc = self._lifecycles.pop(task_id, None)
            if lc and lc.submit_id:
                self._submit_to_task.pop(lc.submit_id, None)

    def active_tasks(self) -> list[_TaskLifecycle]:
        with self._lock:
            return [lc for lc in self._lifecycles.values() if lc.status not in ("completed", "failed", "cancelled")]

    def completed_tasks(self) -> list[_TaskLifecycle]:
        with self._lock:
            return [lc for lc in self._lifecycles.values() if lc.status == "completed"]

    def all_lifecycles(self) -> list[_TaskLifecycle]:
        with self._lock:
            return list(self._lifecycles.values())

    def on_complete(self, callback: Any) -> None:
        self._on_complete_callbacks.append(callback)

    def start_polling(self, api_key: str, api_base: str, poll_interval: float = 10.0) -> None:
        self._poll_interval = poll_interval
        self._stop_event.clear()
        if self._poll_thread and self._poll_thread.is_alive():
            return
        self._poll_thread = threading.Thread(
            target=self._poll_loop,
            args=(api_key, api_base),
            daemon=True,
            name="runwayml-task-monitor",
        )
        self._poll_thread.start()
        _log(f"TaskMonitor: polling started, interval={poll_interval}s")

    def stop_polling(self) -> None:
        self._stop_event.set()
        if self._poll_thread and self._poll_thread.is_alive():
            self._poll_thread.join(timeout=5)
        _log("TaskMonitor: polling stopped")

    def _poll_loop(self, api_key: str, api_base: str) -> None:
        client = RunwayMLClient(api_key, api_base)
        while not self._stop_event.is_set():
            try:
                active = self.active_tasks()
                for lc in active:
                    if not lc.submit_id:
                        continue
                    try:
                        task_data = client.get_task(lc.submit_id)
                        status = str(task_data.get("status") or "").strip().lower()
                        progress = task_data.get("progress")
                        if isinstance(progress, (int, float)):
                            self.update(lc.task_id, progress_pct=float(progress))
                        if status in ("succeeded", "complete", "completed", "done"):
                            output_list = task_data.get("output") or []
                            video_url = ""
                            if isinstance(output_list, list) and output_list:
                                for item in output_list:
                                    if isinstance(item, list) and len(item) >= 1:
                                        candidate = str(item[0]).strip()
                                        if candidate.startswith("http"):
                                            video_url = candidate
                                            break
                                    elif isinstance(item, str) and item.startswith("http"):
                                        video_url = item
                                        break
                            if not video_url:
                                video_url = task_data.get("video_url") or task_data.get("url") or ""
                            self.update(
                                lc.task_id,
                                status="completed",
                                completed_at=time.time(),
                                output_url=str(video_url),
                                progress_pct=1.0,
                            )
                            _log(f"TaskMonitor: task {lc.task_id} completed, url={_mask_secret(str(video_url), 15)}")
                            for cb in self._on_complete_callbacks:
                                try:
                                    cb(lc)
                                except Exception:
                                    pass
                        elif status in ("failed", "error", "cancelled", "canceled"):
                            error_msg = task_data.get("error") or task_data.get("failure") or "任务失败"
                            self.update(
                                lc.task_id,
                                status="failed",
                                completed_at=time.time(),
                                error_message=str(error_msg),
                            )
                            _log(f"TaskMonitor: task {lc.task_id} failed: {error_msg}", level="WARN")
                            for cb in self._on_complete_callbacks:
                                try:
                                    cb(lc)
                                except Exception:
                                    pass
                        else:
                            self.update(lc.task_id, status=status)
                    except Exception as exc:
                        _log(f"TaskMonitor: poll error for {lc.submit_id}: {exc}", level="WARN")
            except Exception as exc:
                _log(f"TaskMonitor: poll loop error: {exc}", level="WARN")
            self._stop_event.wait(self._poll_interval)

    def stats(self) -> dict[str, Any]:
        with self._lock:
            total = len(self._lifecycles)
            active = sum(1 for lc in self._lifecycles.values() if lc.status not in ("completed", "failed", "cancelled"))
            completed = sum(1 for lc in self._lifecycles.values() if lc.status == "completed")
            failed = sum(1 for lc in self._lifecycles.values() if lc.status == "failed")
            avg_elapsed = 0.0
            completed_lcs = [lc for lc in self._lifecycles.values() if lc.status == "completed" and lc.completed_at > 0]
            if completed_lcs:
                avg_elapsed = sum(lc.elapsed_seconds() for lc in completed_lcs) / len(completed_lcs)
            return {
                "total": total,
                "active": active,
                "completed": completed,
                "failed": failed,
                "avg_elapsed_seconds": round(avg_elapsed, 1),
            }


_TASK_MONITOR = _TaskMonitor()


# ═══════════════════════════════════════════════════════════════════════════════
# Module 2.5: Task Scheduler — 全局任务队列调度（解决并发冲突）
# ═══════════════════════════════════════════════════════════════════════════════

from enum import Enum
from collections import deque

class _TaskState(Enum):
    QUEUED = "queued"
    ACQUIRING = "acquiring"
    RUNNING = "running"
    COMPLETED = "completed"
    FAILED = "failed"
    CANCELLED = "cancelled"

@dataclass
class _ScheduledTask:
    task_id: str
    state: _TaskState = _TaskState.QUEUED
    created_at: float = 0.0
    acquired_at: float = 0.0
    started_at: float = 0.0
    completed_at: float = 0.0
    account_alias: str = ""
    retry_count: int = 0
    error_msg: str = ""
    queue_position: int = 0

    def __post_init__(self):
        if self.created_at == 0.0:
            self.created_at = time.time()

class _TaskScheduler:
    def __init__(self):
        self._lock = threading.RLock()
        self._cond = threading.Condition(self._lock)
        self._queue: deque[_ScheduledTask] = deque()
        self._running: dict[str, _ScheduledTask] = {}
        self._max_concurrent: int = 4
        self._total_submitted: int = 0
        self._total_completed: int = 0
        self._total_failed: int = 0
        self._peak_concurrent: int = 0

    def set_max_concurrent(self, n: int):
        with self._lock:
            old = self._max_concurrent
            self._max_concurrent = max(1, n)
            if self._max_concurrent != old:
                _log(f"TaskScheduler: max_concurrent changed {old} → {self._max_concurrent}")
                self._cond.notify_all()

    @property
    def max_concurrent(self) -> int:
        with self._lock:
            return self._max_concurrent

    @property
    def running_count(self) -> int:
        with self._lock:
            return len(self._running)

    @property
    def queued_count(self) -> int:
        with self._lock:
            return len([t for t in self._queue if t.state == _TaskState.QUEUED])

    def submit(self, task_id: str) -> _ScheduledTask:
        with self._cond:
            st = _ScheduledTask(task_id=task_id)
            for i, t in enumerate(self._queue):
                t.queue_position = i + 1
            st.queue_position = len(self._queue) + 1
            self._queue.append(st)
            self._total_submitted += 1
            _log(f"TaskScheduler: SUBMIT task={task_id} queue_pos={st.queue_position} "
                 f"[Q={self.queued_count} R={self.running_count}/{self._max_concurrent}]")
            return st

    def acquire_slot(self, task_id: str, timeout_s: float = 7200,
                     exclude_aliases: list[str] | None = None,
                     exclude_teams: list[str] | None = None,
                     context: dict | None = None) -> tuple[_AccountSlot | None, _ScheduledTask | None]:
        exclude_aliases = exclude_aliases or []
        exclude_teams = exclude_teams or []
        deadline = time.time() + timeout_s
        with self._cond:
            st = next((t for t in self._queue if t.task_id == task_id), None)
            if not st:
                _log(f"TaskScheduler: WARNING task={task_id} not found in queue, creating ad-hoc", level="WARN")
                st = _ScheduledTask(task_id=task_id)
                self._queue.append(st)
            st.exclude_aliases = exclude_aliases
            st.exclude_teams = exclude_teams
            while True:
                now = time.time()
                if now >= deadline:
                    _log(f"TaskScheduler: TIMEOUT task={task_id} waited {timeout_s:.0f}s", level="ERROR")
                    st.state = _TaskState.FAILED
                    st.error_msg = f"等待超时({timeout_s:.0f}s)"
                    try:
                        self._queue.remove(st)
                    except ValueError:
                        pass
                    self._total_failed += 1
                    return None, st

                running = len(self._running)
                browser_busy = _BROWSER_POOL.stats()["busy"] if _BROWSER_POOL._slots else 0
                can_start = running < self._max_concurrent and browser_busy < self._max_concurrent
                _unavailable_reasons = []
                if can_start:
                    slot = None
                    with _ACCOUNT_MGR._lock:
                        # Sort accounts so that the least recently used one is checked first
                        sorted_slots = sorted(
                            _ACCOUNT_MGR._slots.items(),
                            key=lambda item: item[1].last_used_ts or 0.0
                        )
                        for alias, aslot in sorted_slots:
                            actual_disabled = alias in _DISABLED_ACCOUNTS
                            if aslot.disabled != actual_disabled:
                                aslot.disabled = actual_disabled
                            if not aslot.is_available:
                                _unavailable_reasons.append(f"{alias}(disabled)")
                                continue
                            # 限制单账号的最大活跃并发任务数，防止超过 Runway 官方限制导致 Generate 按钮不可用
                            if aslot.active_tasks >= _MAX_CONCURRENT_PER_ACCOUNT:
                                _unavailable_reasons.append(f"{alias}(busy: {aslot.active_tasks}>={_MAX_CONCURRENT_PER_ACCOUNT})")
                                continue
                            if alias in exclude_aliases:
                                _unavailable_reasons.append(f"{alias}(excluded)")
                                continue
                            if aslot.team_name and aslot.team_name in exclude_teams:
                                _unavailable_reasons.append(f"{alias}(team_excluded)")
                                continue
                            # Option B: Wait if another task is currently interacting with this account
                            if aslot.interactive_task_id is not None and aslot.interactive_task_id != task_id:
                                _unavailable_reasons.append(f"{alias}(interactive: task {aslot.interactive_task_id} is configuring browser)")
                                continue
                            
                            # 只有在排在当前任务之前、且也符合抢占该账号资格的任务不存在时，才允许当前任务抢占
                            older_eligible = None
                            for t in self._queue:
                                if t.task_id == task_id:
                                    break
                                t_excludes = getattr(t, "exclude_aliases", None) or []
                                t_teams = getattr(t, "exclude_teams", None) or []
                                if alias not in t_excludes and (not aslot.team_name or aslot.team_name not in t_teams):
                                    older_eligible = t
                                    break
                            
                            if older_eligible is not None:
                                _unavailable_reasons.append(f"{alias}(yielded: task {older_eligible.task_id} is older and eligible)")
                                continue

                            slot = aslot
                            break
                    if slot is not None:
                        with _ACCOUNT_MGR._lock:
                            if not slot.is_available or slot.disabled or slot.alias in _DISABLED_ACCOUNTS:
                                _log(f"TaskScheduler: RACE DETECTED task={task_id} slot={slot.alias} "
                                     "was snatched between check and acquire, retrying...", level="WARN")
                                st.retry_count += 1
                                if st.retry_count <= 3:
                                    wait_time = min(0.5 * st.retry_count, 2.0)
                                    self._cond.wait(timeout=wait_time)
                                    continue
                                else:
                                    _log(f"TaskScheduler: too many race retries ({st.retry_count}) for task={task_id}", level="WARN")
                                    slot = None
                    if slot is not None:
                        with _ACCOUNT_MGR._lock:
                            slot.active_tasks += 1
                            slot.total_tasks += 1
                            slot.last_used_ts = time.time()
                            slot.interactive_task_id = task_id  # Set Option B interactive lock!
                        try:
                            self._queue.remove(st)
                        except ValueError:
                            pass
                        st.state = _TaskState.RUNNING
                        st.account_alias = slot.alias
                        st.acquired_at = time.time()
                        st.started_at = st.acquired_at
                        self._running[task_id] = st
                        if len(self._running) > self._peak_concurrent:
                            self._peak_concurrent = len(self._running)
                        for i, t in enumerate(self._queue):
                            t.queue_position = i + 1
                        _log(f"TaskScheduler: ACQUIRED task={task_id} slot={slot.alias} "
                             f"active={slot.active_tasks} [Q={self.queued_count} R={self.running_count}/{self._max_concurrent}] "
                             f"retry={st.retry_count}")
                        return slot, st
                wait_timeout = min(max(0.5, (deadline - now) * 0.1), 5.0)
                st.state = _TaskState.ACQUIRING
                if _unavailable_reasons:
                    _log(f"TaskScheduler: task={task_id} slot available but accounts unavailable: {_unavailable_reasons}, waiting {wait_timeout:.1f}s")
                if context:
                    q_pos = st.queue_position
                    if q_pos > 1:
                        _safe_progress(context, f"Playwright: 并发排队(第{q_pos}位)")
                    else:
                        _safe_progress(context, "Playwright: 并发排队(第1位)")
                self._cond.wait(timeout=wait_timeout)

    def release_slot(self, task_id: str, success: bool = True, error_msg: str = "") -> bool:
        with self._cond:
            st = self._running.pop(task_id, None)
            if not st:
                _log(f"TaskScheduler: WARNING release for unknown/already-released task={task_id}", level="WARN")
                return False
            st.completed_at = time.time()
            st.state = _TaskState.COMPLETED if success else _TaskState.FAILED
            if not success:
                st.error_msg = error_msg[:300]
                self._total_failed += 1
            else:
                self._total_completed += 1
            alias = st.account_alias
            if alias:
                _ACCOUNT_MGR.release(alias, success=success, error_msg=error_msg, task_id=task_id)
            for i, t in enumerate(self._queue):
                t.queue_position = i + 1
            _log(f"TaskScheduler: RELEASED task={task_id} slot={alias} success={success} "
                 f"[Q={self.queued_count} R={self.running_count}/{self._max_concurrent}] "
                 f"— waking all waiting tasks...")
            self._cond.notify_all()
            return True

    def cancel_task(self, task_id: str) -> bool:
        with self._cond:
            for t in self._queue:
                if t.task_id == task_id:
                    t.state = _TaskState.CANCELLED
                    try:
                        self._queue.remove(t)
                    except ValueError:
                        pass
                    _log(f"TaskScheduler: CANCELLED queued task={task_id}")
                    return True
            st = self._running.get(task_id)
            if st:
                st.state = _TaskState.CANCELLED
                _log(f"TaskScheduler: MARKED running task={task_id} for cancellation")
                return True
            return False

    def get_task_status(self, task_id: str) -> _ScheduledTask | None:
        with self._lock:
            for t in self._queue:
                if t.task_id == task_id:
                    return t
            return self._running.get(task_id)

    def status_snapshot(self) -> dict[str, Any]:
        with self._lock:
            queued_list = [{"id": t.task_id, "pos": t.queue_position, "state": t.state.value,
                           "age_sec": round(time.time() - t.created_at, 1)} for t in self._queue]
            running_list = [{"id": t.task_id, "alias": t.account_alias, "state": t.state.value,
                            "run_sec": round(time.time() - t.started_at, 1)} for t in self._running.values()]
            return {
                "max_concurrent": self._max_concurrent,
                "queued": len(queued_list),
                "running": len(running_list),
                "queued_detail": queued_list,
                "running_detail": running_list,
                "total_submitted": self._total_submitted,
                "total_completed": self._total_completed,
                "total_failed": self._total_failed,
                "peak_concurrent": self._peak_concurrent,
            }

_TASK_SCHEDULER = _TaskScheduler()


# ═══════════════════════════════════════════════════════════════════════════════
# Module 3: Credential Vault — 账号凭证加密存储与自动登录
# ═══════════════════════════════════════════════════════════════════════════════

_VAULT_KEY_ENV = "RUNWAYML_VAULT_KEY"
_VAULT_FILE = DATA_DIR / "runwayml_vault.enc"


def _derive_vault_key() -> bytes:
    env_key = os.environ.get(_VAULT_KEY_ENV, "").strip()
    if env_key:
        return hashlib.sha256(env_key.encode("utf-8")).digest()
    machine_id = str(uuid.getnode()) + str(os.environ.get("USERNAME", "")) + str(os.environ.get("COMPUTERNAME", ""))
    return hashlib.sha256(machine_id.encode("utf-8")).digest()


def _encrypt_data(plaintext: str, key: bytes) -> str:
    import struct
    nonce = os.urandom(12)
    counter = struct.unpack(">Q", nonce[:8])[0] & 0x7FFFFFFFFFFFFFFF
    encrypted = bytearray()
    for i, ch in enumerate(plaintext.encode("utf-8")):
        key_byte = key[(counter + i) % len(key)]
        encrypted.append(ch ^ key_byte)
    return base64.b64encode(nonce + bytes(encrypted)).decode("ascii")


def _decrypt_data(ciphertext: str, key: bytes) -> str:
    import struct
    raw = base64.b64decode(ciphertext)
    nonce = raw[:12]
    counter = struct.unpack(">Q", nonce[:8])[0] & 0x7FFFFFFFFFFFFFFF
    encrypted = raw[12:]
    decrypted = bytearray()
    for i, ch in enumerate(encrypted):
        key_byte = key[(counter + i) % len(key)]
        decrypted.append(ch ^ key_byte)
    return bytes(decrypted).decode("utf-8")


class _CredentialVault:
    def __init__(self) -> None:
        self._lock = threading.Lock()
        self._vault_key: bytes | None = None
        self._cache: dict[str, dict[str, str]] = {}

    def _get_key(self) -> bytes:
        if self._vault_key is None:
            self._vault_key = _derive_vault_key()
        return self._vault_key

    def save(self, vault_path: str | None = None) -> None:
        path = vault_path or str(_VAULT_FILE) if _VAULT_FILE else None
        if not path:
            return
        key = self._get_key()
        with self._lock:
            data = json.dumps(self._cache, ensure_ascii=False)
            encrypted = _encrypt_data(data, key)
        try:
            os.makedirs(os.path.dirname(path), exist_ok=True)
            tmp_path = path + ".tmp"
            with open(tmp_path, "w", encoding="utf-8") as f:
                f.write(encrypted)
            verify_decrypted = _decrypt_data(encrypted, key)
            verify_cache = json.loads(verify_decrypted)
            if set(verify_cache.keys()) != set(self._cache.keys()):
                _log(f"CredentialVault: save verification mismatch! expected={list(self._cache.keys())} got={list(verify_cache.keys())}", level="ERROR")
                return
            if os.path.isfile(path):
                os.replace(tmp_path, path)
            else:
                os.rename(tmp_path, path)
            _log(f"CredentialVault: saved {len(self._cache)} entries to {path}")
        except Exception as exc:
            _log(f"CredentialVault: save failed: {exc}", level="WARN")

    def load(self, vault_path: str | None = None) -> bool:
        path = vault_path or str(_VAULT_FILE) if _VAULT_FILE else None
        if not path or not os.path.isfile(path):
            return False
        key = self._get_key()
        try:
            with open(path, "r", encoding="utf-8") as f:
                encrypted = f.read().strip()
            decrypted = _decrypt_data(encrypted, key)
            with self._lock:
                self._cache = json.loads(decrypted)
            _log(f"CredentialVault: loaded {len(self._cache)} entries")
            return True
        except Exception as exc:
            _log(f"CredentialVault: load failed: {exc}", level="WARN")
            return False

    def store_credential(self, alias: str, email: str, password: str, extra: dict[str, str] | None = None) -> None:
        key = self._get_key()
        with self._lock:
            entry = {
                "email": _encrypt_data(email, key),
                "password": _encrypt_data(password, key),
            }
            if extra:
                for k, v in extra.items():
                    entry[f"enc_{k}"] = _encrypt_data(v, key)
            self._cache[alias] = entry
        _log(f"CredentialVault: stored credential for {alias}")

    def get_credential(self, alias: str) -> dict[str, str] | None:
        key = self._get_key()
        with self._lock:
            entry = self._cache.get(alias)
            if not entry:
                return None
            result: dict[str, str] = {}
            for k, v in entry.items():
                if k.startswith("enc_"):
                    try:
                        result[k[4:]] = _decrypt_data(v, key)
                    except Exception:
                        result[k[4:]] = v
                else:
                    try:
                        result[k] = _decrypt_data(v, key)
                    except Exception:
                        result[k] = v
            return result

    def delete_credential(self, alias: str) -> None:
        with self._lock:
            self._cache.pop(alias, None)

    def list_aliases(self) -> list[str]:
        with self._lock:
            return list(self._cache.keys())


_CREDENTIAL_VAULT = _CredentialVault()

_DISABLED_ACCOUNTS_FILE = str(DATA_DIR / "runwayml_disabled_accounts.json") if DATA_DIR.exists() else ""
_DISABLED_ACCOUNTS: set[str] = set()

def _load_disabled_accounts():
    global _DISABLED_ACCOUNTS
    if not _DISABLED_ACCOUNTS_FILE:
        return
    try:
        if os.path.isfile(_DISABLED_ACCOUNTS_FILE):
            with open(_DISABLED_ACCOUNTS_FILE, "r", encoding="utf-8") as f:
                data = json.load(f)
            _DISABLED_ACCOUNTS = set(data.get("disabled", []))
            _log(f"loaded {len(_DISABLED_ACCOUNTS)} disabled accounts")
    except Exception as e:
        _log(f"load disabled accounts error: {e}", level="WARN")
        _DISABLED_ACCOUNTS = set()

def _save_disabled_accounts():
    if not _DISABLED_ACCOUNTS_FILE:
        return
    try:
        with open(_DISABLED_ACCOUNTS_FILE, "w", encoding="utf-8") as f:
            json.dump({"disabled": sorted(_DISABLED_ACCOUNTS)}, f, ensure_ascii=False, indent=2)
    except Exception as e:
        _log(f"save disabled accounts error: {e}", level="WARN")

_load_disabled_accounts()


def _auto_login_runwayml(page: Any, email: str, password: str, timeout_s: int = 60) -> bool:
    try:
        current_url = page.url
        _log(f"auto_login: current URL = {current_url[:120]}")

        if "/teams/" in current_url and "/teams/guest/" not in current_url:
            _log("auto_login: already on authenticated page (has /teams/ and not guest), no login needed")
            return True

        if "/teams/guest/" in current_url:
            _log("auto_login: on guest page, clicking Login button")
            try:
                login_link = page.locator('[data-testid="login-button"], a:has-text("Login"), a:has-text("Log in")').first
                if login_link.is_visible(timeout=5000):
                    login_link.click()
                    page.wait_for_timeout(3000)
            except Exception as exc:
                _log(f"auto_login: click login link failed, navigating directly: {exc}", level="WARN")
                page.goto(f"{RUNWAYML_WEB_BASE}/login", wait_until="domcontentloaded")
                page.wait_for_timeout(3000)
        elif "login" in current_url.lower() or "sign-in" in current_url.lower():
            _log("auto_login: on login page, proceeding with login flow")
        else:
            try:
                login_btn = page.locator('[data-testid="login-button"], a:has-text("Login"), a:has-text("Log in")').first
                if login_btn.is_visible(timeout=3000):
                    _log("auto_login: Login button visible, clicking it to go to login page")
                    login_btn.click()
                    page.wait_for_timeout(3000)
                else:
                    _log("auto_login: no guest/login indicators and no Login button visible, assuming already logged in")
                    return True
            except Exception:
                _log("auto_login: no guest/login indicators and cannot find Login button, assuming already logged in")
                return True

        current_url = page.url
        _log(f"auto_login: after redirect, URL = {current_url[:120]}")
        if "/teams/" in current_url and "/teams/guest/" not in current_url:
            _log("auto_login: already logged in (has /teams/ in URL)")
            return True

        _log("auto_login: starting login flow")
        try:
            email_input = page.locator('input[name="usernameOrEmail"], input[type="text"][placeholder*="Username" i], input[type="text"][placeholder*="Email" i], input[type="email"]').first
            email_input.click()
            email_input.fill(email)
            page.wait_for_timeout(500)
        except Exception as exc:
            _log(f"auto_login: email input failed: {exc}", level="WARN")
            return False

        try:
            pw_input = page.locator('input[name="password"], input[type="password"]').first
            pw_input.click()
            pw_input.fill(password)
            page.wait_for_timeout(500)
        except Exception as exc:
            _log(f"auto_login: password input failed: {exc}", level="WARN")
            return False

        try:
            submit_btn = page.locator('button:has-text("Log in"):not(:has-text("Google")):not(:has-text("Apple")):not(:has-text("SSO"))').first
            submit_btn.click()
        except Exception as exc:
            _log(f"auto_login: submit failed: {exc}", level="WARN")
            return False

        try:
            for _ in range(12):
                page.wait_for_timeout(5000)
                current_url = page.url
                _log(f"auto_login: polling URL = {current_url[:120]}")
                if "/teams/" in current_url and "/teams/guest/" not in current_url:
                    _log("auto_login: login successful (has /teams/ in URL)")
                    return True
                if "login" not in current_url.lower() and "sign-in" not in current_url.lower() and "/teams/" not in current_url:
                    pass
            _log(f"auto_login: login may have timed out, current URL: {current_url}", level="WARN")
            return False
        except Exception:
            page.wait_for_timeout(3000)
            current_url = page.url
            if "/teams/" in current_url and "/teams/guest/" not in current_url:
                _log("auto_login: login appears successful (URL check after exception)")
                return True
            _log(f"auto_login: login may have failed, current URL: {current_url}", level="WARN")
            return False
    except Exception as exc:
        _log(f"auto_login: exception: {exc}", level="ERROR")
        return False


# ═══════════════════════════════════════════════════════════════════════════════
# Module 4: Browser Pool — 多无痕浏览器实例管理
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class _BrowserSlot:
    slot_id: str
    account_alias: str
    task_id: str = ""
    browser: Any = None
    context: Any = None
    page: Any = None
    playwright: Any = None
    created_at: float = 0.0
    last_used_at: float = 0.0
    is_busy: bool = False
    task_count: int = 0
    position_index: int = -1
    tile_width: int = 800
    tile_height: int = 600
    zoom_factor: float = 1.0
    physical_inner_width: int = 0
    physical_inner_height: int = 0
    cdp_session: Any = None

    @property
    def idle_seconds(self) -> float:
        return time.time() - self.last_used_at

    @property
    def is_alive(self) -> bool:
        try:
            return self.browser is not None and self.browser.is_connected()
        except Exception:
            return False

def _execute_cancellation_on_page(page: Any, account_alias: str, team_name: str) -> None:
    _log(f"cancellation: starting task cancellation on page for account={account_alias}, team={team_name}")
    try:
        if not team_name:
            _log(f"cancellation: team_name is empty for {account_alias}, navigating to home to detect...")
            page.goto("https://app.runwayml.com/", timeout=20000)
            page.wait_for_timeout(3000)
            current_url = page.url
            team_match = re.search(r"/teams/([^/]+)/", current_url)
            if team_match and "/teams/guest/" not in current_url:
                team_name = team_match.group(1)
                _log(f"cancellation: detected team_name='{team_name}' for {account_alias}")
            else:
                _log(f"cancellation: could not detect team_name for {account_alias}, current_url={current_url}", level="WARN")

        if team_name:
            assets_url = f"https://app.runwayml.com/video-tools/teams/{team_name}/ai-tools/assets"
        else:
            assets_url = "https://app.runwayml.com/video-tools/ai-tools/assets"

        _log(f"cancellation: navigating to assets URL: {assets_url}")
        page.goto(assets_url, timeout=30000)
        page.wait_for_timeout(5000)

        js_code = """
        async () => {
            const delay = ms => new Promise(res => setTimeout(res, ms));
            let canceledCount = 0;
            
            for (let attempt = 0; attempt < 5; attempt++) {
                const selectors = [
                    '[class*="slot-" i]',
                    '[class*="asset" i]',
                    '[class*="card" i]',
                    '[class*="grid-item" i]',
                    '[class*="item" i]',
                    '[class*="thumbnail" i]',
                    '[class*="preview" i]',
                    '[class*="TaskCard"]',
                    '[class*="Progress"]'
                ];
                
                let items = [];
                for (const sel of selectors) {
                    try {
                        const found = Array.from(document.querySelectorAll(sel));
                        if (found.length > 0) {
                            items = found;
                            break;
                        }
                    } catch (e) {}
                }
                
                if (items.length === 0) {
                    items = Array.from(document.querySelectorAll('div'));
                }
                
                let foundActive = false;
                
                for (const item of items) {
                    const txt = (item.innerText || '').toLowerCase();
                    const isGenerating = txt.includes('generating') || 
                                         txt.includes('queued') || 
                                         txt.includes('排队') || 
                                         txt.includes('生成中') || 
                                         /\\d+%/.test(txt);
                                         
                    if (!isGenerating) continue;
                    
                    foundActive = true;
                    console.log("Found generating item:", txt.substring(0, 100));
                    
                    item.dispatchEvent(new MouseEvent('mouseover', { bubbles: true, cancelable: true, view: window }));
                    await delay(500);
                    
                    const buttons = Array.from(item.querySelectorAll('button, [role="button"], svg, a'));
                    let cancelBtn = null;
                    
                    for (const btn of buttons) {
                        const btnText = (btn.innerText || '').toLowerCase();
                        const btnAria = (btn.getAttribute('aria-label') || '').toLowerCase();
                        const btnClass = (btn.getAttribute('class') || '').toLowerCase();
                        
                        if (btnText.includes('cancel') || btnText.includes('取消') || btnText.includes('stop') ||
                            btnAria.includes('cancel') || btnAria.includes('取消') || btnAria.includes('stop') ||
                            btnClass.includes('cancel') || btnClass.includes('close')) {
                            cancelBtn = btn;
                            break;
                        }
                    }
                    
                    if (!cancelBtn) {
                        for (const btn of buttons) {
                            if (btn.tagName.toLowerCase() === 'svg' || btn.querySelector('svg')) {
                                cancelBtn = btn;
                                break;
                            }
                        }
                    }
                    
                    if (cancelBtn) {
                        console.log("Clicking cancel button");
                        cancelBtn.click();
                        await delay(1000);
                        
                        const modalButtons = Array.from(document.querySelectorAll('button, [role="button"]'));
                        for (const mBtn of modalButtons) {
                            const parentDialog = mBtn.closest('[role="dialog"], [class*="modal" i], [class*="dialog" i]');
                            if (parentDialog) {
                                const mBtnTxt = (mBtn.innerText || '').toLowerCase();
                                if (mBtnTxt.includes('confirm') || mBtnTxt.includes('确定') || mBtnTxt.includes('yes') || 
                                    mBtnTxt.includes('cancel task') || mBtnTxt.includes('delete') || mBtnTxt.includes('ok')) {
                                    console.log("Confirming cancellation modal button:", mBtnTxt);
                                    mBtn.click();
                                    canceledCount++;
                                    await delay(1000);
                                    break;
                                }
                            }
                        }
                    }
                }
                
                if (!foundActive) {
                    console.log("No active/generating tasks found on attempt " + attempt);
                    break;
                }
                await delay(1500);
            }
            return canceledCount;
        }
        """
        canceled_count = page.evaluate(js_code)
        _log(f"cancellation: successfully finished task cancellation for {account_alias}, canceled {canceled_count} tasks")
    except Exception as e:
        _log(f"cancellation: failed to execute task cancellation for {account_alias}: {e}", level="ERROR")


def _cancel_active_tasks_for_account(account_alias: str, team_name: str, page_to_use=None) -> None:
    _log(f"cancellation: starting task cancellation for account alias={account_alias}, team_name={team_name}")
    if page_to_use:
        try:
            if not page_to_use.is_closed():
                _execute_cancellation_on_page(page_to_use, account_alias, team_name)
                return
        except Exception as e:
            _log(f"cancellation: failed to use slot page for {account_alias}: {e}. Falling back to temp browser...", level="WARN")

    _log(f"cancellation: spinning up temporary headless browser for {account_alias} cancellation")
    pw = None
    browser = None
    try:
        from playwright.sync_api import sync_playwright
        pw = sync_playwright().start()
        
        for ch in ["chrome", "msedge", None]:
            try:
                if ch:
                    browser = pw.chromium.launch(headless=True, channel=ch)
                    break
                else:
                    browser = pw.chromium.launch(headless=True)
                    break
            except Exception:
                continue
        if not browser:
            raise Exception("failed to launch temp browser with any channel")
            
        ctx_opts = {"viewport": {"width": 800, "height": 600}}
        state_path = ""
        if DATA_DIR.exists():
            auto_state = os.path.join(str(DATA_DIR), "storage_states", f"{account_alias}_state.json")
            if os.path.isfile(auto_state):
                state_path = auto_state
                ctx_opts["storage_state"] = state_path
                _log(f"cancellation: loaded storage state from {state_path}")
                
        ctx = browser.new_context(**ctx_opts)
        page = ctx.new_page()
        _execute_cancellation_on_page(page, account_alias, team_name)
        ctx.close()
    except Exception as exc:
        _log(f"cancellation: temp browser cancellation failed for {account_alias}: {exc}", level="ERROR")
    finally:
        if browser:
            try:
                browser.close()
            except Exception:
                pass
        if pw:
            try:
                pw.stop()
            except Exception:
                pass


_MAX_BROWSER_INSTANCES = 30
_BROWSER_IDLE_TIMEOUT_S = 600
_BROWSER_MAX_TASKS = 200


class _BrowserPool:
    def __init__(self) -> None:
        self._lock = threading.RLock()
        self._slots: dict[str, _BrowserSlot] = {}
        self._cleanup_thread: threading.Thread | None = None
        self._stop_event = threading.Event()
        self._active_accounts: set[str] = set()
        self._active_account_started: dict[str, float] = {}
        self._active_accounts_cond = threading.Condition(self._lock)

    def _launch_new_browser(
        self,
        headless: bool,
        position_index: int = -1,
        browser_channel: str = "",
        grid_size: int = 1,
        arrange_layout: str = "2x2",
        zoom_factor: Any = 1.0,
    ) -> tuple[Any, Any, int, int] | None:
        launch_args = []
        screen_w = 1920
        screen_h = 1080
        try:
            from PySide6.QtGui import QGuiApplication
            app = QGuiApplication.instance()
            if app:
                screen = app.primaryScreen()
                if screen:
                    # availableGeometry 自动排除任务栏区域，比手动减60更准确
                    geom = screen.availableGeometry()
                    screen_w = geom.width()
                    screen_h = geom.height()
                    _log(f"BrowserPool: screen available area = {screen_w}x{screen_h} (DPR={screen.devicePixelRatio()})")
        except Exception as e:
            _log(f"BrowserPool: screen resolution detection error: {e}", level="WARN")

        tile_w = 800
        tile_h = 600

        if position_index >= 0 and not headless:
            try:
                smart_zoom = max(0.3, min(1.0, float(zoom_factor or 1.0)))
            except Exception:
                smart_zoom = 1.0
            # Smart Arrange uses a fixed 800x600 logical page. Match the Chrome
            # outer window to the selected page zoom so the visible area stays snug.
            tile_w = max(416, int((800 * smart_zoom) + 16 + 0.5))
            tile_h = max(395, int((600 * smart_zoom) + 95 + 0.5))
            col = position_index % 4
            row = position_index // 4
            if screen_w > tile_w:
                physical_x = int(col * (screen_w - tile_w) / 3)
            else:
                physical_x = 0
            if screen_h > tile_h + 60:
                physical_y = int(row * (screen_h - 60 - tile_h))
            else:
                physical_y = row * 100

            launch_args.extend([
                f"--window-position={physical_x},{physical_y}",
                f"--window-size={tile_w},{tile_h}"
            ])
            _log(
                f"BrowserPool: smart arrange slot index {position_index} "
                f"-> position={physical_x},{physical_y}, size={tile_w},{tile_h}, zoom={smart_zoom:.2f}"
            )
        elif not headless:
            launch_args.append(f"--window-size={tile_w},{tile_h}")
            _log(f"BrowserPool: smart_arrange disabled, launching browser with physical {tile_w}x{tile_h} size")

        try:
            from playwright.sync_api import sync_playwright
        except ImportError:
            _log("BrowserPool: playwright not installed, attempting auto-install", level="WARN")
            try:
                subprocess.run(
                    [sys.executable, "-m", "pip", "install", "playwright"],
                    capture_output=True, text=True, timeout=120, check=True,
                )
                from playwright.sync_api import sync_playwright
            except Exception as install_exc:
                _log(f"BrowserPool: playwright install failed: {install_exc}", level="ERROR")
                return None
        pw = None
        try:
            _log("BrowserPool: starting playwright instance...", level="INFO")
            pw = sync_playwright().__enter__()
            _log(f"BrowserPool: playwright instance started, type={type(pw).__name__}", level="INFO")
        except Exception as pw_exc:
            _log(f"BrowserPool: playwright __enter__ failed: {pw_exc}", level="ERROR")
            try:
                _log("BrowserPool: attempting legacy .start() method as fallback...", level="WARN")
                _pw_mgr = sync_playwright()
                if hasattr(_pw_mgr, 'start') and callable(getattr(_pw_mgr, 'start')):
                    pw = _pw_mgr.start()
                    _log(f"BrowserPool: playwright started via .start(), type={type(pw).__name__}", level="INFO")
                else:
                    raise pw_exc
            except Exception as fallback_exc:
                _log(f"BrowserPool: all playwright start methods failed: {fallback_exc}", level="ERROR")
                return None
        try:
            browser = None
            if browser_channel:
                ch_list = [browser_channel]
                _log(f"BrowserPool: using specified browser channel: {browser_channel}", level="INFO")
                if browser_channel.lower() in ("chromium", ""):
                    _log(f"BrowserPool: ensuring Playwright bundled Chromium is installed...", level="INFO")
                    try:
                        subprocess.run(
                            [sys.executable, "-m", "playwright", "install", "chromium"],
                            capture_output=True, text=True, timeout=300, check=False,
                        )
                        _log(f"BrowserPool: Playwright Chromium installation check completed", level="INFO")
                    except Exception as install_browser_exc:
                        _log(f"BrowserPool: Playwright Chromium auto-install warning: {install_browser_exc}", level="WARN")
            else:
                ch_list = [None, "chrome", "msedge"]
                _log(f"BrowserPool: auto-detecting browsers: {ch_list}", level="INFO")

            for ch in ch_list:
                try:
                    launch_opts = {"headless": headless}
                    if ch and ch.lower() != "chromium":
                        launch_opts["channel"] = ch
                    if launch_args:
                        launch_opts["args"] = launch_args
                    browser = pw.chromium.launch(**launch_opts)
                    _log(f"BrowserPool: chromium launched successfully with channel='{ch}' (headless={headless})")
                    break
                except Exception as ch_err:
                    _log(f"BrowserPool: failed to launch with channel='{ch}': {ch_err}", level="WARN")
            if not browser:
                raise Exception("failed to launch browser with any channel")
            return (pw, browser, tile_w, tile_h)
        except Exception as launch_exc:
            _log(f"BrowserPool: chromium launch failed: {launch_exc}", level="WARN")
            try:
                subprocess.run(
                    [sys.executable, "-m", "playwright", "install", "chromium"],
                    capture_output=True, text=True, timeout=300, check=True,
                )
                for ch in [None, "chrome", "msedge"]:
                    try:
                        launch_opts = {"headless": headless}
                        if ch:
                            launch_opts["channel"] = ch
                        if launch_args:
                            launch_opts["args"] = launch_args
                        browser = pw.chromium.launch(**launch_opts)
                        _log(f"BrowserPool: chromium launched after retry with channel='{ch}'")
                        break
                    except Exception:
                        continue
                if browser:
                    return (pw, browser, tile_w, tile_h)
            except Exception as retry_exc:
                _log(f"BrowserPool: chromium launch retry failed: {retry_exc}", level="ERROR")
                try:
                    pw.stop()
                except Exception:
                    pass
                return None

    def acquire(
        self,
        account_alias: str,
        task_id: str = "",
        headless: bool = False,
        storage_state_path: str = "",
        cookie_header: str = "",
        smart_arrange: bool = False,
        browser_channel: str = "",
        zoom_factor: Any = "auto",
        arrange_layout: str = "2x2",
    ) -> _BrowserSlot | None:
        with self._lock:
            while account_alias in self._active_accounts:
                _log(f"BrowserPool: account {account_alias} is busy, waiting...")
                self._active_accounts_cond.wait()

            same_account_busy = sum(
                1
                for s in self._slots.values()
                if s.account_alias == account_alias and s.is_busy and s.is_alive
            )
            if same_account_busy >= _MAX_CONCURRENT_PER_ACCOUNT:
                _log(
                    f"BrowserPool: account {account_alias} already has "
                    f"{same_account_busy}/{_MAX_CONCURRENT_PER_ACCOUNT} busy browsers, refusing new browser",
                    level="WARN",
                )
                return None

            busy_count = sum(1 for s in self._slots.values() if s.is_busy)
            if busy_count >= _MAX_BROWSER_INSTANCES:
                _log(f"BrowserPool: max concurrent browsers ({_MAX_BROWSER_INSTANCES}) reached, cannot acquire", level="WARN")
                return None

            self._active_accounts.add(account_alias)
            self._active_account_started[account_alias] = time.time()
            _log(f"BrowserPool: launching new browser for {account_alias} (active={busy_count}/{_MAX_BROWSER_INSTANCES})")

        launch_result = None
        try:
            position_index = -1
            if smart_arrange and not headless:
                with self._lock:
                    used_indices = {s.position_index for s in self._slots.values() if s.position_index >= 0 and s.is_alive}
                    idx = 0
                    while idx in used_indices:
                        idx += 1
                    position_index = idx

            grid_size = _TASK_SCHEDULER.max_concurrent
            grid_size = max(1, grid_size)

            launch_result = self._launch_new_browser(
                headless,
                position_index=position_index,
                browser_channel=browser_channel,
                grid_size=grid_size,
                arrange_layout=arrange_layout,
                zoom_factor=zoom_factor,
            )
            if launch_result is None:
                _log("BrowserPool: launch new browser failed", level="ERROR")
                with self._lock:
                    if account_alias in self._active_accounts:
                        self._active_accounts.remove(account_alias)
                        self._active_account_started.pop(account_alias, None)
                        self._active_accounts_cond.notify_all()
                return None

            pw, browser, tile_w, tile_h = launch_result

            try:
                if smart_arrange:
                    logical_width = 800
                    logical_height = 600
                    try:
                        zoom_f = max(0.3, min(1.0, float(zoom_factor or 1.0)))
                    except Exception:
                        zoom_f = 1.0
                else:
                    _RUNWAY_MIN_LOGICAL_W = 914
                    _RUNWAY_TARGET_LOGICAL_H = 686
                    estimated_content_w = max(320.0, float(tile_w - 16))
                    estimated_content_h = max(240.0, float(tile_h - 95))
                    if str(zoom_factor).strip().lower() == "auto":
                        zoom_h = estimated_content_h / float(_RUNWAY_TARGET_LOGICAL_H)
                        zoom_f = max(0.45, min(1.0, zoom_h))
                    else:
                        try:
                            zoom_f = max(0.3, min(1.0, float(zoom_factor)))
                        except Exception:
                            zoom_f = 1.0
                    logical_width = max(_RUNWAY_MIN_LOGICAL_W, int((estimated_content_w / zoom_f) + 0.999))
                    logical_height = _RUNWAY_TARGET_LOGICAL_H

                _log(
                    f"BrowserPool: viewport tile={tile_w}x{tile_h} (outer), "
                    f"smart_arrange={smart_arrange}, "
                    f"zoom_f={zoom_f:.3f}, logical_viewport={logical_width}x{logical_height}"
                )

                def _restore_smart_window_size(page_obj: Any, reason: str) -> None:
                    if not smart_arrange or headless:
                        return
                    try:
                        cdp_page = ctx.new_cdp_session(page_obj)
                        win_info = cdp_page.send("Browser.getWindowForTarget")
                        window_id = win_info.get("windowId")
                        if window_id is not None:
                            cdp_page.send(
                                "Browser.setWindowBounds",
                                {
                                    "windowId": window_id,
                                    "bounds": {
                                        "width": int(tile_w),
                                        "height": int(tile_h),
                                    },
                                },
                            )
                            _log(f"BrowserPool: restored smart window size {tile_w}x{tile_h} after {reason}")
                    except Exception as bounds_exc:
                        _log(f"BrowserPool: restore smart window size failed after {reason}: {bounds_exc}", level="WARN")

                ctx_opts: dict[str, Any] = {
                    "viewport": {"width": logical_width, "height": logical_height},
                }
                state_path = storage_state_path
                if not state_path or not os.path.isfile(state_path):
                    if DATA_DIR.exists():
                        auto_state = os.path.join(str(DATA_DIR), "storage_states", f"{account_alias}_state.json")
                        if os.path.isfile(auto_state):
                            state_path = auto_state
                            _log(f"BrowserPool: auto-loaded storage state for {account_alias} from {auto_state}")
                if state_path and os.path.isfile(state_path):
                    try:
                        with open(state_path, "r", encoding="utf-8") as f:
                            json.load(f)
                        ctx_opts["storage_state"] = state_path
                    except Exception as state_exc:
                        _log(f"BrowserPool: storage state file invalid, skipping: {state_exc}", level="WARN")
                _log(f"BrowserPool: creating context for {account_alias} (storage_state={'yes' if 'storage_state' in ctx_opts else 'no'})")
                ctx = browser.new_context(**ctx_opts)
                if cookie_header:
                    site_profile = _SITE_PROFILES.get("runwayml")
                    domains = list(site_profile.domains) if site_profile and site_profile.domains else [".runwayml.com"]
                    if ".runwayml.com" not in domains:
                        domains.append(".runwayml.com")
                    for pair in cookie_header.split(";"):
                        pair = pair.strip()
                        if "=" in pair:
                            k, v = pair.split("=", 1)
                            cookies = [
                                {"name": k.strip(), "value": v.strip(), "domain": domain, "path": "/"}
                                for domain in domains
                        ]
                            ctx.add_cookies(cookies)
                page = ctx.new_page()
                _restore_smart_window_size(page, "context/page creation")
                physical_inner_w = 0
                physical_inner_h = 0
                try:
                    physical_inner = page.evaluate("""() => ({ width: window.innerWidth, height: window.innerHeight })""")
                    physical_inner_w = int(physical_inner.get("width") or 0)
                    physical_inner_h = int(physical_inner.get("height") or 0)
                    _log(f"BrowserPool: captured physical inner size {physical_inner_w}x{physical_inner_h}")
                except Exception as inner_exc:
                    _log(f"BrowserPool: capture physical inner size failed: {inner_exc}", level="WARN")
                slot_id = f"bw_{uuid.uuid4().hex[:8]}"
                slot = _BrowserSlot(
                    slot_id=slot_id,
                    account_alias=account_alias,
                    task_id=str(task_id or ""),
                    browser=browser,
                    context=ctx,
                    page=page,
                    playwright=pw,
                    created_at=time.time(),
                    last_used_at=time.time(),
                    is_busy=True,
                    task_count=1,
                    position_index=position_index,
                    tile_width=tile_w,
                    tile_height=tile_h,
                    zoom_factor=zoom_f,
                    physical_inner_width=physical_inner_w,
                    physical_inner_height=physical_inner_h,
                )
                with self._lock:
                    self._slots[slot_id] = slot
                _log(f"BrowserPool: created slot {slot_id} for {account_alias} (dedicated browser)")
                return slot
            except Exception as exc:
                _log(f"BrowserPool: context creation failed: {exc}, retrying without storage state", level="WARN")
                try:
                    ctx = browser.new_context(viewport={"width": logical_width, "height": logical_height})
                    page = ctx.new_page()
                    _restore_smart_window_size(page, "fallback context/page creation")
                    physical_inner_w = 0
                    physical_inner_h = 0
                    try:
                        physical_inner = page.evaluate("""() => ({ width: window.innerWidth, height: window.innerHeight })""")
                        physical_inner_w = int(physical_inner.get("width") or 0)
                        physical_inner_h = int(physical_inner.get("height") or 0)
                        _log(f"BrowserPool: captured physical inner size {physical_inner_w}x{physical_inner_h}")
                    except Exception as inner_exc:
                        _log(f"BrowserPool: capture physical inner size failed: {inner_exc}", level="WARN")
                    slot_id = f"bw_{uuid.uuid4().hex[:8]}"
                    slot = _BrowserSlot(
                        slot_id=slot_id,
                        account_alias=account_alias,
                        task_id=str(task_id or ""),
                        browser=browser,
                        context=ctx,
                        page=page,
                        playwright=pw,
                        created_at=time.time(),
                        last_used_at=time.time(),
                        is_busy=True,
                        task_count=1,
                        position_index=position_index,
                        tile_width=tile_w,
                        tile_height=tile_h,
                        zoom_factor=zoom_f,
                        physical_inner_width=physical_inner_w,
                        physical_inner_height=physical_inner_h,
                    )
                    with self._lock:
                        self._slots[slot_id] = slot
                    _log(f"BrowserPool: created slot {slot_id} for {account_alias} (no storage state, fallback)")
                    return slot
                except Exception as fallback_exc:
                    _log(f"BrowserPool: fallback context creation also failed: {fallback_exc}", level="ERROR")
                    try:
                        browser.close()
                    except Exception:
                        pass
                    try:
                        pw.stop()
                    except Exception:
                        pass
                    with self._lock:
                        if account_alias in self._active_accounts:
                            self._active_accounts.remove(account_alias)
                            self._active_account_started.pop(account_alias, None)
                            self._active_accounts_cond.notify_all()
                    return None
        except Exception as outer_exc:
            _log(f"BrowserPool: acquire exception: {outer_exc}", level="ERROR")
            if launch_result:
                pw, browser = launch_result
                try:
                    browser.close()
                except Exception:
                    pass
                try:
                    pw.stop()
                except Exception:
                    pass
            with self._lock:
                if account_alias in self._active_accounts:
                    self._active_accounts.remove(account_alias)
                    self._active_account_started.pop(account_alias, None)
                    self._active_accounts_cond.notify_all()
            return None

    def release(self, slot_id: str, keep_alive: bool = False) -> None:
        with self._lock:
            slot = self._slots.get(slot_id)
            if not slot:
                return
            alias = slot.account_alias
            slot.is_busy = False
            slot.last_used_at = time.time()
            slot.task_count += 1

            # 释放 Slot 时自动保存最新 Session 状态，确保 Cookie 始终最新且有效
            try:
                if slot.context and alias:
                    storage_dir = str(DATA_DIR / "storage_states") if DATA_DIR.exists() else ""
                    if storage_dir:
                        state_path = os.path.join(storage_dir, f"{alias}_state.json")
                        slot.context.storage_state(path=state_path)
                        _log(f"BrowserPool: auto-saved storage state on release for {alias}")
            except Exception as save_err:
                _log(f"BrowserPool: failed to auto-save state on release for {alias}: {save_err}", level="WARN")

            if not keep_alive or slot.task_count >= _BROWSER_MAX_TASKS or not slot.is_alive:
                self._destroy_slot(slot_id)
            else:
                _log(f"BrowserPool: released slot {slot_id}, keeping alive (tasks={slot.task_count})")
            
            if alias in self._active_accounts:
                self._active_accounts.remove(alias)
                self._active_account_started.pop(alias, None)
                self._active_accounts_cond.notify_all()

        try:
            with _TASK_SCHEDULER._cond:
                _TASK_SCHEDULER._cond.notify_all()
        except Exception:
            pass

    def release_setup_lock(self, account_alias: str) -> None:
        """
        早期释放账号的启动初始化锁(Setup Lock)，允许同账号的下一个并发任务开始启动初始化。
        """
        with self._lock:
            if account_alias in self._active_accounts:
                self._active_accounts.remove(account_alias)
                self._active_account_started.pop(account_alias, None)
                self._active_accounts_cond.notify_all()
                _log(f"BrowserPool: early released setup lock for account '{account_alias}'")

    def _destroy_slot(self, slot_id: str) -> None:
        slot = self._slots.pop(slot_id, None)
        if not slot:
            return

        # Destroy 时自动保存最终 Session 状态，确保下次启动可以直接使用
        try:
            if slot.context and slot.account_alias:
                storage_dir = str(DATA_DIR / "storage_states") if DATA_DIR.exists() else ""
                if storage_dir:
                    state_path = os.path.join(storage_dir, f"{slot.account_alias}_state.json")
                    slot.context.storage_state(path=state_path)
                    _log(f"BrowserPool: automatically saved final storage state for {slot.account_alias}")
        except Exception as save_err:
            _log(f"BrowserPool: failed to automatically save final state for {slot.account_alias}: {save_err}", level="WARN")

        try:
            if slot.page and not slot.page.is_closed():
                slot.page.close()
        except Exception:
            pass
        try:
            if slot.context:
                slot.context.close()
        except Exception:
            pass
        try:
            if slot.browser and slot.browser.is_connected():
                slot.browser.close()
        except Exception:
            pass
        try:
            if slot.playwright:
                slot.playwright.stop()
        except Exception:
            pass
        _log(f"BrowserPool: destroyed slot {slot_id} and closed browser")

    def save_storage_state(self, slot_id: str, path: str) -> bool:
        with self._lock:
            slot = self._slots.get(slot_id)
            if not slot or not slot.context:
                return False
        
        max_retries = 5
        retry_delay = 0.5
        for attempt in range(max_retries):
            try:
                os.makedirs(os.path.dirname(path), exist_ok=True)
                with self._lock:
                    slot.context.storage_state(path=path)
                _log(f"BrowserPool: saved storage state to {path} on attempt {attempt+1}")
                return True
            except PermissionError as pe:
                _log(f"BrowserPool: save storage state permission error (attempt {attempt+1}/{max_retries}): {pe}", level="WARN")
                if attempt < max_retries - 1:
                    time.sleep(retry_delay)
                else:
                    return False
            except Exception as exc:
                _log(f"BrowserPool: save storage state general error: {exc}", level="WARN")
                return False
        return False

    def start_cleanup(self, interval_s: float = 60) -> None:
        self._stop_event.clear()
        if self._cleanup_thread and self._cleanup_thread.is_alive():
            return
        self._cleanup_thread = threading.Thread(
            target=self._cleanup_loop,
            args=(interval_s,),
            daemon=True,
            name="runwayml-browser-cleanup",
        )
        self._cleanup_thread.start()
        _log(f"BrowserPool: cleanup started, interval={interval_s}s")

    def stop_cleanup(self) -> None:
        self._stop_event.set()
        if self._cleanup_thread and self._cleanup_thread.is_alive():
            self._cleanup_thread.join(timeout=5)
        _log("BrowserPool: cleanup stopped")

    def _cleanup_loop(self, interval_s: float) -> None:
        while not self._stop_event.is_set():
            try:
                with self._lock:
                    to_evict = []
                    for slot_id, slot in self._slots.items():
                        if not slot.is_busy:
                            if not slot.is_alive:
                                to_evict.append(slot_id)
                            elif slot.idle_seconds > _BROWSER_IDLE_TIMEOUT_S:
                                to_evict.append(slot_id)
                    for slot_id in to_evict:
                        self._destroy_slot(slot_id)
                    if to_evict:
                        _log(f"BrowserPool: cleanup evicted {len(to_evict)} idle slots")
            except Exception as exc:
                _log(f"BrowserPool: cleanup error: {exc}", level="WARN")
            self._stop_event.wait(interval_s)

    def shutdown(self) -> None:
        self.stop_cleanup()
        slots_to_cancel = []
        with self._lock:
            for slot_id, slot in self._slots.items():
                if slot.is_alive:
                    slots_to_cancel.append((slot_id, slot))
                    
        if slots_to_cancel:
            _log(f"BrowserPool: starting parallel task cancellation for {len(slots_to_cancel)} active browser slots before shutdown")
            threads = []
            for slot_id, slot in slots_to_cancel:
                team_name = ""
                try:
                    acc_slot = _ACCOUNT_MGR.get_slot(slot.account_alias)
                    if acc_slot:
                        team_name = acc_slot.team_name
                except Exception:
                    pass
                t = threading.Thread(
                    target=_cancel_active_tasks_for_account,
                    args=(slot.account_alias, team_name, slot.page),
                    name=f"cancel-tasks-{slot.account_alias}"
                )
                t.daemon = True
                threads.append(t)
                t.start()
                
            _log("BrowserPool: waiting for task cancellation threads to complete...")
            start_wait = time.time()
            for t in threads:
                rem_time = max(0.1, 20.0 - (time.time() - start_wait))
                t.join(timeout=rem_time)
            _log(f"BrowserPool: finished task cancellation wait in {time.time() - start_wait:.2f}s")
            
        with self._lock:
            slot_ids = list(self._slots.keys())
            for slot_id in slot_ids:
                self._destroy_slot(slot_id)
            self._active_accounts.clear()
            self._active_account_started.clear()
            self._active_accounts_cond.notify_all()
        _log("BrowserPool: shutdown complete")

    def stats(self) -> dict[str, Any]:
        with self._lock:
            total = len(self._slots)
            busy = sum(1 for s in self._slots.values() if s.is_busy)
            alive = sum(1 for s in self._slots.values() if s.is_alive)
            return {
                "total_slots": total,
                "busy": busy,
                "idle": total - busy,
                "alive": alive,
                "max_browsers": _MAX_BROWSER_INSTANCES,
            }


_BROWSER_POOL = _BrowserPool()


def _sandboxed_input_text(locator: Any, text: str) -> None:
    page = locator.page
    try:
        locator.focus()
    except Exception:
        pass
    try:
        locator.evaluate("el => { el.focus(); el.click(); }")
    except Exception:
        pass
    page.wait_for_timeout(150)
    try:
        tag_name = locator.evaluate("el => el.tagName")
    except Exception:
        tag_name = "DIV"
        
    if tag_name in ["INPUT", "TEXTAREA"]:
        try:
            locator.fill(text)
        except Exception:
            try:
                locator.click(force=True)
            except Exception:
                pass
            page.wait_for_timeout(100)
            page.keyboard.press("Control+a")
            page.keyboard.press("Backspace")
            page.keyboard.insert_text(text)
    else:
        # It's contenteditable (like Runway prompt box).
        # We need to click/focus, select all, delete, and type/insert natively.
        try:
            locator.click(force=True)
        except Exception:
            try:
                locator.evaluate("el => { el.focus(); el.click(); }")
            except Exception:
                pass
        page.wait_for_timeout(150)
        page.keyboard.press("Control+a")
        page.keyboard.press("Backspace")
        page.wait_for_timeout(100)
        # Using insert_text is super fast and native!
        page.keyboard.insert_text(text)
    page.wait_for_timeout(150)


def _get_input_value_safe(locator: Any) -> str:
    try:
        tag_name = locator.evaluate("el => el.tagName")
        if tag_name in ["INPUT", "TEXTAREA", "SELECT"]:
            return (locator.input_value() or "").strip()
        else:
            return (locator.inner_text() or "").strip()
    except Exception:
        try:
            return (locator.inner_text() or "").strip()
        except Exception:
            return ""


def _count_current_thumbnails(page: Any) -> int:
    try:
        return page.evaluate("""() => {
            const elements = document.querySelectorAll(
                'img, video, [class*="thumbnail" i] img, [class*="preview" i] img, ' +
                '[class*="image-preview" i] img, [class*="slot-" i] img, ' +
                '[class*="upload" i] img, [data-testid*="reference" i] img, ' +
                '[class*="reference" i] img, ' +
                '[class*="thumbnail" i] video, [class*="preview" i] video, ' +
                '[class*="video-preview" i] video, [class*="slot-" i] video, ' +
                '[class*="upload" i] video, [data-testid*="reference" i] video, ' +
                '[class*="reference" i] video'
            );
            let count = 0;
            
            const emptyPatterns = ["emptystate", "empty-state", "touchpoint", "hero_comp", "product.webm", "demo/"];
            const emptyDomains = ["cloudfront.net"];
            
            function isEmptyState(url) {
                if (!url) return true;
                const lower = url.toLowerCase();
                for (const pat of emptyPatterns) {
                    if (lower.includes(pat)) return true;
                }
                for (const dom of emptyDomains) {
                    if (lower.includes(dom) && lower.includes("/app/")) return true;
                }
                return false;
            }

            for (const el of elements) {
                const tagName = el.tagName.toUpperCase();
                const src = el.src || el.currentSrc || "";
                
                if (tagName === "IMG") {
                    const isBlobOrDataOrHttp = src.startsWith("blob:") || src.startsWith("data:") || src.startsWith("http");
                    if (isBlobOrDataOrHttp && !isEmptyState(src)) {
                        if (el.complete && el.naturalWidth > 0) {
                            count++;
                        }
                    }
                } else if (tagName === "VIDEO") {
                    const isBlobOrHttp = src.startsWith("blob:") || src.startsWith("http");
                    if (isBlobOrHttp && !isEmptyState(src)) {
                        if (el.readyState >= 1 || el.duration > 0) {
                            count++;
                        }
                    }
                }
            }
            return count;
        }""")
    except Exception as e:
        _log(f"playwright: count thumbnails failed: {e}", level="WARN")
        return 0


def _clear_existing_references(page: Any) -> None:
    try:
        selectors = [
            '[class*="thumbnail" i] button',
            '[class*="preview" i] button',
            '[class*="slot-" i] button',
            '[class*="reference" i] button[aria-label*="close" i]',
            '[class*="reference" i] button[aria-label*="remove" i]',
            'button[aria-label="Remove Reference"]',
            'button[aria-label="Remove"]',
            '[data-testid*="remove" i]',
            '[class*="remove" i]',
        ]
        removed = 0
        for sel in selectors:
            try:
                btns = page.locator(sel).all()
                for btn in btns:
                    if btn.is_visible(timeout=200):
                        btn.click()
                        page.wait_for_timeout(200)
                        removed += 1
            except Exception:
                continue
        if removed > 0:
            _log(f"playwright: cleared {removed} existing reference card(s)")
    except Exception as exc:
        _log(f"playwright: clear references failed: {exc}", level="WARN")


def _wait_for_upload_confirm(page: Any, timeout_s: int = 120, poll_interval_s: float = 3.0, expected_count: int | None = None, baseline_count: int = 0) -> bool:
    deadline = time.time() + max(10, timeout_s)
    attempt = 0
    target_count = baseline_count + expected_count if expected_count is not None else baseline_count + 1
    
    while time.time() < deadline:
        attempt += 1
        page.wait_for_timeout(int(poll_interval_s * 1000))
        try:
            img_check = _count_current_thumbnails(page)
            
            ref_btn_visible = False
            ref_btn_text = ""
            try:
                ref_btn = page.locator('button[aria-label="Reference"]').first
                if ref_btn.is_visible(timeout=500):
                    ref_btn_visible = True
                    ref_btn_text = ref_btn.inner_text().strip()
            except Exception:
                pass
                
            # Check for any active upload progress or loading indicator inside upload/thumbnail cards
            has_active_loading = False
            try:
                loading_indicators = page.locator(
                    '[class*="thumbnail" i] [class*="loading" i], '
                    '[class*="thumbnail" i] [class*="progress" i], '
                    '[class*="preview" i] [class*="loading" i], '
                    '[class*="preview" i] [class*="progress" i], '
                    '[class*="upload" i] [class*="loading" i], '
                    '[class*="upload" i] [class*="progress" i], '
                    '[class*="slot-" i] [class*="loading" i], '
                    '[class*="slot-" i] [class*="progress" i], '
                    '[role="progressbar"]'
                ).all()
                for indicator in loading_indicators:
                    try:
                        if indicator.is_visible(timeout=100):
                            has_active_loading = True
                            break
                    except Exception:
                        continue
            except Exception as le_exc:
                _log(f"upload_confirm: indicator check error: {le_exc}", level="WARN")
                
            # Check network intercepted upload counts
            net_uploaded_count = getattr(page, "_uploaded_network_count", None)
            net_ok = True
            if net_uploaded_count is not None and expected_count is not None:
                if net_uploaded_count[0] < expected_count:
                    net_ok = False
                    
            elapsed = int(time.time() - (deadline - timeout_s))
            _log(f"upload_confirm: attempt {attempt}, elapsed={elapsed}s, preview_count={img_check}, target={target_count}, ref_btn_text='{ref_btn_text}', has_loading={has_active_loading}, net_ok={net_ok}")
            
            if expected_count is not None:
                # Require preview thumbnail to be rendered AND no loading states AND network upload confirmed (in Pool mode)
                if img_check >= target_count and not has_active_loading and net_ok:
                    _log(f"upload_confirm: confirmed after {elapsed}s (attempt {attempt}), count {img_check}>={target_count})")
                    return True
            else:
                if (img_check > baseline_count or (ref_btn_visible and ref_btn_text not in ("Reference", ""))) and not has_active_loading and net_ok:
                    _log(f"upload_confirm: confirmed after {elapsed}s (attempt {attempt})")
                    return True
        except Exception as exc:
            _log(f"upload_confirm: check error on attempt {attempt}: {exc}", level="WARN")
    _log(f"upload_confirm: NOT confirmed after {timeout_s}s ({attempt} attempts)", level="WARN")
    return False


def _drag_and_drop_file_via_js(page: Any, drop_target_selector: str, file_path: str, is_video: bool = False) -> bool:
    try:
        # 1. Create a temporary input element in the page
        temp_input_id = "pw_temp_file_input"
        page.evaluate(f"""() => {{
            let input = document.getElementById('{temp_input_id}');
            if (!input) {{
                input = document.createElement('input');
                input.id = '{temp_input_id}';
                input.type = 'file';
                input.style.display = 'none';
                document.body.appendChild(input);
            }}
        }}""")
        
        # 2. Set the input files on this temporary input
        temp_input = page.locator(f"#{temp_input_id}")
        temp_input.set_input_files(file_path)
        
        # 3. Dispatch the drop event using JS DataTransfer
        ok = page.evaluate(f"""() => {{
            const targets = document.querySelectorAll('{drop_target_selector}');
            const input = document.getElementById('{temp_input_id}');
            if (targets.length === 0 || !input || !input.files || input.files.length === 0) return false;
            
            const is_video = {'true' if is_video else 'false'};
            const target = is_video && targets.length > 1 ? targets[targets.length - 1] : targets[0];
            
            const dataTransfer = new DataTransfer();
            for (let i = 0; i < input.files.length; i++) {{
                dataTransfer.items.add(input.files[i]);
            }}
            
            const dragEnterEvent = new DragEvent('dragenter', {{
                bubbles: true,
                cancelable: true,
                dataTransfer: dataTransfer
            }});
            target.dispatchEvent(dragEnterEvent);
            
            const dragOverEvent = new DragEvent('dragover', {{
                bubbles: true,
                cancelable: true,
                dataTransfer: dataTransfer
            }});
            target.dispatchEvent(dragOverEvent);
            
            const dropEvent = new DragEvent('drop', {{
                bubbles: true,
                cancelable: true,
                dataTransfer: dataTransfer
            }});
            target.dispatchEvent(dropEvent);
            
            // Clean up temporary input files so we don't leak
            input.value = "";
            return true;
        }}""")
        if ok:
            _log(f"drag_drop: successfully simulated drop (is_video={is_video}) of {file_path} onto {drop_target_selector}")
            return True
        return False
    except Exception as e:
        _log(f"drag_drop: failed to drag and drop file: {e}", level="WARN")
        return False


def _upload_single_image(page: Any, image_path: str, label: str = "image", is_video: bool = False) -> bool:
    page.evaluate("() => { document.querySelectorAll('input[type=file]').forEach(el => el.removeAttribute('accept')); }")
    
    # 1. Primary: Direct input uploading targeted by is_video flag (Standard Injection Method)
    _log(f"upload_single: trying standard uploader input injection for {label} (is_video={is_video})")
    file_inputs = page.locator('input[type="file"]').all()
    if file_inputs:
        try:
            target_input = file_inputs[-1] if (is_video and len(file_inputs) > 1) else file_inputs[0]
            target_input.set_input_files(image_path)
            _log(f"upload_single: {label} uploaded via targeted file input (is_video={is_video}): {image_path}")
            return True
        except Exception as fi_exc:
            _log(f"upload_single: targeted input failed for {label}: {fi_exc}, trying other fallbacks", level="WARN")
            
        for fi in file_inputs:
            try:
                fi.set_input_files(image_path)
                _log(f"upload_single: {label} uploaded via fallback file input: {image_path}")
                return True
            except Exception:
                continue

    # 2. Fallback: Simulated W3C HTML5 Drag and Drop. Highly effective if standard inputs fail or are ignored by React handlers.
    _log(f"upload_single: trying simulated HTML5 drag & drop fallback for {label}")
    drop_selectors = [
        '[class*="dropRegion"]',
        '[class*="drop-region"]',
        '[class*="DropRegion"]',
        '[class*="upload" i]',
        '[class*="reference" i]',
        '[data-testid*="upload" i]',
    ]
    for sel in drop_selectors:
        try:
            cand = page.locator(sel).first
            if cand.is_visible(timeout=200):
                ok = _drag_and_drop_file_via_js(page, sel, image_path, is_video=is_video)
                if ok:
                    _log(f"upload_single: {label} uploaded successfully via simulated drag & drop fallback on selector: {sel}")
                    return True
        except Exception as dd_err:
            _log(f"upload_single: simulated drag & drop failed on {sel}: {dd_err}", level="DEBUG")
            continue
                
    # 3. Fallback: Click drop region and set files
    try:
        drop_regions = page.locator('[class*="dropRegion"], [class*="drop-region"], [class*="DropRegion"]').all()
        target_drop = drop_regions[-1] if (is_video and len(drop_regions) > 1) else (drop_regions[0] if drop_regions else None)
        if target_drop and target_drop.is_visible(timeout=1500):
            target_drop.click()
            page.wait_for_timeout(800)
            retry_inputs = page.locator('input[type="file"]').all()
            if retry_inputs:
                target_input = retry_inputs[-1] if (is_video and len(retry_inputs) > 1) else retry_inputs[0]
                target_input.set_input_files(image_path)
                _log(f"upload_single: {label} uploaded after clicking drop region: {image_path}")
                return True
    except Exception as drop_exc:
        _log(f"upload_single: drop region fallback failed for {label}: {drop_exc}", level="WARN")
        
    _log(f"upload_single: all methods failed for {label}: {image_path}", level="ERROR")
    return False





def _generate_via_playwright_with_slot(
    context: dict,
    params: dict[str, Any],
    prompt: str,
    first_path: str | None,
    end_path: str | None,
    model: str,
    duration_s: int,
    ratio: str,
    timeout_s: int,
    browser_slot: _BrowserSlot,
    cred: dict[str, str] | None = None,
    generation_mode: str = "multi_reference",
    all_ref_paths: list[str] | None = None,
    video_path: str | None = None,
    all_video_paths: list[str] | None = None,
) -> str:
    progress_card = RunwayProgressCard(context)
    progress_card.start()
    progress_card.update("正在悄悄启动后台浏览器... 嘘，不要打扰它睡觉。💤", "info", f"🤖 智能小助手 | {progress_card.account_label}")

    page = browser_slot.page
    if page is None or page.is_closed():
        try:
            page = browser_slot.context.new_page()
            browser_slot.page = page
        except Exception:
            raise Exception("PLUGIN_ERROR:::浏览器 slot 无有效页面且无法创建新页面")

    # 注入动态网页缩放脚本，支持根据设置缩放网页页面内容大小
    zoom_f = getattr(browser_slot, "zoom_factor", 1.0)
    zoom_auto = (
        str(params.get("playwright_zoom_factor") or params.get("playwright_scale_factor") or "auto").strip().lower() == "auto"
        and not bool(params.get("smart_arrange", False))
    )
    use_cdp_fit = False
    target_page_w = max(914, _safe_int(params.get("target_page_width"), 914))
    target_page_h = max(686, _safe_int(params.get("target_page_height"), 686))
    locked_canvas_w = target_page_w
    locked_canvas_h = target_page_h
    try:
        if zoom_f != 1.0 or use_cdp_fit:
            _log(f"playwright: registering dynamic page zoom init script to {zoom_f * 100}%")
            script = f"""
            (function() {{
                window.__RUNWAY_ZOOM_FACTOR__ = Number(window.__RUNWAY_ZOOM_FACTOR__ || {zoom_f!r});
                function applyZoom() {{
                    try {{
                        var z = Number(window.__RUNWAY_ZOOM_FACTOR__ || 1);
                        if (z > 0 && document.documentElement.style.zoom !== String(z)) {{
                            document.documentElement.style.zoom = String(z);
                        }}
                        document.documentElement.style.transformOrigin = '0 0';
                        if (document.body) {{
                            document.body.style.zoom = '';
                            document.body.style.transform = '';
                            document.body.style.transformOrigin = '';
                        }}
                    }} catch(e) {{}}
                }}
                applyZoom();
                window.addEventListener('DOMContentLoaded', applyZoom);
                window.addEventListener('load', applyZoom);
                setInterval(applyZoom, 500);
            }})();
            """
            page.add_init_script(script)
    except Exception as zoom_exc:
        _log(f"playwright: failed to add init script for zoom: {zoom_exc}", level="WARN")

    def _apply_page_zoom_now(reason: str = "") -> None:
        nonlocal zoom_f
        live = None
        if zoom_auto:
            try:
                live = page.evaluate(
                    """([targetW, targetH]) => {
                        const z = Math.max(0.45, Math.min(1.0, window.innerWidth / targetW, window.innerHeight / targetH));
                        return { zoom: z, innerWidth: window.innerWidth, innerHeight: window.innerHeight };
                    }""",
                    [target_page_w, target_page_h],
                )
                live_zoom = float(live.get("zoom") or zoom_f)
                if live_zoom > 0:
                    zoom_f = live_zoom
                    try:
                        browser_slot.zoom_factor = zoom_f
                    except Exception:
                        pass
                    _log(
                        f"playwright: live auto zoom from inner={live.get('innerWidth')}x{live.get('innerHeight')} "
                        f"→ {zoom_f * 100:.1f}%{(' after ' + reason) if reason else ''}"
                    )
            except Exception as live_zoom_exc:
                _log(f"playwright: live auto zoom calculation failed: {live_zoom_exc}", level="WARN")
        elif use_cdp_fit:
            try:
                live = page.evaluate("""() => ({ innerWidth: window.innerWidth, innerHeight: window.innerHeight })""")
            except Exception:
                live = None

        if use_cdp_fit:
            try:
                physical_w = int(getattr(browser_slot, "physical_inner_width", 0) or 0)
                physical_h = int(getattr(browser_slot, "physical_inner_height", 0) or 0)
                live_w = int((live or {}).get("innerWidth") or 0)
                live_h = int((live or {}).get("innerHeight") or 0)
                if (physical_w <= 0 or physical_h <= 0) and live_w > 0 and live_h > 0:
                    physical_w = live_w
                    physical_h = live_h
                    browser_slot.physical_inner_width = physical_w
                    browser_slot.physical_inner_height = physical_h

                if physical_w > 0 and physical_h > 0:
                    if zoom_auto:
                        # Height-first fit: width may be cropped, but the page control height must remain visible.
                        zoom_f = max(0.45, min(1.0, physical_h / float(target_page_h)))
                        browser_slot.zoom_factor = zoom_f
                    logical_w = max(target_page_w, int((physical_w / max(zoom_f, 0.01)) + 0.999))
                    logical_h = max(target_page_h, int((physical_h / max(zoom_f, 0.01)) + 0.999))
                    cdp = getattr(browser_slot, "cdp_session", None)
                    if cdp is None:
                        cdp = browser_slot.context.new_cdp_session(page)
                        browser_slot.cdp_session = cdp
                    cdp.send(
                        "Emulation.setDeviceMetricsOverride",
                        {
                            "width": logical_w,
                            "height": logical_h,
                            "deviceScaleFactor": 1,
                            "mobile": False,
                        },
                    )
                    _log(
                        f"playwright: CDP fit viewport physical={physical_w}x{physical_h} "
                        f"logical={logical_w}x{logical_h} zoom={zoom_f * 100:.1f}%"
                        f"{(' after ' + reason) if reason else ''}"
                    )
            except Exception as cdp_exc:
                _log(f"playwright: CDP fit failed{(' after ' + reason) if reason else ''}: {cdp_exc}", level="WARN")
        if zoom_f == 1.0:
            return
        try:
            page.evaluate(
                """zoomValue => {
                    try {
                        window.__RUNWAY_ZOOM_FACTOR__ = Number(zoomValue);
                        document.documentElement.style.zoom = String(zoomValue);
                        document.documentElement.style.transformOrigin = '0 0';
                        if (document.body) {
                            document.body.style.zoom = '';
                            document.body.style.transform = '';
                            document.body.style.transformOrigin = '';
                        }
                    } catch (e) {}
                }""",
                zoom_f,
            )
            try:
                zm = page.evaluate(
                    """() => ({
                        zoom: document.documentElement.style.zoom || getComputedStyle(document.documentElement).zoom,
                        innerWidth: window.innerWidth,
                        innerHeight: window.innerHeight,
                        viewportW: window.visualViewport ? window.visualViewport.width : 0,
                        viewportH: window.visualViewport ? window.visualViewport.height : 0
                    })"""
                )
                _log(
                    f"playwright: applied page zoom now {zoom_f * 100:.1f}% "
                    f"style={zm.get('zoom')} inner={zm.get('innerWidth')}x{zm.get('innerHeight')} "
                    f"visual={zm.get('viewportW')}x{zm.get('viewportH')}"
                    f"{(' after ' + reason) if reason else ''}"
                )
            except Exception:
                _log(f"playwright: applied page zoom now {zoom_f * 100:.1f}%{(' after ' + reason) if reason else ''}")
        except Exception as apply_zoom_exc:
            _log(f"playwright: apply page zoom now failed{(' after ' + reason) if reason else ''}: {apply_zoom_exc}", level="WARN")

    def _locator_text_now(locator: Any) -> str:
        try:
            txt = locator.evaluate("el => (el.innerText || el.textContent || '').trim()", timeout=3000)
            return str(txt or "").strip()
        except Exception:
            try:
                return str(locator.text_content(timeout=3000) or "").strip()
            except Exception:
                return ""

    try:
        page.set_default_navigation_timeout(120000)
        page.set_default_timeout(120000)
    except Exception as e:
        _log(f"playwright: set timeouts error: {e}", level="WARN")

    debug_save_screenshot = bool(params.get("debug_save_screenshot", True))

    model_url_map = {
        "seedance_2.0": "seedance-2",
    }
    model_label_map = {
        "seedance_2.0": ("Seedance 2.0",),
    }
    model_slug = model_url_map.get(model, "seedance-2")
    model_labels = model_label_map.get(model, ("Seedance 2.0",))
    mode_param = "keyframe" if generation_mode == "keyframe" else "tools"
    generate_url = f"{RUNWAYML_WEB_BASE}/video-tools/ai-tools/generate?tool=video&mode={mode_param}&model={model_slug}"

    _nav_jump_count = [0]
    _nav_last_good_url = [generate_url]

    def _on_frame_navigated(frame: Any) -> None:
        try:
            url = frame.url
            if frame != page.main_frame:
                return
            if "runwayml.com" not in url and "runway" not in url.lower():
                _nav_jump_count[0] += 1
                _log(f"playwright: ANTI-JUMP detected navigation away! url={url}, navigating back to {_nav_last_good_url[0]}", level="WARN")
                try:
                    page.goto(_nav_last_good_url[0], wait_until="domcontentloaded")
                except Exception:
                    pass
            elif "generate" in url.lower() or "video" in url.lower():
                _nav_last_good_url[0] = url
        except Exception:
            pass

    try:
        page.on("framenavigated", _on_frame_navigated)
    except Exception:
        pass

    def _ensure_on_generate_page(action: str = "") -> None:
        try:
            current = page.url
            if "generate" not in current.lower() and "video" not in current.lower():
                _log(f"playwright: ANTI-JUMP page off generate during {action}! current={current}, navigating back", level="WARN")
                page.goto(_nav_last_good_url[0], wait_until="domcontentloaded")
                page.wait_for_timeout(2000)
        except Exception:
            pass

    _EMPTY_STATE_DOMAINS = ("d3phaj0sisr2ct.cloudfront.net",)
    _EMPTY_STATE_PATTERNS = ("emptystate", "empty-state", "touchpoint", "hero_comp", "product.webm", "demo/")

    def _is_empty_state_video(url: str) -> bool:
        lower = url.lower()
        for pat in _EMPTY_STATE_PATTERNS:
            if pat in lower:
                return True
        for dom in _EMPTY_STATE_DOMAINS:
            if dom in lower and "/app/" in lower:
                return True
        return False

    try:
        progress_card.update("正在核对您的通行证... 看来你已经是个成熟的 Runway 玩家了！✨", "info", f"🔑 身份确认中 | {progress_card.account_label}")
        _safe_progress(context, "Playwright: 导航到生成页面")
        _log(f"playwright: navigating to {generate_url}")
        page.goto(generate_url, wait_until="domcontentloaded", timeout=120000)
        _apply_page_zoom_now("initial navigation")
        
        # 智能轮询稳定逻辑：检测关键元素是否渲染完成，期间随时清理动态弹窗
        _log("playwright: waiting for page elements to settle (supporting 40-50s slow network)")
        page_settled = False
        for _ in range(30):  # 最多轮询等待 60 秒
            if page.is_closed():
                break
            progress_card.update("网页正在伸懒腰，好像有点起床气... 咱们耐心等等它！⏰", "info", f"☕ 咖啡时间 | {progress_card.account_label}")
            _dismiss_promotional_popups(page, progress_card)
            try:
                # 检查主要控制台元素是否可见，或者已发生登录/访客重定向
                if (_is_page_settled(page) or
                    "/teams/guest/" in page.url or
                    "login" in page.url.lower() or
                    "sign-in" in page.url.lower()):
                    _log("playwright: page settled, key elements visible")
                    page_settled = True
                    break
            except Exception:
                pass
            page.wait_for_timeout(2000)

        if page.is_closed():
            raise Exception("PLUGIN_ERROR:::Runway 页面或浏览器已关闭，无法继续生成。请不要在生成过程中关闭浏览器窗口")

        current_url = page.url
        if not page_settled and "login" not in current_url.lower() and "sign-in" not in current_url.lower():
            _log(f"playwright: page did not settle after first wait, reloading once; current URL: {current_url}", level="WARN")
            try:
                page.reload(wait_until="domcontentloaded", timeout=120000)
                _apply_page_zoom_now("reload")
                for _ in range(45):
                    if page.is_closed():
                        break
                    _dismiss_promotional_popups(page, progress_card)
                    try:
                        if (_is_page_settled(page) or
                            "/teams/guest/" in page.url or
                            "login" in page.url.lower() or
                            "sign-in" in page.url.lower()):
                            _log("playwright: page settled after reload")
                            page_settled = True
                            break
                    except Exception:
                        pass
                    page.wait_for_timeout(2000)
                if not page.is_closed():
                    current_url = page.url
            except Exception as reload_exc:
                _log(f"playwright: reload after unsettled page failed: {reload_exc}", level="WARN")

        if page.is_closed():
            raise Exception("PLUGIN_ERROR:::Runway 页面或浏览器已关闭，无法继续生成。请不要在生成过程中关闭浏览器窗口")

        if (not page_settled and
            "login" not in current_url.lower() and
            "sign-in" not in current_url.lower() and
            "/teams/guest/" not in current_url):
            _debug_screenshot(page, "page_not_ready_before_upload")
            raise Exception(f"PLUGIN_ERROR:::Runway 页面未加载出生成控件，当前地址：{current_url}。请检查网络、登录状态或 Runway 页面是否白屏")

        if "runwayml.com" not in current_url and "runway" not in current_url.lower():
            _log(f"playwright: wrong site detected, current URL: {current_url}, force navigating to runwayml", level="WARN")
            page.goto(generate_url, wait_until="domcontentloaded", timeout=120000)
            _apply_page_zoom_now("fallback navigation")
            
            # 对第二次导航再次进行智能稳定检测
            _log("playwright: waiting for page elements to settle after fallback navigation")
            for _ in range(30):
                if page.is_closed():
                    break
                progress_card.update("网页正在伸懒腰，好像有点起床气... 咱们耐心等等它！⏰", "info", f"☕ 咖啡时间 | {progress_card.account_label}")
                _dismiss_promotional_popups(page, progress_card)
                try:
                    if (page.locator('[data-testid="select-base-model"]').first.is_visible(timeout=500) or
                        page.locator('textarea').first.is_visible(timeout=500) or
                        page.locator('[placeholder*="Describe" i]').first.is_visible(timeout=500) or
                        "/teams/guest/" in page.url or
                        "login" in page.url.lower() or
                        "sign-in" in page.url.lower()):
                        _log("playwright: page settled after fallback navigation")
                        break
                except Exception:
                    pass
                page.wait_for_timeout(2000)
            current_url = page.url
        team_match = re.search(r"/teams/([^/]+)/", current_url)
        if team_match and "/teams/guest/" not in current_url:
            team_name = team_match.group(1)
            generate_url = f"{RUNWAYML_WEB_BASE}/video-tools/teams/{team_name}/ai-tools/generate?tool=video&mode={mode_param}&model={model_slug}"
            _log(f"playwright: detected team '{team_name}' from redirect, updated generate_url")
            try:
                _alias = context.get("_runtime_account", {}).get("alias", "")
                if _alias:
                    _slot = _ACCOUNT_MGR.get_slot(_alias)
                    if _slot:
                        _slot.team_name = team_name
                        _log(f"playwright: updated team_name='{team_name}' for account alias={_alias}")
            except Exception:
                pass

        needs_login = False
        if "/teams/guest/" in current_url:
            needs_login = True
        elif "login" in current_url.lower() or "sign-in" in current_url.lower():
            needs_login = True
        elif "/teams/" not in current_url:
            try:
                login_btn = page.locator('[data-testid="login-button"], a:has-text("Login"), a:has-text("Log in")').first
                if login_btn.is_visible(timeout=3000):
                    needs_login = True
                    _log("playwright: no /teams/ in URL but Login button visible, treating as not logged in")
            except:
                pass

        if needs_login:
            _log("playwright: on guest page, attempting auto-login")
            _safe_progress(context, "Playwright: 检测到未登录，尝试自动登录")
            pw_account_alias = browser_slot.account_alias
            login_cred = cred
            if not login_cred or not login_cred.get("email") or not login_cred.get("password"):
                if browser_slot.email and browser_slot.password_enc:
                    login_cred = {"email": browser_slot.email, "password": browser_slot.password_enc}
                    _log(f"playwright: using email/password from browser slot for '{pw_account_alias}'")
                else:
                    login_cred = _CREDENTIAL_VAULT.get_credential(pw_account_alias)
                    _log(f"playwright: credential from vault for alias '{pw_account_alias}': found={login_cred is not None}")
                    if not login_cred or not login_cred.get("email") or not login_cred.get("password"):
                        all_aliases = _CREDENTIAL_VAULT.list_aliases()
                        for alias_key in all_aliases:
                            c = _CREDENTIAL_VAULT.get_credential(alias_key)
                            if c and c.get("email") and c.get("password"):
                                login_cred = c
                                pw_account_alias = alias_key
                                _log(f"playwright: using credentials from vault alias '{alias_key}'")
                                break
            login_ok = False
            if login_cred and login_cred.get("email") and login_cred.get("password"):
                _log(f"playwright: attempting login with email={login_cred['email'][:3]}***")
                login_ok = _auto_login_runwayml(page, login_cred["email"], login_cred["password"])
                if login_ok:
                    try:
                        storage_dir = str(DATA_DIR / "storage_states") if DATA_DIR.exists() else ""
                        if storage_dir:
                            state_path = os.path.join(storage_dir, f"{pw_account_alias}_state.json")
                            _BROWSER_POOL.save_storage_state(browser_slot.slot_id, state_path)
                            _log(f"playwright: saved login state for {pw_account_alias}")
                    except Exception as save_exc:
                        _log(f"playwright: save state failed: {save_exc}", level="WARN")
                    post_login_url = page.url
                    _log(f"playwright: post-login URL: {post_login_url}")
                    team_match = re.search(r"/teams/([^/]+)/", post_login_url)
                    if team_match:
                        team_name = team_match.group(1)
                        generate_url = f"{RUNWAYML_WEB_BASE}/video-tools/teams/{team_name}/ai-tools/generate?tool=video&mode={mode_param}&model={model_slug}"
                        _log(f"playwright: rebuilt generate_url with team: {generate_url}")
                    page.goto(generate_url, wait_until="domcontentloaded", timeout=120000)
                    _apply_page_zoom_now("login navigation")
                    
                    # 智能轮询稳定逻辑：检测关键元素是否渲染完成，期间随时清理动态弹窗
                    _log("playwright: waiting for page elements to settle after login navigation")
                    for _ in range(30):
                        if page.is_closed():
                            break
                        progress_card.update("网页正在伸懒腰，好像有点起床气... 咱们耐心等等它！⏰", "info", f"☕ 咖啡时间 | {progress_card.account_label}")
                        _dismiss_promotional_popups(page, progress_card)
                        try:
                            if (_is_page_settled(page)):
                                _log("playwright: page settled after login navigation")
                                break
                        except Exception:
                            pass
                        page.wait_for_timeout(2000)
                    current_url = page.url
            if not login_ok or "/teams/guest/" in current_url:
                _log("playwright: auto-login failed or still on guest page", level="ERROR")
                raise Exception("PLUGIN_ERROR:::自动登录失败，请检查账号管理中的邮箱和密码是否正确")
        
        _apply_page_zoom_now("before controls")
        _safe_progress(context, "Playwright: 选择模型")
        try:
            model_btn = page.locator('[data-testid="select-base-model"]').first
            if model_btn.is_visible(timeout=3000):
                current_model = model_btn.inner_text().strip()
                _log(f"playwright: current model shown: {current_model}")
                cur_norm = current_model.replace(" ", "").replace("-", "").replace(".", "").replace("/", "").lower()
                wanted_norms = [
                    label.replace(" ", "").replace("-", "").replace(".", "").replace("/", "").lower()
                    for label in model_labels
                ]
                if not any(w in cur_norm or cur_norm in w for w in wanted_norms):
                    model_btn.click()
                    page.wait_for_timeout(500)
                    model_option = None
                    for label in model_labels:
                        for opt_sel in [
                            f'[role="option"]:has-text("{label}")',
                            f'[role="menuitem"]:has-text("{label}")',
                            f'li:has-text("{label}")',
                            f'button:has-text("{label}")',
                            f'[data-testid*="model"]:has-text("{label}")',
                        ]:
                            try:
                                cand = page.locator(opt_sel).last
                                if cand.is_visible(timeout=1000):
                                    model_option = cand
                                    break
                            except Exception:
                                continue
                        if model_option:
                            break
                    if model_option:
                        model_option.click()
                        page.wait_for_timeout(500)
                        _log(f"playwright: selected model {model_labels[0]}")
                    else:
                        _log(f"playwright: model option not visible for {model} labels={model_labels}", level="WARN")
                        page.keyboard.press("Escape")
                else:
                    _log(f"playwright: model already set to {current_model}")
            else:
                _log("playwright: model selector not visible, URL param may handle it", level="WARN")
        except Exception as exc:
            _log(f"playwright: model selection failed: {exc}", level="WARN")

        _safe_progress(context, "Playwright: 切换生成类型")
        try:
            target_mode_label = "Multi-reference" if generation_mode == "multi_reference" else "Keyframe"
            _log(f"playwright: switching generation mode to '{target_mode_label}'")
            mode_tab = page.locator(f'label:has-text("{target_mode_label}")').first
            if mode_tab.is_visible(timeout=2000):
                mode_tab.click()
                page.wait_for_timeout(300)
                _log(f"playwright: clicked {target_mode_label} tab")
            else:
                _log("playwright: mode tab not found, URL param may handle it", level="WARN")
        except Exception as exc:
            _log(f"playwright: generation mode switch failed: {exc}", level="WARN")
        _dismiss_promotional_popups(page)
        _safe_progress(context, "Playwright: 预设时长")
        try:
            _log(f"playwright: pre-setting duration to {duration_s}s before aspect ratio")
            target_dur_text = f"{duration_s}s"
            duration_btn_early = None
            for dsel in [
                'button[aria-label="Duration"]',
                'button[aria-label*="duration" i]',
                f'button:has-text("{target_dur_text}")',
                'button[class*="duration" i]',
            ]:
                try:
                    dcand = page.locator(dsel).first
                    if dcand.is_visible(timeout=1200):
                        duration_btn_early = dcand
                        break
                except Exception:
                    continue
            if duration_btn_early:
                current_dur_early = _locator_text_now(duration_btn_early)
                if target_dur_text not in current_dur_early:
                    duration_btn_early.click(force=True)
                    page.wait_for_timeout(500)
                    duration_input_early = None
                    for input_sel in [
                        'input[aria-label*="duration" i]:visible',
                        'input[type="number"]:visible',
                        '[role="spinbutton"]:visible',
                        'input:visible',
                    ]:
                        try:
                            cand = page.locator(input_sel).first
                            if cand.is_visible(timeout=1500):
                                duration_input_early = cand
                                break
                        except Exception:
                            continue
                    if duration_input_early:
                        duration_input_early.click(force=True)
                        try:
                            duration_input_early.fill(str(duration_s))
                        except Exception:
                            page.keyboard.press("Control+A")
                            page.keyboard.type(str(duration_s))
                        page.keyboard.press("Enter")
                        page.wait_for_timeout(300)
                        page.keyboard.press("Escape")
                        page.wait_for_timeout(200)
                        try:
                            page.mouse.click(8, 8)
                        except Exception:
                            pass
                        _log(f"playwright: pre-set duration to {target_dur_text}")
                else:
                    _log(f"playwright: duration already {target_dur_text}")
            else:
                _log("playwright: early duration button not found; later duration step will retry", level="WARN")
        except Exception as exc:
            _log(f"playwright: early duration setting failed: {exc}", level="WARN")

        _safe_progress(context, "Playwright: 设置画幅比例")
        try:
            ratio_display = ratio.replace("1280:720", "16:9").replace("720:1280", "9:16").replace("960:960", "1:1").replace("1104:832", "4:3").replace("832:1104", "3:4").replace("1584:672", "21:9").replace("672:1584", "9:16")
            _log(f"playwright: setting aspect ratio to {ratio_display}")
            ratio_btn = None
            for rsel in [
                'button[aria-label="Aspect ratio"]',
                'button[aria-label*="aspect" i]',
                'button[aria-label*="ratio" i]',
                f'button:has-text("{ratio_display}")',
                'button[class*="ratio" i]',
                'button[class*="aspect" i]',
            ]:
                try:
                    rcand = page.locator(rsel).first
                    if rcand.is_visible(timeout=1000):
                        ratio_btn = rcand
                        _log(f"playwright: found ratio button with selector: {rsel}")
                        break
                except Exception:
                    continue
            if not ratio_btn:
                _log("playwright: trying text-based ratio detection", level="WARN")
                try:
                    all_btns = page.locator("button:visible").all()
                    for b in all_btns[:20]:
                        try:
                            txt = b.inner_text().strip()
                            if ":" in txt and any(r in txt for r in [":16", ":9", ":1", ":3", ":4"]):
                                ratio_btn = b
                                _log(f"playwright: found ratio button by text: '{txt}'")
                                break
                        except Exception:
                            continue
                except Exception:
                    pass
            if ratio_btn:
                current_ratio = _locator_text_now(ratio_btn)
                if ratio_display not in current_ratio:
                    ratio_btn.click()
                    page.wait_for_timeout(500)
                    ratio_option = None
                    for opt_sel in [
                        f'text=/^{re.escape(ratio_display)}$/',
                        f'[role="option"]:has-text("{ratio_display}")',
                        f'[role="menuitem"]:has-text("{ratio_display}")',
                        f'li:has-text("{ratio_display}")',
                        f'button:has-text("{ratio_display}")',
                    ]:
                        try:
                            cand = page.locator(opt_sel).last
                            if cand.is_visible(timeout=1200):
                                ratio_option = cand
                                break
                        except Exception:
                            continue
                    if ratio_option:
                        ratio_option.click()
                        page.wait_for_timeout(300)
                        _log(f"playwright: set ratio to {ratio_display}")
                    else:
                        _log(f"playwright: {ratio_display} option not visible; keeping current ratio instead of choosing a wrong fallback", level="WARN")
                        page.keyboard.press("Escape")
                else:
                    _log(f"playwright: ratio already {ratio_display}")
            else:
                _log("playwright: ratio button not found", level="WARN")
        except Exception as exc:
            _log(f"playwright: aspect ratio setting failed: {exc}", level="WARN")

        _safe_progress(context, "Playwright: 预检测账号可用性")
        _log("playwright: pre-check: entering test prompt to verify account availability")
        try:
            prompt_input = None
            prompt_selectors = [
                '[role="textbox"][aria-label="Prompt"]',
                '[role="textbox"][contenteditable="true"]',
                '[contenteditable="true"][class*="textbox"]',
                '[contenteditable="true"][class*="prompt" i]',
                '[contenteditable="true"][class*="input" i]',
                'textarea[placeholder*="rompt" i]',
                'div[contenteditable="true"]',
                '[role="textbox"]',
            ]
            for psel in prompt_selectors:
                try:
                    pcand = page.locator(psel).first
                    if pcand.is_visible(timeout=2000):
                        prompt_input = pcand
                        _log(f"playwright: pre-check found prompt input with selector: {psel}")
                        break
                except Exception:
                    continue
            if not prompt_input:
                _log("playwright: pre-check could not find prompt input, trying click-based detection", level="WARN")
                try:
                    page.wait_for_timeout(3000)
                    editable = page.locator('[contenteditable="true"]')
                    count = editable.count()
                    _log(f"playwright: pre-check found {count} contenteditable elements")
                    for i in range(min(count, 5)):
                        el = editable.nth(i)
                        try:
                            if el.is_visible(timeout=1000):
                                bb = el.bounding_box()
                                tag = el.evaluate("el => el.tagName")
                                cls = el.get_attribute("class") or ""
                                _log(f"playwright: pre-check contenteditable[{i}] tag={tag} class={cls[:60]} bbox={bb}")
                                if bb and bb["width"] > 100 and bb["height"] > 40:
                                    prompt_input = el
                                    _log(f"playwright: pre-check using contenteditable[{i}] as prompt input")
                                    break
                        except Exception:
                            continue
                except Exception as pexc:
                    _log(f"playwright: pre-check click-based detection failed: {pexc}", level="WARN")

            if prompt_input and prompt_input.is_visible(timeout=3000):
                _ensure_on_generate_page("prompt input")
                try:
                    _sandboxed_input_text(prompt_input, _PRECHECK_TEST_PROMPT)
                except Exception as _e_pre:
                    _log(f"playwright: pre-check sandboxed input failed: {_e_pre}, using fallback", level="WARN")
                    try:
                        prompt_input.click()
                        page.wait_for_timeout(300)
                        page.keyboard.press("Control+a")
                        page.keyboard.press("Backspace")
                        page.keyboard.type(_PRECHECK_TEST_PROMPT, delay=10)
                    except Exception:
                        pass
                page.wait_for_timeout(3000)

                wait_deadline = time.time() + _PRECHECK_MAX_WAIT_SECONDS
                account_available = False
                block_reason = "初始化检测"
                is_first_loop = True

                _log("playwright: entering in-browser pre-check availability wait loop (max 50 mins, poll every 10s)...")
                while time.time() < wait_deadline:
                    if page.is_closed() or not browser_slot.is_alive:
                        raise Exception("PLUGIN_ERROR:::浏览器或页面已被手动关闭，任务终止")

                    if not is_first_loop:
                        try:
                            current_val = _get_input_value_safe(prompt_input)
                            if not current_val or current_val != _PRECHECK_TEST_PROMPT:
                                _sandboxed_input_text(prompt_input, _PRECHECK_TEST_PROMPT)
                        except Exception:
                            pass

                    if is_first_loop and debug_save_screenshot:
                        try:
                            ts = datetime.now().strftime("%Y%m%d_%H%M%S")
                            pre_ss = str(plugin_dir / f"_debug_precheck_{ts}.png")
                            page.screenshot(path=pre_ss)
                            _log(f"playwright: pre-check screenshot saved: {pre_ss}")
                        except Exception:
                            pass

                    generate_btn_pre = None
                    all_candidates = []
                    for sel in [
                        'button:has-text("Generate"):not(:has-text("Sign")):not(:has-text("Log"))',
                        'button[data-testid*="generate"]',
                        'button[class*="primaryButton"]',
                        'button[class*="generate" i]',
                        'button[aria-label*="Generate" i]',
                        'text=Generate >> visible=true >> button',
                        ':text-is("Generate") >> button:visible',
                        'button >> text=/^Generate$/',
                        '[role="button"]:has-text("Generate")',
                        'div[role="button"]:has-text("Generate")',
                        '*[class*="generate" i]:has-text("Generate")',
                        'button:visible >> text=Generate',
                    ]:
                        try:
                            candidates = page.locator(sel).all()
                            for c in candidates:
                                try:
                                    if c.is_visible(timeout=500):
                                        bbox = c.bounding_box()
                                        txt = c.inner_text().strip()[:30]
                                        tag = c.evaluate("el => el.tagName")
                                        all_candidates.append({
                                            "sel": sel,
                                            "loc": c,
                                            "bbox": bbox,
                                            "text": txt,
                                            "tag": tag,
                                        })
                                except Exception:
                                    continue
                        except Exception:
                            continue

                    button_candidates = [c for c in all_candidates if c["tag"] == "BUTTON" and c["text"].strip() == "Generate"]

                    generate_btn_pre = None
                    if len(button_candidates) >= 1:
                        best_btn = None
                        for cand in button_candidates:
                            bb = cand["bbox"]
                            if bb and bb["width"] > 50 and bb["height"] > 25:
                                if best_btn is None:
                                    best_btn = cand
                                elif bb["y"] > (best_btn["bbox"]["y"] or 0):
                                    best_btn = cand
                        if best_btn:
                            generate_btn_pre = best_btn["loc"]
                    elif len(all_candidates) == 1:
                        generate_btn_pre = all_candidates[0]["loc"]

                    account_available = True
                    block_reason = ""

                    if generate_btn_pre:
                        try:
                            if generate_btn_pre.is_disabled():
                                account_available = False
                                block_reason = "button is_disabled=True"
                        except Exception:
                            pass

                        if account_available:
                            try:
                                disabled_attr = generate_btn_pre.get_attribute("disabled")
                                if disabled_attr is not None:
                                    account_available = False
                                    block_reason = f"disabled attr present: {disabled_attr}"
                            except Exception:
                                pass

                        if account_available:
                            try:
                                aria_disabled = generate_btn_pre.get_attribute("aria-disabled")
                                if aria_disabled and aria_disabled.lower() == "true":
                                    account_available = False
                                    block_reason = "aria-disabled=true"
                            except Exception:
                                pass

                        if account_available:
                            try:
                                btn_class = generate_btn_pre.get_attribute("class") or ""
                                cls_lower = btn_class.lower()
                                if "disabled" in cls_lower or "muted" in cls_lower or "inactive" in cls_lower:
                                    account_available = False
                                    block_reason = f"CSS class contains disabled/muted"
                            except Exception:
                                pass

                        if account_available:
                            try:
                                opacity = generate_btn_pre.evaluate("el => window.getComputedStyle(el).opacity")
                                pointer_events = generate_btn_pre.evaluate("el => window.getComputedStyle(el).pointerEvents")
                                background = generate_btn_pre.evaluate("el => window.getComputedStyle(el).backgroundColor")
                                color = generate_btn_pre.evaluate("el => window.getComputedStyle(el).color")

                                def _parse_rgb(css_color):
                                    m = re.search(r'rgb[a]?\((\d+)[,\s]+(\d+)[,\s]+(\d+)', css_color or "")
                                    if m:
                                        return int(m.group(1)), int(m.group(2)), int(m.group(3))
                                    return None

                                bg_rgb = _parse_rgb(background)
                                txt_rgb = _parse_rgb(color)
                                is_disabled_by_color = False
                                color_detail = ""

                                if bg_rgb:
                                    r, g, b = bg_rgb
                                    brightness = (r + g + b) / 3.0
                                    deviation = ((abs(r - brightness) + abs(g - brightness) + abs(b - brightness)) / 3.0)
                                    is_achromatic = deviation < 18
                                    is_very_light = brightness > 225
                                    if is_very_light and is_achromatic:
                                        is_disabled_by_color = True
                                        color_detail = f"灰白背景({r},{g},{b})"

                                if not is_disabled_by_color and txt_rgb and bg_rgb:
                                    tr, tg, tb = txt_rgb
                                    txt_brightness = (tr + tg + tb) / 3.0
                                    br, bg_val, bb = bg_rgb
                                    bg_brightness = (br + bg_val + bb) / 3.0
                                    if txt_brightness < 140 and bg_brightness > 220:
                                        is_disabled_by_color = True
                                        color_detail = "深色文字+浅背景"

                                if is_disabled_by_color:
                                    account_available = False
                                    block_reason = f"按钮呈灰色不可用({color_detail})"
                                elif opacity and float(opacity) < 0.5:
                                    account_available = False
                                    block_reason = f"opacity={opacity}"
                                elif pointer_events and pointer_events == "none":
                                    account_available = False
                                    block_reason = "pointer-events=none"
                            except Exception:
                                pass

                        if not account_available:
                            try:
                                tooltip_texts = []
                                tooltip_els = page.locator('[role="tooltip"], [data-state="delayed-open"], [data-radix-tooltip-content], [class*="Tooltip"], [class*="tooltip"]').all()
                                for tel in tooltip_els:
                                    try:
                                        if tel.is_visible(timeout=100):
                                            tt = tel.inner_text().strip()
                                            if tt and len(tt) < 300:
                                                tooltip_texts.append(tt)
                                    except Exception:
                                        continue
                                try:
                                    title_attr = generate_btn_pre.get_attribute("title") or ""
                                    if title_attr:
                                        tooltip_texts.append(title_attr)
                                except Exception:
                                    pass
                                if tooltip_texts:
                                    block_reason += f" | tooltips: {tooltip_texts[:3]}"
                            except Exception:
                                pass
                    else:
                        account_available = False
                        block_reason = "未找到 Generate 按钮"

                    _log(f"playwright: pre-check result: account_available={account_available}, reason={block_reason}")

                    if account_available:
                        _log("playwright: pre-check passed, account is available!")
                        break

                    is_first_loop = False
                    _log(f"playwright: account unavailable ({block_reason}), waiting 10 seconds before re-check...")
                    page.wait_for_timeout(_PRECHECK_POLL_INTERVAL_MS)

                # Clear the test prompt
                try:
                    prompt_input.click()
                    page.wait_for_timeout(200)
                    page.keyboard.press("Control+a")
                    page.keyboard.press("Backspace")
                    page.wait_for_timeout(500)
                    _pc_val = _get_input_value_safe(prompt_input)
                    if _pc_val:
                        prompt_input.click()
                        page.wait_for_timeout(200)
                        page.keyboard.press("Control+a")
                        page.keyboard.press("Backspace")
                        page.wait_for_timeout(500)
                except Exception as clear_exc:
                    _log(f"playwright: pre-check clear test prompt failed: {clear_exc}", level="WARN")

                if not account_available:
                    _log(f"playwright: pre-check FAILED - account unavailable after 50 mins ({block_reason})", level="WARN")
                    raise Exception(
                        f"PLUGIN_ERROR:::账号 Generate 按钮 50 分钟内一直不可用（{block_reason}）。"
                        "该账号可能被用户手动打开的 Runway 任务占用，或官方并发通道仍未释放"
                    )
                _log("playwright: pre-check PASSED - account is available")
            else:
                _log("playwright: pre-check could not find prompt input, skipping check", level="WARN")
        except Exception as exc:
            if "PLUGIN_ERROR" in str(exc):
                raise
            _log(f"playwright: pre-check failed: {exc}", level="WARN")
        _safe_progress(context, "Playwright: 设置时长")
        try:
            _log(f"playwright: setting duration to {duration_s}s (from params)")
            duration_btn = None
            target_dur_text = f"{duration_s}s"
            for dsel in [
                'button[aria-label="Duration"]',
                'button[aria-label*="duration" i]',
                'button[aria-label*="Duration" i]',
                f'button:has-text("{target_dur_text}")',
                'button[class*="duration" i]',
                'button:has-text("s")',
            ]:
                try:
                    dcand = page.locator(dsel).first
                    if dcand.is_visible(timeout=1000):
                        duration_btn = dcand
                        _log(f"playwright: found duration button with selector: {dsel}")
                        break
                except Exception:
                    continue
            if not duration_btn:
                _log("playwright: trying text-based duration detection", level="WARN")
                try:
                    all_btns2 = page.locator("button:visible").all()
                    for b in all_btns2[:20]:
                        try:
                            txt = b.inner_text().strip()
                            if re.match(r'^\d+s$', txt) or txt.endswith("s") and txt[:-1].isdigit():
                                duration_btn = b
                                _log(f"playwright: found duration button by text: '{txt}'")
                                break
                        except Exception:
                            continue
                except Exception:
                    pass
            if duration_btn:
                current_dur = _locator_text_now(duration_btn)
                if target_dur_text not in current_dur:
                    duration_btn.click(force=True)
                    page.wait_for_timeout(500)
                    duration_input = None
                    for input_sel in [
                        'input[aria-label*="duration" i]:visible',
                        'input[type="number"]:visible',
                        '[role="spinbutton"]:visible',
                        'input:visible',
                        '[role="textbox"]:visible',
                    ]:
                        try:
                            for cand in page.locator(input_sel).all()[:10]:
                                try:
                                    box = cand.bounding_box()
                                    if not box:
                                        continue
                                    if box.get("width", 999) <= 140 and box.get("height", 999) <= 80:
                                        duration_input = cand
                                        _log(f"playwright: found duration input with selector: {input_sel} box={box}")
                                        break
                                except Exception:
                                    continue
                            if duration_input:
                                break
                        except Exception:
                            continue
                    if duration_input:
                        duration_input.click(force=True)
                        try:
                            duration_input.fill(str(duration_s))
                        except Exception:
                            page.keyboard.press("Control+A")
                            page.keyboard.type(str(duration_s))
                        page.keyboard.press("Enter")
                        page.wait_for_timeout(300)
                        page.keyboard.press("Escape")
                        page.wait_for_timeout(200)
                        try:
                            page.mouse.click(8, 8)
                        except Exception:
                            pass
                        verified = False
                        new_dur = ""
                        for _dur_check in range(4):
                            page.wait_for_timeout(500)
                            new_dur = _locator_text_now(duration_btn)
                            if target_dur_text in new_dur:
                                verified = True
                                break
                        if verified:
                            _log(f"playwright: set duration to {target_dur_text}")
                        else:
                            _log(f"playwright: duration input submitted {duration_s}, current button text is '{new_dur}'", level="WARN")
                    else:
                        _log(f"playwright: duration input not found after opening Duration panel; keeping current duration", level="WARN")
                        page.keyboard.press("Escape")
                else:
                    _log(f"playwright: duration already {target_dur_text}")
            else:
                _log("playwright: duration button not found", level="WARN")
        except Exception as exc:
            _log(f"playwright: duration setting failed: {exc}", level="WARN")

        upload_paths = all_ref_paths if all_ref_paths else ([first_path] if first_path else [])
        upload_paths = [p for p in upload_paths if p]
        uploaded = False

        if upload_paths or video_path:
            _ensure_on_generate_page("upload references")
            try:
                ref_btn = page.locator('button[aria-label="Reference"]').first
                if ref_btn.is_visible(timeout=2000):
                    ref_btn.click()
                    page.wait_for_timeout(500)
                    _log("playwright: clicked Reference button to prepare for clearing references")
                _clear_existing_references(page)
            except Exception as e:
                _log(f"playwright: pre-upload references clear failed: {e}", level="WARN")

        if upload_paths:
            _ensure_on_generate_page("upload references")
            _safe_progress(context, f"Playwright: 上传参考图片（共{len(upload_paths)}张）")
            try:
                # Register network upload interceptor to trace real cloud uploads (S3/uploads API)
                _uploaded_network_count = [0]
                def _on_upload_response(response):
                    try:
                        url = response.url
                        method = response.request.method
                        status = response.status
                        if method in ("POST", "PUT") and status in (200, 201, 204):
                            if any(kw in url.lower() for kw in ("upload", "s3.amazonaws.com", "runwayml-uploads", "multipart")):
                                _uploaded_network_count[0] += 1
                                _log(f"playwright: NET intercepted successful upload response: {url} status={status}, total={_uploaded_network_count[0]}")
                    except Exception as e:
                        pass
                page.on("response", _on_upload_response)
                page._uploaded_network_count = _uploaded_network_count

                confirmed_count = 0
                for idx, img_path in enumerate(upload_paths):
                    img_label = f"ref_{idx+1}/{len(upload_paths)}"
                    progress_card.update(
                        f"正在努力喂图中，第 {idx+1}/{len(upload_paths)} 张。大口点，别噎着... 🍖",
                        "info",
                        f"🍖 正在喂图 | {progress_card.account_label}"
                    )
                    _safe_progress(context, f"Playwright: 上传第{idx+1}张参考图片（共{len(upload_paths)}张）")
                    
                    baseline_count = _count_current_thumbnails(page)
                    ok = _upload_single_image(page, img_path, label=img_label)
                    if ok:
                        # Wait for cloud network completion + local thumbnail previews + DOM loader check
                        confirmed = _wait_for_upload_confirm(page, timeout_s=120, poll_interval_s=3.0, expected_count=1, baseline_count=baseline_count)
                        if confirmed:
                            confirmed_count += 1
                            _log(f"playwright: {img_label} upload confirmed")
                            progress_card.update(
                                f"第 {idx+1} 张图已成功吃饱，消化系统非常完美！👍",
                                "info",
                                f"😋 消化完毕 | {progress_card.account_label}"
                            )
                            _safe_progress(context, f"Playwright: 第{idx+1}张图片上传成功（{confirmed_count}/{len(upload_paths)}）")
                        else:
                            _log(f"playwright: {img_label} upload NOT confirmed after 120s", level="WARN")
                            progress_card.update(
                                f"糟糕，第 {idx+1} 张图有点消化不良，确认超时了... 🤢",
                                "warning",
                                f"🤢 上传超时 | {progress_card.account_label}"
                            )
                            _safe_progress(context, f"Playwright: 第{idx+1}张图片上传确认超时")
                    else:
                        _log(f"playwright: {img_label} upload failed entirely", level="ERROR")
                        progress_card.update(
                            f"糟糕，第 {idx+1} 张图上传失败，被卡在食道了！😭",
                            "error",
                            f"😭 上传失败 | {progress_card.account_label}"
                        )
                        _safe_progress(context, f"Playwright: 第{idx+1}张图片上传失败")
                    if idx < len(upload_paths) - 1:
                        # Increased stabilization wait to 2000ms for slow networks
                        page.wait_for_timeout(2000)

                uploaded = confirmed_count > 0
                _log(f"playwright: upload summary: {confirmed_count}/{len(upload_paths)} confirmed")
                if upload_paths and confirmed_count < len(upload_paths):
                    _log(f"playwright: {len(upload_paths) - confirmed_count} images failed to upload, retrying once", level="WARN")
                    _safe_progress(context, f"Playwright: 重试未成功的图片上传（{len(upload_paths) - confirmed_count}/{len(upload_paths)}）")
                    for _retry_idx, _retry_path in enumerate(upload_paths):
                        try:
                            _ref_els = page.locator('[class*="thumbnail" i], [class*="preview" i], [class*="upload" i] img, [data-testid*="reference"] img').all()
                            if len(_ref_els) >= len(upload_paths):
                                continue
                            baseline_count2 = _count_current_thumbnails(page)
                            _ok2 = _upload_single_image(page, _retry_path, label=f"retry_{_retry_idx+1}")
                            if _ok2:
                                _safe_progress(context, f"Playwright: 等待第{_retry_idx+1}张重传图片上传完成...")
                                confirmed2 = _wait_for_upload_confirm(page, timeout_s=150, poll_interval_s=3.0, expected_count=1, baseline_count=baseline_count2)
                                if confirmed2:
                                    confirmed_count += 1
                                    _log(f"playwright: retry upload {_retry_idx+1} confirmed")
                        except Exception as _re_exc:
                            _log(f"playwright: retry upload {_retry_idx+1} error: {_re_exc}", level="WARN")
                    uploaded = confirmed_count > 0
                    _log(f"playwright: after retry: {confirmed_count}/{len(upload_paths)} confirmed")
                # Strict check: If image uploads are required but not all successfully confirmed, raise Exception immediately!
                if upload_paths and confirmed_count < len(upload_paths):
                    _log(f"playwright: only {confirmed_count}/{len(upload_paths)} images confirmed uploaded, aborting prompt entry", level="ERROR")
                    _safe_progress(context, "Playwright: ❌ 图片未全部上传成功，放弃当前生成")
                    raise Exception(f"PLUGIN_ERROR:::图片未全部上传成功并确认（仅确认 {confirmed_count}/{len(upload_paths)} 张），无法生成视频")
            except Exception as exc:
                _log(f"playwright: file upload failed: {exc}", level="WARN")
                if upload_paths:
                    _safe_progress(context, "Playwright: ❌ 图片上传抛出异常，放弃当前生成")
                    raise Exception(f"PLUGIN_ERROR:::图片上传发生严重错误（{exc}），无法生成视频")

        # Determine video paths to upload (supporting multiple video inputs)
        vids_to_upload = all_video_paths if all_video_paths else ([video_path] if video_path else [])
        vids_to_upload = [p for p in vids_to_upload if p]

        if vids_to_upload:
            _ensure_on_generate_page("upload reference video")
            _safe_progress(context, f"Playwright: 上传参考视频（共{len(vids_to_upload)}个）")
            try:
                for v_idx, v_path in enumerate(vids_to_upload):
                    v_label = f"video_{v_idx+1}/{len(vids_to_upload)}"
                    progress_card.update(
                        f"正在喂第 {v_idx+1}/{len(vids_to_upload)} 个参考视频，大块头，慢慢嚼... 🎬",
                        "info",
                        f"🎬 正在上传视频 | {progress_card.account_label}"
                    )
                    _safe_progress(context, f"Playwright: 上传第{v_idx+1}个参考视频 ({os.path.basename(v_path)})")

                    baseline_count = _count_current_thumbnails(page)
                    ok = _upload_single_image(page, v_path, label=v_label, is_video=True)
                    if ok:
                        confirmed = _wait_for_upload_confirm(page, timeout_s=180, poll_interval_s=3.0, expected_count=1, baseline_count=baseline_count)
                        if confirmed:
                            _log(f"playwright: {v_label} upload confirmed")
                            progress_card.update(
                                f"第 {v_idx+1} 个参考视频上传成功！🎬 营养吸收完毕！",
                                "info",
                                f"😋 视频吸收成功 | {progress_card.account_label}"
                            )
                            _safe_progress(context, f"Playwright: 第{v_idx+1}个参考视频上传成功")
                        else:
                            _log(f"playwright: {v_label} upload confirmation timed out, aborting", level="ERROR")
                            progress_card.update(
                                f"第 {v_idx+1} 个视频确认超时了！😭 请确保网络顺畅",
                                "error",
                                f"😭 视频超时 | {progress_card.account_label}"
                            )
                            _safe_progress(context, f"Playwright: ❌ 第{v_idx+1}个视频确认超时，放弃生成")
                            raise Exception(f"PLUGIN_ERROR:::参考视频 {v_label} 上传成功但未能在规定时间内确认，无法生成视频")
                    else:
                        _log(f"playwright: {v_label} upload failed", level="ERROR")
                        progress_card.update(
                            f"第 {v_idx+1} 个视频上传失败了！😭",
                            "error",
                            f"😭 视频上传失败 | {progress_card.account_label}"
                        )
                        _safe_progress(context, f"Playwright: ❌ 第{v_idx+1}个视频上传失败，放弃生成")
                        raise Exception(f"PLUGIN_ERROR:::参考视频 {v_label} 上传失败")
                    
                    if v_idx < len(vids_to_upload) - 1:
                        page.wait_for_timeout(2000)
            except Exception as exc:
                _log(f"playwright: reference video upload failed: {exc}", level="WARN")
                if "PLUGIN_ERROR" in str(exc):
                    raise
                _safe_progress(context, f"Playwright: ❌ 视频上传抛出异常 ({exc})，放弃当前生成")
                raise Exception(f"PLUGIN_ERROR:::参考视频上传发生严重错误（{exc}），无法生成视频")

        _safe_progress(context, "Playwright: 设置提示词")
        try:
            prompt_input = page.locator('[role="textbox"][aria-label="Prompt"]').first
            if prompt and prompt_input.is_visible(timeout=3000):
                progress_card.update(
                    "正在为您输入神级提示词，字字珠玑，字字千金！🔮",
                    "info",
                    f"🔮 吟唱咒语 | {progress_card.account_label}"
                )
                try:
                    _sandboxed_input_text(prompt_input, prompt)
                    _log(f"playwright: prompt sandboxed input success ({len(prompt)} chars)")
                except Exception as _e_prompt:
                    _log(f"playwright: prompt sandboxed input failed: {_e_prompt}, using fallback", level="WARN")
                    try:
                        prompt_input.click()
                        page.wait_for_timeout(200)
                        page.keyboard.press("Control+a")
                        page.keyboard.press("Backspace")
                        try:
                            page.evaluate(f"() => {{ navigator.clipboard.writeText({json.dumps(prompt)}); }}")
                            page.keyboard.press("Control+v")
                            _log(f"playwright: prompt pasted ({len(prompt)} chars)")
                        except Exception:
                            page.keyboard.type(prompt, delay=5)
                            _log(f"playwright: prompt typed ({len(prompt)} chars)")
                    except Exception:
                        pass
                page.wait_for_timeout(500)
                try:
                    page.evaluate('() => { const el = document.querySelector(\'[role="textbox"][aria-label="Prompt"]\'); if(el) el.blur(); }')
                    _log("playwright: blurred prompt input to dismiss @ mention autocomplete")
                except Exception:
                    pass
                try:
                    page.evaluate('() => { const el = document.querySelector(\'[role="textbox"][contenteditable="true"]\'); if(el) el.blur(); }')
                    _log("playwright: blurred contenteditable prompt input")
                except Exception:
                    pass
                page.keyboard.press("Escape")
                page.wait_for_timeout(800)
                try:
                    autocomplete = page.locator('[role="listbox"], [class*="mention" i], [class*="autocomplete" i], [class*="suggestion" i], [class*="dropdown" i]').all()
                    for ac in autocomplete:
                        try:
                            if ac.is_visible(timeout=300):
                                ac.evaluate("el => el.remove()")
                                _log("playwright: removed @ mention autocomplete dropdown from DOM")
                                break
                        except Exception:
                            continue
                except Exception:
                    pass
                try:
                    remaining_popups = page.locator('[role="listbox"], [role="menu"], [class*="mention" i], [class*="autocomplete" i], [class*="suggestion" i], [class*="dropdown" i], [class*="popover" i], [class*="tooltip" i]').all()
                    for rp in remaining_popups:
                        try:
                            if rp.is_visible(timeout=200):
                                rp.evaluate("el => { el.style.display = 'none'; el.style.visibility = 'hidden'; }")
                                _log("playwright: hidden remaining popup/overlay that could block Generate button")
                        except Exception:
                            continue
                except Exception:
                    pass
        except Exception as exc:
            _log(f"playwright: prompt input failed: {exc}", level="WARN")

        _prompt_verified = False
        if prompt:
            page.wait_for_timeout(2000)
            _safe_progress(context, "Playwright: 校验提示词写入")
            for _pv_retry in range(3):
                try:
                    _pi = page.locator('[role="textbox"][aria-label="Prompt"]').first
                    if _pi.is_visible(timeout=3000):
                        _actual = _get_input_value_safe(_pi)
                        if len(_actual) >= min(len(prompt), 10):
                            _prompt_verified = True
                            _log(f"playwright: prompt verified ({len(_actual)} chars)")
                            break
                        else:
                            _log(f"playwright: prompt verification retry {_pv_retry+1}/3, got {len(_actual)} chars", level="WARN")
                            try:
                                _sandboxed_input_text(_pi, prompt)
                            except Exception as _e_pv:
                                _log(f"playwright: prompt verify sandboxed input failed: {_e_pv}, using fallback", level="WARN")
                                try:
                                    _pi.click()
                                    page.wait_for_timeout(500)
                                    page.keyboard.press("Control+a")
                                    page.keyboard.press("Backspace")
                                    page.wait_for_timeout(500)
                                    page.evaluate(f"() => {{ navigator.clipboard.writeText({json.dumps(prompt)}); }}")
                                    page.keyboard.press("Control+v")
                                except Exception:
                                    try:
                                        page.keyboard.type(prompt, delay=5)
                                    except Exception:
                                        pass
                            page.wait_for_timeout(2000)
                except Exception as _pv_exc:
                    _log(f"playwright: prompt verify error retry {_pv_retry+1}/3: {_pv_exc}", level="WARN")
                page.wait_for_timeout(2000)
            if not _prompt_verified:
                _log("playwright: prompt verification FAILED after 3 retries, raising exception to trigger failover/retry", level="ERROR")
                _safe_progress(context, "Playwright: ❌ 提示词校验未通过，放弃当前生成")
                raise Exception("PLUGIN_ERROR:::提示词校验未通过，未能正确/完整写入提示词")
            else:
                _safe_progress(context, "Playwright: ✅ 提示词已确认写入")



        _safe_progress(context, "Playwright: 点击生成")
        try:
            generate_selectors = [
                'button:has-text("Generate"):not(:has-text("Sign")):not(:has-text("Log"))',
                'button[data-testid*="generate"]',
                'button[class*="primaryButton"]',
                'button[class*="generate" i]',
                'button[aria-label*="Generate" i]',
                'button[aria-label*="generate" i]',
            ]
            generate_btn = None
            for sel in generate_selectors:
                try:
                    candidate = page.locator(sel).first
                    if candidate.is_visible(timeout=2000):
                        generate_btn = candidate
                        _log(f"playwright: found Generate button with selector: {sel}")
                        break
                except Exception:
                    continue

            if generate_btn:
                try:
                    btn_text = generate_btn.inner_text().strip()[:50]
                    btn_disabled_attr = generate_btn.get_attribute("disabled")
                    btn_aria_disabled = generate_btn.get_attribute("aria-disabled")
                    _log(f"playwright: Generate button info: text={btn_text}, disabled={btn_disabled_attr}, aria_disabled={btn_aria_disabled}")
                except Exception:
                    pass

                is_concurrent_blocked = False
                block_reason = ""
                try:
                    generate_btn.hover(timeout=3000)
                    page.wait_for_timeout(1500)
                    tooltip_texts = []
                    try:
                        tooltip_els = page.locator('[role="tooltip"], [data-state="delayed-open"], [data-radix-tooltip-content], [class*="Tooltip"], [class*="tooltip"]').all()
                        for tel in tooltip_els:
                            try:
                                if tel.is_visible(timeout=500):
                                    tt = tel.inner_text().strip()
                                    if tt and len(tt) < 300:
                                        tooltip_texts.append(tt)
                            except Exception:
                                continue
                    except Exception:
                        pass
                    try:
                        title_attr = generate_btn.get_attribute("title") or ""
                        if title_attr:
                            tooltip_texts.append(title_attr)
                    except Exception:
                        pass
                    _log(f"playwright: Generate button hover tooltips: {tooltip_texts}")
                    for tt in tooltip_texts:
                        tl = tt.lower()
                        if any(kw in tl for kw in [
                            "please wait", "switch to credits", "still generating",
                            "concurrent", "limit reached", "max tasks", "queue full",
                        ]):
                            is_concurrent_blocked = True
                            block_reason = f"tooltip: {tt[:100]}"
                            break
                except Exception as hover_exc:
                    _log(f"playwright: hover check failed: {hover_exc}", level="WARN")

                if is_concurrent_blocked:
                    _log(f"playwright: Generate button BLOCKED by concurrent limit ({block_reason}); marking account capacity unavailable", level="WARN")
                    raise Exception(
                        f"PLUGIN_ERROR:::Generate 按钮不可用（{block_reason}），"
                        "该账号并发任务已满或被外部任务占用"
                    )

                _captured_task_ids = []
                _captured_gen_responses = []
                _captured_task_video_urls = []
                _last_net_task_status = {"value": ""}

                # Record all existing video, source, and download URLs to exclude them from generated results
                existing_video_urls = set()
                try:
                    for v in page.locator("video").all():
                        src = v.get_attribute("src") or ""
                        if src.startswith("http") or src.startswith("blob:"):
                            existing_video_urls.add(src)
                    for s in page.locator("video source").all():
                        src = s.get_attribute("src") or ""
                        if src.startswith("http") or src.startswith("blob:"):
                            existing_video_urls.add(src)
                    for link in page.locator('a[download], a:has-text("Download"), button:has-text("Download"), button:has-text("下载")').all():
                        href = link.get_attribute("href") or ""
                        if href.startswith("http") or href.startswith("blob:"):
                            existing_video_urls.add(href)
                    _log(f"playwright: recorded {len(existing_video_urls)} existing video/source/download URLs to exclude: {existing_video_urls}")
                except Exception as ex_exc:
                    _log(f"playwright: failed to record existing video URLs: {ex_exc}", level="WARN")

                def _on_gen_response(response):
                    try:
                        url = response.url
                        lower_url = url.lower()
                        method = response.request.method
                        is_task_create = method == "POST" and "/v1/tasks" in lower_url
                        is_task_poll = "/v1/tasks/" in lower_url
                        is_asset_detail = "/v1/assets/" in lower_url and bool(_captured_task_ids)
                        if not (is_task_create or is_task_poll or is_asset_detail):
                            return
                        if is_task_create:
                            _log(f"playwright: NET intercepted POST {url} status={response.status}")
                        try:
                            body = response.json()
                        except Exception:
                            try:
                                text = response.text()[:500]
                                _log(f"playwright: NET response text: {text}")
                            except Exception:
                                pass
                            return

                        status = _extract_runway_task_status(body)
                        if status and status != _last_net_task_status.get("value"):
                            _last_net_task_status["value"] = status
                            _log(f"playwright: NET current task status={status}")

                        if is_task_create:
                            try:
                                _log(f"playwright: NET response body keys={list(body.keys())[:10]}")
                                tid = _extract_runway_task_id(body)
                                if tid and isinstance(body.get("task"), dict):
                                    task_obj = body["task"]
                                    _log(f"playwright: NET extracted task_id from body.task: {tid}")
                                    for k, v in task_obj.items():
                                        _log(f"playwright: NET task.{k}={str(v)[:100]}")
                                elif tid:
                                    _log(f"playwright: NET extracted task_id: {tid}")
                                if tid and str(tid) not in _captured_task_ids:
                                    _captured_task_ids.append(str(tid))
                                    _log(f"playwright: NET captured task_id={tid}")
                                elif not tid:
                                    _log(f"playwright: NET could not find task_id in response, full body: {json.dumps(body)[:500]}")
                                _captured_gen_responses.append({"url": url, "body": body})
                            except Exception as e:
                                _log(f"playwright: NET task create parse error: {e}", level="WARN")

                        if _body_mentions_task_ids(body, _captured_task_ids):
                            for candidate in _extract_runway_video_urls_from_body(body):
                                if candidate not in _captured_task_video_urls:
                                    _captured_task_video_urls.append(candidate)
                                    _log(f"playwright: NET captured task-bound video url from {url}")
                    except Exception:
                        pass

                page.on("response", _on_gen_response)
                try:
                    page.keyboard.press("Escape")
                    page.wait_for_timeout(300)
                    popups = page.locator('[role="listbox"], [role="dialog"], [class*="autocomplete" i], [class*="suggestion" i], [class*="dropdown" i], [class*="popover" i], [class*="tooltip" i]').all()
                    for popup in popups:
                        try:
                            if popup.is_visible(timeout=200):
                                _log(f"playwright: dismissing popup overlay before Generate click")
                                page.keyboard.press("Escape")
                                page.wait_for_timeout(300)
                                break
                        except Exception:
                            continue
                except Exception:
                    pass
                pre_click_url = page.url
                _log(f"playwright: pre-click URL: {pre_click_url}")
                _ensure_on_generate_page("click Generate")
                progress_card.update(
                    "已经狠狠点击了生成按钮！Runway 的显卡开始冒烟了，离起飞不远了... 🚀",
                    "info",
                    f"🔥 炉温已满 | {progress_card.account_label}"
                )
                generate_btn.click(force=True)
                _log("playwright: clicked Generate button")
                generate_clicked_at = time.time()
                
                # Release Option B interactive lock for this account so other tasks can start their browser phase
                try:
                    acct_alias = context.get("_runtime_account", {}).get("alias")
                    if acct_alias:
                        aslot = _ACCOUNT_MGR.get_slot(acct_alias)
                        if aslot and aslot.interactive_task_id == context.get("task_id"):
                            aslot.interactive_task_id = None
                            _log(f"playwright: released Option B interactive lock for account '{acct_alias}' after click Generate")
                            with _TASK_SCHEDULER._lock:
                                _TASK_SCHEDULER._cond.notify_all()
                except Exception as interactive_exc:
                    _log(f"playwright: Option B interactive lock release warning: {interactive_exc}", level="WARN")

                page.wait_for_timeout(3000)
                _confirm_policy_violation(page, {}, required_count=3)
                _confirm_runway_technical_glitch(page, {}, required_count=3)
                post_click_url = page.url
                if post_click_url != pre_click_url:
                    _log(f"playwright: page navigated after Generate click! pre={pre_click_url} post={post_click_url}")
                    if "runwayml.com" in post_click_url and "generate" in post_click_url.lower():
                        _log("playwright: navigated to another generate page, will continue on new page")
                    elif "runwayml.com" in post_click_url:
                        _log(f"playwright: navigated to non-generate runwayml page, waiting briefly then navigating back", level="WARN")
                        page.wait_for_timeout(2000)
                        try:
                            page.goto(generate_url, wait_until="domcontentloaded")
                            page.wait_for_timeout(3000)
                            _log(f"playwright: navigated back to generate URL: {generate_url}")
                        except Exception as nav_back_exc:
                            _log(f"playwright: navigate back to generate URL failed: {nav_back_exc}", level="ERROR")
                    else:
                        _log("playwright: navigation went outside runwayml.com, attempting to go back", level="WARN")
                        try:
                            page.go_back(wait_until="domcontentloaded")
                            page.wait_for_timeout(3000)
                        except Exception:
                            pass
                try:
                    error_toast = page.locator('[class*="toast" i][class*="error" i], [class*="error" i][class*="message" i], [role="alert"]').first
                    if error_toast.is_visible(timeout=1500):
                        err_text = error_toast.inner_text().strip()[:200]
                        _log(f"playwright: error toast after click: {err_text}", level="WARN")
                        if "concurrent" in err_text.lower() or "capacity" in err_text.lower() or "limit" in err_text.lower():
                            raise Exception(
                                f"PLUGIN_ERROR:::点击Generate后出现并发限制错误（{err_text}），切换账号"
                            )
                except Exception as toast_exc:
                    if "PLUGIN_ERROR" in str(toast_exc):
                        raise
                    pass

                generation_started = False
                try:
                    page.wait_for_timeout(2000)
                    try:
                        in_queue_el = page.locator('text=/in queue/i').first
                        if in_queue_el.is_visible(timeout=3000):
                            iq_txt = in_queue_el.inner_text().strip()[:200]
                            generation_started = True
                            _log(f"playwright: generation confirmed started - In Queue: '{iq_txt}'")
                    except Exception:
                        pass
                    if not generation_started:
                        try:
                            queue_msg = page.locator('text=/will start in a few/i').first
                            if queue_msg.is_visible(timeout=1000):
                                generation_started = True
                                _log("playwright: generation confirmed started - queue message found")
                        except Exception:
                            pass
                    if not generation_started:
                        gen_indicators = [
                            'text=/queued|processing|generating|rendering|in progress|排队|生成中|渲染中|处理中/i',
                            '[class*="progress" i]',
                            '[class*="Progress"]',
                            '[class*="generation-status" i]',
                            '[class*="GenerationStatus"]',
                            '[class*="queue" i]',
                            '[class*="Queue"]',
                            '[class*="task-card" i]',
                            '[class*="TaskCard"]',
                            '[class*="output" i][class*="item" i]',
                            '[data-testid*="progress"]',
                            '[data-testid*="generation"]',
                        ]
                        for gi_sel in gen_indicators:
                            try:
                                gi_els = page.locator(gi_sel).all()
                                for gi_el in gi_els:
                                    if gi_el.is_visible(timeout=500):
                                        gi_txt = gi_el.inner_text().strip()[:100]
                                        if gi_txt:
                                            generation_started = True
                                            _log(f"playwright: generation confirmed started - indicator: '{gi_txt}' (sel={gi_sel[:50]})")
                                            break
                                if generation_started:
                                    break
                            except Exception:
                                continue
                    if not generation_started:
                        try:
                            percent_els = page.locator('text=/\\d+%/').all()
                            for pel in percent_els:
                                if pel.is_visible(timeout=500):
                                    generation_started = True
                                    _log(f"playwright: generation confirmed started - percent: '{pel.inner_text().strip()}'")
                                    break
                        except Exception:
                            pass
                    if not generation_started:
                        try:
                            new_videos = page.locator("video").all()
                            for nv in new_videos:
                                try:
                                    if page.evaluate("el => el.closest('[class*=\"thumbnail\" i], [class*=\"preview\" i], [class*=\"slot-\" i], [class*=\"reference\" i], [data-testid*=\"reference\" i]') !== null", nv):
                                        continue
                                except Exception:
                                    pass
                                src = nv.get_attribute("src") or ""
                                if src in existing_video_urls:
                                    continue
                                if src.startswith("http") and not _is_empty_state_video(src):
                                    generation_started = True
                                    _log("playwright: generation confirmed started - video element found")
                                    break
                        except Exception:
                            pass
                    if not generation_started:
                        _log("playwright: WARNING - no generation indicator found after click, Generate may not have triggered", level="WARN")
                        try:
                            page.screenshot(path=str(plugin_dir / f"_debug_nogen_{datetime.now().strftime('%Y%m%d_%H%M%S')}.png"))
                        except Exception:
                            pass
                except Exception as gi_exc:
                    _log(f"playwright: generation start check error: {gi_exc}", level="WARN")
            else:
                _log("playwright: Generate button not found with any selector", level="WARN")
                try:
                    all_btns = page.locator("button").all()
                    btn_info = []
                    for b in all_btns[:20]:
                        try:
                            if b.is_visible(timeout=200):
                                txt = b.inner_text().strip()[:30]
                                btn_info.append(f"[{txt}]")
                        except Exception:
                            continue
                    _log(f"playwright: visible buttons on page: {btn_info}")
                except Exception:
                    pass
                try:
                    page.keyboard.press("Control+Enter")
                    _log("playwright: tried Ctrl+Enter as fallback")
                    page.wait_for_timeout(2000)
                except Exception:
                    pass
        except Exception as exc:
            if "PLUGIN_ERROR" in str(exc):
                raise
            _log(f"playwright: generate click failed: {exc}", level="WARN")

        _safe_progress(context, "Playwright: 等待生成结果")

        # 点击生成成功并确立任务后，立即早期释放 Setup 锁，允许下一个同账号任务错峰启动
        try:
            _log(f"playwright: releasing browser setup lock early for account '{browser_slot.account_alias}'")
            _BROWSER_POOL.release_setup_lock(browser_slot.account_alias)
        except Exception as rel_exc:
            _log(f"playwright: failed to release setup lock early: {rel_exc}", level="WARN")

        deadline = time.time() + max(60, timeout_s)
        video_url = None
        poll_count = 0
        last_known_generate_url = generate_url
        policy_confirm_state: dict[str, Any] = {}
        technical_glitch_state: dict[str, Any] = {}
        while time.time() < deadline:
                poll_count += 1
                if page.is_closed() or not browser_slot.is_alive:
                    raise Exception("PLUGIN_ERROR:::浏览器或页面已被手动关闭，任务终止")
                try:
                    _confirm_policy_violation(page, policy_confirm_state, required_count=3)
                    _confirm_runway_technical_glitch(page, technical_glitch_state, required_count=3)
                except Exception as p_exc:
                    if "PLUGIN_ERROR" in str(p_exc):
                        raise
                try:
                    current_poll_url = page.url
                    if "runwayml.com" not in current_poll_url and "runway" not in current_poll_url.lower():
                        _log(f"playwright: page navigated away during polling! current={current_poll_url}, navigating back to {last_known_generate_url}", level="WARN")
                        try:
                            page.goto(last_known_generate_url, wait_until="domcontentloaded")
                            page.wait_for_timeout(3000)
                            if "/teams/guest/" in page.url or "login" in page.url.lower():
                                _log("playwright: session expired during polling, attempting re-login", level="WARN")
                                if cred and cred.get("email") and cred.get("password"):
                                    _auto_login_runwayml(page, cred["email"], cred["password"])
                                    page.wait_for_timeout(3000)
                                    page.goto(last_known_generate_url, wait_until="domcontentloaded")
                                    page.wait_for_timeout(3000)
                        except Exception as nav_exc:
                            _log(f"playwright: navigate back failed: {nav_exc}", level="ERROR")
                    elif "runwayml.com" in current_poll_url and "generate" not in current_poll_url.lower() and "video" not in current_poll_url.lower():
                        _log(f"playwright: page on non-generate runwayml page during polling! current={current_poll_url}, navigating back to {last_known_generate_url}", level="WARN")
                        try:
                            page.goto(last_known_generate_url, wait_until="domcontentloaded")
                            page.wait_for_timeout(3000)
                            if "/teams/guest/" in page.url or "login" in page.url.lower():
                                _log("playwright: session expired during polling, attempting re-login", level="WARN")
                                if cred and cred.get("email") and cred.get("password"):
                                    _auto_login_runwayml(page, cred["email"], cred["password"])
                                    page.wait_for_timeout(3000)
                                    page.goto(last_known_generate_url, wait_until="domcontentloaded")
                                    page.wait_for_timeout(3000)
                        except Exception as nav_exc:
                            _log(f"playwright: navigate back failed: {nav_exc}", level="ERROR")
                    if _captured_task_video_urls:
                        video_url = _captured_task_video_urls[0]
                        _log("playwright: using task-bound network video url")
                        break
                    allow_video_result = bool(_captured_task_ids) and (time.time() - generate_clicked_at >= _MIN_RESULT_ACCEPT_SECONDS) and not _page_has_generation_activity(page)
                    if not allow_video_result and (poll_count <= 3 or poll_count % 12 == 0):
                        _log(
                            f"playwright: video result scan gated: task_id_seen={bool(_captured_task_ids)} "
                            f"elapsed={time.time() - generate_clicked_at:.1f}s active={_page_has_generation_activity(page)}",
                            level="DEBUG",
                        )
                    videos = page.locator("video").all() if allow_video_result else []
                    for v in videos:
                        try:
                            if page.evaluate("el => el.closest('[class*=\"thumbnail\" i], [class*=\"preview\" i], [class*=\"slot-\" i], [class*=\"reference\" i], [data-testid*=\"reference\" i], [class*=\"left\" i], [class*=\"control\" i], [class*=\"sidebar\" i], [class*=\"settings\" i]') !== null", v):
                                remove_cv = False
                                # Double check if it's the generated output video container
                                if v.closest('[class*="settings" i]') is not None or v.closest('[class*="sidebar" i]') is not None or v.closest('[class*="left" i]') is not None:
                                    remove_cv = True
                                if remove_cv:
                                    continue
                        except Exception:
                            pass
                        src = v.get_attribute("src") or ""
                        if src in existing_video_urls:
                            continue
                        if src.startswith("http") and not _is_empty_state_video(src):
                            video_url = src
                            _log(f"playwright: found generated video src")
                            break
                    if allow_video_result and not video_url:
                        sources = page.locator("video source").all()
                        for s in sources:
                            try:
                                if page.evaluate("el => { const p = el.closest('video'); return p && p.closest('[class*=\"thumbnail\" i], [class*=\"preview\" i], [class*=\"slot-\" i], [class*=\"reference\" i], [data-testid*=\"reference\" i], [class*=\"left\" i], [class*=\"control\" i], [class*=\"sidebar\" i], [class*=\"settings\" i]') !== null; }", s):
                                    remove_cs = False
                                    if s.closest('[class*="settings" i]') is not None or s.closest('[class*="sidebar" i]') is not None or s.closest('[class*="left" i]') is not None:
                                        remove_cs = True
                                    if remove_cs:
                                        continue
                            except Exception:
                                pass
                            src = s.get_attribute("src") or ""
                            if src in existing_video_urls:
                                continue
                            if src.startswith("http") and not _is_empty_state_video(src):
                                video_url = src
                                _log(f"playwright: found generated video source src")
                                break
                except Exception:
                    pass
                if video_url:
                    break

                progress_text = ""
                progress_pct = 0
                try:
                    # 1. Evaluate JS on the page to find percentage values.
                    pct_val = page.evaluate("""() => {
                        const regex = /(\\d+)\\s*%/;
                        const selectors = [
                            '[class*="progress" i]', 
                            '[class*="percent" i]', 
                            '[class*="status" i]', 
                            '[data-testid*="progress" i]', 
                            '[role="progressbar"]'
                        ];
                        for (const sel of selectors) {
                            try {
                                const elements = document.querySelectorAll(sel);
                                for (const el of elements) {
                                    if (el.offsetWidth > 0 && el.offsetHeight > 0) {
                                        const valAttr = el.getAttribute('aria-valuenow');
                                        if (valAttr) {
                                            const val = parseInt(valAttr, 10);
                                            if (val > 0 && val < 100) return val;
                                        }
                                        const text = el.innerText || "";
                                        const match = text.match(regex);
                                        if (match) {
                                            const val = parseInt(match[1], 10);
                                            if (val > 0 && val < 100) return val;
                                        }
                                    }
                                }
                            } catch (e) {}
                        }
                        try {
                            const walker = document.createTreeWalker(
                                document.body,
                                NodeFilter.SHOW_TEXT,
                                null,
                                false
                            );
                            let node;
                            while (node = walker.nextNode()) {
                                const text = node.nodeValue;
                                if (text && text.includes('%')) {
                                    const match = text.match(regex);
                                    if (match) {
                                        const val = parseInt(match[1], 10);
                                        if (val > 0 && val < 100) {
                                            const parent = node.parentElement;
                                            if (parent && parent.offsetWidth > 0 && parent.offsetHeight > 0) {
                                                return val;
                                            }
                                        }
                                    }
                                }
                            }
                        } catch (e) {}
                        return null;
                    }""")
                    if pct_val is not None:
                        progress_pct = int(pct_val)
                        progress_text = f"生成中 ({progress_pct}%)"
                    else:
                        # 2. Try selectors if JS did not find a numeric percentage
                        progress_selectors = [
                            '[class*="progress" i]',
                            '[class*="percent" i]',
                            '[data-testid*="progress" i]',
                            '[class*="generation-status" i]',
                            '[class*="task-status" i]',
                            '[class*="queue" i]',
                        ]
                        for sel in progress_selectors:
                            try:
                                els = page.locator(sel).all()
                                for el in els:
                                    if el.is_visible(timeout=200):
                                        txt = el.inner_text().strip()
                                        if txt and len(txt) < 100:
                                            progress_text = txt
                                            break
                                if progress_text:
                                    break
                            except Exception:
                                continue
                        
                        if not progress_text:
                            # Try simple status keyword match
                            try:
                                status_texts = page.locator('text=/queued|processing|generating|rendering|in progress|排队|生成中|渲染中|处理中/i').all()
                                for st_el in status_texts:
                                    if st_el.is_visible(timeout=200):
                                        txt = st_el.inner_text().strip()
                                        if txt:
                                            progress_text = txt
                                            break
                            except Exception:
                                pass
                except Exception as p_exc:
                    _log(f"playwright: progress scraping exception: {p_exc}", level="DEBUG")

                # Report progress
                elapsed = int(time.time() - (deadline - max(60, timeout_s)))
                if progress_text:
                    if not progress_pct:
                        pct_match = re.search(r'(\d+)\s*%', progress_text)
                        if pct_match:
                            progress_pct = int(pct_match.group(1))
                    
                    lower_text = progress_text.lower()
                    if "queue" in lower_text or "排队" in lower_text:
                        msg = f"网页排队: {elapsed}秒"
                        progress_card.update(
                            f"网页正在乖乖排队中... 已等待 {elapsed} 秒，不要着急哦。💤",
                            "info",
                            f"🎬 网页排队中 | {progress_card.account_label}"
                        )
                    elif progress_pct > 0:
                        msg = "生成中"
                        progress_card.update(
                            f"视频正在加紧渲染中... 已完成 {progress_pct}%，胜利就在眼前！🎬",
                            "info",
                            f"🎬 渲染进度: {progress_pct}% | {progress_card.account_label}"
                        )
                    else:
                        msg = f"网页排队: {elapsed}秒"
                        progress_card.update(
                            f"网页正在排队或者处理中... 已等待 {elapsed} 秒 ⏰",
                            "info",
                            f"🎬 处理中 | {progress_card.account_label}"
                        )
                    
                    if "排队" in msg:
                        _safe_progress(context, msg, None)
                    else:
                        _safe_progress(context, msg, progress_pct if progress_pct > 0 else None)
                    if progress_pct > 0:
                        _update_task_runtime(context.get("task_id") or "", progress_pct=progress_pct)
                else:
                    if poll_count % 3 == 0:
                        _safe_progress(context, f"网页排队: {elapsed}秒")
                    progress_card.update(
                        f"视频正在加紧生成中... 已等待 {elapsed} 秒，胜利就在眼前！🎬",
                        "info",
                        f"🎬 生成中 | {progress_card.account_label}"
                    )

                try:
                    allow_download_result = bool(_captured_task_ids) and (time.time() - generate_clicked_at >= _MIN_RESULT_ACCEPT_SECONDS) and not _page_has_generation_activity(page)
                    if not allow_download_result:
                        raise RuntimeError("__skip_download_result_scan__")
                    download_links = page.locator('a[download], a:has-text("Download"), button:has-text("Download"), button:has-text("下载")').all()
                    for link in download_links:
                        href = link.get_attribute("href") or ""
                        if href.startswith("http"):
                            video_url = href
                            break
                except Exception:
                    pass
                if video_url:
                    break

                page.wait_for_timeout(5000)

        if not video_url:
            raise Exception("PLUGIN_ERROR:::Playwright 模式未能获取视频URL，生成可能超时或失败")

        _log(f"playwright: video url: {_mask_secret(video_url, 15)}")
        if 'progress_card' in locals() and progress_card.active:
            progress_card.update(
                "大功告成！视频已经妥妥拿下，快去欣赏你的杰作吧！🍿",
                "success",
                f"🎉 生成成功！ | {progress_card.account_label}"
            )
        return video_url

    except Exception as exc:
        if 'progress_card' in locals() and progress_card.active:
            err_msg = str(exc).replace("PLUGIN_ERROR:::", "")
            progress_card.update(
                f"糟糕，翻车了！跑通失败，报错是: {err_msg[:60]}... 😭",
                "error",
                f"😭 运行报错 | {progress_card.account_label}"
            )
        if page is not None and not page.is_closed() and debug_save_screenshot:
            try:
                ts = datetime.now().strftime("%Y%m%d_%H%M%S")
                out_png = str(plugin_dir / f"_debug_fail_{ts}.png")
                page.screenshot(path=out_png, full_page=True)
                _log(f"debug: saved screenshot: {out_png}", level="WARN")
            except Exception:
                pass
        _log_exc("playwright: generation failed")
        raise
    finally:
        if 'progress_card' in locals() and progress_card.active:
            time.sleep(5)
            progress_card.close()


_active_progress_slots = {}  # slot_index -> card_id
_progress_slots_lock = threading.Lock()


class SpeedometerWidget:
    def __init__(self, parent_canvas, x, y, radius=34):
        self.canvas = parent_canvas
        self.x = x
        self.y = y
        self.r = radius
        self.needle = None
        self._setup_dial()

    def _setup_dial(self):
        # Draw background gray dial arc
        self.canvas.create_arc(
            self.x - self.r, self.y - self.r, 
            self.x + self.r, self.y + self.r, 
            start=0, extent=180, style="arc", outline="#313244", width=4
        )
        # Dynamic colored speed track (filled based on speed progress)
        self.track = self.canvas.create_arc(
            self.x - self.r, self.y - self.r, 
            self.x + self.r, self.y + self.r, 
            start=180, extent=0, style="arc", outline="#89B4FA", width=4
        )
        # Center pivot cap
        self.canvas.create_oval(self.x-4, self.y-4, self.x+4, self.y+4, fill="#F38BA8", outline="#1E1E2E")
        
        # Custom ticks
        self.canvas.create_text(self.x - self.r - 8, self.y + 4, text="L", fill="#6C7086", font=("Segoe UI", 6, "bold"))
        self.canvas.create_text(self.x + self.r + 8, self.y + 4, text="H", fill="#6C7086", font=("Segoe UI", 6, "bold"))

    def set_value(self, pct):
        # Update progress track arc (extent maps 0-100% to 0 to -180 degrees)
        extent = -pct * 1.8
        self.canvas.itemconfigure(self.track, extent=extent)
        
        # Color redline at high speeds
        if pct > 80:
            self.canvas.itemconfigure(self.track, outline="#F38BA8")
        elif pct > 50:
            self.canvas.itemconfigure(self.track, outline="#F9E2AF")
        else:
            self.canvas.itemconfigure(self.track, outline="#89B4FA")
            
        # Update pointer needle
        if self.needle:
            self.canvas.delete(self.needle)
            
        # Calculate needle end point via trig
        angle_rad = math.radians(180 - pct * 1.8)
        px = self.x + (self.r - 4) * math.cos(angle_rad)
        py = self.y - (self.r - 4) * math.sin(angle_rad)
        self.needle = self.canvas.create_line(
            self.x, self.y, px, py, fill="#F5C2E7", width=2, arrow="last", arrowshape=(6, 8, 2)
        )


class RunwayProgressCard:
    def __init__(self, context: dict):
        self.context = context
        self.active = False
        self.msg_queue = None
        self.root = None
        self.thread = None
        self.view_mode = "dashboard"  # "dashboard" or "logs"
        self.card_id = uuid.uuid4().hex[:8]
        
        # Stats & History
        self.success_count = 0
        self.fail_count = 0
        self.logs_history = []
        
        account_label = str(self.context.get("unique_name") or self.context.get("unique_id") or "").strip()
        if not account_label:
            account_label = str(self.context.get("email") or "").split("@")[0]
        if not account_label:
            account_label = "默认"
        self.account_label = account_label[:12]
        
        # Current status state
        self.current_pct = 0
        self.current_msg = "初始化..."
        self.current_status_type = "info"
        
        # UI Elements
        self.speedometer = None
        self.color_bar = None
        self.title_label = None
        self.close_btn = None
        self.body_frame = None
        self.dash_frame = None
        self.logs_frame = None
        self.desc_label = None
        self.stats_label = None
        self.logs_text_label = None
        self.canvas_gauge = None
        
    def start(self):
        try:
            import queue
            import tkinter as tk
            self.msg_queue = queue.Queue()
            self.active = True
            self.thread = threading.Thread(target=self._run_ui, daemon=True)
            self.thread.start()
        except Exception as e:
            _log(f"progress card: fail to start: {e}", level="WARN")
            self.active = False

    def update(self, text: str, status_type: str = "info", title: str = None, pct: int = 0):
        if self.active and self.msg_queue is not None:
            try:
                # Humorous car metaphor translation for View A (Dashboard)
                dashboard_text = text
                lower = text.lower()
                if "启动浏览器" in lower or "launch" in lower:
                    pct = 5
                    dashboard_text = "正在插入钥匙，启动行车电脑... 🔑"
                elif "通行证" in lower or "登录" in lower or "login" in lower:
                    pct = 15
                    dashboard_text = "正在核对车主指纹与防盗锁... 🔒"
                elif "怠速" in lower or "伸懒腰" in lower or "settle" in lower:
                    pct = 25
                    dashboard_text = "正在怠速热车，检查水温与机油... ☕"
                elif "拦截" in lower or "广告" in lower or "popup" in lower:
                    pct = 30
                    dashboard_text = "路遇前方巨幅广告牌路障，一把方向盘闪开！🚧"
                elif "喂图" in lower or "上传" in lower or "upload" in lower:
                    m = re.search(r'(\d+)\s*/\s*(\d+)', text)
                    if m:
                        curr, tot = int(m.group(1)), int(m.group(2))
                        pct = int(35 + (curr / tot) * 20)
                        dashboard_text = f"正在强力加油中！第 {curr}/{tot} 升，加满出发！⛽"
                    else:
                        pct = 40
                        dashboard_text = "正在往油箱里强力加油... ⛽"
                elif "吃饱" in lower or "消化" in lower or "confirm" in lower:
                    pct = 55
                    dashboard_text = "油品确认完成，过滤杂质，燃烧完美！👍"
                elif "提示词" in lower or "咒语" in lower or "prompt" in lower:
                    pct = 65
                    dashboard_text = "已规划神级提示词航线，GPS 正在锁定终点！📍"
                elif "地板油" in lower or "点击" in lower or "冒烟" in lower or "generate" in lower:
                    pct = 80
                    dashboard_text = "一脚地板油起步！转速拉满，排气管冒烟，准备发车！🔥"
                elif "排队" in lower or "queue" in lower:
                    m_elapsed = re.search(r'(\d+)秒', text)
                    elapsed_str = f"已等待 {m_elapsed.group(1)} 秒" if m_elapsed else "排队中"
                    pct = 20
                    dashboard_text = f"收费站正在排队中... {elapsed_str}，耐心等候发车 💨"
                elif "渲染" in lower or "progress" in lower or "生成中" in lower:
                    # Try to parse numeric %
                    m_pct = re.search(r'(\d+)\s*%', text)
                    if m_pct:
                        pct = int(m_pct.group(1))
                    else:
                        pct = 90
                    dashboard_text = f"高速巡航中！车速达 {pct} 码，发动机轰鸣，抓稳扶手！🚀"
                elif "成功" in lower or "冲线" in lower or "url" in lower:
                    pct = 100
                    dashboard_text = "完美的漂移冲线！冠军奖杯已到手，请尽情鼓掌！🏁"
                elif "报错" in lower or "故障" in lower or "翻车" in lower or "fail" in lower:
                    pct = 0
                    dashboard_text = f"发动机抛锚拉稀啦！亮黄灯故障：{text[:30]}... ⚠️"

                card_title = title if title else f"🏎️ 仪表盘 | {self.account_label}"
                self.msg_queue.put((dashboard_text, text, status_type, card_title, pct))
            except Exception:
                pass

    def _run_ui(self):
        try:
            import tkinter as tk
            self.root = tk.Tk()
            self._setup_window()
            self._tick()
            self.root.mainloop()
        except Exception as e:
            _log(f"progress card UI error: {e}", level="WARN")
            self.active = False

    def _setup_window(self):
        import tkinter as tk
        global _active_progress_slots
        with _progress_slots_lock:
            slot_index = 0
            while slot_index in _active_progress_slots:
                slot_index += 1
            _active_progress_slots[slot_index] = self.card_id
            self.slot_index = slot_index

        self.root.overrideredirect(True)
        self.root.attributes("-topmost", True)
        self.root.attributes("-alpha", 0.92)
        self.root.configure(bg="#1E1E2E")
        
        sw = self.root.winfo_screenwidth()
        sh = self.root.winfo_screenheight()
        width = 380
        height = 110
        x = sw - width - 20
        y = sh - (self.slot_index + 1) * (height + 12) - 60
        self.root.geometry(f"{width}x{height}+{x}+{y}")
        
        # Bind click anywhere on the card to flip views (except the close button)
        self.root.bind("<Button-1>", self._on_card_click)

        # 1. Left Color Bar
        self.bar_color_map = {
            "info": "#89B4FA",
            "success": "#A6E3A1",
            "warning": "#F9E2AF",
            "error": "#F38BA8"
        }
        self.color_bar = tk.Frame(self.root, bg=self.bar_color_map["info"], width=6)
        self.color_bar.pack(side=tk.LEFT, fill=tk.Y)
        
        # 2. Outer Layout Frame
        self.outer_frame = tk.Frame(self.root, bg="#181825")
        self.outer_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        # 3. Header Title & Manual Close button
        header_frame = tk.Frame(self.outer_frame, bg="#181825")
        header_frame.pack(fill=tk.X, padx=12, pady=(6, 0))
        
        self.title_label = tk.Label(
            header_frame, text=f"🏎️ 仪表盘 | {self.account_label}", fg="#CDD6F4", bg="#181825",
            font=("Microsoft YaHei", 9, "bold"), anchor="w"
        )
        self.title_label.pack(side=tk.LEFT, fill=tk.X)
        
        self.close_btn = tk.Label(
            header_frame, text="×", fg="#6C7086", bg="#181825",
            font=("Segoe UI", 11, "bold"), cursor="hand2"
        )
        self.close_btn.pack(side=tk.RIGHT)
        self.close_btn.bind("<Button-1>", lambda e: self.close())
        
        # 4. Main Body Frame (Will hold either Dashboard widgets or Trip logs)
        self.body_frame = tk.Frame(self.outer_frame, bg="#181825")
        self.body_frame.pack(fill=tk.BOTH, expand=True, padx=12, pady=(4, 8))
        
        # Initialize subviews
        self._build_dashboard_view()
        self._build_logs_view()
        
        # Render default view
        self._render_current_view()

    def _build_dashboard_view(self):
        import tkinter as tk
        # Frame for gauge + description side-by-side
        self.dash_frame = tk.Frame(self.body_frame, bg="#181825")
        
        # Left Side: Canvas Vector Speedometer
        self.canvas_gauge = tk.Canvas(self.dash_frame, width=90, height=65, bg="#181825", highlightthickness=0)
        self.canvas_gauge.pack(side=tk.LEFT, padx=(0, 6))
        self.speedometer = SpeedometerWidget(self.canvas_gauge, 45, 52, radius=34)
        
        # Right Side: Metaphorical car description
        self.desc_label = tk.Label(
            self.dash_frame, text="正在启动行车电脑... 🔑", fg="#CDD6F4", bg="#181825",
            font=("Microsoft YaHei", 9), wraplength=230, justify=tk.LEFT, anchor="nw"
        )
        self.desc_label.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, pady=(2, 0))

    def _build_logs_view(self):
        import tkinter as tk
        self.logs_frame = tk.Frame(self.body_frame, bg="#181825")
        
        # Trip Stats line (Success / Fail count)
        self.stats_label = tk.Label(
            self.logs_frame, text="✅ 成功到达: 0 次   |   ❌ 中途抛锚: 0 次", fg="#A6E3A1", bg="#181825",
            font=("Microsoft YaHei", 8, "bold"), anchor="w"
        )
        self.stats_label.pack(fill=tk.X, pady=(0, 2))
        
        # Text area/Label showing past logs
        self.logs_text_label = tk.Label(
            self.logs_frame, text="暂无行车诊断日志", fg="#BAC2DE", bg="#11111b",
            font=("Consolas", 8), justify=tk.LEFT, anchor="nw", relief=tk.FLAT, bd=0, padx=6, pady=4
        )
        self.logs_text_label.pack(fill=tk.BOTH, expand=True)

    def _render_current_view(self):
        # Hide both frames
        self.dash_frame.pack_forget()
        self.logs_frame.pack_forget()
        
        if self.view_mode == "dashboard":
            self.title_label.configure(text=f"🏎️ 仪表盘 | {self.account_label} (点击看日志 📊)")
            self.dash_frame.pack(fill=tk.BOTH, expand=True)
            self._update_speedometer_visual()
        else:
            self.title_label.configure(text=f"📊 行车诊断日志 | {self.account_label} (点击看仪表 🏎️)")
            self._update_logs_visual()
            self.logs_frame.pack(fill=tk.BOTH, expand=True)

    def _on_card_click(self, event):
        # Avoid toggle if clicking close button
        try:
            widget = event.widget
            if widget == self.close_btn:
                return
        except Exception:
            pass
        
        # Toggle view
        self.view_mode = "logs" if self.view_mode == "dashboard" else "dashboard"
        self._render_current_view()

    def _update_speedometer_visual(self):
        if self.speedometer:
            self.speedometer.set_value(self.current_pct)
        if hasattr(self, 'desc_label') and self.desc_label:
            self.desc_label.configure(text=self.current_msg)
        bar_color = self.bar_color_map.get(self.current_status_type, self.bar_color_map["info"])
        if self.color_bar:
            self.color_bar.configure(bg=bar_color)

    def _update_logs_visual(self):
        if self.stats_label:
            self.stats_label.configure(text=f"✅ 成功到达: {self.success_count} 次   |   ❌ 中途抛锚: {self.fail_count} 次")
        recent_logs = self.logs_history[-4:]  # Get last 4 logs
        if self.logs_text_label:
            if recent_logs:
                self.logs_text_label.configure(text="\n".join(recent_logs))
            else:
                self.logs_text_label.configure(text="暂无行车诊断日志")

    def _tick(self):
        if not self.active:
            return
        import queue
        try:
            while True:
                dashboard_msg, original_msg, status_type, title, pct = self.msg_queue.get_nowait()
                self.current_msg = dashboard_msg
                self.current_pct = pct
                self.current_status_type = status_type
                
                # Append original_msg to logs_history
                ts = time.strftime("%H:%M:%S")
                log_tag = "INFO"
                if status_type == "success":
                    log_tag = " OK "
                    self.success_count += 1
                elif status_type == "error":
                    log_tag = "FAIL"
                    self.fail_count += 1
                elif status_type == "warning":
                    log_tag = "WARN"
                
                # Strip emojis for technical logs
                clean_msg = original_msg
                for emoji in ("🔑", "✨", "🔒", "☕", "⏰", "🙅‍♂️", "🍖", "👍", "🤢", "🔮", "🚀", "🍿", "😭", "💔", "🏁", "⚠️", "🚧", "⛽", "🏎️", "📍"):
                    clean_msg = clean_msg.replace(emoji, "")
                clean_msg = clean_msg.strip()[:35]
                
                self.logs_history.append(f"[{ts}][{log_tag}] {clean_msg}")
                
                # Update currently rendered view
                if self.view_mode == "dashboard":
                    self._update_speedometer_visual()
                else:
                    self._update_logs_visual()
                    
                self.msg_queue.task_done()
        except queue.Empty:
            pass
        except Exception:
            pass
        
        if self.root and self.active:
            try:
                self.root.after(100, self._tick)
            except Exception:
                pass

    def close(self):
        """Safely destroy and fade out the Tkinter UI."""
        self.active = False
        global _active_progress_slots
        try:
            with _progress_slots_lock:
                if hasattr(self, 'slot_index') and _active_progress_slots.get(self.slot_index) == self.card_id:
                    _active_progress_slots.pop(self.slot_index, None)
        except Exception:
            pass

        if self.root:
            try:
                def fade(alpha=0.92):
                    if not self.root:
                        return
                    if alpha > 0.1:
                        try:
                            self.root.attributes("-alpha", alpha)
                            self.root.after(30, lambda: fade(alpha - 0.15))
                        except Exception:
                            try:
                                self.root.destroy()
                            except Exception:
                                pass
                    else:
                        try:
                            self.root.destroy()
                        except Exception:
                            pass
                fade()
            except Exception:
                pass



def _generate_via_playwright(

    context: dict,
    params: dict[str, Any],
    prompt: str,
    first_path: str | None,
    end_path: str | None,
    model: str,
    duration_s: int,
    ratio: str,
    timeout_s: int,
    api_key: str,
) -> str:
    try:
        progress_card = RunwayProgressCard(context)
        progress_card.start()
        progress_card.update("正在悄悄启动后台浏览器... 嘘，不要打扰它睡觉。💤", "info", f"🤖 智能小助手 | {progress_card.account_label}")

        from playwright.sync_api import sync_playwright
    except Exception:
        raise Exception("PLUGIN_ERROR:::Playwright 未安装，请运行: pip install playwright && playwright install chromium")

    site_profile = _get_site_profile(params=params, context=context)
    task_id = str(context.get("task_id") or "").strip()
    worker_id = _sanitize_token(context.get("worker_id") or task_id or f"worker_{uuid.uuid4().hex[:6]}", max_len=48)

    headless = bool(params.get("playwright_headless", False))
    keep_browser = bool(params.get("playwright_keep_browser", False))
    debug_save_screenshot = bool(params.get("debug_save_screenshot", True))
    cookie_header = str(params.get("cookie_header") or "").strip()
    storage_state_path = str(params.get("playwright_storage_state") or "").strip()
    storage_state = None
    if storage_state_path and os.path.isfile(storage_state_path):
        storage_state = storage_state_path

    _log(f"playwright: start site={site_profile.key} model={model} headless={headless}")

    model_url_map = {
        "seedance_2.0": "seedance-2",
    }
    model_slug = model_url_map.get(model, "seedance-2")
    gen_mode = str(params.get("generation_mode") or "multi_reference").strip().lower()
    mode_param = "keyframe" if gen_mode == "keyframe" else "tools"
    generate_url = f"{site_profile.base_url}/video-tools/ai-tools/generate?tool=video&mode={mode_param}&model={model_slug}"

    with sync_playwright() as p:
        page = None
        browser = None
        try:
            # Prefer official Google Chrome or Microsoft Edge to support proprietary MP4/H.264 video codecs
            for ch in ["chrome", "msedge", None]:
                try:
                    if ch:
                        browser = p.chromium.launch(headless=headless, channel=ch)
                        _log(f"playwright: launched chromium successfully with channel='{ch}'")
                        break
                    else:
                        browser = p.chromium.launch(headless=headless)
                        _log("playwright: launched default chromium successfully")
                        break
                except Exception as ch_err:
                    _log(f"playwright: failed to launch with channel='{ch}': {ch_err}", level="WARN")
            ctx_opts: dict[str, Any] = {
                "viewport": {"width": 800, "height": 600},
            }
            if storage_state:
                ctx_opts["storage_state"] = storage_state
            context_obj = browser.new_context(**ctx_opts)
            page = context_obj.new_page()

            try:
                page.set_default_navigation_timeout(120000)
                page.set_default_timeout(120000)
            except Exception as e:
                _log(f"playwright: set timeouts error: {e}", level="WARN")

            if cookie_header:
                _log("playwright: injecting cookies from cookie_header")
                try:
                    for pair in cookie_header.split(";"):
                        pair = pair.strip()
                        if "=" in pair:
                            k, v = pair.split("=", 1)
                            context_obj.add_cookies([{
                                "name": k.strip(),
                                "value": v.strip(),
                                "domain": site_profile.domains[0] if site_profile.domains else ".runwayml.com",
                                "path": "/",
                            }])
                except Exception as exc:
                    _log(f"playwright: cookie injection failed: {exc}", level="WARN")

            _safe_progress(context, "Playwright: 页面")
            _log(f"playwright: navigating to {generate_url}")
            page.goto(generate_url, wait_until="domcontentloaded", timeout=120000)

            _log("playwright: waiting for page elements to settle (supporting 40-50s slow network)")
            for _ in range(30):
                if page.is_closed():
                    break
                _dismiss_promotional_popups(page)
                try:
                    if (page.locator('[data-testid="select-base-model"]').first.is_visible(timeout=500) or
                        page.locator('textarea').first.is_visible(timeout=500) or
                        page.locator('[placeholder*="Describe" i]').first.is_visible(timeout=500) or
                        "/teams/guest/" in page.url or
                        "login" in page.url.lower() or
                        "sign-in" in page.url.lower()):
                        _log("playwright: page settled, key elements visible")
                        break
                except Exception:
                    pass
                page.wait_for_timeout(2000)

            current_url = page.url
            if "/teams/guest/" in current_url:
                _log("playwright: on guest page, not logged in", level="WARN")
                _safe_progress(context, "Playwright: 未登录要先登录")
                raise Exception("PLUGIN_ERROR:::Playwright 未登录或未激活")

            if "login" in current_url.lower() or "sign-in" in current_url.lower():
                _log("playwright: redirected to login page, waiting for manual login", level="WARN")
                _safe_progress(context, "Playwright: 需要登录手动登录")
                try:
                    page.wait_for_url("**/video-tools/**", timeout=120000)
                    _log("playwright: login completed, proceeding")
                except Exception:
                    raise Exception("PLUGIN_ERROR:::Playwright 登录超时或登录失败")

            _safe_progress(context, "Playwright: 选模")
            try:
                model_btn = page.locator('[data-testid="select-base-model"]').first
                if model_btn.is_visible(timeout=5000):
                    current_model = model_btn.inner_text().strip()
                    _log(f"playwright: current model shown: {current_model}")
                    if model_slug.replace("-", "").replace("/", "").lower() not in current_model.replace(" ", "").replace(".", "").lower():
                        model_btn.click()
                        page.wait_for_timeout(1000)
                        model_option = page.locator(f'[data-testid*="{model_slug}"], li:has-text("{model}"), button:has-text("{model}"), [role="option"]:has-text("{model}")').first
                        if model_option.is_visible(timeout=3000):
                            model_option.click()
                            page.wait_for_timeout(1000)
            except Exception as exc:
                _log(f"playwright: model selection failed (will use URL param): {exc}", level="WARN")

            _safe_progress(context, "Playwright: 预检账户")
            _log("playwright: pre-check: entering test prompt to verify account availability")
            try:
                prompt_input_pre = None
                prompt_selectors_2 = [
                    '[role="textbox"][aria-label="Prompt"]',
                    '[role="textbox"][contenteditable="true"]',
                    '[contenteditable="true"][class*="textbox"]',
                    '[contenteditable="true"][class*="prompt" i]',
                    '[contenteditable="true"][class*="input" i]',
                    'textarea[placeholder*="rompt" i]',
                    'div[contenteditable="true"]',
                    '[role="textbox"]',
                ]
                for psel in prompt_selectors_2:
                    try:
                        pcand = page.locator(psel).first
                        if pcand.is_visible(timeout=2000):
                            prompt_input_pre = pcand
                            _log(f"playwright: pre-check found prompt input with selector: {psel}")
                            break
                    except Exception:
                        continue
                if not prompt_input_pre:
                    _log("playwright: pre-check could not find prompt input, trying click-based detection", level="WARN")
                    try:
                        page.wait_for_timeout(3000)
                        editable = page.locator('[contenteditable="true"]')
                        count = editable.count()
                        _log(f"playwright: pre-check found {count} contenteditable elements")
                        for i in range(min(count, 5)):
                            el = editable.nth(i)
                            try:
                                if el.is_visible(timeout=1000):
                                    bb = el.bounding_box()
                                    tag = el.evaluate("el => el.tagName")
                                    cls = el.get_attribute("class") or ""
                                    _log(f"playwright: pre-check contenteditable[{i}] tag={tag} class={cls[:60]} bbox={bb}")
                                    if bb and bb["width"] > 100 and bb["height"] > 40:
                                        prompt_input_pre = el
                                        _log(f"playwright: pre-check using contenteditable[{i}] as prompt input")
                                        break
                            except Exception:
                                continue
                    except Exception as pexc2:
                        _log(f"playwright: pre-check click-based detection failed: {pexc2}", level="WARN")

                if prompt_input_pre and prompt_input_pre.is_visible(timeout=3000):
                    try:
                        _sandboxed_input_text(prompt_input_pre, _PRECHECK_TEST_PROMPT)
                    except Exception as _e_pre:
                        _log(f"playwright: pre-check sandboxed input failed: {_e_pre}, using fallback", level="WARN")
                        try:
                            prompt_input_pre.click()
                            page.wait_for_timeout(300)
                            page.keyboard.press("Control+a")
                            page.keyboard.press("Backspace")
                            page.keyboard.type(_PRECHECK_TEST_PROMPT, delay=10)
                        except Exception:
                            pass
                    page.wait_for_timeout(3000)

                    wait_deadline = time.time() + _PRECHECK_MAX_WAIT_SECONDS
                    account_available = False
                    block_reason = "初始化检测"
                    is_first_loop = True

                    _log("playwright: entering in-browser pre-check availability wait loop (max 50 mins, poll every 10s)...")
                    while time.time() < wait_deadline:
                        if page.is_closed():
                            raise Exception("PLUGIN_ERROR:::浏览器或页面已被手动关闭，任务终止")

                        if not is_first_loop:
                            try:
                                current_val = _get_input_value_safe(prompt_input_pre)
                                if not current_val or current_val != _PRECHECK_TEST_PROMPT:
                                    _sandboxed_input_text(prompt_input_pre, _PRECHECK_TEST_PROMPT)
                            except Exception:
                                pass

                        if is_first_loop and debug_save_screenshot:
                            try:
                                ts = datetime.now().strftime("%Y%m%d_%H%M%S")
                                pre_ss = str(plugin_dir / f"_debug_precheck_{ts}.png")
                                page.screenshot(path=pre_ss)
                                _log(f"playwright: pre-check screenshot saved: {pre_ss}")
                            except Exception:
                                pass

                        generate_btn_pre = None
                        all_candidates = []
                        for sel in [
                            'button:has-text("Generate"):not(:has-text("Sign")):not(:has-text("Log"))',
                            'button[data-testid*="generate"]',
                            'button[class*="primaryButton"]',
                            'button[class*="generate" i]',
                            'button[aria-label*="Generate" i]',
                            'text=Generate >> visible=true >> button',
                            ':text-is("Generate") >> button:visible',
                            'button >> text=/^Generate$/',
                            '[role="button"]:has-text("Generate")',
                            'div[role="button"]:has-text("Generate")',
                            '*[class*="generate" i]:has-text("Generate")',
                            'button:visible >> text=Generate',
                        ]:
                            try:
                                candidates = page.locator(sel).all()
                                for c in candidates:
                                    try:
                                        if c.is_visible(timeout=500):
                                            bbox = c.bounding_box()
                                            txt = c.inner_text().strip()[:30]
                                            tag = c.evaluate("el => el.tagName")
                                            all_candidates.append({
                                                "sel": sel,
                                                "loc": c,
                                                "bbox": bbox,
                                                "text": txt,
                                                "tag": tag,
                                            })
                                    except Exception:
                                        continue
                            except Exception:
                                continue

                        button_candidates = [c for c in all_candidates if c["tag"] == "BUTTON" and c["text"].strip() == "Generate"]

                        generate_btn_pre = None
                        if len(button_candidates) >= 1:
                            best_btn = None
                            for cand in button_candidates:
                                bb = cand["bbox"]
                                if bb and bb["width"] > 50 and bb["height"] > 25:
                                    if best_btn is None:
                                        best_btn = cand
                                    elif bb["y"] > (best_btn["bbox"]["y"] or 0):
                                        best_btn = cand
                            if best_btn:
                                generate_btn_pre = best_btn["loc"]
                        elif len(all_candidates) == 1:
                            generate_btn_pre = all_candidates[0]["loc"]

                        account_available = True
                        block_reason = ""

                        if generate_btn_pre:
                            try:
                                if generate_btn_pre.is_disabled():
                                    account_available = False
                                    block_reason = "button is_disabled=True"
                            except Exception:
                                pass

                            if account_available:
                                try:
                                    disabled_attr = generate_btn_pre.get_attribute("disabled")
                                    if disabled_attr is not None:
                                        account_available = False
                                        block_reason = f"disabled attr present: {disabled_attr}"
                                except Exception:
                                    pass

                            if account_available:
                                try:
                                    aria_disabled = generate_btn_pre.get_attribute("aria-disabled")
                                    if aria_disabled and aria_disabled.lower() == "true":
                                        account_available = False
                                        block_reason = "aria-disabled=true"
                                except Exception:
                                    pass

                            if account_available:
                                try:
                                    btn_class = generate_btn_pre.get_attribute("class") or ""
                                    cls_lower = btn_class.lower()
                                    if "disabled" in cls_lower or "muted" in cls_lower or "inactive" in cls_lower:
                                        account_available = False
                                        block_reason = f"CSS class contains disabled/muted"
                                except Exception:
                                    pass

                            if account_available:
                                try:
                                    opacity = generate_btn_pre.evaluate("el => window.getComputedStyle(el).opacity")
                                    pointer_events = generate_btn_pre.evaluate("el => window.getComputedStyle(el).pointerEvents")
                                    background = generate_btn_pre.evaluate("el => window.getComputedStyle(el).backgroundColor")
                                    color = generate_btn_pre.evaluate("el => window.getComputedStyle(el).color")

                                    def _parse_rgb(css_color):
                                        m = re.search(r'rgb[a]?\((\d+)[,\s]+(\d+)[,\s]+(\d+)', css_color or "")
                                        if m:
                                            return int(m.group(1)), int(m.group(2)), int(m.group(3))
                                        return None

                                    bg_rgb = _parse_rgb(background)
                                    txt_rgb = _parse_rgb(color)
                                    is_disabled_by_color = False
                                    color_detail = ""

                                    if bg_rgb:
                                        r, g, b = bg_rgb
                                        brightness = (r + g + b) / 3.0
                                        deviation = ((abs(r - brightness) + abs(g - brightness) + abs(b - brightness)) / 3.0)
                                        is_achromatic = deviation < 18
                                        is_very_light = brightness > 225
                                        if is_very_light and is_achromatic:
                                            is_disabled_by_color = True
                                            color_detail = f"灰白背景({r},{g},{b})"

                                    if not is_disabled_by_color and txt_rgb and bg_rgb:
                                        tr, tg, tb = txt_rgb
                                        txt_brightness = (tr + tg + tb) / 3.0
                                        br, bg_val, bb = bg_rgb
                                        bg_brightness = (br + bg_val + bb) / 3.0
                                        if txt_brightness < 140 and bg_brightness > 220:
                                            is_disabled_by_color = True
                                            color_detail = "深色文字+浅背景"

                                    if is_disabled_by_color:
                                        account_available = False
                                        block_reason = f"按钮呈灰色不可用({color_detail})"
                                    elif opacity and float(opacity) < 0.5:
                                        account_available = False
                                        block_reason = f"opacity={opacity}"
                                    elif pointer_events and pointer_events == "none":
                                        account_available = False
                                        block_reason = "pointer-events=none"
                                except Exception:
                                    pass

                            if not account_available:
                                try:
                                    tooltip_texts = []
                                    tooltip_els = page.locator('[role="tooltip"], [data-state="delayed-open"], [data-radix-tooltip-content], [class*="Tooltip"], [class*="tooltip"]').all()
                                    for tel in tooltip_els:
                                        try:
                                            if tel.is_visible(timeout=100):
                                                tt = tel.inner_text().strip()
                                                if tt and len(tt) < 300:
                                                    tooltip_texts.append(tt)
                                        except Exception:
                                            continue
                                    try:
                                        title_attr = generate_btn_pre.get_attribute("title") or ""
                                        if title_attr:
                                            tooltip_texts.append(title_attr)
                                    except Exception:
                                        pass
                                    if tooltip_texts:
                                        block_reason += f" | tooltips: {tooltip_texts[:3]}"
                                except Exception:
                                    pass
                        else:
                            account_available = False
                            block_reason = "未找到 Generate 按钮"

                        _log(f"playwright: pre-check result: account_available={account_available}, reason={block_reason}")

                        if account_available:
                            _log("playwright: pre-check passed, account is available!")
                            break

                        is_first_loop = False
                        _log(f"playwright: account unavailable ({block_reason}), waiting 10 seconds before re-check...")
                        page.wait_for_timeout(_PRECHECK_POLL_INTERVAL_MS)

                    # Clear the test prompt
                    try:
                        prompt_input_pre.click()
                        page.wait_for_timeout(200)
                        page.keyboard.press("Control+a")
                        page.keyboard.press("Backspace")
                        page.wait_for_timeout(500)
                        _pc_val = _get_input_value_safe(prompt_input_pre)
                        if _pc_val:
                            prompt_input_pre.click()
                            page.wait_for_timeout(200)
                            page.keyboard.press("Control+a")
                            page.keyboard.press("Backspace")
                            page.wait_for_timeout(500)
                    except Exception as clear_exc:
                        _log(f"playwright: pre-check clear test prompt failed: {clear_exc}", level="WARN")

                    if not account_available:
                        _log(f"playwright: pre-check FAILED - account unavailable after 50 mins ({block_reason})", level="WARN")
                        raise Exception(
                            f"PLUGIN_ERROR:::账号 Generate 按钮 50 分钟内一直不可用（{block_reason}）。"
                            "该账号可能被用户手动打开的 Runway 任务占用，或官方并发通道仍未释放"
                        )
                    _log("playwright: pre-check PASSED - account is available")
                else:
                    _log("playwright: pre-check could not find prompt input, skipping check", level="WARN")
            except Exception as exc:
                if "PLUGIN_ERROR" in str(exc):
                    raise
                _log(f"playwright: pre-check failed: {exc}", level="WARN")
            _safe_progress(context, "Playwright: 设置提示词")
            try:
                prompt_input = page.locator('[role="textbox"][contenteditable="true"], [contenteditable="true"][class*="textbox"]').first
                if prompt and prompt_input.is_visible(timeout=5000):
                    try:
                        _sandboxed_input_text(prompt_input, prompt)
                        _log(f"playwright: prompt sandboxed input success ({len(prompt)} chars)")
                    except Exception as _e_prompt:
                        _log(f"playwright: prompt sandboxed input failed: {_e_prompt}, using fallback", level="WARN")
                        try:
                            prompt_input.click()
                            page.wait_for_timeout(300)
                            page.keyboard.press("Control+a")
                            page.keyboard.press("Backspace")
                            try:
                                page.evaluate(f"() => {{ navigator.clipboard.writeText({json.dumps(prompt)}); }}")
                                page.keyboard.press("Control+v")
                                _log(f"playwright: prompt pasted ({len(prompt)} chars)")
                            except Exception:
                                page.keyboard.type(prompt, delay=5)
                                _log(f"playwright: prompt typed ({len(prompt)} chars)")
                        except Exception:
                            pass
                    page.wait_for_timeout(500)
                    try:
                        page.evaluate('() => { const el = document.querySelector(\'[role="textbox"][contenteditable="true"], [contenteditable="true"][class*="textbox"]\'); if(el) el.blur(); }')
                        _log("playwright: blurred prompt input to dismiss @ mention autocomplete")
                    except Exception:
                        pass
                    try:
                        page.evaluate('() => { const el = document.querySelector(\'[role="textbox"][aria-label="Prompt"]\'); if(el) el.blur(); }')
                        _log("playwright: blurred prompt input by aria-label")
                    except Exception:
                        pass
                    page.keyboard.press("Escape")
                    page.wait_for_timeout(800)
                    try:
                        autocomplete2 = page.locator('[role="listbox"], [class*="mention" i], [class*="autocomplete" i], [class*="suggestion" i], [class*="dropdown" i]').all()
                        for ac in autocomplete2:
                            try:
                                if ac.is_visible(timeout=300):
                                    ac.evaluate("el => el.remove()")
                                    _log("playwright: removed @ mention autocomplete dropdown from DOM")
                                    break
                            except Exception:
                                continue
                    except Exception:
                        pass
                    try:
                        remaining_popups2 = page.locator('[role="listbox"], [role="menu"], [class*="mention" i], [class*="autocomplete" i], [class*="suggestion" i], [class*="dropdown" i], [class*="popover" i], [class*="tooltip" i]').all()
                        for rp in remaining_popups2:
                            try:
                                if rp.is_visible(timeout=200):
                                    rp.evaluate("el => { el.style.display = 'none'; el.style.visibility = 'hidden'; }")
                                    _log("playwright: hidden remaining popup/overlay that could block Generate button")
                            except Exception:
                                continue
                    except Exception:
                        pass
            except Exception as exc:
                _log(f"playwright: prompt input failed: {exc}", level="WARN")

            if first_path:
                _safe_progress(context, "Playwright: 上传参考图片")
                try:
                    page.evaluate("() => { document.querySelectorAll('input[type=file]').forEach(el => el.removeAttribute('accept')); }")
                    file_inputs = page.locator('input[type="file"]').all()
                    _log(f"playwright: found {len(file_inputs)} file input(s) for first image upload")
                    uploaded = False
                    if file_inputs:
                        for fi in file_inputs:
                            try:
                                fi.set_input_files(first_path)
                                uploaded = True
                                _log(f"playwright: uploaded first image via file input: {first_path}")
                                break
                            except Exception as fi_exc:
                                _log(f"playwright: file input set_input_files failed: {fi_exc}", level="WARN")
                                continue
                    if not uploaded:
                        upload_areas = page.locator('[class*="upload"], [class*="Upload"], [data-testid*="upload"], [class*="reference-image"], [class*="ImageInput"]').all()
                        for area in upload_areas:
                            try:
                                if area.is_visible(timeout=2000):
                                    area.click()
                                    page.wait_for_timeout(1500)
                                    retry_inputs = page.locator('input[type="file"]').all()
                                    if retry_inputs:
                                        retry_inputs[0].set_input_files(first_path)
                                        uploaded = True
                                        _log(f"playwright: uploaded first image after clicking upload area: {first_path}")
                                        break
                            except Exception:
                                continue
                    if not uploaded:
                        _log("playwright: all first image upload methods failed", level="ERROR")
                    page.wait_for_timeout(3000)
                except Exception as exc:
                    _log(f"playwright: file upload failed: {exc}", level="WARN")

            if end_path:
                _safe_progress(context, "Playwright: 上传尾帧图片")
                try:
                    file_inputs = page.locator('input[type="file"]').all()
                    _log(f"playwright: found {len(file_inputs)} file input(s) for end frame upload")
                    if len(file_inputs) > 1:
                        file_inputs[1].set_input_files(end_path)
                        _log(f"playwright: uploaded end frame via 2nd file input: {end_path}")
                    elif len(file_inputs) == 1:
                        try:
                            file_inputs[0].set_input_files([first_path or "", end_path])
                            _log(f"playwright: uploaded both frames via single file input (multi-file)")
                        except Exception:
                            _log("playwright: single file input, cannot upload end frame separately", level="WARN")
                    else:
                        _log("playwright: no file input found for end frame", level="WARN")
                    page.wait_for_timeout(3000)
                except Exception as exc:
                    _log(f"playwright: end frame upload failed: {exc}", level="WARN")

            if video_path:
                _safe_progress(context, "Playwright: 上传参考视频/MP4")
                try:
                    file_inputs = page.locator('input[type="file"]').all()
                    if file_inputs:
                        target_input = file_inputs[-1] if len(file_inputs) > 1 else file_inputs[0]
                        target_input.set_input_files(video_path)
                        _log(f"playwright: uploaded video via file input: {video_path}")
                    else:
                        upload_areas = page.locator('[class*="upload"], [class*="Upload"], [data-testid*="upload"]').all()
                        if upload_areas:
                            upload_areas[-1].click()
                            page.wait_for_timeout(1000)
                            retry_inputs = page.locator('input[type="file"]').all()
                            if retry_inputs:
                                target_input = retry_inputs[-1] if len(retry_inputs) > 1 else retry_inputs[0]
                                target_input.set_input_files(video_path)
                                _log(f"playwright: uploaded video after clicking upload area: {video_path}")
                        else:
                            _log("playwright: no file input found for video", level="WARN")
                    page.wait_for_timeout(3000)
                except Exception as exc:
                    _log(f"playwright: video upload failed: {exc}", level="WARN")

            _safe_progress(context, "Playwright: 点击生成")
            generate_btn_clicked = False
            try:
                generate_selectors = [
                    'button:has-text("Generate"):not(:has-text("Sign")):not(:has-text("Log"))',
                    'button[data-testid*="generate"]',
                    'button[class*="primaryButton"]',
                    'button[class*="generate" i]',
                    'button[aria-label*="Generate" i]',
                    'button[aria-label*="generate" i]',
                ]
                generate_btn = None
                for sel in generate_selectors:
                    try:
                        candidate = page.locator(sel).first
                        if candidate.is_visible(timeout=2000):
                            generate_btn = candidate
                            _log(f"playwright: found Generate button with selector: {sel}")
                            break
                    except Exception:
                        continue

                if generate_btn:
                    try:
                        btn_tag = generate_btn.evaluate("el => el.tagName")
                        btn_text = generate_btn.inner_text().strip()[:50]
                        btn_class = generate_btn.get_attribute("class") or ""
                        btn_disabled_attr = generate_btn.get_attribute("disabled")
                        btn_aria_disabled = generate_btn.get_attribute("aria-disabled")
                        btn_href = generate_btn.get_attribute("href") or ""
                        _log(f"playwright: Generate button info: tag={btn_tag}, text={btn_text}, disabled_attr={btn_disabled_attr}, aria_disabled={btn_aria_disabled}, class={btn_class[:100]}")
                    except Exception as info_exc:
                        _log(f"playwright: could not read Generate button info: {info_exc}", level="WARN")

                    def _check_generate_blocked() -> tuple[bool, str]:
                        is_concurrent_blocked = False
                        is_visually_disabled = False
                        reason = ""
                        visual_reason = ""
                        try:
                            if generate_btn.is_disabled():
                                is_visually_disabled = True
                                visual_reason = "button disabled (is_disabled=True)"
                        except Exception:
                            pass
                        if not is_visually_disabled:
                            try:
                                disabled_attr = generate_btn.get_attribute("disabled")
                                if disabled_attr is not None:
                                    is_visually_disabled = True
                                    visual_reason = f"disabled attribute present: {disabled_attr}"
                            except Exception:
                                pass
                        if not is_visually_disabled:
                            try:
                                btn_class = generate_btn.get_attribute("class") or ""
                                cls_lower = btn_class.lower()
                                if "disabled" in cls_lower or "muted" in cls_lower or "inactive" in cls_lower:
                                    is_visually_disabled = True
                                    visual_reason = f"class contains disabled/muted/inactive: {btn_class[:120]}"
                            except Exception:
                                pass
                        if not is_visually_disabled:
                            try:
                                aria_disabled = generate_btn.get_attribute("aria-disabled")
                                if aria_disabled and aria_disabled.lower() == "true":
                                    is_visually_disabled = True
                                    visual_reason = "aria-disabled=true"
                            except Exception:
                                pass
                        if not is_visually_disabled:
                            try:
                                opacity = generate_btn.evaluate("el => window.getComputedStyle(el).opacity")
                                pointer_events = generate_btn.evaluate("el => window.getComputedStyle(el).pointerEvents")
                                cursor = generate_btn.evaluate("el => window.getComputedStyle(el).cursor")
                                _log(f"playwright: Generate button CSS: opacity={opacity}, pointerEvents={pointer_events}, cursor={cursor}")
                                if opacity and float(opacity) < 0.5:
                                    is_visually_disabled = True
                                    visual_reason = f"opacity too low: {opacity}"
                                if pointer_events and pointer_events == "none":
                                    is_visually_disabled = True
                                    visual_reason = f"pointer-events=none"
                            except Exception as css_exc:
                                _log(f"playwright: CSS check failed: {css_exc}", level="WARN")
                        try:
                            generate_btn.hover(timeout=3000)
                            page.wait_for_timeout(1500)
                            tooltip_texts = []
                            try:
                                tooltip_els = page.locator('[role="tooltip"], [data-state="delayed-open"], [data-radix-tooltip-content], [class*="Tooltip"], [class*="tooltip"]').all()
                                for tel in tooltip_els:
                                    try:
                                        if tel.is_visible(timeout=500):
                                            tt = tel.inner_text().strip()
                                            if tt and len(tt) < 300:
                                                tooltip_texts.append(tt)
                                    except Exception:
                                        continue
                            except Exception:
                                pass
                            try:
                                title_attr = generate_btn.get_attribute("title") or ""
                                if title_attr:
                                    tooltip_texts.append(title_attr)
                            except Exception:
                                pass
                            try:
                                aria_label = generate_btn.get_attribute("aria-label") or ""
                                if aria_label:
                                    tooltip_texts.append(aria_label)
                            except Exception:
                                pass
                            _log(f"playwright: Generate button hover tooltips: {tooltip_texts}")
                            for tt in tooltip_texts:
                                tl = tt.lower()
                                if any(kw in tl for kw in [
                                    "please wait", "switch to credits", "still generating",
                                    "concurrent", "limit reached", "max tasks", "queue full",
                                    "no credits", "insufficient", "upgrade",
                                    "任务", "等待", "排队", "额度", "上限",
                                ]):
                                    is_concurrent_blocked = True
                                    reason = f"tooltip: {tt[:100]}"
                                    break
                        except Exception as hover_exc:
                            _log(f"playwright: hover check failed: {hover_exc}", level="WARN")
                        if not is_concurrent_blocked:
                            try:
                                page_html = generate_btn.evaluate("el => el.outerHTML")[:500]
                                _log(f"playwright: Generate button HTML: {page_html}")
                            except Exception:
                                pass
                        _log(f"playwright: Generate button check result: is_visually_disabled={is_visually_disabled}({visual_reason}), is_concurrent_blocked={is_concurrent_blocked}({reason})")
                        return is_concurrent_blocked, reason, is_visually_disabled, visual_reason

                    is_concurrent_blocked, block_reason, is_visually_disabled, visual_reason = _check_generate_blocked()
                    if is_concurrent_blocked:
                        _log(f"playwright: Generate button BLOCKED by concurrent limit ({block_reason}); marking account capacity unavailable", level="WARN")
                        raise Exception(
                            f"PLUGIN_ERROR:::Generate 按钮不可用（{block_reason}），"
                            "该账号并发任务已满或被外部任务占用"
                        )
                    if is_visually_disabled:
                        _log(f"playwright: Generate button appears disabled ({visual_reason}), but no concurrent limit detected, will try force click", level="WARN")
                    _captured_task_ids2 = []
                    _captured_gen_responses2 = []
                    _captured_task_video_urls2 = []
                    _last_net_task_status2 = {"value": ""}

                    # Record all existing video, source, and download URLs to exclude them from generated results
                    existing_video_urls2 = set()
                    try:
                        for v in page.locator("video").all():
                            src = v.get_attribute("src") or ""
                            if src.startswith("http") or src.startswith("blob:"):
                                existing_video_urls2.add(src)
                        for s in page.locator("video source").all():
                            src = s.get_attribute("src") or ""
                            if src.startswith("http") or src.startswith("blob:"):
                                existing_video_urls2.add(src)
                        for link in page.locator('a[download], a:has-text("Download"), button:has-text("Download"), button:has-text("下载")').all():
                            href = link.get_attribute("href") or ""
                            if href.startswith("http") or href.startswith("blob:"):
                                existing_video_urls2.add(href)
                        _log(f"playwright: recorded {len(existing_video_urls2)} existing video/source/download URLs to exclude: {existing_video_urls2}")
                    except Exception as ex_exc:
                        _log(f"playwright: failed to record existing video URLs: {ex_exc}", level="WARN")

                    def _on_gen_response2(response):
                        try:
                            url = response.url
                            lower_url = url.lower()
                            method = response.request.method
                            is_task_create = method == "POST" and "/v1/tasks" in lower_url
                            is_task_poll = "/v1/tasks/" in lower_url
                            is_asset_detail = "/v1/assets/" in lower_url and bool(_captured_task_ids2)
                            if not (is_task_create or is_task_poll or is_asset_detail):
                                return
                            if is_task_create:
                                _log(f"playwright: NET intercepted POST {url} status={response.status}")
                            try:
                                body = response.json()
                            except Exception:
                                try:
                                    text = response.text()[:500]
                                    _log(f"playwright: NET response text: {text}")
                                except Exception:
                                    pass
                                return

                            status = _extract_runway_task_status(body)
                            if status and status != _last_net_task_status2.get("value"):
                                _last_net_task_status2["value"] = status
                                _log(f"playwright: NET current task status={status}")

                            if is_task_create:
                                try:
                                    _log(f"playwright: NET response body keys={list(body.keys())[:10]}")
                                    tid = _extract_runway_task_id(body)
                                    if tid and isinstance(body.get("task"), dict):
                                        task_obj = body["task"]
                                        _log(f"playwright: NET extracted task_id from body.task: {tid}")
                                        for k, v in task_obj.items():
                                            _log(f"playwright: NET task.{k}={str(v)[:100]}")
                                    elif tid:
                                        _log(f"playwright: NET extracted task_id: {tid}")
                                    if tid and str(tid) not in _captured_task_ids2:
                                        _captured_task_ids2.append(str(tid))
                                        _log(f"playwright: NET captured task_id={tid}")
                                    elif not tid:
                                        _log(f"playwright: NET could not find task_id in response, full body: {json.dumps(body)[:500]}")
                                    _captured_gen_responses2.append({"url": url, "body": body})
                                except Exception as e:
                                    _log(f"playwright: NET task create parse error: {e}", level="WARN")

                            if _body_mentions_task_ids(body, _captured_task_ids2):
                                for candidate in _extract_runway_video_urls_from_body(body):
                                    if candidate not in _captured_task_video_urls2:
                                        _captured_task_video_urls2.append(candidate)
                                        _log(f"playwright: NET captured task-bound video url from {url}")
                        except Exception:
                            pass

                    page.on("response", _on_gen_response2)
                    try:
                        page.keyboard.press("Escape")
                        page.wait_for_timeout(300)
                        popups2 = page.locator('[role="listbox"], [role="dialog"], [class*="autocomplete" i], [class*="suggestion" i], [class*="dropdown" i], [class*="popover" i], [class*="tooltip" i]').all()
                        for popup in popups2:
                            try:
                                if popup.is_visible(timeout=200):
                                    _log(f"playwright: dismissing popup overlay before Generate click")
                                    page.keyboard.press("Escape")
                                    page.wait_for_timeout(300)
                                    break
                            except Exception:
                                continue
                    except Exception:
                        pass
                    pre_click_url2 = page.url
                    _log(f"playwright: pre-click URL: {pre_click_url2}")
                    _ensure_on_generate_page("click Generate")
                    generate_btn.click(force=True)
                    generate_btn_clicked = True
                    _log("playwright: clicked Generate button")
                    generate_clicked_at2 = time.time()
                    page.wait_for_timeout(3000)
                    _confirm_policy_violation(page, {}, required_count=3)
                    _confirm_runway_technical_glitch(page, {}, required_count=3)
                    post_click_url2 = page.url
                    if post_click_url2 != pre_click_url2:
                        _log(f"playwright: page navigated after Generate click! pre={pre_click_url2} post={post_click_url2}")
                        if "runwayml.com" in post_click_url2 and "generate" in post_click_url2.lower():
                            _log("playwright: navigated to another generate page, will continue on new page")
                        elif "runwayml.com" in post_click_url2:
                            _log(f"playwright: navigated to non-generate runwayml page, waiting briefly then navigating back", level="WARN")
                            page.wait_for_timeout(2000)
                            try:
                                page.goto(generate_url, wait_until="domcontentloaded")
                                page.wait_for_timeout(3000)
                                _log(f"playwright: navigated back to generate URL: {generate_url}")
                            except Exception as nav_back_exc2:
                                _log(f"playwright: navigate back to generate URL failed: {nav_back_exc2}", level="ERROR")
                        else:
                            _log("playwright: navigation went outside runwayml.com, attempting to go back", level="WARN")
                            try:
                                page.go_back(wait_until="domcontentloaded")
                                page.wait_for_timeout(3000)
                            except Exception:
                                pass
                    try:
                        error_toast2 = page.locator('[class*="toast" i][class*="error" i], [class*="error" i][class*="message" i], [role="alert"]').first
                        if error_toast2.is_visible(timeout=1500):
                            err_text2 = error_toast2.inner_text().strip()[:200]
                            _log(f"playwright: error toast after click: {err_text2}", level="WARN")
                            if "concurrent" in err_text2.lower() or "capacity" in err_text2.lower() or "limit" in err_text2.lower():
                                raise Exception(
                                    f"PLUGIN_ERROR:::点击Generate后出现并发限制错误（{err_text2}），切换账号"
                                )
                    except Exception as toast_exc2:
                        if "PLUGIN_ERROR" in str(toast_exc2):
                            raise
                        pass

                    generation_started2 = False
                    try:
                        page.wait_for_timeout(2000)
                        try:
                            in_queue_el2 = page.locator('text=/in queue/i').first
                            if in_queue_el2.is_visible(timeout=3000):
                                iq_txt2 = in_queue_el2.inner_text().strip()[:200]
                                generation_started2 = True
                                _log(f"playwright: generation confirmed started - In Queue: '{iq_txt2}'")
                        except Exception:
                            pass
                        if not generation_started2:
                            try:
                                queue_msg2 = page.locator('text=/will start in a few/i').first
                                if queue_msg2.is_visible(timeout=1000):
                                    generation_started2 = True
                                    _log("playwright: generation confirmed started - queue message found")
                            except Exception:
                                pass
                        if not generation_started2:
                            gen_indicators2 = [
                                'text=/queued|processing|generating|rendering|in progress|排队|生成中|渲染中|处理中/i',
                                '[class*="progress" i]',
                                '[class*="Progress"]',
                                '[class*="generation-status" i]',
                                '[class*="GenerationStatus"]',
                                '[class*="queue" i]',
                                '[class*="Queue"]',
                                '[class*="task-card" i]',
                                '[class*="TaskCard"]',
                                '[class*="output" i][class*="item" i]',
                                '[data-testid*="progress"]',
                                '[data-testid*="generation"]',
                            ]
                            for gi2_sel in gen_indicators2:
                                try:
                                    gi2_els = page.locator(gi2_sel).all()
                                    for gi2_el in gi2_els:
                                        if gi2_el.is_visible(timeout=500):
                                            gi2_txt = gi2_el.inner_text().strip()[:100]
                                            if gi2_txt:
                                                generation_started2 = True
                                                _log(f"playwright: generation confirmed started - indicator: '{gi2_txt}' (sel={gi2_sel[:50]})")
                                                break
                                    if generation_started2:
                                        break
                                except Exception:
                                    continue
                        if not generation_started2:
                            try:
                                percent_els2 = page.locator('text=/\\d+%/').all()
                                for pel2 in percent_els2:
                                    if pel2.is_visible(timeout=500):
                                        generation_started2 = True
                                        _log(f"playwright: generation confirmed started - percent: '{pel2.inner_text().strip()}'")
                                        break
                            except Exception:
                                pass
                        if not generation_started2:
                            new_videos2 = page.locator("video").all()
                            for nv2 in new_videos2:
                                try:
                                    if page.evaluate("el => el.closest('[class*=\"thumbnail\" i], [class*=\"preview\" i], [class*=\"slot-\" i], [class*=\"reference\" i], [data-testid*=\"reference\" i]') !== null", nv2):
                                        continue
                                except Exception:
                                    pass
                                src2 = nv2.get_attribute("src") or ""
                                if src2 in existing_video_urls2:
                                    continue
                                if src2.startswith("http") and not _is_empty_np(src2):
                                    generation_started2 = True
                                    _log("playwright: generation confirmed started - video element found")
                                    break
                        if not generation_started2:
                            _log("playwright: WARNING - no generation indicator found after click, Generate may not have triggered", level="WARN")
                            try:
                                page.screenshot(path=str(plugin_dir / f"_debug_nogen_{datetime.now().strftime('%Y%m%d_%H%M%S')}.png"))
                            except Exception:
                                pass
                    except Exception as gi2_exc:
                        _log(f"playwright: generation start check error: {gi2_exc}", level="WARN")
                else:
                    _log("playwright: Generate button not found with any selector", level="WARN")
                    try:
                        all_btns = page.locator("button").all()
                        btn_info = []
                        for b in all_btns[:20]:
                            try:
                                if b.is_visible(timeout=200):
                                    txt = b.inner_text().strip()[:30]
                                    cls = (b.get_attribute("class") or "")[:40]
                                    btn_info.append(f"[{txt}] class={cls}")
                            except Exception:
                                continue
                        _log(f"playwright: visible buttons on page: {btn_info}")
                    except Exception:
                        pass
                    try:
                        page.keyboard.press("Control+Enter")
                        _log("playwright: tried Ctrl+Enter as fallback")
                        page.wait_for_timeout(2000)
                    except Exception:
                        pass
            except Exception as exc:
                if "PLUGIN_ERROR" in str(exc):
                    raise
                _log(f"playwright: generate click failed: {exc}", level="WARN")

            _safe_progress(context, "Playwright: 等待生成结果")
            _EMPTY_STATE_PATTERNS_NP = ("emptystate", "empty-state", "touchpoint", "hero_comp", "product.webm", "demo/")
            _EMPTY_STATE_DOMAINS_NP = ("d3phaj0sisr2ct.cloudfront.net",)

            def _is_empty_np(url: str) -> bool:
                lower = url.lower()
                for pat in _EMPTY_STATE_PATTERNS_NP:
                    if pat in lower:
                        return True
                for dom in _EMPTY_STATE_DOMAINS_NP:
                    if dom in lower and "/app/" in lower:
                        return True
                return False

            deadline = time.time() + max(60, timeout_s)
            video_url = None
            poll_attempt = 0
            last_progress_text = ""
            poll_task_id = str(context.get("task_id") or "").strip()
            last_known_generate_url2 = generate_url
            policy_confirm_state2: dict[str, Any] = {}
            technical_glitch_state2: dict[str, Any] = {}
            while time.time() < deadline:
                poll_attempt += 1
                try:
                    _confirm_policy_violation(page, policy_confirm_state2, required_count=3)
                    _confirm_runway_technical_glitch(page, technical_glitch_state2, required_count=3)
                except Exception as p_exc:
                    if "PLUGIN_ERROR" in str(p_exc):
                        raise
                    try:
                        if page.is_closed():
                            _log("playwright: page was closed during polling, cannot continue", level="ERROR")
                            raise Exception("PLUGIN_ERROR:::浏览器页面被关闭，无法继续监控视频生成结果。请不要在生成过程中关闭浏览器页面")
                    except Exception as page_check_exc:
                        if "PLUGIN_ERROR" in str(page_check_exc):
                            raise
                        _log(f"playwright: page check failed: {page_check_exc}", level="ERROR")
                        raise Exception("PLUGIN_ERROR:::浏览器页面异常（可能已关闭），无法继续监控视频生成结果。请不要在生成过程中关闭浏览器页面")

                    try:
                        current_poll_url2 = page.url
                        if "runwayml.com" not in current_poll_url2 and "runway" not in current_poll_url2.lower():
                            _log(f"playwright: page navigated away during polling! current={current_poll_url2}, navigating back to {last_known_generate_url2}", level="WARN")
                            try:
                                page.goto(last_known_generate_url2, wait_until="domcontentloaded")
                                page.wait_for_timeout(3000)
                                if "/teams/guest/" in page.url or "login" in page.url.lower():
                                    _log("playwright: session expired during polling, attempting re-login", level="WARN")
                                    if cred and cred.get("email") and cred.get("password"):
                                        _auto_login_runwayml(page, cred["email"], cred["password"])
                                        page.wait_for_timeout(3000)
                                        page.goto(last_known_generate_url2, wait_until="domcontentloaded")
                                        page.wait_for_timeout(3000)
                            except Exception as nav_exc2:
                                _log(f"playwright: navigate back failed: {nav_exc2}", level="ERROR")
                        elif "runwayml.com" in current_poll_url2 and "generate" not in current_poll_url2.lower() and "video" not in current_poll_url2.lower():
                            _log(f"playwright: page on non-generate runwayml page during polling! current={current_poll_url2}, navigating back to {last_known_generate_url2}", level="WARN")
                            try:
                                page.goto(last_known_generate_url2, wait_until="domcontentloaded")
                                page.wait_for_timeout(3000)
                                if "/teams/guest/" in page.url or "login" in page.url.lower():
                                    _log("playwright: session expired during polling, attempting re-login", level="WARN")
                                    if cred and cred.get("email") and cred.get("password"):
                                        _auto_login_runwayml(page, cred["email"], cred["password"])
                                        page.wait_for_timeout(3000)
                                        page.goto(last_known_generate_url2, wait_until="domcontentloaded")
                                        page.wait_for_timeout(3000)
                            except Exception as nav_exc2:
                                _log(f"playwright: navigate back failed: {nav_exc2}", level="ERROR")
                    except Exception as poll_url_exc:
                        if "PLUGIN_ERROR" in str(poll_url_exc):
                            raise
                        _log(f"playwright: poll URL check error: {poll_url_exc}", level="WARN")

                    if _captured_task_video_urls2:
                        video_url = _captured_task_video_urls2[0]
                        _log("playwright: using task-bound network video url")
                        break

                    progress_text = ""
                    progress_pct = 0
                    try:
                        # 1. Evaluate JS on the page to find percentage values.
                        pct_val = page.evaluate("""() => {
                            const regex = /(\\d+)\\s*%/;
                            const selectors = [
                                '[class*="progress" i]', 
                                '[class*="percent" i]', 
                                '[class*="status" i]', 
                                '[data-testid*="progress" i]', 
                                '[role="progressbar"]'
                            ];
                            for (const sel of selectors) {
                                try {
                                    const elements = document.querySelectorAll(sel);
                                    for (const el of elements) {
                                        if (el.offsetWidth > 0 && el.offsetHeight > 0) {
                                            const valAttr = el.getAttribute('aria-valuenow');
                                            if (valAttr) {
                                                const val = parseInt(valAttr, 10);
                                                if (val > 0 && val < 100) return val;
                                            }
                                            const text = el.innerText || "";
                                            const match = text.match(regex);
                                            if (match) {
                                                const val = parseInt(match[1], 10);
                                                if (val > 0 && val < 100) return val;
                                            }
                                        }
                                    }
                                } catch (e) {}
                            }
                            try {
                                const walker = document.createTreeWalker(
                                    document.body,
                                    NodeFilter.SHOW_TEXT,
                                    null,
                                    false
                                );
                                let node;
                                while (node = walker.nextNode()) {
                                    const text = node.nodeValue;
                                    if (text && text.includes('%')) {
                                        const match = text.match(regex);
                                        if (match) {
                                            const val = parseInt(match[1], 10);
                                            if (val > 0 && val < 100) {
                                                const parent = node.parentElement;
                                                if (parent && parent.offsetWidth > 0 && parent.offsetHeight > 0) {
                                                    return val;
                                                }
                                            }
                                        }
                                    }
                                }
                            } catch (e) {}
                            return null;
                        }""")
                        if pct_val is not None:
                            progress_pct = int(pct_val)
                            progress_text = f"生成中 ({progress_pct}%)"
                        else:
                            # 2. Try selectors if JS did not find a numeric percentage
                            progress_selectors = [
                                '[class*="progress" i]',
                                '[class*="percent" i]',
                                '[data-testid*="progress" i]',
                                '[class*="generation-status" i]',
                                '[class*="task-status" i]',
                                '[class*="queue" i]',
                            ]
                            for sel in progress_selectors:
                                try:
                                    els = page.locator(sel).all()
                                    for el in els:
                                        if el.is_visible(timeout=200):
                                            txt = el.inner_text().strip()
                                            if txt and len(txt) < 100:
                                                progress_text = txt
                                                break
                                    if progress_text:
                                        break
                                except Exception:
                                    continue
                            
                            if not progress_text:
                                # Try simple status keyword match
                                try:
                                    status_texts = page.locator('text=/queued|processing|generating|rendering|in progress|排队|生成中|渲染中|处理中/i').all()
                                    for st_el in status_texts:
                                        if st_el.is_visible(timeout=200):
                                            txt = st_el.inner_text().strip()
                                            if txt:
                                                progress_text = txt
                                                break
                                except Exception:
                                    pass
                    except Exception as p_exc:
                        _log(f"playwright: progress scraping exception: {p_exc}", level="DEBUG")

                    if progress_text and progress_text != last_progress_text:
                        last_progress_text = progress_text
                        _log(f"playwright: generation progress: {progress_text}")

                    try:
                        allow_video_result2 = bool(_captured_task_ids2) and (time.time() - generate_clicked_at2 >= _MIN_RESULT_ACCEPT_SECONDS) and not _page_has_generation_activity(page)
                        if not allow_video_result2 and (poll_attempt <= 3 or poll_attempt % 12 == 0):
                            _log(
                                f"playwright: video result scan gated: task_id_seen={bool(_captured_task_ids2)} "
                                f"elapsed={time.time() - generate_clicked_at2:.1f}s active={_page_has_generation_activity(page)}",
                                level="DEBUG",
                            )
                        videos = page.locator("video").all() if allow_video_result2 else []
                        for v in videos:
                            try:
                                if page.evaluate("el => el.closest('[class*=\"thumbnail\" i], [class*=\"preview\" i], [class*=\"slot-\" i], [class*=\"reference\" i], [data-testid*=\"reference\" i], [class*=\"left\" i], [class*=\"control\" i], [class*=\"sidebar\" i], [class*=\"settings\" i]') !== null", v):
                                    continue
                            except Exception:
                                pass
                            src = v.get_attribute("src") or ""
                            if src in existing_video_urls2:
                                continue
                            if src.startswith("http") and not _is_empty_np(src):
                                video_url = src
                                break
                        if allow_video_result2 and not video_url:
                            sources = page.locator("video source").all()
                            for s in sources:
                                try:
                                    if page.evaluate("el => { const p = el.closest('video'); return p && p.closest('[class*=\"thumbnail\" i], [class*=\"preview\" i], [class*=\"slot-\" i], [class*=\"reference\" i], [data-testid*=\"reference\" i], [class*=\"left\" i], [class*=\"control\" i], [class*=\"sidebar\" i], [class*=\"settings\" i]') !== null; }", s):
                                        continue
                                except Exception:
                                    pass
                                src = s.get_attribute("src") or ""
                                if src in existing_video_urls2:
                                    continue
                                if src.startswith("http") and not _is_empty_np(src):
                                    video_url = src
                                    break
                    except Exception:
                        pass
                    if video_url:
                        break
                    try:
                        allow_download_result2 = bool(_captured_task_ids2) and (time.time() - generate_clicked_at2 >= _MIN_RESULT_ACCEPT_SECONDS) and not _page_has_generation_activity(page)
                        if not allow_download_result2:
                            raise RuntimeError("__skip_download_result_scan__")
                        download_links = page.locator('a[download], a:has-text("Download"), button:has-text("Download"), button:has-text("下载")').all()
                        for link in download_links:
                            href = link.get_attribute("href") or ""
                            if href.startswith("http"):
                                video_url = href
                                break
                    except Exception:
                        pass
                    if video_url:
                        break
                    elapsed = int(time.time() - (deadline - max(60, timeout_s)))
                    if progress_text:
                        if not progress_pct:
                            pct_match = re.search(r'(\d+)\s*%', progress_text)
                            if pct_match:
                                progress_pct = int(pct_match.group(1))
                        
                        lower_text = progress_text.lower()
                        if "queue" in lower_text or "排队" in lower_text:
                            msg = f"网页排队: {elapsed}秒"
                            progress_card.update(
                                f"网页正在乖乖排队中... 已等待 {elapsed} 秒，不要着急哦。💤",
                                "info",
                                f"🎬 网页排队中 | {progress_card.account_label}"
                            )
                        elif progress_pct > 0:
                            msg = "生成中"
                            progress_card.update(
                                f"视频正在加紧渲染中... 已完成 {progress_pct}%，胜利就在眼前！🎬",
                                "info",
                                f"🎬 渲染进度: {progress_pct}% | {progress_card.account_label}"
                            )
                        else:
                            msg = f"网页排队: {elapsed}秒"
                            progress_card.update(
                                f"网页正在排队或者处理中... 已等待 {elapsed} 秒 ⏰",
                                "info",
                                f"🎬 处理中 | {progress_card.account_label}"
                            )
                            
                        if "排队" in msg:
                            _safe_progress(context, msg, None)
                        else:
                            _safe_progress(context, msg, progress_pct if progress_pct > 0 else None)
                        if progress_pct > 0:
                            _update_task_runtime(poll_task_id, progress_pct=progress_pct)
                    else:
                        if poll_attempt % 3 == 0:
                            _safe_progress(context, f"网页排队: {elapsed}秒")
                        progress_card.update(
                            f"视频正在加紧生成中... 已等待 {elapsed} 秒，胜利就在眼前！🎬",
                            "info",
                            f"🎬 生成中 | {progress_card.account_label}"
                        )
                    page.wait_for_timeout(5000)

            if not video_url:
                raise Exception("PLUGIN_ERROR:::Playwright 模式未能获取视频URL，生成可能超时或失败")

            _log(f"playwright: video url: {_mask_secret(video_url, 15)}")
            if 'progress_card' in locals() and progress_card.active:
                progress_card.update(
                    "大功告成！视频已经妥妥拿下，快去欣赏你的杰作吧！🍿",
                    "success",
                    f"🎉 生成成功！ | {progress_card.account_label}"
                )
            return video_url

        except Exception as exc:
            if 'progress_card' in locals() and progress_card.active:
                err_msg = str(exc).replace("PLUGIN_ERROR:::", "")
                progress_card.update(
                    f"糟糕，翻车了！跑通失败，报错是: {err_msg[:60]}... 😭",
                    "error",
                    f"😭 运行报错 | {progress_card.account_label}"
                )
            if page is not None and debug_save_screenshot:
                try:
                    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
                    out_png = str(plugin_dir / f"_debug_fail_{ts}.png")
                    page.screenshot(path=out_png, full_page=True)
                    _log(f"debug: saved screenshot: {out_png}", level="WARN")
                except Exception:
                    pass
            _log_exc("playwright: generation failed")
            raise
        finally:
            if 'progress_card' in locals() and progress_card.active:
                time.sleep(5)
                progress_card.close()
            if not keep_browser and browser is not None:
                try:
                    if browser.is_connected():
                        browser.close()
                except Exception:
                    pass


def _build_headers(plugin_params: dict[str, Any]) -> dict[str, str]:
    site_profile = _get_site_profile(params=plugin_params)
    headers: dict[str, str] = {
        "User-Agent": (
            "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
            "AppleWebKit/537.36 (KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36"
        ),
        "Origin": site_profile.base_url,
        "Referer": site_profile.base_url + "/",
        "Accept": "application/json, text/plain, */*",
    }
    api_key = str(plugin_params.get("api_key") or "").strip()
    if api_key:
        headers["Authorization"] = f"Bearer {api_key}"
    cookie_text = str(plugin_params.get("cookie_header") or "").strip()
    if cookie_text:
        headers["Cookie"] = cookie_text
    return headers


def _download_video(url: str, headers: dict[str, str], output_path: str, timeout: int = 120) -> tuple[str, str]:
    t0 = time.time()
    total = 0
    tmp_path = output_path + ".part"
    try:
        if os.path.exists(tmp_path):
            os.remove(tmp_path)
    except Exception:
        pass
    try:
        with requests.get(url, headers=headers, stream=True, timeout=timeout) as r:
            r.raise_for_status()
            expected = 0
            try:
                expected = int(r.headers.get("Content-Length") or 0)
            except Exception:
                expected = 0
            with open(tmp_path, "wb") as f:
                for chunk in r.iter_content(chunk_size=1024 * 1024):
                    if chunk:
                        total += len(chunk)
                        f.write(chunk)
                f.flush()
                try:
                    os.fsync(f.fileno())
                except Exception:
                    pass
            if total <= 0:
                raise Exception("PLUGIN_ERROR:::视频下载失败：返回内容为空")
            if expected > 0 and total < expected:
                raise Exception(f"PLUGIN_ERROR:::视频下载不完整：已下载 {total} / {expected} bytes")
    except Exception:
        try:
            if os.path.exists(tmp_path):
                os.remove(tmp_path)
        except Exception:
            pass
        raise
    os.replace(tmp_path, output_path)
    _log(f"download: saved mp4={os.path.abspath(output_path)} bytes={total} elapsed={time.time() - t0:.1f}s")
    return "mp4", output_path


def _make_unique_output_path(output_dir_abs: str, base_name: str, context: dict[str, Any]) -> str:
    preferred_path = os.path.join(output_dir_abs, base_name + ".mp4")
    if not os.path.exists(preferred_path):
        return preferred_path
    task_id = _sanitize_token(str(context.get("task_id") or ""), max_len=40)
    submit_id = _sanitize_token(str(context.get("submit_id") or ""), max_len=40)
    suffix_parts = [part for part in (task_id, submit_id) if part]
    if not suffix_parts:
        suffix_parts.append(uuid.uuid4().hex[:10])
    unique_base = base_name + "__" + "__".join(suffix_parts)
    unique_path = os.path.join(output_dir_abs, unique_base + ".mp4")
    if not os.path.exists(unique_path):
        return unique_path
    for attempt in range(1, 1000):
        candidate = os.path.join(output_dir_abs, f"{unique_base}__r{attempt}.mp4")
        if not os.path.exists(candidate):
            return candidate
    raise Exception(f"PLUGIN_ERROR:::输出目录下存在过多重名文件: {output_dir_abs}")


def _download_and_save_video(
    context: dict,
    video_url: str,
    headers: dict[str, str],
    output_dir: str,
) -> list[str]:
    _safe_progress(context, "下载视频")
    viewer_index = _safe_int(context.get("viewer_index"), 0)
    unique_name = _sanitize_token(str(context.get("unique_name") or context.get("unique_id") or "")) or uuid.uuid4().hex[:10]
    generation_round = _safe_int(context.get("generation_round"), 0)
    output_position = context.get("output_position")
    position = 0
    if isinstance(output_position, list) and output_position:
        position = _safe_int(output_position[0], 0)
    elif output_position is not None:
        position = _safe_int(output_position, 0)
    base_name = f"runwayml_{unique_name}_r{generation_round}_p{position}"
    os.makedirs(output_dir, exist_ok=True)
    output_path = _make_unique_output_path(output_dir, base_name, context)
    _download_video(video_url, headers, output_path)
    return [output_path]


_VALID_MODELS = {
    "seedance_2.0",
}

_API_MODELS = set()

_WEB_ONLY_MODELS = {
    "seedance_2.0",
}

_I2V_MODELS = {"seedance_2.0"}
_T2V_MODELS = {"seedance_2.0"}
_V2V_MODELS = {"seedance_2.0"}
_T2I_MODELS = set()
_CHAR_MODELS = set()

_VALID_RATIOS = {
    "1280:720", "720:1280", "1104:832", "832:1104",
    "960:960", "1584:672", "672:1584",
    "16:9", "9:16", "1:1", "4:3", "3:4", "21:9",
}

_RATIO_MAP = {
    "16:9": "1280:720",
    "9:16": "720:1280",
    "1:1": "960:960",
    "4:3": "1104:832",
    "3:4": "832:1104",
    "21:9": "1584:672",
}

_DEFAULT_PARAMS: dict[str, Any] = {
    "site_profile": "runwayml",
    "mode": "playwright",
    "api_key": "",
    "api_base": RUNWAYML_API_BASE,
    "account_pool_path": account_pool_file,
    "model": "seedance_2.0",
    "generation_mode": "multi_reference",
    "aspect_ratio": "16:9",
    "duration": 8,
    "seed": "",
    "timeout": 6000,
    "timeout_options": "300,600,900,1200,1800,2400,3600,6000,7200,18000",
    "use_end_frame": True,
    "debug_save_screenshot": True,
    "playwright_headless": False,
    "playwright_browser": "chromium",
    "playwright_keep_browser": False,  # 暂未实装，固定每任务独立浏览器
    "use_paid_accounts": False,
    "auto_switch_account": True,
    "max_concurrent_tasks": 0,
    "concurrent_wait_timeout": 999999,
    "polling_method": "page",
    "smart_arrange": False,
    "playwright_zoom_factor": 1.0,
    "playwright_zoom_factor_options": "0.5,0.6,0.7,0.75,0.8,0.9,1.0",
    "smart_arrange_layout": "2x2",
    "target_page_width": 914,
    "target_page_height": 686,
    "aspect_ratio_options": "16:9,9:16,21:9,1:1,3:4,4:3",
    "duration_options": "4,5,6,7,8,9,10,11,12,13,14,15",
    "model_options": "seedance_2.0",
}

_GLOBAL_PARAMS: dict[str, Any] = _DEFAULT_PARAMS.copy()

try:
    from plugin_utils import load_plugin_config, update_plugin_param
except Exception:
    def _local_config_path(file_path: str) -> Path:
        try:
            base = Path(file_path)
        except Exception:
            base = Path(__file__)
        return base.resolve().with_name("runwayml_plugin_config.json")

    def load_plugin_config(file_path: str) -> dict:
        cfg_path = _local_config_path(file_path)
        try:
            return json.loads(cfg_path.read_text(encoding="utf-8"))
        except Exception:
            return {}

    def update_plugin_param(file_path: str, key: str, value: Any) -> None:
        cfg_path = _local_config_path(file_path)
        try:
            data = load_plugin_config(file_path) or {}
            data[str(key)] = value
            cfg_path.write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8")
        except Exception:
            pass

try:
    _GLOBAL_PARAMS.update(load_plugin_config(_PLUGIN_FILE) or {})
except Exception:
    pass


def generate(context: dict) -> list[str]:
    old_tag = _set_task_tag(context)
    try:
        started = time.time()
        _log("=" * 60)
        _log("RunwayML: generate start")

        from runway_sec import get_license
        get_license().require_valid()

        output_dir = context.get("project_path") or context.get("output_dir") or "."
        prompt, prompt_source = _extract_prompt_text(context)
        prompt, override_ratio, override_duration = _parse_prompt_override_params(prompt)
        context["prompt"] = prompt
        context["text"] = prompt

        plugin_params = context.get("plugin_params", {}) or {}
        params = _GLOBAL_PARAMS.copy()
        params.update(plugin_params)

        if override_ratio:
            _log(f"Prompt override: aspect_ratio={override_ratio}")
            params["aspect_ratio"] = override_ratio
        if override_duration:
            _log(f"Prompt override: duration={override_duration}")
            params["duration"] = override_duration

        site_profile = _get_site_profile(params=params, context=context)
        context["site_profile"] = site_profile.key
        task_id = str(context.get("task_id") or "").strip() or _make_task_id(context, site_profile)
        context["task_id"] = task_id

        output_position = context.get("output_position")
        task_position = 0
        if isinstance(output_position, list) and output_position:
            task_position = _safe_int(output_position[0], 0)
        elif output_position is not None:
            task_position = _safe_int(output_position, 0)

        runtime = _TaskRuntime(
            task_id=task_id,
            viewer_index=_safe_int(context.get("viewer_index"), 0),
            unique_name=_sanitize_token(context.get("unique_name") or context.get("unique_id") or "task", max_len=32) or "task",
            generation_round=_safe_int(context.get("generation_round"), 0),
            output_position=task_position,
            site_profile=site_profile.key,
            worker_id="",
            profile_dir="",
            port=0,
            account_alias="",
            status="queued",
        )
        _register_task_runtime(runtime)
        _log(f"task runtime registered: {asdict(runtime)}")

        mode = str(params.get("mode") or "api").strip().lower()
        model = str(params.get("model") or "seedance_2.0").strip()
        if model not in _VALID_MODELS:
            _log(f"warn: unknown model={model!r}, fallback to seedance_2.0")
            model = "seedance_2.0"

        if model in _WEB_ONLY_MODELS and mode == "api":
            _log(f"info: model={model} is web-only, switching to playwright mode")
            mode = "playwright"
            params["mode"] = "playwright"

        generation_mode = str(params.get("generation_mode") or params.get("generation_type") or "multi_reference").strip().lower()
        if generation_mode in ("first_end_frame", "first_end", "first_last_frame"):
            generation_mode = "keyframe"
        valid_gen_modes = ("multi_reference", "keyframe", "image_to_video", "text_to_video", "video_to_video", "text_to_image", "character_performance")
        if generation_mode not in valid_gen_modes:
            _log(f"warn: unknown generation_mode={generation_mode!r}, fallback to multi_reference")
            generation_mode = "multi_reference"
        if generation_mode == "image_to_video":
            generation_mode = "multi_reference"
        elif generation_mode == "text_to_video":
            generation_mode = "multi_reference"

        raw_ratio = str(params.get("aspect_ratio") or "16:9").strip() or "16:9"
        ratio = _RATIO_MAP.get(raw_ratio, raw_ratio)
        if ratio not in _VALID_RATIOS:
            _log(f"warn: unknown ratio={ratio!r}, fallback to 1280:720")
            ratio = "1280:720"

        duration_s = _safe_int(params.get("duration"), 8)
        if duration_s < 4:
            duration_s = 4
        if duration_s > 15:
            duration_s = 15

        seed_raw = str(params.get("seed") or "").strip()
        seed = int(seed_raw) if seed_raw and seed_raw.isdigit() else None
        if seed is not None and (seed < 0 or seed > 4294967295):
            seed = None
        timeout = max(60, _safe_int(params.get("timeout"), 6000))

        first_path = _norm_path(context.get("first_frame_path") or context.get("first_frame"))
        end_path = None
        if bool(params.get("use_end_frame", True)):
            end_path = _norm_path(context.get("end_frame_path") or context.get("end_frame"))
            
        all_video_paths: list[str] = []
        raw_video = context.get("video_path") or context.get("reference_video")
        if raw_video:
            p = _norm_path(raw_video)
            if p and p not in all_video_paths:
                all_video_paths.append(p)

        # Robustly look up all from reference_videos (can be dict or list under ZiZi Animation schema)
        ref_vids = context.get("reference_videos")
        if isinstance(ref_vids, dict) and ref_vids:
            sorted_keys = sorted(ref_vids.keys(), key=lambda k: int(k) if str(k).isdigit() else 999)
            for sk in sorted_keys:
                p = _norm_path(ref_vids[sk])
                if p and p not in all_video_paths:
                    all_video_paths.append(p)
        elif isinstance(ref_vids, list) and ref_vids:
            for item in ref_vids:
                p = _norm_path(item)
                if p and p not in all_video_paths:
                    all_video_paths.append(p)

        video_path = all_video_paths[0] if all_video_paths else None

        all_ref_paths: list[str] = []

        ref_images = context.get("reference_images")
        ref_image_paths = context.get("reference_image_paths")

        if isinstance(ref_images, list) and ref_images:
            for item in ref_images:
                p = _norm_path(item)
                if p and p not in all_ref_paths:
                    all_ref_paths.append(p)
        elif isinstance(ref_images, dict) and ref_images:
            sorted_keys = sorted(ref_images.keys(), key=lambda k: int(k) if str(k).isdigit() else 999)
            for sk in sorted_keys:
                v = ref_images.get(sk)
                if v:
                    p = _norm_path(v)
                    if p and p not in all_ref_paths:
                        all_ref_paths.append(p)

        if isinstance(ref_image_paths, (list, tuple)) and ref_image_paths:
            for item in ref_image_paths:
                p = _norm_path(item)
                if p and p not in all_ref_paths:
                    all_ref_paths.append(p)

        if first_path and first_path not in all_ref_paths:
            all_ref_paths.insert(0, first_path)
        if end_path and end_path not in all_ref_paths:
            all_ref_paths.append(end_path)

        if all_ref_paths and not first_path:
            first_path = all_ref_paths[0]
        if len(all_ref_paths) > 1 and not end_path:
            end_path = all_ref_paths[-1]

        all_ref_paths = all_ref_paths[:9]

        if generation_mode == "text_to_video":
            first_path = None
            end_path = None
            video_path = None
        elif generation_mode == "video_to_video":
            if not video_path:
                raise Exception("PLUGIN_ERROR:::video_to_video 模式需要提供 video_path")
            first_path = None
            end_path = None
        elif generation_mode == "text_to_image":
            first_path = None
            end_path = None
            video_path = None
            if not prompt:
                raise Exception("PLUGIN_ERROR:::text_to_image 模式需要提供提示词")
        elif generation_mode == "character_performance":
            if not first_path:
                raise Exception("PLUGIN_ERROR:::character_performance 模式需要提供角色图片(first_frame)")
            if not video_path:
                raise Exception("PLUGIN_ERROR:::character_performance 模式需要提供表演视频(video_path)")
            end_path = None
        else:
            if not first_path and not prompt:
                raise Exception("PLUGIN_ERROR:::需要提供参考图片或提示词")

        _log(
            f"inputs: mode={mode} model={model} gen_mode={generation_mode} "
            f"first={'(none)' if not first_path else first_path} "
            f"end={'(none)' if not end_path else end_path} "
            f"video={'(none)' if not video_path else video_path} "
            f"ratio={ratio} duration={duration_s}s prompt_len={len(prompt)}"
        )

        api_key = str(params.get("api_key") or "").strip()
        api_base = str(params.get("api_base") or RUNWAYML_API_BASE).strip()
        account: dict[str, Any] | None = None
        account_alias = ""
        account_released = False

        _ACCOUNT_MGR.load_from_pool(params, site_profile)
        _ACCOUNT_MGR.load_from_vault()
        _ACCOUNT_MGR.sync_disabled_state()
        _log(f"playwright: accounts loaded: {[(a, s.disabled, s.active_tasks) for a, s in _ACCOUNT_MGR._slots.items()]}")
        _log(f"playwright: _DISABLED_ACCOUNTS={_DISABLED_ACCOUNTS}")

        lifecycle = _TaskLifecycle(
            task_id=task_id,
            model=model,
            generation_type=generation_mode,
            created_at=time.time(),
        )
        _TASK_MONITOR.register(lifecycle)
        _sched_task = _TASK_SCHEDULER.submit(task_id)
        _safe_progress(context, f"Playwright: 并发排队(第{_sched_task.queue_position}位)" if _sched_task.queue_position > 1 else "Playwright: 并发排队(第1位)")
        max_concurrent = int(params.get("max_concurrent_tasks") or 0)
        if max_concurrent > 0:
            _TASK_SCHEDULER.set_max_concurrent(max_concurrent)
        else:
            enabled_count = sum(1 for s in _ACCOUNT_MGR._slots.values() if not s.disabled) if _ACCOUNT_MGR._slots else 2
            auto_max = max(enabled_count * _MAX_CONCURRENT_PER_ACCOUNT, 1)
            _TASK_SCHEDULER.set_max_concurrent(auto_max)

        if mode == "api":
            _api_failed_aliases: list[str] = []
            acct_slot, sched_info = _TASK_SCHEDULER.acquire_slot(task_id, timeout_s=60, exclude_aliases=_api_failed_aliases, context=context)
            if acct_slot is None:
                if not api_key:
                    raise Exception(
                        "PLUGIN_ERROR:::未提供 API Key 且所有账号已满（调度器等待超时）。"
                        "请添加更多账号或等待当前任务完成"
                    )
            if acct_slot:
                api_key = acct_slot.api_key or api_key
                account_alias = acct_slot.alias
                account = {"api_key": api_key, "alias": account_alias}
                context["_runtime_account"] = dict(account)
                _log(f"API: scheduler acquired account alias={account_alias}")
            elif not api_key:
                raise Exception(
                    "PLUGIN_ERROR:::未提供 API Key 且账号池为空。"
                    "请在插件参数中设置 api_key 或在 account_pool_path 指向的文件中添加 API Key"
                )
            _update_task_runtime(task_id, status="generating", account_alias=account_alias)

            retry_budget = 3
            last_exc: Exception | None = None
            video_url = ""
            for attempt in range(1, retry_budget + 1):
                try:
                    video_url = _generate_via_api(
                        context=context,
                        params=params,
                        prompt=prompt,
                        first_path=first_path,
                        end_path=end_path,
                        video_path=video_path,
                        model=model,
                        duration_s=duration_s,
                        ratio=ratio,
                        timeout_s=timeout,
                        seed=seed,
                        api_key=api_key,
                        api_base=api_base,
                        generation_type=generation_mode,
                    )
                    break
                except Exception as exc:
                    last_exc = exc
                    msg = str(exc or "")
                    if "429" in msg or "rate_limit" in msg.lower() or "quota" in msg.lower():
                        _log(f"API: rate limited, attempt={attempt}/{retry_budget}")
                        if account_alias:
                            _TASK_SCHEDULER.release_slot(task_id, success=False, error_msg=msg)
                            if account_alias not in _api_failed_aliases:
                                _api_failed_aliases.append(account_alias)
                        if attempt < retry_budget:
                            next_slot, next_sched = _TASK_SCHEDULER.acquire_slot(task_id, timeout_s=30, exclude_aliases=_api_failed_aliases, context=context)
                            if next_slot and next_slot.api_key != api_key:
                                account_alias = next_slot.alias
                                api_key = next_slot.api_key
                                account = {"api_key": api_key, "alias": account_alias}
                                context["_runtime_account"] = dict(account)
                                _log(f"API: scheduler switched to account alias={account_alias}")
                                continue
                    raise
            if not video_url:
                if last_exc is not None:
                    raise last_exc
                raise Exception("PLUGIN_ERROR:::未能获取视频链接")

        elif mode == "playwright":
            pw_slot = None
            pw_retry_budget = 3
            pw_last_exc: Exception | None = None
            concurrent_wait_timeout = int(params.get("concurrent_wait_timeout") or 999999)
            _queue_round = 0
            _pw_failed_aliases = []
            total_accounts = len(_ACCOUNT_MGR._slots) if _ACCOUNT_MGR._slots else 0
            while True:
                _queue_round += 1
                _got_slot = False
                
                # If all enabled accounts have failed once, clear the exclusions to allow retrying them
                enabled_accounts = [a for a, s in _ACCOUNT_MGR._slots.items() if not s.disabled]
                if len(_pw_failed_aliases) >= len(enabled_accounts) and enabled_accounts:
                    _log(f"playwright: all enabled accounts ({enabled_accounts}) have been excluded/failed, clearing failed list {_pw_failed_aliases} to retry")
                    _pw_failed_aliases.clear()
                    
                for pw_retry in range(1, pw_retry_budget + 1):
                    pw_slot = None
                    pw_generation_ready = False
                    try:
                        _log(f"playwright: queue_round={_queue_round} retry={pw_retry}/{pw_retry_budget} task={task_id}")
                        acct_slot, sched_info = _TASK_SCHEDULER.acquire_slot(
                            task_id,
                            timeout_s=concurrent_wait_timeout,
                            exclude_aliases=_pw_failed_aliases,
                            exclude_teams=[],
                            context=context
                        )
                        if acct_slot is None:
                            enabled_accounts = sum(1 for s in _ACCOUNT_MGR._slots.values() if not s.disabled) if _ACCOUNT_MGR._slots else 0
                            total_accounts = len(_ACCOUNT_MGR._slots) if _ACCOUNT_MGR._slots else 0
                            disabled_accounts = total_accounts - enabled_accounts
                            sched_snap = _TASK_SCHEDULER.status_snapshot()
                            if enabled_accounts > 0:
                                raise Exception(
                                    f"PLUGIN_ERROR:::所有账号并发已满，调度器等待超时（{concurrent_wait_timeout}秒）。"
                                    f"当前共 {enabled_accounts} 个启用账号，最大并发 {sched_snap.get('max_concurrent', '?')}。"
                                    f"调度状态: 排队={sched_snap.get('queued',0)} 执行中={sched_snap.get('running',0)}。"
                                    "请添加更多账号或等待任务完成"
                                )
                            if total_accounts > 0 and disabled_accounts == total_accounts:
                                raise Exception(
                                    f"PLUGIN_ERROR:::所有 {total_accounts} 个账号均已停用，没有可用账号。"
                                    "请在插件界面的「账号管理」中启用至少一个账号"
                                )
                            _log("playwright: no account from pool, creating default slot", level="WARN")
                            acct_slot = _AccountSlot(
                                alias="default",
                                api_key="",
                                email="",
                                password_enc="",
                                cookie_header=str(params.get("cookie_header") or "").strip(),
                                storage_state_path=str(params.get("playwright_storage_state") or "").strip(),
                            )
                        account_alias = acct_slot.alias
                        if acct_slot.disabled or account_alias in _DISABLED_ACCOUNTS:
                            _log(f"playwright: BLOCKED - account {account_alias} is disabled, releasing via scheduler", level="ERROR")
                            _TASK_SCHEDULER.release_slot(task_id, success=False, error_msg="account is disabled")
                            account_released = True
                            continue
                        account = {"api_key": acct_slot.api_key, "alias": account_alias}
                        context["_runtime_account"] = dict(account)
                        _log(f"playwright: scheduler acquired alias={account_alias} active={acct_slot.active_tasks} "
                             f"queue_pos={sched_info.queue_position if sched_info else '?'} round={_queue_round}")
                        _got_slot = True

                        pw_account_alias = account_alias
                        pw_slot = None
                        pw_acquire_retries = 6
                        for pw_attempt in range(1, pw_acquire_retries + 1):
                            pw_slot = _BROWSER_POOL.acquire(
                                account_alias=pw_account_alias,
                                task_id=task_id,
                                headless=bool(params.get("playwright_headless", False)),
                                storage_state_path=str(acct_slot.storage_state_path or params.get("playwright_storage_state") or "").strip(),
                                cookie_header=str(acct_slot.cookie_header or params.get("cookie_header") or "").strip(),
                                smart_arrange=bool(params.get("smart_arrange", False)),
                                browser_channel=str(params.get("playwright_browser") or "").strip(),
                                zoom_factor=params.get("playwright_zoom_factor") or params.get("playwright_scale_factor") or "auto",
                                arrange_layout=str(params.get("smart_arrange_layout") or "2x2").strip(),
                            )
                            if pw_slot is not None:
                                break
                            pool_stats = _BROWSER_POOL.stats()
                            _log(f"playwright: browser acquire attempt {pw_attempt}/{pw_acquire_retries} failed, pool={pool_stats}", level="WARN")
                            if pw_attempt < pw_acquire_retries:
                                _safe_progress(context, "Playwright: 等待浏览器...")
                                time.sleep(15)
                        if pw_slot is None:
                            pool_stats = _BROWSER_POOL.stats()
                            _TASK_SCHEDULER.release_slot(task_id, success=False, error_msg="browser pool exhausted")
                            account_released = True
                            raise Exception(
                                f"PLUGIN_ERROR:::无法获取浏览器实例（尝试{pw_acquire_retries}次）。"
                                f"浏览器池状态: busy={pool_stats.get('busy',0)}/{pool_stats.get('max_browsers',8)}。"
                                f"请检查: 1) Playwright 是否安装 2) Chromium 是否下载 3) 是否有浏览器进程残留"
                            )

                        if acct_slot.email and acct_slot.password_enc:
                            cred = {"email": acct_slot.email, "password": acct_slot.password_enc}
                            _log(f"playwright: using email/password from account slot for '{pw_account_alias}'")
                        else:
                            cred = _CREDENTIAL_VAULT.get_credential(pw_account_alias)
                            _log(f"playwright: credential lookup for alias '{pw_account_alias}': found={cred is not None}")
                            if not cred or not cred.get("email") or not cred.get("password"):
                                all_aliases = _CREDENTIAL_VAULT.list_aliases()
                                if all_aliases:
                                    for alias_key in all_aliases:
                                        c = _CREDENTIAL_VAULT.get_credential(alias_key)
                                        if c and c.get("email") and c.get("password"):
                                            cred = c
                                            _log(f"playwright: using credentials from vault alias '{alias_key}'")
                                            break
                            if not cred or not cred.get("email") or not cred.get("password"):
                                raise Exception(
                                    f"PLUGIN_ERROR:::账号 '{pw_account_alias}' 未找到登录凭证。"
                                    "请在插件界面的「账号管理」中添加账号（邮箱----密码格式），"
                                    "或检查账号池文件路径是否正确"
                                )

                        video_url = _generate_via_playwright_with_slot(
                            context=context,
                            params=params,
                            prompt=prompt,
                            first_path=first_path,
                            end_path=end_path,
                            model=model,
                            duration_s=duration_s,
                            ratio=ratio,
                            timeout_s=timeout,
                            browser_slot=pw_slot,
                            cred=cred,
                            generation_mode=generation_mode,
                            all_ref_paths=all_ref_paths,
                            video_path=video_path,
                            all_video_paths=all_video_paths,
                        )
                        pw_generation_ready = True
                        break
                    except Exception as pw_exc:
                        pw_last_exc = pw_exc
                        slot_was_closed = False
                        if pw_slot:
                            try:
                                slot_was_closed = bool(
                                    (not getattr(pw_slot, "is_alive", True))
                                    or (getattr(pw_slot, "page", None) is not None and pw_slot.page.is_closed())
                                )
                            except Exception:
                                slot_was_closed = True
                        if pw_slot:
                            _BROWSER_POOL.release(pw_slot.slot_id, keep_alive=False)
                            pw_slot = None
                        if account_alias and not account_released:
                            _TASK_SCHEDULER.release_slot(task_id, success=False, error_msg=str(pw_exc))
                            account_released = True
                        msg = str(pw_exc)
                        
                        # These are terminal for the current task: do not retry the same prompt on other accounts.
                        is_policy_violation = _is_prompt_policy_error(msg)
                        if is_policy_violation:
                            _log(f"playwright: PROMPT/CONTENT POLICY VIOLATION detected: {msg}. Aborting immediately without switching accounts to prevent account pool suspension.", level="ERROR")
                            raise pw_exc
                        
                        # Manual close/cancel is also terminal: the user intentionally stopped this task.
                        is_manual_cancel = slot_was_closed or _is_manual_close_error(msg)
                        if is_manual_cancel:
                            _log(
                                f"playwright: BROWSER CLOSED/MANUAL CANCEL detected "
                                f"(slot_was_closed={slot_was_closed}): {msg}. "
                                "Aborting task immediately without switching accounts.",
                                level="ERROR",
                            )
                            raise pw_exc
                        
                        # Set a cooldown if Runway is at capacity or an external task occupies the account.
                        is_capacity_err = "并发" in msg or "灰色" in msg or "GRAY" in msg or "不可用" in msg or "disabled" in msg.lower() or "concurrent" in msg.lower() or "at capacity" in msg.lower()
                        if is_capacity_err:
                            aslot = _ACCOUNT_MGR.get_slot(account_alias)
                            if aslot:
                                aslot.cooldown_until = time.time() + _CAPACITY_COOLDOWN_SECONDS
                                _log(f"playwright: set capacity cooldown for {account_alias} {_CAPACITY_COOLDOWN_SECONDS}s until {aslot.cooldown_until}")
                        
                        if account_alias and account_alias not in _pw_failed_aliases:
                            _pw_failed_aliases.append(account_alias)
                            _log(f"playwright: added failed account '{account_alias}' to exclusions: {_pw_failed_aliases}")

                        # If it's a non-capacity error and all enabled accounts have failed, abort immediately
                        if not is_capacity_err:
                            enabled_accounts = [a for a, s in _ACCOUNT_MGR._slots.items() if not s.disabled]
                            if len(_pw_failed_aliases) >= len(enabled_accounts) and enabled_accounts:
                                _log(f"playwright: all enabled accounts tried and failed with non-capacity error ({_pw_failed_aliases}), raising last error: {msg}", level="ERROR")
                                raise pw_exc

                        if is_capacity_err:
                            _log(f"playwright: account {account_alias} at capacity (attempt {pw_retry}/{pw_retry_budget}), will retry after waiting")
                            sched_snap = _TASK_SCHEDULER.status_snapshot()
                            _log(f"playwright: all accounts at capacity (queue round {_queue_round}), waiting for slot... "
                                 f"[Q={sched_snap.get('queued',0)} R={sched_snap.get('running',0)}]")
                            _safe_progress(context, "Playwright: 并发排队(第1位)")
                            
                            # If all accounts have been tried and found at capacity, clear failed list to allow any to be acquired during wait
                            enabled_accounts = [a for a, s in _ACCOUNT_MGR._slots.items() if not s.disabled]
                            if len(_pw_failed_aliases) >= len(enabled_accounts):
                                _log(f"playwright: all accounts at capacity, clearing fail list {_pw_failed_aliases} to allow waiting/cooldown retry")
                                _pw_failed_aliases.clear()

                            wait_s = min(30, max(5, int(params.get("capacity_retry_wait", 10) or 10)))
                            _log(f"playwright: capacity retry sleeping {wait_s}s before re-entering scheduler")
                            time.sleep(wait_s)
                            account_alias = ""
                            account_released = False
                            _got_slot = False
                            break
                                
                            wait_slot, wait_sched = _TASK_SCHEDULER.acquire_slot(
                                task_id,
                                timeout_s=concurrent_wait_timeout,
                                exclude_aliases=_pw_failed_aliases,
                                exclude_teams=[],
                                context=context
                            )
                            if wait_slot is not None:
                                acct_slot = wait_slot
                                account_alias = ""
                                account_released = False
                                _got_slot = False   # Reset so we don't break out of the while True loop!
                                break
                            raise Exception(
                                f"PLUGIN_ERROR:::所有账号并发已满，调度器等待超时（{concurrent_wait_timeout}秒）。"
                                f"当前共 {total_accounts} 个账号，最大并发 {sched_snap.get('max_concurrent', '?')}。"
                                f"调度状态: 排队={sched_snap.get('queued',0)} 执行中={sched_snap.get('running',0)}。"
                                "请添加更多账号或等待任务完成"
                            )
                        
                        # For other non-capacity errors, immediately log and break to try the next account in the next round
                        _log(f"playwright: account {account_alias} failed with non-capacity error: {msg}, immediately switching to next account", level="WARN")
                        account_alias = ""
                        account_released = False
                        _got_slot = False
                        break
                    finally:
                        if pw_slot and not pw_generation_ready:
                            _BROWSER_POOL.release(pw_slot.slot_id, keep_alive=False)
                if _got_slot:
                    break
            else:
                if pw_last_exc:
                    raise pw_last_exc
                raise Exception("PLUGIN_ERROR:::Playwright 模式所有重试均失败")
        else:
            raise Exception(f"PLUGIN_ERROR:::不支持的模式: {mode}")

        headers = _build_headers(params)
        if pw_slot and getattr(pw_slot, "context", None):
            try:
                browser_cookies = pw_slot.context.cookies()
                cookie_header = "; ".join(
                    f"{c.get('name')}={c.get('value')}"
                    for c in browser_cookies
                    if c.get("name") and c.get("value") is not None
                )
                if cookie_header:
                    headers["Cookie"] = cookie_header
                    _log(f"download: using {len(browser_cookies)} cookies from active browser context")
            except Exception as cookie_exc:
                _log(f"download: could not extract browser cookies before download: {cookie_exc}", level="WARN")
        _log(f"headers: Authorization={'***' if headers.get('Authorization') else 'none'}")
        _update_task_runtime(task_id, status="downloading")
        out = _download_and_save_video(context, video_url, headers, output_dir)
        if pw_slot:
            _BROWSER_POOL.release(pw_slot.slot_id, keep_alive=False)
            pw_slot = None
            _log(f"playwright: released browser slot after video download completed")
        if out:
            _update_task_runtime(task_id, status="completed", output_path=str(out[0]))
            _TASK_MONITOR.update(task_id, status="completed", completed_at=time.time(), output_path=str(out[0]))
            if account_alias and not account_released:
                _TASK_SCHEDULER.release_slot(task_id, success=True)
                account_released = True
                _log(f"task scheduler released: task={task_id} alias={account_alias} status=success")
            _log(f"task runtime completed: {_snapshot_task_runtime(task_id)}")
        _log(f"generate done: files={len(out)} elapsed={time.time() - started:.1f}s")
        _log("=" * 60)
        return out
    except Exception as gen_exc:
        if pw_slot:
            try:
                _BROWSER_POOL.release(pw_slot.slot_id, keep_alive=False)
                _log("playwright: released browser slot after failure/download error")
            except Exception as rel_exc:
                _log(f"playwright: release browser slot after failure failed: {rel_exc}", level="WARN")
            pw_slot = None
        try:
            _update_task_runtime(str(context.get("task_id") or ""), status="failed")
            _TASK_MONITOR.update(str(context.get("task_id") or ""), status="failed", completed_at=time.time(), error_message=str(gen_exc)[:500])
        except Exception:
            pass
        if account_alias and not account_released:
            _TASK_SCHEDULER.release_slot(task_id, success=False, error_msg=str(gen_exc))
            account_released = True
            _log(f"task scheduler released: task={task_id} alias={account_alias} status=failed error={str(gen_exc)[:100]}")
        _log_exc("generate failed")
        raise
    finally:
        global _TASK_TAG
        _TASK_TAG = old_tag
        try:
            _release_task_runtime(str(context.get("task_id") or ""))
        except Exception:
            pass


try:
    from PySide6.QtWidgets import (
        QWidget, QVBoxLayout, QHBoxLayout, QFormLayout,
        QLabel, QTextEdit, QPlainTextEdit, QLineEdit, QPushButton, QCheckBox,
        QGroupBox, QScrollArea, QComboBox, QSizePolicy, QMessageBox,
        QListWidget, QListWidgetItem, QFrame,
    )
    from PySide6.QtCore import Qt
    from PySide6.QtGui import QFont
except Exception:
    QWidget = object
    QVBoxLayout = object
    QHBoxLayout = object
    QFormLayout = object
    QLabel = object
    QTextEdit = object
    QPlainTextEdit = object
    QLineEdit = object
    QPushButton = object
    QCheckBox = object
    QGroupBox = object
    QScrollArea = object
    QComboBox = object
    QSizePolicy = object
    QMessageBox = object
    QListWidget = object
    QListWidgetItem = object
    QFrame = object
    Qt = object
    QFont = object


class _UI:
    def __init__(self) -> None:
        self.widgets: dict[str, Any] = {}

    def _update_param(self, key: str, value: Any) -> None:
        _GLOBAL_PARAMS[key] = value
        try:
            update_plugin_param(_PLUGIN_FILE, key, value)
        except Exception:
            pass

    def _font(self, size: int = 9, bold: bool = False) -> Any:
        try:
            f = QFont("Microsoft YaHei", int(size))
            if bold:
                f.setBold(True)
            return f
        except Exception:
            return None

    def create_ui(self, parent_widget) -> Any:
        try:
            root = QWidget()
            root.setObjectName("runwayml_root")
            scroll = QScrollArea()
            scroll.setObjectName("runwayml_scroll")
            scroll.setWidgetResizable(True)
            content = QWidget()
            content.setObjectName("runwayml_content")
            layout = QVBoxLayout(content)
            layout.setSpacing(6)

            title = QLabel("RunwayML.COM 批量插件")
            title.setFont(self._font(11, bold=True))
            layout.addWidget(title)

            auth_group = QGroupBox("授权信息")
            auth_group.setStyleSheet("QGroupBox::title { color: #ff9800; }")
            auth_layout = QFormLayout()
            auth_group.setLayout(auth_layout)

            try:
                from runway_sec import get_license as _get_lic
                _lic = _get_lic()
                _machine_code = _lic.get_machine_code()
            except Exception as exc:
                _lic = None
                _machine_code = f"加载失败: {exc}"

            mc_label = QLabel(str(_machine_code))
            mc_label.setTextInteractionFlags(Qt.TextSelectableByMouse)
            mc_label.setStyleSheet("color: #4fc3f7; font-family: Consolas, monospace; font-size: 9pt;")
            auth_layout.addRow("机器码:", mc_label)
            self.widgets["auth_machine_code"] = mc_label

            lic_key_input = QLineEdit()
            lic_key_input.setPlaceholderText("RWPG1.xxxxx.xxxxx")
            lic_key_input.setStyleSheet("font-family: Consolas, monospace; font-size: 9pt;")
            auth_layout.addRow("激活码:", lic_key_input)
            self.widgets["auth_license_key"] = lic_key_input

            lic_status_label = QLabel()
            lic_status_label.setStyleSheet("font-size: 9pt; font-weight: bold;")
            auth_layout.addRow("状态:", lic_status_label)
            self.widgets["auth_status"] = lic_status_label

            lic_expiry_label = QLabel()
            lic_expiry_label.setStyleSheet("color: #aaa; font-size: 8pt;")
            auth_layout.addRow("", lic_expiry_label)
            self.widgets["auth_expiry"] = lic_expiry_label

            def _refresh_auth_ui():
                try:
                    from runway_sec import get_license
                    _l = get_license()
                    s = _l.check_status()
                    lic_status_label.setText(s.get("status_text", "未知"))
                    lic_expiry_label.setText(s.get("expiry_text", ""))
                    if s.get("is_valid"):
                        lic_status_label.setStyleSheet("color: #4caf50; font-size: 9pt; font-weight: bold;")
                    elif s.get("status") == "unlicensed":
                        lic_status_label.setStyleSheet("color: #ff9800; font-size: 9pt; font-weight: bold;")
                    else:
                        lic_status_label.setStyleSheet("color: #f44336; font-size: 9pt; font-weight: bold;")
                    if not s.get("is_valid") and s.get("error"):
                        lic_expiry_label.setText(f"⚠ {s['error']}")
                        lic_expiry_label.setStyleSheet("color: #f44336; font-size: 8pt;")
                except Exception as exc:
                    lic_status_label.setText("异常")
                    lic_status_label.setStyleSheet("color: #f44336; font-size: 9pt; font-weight: bold;")
                    lic_expiry_label.setText(str(exc))

            auth_btn_row = QHBoxLayout()
            activate_btn = QPushButton("✅ 激活")
            activate_btn.setStyleSheet("""
                QPushButton {
                    background: #4caf50; color: #fff; font-weight: bold;
                    padding: 5px 16px; border-radius: 4px;
                }
                QPushButton:hover { background: #43a047; }
            """)
            def _on_activate():
                key_text = str(lic_key_input.text() or "").strip()
                if not key_text:
                    from PySide6.QtWidgets import QMessageBox
                    dlg = QMessageBox(QMessageBox.Icon.Warning, "提示", "请先输入激活码。")
                    dlg.setWindowFlags(dlg.windowFlags() | Qt.WindowType.WindowStaysOnTopHint)
                    dlg.exec()
                    return
                try:
                    from runway_sec import get_license
                    r = get_license().activate(key_text)
                    lic_key_input.clear()
                    _refresh_auth_ui()
                    msg = r.get("message", "")
                    err = r.get("error", "")
                    from PySide6.QtWidgets import QMessageBox
                    if r.get("has_error"):
                        dlg = QMessageBox(QMessageBox.Icon.Critical, "激活失败", f"{msg}\n\n{err}")
                        dlg.setWindowFlags(dlg.windowFlags() | Qt.WindowType.WindowStaysOnTopHint)
                        dlg.exec()
                    else:
                        dlg = QMessageBox(QMessageBox.Icon.Information, "激活成功", msg)
                        dlg.setWindowFlags(dlg.windowFlags() | Qt.WindowType.WindowStaysOnTopHint)
                        dlg.exec()
                except Exception as exc:
                    from PySide6.QtWidgets import QMessageBox
                    dlg = QMessageBox(QMessageBox.Icon.Critical, "激活失败", str(exc))
                    dlg.setWindowFlags(dlg.windowFlags() | Qt.WindowType.WindowStaysOnTopHint)
                    dlg.exec()
            activate_btn.clicked.connect(_on_activate)
            auth_btn_row.addWidget(activate_btn)

            deactivate_btn = QPushButton("🗑 卸载")
            deactivate_btn.setStyleSheet("""
                QPushButton {
                    background: #757575; color: #fff;
                    padding: 5px 12px; border-radius: 4px;
                }
                QPushButton:hover { background: #616161; }
            """)
            def _on_deactivate():
                from PySide6.QtWidgets import QMessageBox
                dlg = QMessageBox(QMessageBox.Icon.Question, "确认卸载", "确定要卸载当前授权吗？",
                    QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No)
                dlg.setWindowFlags(dlg.windowFlags() | Qt.WindowType.WindowStaysOnTopHint)
                reply = dlg.exec()
                if reply == QMessageBox.StandardButton.Yes:
                    try:
                        from runway_sec import get_license
                        get_license().deactivate()
                        _refresh_auth_ui()
                        dlg2 = QMessageBox(QMessageBox.Icon.Information, "已卸载", "授权已卸载。")
                        dlg2.setWindowFlags(dlg2.windowFlags() | Qt.WindowType.WindowStaysOnTopHint)
                        dlg2.exec()
                    except Exception as exc:
                        dlg3 = QMessageBox(QMessageBox.Icon.Critical, "卸载失败", str(exc))
                        dlg3.setWindowFlags(dlg3.windowFlags() | Qt.WindowType.WindowStaysOnTopHint)
                        dlg3.exec()
            deactivate_btn.clicked.connect(_on_deactivate)
            auth_btn_row.addWidget(deactivate_btn)

            auth_btn_row.addStretch()
            auth_layout.addRow("", auth_btn_row)

            _refresh_auth_ui()

            layout.addWidget(auth_group)

            self._update_param("mode", "playwright")

            acct_group = QGroupBox("账号管理")
            acct_group.setStyleSheet("QGroupBox::title { color: #4caf50; }")
            acct_outer = QVBoxLayout()
            acct_group.setLayout(acct_outer)

            timeout_group = QGroupBox("超时与调试")
            timeout_group.setStyleSheet("QGroupBox::title { color: #4caf50; }")
            timeout_layout = QFormLayout()
            timeout_group.setLayout(timeout_layout)

            timeout_combo = QComboBox()
            timeout_combo.setEditable(True)
            timeout_combo.addItems(["300", "600", "900", "1200", "1800", "2400", "3600", "6000", "7200", "18000"])
            timeout_combo.setCurrentText(str(_GLOBAL_PARAMS.get("timeout") or "6000"))
            timeout_combo.currentTextChanged.connect(lambda v: self._update_param("timeout", int(v) if v.isdigit() else 6000))
            timeout_layout.addRow("超时(秒):", timeout_combo)
            self.widgets["timeout"] = timeout_combo
            timeout_hint = QLabel("💡 单个视频从提交到生成完成的等待上限，复杂模型建议设大（如2700秒=45分钟）")
            timeout_hint.setStyleSheet("color: #aaaaaa; font-size: 8pt;")
            timeout_layout.addRow("", timeout_hint)

            screenshot_cb = QCheckBox("失败时保存截图")
            screenshot_cb.setChecked(bool(_GLOBAL_PARAMS.get("debug_save_screenshot", True)))
            screenshot_cb.toggled.connect(lambda v: self._update_param("debug_save_screenshot", v))
            timeout_layout.addRow("", screenshot_cb)

            pw_group = QGroupBox("Playwright 设置")
            pw_group.setStyleSheet("QGroupBox::title { color: #4caf50; }")
            pw_layout = QFormLayout()
            pw_group.setLayout(pw_layout)

            keep_browser_cb = QCheckBox("保持浏览器复用（开发中，暂不生效）")
            keep_browser_cb.setChecked(False)
            keep_browser_cb.setEnabled(False)
            keep_browser_cb.setToolTip("该功能暂未实装：当前每个任务始终使用独立浏览器实例，保证任务数据完全隔离，不会互相干扰")
            keep_browser_cb.setStyleSheet("color: #666666;")
            pw_layout.addRow("", keep_browser_cb)
            self.widgets["playwright_keep_browser"] = keep_browser_cb

            keep_browser_hint = QLabel("⚙️ 每任务独立浏览器（当前固定行为），复用功能完善后再开放")
            keep_browser_hint.setStyleSheet("color: #666666; font-size: 8pt;")
            pw_layout.addRow("", keep_browser_hint)

            headless_cb = QCheckBox("无头模式（后台隐藏运行）")
            headless_cb.setChecked(bool(_GLOBAL_PARAMS.get("playwright_headless", False)))
            headless_cb.toggled.connect(lambda v: self._update_param("playwright_headless", v))
            pw_layout.addRow("", headless_cb)
            self.widgets["playwright_headless"] = headless_cb

            _polling_method_map = {"page": "页面轮询"}
            _polling_method_reverse = {"页面轮询": "page"}
            polling_combo = QComboBox()
            polling_combo.addItems(list(_polling_method_map.values()))
            cur_polling = str(_GLOBAL_PARAMS.get("polling_method") or "page")
            polling_combo.setCurrentText(_polling_method_map.get(cur_polling, "页面轮询"))
            polling_combo.currentTextChanged.connect(lambda v: self._update_param("polling_method", _polling_method_reverse.get(v, "page")))
            pw_layout.addRow("轮询方式:", polling_combo)
            self.widgets["polling_method"] = polling_combo

            polling_hint = QLabel("页面轮询=浏览器保持打开监控，直到视频下载完成后再关闭")
            polling_hint.setStyleSheet("color: #aaaaaa; font-size: 8pt;")
            pw_layout.addRow("", polling_hint)

            concurrent_input = QLineEdit()
            concurrent_input.setText(str(_GLOBAL_PARAMS.get("max_concurrent_tasks") or "0"))
            concurrent_input.setPlaceholderText("0 = 自动（账号数 × 2）")
            concurrent_input.textChanged.connect(lambda v: self._update_param("max_concurrent_tasks", int(v) if v.isdigit() else 0))
            pw_layout.addRow("最大并发数:", concurrent_input)
            self.widgets["max_concurrent_tasks"] = concurrent_input

            concurrent_hint = QLabel("0=自动计算（每个账号2并发），如2账号=4并发")
            concurrent_hint.setStyleSheet("color: #aaaaaa; font-size: 8pt;")
            pw_layout.addRow("", concurrent_hint)

            wait_timeout_input = QLineEdit()
            wait_timeout_input.setText(str(_GLOBAL_PARAMS.get("concurrent_wait_timeout") or "999999"))
            wait_timeout_input.setPlaceholderText("并发满时排队等待超时（秒）")
            wait_timeout_input.textChanged.connect(lambda v: self._update_param("concurrent_wait_timeout", int(v) if v.isdigit() else 999999))
            pw_layout.addRow("排队超时(秒):", wait_timeout_input)
            self.widgets["concurrent_wait_timeout"] = wait_timeout_input

            pool_file_frame = QFrame()
            pool_file_frame.setStyleSheet("QFrame { background: #2a2a3a; border-radius: 6px; padding: 8px; }")
            pool_file_layout = QVBoxLayout(pool_file_frame)
            pool_file_layout.setContentsMargins(10, 10, 10, 10)
            pool_file_layout.setSpacing(6)

            pool_input = QLineEdit()
            pool_input.setText(str(_GLOBAL_PARAMS.get("account_pool_path") or ""))
            pool_input.setPlaceholderText("选择或输入账号池文件路径...")
            pool_input.setStyleSheet("QLineEdit { padding: 6px 8px; border: 1px solid #555; border-radius: 4px; background: #1e1e2e; color: #eee; } QLineEdit:focus { border-color: #4fc3f7; }")
            self.widgets["account_pool_path"] = pool_input
            pool_input.textChanged.connect(lambda v: self._update_param("account_pool_path", v))

            pool_browse_btn = QPushButton("📂 选择文件")
            pool_browse_btn.setStyleSheet("""
                QPushButton {
                    background: #5c6bc0; color: #fff; font-weight: bold;
                    padding: 6px 16px; border-radius: 4px;
                }
                QPushButton:hover { background: #7986cb; }
                QPushButton:pressed { background: #3f51b5; }
            """)
            def _on_browse_pool_file():
                from PySide6.QtWidgets import QFileDialog
                default_path = str(_GLOBAL_PARAMS.get("account_pool_path") or account_pool_file or "")
                if not default_path or not os.path.isfile(default_path):
                    default_path = str(DATA_DIR) if DATA_DIR.exists() else ""
                file_path, _ = QFileDialog.getOpenFileName(
                    None, "选择账号池文件", default_path,
                    "文本文件 (*.txt);;所有文件 (*.*)"
                )
                if file_path:
                    pool_input.setText(file_path)
                    self._update_param("account_pool_path", file_path)
                    _update_pool_path_hint()
                    handle_action("reload_accounts")
                    _refresh_acct_list()
            pool_browse_btn.clicked.connect(_on_browse_pool_file)

            pool_file_row = QHBoxLayout()
            pool_file_row.addWidget(pool_input)
            pool_file_row.addWidget(pool_browse_btn)
            pool_file_layout.addLayout(pool_file_row)

            pool_format_hint = QLabel("格式: 邮箱----密码 （每行一个，支持 # 注释）")
            pool_format_hint.setStyleSheet("color: #666; font-size: 8pt;")
            pool_file_layout.addWidget(pool_format_hint)

            acct_outer.addWidget(pool_file_frame)

            pool_path_hint = QLabel()
            pool_path_hint.setStyleSheet("color: #888; font-size: 8pt;")
            pool_path_hint.setWordWrap(True)
            def _update_pool_path_hint():
                current_path = str(_GLOBAL_PARAMS.get("account_pool_path") or "").strip()
                if current_path and os.path.isfile(current_path):
                    try:
                        with open(current_path, "r", encoding="utf-8") as f:
                            lines = [l.strip() for l in f.readlines() if l.strip() and not l.startswith("#")]
                        pool_path_hint.setText(f"📄 账号池文件: {os.path.basename(current_path)} ({len(lines)} 个账号)")
                    except Exception:
                        pool_path_hint.setText(f"📄 账号池文件: {current_path}")
                elif current_path:
                    pool_path_hint.setText(f"⚠️ 账号池文件不存在: {current_path}")
                else:
                    pool_path_hint.setText("💡 提示: 设置「账号池文件」路径可批量导入账号（格式: 邮箱----密码）")
            _update_pool_path_hint()
            acct_outer.addWidget(pool_path_hint)

            btn_row = QHBoxLayout()
            refresh_acct_btn = QPushButton("🔄 刷新账号")
            refresh_acct_btn.setStyleSheet("""
                QPushButton {
                    background: #43a047; color: #fff; font-weight: bold;
                    padding: 6px 12px; border-radius: 4px;
                }
                QPushButton:hover { background: #388e3c; }
                QPushButton:pressed { background: #2e7d32; }
            """)
            refresh_acct_btn.clicked.connect(lambda: handle_action("reload_accounts"))
            btn_row.addWidget(refresh_acct_btn)
            btn_row.addStretch()
            acct_outer.addLayout(btn_row)

            handle_action("reload_accounts")

            layout.addWidget(acct_group)

            gen_group = QGroupBox("生成参数")
            gen_group.setStyleSheet("QGroupBox::title { color: #4caf50; }")
            gen_layout = QFormLayout()
            gen_group.setLayout(gen_layout)

            model_combo = QComboBox()
            model_combo.addItems(["seedance_2.0"])
            model_combo.setCurrentText(str(_GLOBAL_PARAMS.get("model") or "seedance_2.0"))
            model_combo.currentTextChanged.connect(lambda v: self._update_param("model", v))
            gen_layout.addRow("模型:", model_combo)
            self.widgets["model"] = model_combo

            _gen_mode_map = {"multi_reference": "全能参考", "keyframe": "首尾帧"}
            _gen_mode_reverse = {"全能参考": "multi_reference", "首尾帧": "keyframe"}
            type_combo = QComboBox()
            type_combo.addItems(list(_gen_mode_map.values()))
            cur_mode = str(_GLOBAL_PARAMS.get("generation_mode") or "multi_reference")
            type_combo.setCurrentText(_gen_mode_map.get(cur_mode, "全能参考"))
            type_combo.currentTextChanged.connect(lambda v: self._update_param("generation_mode", _gen_mode_reverse.get(v, "multi_reference")))
            gen_layout.addRow("生成类型:", type_combo)
            self.widgets["generation_mode"] = type_combo

            ratio_combo = QComboBox()
            ratio_combo.setEditable(True)
            ratio_combo.addItems(["16:9", "9:16", "21:9", "1:1", "3:4", "4:3"])
            ratio_combo.setCurrentText(str(_GLOBAL_PARAMS.get("aspect_ratio") or "16:9"))
            ratio_combo.currentTextChanged.connect(lambda v: self._update_param("aspect_ratio", v))
            gen_layout.addRow("画幅比例:", ratio_combo)
            self.widgets["aspect_ratio"] = ratio_combo

            duration_combo = QComboBox()
            duration_combo.addItems([str(i) for i in range(4, 16)])
            duration_combo.setCurrentText(str(_GLOBAL_PARAMS.get("duration") or "8"))
            duration_combo.currentTextChanged.connect(lambda v: self._update_param("duration", int(v) if v.isdigit() else 8))
            gen_layout.addRow("时长(秒):", duration_combo)
            self.widgets["duration"] = duration_combo

            use_end_frame_cb = QCheckBox("使用尾帧")
            use_end_frame_cb.setChecked(bool(_GLOBAL_PARAMS.get("use_end_frame", True)))
            use_end_frame_cb.toggled.connect(lambda v: self._update_param("use_end_frame", v))
            gen_layout.addRow("", use_end_frame_cb)
            self.widgets["use_end_frame"] = use_end_frame_cb

            layout.addWidget(gen_group)

            layout.addWidget(timeout_group)
            layout.addWidget(pw_group)

            hint = QLabel(
                "使用说明:\n"
                "1. 设置「账号池文件」路径，格式: 邮箱----密码（每行一个）\n"
                "2. 账号从文本文件自动加载，勾选可停用/启用\n"
                "3. 多账号自动轮询，每个账号2个并发，突破单账号限制\n"
                "4. 账号并发满时自动排队等待，任务完成后自动下载视频"
            )
            hint.setStyleSheet("color: #888888; font-size: 8pt;")
            hint.setWordWrap(True)
            layout.addWidget(hint)

            layout.addStretch()
            scroll.setWidget(content)

            outer_layout = QVBoxLayout(root)
            outer_layout.setContentsMargins(0, 0, 0, 0)
            outer_layout.addWidget(scroll)

            return root
        except Exception as exc:
            _log(f"create_ui failed: {exc}", level="ERROR")
            return None

    def load_params(self, params: dict[str, Any]) -> None:
        for key, value in params.items():
            _GLOBAL_PARAMS[key] = value
            widget = self.widgets.get(key)
            if widget is None:
                continue
            try:
                if isinstance(widget, QLineEdit):
                    widget.setText(str(value or ""))
                elif isinstance(widget, QComboBox):
                    widget.setCurrentText(str(value or ""))
                elif isinstance(widget, QCheckBox):
                    widget.setChecked(bool(value))
            except Exception:
                pass


_UI_INSTANCE = _UI()


def get_info():
    return {
        "name": "小鸭快跑RunwayML视频插件",
        "version": "1.0.0",
        "author": "ZZDH",
        "description": "",
    }


def create_ui(parent_widget):
    return _UI_INSTANCE.create_ui(parent_widget)


def get_params():
    params = _DEFAULT_PARAMS.copy()
    try:
        params.update(load_plugin_config(_PLUGIN_FILE) or {})
    except Exception:
        pass
    return params


def load_params(params: dict[str, Any]) -> None:
    _UI_INSTANCE.load_params(params)
def _diagnose_and_repair_runtime() -> dict[str, Any]:
    fixed: dict[str, Any] = {
        "removed_dead_browsers": 0,
        "released_stale_running": 0,
        "fixed_active_accounts": 0,
        "cleared_interactive": 0,
        "cleared_setup_locks": 0,
        "long_running_alive": 0,
        "synced_max_concurrent": 0,
    }
    notes: list[str] = []

    try:
        _ACCOUNT_MGR.sync_disabled_state()
    except Exception as exc:
        notes.append(f"disabled sync warning: {exc}")

    alive_task_ids: set[str] = set()
    alive_busy_by_alias: dict[str, int] = {}
    unknown_busy_by_alias: dict[str, int] = {}

    with _BROWSER_POOL._lock:
        dead_slot_ids: list[str] = []
        for slot_id, slot in list(_BROWSER_POOL._slots.items()):
            page_closed = False
            try:
                page_closed = bool(slot.page and slot.page.is_closed())
            except Exception:
                page_closed = True
            alive = bool(slot.is_alive and not page_closed)
            if not alive:
                dead_slot_ids.append(slot_id)
                continue
            if slot.is_busy:
                alive_busy_by_alias[slot.account_alias] = alive_busy_by_alias.get(slot.account_alias, 0) + 1
                if slot.task_id:
                    alive_task_ids.add(slot.task_id)
                else:
                    unknown_busy_by_alias[slot.account_alias] = unknown_busy_by_alias.get(slot.account_alias, 0) + 1

        now = time.time()
        for alias in list(_BROWSER_POOL._active_accounts):
            lock_age = now - float(_BROWSER_POOL._active_account_started.get(alias) or now)
            if alive_busy_by_alias.get(alias, 0) <= 0 and lock_age > 120:
                _BROWSER_POOL._active_accounts.discard(alias)
                _BROWSER_POOL._active_account_started.pop(alias, None)
                fixed["cleared_setup_locks"] += 1
        _BROWSER_POOL._active_accounts_cond.notify_all()

    for slot_id in dead_slot_ids:
        try:
            _BROWSER_POOL._destroy_slot(slot_id)
            fixed["removed_dead_browsers"] += 1
        except Exception as exc:
            notes.append(f"destroy dead browser {slot_id} warning: {exc}")

    with _TASK_SCHEDULER._cond:
        release_ids: list[str] = []
        unknown_budget = dict(unknown_busy_by_alias)
        now = time.time()
        for tid, st in list(_TASK_SCHEDULER._running.items()):
            if tid in alive_task_ids:
                if st.started_at and now - st.started_at >= 3600:
                    fixed["long_running_alive"] += 1
                continue
            alias = st.account_alias
            if unknown_budget.get(alias, 0) > 0:
                unknown_budget[alias] -= 1
                if st.started_at and now - st.started_at >= 3600:
                    fixed["long_running_alive"] += 1
                continue
            release_ids.append(tid)

        _TASK_SCHEDULER._cond.notify_all()

    for tid in release_ids:
        try:
            _TASK_SCHEDULER.release_slot(
                tid,
                success=False,
                error_msg="diagnose repair: running task has no live browser",
            )
            fixed["released_stale_running"] += 1
        except Exception as exc:
            notes.append(f"release stale task {tid} warning: {exc}")

    with _TASK_SCHEDULER._cond:
        for i, t in enumerate(_TASK_SCHEDULER._queue):
            t.queue_position = i + 1
        running_ids = set(_TASK_SCHEDULER._running.keys())
        running_by_alias: dict[str, int] = {}
        for st in _TASK_SCHEDULER._running.values():
            if st.account_alias:
                running_by_alias[st.account_alias] = running_by_alias.get(st.account_alias, 0) + 1
        _TASK_SCHEDULER._cond.notify_all()

    with _ACCOUNT_MGR._lock:
        for alias, slot in _ACCOUNT_MGR._slots.items():
            expected_active = running_by_alias.get(alias, 0)
            if slot.active_tasks != expected_active:
                _log(f"diagnose: fixing active_tasks for {alias}: {slot.active_tasks} -> {expected_active}", level="WARN")
                slot.active_tasks = expected_active
                fixed["fixed_active_accounts"] += 1
            if slot.interactive_task_id and slot.interactive_task_id not in running_ids:
                _log(f"diagnose: clearing stale interactive_task_id for {alias}: {slot.interactive_task_id}", level="WARN")
                slot.interactive_task_id = None
                fixed["cleared_interactive"] += 1
            elif slot.active_tasks == 0 and slot.interactive_task_id:
                slot.interactive_task_id = None
                fixed["cleared_interactive"] += 1

        enabled_count = sum(1 for s in _ACCOUNT_MGR._slots.values() if not s.disabled)
        custom_capacity = _safe_int(_GLOBAL_PARAMS.get("max_concurrent_tasks"), 0)
        target_capacity = custom_capacity if custom_capacity > 0 else max(enabled_count * _MAX_CONCURRENT_PER_ACCOUNT, 1)

    old_capacity = _TASK_SCHEDULER.max_concurrent
    _TASK_SCHEDULER.set_max_concurrent(target_capacity)
    if old_capacity != target_capacity:
        fixed["synced_max_concurrent"] = target_capacity

    with _TASK_SCHEDULER._cond:
        _TASK_SCHEDULER._cond.notify_all()
    with _BROWSER_POOL._lock:
        _BROWSER_POOL._active_accounts_cond.notify_all()

    return {"fixed": fixed, "notes": notes}


def _run_manual_login(alias: str) -> None:
    _log(f"manual_login: starting manual login thread for account={alias}")
    try:
        email = ""
        password = ""
        acc_slot = _ACCOUNT_MGR.get_slot(alias)
        if acc_slot and acc_slot.email and acc_slot.password_enc:
            email = acc_slot.email
            password = acc_slot.password_enc
        else:
            cred = _CREDENTIAL_VAULT.get_credential(alias)
            if cred:
                email = cred.get("email", "")
                password = cred.get("password", "")

        from playwright.sync_api import sync_playwright
        pw = sync_playwright().start()
        
        params = get_params()
        ch = params.get("playwright_browser") or "chromium"
        if ch not in ["chrome", "msedge"]:
            ch = None
            
        _log(f"manual_login: launching headful maximized browser with channel={ch}")
        browser = None
        for channel in [ch, "chrome", "msedge", None]:
            try:
                launch_opts = {
                    "headless": False,
                    "args": ["--start-maximized"]
                }
                if channel:
                    launch_opts["channel"] = channel
                browser = pw.chromium.launch(**launch_opts)
                break
            except Exception as e:
                _log(f"manual_login: failed to launch with channel={channel}: {e}", level="WARN")
                
        if not browser:
            raise Exception("failed to launch headful browser")
            
        ctx_opts = {"no_viewport": True}
        state_path = ""
        if DATA_DIR.exists():
            state_dir = DATA_DIR / "storage_states"
            state_dir.mkdir(parents=True, exist_ok=True)
            state_path = str(state_dir / f"{alias}_state.json")
            if os.path.isfile(state_path):
                ctx_opts["storage_state"] = state_path
                _log(f"manual_login: loaded existing state from {state_path}")
                
        ctx = browser.new_context(**ctx_opts)
        page = ctx.new_page()
        
        _log("manual_login: navigating to RunwayML base URL")
        page.goto("https://app.runwayml.com/", timeout=120000)
        
        _log("manual_login: window is open. Auto-saving storage state periodically.")
        
        while not page.is_closed():
            try:
                page.wait_for_timeout(15000)
                if not page.is_closed() and state_path:
                    ctx.storage_state(path=state_path)
            except Exception:
                if page.is_closed():
                    break
                    
        if state_path:
            try:
                ctx.storage_state(path=state_path)
                _log(f"manual_login: final state saved to {state_path}")
            except Exception as e:
                _log(f"manual_login: final save state failed: {e}", level="ERROR")
                
        try:
            ctx.close()
            browser.close()
            pw.stop()
        except Exception:
            pass
        _log(f"manual_login: session finished for {alias}")
    except Exception as exc:
        _log(f"manual_login: thread error: {exc}", level="ERROR")


def _fetch_update_manifest() -> dict[str, Any]:
    resp = requests.get(_UPDATE_VERSION_URL, timeout=30)
    resp.raise_for_status()
    data = resp.json()
    if not isinstance(data, dict):
        raise ValueError("version.json 格式错误")
    return data


def _check_plugin_update() -> dict[str, Any]:
    manifest = _fetch_update_manifest()
    remote_version = str(manifest.get("version") or "").strip()
    zip_url = str(manifest.get("zip_url") or manifest.get("archive_url") or _UPDATE_ARCHIVE_URL).strip()
    notes = str(manifest.get("notes") or manifest.get("message") or "").strip()
    if not remote_version:
        raise ValueError("version.json 缺少 version")
    if not zip_url:
        raise ValueError("version.json 缺少 zip_url")
    return {
        "ok": True,
        "current_version": _PLUGIN_VERSION,
        "remote_version": remote_version,
        "has_update": remote_version != _PLUGIN_VERSION,
        "zip_url": zip_url,
        "notes": notes,
        "repo": _UPDATE_REPO,
    }


def _safe_extract_update_zip(zip_path: Path, dest_dir: Path) -> Path:
    with zipfile.ZipFile(str(zip_path), "r") as zf:
        for member in zf.infolist():
            name = member.filename.replace("\\", "/")
            if name.startswith("/") or ".." in Path(name).parts:
                raise ValueError(f"更新包包含非法路径: {member.filename}")
        zf.extractall(str(dest_dir))

    candidates: list[Path] = []
    if (dest_dir / "main.py").is_file() and (dest_dir / "ui").is_dir():
        candidates.append(dest_dir)
    for child in dest_dir.iterdir():
        if child.is_dir() and (child / "main.py").is_file() and (child / "ui").is_dir():
            candidates.append(child)
    if not candidates:
        raise ValueError("更新包内未找到 main.py 和 ui 文件夹")
    return candidates[0]


def _install_plugin_update(zip_url: str = "") -> dict[str, Any]:
    zip_url = str(zip_url or "").strip() or _UPDATE_ARCHIVE_URL
    plugin_root = Path(_PLUGIN_FILE).resolve().parent
    current_main = plugin_root / "main.py"
    current_ui = plugin_root / "ui"
    if not current_main.is_file():
        raise FileNotFoundError(f"当前 main.py 不存在: {current_main}")
    if not current_ui.is_dir():
        raise FileNotFoundError(f"当前 ui 文件夹不存在: {current_ui}")

    backup_root = plugin_dir / "update_backups" / datetime.now().strftime("%Y%m%d_%H%M%S")
    backup_root.mkdir(parents=True, exist_ok=True)
    tmp_parent = Path(tempfile.mkdtemp(prefix="runway_update_"))
    try:
        zip_path = tmp_parent / "update.zip"
        with requests.get(zip_url, stream=True, timeout=120) as resp:
            resp.raise_for_status()
            with open(zip_path, "wb") as fh:
                for chunk in resp.iter_content(chunk_size=1024 * 512):
                    if chunk:
                        fh.write(chunk)

        extract_dir = tmp_parent / "extract"
        extract_dir.mkdir(parents=True, exist_ok=True)
        package_root = _safe_extract_update_zip(zip_path, extract_dir)
        new_main = package_root / "main.py"
        new_ui = package_root / "ui"
        if not new_main.is_file() or not new_ui.is_dir():
            raise ValueError("更新包校验失败: 缺少 main.py 或 ui/")

        shutil.copy2(str(current_main), str(backup_root / "main.py"))
        shutil.copytree(str(current_ui), str(backup_root / "ui"))

        shutil.copy2(str(new_main), str(current_main))
        if current_ui.exists():
            shutil.rmtree(str(current_ui))
        shutil.copytree(str(new_ui), str(current_ui))

        _log(f"plugin updater: installed update from {zip_url}, backup={backup_root}")
        return {
            "ok": True,
            "message": "更新完成，请重启字字动画后生效",
            "backup_dir": str(backup_root),
            "updated": ["main.py", "ui/"],
        }
    except Exception:
        _log_exc("plugin updater failed")
        raise
    finally:
        try:
            shutil.rmtree(str(tmp_parent), ignore_errors=True)
        except Exception:
            pass


def handle_action(action, data=None):
    if action == "manual_login":
        try:
            d = data or {}
            alias = str(d.get("alias") or "").strip()
            if not alias:
                return {"ok": False, "error": "alias 不能为空"}
            t = threading.Thread(target=_run_manual_login, args=(alias,), name=f"manual-login-{alias}", daemon=True)
            t.start()
            return {"ok": True, "message": f"正在后台启动 {alias} 浏览器窗口进行登录..."}
        except Exception as e:
            return {"ok": False, "error": str(e)}

    elif action == "test_api_key":
        try:
            api_key = str(data or _GLOBAL_PARAMS.get("api_key") or "").strip()
            if not api_key:
                return {"ok": False, "error": "API Key 为空"}
            client = RunwayMLClient(api_key, str(_GLOBAL_PARAMS.get("api_base") or RUNWAYML_API_BASE))
            resp = client._request("GET", "/organization")
            if resp.status_code == 200:
                org_info = resp.json()
                return {"ok": True, "message": f"连接成功: {org_info.get('name', 'Unknown')}"}
            else:
                return {"ok": False, "error": f"API 返回错误: {resp.status_code}"}
        except Exception as e:
            return {"ok": False, "error": str(e)}

    elif action == "account_status":
        return {"ok": True, "accounts": _ACCOUNT_MGR.status_summary()}

    elif action == "task_stats":
        return {"ok": True, "stats": _TASK_MONITOR.stats()}

    elif action == "browser_stats":
        return {"ok": True, "stats": _BROWSER_POOL.stats()}

    elif action == "store_credential":
        try:
            d = data or {}
            _apply_action_pool_path(d)
            email = str(d.get("email") or "").strip()
            password = str(d.get("password") or "").strip()
            if not email or not password:
                return {"ok": False, "error": "email/password 不能为空"}
            ok, msg = _add_account_to_pool_file(email, password)
            if ok:
                alias = email.split("@")[0] if "@" in email else email
                _DISABLED_ACCOUNTS.discard(alias)
                _save_disabled_accounts()
                total, reloaded, reload_msg = _safe_reload_accounts("store_credential")
                message = msg if reloaded else f"{msg}\n{reload_msg}"
                return {"ok": True, "message": message, "path": _get_current_pool_path(), "total": total, "reloaded": reloaded}
            return {"ok": False, "error": msg}
        except Exception as e:
            return {"ok": False, "error": str(e)}

    elif action == "list_credentials":
        accounts = _read_all_accounts_from_file()
        aliases = [a.get("alias") or a.get("email", "").split("@")[0] for a in accounts if a.get("email")]
        return {"ok": True, "aliases": aliases}

    elif action == "delete_credential":
        try:
            d = data if isinstance(data, dict) else {}
            _apply_action_pool_path(d)
            raw_alias = d.get("alias") if isinstance(data, dict) else data
            alias = str(raw_alias or "").strip()
            if not alias:
                return {"ok": False, "error": "alias 不能为空"}
            ok, msg = _remove_account_from_pool_file(alias)
            if not ok:
                return {"ok": False, "error": msg}
            active_work = _has_active_browser_or_scheduler_work()
            _DISABLED_ACCOUNTS.add(alias)
            _save_disabled_accounts()
            if active_work:
                with _ACCOUNT_MGR._lock:
                    slot = _ACCOUNT_MGR._slots.get(alias)
                    if slot:
                        slot.disabled = True
                _log(f"delete_credential deferred in-memory removal because active work exists: alias={alias}", level="WARN")
            else:
                try:
                    _CREDENTIAL_VAULT.delete_credential(alias)
                except Exception:
                    pass
                with _ACCOUNT_MGR._lock:
                    _ACCOUNT_MGR._slots.pop(alias, None)
                    for k in list(_ACCOUNT_MGR._key_to_alias.keys()):
                        if _ACCOUNT_MGR._key_to_alias[k] == alias:
                            del _ACCOUNT_MGR._key_to_alias[k]
                try:
                    storage_dir = str(DATA_DIR / "storage_states") if DATA_DIR.exists() else ""
                    if storage_dir and os.path.isdir(storage_dir):
                        for fname in os.listdir(storage_dir):
                            if fname.startswith(alias) and fname.endswith("_state.json"):
                                fpath = os.path.join(storage_dir, fname)
                                os.remove(fpath)
                                _log(f"deleted storage state file: {fpath}")
                except Exception as clean_exc:
                    _log(f"clean storage state error: {clean_exc}", level="WARN")
            total, reloaded, reload_msg = _safe_reload_accounts("delete_credential")
            message = msg if reloaded else f"{msg}\n{reload_msg}"
            _log(f"deleted account from pool file: alias={alias}")
            return {"ok": True, "message": message, "path": _get_current_pool_path(), "total": total, "reloaded": reloaded}
        except Exception as e:
            _log(f"delete_credential error: {e}", level="ERROR")
            return {"ok": False, "error": str(e)}

    elif action == "toggle_account":
        try:
            d = data or {}
            alias = str(d.get("alias") or "").strip()
            disabled = bool(d.get("disabled", False))
            if not alias:
                return {"ok": False, "error": "alias 不能为空"}
            _ACCOUNT_MGR.set_disabled(alias, disabled)
            return {"ok": True, "message": f"账号 {alias} 已{'停用' if disabled else '启用'}"}
        except Exception as e:
            return {"ok": False, "error": str(e)}

    elif action == "list_account_status":
        try:
            accounts = _read_all_accounts_from_file()
            result = []
            for a in accounts:
                alias = a.get("alias") or (a.get("email", "").split("@")[0] if a.get("email") else "")
                email = a.get("email", "")
                if not alias and email:
                    alias = email.split("@")[0] if "@" in email else email
                if alias:
                    result.append({"alias": alias, "disabled": alias in _DISABLED_ACCOUNTS})
            return {"ok": True, "accounts": result}
        except Exception as e:
            return {"ok": False, "error": str(e)}

    elif action == "scheduler_status":
        try:
            snap = _TASK_SCHEDULER.status_snapshot()
            return {"ok": True, **snap}
        except Exception as e:
            return {"ok": False, "error": str(e)}

    elif action == "diagnose_and_wakeup":
        try:
            repair = _diagnose_and_repair_runtime()
            sched = _TASK_SCHEDULER.status_snapshot()
            browsers = _BROWSER_POOL.stats()
            monitor_stats = _TASK_MONITOR.stats()
            with _TASK_RUNTIME_LOCK:
                runtime_count = len(_TASK_RUNTIME_BY_ID)
            accounts = _ACCOUNT_MGR.status_summary()
            enabled_accounts = [a for a in accounts if not a.get("disabled")]
            active_tasks = sum(int(a.get("active_tasks") or 0) for a in enabled_accounts)
            auto_capacity = len(enabled_accounts) * _MAX_CONCURRENT_PER_ACCOUNT
            custom_capacity = int(_GLOBAL_PARAMS.get("max_concurrent_tasks") or 0)
            capacity = custom_capacity if custom_capacity > 0 else auto_capacity
            with _TASK_SCHEDULER._cond:
                _TASK_SCHEDULER._cond.notify_all()
            with _BROWSER_POOL._lock:
                _BROWSER_POOL._active_accounts_cond.notify_all()
            fixed = repair.get("fixed", {}) if isinstance(repair, dict) else {}
            report = [
                "诊断修复并唤醒完成",
                f"账号: enabled={len(enabled_accounts)} total={len(accounts)} per_account={_MAX_CONCURRENT_PER_ACCOUNT}",
                f"并发: active={active_tasks} capacity={capacity} queued={sched.get('queued', 0)} running={sched.get('running', 0)} max={sched.get('max_concurrent', '?')}",
                (
                    "任务口径: "
                    f"scheduler_submitted={sched.get('total_submitted', 0)} "
                    f"scheduler_done={sched.get('total_completed', 0)} "
                    f"scheduler_failed={sched.get('total_failed', 0)} "
                    f"monitor_total={monitor_stats.get('total', 0)} "
                    f"monitor_active={monitor_stats.get('active', 0)} "
                    f"runtime_active={runtime_count}"
                ),
                f"浏览器: busy={browsers.get('busy', 0)} alive={browsers.get('alive', 0)} total={browsers.get('total_slots', 0)} max={browsers.get('max_browsers', 0)}",
                (
                    "修复: "
                    f"dead_browser={fixed.get('removed_dead_browsers', 0)} "
                    f"stale_running={fixed.get('released_stale_running', 0)} "
                    f"active_fixed={fixed.get('fixed_active_accounts', 0)} "
                    f"interactive_cleared={fixed.get('cleared_interactive', 0)} "
                    f"setup_lock_cleared={fixed.get('cleared_setup_locks', 0)} "
                    f"long_alive={fixed.get('long_running_alive', 0)}"
                ),
            ]
            for note in repair.get("notes", []) if isinstance(repair, dict) else []:
                report.append(f"! {note}")
            for acc in accounts:
                report.append(
                    f"- {acc.get('alias')}: disabled={acc.get('disabled')} active={acc.get('active_tasks')} "
                    f"available={acc.get('available_slots')} browsers={acc.get('browsers_count')} "
                    f"cooldown={int(acc.get('cooldown_remaining') or 0)}s"
                )
            return {
                "ok": True,
                "message": "\n".join(report),
                "scheduler": sched,
                "task_monitor": monitor_stats,
                "runtime_active": runtime_count,
                "browsers": browsers,
                "accounts": accounts,
                "repair": repair,
            }
        except Exception as e:
            return {"ok": False, "error": str(e)}

    elif action == "browse_pool_file":
        try:
            from PySide6.QtWidgets import QFileDialog
            default_path = str(_GLOBAL_PARAMS.get("account_pool_path") or account_pool_file or "")
            if not default_path or not os.path.isfile(default_path):
                default_path = str(DATA_DIR) if DATA_DIR.exists() else ""
            file_path, _ = QFileDialog.getOpenFileName(
                None,
                "选择账号池文件",
                default_path,
                "文本文件 (*.txt);;所有文件 (*.*)",
            )
            if not file_path:
                return {"ok": False, "error": "未选择文件"}
            file_path = _set_current_pool_path(file_path, persist=True)
            total, reloaded, reload_msg = _safe_reload_accounts("browse_pool_file")
            message = f"已选择账号池文件，加载 {total} 个账号" if reloaded else reload_msg
            return {"ok": True, "path": file_path, "message": message, "reloaded": reloaded}
        except Exception as e:
            return {"ok": False, "error": str(e)}

    elif action == "reload_accounts":
        try:
            d = data if isinstance(data, dict) else {}
            _apply_action_pool_path(d)
            total, reloaded, reload_msg = _safe_reload_accounts("reload_accounts")
            return {
                "ok": True,
                "message": f"已重新加载，共 {total} 个账号" if reloaded else reload_msg,
                "path": _get_current_pool_path(),
                "silent": bool(d.get("silent")) if isinstance(d, dict) else False,
                "reloaded": reloaded,
            }
        except Exception as e:
            return {"ok": False, "error": str(e)}

    elif action == "shutdown_browsers":
        try:
            _BROWSER_POOL.shutdown()
            return {"ok": True, "message": "所有浏览器实例已关闭"}
        except Exception as e:
            return {"ok": False, "error": str(e)}

    elif action == "concurrent_capacity":
        total_accounts = len(_ACCOUNT_MGR._slots)
        enabled_accounts = sum(1 for s in _ACCOUNT_MGR._slots.values() if not s.disabled)
        auto_capacity = enabled_accounts * _MAX_CONCURRENT_PER_ACCOUNT
        max_concurrent = int(_GLOBAL_PARAMS.get("max_concurrent_tasks") or 0)
        capacity = max_concurrent if max_concurrent > 0 else auto_capacity
        current_active = sum(s.active_tasks for s in _ACCOUNT_MGR._slots.values() if not s.disabled)
        return {
            "ok": True,
            "total_accounts": total_accounts,
            "max_concurrent_per_account": _MAX_CONCURRENT_PER_ACCOUNT,
            "auto_capacity": auto_capacity,
            "custom_max_concurrent": max_concurrent,
            "capacity": capacity,
            "current_active": current_active,
            "available_slots": capacity - current_active,
            "is_full": current_active >= capacity,
            "accounts": _ACCOUNT_MGR.status_summary(),
        }

    elif action == "get_logs":
        try:
            if _LOG_FILE.exists():
                with open(_LOG_FILE, "r", encoding="utf-8", errors="ignore") as f:
                    lines = f.readlines()
                last_lines = lines[-200:]
                log_content = "".join(last_lines)
                return {"ok": True, "logs": log_content}
            else:
                return {"ok": True, "logs": "等待日志产生..."}
        except Exception as e:
            return {"ok": False, "error": str(e)}

    elif action == "check_license_status":
        try:
            from runway_sec import get_license
            lic = get_license()
            status_info = lic.check_status()
            return {"ok": True, **status_info}
        except Exception as e:
            return {"ok": False, "error": str(e)}

    elif action == "activate_license":
        try:
            from runway_sec import get_license
            lic = get_license()
            license_key = str(data or "").strip()
            res = lic.activate(license_key)
            ok = res.get("is_valid", False)
            return {"ok": ok, "message": res.get("message"), "error": res.get("error"), **res}
        except Exception as e:
            return {"ok": False, "error": str(e)}

    elif action == "deactivate_license":
        try:
            from runway_sec import get_license
            lic = get_license()
            res = lic.deactivate()
            return {"ok": True, "message": res.get("message"), **res}
        except Exception as e:
            return {"ok": False, "error": str(e)}

    elif action == "check_plugin_update":
        try:
            return _check_plugin_update()
        except Exception as e:
            return {"ok": False, "error": str(e), "repo": _UPDATE_REPO}

    elif action == "install_plugin_update":
        try:
            d = data if isinstance(data, dict) else {}
            zip_url = str(d.get("zip_url") or "").strip()
            return _install_plugin_update(zip_url)
        except Exception as e:
            return {"ok": False, "error": str(e), "repo": _UPDATE_REPO}

    return {"ok": False, "error": f"未知操作: {action}"}
