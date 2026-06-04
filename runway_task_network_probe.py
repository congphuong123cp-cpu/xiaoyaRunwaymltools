# -*- coding: utf-8 -*-
"""
Runway Seedance 2.0 task/network probe.

Purpose:
- Capture the task id returned after clicking Generate.
- Watch later browser network responses for the same task id.
- Compare network artifact URLs with DOM video/download URLs.
- Optionally download the matched video URL.

Default mode is manual: the browser opens, the script listens, and you click
Generate yourself. Use --auto-generate to let the script click Generate.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
import time
from datetime import datetime
from pathlib import Path
from typing import Any


ROOT_DIR = Path(__file__).resolve().parent
PLUGIN_ROOT_DIR = ROOT_DIR.parent
DATA_DIR = PLUGIN_ROOT_DIR / "data"
RUNTIME_ROOT_DIR = PLUGIN_ROOT_DIR / "runtime"
PY_DEPS_DIR = RUNTIME_ROOT_DIR / "chrome_buffer" / "runwayml_global" / ".runwayml_pydeps"

if PY_DEPS_DIR.exists() and str(PY_DEPS_DIR) not in sys.path:
    sys.path.insert(0, str(PY_DEPS_DIR))

OUT_DIR = ROOT_DIR / "layout_test_shots"
OUT_DIR.mkdir(exist_ok=True)

RUNWAY_URL = (
    "https://app.runwayml.com/video-tools/ai-tools/"
    "generate?tool=video&mode=tools&model=seedance-2"
)


def _now() -> str:
    return datetime.now().strftime("%Y-%m-%d %H:%M:%S")


def _extract_task_id(obj: Any) -> str:
    if not isinstance(obj, dict):
        return ""
    direct = obj.get("id") or obj.get("taskId") or obj.get("task_id") or obj.get("uuid")
    if direct:
        return str(direct)
    for key in ("task", "data", "result"):
        val = obj.get(key)
        if isinstance(val, dict):
            tid = val.get("id") or val.get("taskId") or val.get("task_id") or val.get("uuid")
            if tid:
                return str(tid)
    return ""


def _extract_status(obj: Any) -> str:
    if isinstance(obj, dict):
        for key in ("status", "state", "progressText"):
            if obj.get(key):
                return str(obj.get(key))
        for key in ("task", "data", "result"):
            val = obj.get(key)
            if isinstance(val, dict):
                status = _extract_status(val)
                if status:
                    return status
    return ""


def _extract_urls(obj: Any) -> list[str]:
    found: list[str] = []

    def walk(value: Any) -> None:
        if isinstance(value, str):
            if value.startswith("http://") or value.startswith("https://"):
                found.append(value)
            else:
                for match in re.findall(r"https?://[^\s\"'<>]+", value):
                    found.append(match)
        elif isinstance(value, list):
            for item in value:
                walk(item)
        elif isinstance(value, dict):
            for item in value.values():
                walk(item)

    walk(obj)
    deduped: list[str] = []
    seen: set[str] = set()
    for url in found:
        clean = url.rstrip(").,;")
        if clean not in seen:
            seen.add(clean)
            deduped.append(clean)
    return deduped


def _likely_video_urls(urls: list[str]) -> list[str]:
    likely: list[str] = []
    for url in urls:
        lower = url.lower()
        if (
            ".mp4" in lower
            or ".mov" in lower
            or "dnznrvs" in lower
            or "video" in lower
            or "artifact" in lower
            or "download" in lower
        ):
            likely.append(url)
    return likely


def _summarize_assets(obj: Any) -> list[dict[str, Any]]:
    if not isinstance(obj, dict):
        return []
    assets = obj.get("assets") or obj.get("pendingAssets") or []
    if not isinstance(assets, list):
        return []
    summary: list[dict[str, Any]] = []
    id_keys = (
        "id",
        "uuid",
        "assetId",
        "taskId",
        "task_id",
        "sourceTaskId",
        "sourceTaskID",
        "parentTaskId",
        "generationTaskId",
        "assetGroupId",
        "targetAssetGroupId",
    )
    meta_keys = ("name", "filename", "createdAt", "updatedAt", "type", "mediaType", "taskType", "status")
    for asset in assets[:12]:
        if not isinstance(asset, dict):
            continue
        item: dict[str, Any] = {}
        for key in id_keys + meta_keys:
            if key in asset:
                val = asset.get(key)
                item[key] = str(val)[:180] if val is not None else None
        urls = _likely_video_urls(_extract_urls(asset))
        if urls:
            item["likely_urls"] = urls[:3]
        nested_keys = []
        for key, val in asset.items():
            if isinstance(val, (dict, list)):
                nested_keys.append(key)
        item["keys"] = list(asset.keys())[:40]
        item["nested_keys"] = nested_keys[:20]
        summary.append(item)
    return summary


def _set_prompt(page: Any, prompt: str) -> None:
    loc = page.locator('[role="textbox"][aria-label="Prompt"]').first
    loc.wait_for(state="visible", timeout=90000)
    loc.click(force=True)
    page.keyboard.press("Control+A")
    page.keyboard.press("Backspace")
    page.evaluate(
        """text => {
            const el = document.querySelector('[role="textbox"][aria-label="Prompt"]');
            if (!el) return false;
            el.focus();
            el.textContent = text;
            el.dispatchEvent(new InputEvent('input', {bubbles: true, inputType: 'insertText', data: text}));
            el.dispatchEvent(new Event('change', {bubbles: true}));
            return true;
        }""",
        prompt,
    )
    page.keyboard.press("End")
    page.mouse.click(10, 10)


def _set_duration(page: Any, duration: int) -> None:
    target = f"{duration}s"
    btn = None
    for sel in (
        'button[aria-label="Duration"]',
        'button[aria-label*="duration" i]',
        f'button:has-text("{target}")',
        'button:has-text("s")',
    ):
        try:
            cand = page.locator(sel).first
            if cand.is_visible(timeout=1500):
                btn = cand
                break
        except Exception:
            continue
    if not btn:
        print(f"[{_now()}] duration button not found; keeping current duration")
        return
    try:
        if target in (btn.inner_text(timeout=1000) or ""):
            print(f"[{_now()}] duration already {target}")
            return
    except Exception:
        pass
    btn.click(force=True)
    page.wait_for_timeout(500)
    input_loc = None
    for sel in (
        'input[aria-label*="duration" i]:visible',
        'input[type="number"]:visible',
        '[role="spinbutton"]:visible',
        'input:visible',
        '[role="textbox"]:visible',
    ):
        try:
            for cand in page.locator(sel).all()[:10]:
                box = cand.bounding_box()
                if box and box.get("width", 999) <= 160 and box.get("height", 999) <= 90:
                    input_loc = cand
                    break
            if input_loc:
                break
        except Exception:
            continue
    if not input_loc:
        print(f"[{_now()}] duration input not found after opening panel")
        page.keyboard.press("Escape")
        return
    input_loc.click(force=True)
    try:
        input_loc.fill(str(duration))
    except Exception:
        page.keyboard.press("Control+A")
        page.keyboard.type(str(duration))
    page.keyboard.press("Enter")
    page.wait_for_timeout(300)
    page.keyboard.press("Escape")
    page.mouse.click(10, 10)
    print(f"[{_now()}] submitted duration={duration}s")


def _page_active(page: Any) -> bool:
    selectors = [
        'text=/queued|processing|generating|rendering|in progress|排队|生成中|渲染中|处理中/i',
        '[class*="progress" i]',
        '[data-testid*="progress" i]',
        '[role="progressbar"]',
    ]
    for sel in selectors:
        try:
            for loc in page.locator(sel).all()[:8]:
                if loc.is_visible(timeout=100):
                    return True
        except Exception:
            continue
    return False


def _visible_dom_video_urls(page: Any) -> list[str]:
    urls: list[str] = []
    try:
        for loc in page.locator("video, video source, a[download]").all():
            try:
                src = loc.get_attribute("src") or loc.get_attribute("href") or ""
                if src.startswith("http"):
                    urls.append(src)
            except Exception:
                continue
    except Exception:
        pass
    return list(dict.fromkeys(urls))


def _click_history_or_recents(page: Any) -> None:
    candidates = [
        'text="Recents"',
        'text="Recent"',
        'text="History"',
        'text="历史"',
        '[aria-label*="Recent" i]',
        '[aria-label*="History" i]',
        '[href*="recent" i]',
        '[href*="history" i]',
    ]
    for sel in candidates:
        try:
            loc = page.locator(sel).first
            if loc.is_visible(timeout=1000):
                loc.click(force=True)
                print(f"[{_now()}] clicked history selector: {sel}")
                page.wait_for_timeout(5000)
                return
        except Exception:
            continue
    print(f"[{_now()}] history/recents entry not found")


def _visible_text_probe(page: Any) -> dict[str, Any]:
    try:
        return page.evaluate(
            """() => {
                const visible = el => {
                    const r = el.getBoundingClientRect();
                    const s = getComputedStyle(el);
                    return r.width > 1 && r.height > 1 && s.visibility !== 'hidden' && s.display !== 'none';
                };
                const items = Array.from(document.querySelectorAll('button,a,[role="button"],[role="tab"]'))
                    .filter(visible)
                    .slice(0, 160)
                    .map(el => ({
                        tag: el.tagName,
                        text: (el.innerText || el.textContent || '').trim().replace(/\\s+/g, ' ').slice(0, 120),
                        aria: el.getAttribute('aria-label') || '',
                        href: el.getAttribute('href') || '',
                        role: el.getAttribute('role') || '',
                    }));
                return {url: location.href, title: document.title, items};
            }"""
        )
    except Exception as exc:
        return {"error": str(exc)}


def _download_with_browser_cookies(context: Any, url: str, output_path: Path) -> None:
    import requests

    cookies = context.cookies()
    cookie_header = "; ".join(f"{c.get('name')}={c.get('value')}" for c in cookies if c.get("name"))
    headers = {
        "User-Agent": "Mozilla/5.0",
        "Referer": "https://app.runwayml.com/",
    }
    if cookie_header:
        headers["Cookie"] = cookie_header
    with requests.get(url, headers=headers, stream=True, timeout=180) as resp:
        resp.raise_for_status()
        with output_path.open("wb") as fh:
            for chunk in resp.iter_content(chunk_size=1024 * 1024):
                if chunk:
                    fh.write(chunk)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--alias", default="congphuong123cp")
    parser.add_argument("--duration", type=int, default=1)
    parser.add_argument("--prompt", default="A simple cinematic shot of a small glass cube on a table, slow camera move, no text, no watermark.")
    parser.add_argument("--auto-generate", action="store_true")
    parser.add_argument("--history", action="store_true")
    parser.add_argument("--timeout", type=int, default=5400)
    parser.add_argument("--devtools", action="store_true")
    parser.add_argument("--maximized", action="store_true")
    parser.add_argument("--no-download", action="store_true")
    args = parser.parse_args()

    stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    json_path = OUT_DIR / f"task_network_probe_{stamp}.json"
    shot_path = OUT_DIR / f"task_network_probe_{stamp}.png"
    mp4_path = OUT_DIR / f"task_network_probe_{stamp}.mp4"
    state_path = DATA_DIR / "storage_states" / f"{args.alias}_state.json"

    events: list[dict[str, Any]] = []
    current_task_id = ""
    matched_urls: list[str] = []
    dom_urls_at_click: set[str] = set()

    def record(event: dict[str, Any]) -> None:
        event["ts"] = _now()
        events.append(event)
        print(json.dumps(event, ensure_ascii=False)[:1200], flush=True)
        json_path.write_text(
            json.dumps(
                {
                    "current_task_id": current_task_id,
                    "matched_urls": matched_urls,
                    "events": events,
                },
                ensure_ascii=False,
                indent=2,
            ),
            encoding="utf-8",
        )

    from playwright.sync_api import sync_playwright

    with sync_playwright() as pw:
        launch_opts = {
            "headless": False,
            "args": ["--window-size=1000,720", "--window-position=80,80"],
        }
        if args.maximized:
            launch_opts["args"] = ["--start-maximized"]
        if args.devtools:
            launch_opts["args"].append("--auto-open-devtools-for-tabs")
        try:
            browser = pw.chromium.launch(channel="chrome", **launch_opts)
        except Exception:
            browser = pw.chromium.launch(**launch_opts)

        context_opts: dict[str, Any] = {"no_viewport": True}
        if state_path.exists() and state_path.stat().st_size > 100:
            context_opts["storage_state"] = str(state_path)
        context = browser.new_context(**context_opts)
        page = context.new_page()

        def on_response(response: Any) -> None:
            nonlocal current_task_id, matched_urls
            try:
                url = response.url
                lower = url.lower()
                method = response.request.method
                watch = (
                    "api.runwayml.com" in lower
                    or "graphql" in lower
                    or any(key in lower for key in ("task", "generate", "artifact", "download", "seedance", "asset", "session"))
                )
                if not watch:
                    return
                body: Any = None
                text = ""
                try:
                    body = response.json()
                except Exception:
                    try:
                        text = response.text()[:1500]
                    except Exception:
                        text = ""

                tid = _extract_task_id(body) if body is not None else ""
                status = _extract_status(body) if body is not None else ""
                urls = _extract_urls(body) if body is not None else _extract_urls(text)
                likely = _likely_video_urls(urls)
                asset_summary = _summarize_assets(body)
                body_has_current = bool(current_task_id and body is not None and current_task_id in json.dumps(body, ensure_ascii=False))

                if method == "POST" and tid and not current_task_id:
                    current_task_id = tid
                    record({"type": "task_created", "method": method, "url": url, "status_code": response.status, "task_id": tid, "task_status": status, "likely_urls": likely})
                elif tid or body_has_current or likely:
                    if current_task_id and (tid == current_task_id or body_has_current):
                        for item in likely:
                            if item not in matched_urls:
                                matched_urls.append(item)
                    record({"type": "network", "method": method, "url": url, "status_code": response.status, "task_id": tid, "matches_current": bool(tid == current_task_id or body_has_current), "task_status": status, "likely_urls": likely, "asset_summary": asset_summary, "body_keys": list(body.keys())[:12] if isinstance(body, dict) else []})
                elif "api.runwayml.com" in lower or "graphql" in lower:
                    record({"type": "api_seen", "method": method, "url": url, "status_code": response.status, "asset_summary": asset_summary, "body_keys": list(body.keys())[:12] if isinstance(body, dict) else [], "text": text[:300] if text else ""})
            except Exception as exc:
                record({"type": "probe_error", "error": str(exc)})

        page.on("response", on_response)
        record({"type": "start", "alias": args.alias, "auto_generate": args.auto_generate, "duration": args.duration, "state_path": str(state_path), "state_exists": state_path.exists()})

        page.goto(RUNWAY_URL, wait_until="domcontentloaded", timeout=120000)
        for _ in range(120):
            try:
                if (
                    page.locator('[role="textbox"][aria-label="Prompt"]').first.is_visible(timeout=500)
                    and page.locator('button:has-text("Generate")').first.is_visible(timeout=500)
                ):
                    break
            except Exception:
                pass
            time.sleep(1)

        _set_duration(page, max(1, min(15, args.duration)))
        _set_prompt(page, args.prompt)
        dom_urls_at_click = set(_visible_dom_video_urls(page))
        record({"type": "ready", "url": page.url, "dom_urls_before_generate": list(dom_urls_at_click)})

        if args.history:
            record({"type": "visible_controls_before_history", "probe": _visible_text_probe(page)})
            _click_history_or_recents(page)
            record({"type": "visible_controls_after_history", "probe": _visible_text_probe(page), "dom_urls": _visible_dom_video_urls(page)})

        if args.auto_generate:
            page.locator('button:has-text("Generate")').first.click(force=True)
            record({"type": "clicked_generate"})
        else:
            record({"type": "manual_wait", "message": "Click Generate in the opened browser. The probe is listening."})

        start = time.time()
        chosen_url = ""
        while time.time() - start < args.timeout:
            page.wait_for_timeout(5000)
            dom_urls = [u for u in _visible_dom_video_urls(page) if u not in dom_urls_at_click]
            active = _page_active(page)
            if dom_urls:
                record({"type": "dom_urls", "active": active, "urls": dom_urls})
            if matched_urls:
                chosen_url = _likely_video_urls(matched_urls)[0] if _likely_video_urls(matched_urls) else matched_urls[0]
                record({"type": "selected_network_url", "url": chosen_url})
                break
            if current_task_id and dom_urls and not active:
                chosen_url = _likely_video_urls(dom_urls)[0] if _likely_video_urls(dom_urls) else dom_urls[0]
                record({"type": "selected_dom_fallback_url", "url": chosen_url})
                break

        try:
            page.screenshot(path=str(shot_path), full_page=True)
        except Exception:
            pass

        downloaded = ""
        if chosen_url and not args.no_download:
            try:
                _download_with_browser_cookies(context, chosen_url, mp4_path)
                downloaded = str(mp4_path)
                record({"type": "downloaded", "path": downloaded, "bytes": mp4_path.stat().st_size})
            except Exception as exc:
                record({"type": "download_failed", "url": chosen_url, "error": str(exc)})

        result = {
            "current_task_id": current_task_id,
            "matched_urls": matched_urls,
            "chosen_url": chosen_url,
            "downloaded": downloaded,
            "json": str(json_path),
            "screenshot": str(shot_path),
            "events": events,
        }
        json_path.write_text(json.dumps(result, ensure_ascii=False, indent=2), encoding="utf-8")
        print(json.dumps(result, ensure_ascii=False, indent=2))

        context.close()
        browser.close()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
