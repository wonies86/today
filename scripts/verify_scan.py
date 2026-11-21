#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""조건식 × 당일 수급 교집합 · 과거 차트 반응 검증

    python3 scripts/verify_scan.py            # data.json 결과 검증(네트워크 없음)
    python3 scripts/verify_scan.py --live     # 네이버 일봉을 다시 받아 독립 재계산해 대조

검사 항목
  · 최신 항목에 conditionScan / conditionHits / chartReactions 가 있고 규칙이 맞는지
  · 포착 종목마다 A·D·E 참, B 또는 C 참, 거래대금 100억 이상, 거래대금 내림차순
  · charts.stocks 는 [시,고,저,종] 4개만 (용량 규칙)
  · 과거 반응 수치(0<=M<=N, 평균이 최소~최대 사이)가 맞는지
  · --live: 일봉 120거래일을 새로 받아 A~E·백테스트를 다른 코드로 다시 계산해 대조
"""

from __future__ import annotations

import json
import re
import sys
import urllib.request
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DATA_PATH = ROOT / "data.json"
FCHART = "https://fchart.stock.naver.com/sise.nhn"
UA = ("Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36")
HEADERS = {"User-Agent": UA, "Referer": "https://m.stock.naver.com/"}

RULE = "A and (B or C) and D and E"
MIN_VALUE = 100

fails: list[str] = []
passes: list[str] = []


def ok(msg: str) -> None:
    passes.append(msg)
    print(f"  ✓ {msg}")


def bad(msg: str) -> None:
    fails.append(msg)
    print(f"  ✗ {msg}")


def check(cond: bool, good: str, wrong: str) -> None:
    (ok if cond else bad)(good if cond else wrong)


def fetch_bars(code: str, count: int = 120):
    url = f"{FCHART}?symbol={code}&timeframe=day&count={count}&requestType=0"
    try:
        req = urllib.request.Request(url, headers=HEADERS)
        with urllib.request.urlopen(req, timeout=20) as res:
            text = res.read().decode("euc-kr", "replace")
    except Exception:                       # noqa: BLE001
        return None
    rows = []
    for m in re.finditer(r'item data="([^"]+)"', text):
        p = m.group(1).split("|")
        if len(p) < 6:
            continue
        try:
            rows.append({"d": p[0], "o": int(p[1]), "h": int(p[2]),
                         "l": int(p[3]), "c": int(p[4]), "v": int(p[5])})
        except ValueError:
            continue
    return rows[-count:] if rows else None


def recompute(rows):
    """독립 구현 — update_market.py 를 가져다 쓰지 않고 다시 계산한다."""
    c = [r["c"] for r in rows]
    v = [r["v"] for r in rows]
    n = len(c)
    ma = lambda k: sum(c[n - k:]) / k
    ma20, ma60, ma115 = ma(20), ma(60), ma(115)
    vol5 = sum(v[n - 6:n - 1]) / 5
    val5 = sum(c[i] * v[i] for i in range(n - 6, n - 1)) / 5
    gap = abs(ma20 - ma60) / min(ma20, ma60) * 100
    cond = {
        "A": ma20 < ma60 < ma115,
        "B": vol5 >= 55555,
        "C": val5 >= 50000000,
        "D": c[-1] > ma20,
        "E": gap <= 2.0,
    }
    # 백테스트 — 20일선 상향 돌파 또는 20일 평균 1.5배 양봉, 이후 5봉 고가
    sig = 0
    up = 0
    for i in range(21, n - 5):
        p = sum(c[i - 20:i]) / 20
        t = sum(c[i - 19:i + 1]) / 20
        cross = c[i - 1] <= p and c[i] > t
        pv = sum(v[i - 20:i]) / 20
        surge = pv and v[i] >= 1.5 * pv and c[i] > rows[i]["o"]
        if not (cross or surge):
            continue
        sig += 1
        if max(r["h"] for r in rows[i + 1:i + 6]) > c[i]:
            up += 1
    return {"conditions": cond, "gap": gap, "n": sig, "m": up,
            "last": rows[-1]["d"]}


def check_scanner(s: dict) -> None:
    """scanners[] 항목 하나 — 필수 키·포착 규칙·정렬."""
    name = s.get("name") or s.get("id") or "?"
    need = ("id", "name", "summary", "formula", "minValue", "rules",
            "asOf", "basis", "updatedAt", "scanned", "hits", "reactions")
    missing = [k for k in need if k not in s]
    check(not missing, f"[{name}] 필수 키 12개 있음", f"[{name}] 필수 키 빠짐 {missing}")
    hits = s.get("hits") or []
    vals = [h.get("value_eok") or 0 for h in hits]
    check(vals == sorted(vals, reverse=True), f"[{name}] {len(hits)}종목 거래대금 내림차순",
          f"[{name}] 정렬 안 됨: {vals}")
    check(all(v >= (s.get("minValue") or 100) for v in vals),
          f"[{name}] 포착 종목 모두 {s.get('minValue')}억 이상",
          f"[{name}] 기준 미달 포함: {vals}")
    check(all(h.get("passed") for h in hits), f"[{name}] 포착 종목 모두 조건 통과",
          f"[{name}] 미통과 종목이 hits 에 있음")
    codes = [h.get("code") for h in hits]
    check(len(codes) == len(set(codes)), f"[{name}] 포착 종목 중복 없음", f"[{name}] 포착 종목 중복")
    for h in hits:
        cnd = h.get("conditions") or {}
        check(all(cnd.get(k) for k in ("A", "D", "E")), f"[{name}] {h.get('name')}: A·D·E 충족",
              f"[{name}] {h.get('name')}: A·D·E 미충족 {cnd}")
        check(bool(cnd.get("B") or cnd.get("C")), f"[{name}] {h.get('name')}: B 또는 C 충족",
              f"[{name}] {h.get('name')}: B·C 모두 미충족")


def main(argv) -> int:
    live = "--live" in argv
    data = json.loads(DATA_PATH.read_text(encoding="utf-8"))
    entry = data[0]
    print(f"[verify_scan] {entry.get('date')} · {DATA_PATH.stat().st_size / 1024:.0f}KB")
    meta = entry.get("conditionScan") or {}
    hits = entry.get("conditionHits") or []
    rx = entry.get("chartReactions") or {}

    check(bool(meta), "conditionScan 있음", "conditionScan 없음")
    check(bool(hits), "conditionHits 있음", "conditionHits 없음")
    check(meta.get("rule") == RULE, f"규칙 '{RULE}'", f"규칙 다름: {meta.get('rule')}")
    check(meta.get("minValue") == MIN_VALUE, "거래대금 기준 100억",
          f"기준 다름: {meta.get('minValue')}")
    check(meta.get("scanned", 0) > 100, f"{meta.get('scanned')}종목 계산",
          "계산 종목 수가 너무 적음")

    # ── 다중 조건식(scanners) — 조건식을 늘리면 여기도 자동으로 검사한다 ──
    scanners = entry.get("scanners") or []
    check(bool(scanners), f"scanners {len(scanners)}개 (다중 조건식 구조)", "scanners 없음")
    ids = [s.get("id") for s in scanners]
    check(len(ids) == len(set(ids)) and all(ids), "조건식 id 중복·빈 값 없음",
          f"조건식 id 이상 {ids}")
    if scanners:
        first = scanners[0]
        check(first.get("name") == "세력꿈틀이", "첫 조건식 이름 '세력꿈틀이'",
              f"첫 조건식 이름 다름: {first.get('name')!r}")
        check(first.get("hits") == hits, "scanners[0].hits == conditionHits (하위 호환)",
              "scanners[0].hits 와 conditionHits 불일치")
        check(first.get("formula") == RULE and first.get("minValue") == MIN_VALUE,
              f"세력꿈틀이 수식 {RULE} · {MIN_VALUE}억", "세력꿈틀이 수식/기준 다름")
        check(len(first.get("rules") or []) == 5, "세력꿈틀이 필터 기준 5개(A~E)",
              f"필터 기준 개수 다름: {len(first.get('rules') or [])}")
    for s in scanners:
        check_scanner(s)

    charts = entry.get("charts") or {}
    stocks = charts.get("stocks") or {}
    four = sum(1 for bars in stocks.values() if bars and len(bars[0]) == 4)
    check(bool(stocks) and four == len(stocks), f"charts.stocks {four}종목 모두 [o,h,l,c] 4개",
          f"charts.stocks 형식 위반 {len(stocks) - four}종목")

    values = [h.get("value_eok") or 0 for h in hits]
    check(values == sorted(values, reverse=True), "거래대금 내림차순 정렬",
          f"정렬 안 됨: {values}")
    check(all(v >= MIN_VALUE for v in values), f"{len(hits)}종목 모두 100억 이상",
          f"100억 미만 포함: {values}")
    codes = [h.get("code") for h in hits]
    check(len(codes) == len(set(codes)), "포착 종목 중복 없음", "포착 종목 중복")

    for h in hits:
        cnd = h.get("conditions") or {}
        name = h.get("name")
        check(all(cnd.get(k) for k in ("A", "D", "E")), f"{name}: A·D·E 충족",
              f"{name}: A·D·E 미충족 {cnd}")
        check(bool(cnd.get("B") or cnd.get("C")), f"{name}: B 또는 C 충족",
              f"{name}: B·C 모두 미충족 {cnd}")
        bt = h.get("backtest") or {}
        n, m = bt.get("n"), bt.get("m")
        plausible = (isinstance(n, int) and isinstance(m, int) and 0 <= m <= n
                     and (n == 0 or (bt.get("avg") is not None
                                     and bt["avg"] <= bt["best"]["gain"] + 1e-6
                                     and bt["avg"] >= bt["worst"]["gain"] - 1e-6)))
        check(plausible, f"{name}: 과거 반응 {m}/{n}회 · 평균 {bt.get('avg')}%",
              f"{name}: 과거 반응 수치 이상 {bt}")
        check(bool(h.get("patternText")) and bool(h.get("summary")),
              f"{name}: 차트 구조·요약 있음", f"{name}: 차트 구조·요약 없음")

    for code, item in rx.items():
        cnd = item.get("conditions") or {}
        hit_like = (cnd.get("A") and (cnd.get("B") or cnd.get("C"))
                    and cnd.get("D") and cnd.get("E") and (item.get("value_eok") or 0) >= MIN_VALUE)
        check(not hit_like, f"참고용 {item.get('name')}: 포착 목록과 중복 없음",
              f"참고용 {item.get('name')}가 100억+ 조건 충족인데 conditionHits에 없음")
        check(isinstance(item.get("backtest"), dict), f"참고용 {item.get('name')}: 반응 수치 있음",
              f"참고용 {item.get('name')}: 반응 수치 없음")

    size_kb = DATA_PATH.stat().st_size / 1024
    check(size_kb < 3000, f"data.json {size_kb:.0f}KB (3,000KB 미만)", f"data.json 비대 {size_kb:.0f}KB")

    if live:
        print("[live] 네이버 일봉으로 독립 재계산 대조…")
        with ThreadPoolExecutor(max_workers=8) as pool:
            bars = dict(pool.map(lambda c: (c, fetch_bars(c)), codes))
        for h in hits:
            code = h.get("code")
            rows = bars.get(code)
            if not rows or len(rows) < 116:
                bad(f"{h.get('name')}: 일봉을 받지 못해 대조 불가")
                continue
            r = recompute(rows)
            same = (r["conditions"] == {k: bool(v) for k, v in (h.get("conditions") or {}).items()})
            check(same, f"{h.get('name')}: A~E 재계산 일치 {r['conditions']}",
                  f"{h.get('name')}: A~E 불일치 {r['conditions']} vs {h.get('conditions')}")
            near = abs(r["gap"] - (h.get("gap") or 0)) < 0.05
            check(near, f"{h.get('name')}: 이격 {r['gap']:.2f}% vs {h.get('gap')}%",
                  f"{h.get('name')}: 이격 불일치 {r['gap']:.2f}% vs {h.get('gap')}%")
            bt = h.get("backtest") or {}
            check(r["n"] == bt.get("n") and r["m"] == bt.get("m"),
                  f"{h.get('name')}: 백테스트 {r['m']}/{r['n']}회 일치",
                  f"{h.get('name')}: 백테스트 불일치 재계산 {r['m']}/{r['n']} vs {bt.get('m')}/{bt.get('n')}")

    print(f"\n결과: 통과 {len(passes)} · 실패 {len(fails)}")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
