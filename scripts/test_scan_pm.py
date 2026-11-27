#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""종가베팅 핵심 × 오후장 수급(pm) 회귀 테스트 — 네트워크 없이 돈다.

    python3 scripts/test_scan_pm.py

2026-11-27 장애: `종가베팅 핵심` 15종목이 모두 `pending: true`(오후장 대기)로 남았다.
원인은 분봉 조회 한도(PM_MAX_FETCH)를 거래대금 상위 종목이 다 써 버려, 실제 후보
(A·B·C를 통과해 D만 남은 종목)는 분봉을 한 번도 받지 못한 것이다. 그런데
`closing_edge_scan` 은 '분봉 없음(None)'을 '아직 판정 전(pending)'과 같이 봐서
장이 끝난 뒤에도 대기로 통과시켰다.

검사 항목
 1. 판정 시각(15:40) 뒤 — 거래대금 24위 밖 후보도 분봉을 받아 D를 판정한다(pending 아님)
 2. 판정 시각 뒤 — 분봉을 못 받으면 '대기'가 아니라 '미측정'이고 목록에 올리지 않는다
 3. 분봉 한도는 후보(관찰·카드 → A·B·C 통과 후보 → 거래대금 상위) 순서로 쓴다
 4. 13:00 이전(오전장) — 분봉을 한 번도 받지 않고 모두 대기(pending)로 남긴다
 5. 분봉 조회 실패 — '미측정'으로 표시하고 대기로 통과시키지 않는다
"""

from __future__ import annotations

import sys
from datetime import datetime
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import update_market as um  # noqa: E402

FAILS: list[str] = []
OKS: list[str] = []


def ok(msg):
    OKS.append(msg)
    print(f"  ✓ {msg}")


def bad(msg):
    FAILS.append(msg)
    print(f"  ✗ {msg}")


def check(cond, good, wrong):
    (ok if cond else bad)(good if cond else wrong)


CODES = [f"A{i:02d}" for i in range(30)]          # 거래대금 내림차순 30종목
CAND = CODES[24]                                  # 25위 — 예전 한도(24) 밖 후보
DAY = "20261127"


def daily_rows(i: int, days: int = 300):
    """일봉 — 52주 고점 근처(A 참)로 완만히 오르는 종목. 후보만 당일 +5%."""
    rows = []
    price = 10000 + i * 100
    base_vol = 100000 + i
    for k in range(days):
        d = f"2026{1 + k // 28:02d}{1 + k % 28:02d}"
        o = price
        c = int(price * 1.001)
        h = max(o, c) + 50
        low = min(o, c) - 50
        rows.append({"d": d, "o": o, "h": h, "l": low, "c": c,
                     "v": base_vol + (k % 5) * 1000})
        price = c
    last = rows[-1]
    step = 1.05 if rows[-1] and False else 1                     # noqa: F841 - 가독용
    rows[-1] = dict(last)                                        # 당일 봉은 마지막 날
    return rows


def make_series():
    series, deep = {}, {}
    for i, code in enumerate(CODES):
        rows = daily_rows(i)
        series[code] = rows[-130:]
        deep[code] = rows[-250:]
    return series, deep


def make_all_stocks():
    rows = []
    for i, code in enumerate(CODES):
        chg = 5.0 if code == CAND else 0.5
        px = 20000 + i * 100
        rows.append([code, f"종목{code}", "KOSPI", px, chg, 1000 - i * 20, "반도체", 5000, 1.2])
    return rows


def fake_minute(code, day):
    """13:00 10,000원 → 15:30 10,300원, 오후에 거래대금이 몰린 분봉."""
    if day != DAY:
        return None
    bars, cum = [], 1_000_000
    for hm in range(540, 1200):
        price = 10000 if hm <= 780 else 10000 + (hm - 780) * 2
        if 780 < hm <= 930:
            cum += 50000
        elif hm > 930:
            cum += 1000
        bars.append((hm, price, cum))
    return bars


def hit_of(scan, code):
    """종가베팅 핵심 조건식 안에서만 찾는다(다른 조건식에 같은 종목이 있어도 헷갈리지 않게)."""
    edge = edge_of(scan)
    for h in edge.get("hits") or []:
        if h.get("code") == code:
            return edge, h
    h = (edge.get("reactions") or {}).get(code)
    return (edge, h) if h else (edge, None)


def run(now, **kwargs):
    series, deep = make_series()
    return um.build_condition_scan(series, make_all_stocks(), kwargs.pop("extra", set()),
                                   now, deep_series=deep,
                                   index_chg={"KOSPI": 0.0},
                                   investor=kwargs.pop("investor", None),
                                   dominance={"sectors": [{"name": "반도체", "share": 12.0}]})


def edge_of(scan):
    return next(s for s in scan["scanners"] if s["id"] == "closing-edge")


def test_afternoon_candidate_outside_top_value():
    calls = []
    real = um.fetch_minute_bars

    def counting(code, day):
        calls.append(code)
        return fake_minute(code, day)

    um.fetch_minute_bars = counting
    try:
        scan = run(datetime(2026, 11, 27, 15, 40))
    finally:
        um.fetch_minute_bars = real
    edge = edge_of(scan)
    check(CAND in calls, f"거래대금 25위 후보({CAND})도 분봉을 받는다",
          f"25위 후보({CAND})가 이번에도 분봉을 못 받았다 — 호출 {len(calls)}건")
    _, hit = hit_of(scan, CAND)
    check(hit is not None, f"후보 {CAND} 종가베팅 핵심 포착",
          f"후보 {CAND} 포착 안 됨 (D={((hit or {}).get('conditions') or {}).get('D')})")
    if hit:
        pm = hit.get("pm") or {}
        check(not hit.get("pending"), "판정 시각 뒤 포착 항목이 '대기'로 남지 않는다",
              f"판정 시각(15:40)인데 pending=True — pm={pm}")
        check(pm.get("pass") is True, f"오후장 D 통과 (비중 {pm.get('pmShare')}% · {pm.get('chgPm')}%)",
              f"오후장 D 미판정/미통과 pm={pm}")
        check(((hit.get("conditions") or {}).get("D")) is True,
              "조건 D 표시가 오후장 판정과 일치", f"조건 D 표시 불일치 {(hit.get('conditions'))}")
    check(edge.get("pmMeasured", 0) <= um.PM_MAX_FETCH,
          f"분봉 조회 {edge.get('pmMeasured')}종목 (한도 {um.PM_MAX_FETCH})",
          f"분봉 조회 수가 한도를 넘음 {edge.get('pmMeasured')}")


def test_failed_measure_is_not_pending():
    real = um.fetch_minute_bars
    um.fetch_minute_bars = lambda code, day: None            # 분봉 실패
    try:
        scan = run(datetime(2026, 11, 27, 15, 40))
    finally:
        um.fetch_minute_bars = real
    _, hit = hit_of(scan, CAND)
    check(hit is None, "분봉을 못 받은 후보는 목록에 올리지 않는다",
          f"분봉 실패인데 포착 목록에 남음 {(hit or {}).get('pm')}")
    edge = edge_of(scan)
    check(not any(h.get("pending") for h in edge.get("hits") or []),
          "분봉 실패는 '대기'로 통과시키지 않는다",
          "분봉 실패인데 pending=True 로 통과")


def test_budget_priority():
    flow = um.AfternoonFlow(datetime(2026, 11, 27, 15, 40), limit=2)
    called = []
    real = um.fetch_minute_bars
    um.fetch_minute_bars = lambda code, day: (called.append(code) or fake_minute(code, day))
    try:
        flow.warm(["CAND", "OBS", "BIG1", "BIG2"])
        for code in ("CAND", "OBS", "BIG1", "BIG2"):
            flow.get(code, 500)
    finally:
        um.fetch_minute_bars = real
    check(called == ["CAND", "OBS"], f"한도 2종목은 앞선 우선순위에 쓴다 {called}",
          f"우선순위 무시 {called}")
    last = flow.get("BIG2", 500)
    check(last.get("status") == um.PM_MISS_STATE and last.get("measured") is False,
          f"한도 밖 종목은 '{um.PM_MISS_STATE}'", f"한도 밖 상태 이상 {last}")
    check("BIG2" in flow.skipped, "한도 밖 종목을 기록(pmSkipped)으로 남긴다",
          "한도 밖 종목 기록 없음")


def test_before_judge_stays_pending():
    called = []
    real = um.fetch_minute_bars
    um.fetch_minute_bars = lambda code, day: (called.append(code) or fake_minute(code, day))
    try:
        scan = run(datetime(2026, 11, 27, 10, 0))
    finally:
        um.fetch_minute_bars = real
    edge = edge_of(scan)
    check(not called, "오전장에는 분봉을 한 번도 받지 않는다", f"오전장에 분봉 호출 {len(called)}건")
    check(edge.get("hits") or edge.get("reactions"),
          f"오전장 대기 {len(edge.get('hits') or [])}종목을 목록에 남긴다", "오전장 대기 목록이 비었다")
    check(all(h.get("pending") for h in edge.get("hits") or []),
          "오전장 항목은 모두 pending", "오전장인데 pending 이 아닌 항목이 있다")
    check(not any(((h.get("pm") or {}).get("pass")) is True for h in edge.get("hits") or []),
          "오전장에는 D를 판정하지 않는다", "오전장인데 D가 참인 항목이 있다")


def main():
    for fn in (test_afternoon_candidate_outside_top_value, test_failed_measure_is_not_pending,
               test_budget_priority, test_before_judge_stays_pending):
        print(f"[{fn.__name__}]")
        fn()
    print(f"\n결과: 통과 {len(OKS)} · 실패 {len(FAILS)}")
    return 1 if FAILS else 0


if __name__ == "__main__":
    sys.exit(main())
