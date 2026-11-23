#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""조건식 × 당일 수급 교집합 · 과거 차트 반응 검증

    python3 scripts/verify_scan.py            # data.json 결과 검증(네트워크 없음)
    python3 scripts/verify_scan.py --live     # 네이버 일봉을 다시 받아 독립 재계산해 대조

검사 항목
  · 최신 항목의 scannersEncrypted(평문이 없는 경우)를 키로 풀어 검사 — 키는 저장소 밖
    `../.scanner_key` 또는 환경변수 SCANNER_KEY(키가 없으면 조건식 검사는 건너뛴다)
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


def formula_rule(formula: str):
    """'A and (B or C) and D' → (필수 키 [A, D], 또는 묶음 [B, C])."""
    groups = re.findall(r"\(([^)]*)\)", formula or "")
    flat = re.sub(r"\([^)]*\)", "", formula or "")
    req = [t for t in re.split(r"\s+", flat) if re.fullmatch(r"[A-Z]", t)]
    grp = []
    for g in groups:
        keys = [t.strip() for t in g.split("or") if re.fullmatch(r"[A-Z]", t.strip())]
        grp.extend(keys)
    return req, grp


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
    formula = s.get("formula") or ""
    req, grp = formula_rule(formula)
    for h in hits:
        cnd = h.get("conditions") or {}
        # 조건식마다 규칙이 다르다 — formula 에 적힌 필수 키와 (X or Y) 묶음만 검사한다
        check(all(cnd.get(k) for k in req), f"[{name}] {h.get('name')}: {'·'.join(req)} 충족",
              f"[{name}] {h.get('name')}: {'·'.join(req)} 미충족 {cnd}")
        if grp:
            check(any(cnd.get(k) for k in grp), f"[{name}] {h.get('name')}: {' 또는 '.join(grp)} 충족",
                  f"[{name}] {h.get('name')}: {'·'.join(grp)} 모두 미충족 {cnd}")


def load_scan(entry: dict) -> bool:
    """data.json 은 조건식 결과를 암호문으로만 가지고 있다 — 키가 있으면 풀어서 entry 에 붙인다."""
    if entry.get("scanners") or entry.get("conditionHits"):
        return True                              # 옛 평문 기록
    blob = entry.get("scannersEncrypted")
    if not (isinstance(blob, dict) and blob.get("ct")):
        return False
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    try:
        import update_market as um            # noqa: WPS433 - 같은 폴더 스크립트
    except Exception as exc:                  # noqa: BLE001
        print(f"  ! 잠금 해제 모듈을 불러오지 못했습니다({type(exc).__name__})")
        return False
    pw = um.scanner_key()
    if not pw:
        print("  ! 잠금 키가 없어 조건식 검사를 건너뜁니다 "
              "(../.scanner_key 또는 환경변수 SCANNER_KEY)")
        return False
    try:
        payload = um.decrypt_scan_payload(blob, pw)
    except Exception as exc:                  # noqa: BLE001
        print(f"  ! 잠금을 풀지 못했습니다({type(exc).__name__}) — 키가 다를 수 있습니다")
        return False
    for key in ("scanners", "conditionHits", "conditionScan", "chartReactions"):
        if key in payload:
            entry[key] = payload[key]
    print("  · scannersEncrypted 를 키로 풀었습니다")
    return True


def main(argv) -> int:
    live = "--live" in argv
    data = json.loads(DATA_PATH.read_text(encoding="utf-8"))
    entry = data[0]
    print(f"[verify_scan] {entry.get('date')} · {DATA_PATH.stat().st_size / 1024:.0f}KB")
    if not load_scan(entry):
        print("  · data.json 에 풀 수 있는 조건식 기록이 없습니다.")
        return 1
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

    # ── 기관·외인 연속 순매수(investorStreak) + 종목 뉴스 3건 ──
    inv = entry.get("investorStreak") or {}
    inv_stocks = inv.get("stocks") or {}
    check(bool(inv_stocks), f"investorStreak {len(inv_stocks)}종목", "investorStreak 없음")
    if inv_stocks:
        check(inv.get("order") == list(inv_stocks.keys()),
              "order == stocks 키 목록", "order 와 stocks 불일치")
        check(len(inv_stocks) <= 48, f"수집 상한 48종목 이하({len(inv_stocks)})",
              f"수집 종목 초과 {len(inv_stocks)}")
        check(bool(inv.get("asOf")) and len(str(inv.get("asOf"))) == 8,
              f"기준일 {inv.get('asOf')}", f"기준일 형식 이상 {inv.get('asOf')}")
        bad_rows = []
        for code, item in inv_stocks.items():
            rec = item.get("recent5") or []
            dts = [r.get("dt") for r in rec]
            streak_ok = all(isinstance(item.get(k), int)
                            for k in ("frgnStreak", "instStreak", "dualStreak"))
            if (not streak_ok or len(rec) > 5 or dts != sorted(dts)
                    or item.get("dualStreak", 0) < 0
                    or item.get("dualStreak", 0) > max(0, item.get("days", 0))
                    or abs(item.get("frgnStreak", 0)) > item.get("days", 0)
                    or abs(item.get("instStreak", 0)) > item.get("days", 0)
                    or item.get("instDetail", 0) is not None
                    or any((r.get("dt") or "") < (inv.get("asOf") or "") for r in rec[-1:])):
                bad_rows.append(code)
        check(not bad_rows, "연속일수·recent5(오래된→최신)·instDetail=None 규칙 맞음",
              f"연속매수 기록 이상 {bad_rows[:5]}")
    news = entry.get("investorNews") or {}
    news_stocks = news.get("stocks") or {}
    check(bool(news_stocks), f"investorNews {len(news_stocks)}종목", "investorNews 없음")
    if news_stocks:
        check(all(0 <= (v.get("checked") or 0) <= 3 for v in news_stocks.values()),
              "종목당 뉴스 3건 이하", "뉴스 3건 초과")
        check(all(v.get("flagged") == bool(v.get("keywords")) for v in news_stocks.values()),
              "flagged == 키워드 유무", "flagged 와 keywords 불일치")
        urls = [i.get("url") for v in news_stocks.values() for i in (v.get("items") or [])]
        check(all(u.startswith("http") for u in urls), f"뉴스 링크 {len(urls)}건 http 형식",
              "뉴스 링크 형식 이상")
        check(set(inv_stocks) == set(news_stocks) or not inv_stocks,
              "수급·뉴스 수집 종목 일치",
              f"수급 {len(inv_stocks)} vs 뉴스 {len(news_stocks)} 종목 다름")

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
