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
  · charts(charts.json) stocks 는 [시,고,저,종] 4개만 (용량 규칙)
  · data.json 에는 charts 가 없고 charts.json 에 따로 있는지(분리 규칙)
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
CHARTS_PATH = ROOT / "charts.json"
FCHART = "https://fchart.stock.naver.com/sise.nhn"
UA = ("Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36")
HEADERS = {"User-Agent": UA, "Referer": "https://m.stock.naver.com/"}

RULE = "A and (B or C) and D and E"
MIN_VALUE = 100
PM_WAIT_STATES = ("오전장 진행 중", "오후장 초반", "휴장")   # 판정 전(대기)
PM_MISS_STATE = "분봉 미측정"                                  # 분봉 한도·실패

fails: list[str] = []
passes: list[str] = []
notes: list[str] = []


def ok(msg: str) -> None:
    passes.append(msg)
    print(f"  ✓ {msg}")


def warn(msg: str) -> None:
    """고치기 전에 알아야 할 상태 — 실패는 아니지만 통과로 덮지 않는다."""
    notes.append(msg)
    print(f"  △ {msg}")


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
    if s.get("sortBy") == "score":
        # 점수 조건식 — 점수 내림차순 (같으면 거래대금 내림차순)
        keys = [(-(h.get("score") or 0), -(h.get("value_eok") or 0)) for h in hits]
        check(keys == sorted(keys), f"[{name}] {len(hits)}종목 점수 내림차순",
              f"[{name}] 점수 정렬 안 됨: {[h.get('score') for h in hits]}")
    else:
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
        # 오후장 수급(D)처럼 시각이 되기 전에는 판정하지 않는 조건은 '대기'로 통과 처리한다
        pending = bool(h.get("pending"))
        req_use = [k for k in req if not (pending and k == "D")]
        check(all(cnd.get(k) for k in req_use), f"[{name}] {h.get('name')}: {'·'.join(req_use)} 충족",
              f"[{name}] {h.get('name')}: {'·'.join(req_use)} 미충족 {cnd}")
        if pending:
            check(cnd.get("D") is False,
                  f"[{name}] {h.get('name')}: 오후장 대기(D는 미판정)",
                  f"[{name}] {h.get('name')}: 대기인데 D가 참 {cnd}")
        if grp:
            check(any(cnd.get(k) for k in grp), f"[{name}] {h.get('name')}: {' 또는 '.join(grp)} 충족",
                  f"[{name}] {h.get('name')}: {'·'.join(grp)} 모두 미충족 {cnd}")


def check_edge_item(s: dict, item: dict) -> None:
    """종가베팅 핵심 항목의 새 지표(52주·매물대·오후장) — 값의 앞뒤가 맞는지."""
    name = s.get("name") or "?"
    nm = item.get("name")
    w = item.get("w52")
    sh = item.get("shelf")
    pm = item.get("pm")
    if w:
        ok_gap = isinstance(w.get("gap"), (int, float)) and -100 <= w["gap"] <= 60
        check(ok_gap, f"[{name}] {nm}: 52주 이격 {w.get('gap')}%", f"[{name}] {nm}: 52주 이격 이상 {w}")
        check((w.get("high") or 0) > 0 and bool(w.get("highDate")),
              f"[{name}] {nm}: 52주 최고 {w.get('high')} · {w.get('highDate')}",
              f"[{name}] {nm}: 52주 최고값 이상")
        state_ok = (w.get("gap") <= -10 and not w.get("state")) or \
                   (w.get("gap") > -10 and bool(w.get("state")))
        check(state_ok, f"[{name}] {nm}: 52주 상태 '{w.get('state')}' 판정 일치",
              f"[{name}] {nm}: 52주 상태 불일치 {w.get('gap')}% / '{w.get('state')}'")
    if sh:
        check(sh.get("overHigh") in (True, False) and (sh.get("high") or 0) > 0,
              f"[{name}] {nm}: 매물대 {sh.get('date')} 고가 {sh.get('high')} · 소화 {sh.get('overHigh')}",
              f"[{name}] {nm}: 매물대 수치 이상 {sh}")
        check((sh.get("state") == "매물대 소화") == bool(sh.get("overHigh")),
              f"[{name}] {nm}: 매물대 소화 판정 일치",
              f"[{name}] {nm}: 매물대 상태 불일치 {sh.get('state')} / {sh.get('overHigh')}")
    if pm:
        st = str(pm.get("status") or "")
        check(bool(st), f"[{name}] {nm}: 오후장 상태 '{st}'", f"[{name}] {nm}: 오후장 상태 없음")
        if pm.get("pass") is None:
            if st == PM_MISS_STATE:
                # 분봉을 못 받은 종목 — 대기(판정 전)와 다르게 다룬다. 실패는 아니지만 기록한다.
                warn(f"[{name}] {nm}: 오후장 {PM_MISS_STATE} — {pm.get('basis') or '사유 없음'}")
            else:
                check(st in PM_WAIT_STATES,
                      f"[{name}] {nm}: 미판정 상태 '{st}' (오후장 실측 아님)",
                      f"[{name}] {nm}: 미판정인데 상태가 '{st}'")
            check("pmShare" not in pm, f"[{name}] {nm}: 대기 상태에 수치 없음",
                  f"[{name}] {nm}: 대기인데 오후 수치가 있음 {pm}")
        else:
            share = pm.get("pmShare")
            chg = pm.get("chgPm")
            check(isinstance(share, (int, float)) and 0 <= share <= 100,
                  f"[{name}] {nm}: 오후 비중 {share}%", f"[{name}] {nm}: 오후 비중 이상 {share}")
            check(isinstance(chg, (int, float)) and -35 <= chg <= 35,
                  f"[{name}] {nm}: 13:00 대비 {chg}%", f"[{name}] {nm}: 13:00 대비 이상 {chg}")
            check(bool(pm.get("pass")) == (share >= 30 and chg > 0),
                  f"[{name}] {nm}: 오후장 유입·우상향 판정 일치 ({share}% · {chg}%)",
                  f"[{name}] {nm}: 오후장 판정 불일치 {pm}")
    else:
        bad(f"[{name}] {nm}: 오후장 수급 기록 없음")


SCORE_CAPS = {"lead": 40, "trend": 25, "win": 25, "flow": 10}
SCORE_MIN = 51   # 51점 초과만 목록에 올라온다(2026-11-27 개편)


def check_score_item(s: dict, item: dict) -> None:
    """주도돌파 100점 항목 — 배점 합계·범위·D+1 승률 표기가 앞뒤가 맞는지."""
    name = s.get("name") or "?"
    nm = item.get("name")
    score = item.get("score")
    parts = item.get("scoreParts") or {}
    ok_score = isinstance(score, int) and 0 <= score <= 100
    check(ok_score, f"[{name}] {nm}: {score}점/100", f"[{name}] {nm}: 점수 범위 이상 {score}")
    if parts:
        bad_keys = [k for k in parts if k not in SCORE_CAPS]
        over = [k for k, cap in SCORE_CAPS.items() if (parts.get(k) or 0) > cap or (parts.get(k) or 0) < 0]
        check(not bad_keys and not over, f"[{name}] {nm}: 배점 4항목이 상한 안 ({parts})",
              f"[{name}] {nm}: 배점 이상 keys={bad_keys} over={over} {parts}")
        total = sum(int(parts.get(k) or 0) for k in SCORE_CAPS)
        check(total == score, f"[{name}] {nm}: 배점 합 {total} == 점수 {score}",
              f"[{name}] {nm}: 배점 합 {total} != 점수 {score}")
    else:
        bad(f"[{name}] {nm}: scoreParts 없음")
    wr = str(item.get("winRate") or "")
    ok_wr = (wr == "표본 없음") or bool(re.fullmatch(r"\d+(\.\d+)?% \(\d+/\d+\)", wr))
    check(ok_wr, f"[{name}] {nm}: D+1 승률 표기 '{wr}'", f"[{name}] {nm}: 승률 표기 이상 '{wr}'")
    check(re.fullmatch(r"[+-]\d+\.\d{2}%", str(item.get("avgD1") or "")) is not None
          or item.get("avgD1") == "—",
          f"[{name}] {nm}: 평균 수익률 표기 '{item.get('avgD1')}'",
          f"[{name}] {nm}: 평균 수익률 표기 이상 '{item.get('avgD1')}'")
    check(bool(item.get("scoreDetail")) and bool(item.get("winRule")),
          f"[{name}] {nm}: 배점 요약·표본 기준 있음",
          f"[{name}] {nm}: 배점 요약·표본 기준 없음")
    check((item.get("value_eok") or 0) >= (s.get("minValue") or 0),
          f"[{name}] {nm}: 거래대금 {item.get('value_eok')}억 ≥ 기준",
          f"[{name}] {nm}: 거래대금 미달 {item.get('value_eok')}억")


def recompute_d1(rows) -> dict:
    """D+1 승률 독립 재계산 — 정배열 +5%↑ → +3%↑ → 정배열 순으로 표본 3건 이상 기준."""
    c = [r["c"] for r in rows]
    n = len(c)
    start = max(60, n - 121)

    def count(strong):
        sig = 0
        up = 0
        tot = 0.0
        for i in range(start, n - 1):
            ma20 = sum(c[i - 19:i + 1]) / 20
            ma60 = sum(c[i - 59:i + 1]) / 60
            if not (c[i] > ma20 > ma60):
                continue
            if strong is not None and (c[i] / c[i - 1] - 1) * 100 < strong:
                continue
            g = (c[i + 1] / c[i] - 1) * 100
            sig += 1
            tot += g
            if g > 0:
                up += 1
        return sig, up, (round(tot / sig, 2) if sig else None)

    for strong in (5.0, 3.0, None):
        sig, up, avg = count(strong)
        if sig >= 3 or strong is None:
            return {"n": sig, "m": up, "avg": avg,
                    "rule": ("정배열 +5%↑" if strong == 5.0 else
                             ("정배열 +3%↑" if strong == 3.0 else "정배열 상승일"))}
    return {"n": 0, "m": 0, "avg": None, "rule": "표본 없음"}


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


def load_charts() -> dict:
    """charts.json — {날짜: charts}. data.json 에서 분리한 일봉(네이버 금융) 본문."""
    if not CHARTS_PATH.exists():
        print("  ! charts.json 이 없습니다 — 일봉 분리가 안 된 저장소입니다")
        return {}
    try:
        raw = json.loads(CHARTS_PATH.read_text(encoding="utf-8"))
    except Exception as exc:                  # noqa: BLE001
        print(f"  ! charts.json 파싱 실패({type(exc).__name__})")
        return {}
    return raw if isinstance(raw, dict) else {}


def main(argv) -> int:
    live = "--live" in argv
    data = json.loads(DATA_PATH.read_text(encoding="utf-8"))
    entry = data[0]
    charts_by_date = load_charts()
    print(f"[verify_scan] {entry.get('date')} · {DATA_PATH.stat().st_size / 1024:.0f}KB")
    if not load_scan(entry):
        print("  · data.json 에 풀 수 있는 조건식 기록이 없습니다.")
        return 1
    meta = entry.get("conditionScan") or {}
    hits = entry.get("conditionHits") or []
    rx = entry.get("chartReactions") or {}

    check(bool(meta), "conditionScan 있음", "conditionScan 없음")
    check(isinstance(entry.get("conditionHits"), list),
          f"conditionHits {len(hits)}종목", "conditionHits 없음")
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

    # ── 종가베팅 핵심 — 52주 신고가·앞전 매물대·오후장 수급 (2026-11-24 추가) ──
    edge = next((s for s in scanners if s.get("id") == "closing-edge"), None)
    check(bool(edge), "종가베팅 핵심 조건식 있음", "종가베팅 핵심 조건식 없음")
    if edge:
        check(edge.get("formula") == "(A or B) and C and D",
              "종가베팅 수식 (A or B) and C and D", f"수식 다름 {edge.get('formula')}")
        check(edge.get("minValue") == 300, "종가베팅 교집합 300억",
              f"교집합 다름 {edge.get('minValue')}")
        check(len(edge.get("rules") or []) == 4, "종가베팅 필터 기준 4개(A~D)",
              f"필터 기준 개수 다름 {len(edge.get('rules') or [])}")
        check(bool(edge.get("phase")), f"오후장 수급 단계 '{edge.get('phase')}'", "오후장 단계 없음")
        check(isinstance(edge.get("pmMeasured"), int), "오후장 분봉 조회 수 기록",
              "pmMeasured 없음")
        phase = str(edge.get("phase") or "")
        judged = phase not in PM_WAIT_STATES          # 13:30 이후·마감 — D를 판정했어야 하는 시각
        edge_hits = list(edge.get("hits") or [])
        if judged:
            # 2026-11-27 버그 회귀 검사: 다 지난 시각인데 '대기(pending)'로 남은 항목은 없어야 한다
            stuck = [h.get("name") for h in edge_hits if h.get("pending")]
            check(not stuck,
                  f"[{edge.get('name')}] '{phase}' 판정 단계 — 대기(pending) 항목 없음",
                  f"[{edge.get('name')}] '{phase}'인데 대기로 남은 종목 {len(stuck)}건 {stuck[:5]}")
            no_pass = [h.get("name") for h in edge_hits
                       if (h.get("pm") or {}).get("pass") is not True]
            check(not no_pass,
                  f"[{edge.get('name')}] 포착 {len(edge_hits)}종목 모두 오후장(D) 통과",
                  f"[{edge.get('name')}] 오후장(D) 미통과·미측정 항목 {len(no_pass)}건 {no_pass[:5]}")
            if edge.get("pmMissed"):
                warn(f"[{edge.get('name')}] 분봉을 못 받아 판정 못 한 목록 항목 "
                     f"{edge.get('pmMissed')}건 (조회 {edge.get('pmMeasured')}종목)")
            if edge.get("pmDropped"):
                warn(f"[{edge.get('name')}] 오후장 분봉 한도로 판정 못 한 후보 "
                     f"{edge.get('pmDropped')}종목 — 목록에서 빠졌습니다")
        edge_items = edge_hits + list((edge.get("reactions") or {}).values())
        for item in edge_items:
            check_edge_item(edge, item)
        # 관찰·카드 종목(모달용)도 다른 조건식 항목에 52주·오후장 기록이 붙었는지
        # · 화면(scanOf)은 조건식 순서대로 찾아 **먼저 만난 기록**을 쓴다 — 여기서도 같은
        #   순서로만 채워, 뒤 조건식의 얇은 기록이 앞의 52주·pm 기록을 덮지 않게 한다
        rx_all = {}
        for s in scanners:
            for code, item in (s.get("reactions") or {}).items():
                rx_all.setdefault(code, item)
        with52 = sum(1 for v in rx_all.values() if v.get("w52"))
        withpm = sum(1 for v in rx_all.values() if v.get("pm"))
        check(with52 > 0, f"모달용 종목 {with52}건에 52주 지표 기록", "52주 지표가 붙은 모달 항목 없음")
        check(withpm > 0, f"모달용 종목 {withpm}건에 오후장 기록", "오후장 기록이 붙은 모달 항목 없음")

    # ── 주도돌파 100점 — 승률·기대수익 100점 채점 (2026-11-27 추가) ──
    score_sc = next((s for s in scanners if s.get("id") == "breakout-100"), None)
    check(bool(score_sc), "주도돌파 100점 조건식 있음", "주도돌파 100점 조건식 없음")
    if score_sc:
        check(score_sc.get("formula") == "A and B and C",
              "주도돌파 수식 A and B and C", f"수식 다름 {score_sc.get('formula')}")
        check(score_sc.get("minValue") == 300, "주도돌파 교집합 300억",
              f"교집합 다름 {score_sc.get('minValue')}")
        check(score_sc.get("sortBy") == "score", "주도돌파 정렬 기준 score",
              f"정렬 기준 다름 {score_sc.get('sortBy')}")
        check(score_sc.get("limit") == 15, "주도돌파 상위 15종목",
              f"상한 다름 {score_sc.get('limit')}")
        check(len(score_sc.get("rules") or []) == 3, "주도돌파 필터 기준 3개(A~C)",
              f"필터 기준 개수 다름 {len(score_sc.get('rules') or [])}")
        sc_hits = score_sc.get("hits") or []
        check(0 < len(sc_hits) <= 15, f"주도돌파 {len(sc_hits)}종목 포착(15 이하)",
              f"주도돌파 포착 수 이상 {len(sc_hits)}")
        check((score_sc.get("passedTotal") or 0) >= len(sc_hits),
              f"주도돌파 조건 통과 {score_sc.get('passedTotal')}종목 ≥ 표시 {len(sc_hits)}",
              f"passedTotal {score_sc.get('passedTotal')} < 표시 {len(sc_hits)}")
        for item in sc_hits:
            check_score_item(score_sc, item)
            check(int(item.get("score") or 0) > SCORE_MIN,
                  f"[주도돌파] {item.get('name')}: {item.get('score')}점 > {SCORE_MIN}점",
                  f"[주도돌파] {item.get('name')}: {item.get('score')}점 — {SCORE_MIN}점 초과 필터 위반")
            check(all((item.get("conditions") or {}).get(k) for k in ("A", "B", "C")),
                  f"[주도돌파] {item.get('name')}: A·B·C 충족",
                  f"[주도돌파] {item.get('name')}: A·B·C 미충족 {item.get('conditions')}")

    # ── 급등후 눌림목 — 강의 노트 '눌림 매매' 재현 (2026-11-28 추가 · 같은 날 단기 정배열 E 추가) ──
    pb = next((s for s in scanners if s.get("id") == "pullback"), None)
    check(bool(pb), "급등후 눌림목 조건식 있음", "급등후 눌림목 조건식 없음")
    if pb:
        check(pb.get("formula") == "A and B and C and D and E",
              "급등후 눌림목 수식 A and B and C and D and E", f"수식 다름 {pb.get('formula')}")
        check(pb.get("rawFormula") == "A and B and C and D and E",
              "급등후 눌림목 원본 수식에 정배열 E 포함", f"원본 수식 다름 {pb.get('rawFormula')}")
        check(pb.get("minValue") == 100, "급등후 눌림목 교집합 100억",
              f"교집합 다름 {pb.get('minValue')}")
        pb_rules = pb.get("rules") or []
        check(len(pb_rules) == 5, "급등후 눌림목 필터 기준 5개(A~E)",
              f"필터 기준 개수 다름 {len(pb_rules)}")
        check([r.get("key") for r in pb_rules] == ["A", "B", "C", "D", "E"],
              "급등후 눌림목 필터 키 A~E 순서",
              f"필터 키 이상 {[r.get('key') for r in pb_rules]}")
        check(any("정배열" in str(r.get("label", "")) for r in pb_rules),
              "급등후 눌림목 필터에 '단기 이평 정배열' 표시",
              "급등후 눌림목 필터에 정배열 기준 없음")
        check("정배열" in str(pb.get("summary") or ""),
              "급등후 눌림목 설명문에 정배열 포함",
              f"설명문에 정배열 없음: {pb.get('summary')}")
        check(bool(pb.get("summary")) and bool(pb.get("rawNote")),
              "급등후 눌림목 설명·주의 문구 있음", "급등후 눌림목 설명 없음")
        pb_hits = pb.get("hits") or []
        for item in pb_hits:
            nm = item.get("name")
            cnd = item.get("conditions") or {}
            check(all(cnd.get(k) for k in ("A", "B", "C", "D", "E")),
                  f"[급등후 눌림목] {nm}: A·B·C·D·E 충족",
                  f"[급등후 눌림목] {nm}: A·B·C·D·E 미충족 {cnd}")
            drop = (item.get("pullback") or {}).get("pct")
            check(isinstance(drop, (int, float)) and -11.0 <= drop <= -4.0,
                  f"[급등후 눌림목] {nm}: 고점 대비 {drop}% (-4~-11)",
                  f"[급등후 눌림목] {nm}: 눌림 폭 이상 {drop}")
            surge = item.get("surge") or {}
            check(bool(surge.get("date")) and 2 <= int(surge.get("daysAgo") or 0) <= 7
                  and (surge.get("pct") or 0) >= 10.0,
                  f"[급등후 눌림목] {nm}: 급등 {surge.get('date')} {surge.get('pct')}% "
                  f"({surge.get('daysAgo')}거래일 전)",
                  f"[급등후 눌림목] {nm}: 급등일 정보 이상 {surge}")
            check(0 < (item.get("volRatio") or 1) < 1,
                  f"[급등후 눌림목] {nm}: 거래량 비율 {item.get('volRatio')} (전일보다 감소)",
                  f"[급등후 눌림목] {nm}: 거래량이 줄지 않음 {item.get('volRatio')}")
            check((item.get("ma20dist") or 0) >= -3.0,
                  f"[급등후 눌림목] {nm}: 20일선 이격 {item.get('ma20dist')}% (3% 이내)",
                  f"[급등후 눌림목] {nm}: 20일선 이탈 {item.get('ma20dist')}%")
            # ── 단기 이평 정배열·이격도 — 숫자가 있어야 화면 칩·모달이 확인된다
            g = {k: item.get(k) for k in ("ma5GapPct", "ma10GapPct", "ma20GapPct",
                                          "ma5_20SpreadPct")}
            ok_nums = all(isinstance(v, (int, float)) for v in g.values())
            check(ok_nums, f"[급등후 눌림목] {nm}: 이격도 4개 값 있음 {g}",
                  f"[급등후 눌림목] {nm}: 이격도 값 이상 {g}")
            if ok_nums:
                check(g["ma5GapPct"] < g["ma10GapPct"] < g["ma20GapPct"],
                      f"[급등후 눌림목] {nm}: 이격 5일 {g['ma5GapPct']}% < 10일 "
                      f"{g['ma10GapPct']}% < 20일 {g['ma20GapPct']}% (정배열)",
                      f"[급등후 눌림목] {nm}: 이격 순서가 정배열과 다름 {g}")
                check(g["ma5_20SpreadPct"] > 0,
                      f"[급등후 눌림목] {nm}: 5·20 벌어짐 {g['ma5_20SpreadPct']}% (플러스)",
                      f"[급등후 눌림목] {nm}: 5·20 벌어짐 {g['ma5_20SpreadPct']}% (정배열 아님)")
                check(bool(item.get("maOverheat")) == (g["ma20GapPct"] >= 25.0),
                      f"[급등후 눌림목] {nm}: 이격과열 표시 {'있음' if item.get('maOverheat') else '없음'}"
                      f" (20일선 {g['ma20GapPct']}%)",
                      f"[급등후 눌림목] {nm}: 이격과열 표시와 이격도 불일치 "
                      f"{item.get('maOverheat')} / {g['ma20GapPct']}%")
            check(item.get("maAlign") is True,
                  f"[급등후 눌림목] {nm}: maAlign 참", f"[급등후 눌림목] {nm}: maAlign {item.get('maAlign')}")
            wr = str(item.get("winRate") or "")
            check(wr == "표본 없음" or re.fullmatch(r"\d+(\.\d+)?% \(\d+/\d+\)", wr) is not None,
                  f"[급등후 눌림목] {nm}: D+1 승률 '{wr}'", f"[급등후 눌림목] {nm}: 승률 표기 이상 '{wr}'")
            line2 = str(item.get("line2") or "")
            check(bool(line2), f"[급등후 눌림목] {nm}: 한 줄 요약 있음",
                  f"[급등후 눌림목] {nm}: 한 줄 요약 없음")
            check("고점" in line2 and "급등" in line2,
                  f"[급등후 눌림목] {nm}: 요약에 고점·급등 표시",
                  f"[급등후 눌림목] {nm}: 요약에 고점·급등 없음 '{line2}'")

    charts = entry.get("charts") or charts_by_date.get(str(entry.get("date"))) or {}
    check("charts" not in entry or not entry.get("charts"),
          "data.json 에 charts 없음 (charts.json 분리)",
          "data.json 에 charts 가 남아 있음 — 분리되지 않음")
    check(bool(charts), "charts.json 일봉 있음", "charts.json 에 차트 없음")
    stocks = charts.get("stocks") or {}
    four = sum(1 for bars in stocks.values() if bars and len(bars[0]) == 4)
    check(bool(stocks) and four == len(stocks), f"charts.stocks {four}종목 모두 [o,h,l,c] 4개",
          f"charts.stocks 형식 위반 {len(stocks) - four}종목")

    # 📈 차트 탭 거래량·RS — 종목 수와 봉 수가 OHLC와 같은지(빠진 종목은 거래량만 안 그린다)
    days = int(charts.get("days") or 0)
    vols = charts.get("vols") or {}
    if vols:
        bad = [c for c, v in vols.items()
               if c not in stocks or len(v) != days or not all(isinstance(x, int) and x >= 0 for x in v)]
        check(not bad, f"charts.vols {len(vols)}종목 · 거래량 {days}봉 정수",
              f"charts.vols 형식 위반 {len(bad)}종목(예: {bad[:3]})")
        check(int(charts.get("volUnit") or 0) == 1000, "거래량 단위 천주(volUnit=1000)",
              f"volUnit={charts.get('volUnit')}")
    else:
        warn_only = "charts.vols 없음 — 용량 여유가 생기면 채워집니다"
        check(True, warn_only, "")
    idx = charts.get("index") or {}
    for sym in ("KOSPI", "KOSDAQ"):
        block = idx.get(sym) or {}
        series = block.get("c") or []
        if not series:
            continue
        check(len(series) == days, f"{block.get('name', sym)} 지수 {days}봉(RS 기준)",
              f"{sym} 지수 봉 수 {len(series)} != {days}")
        real = [v for v in series if isinstance(v, (int, float)) and v > 0]
        check(len(real) >= days * 0.5, f"{block.get('name', sym)} 지수 유효값 {len(real)}봉",
              f"{sym} 지수 유효값 부족 {len(real)}/{days}")

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
    check(size_kb < 1200, f"data.json {size_kb:.0f}KB (차트 분리로 1,200KB 미만)",
          f"data.json 비대 {size_kb:.0f}KB")
    if CHARTS_PATH.exists():
        charts_kb = CHARTS_PATH.stat().st_size / 1024
        check(charts_kb < 3000, f"charts.json {charts_kb:.0f}KB (3,000KB 미만)",
              f"charts.json 비대 {charts_kb:.0f}KB")

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

        # 52주 신고가·매물대 — 260거래일 일봉으로 다시 계산해 대조
        if edge:
            items = list(edge.get("hits") or []) + list((edge.get("reactions") or {}).values())
            need = [it.get("code") for it in items if it.get("w52") or it.get("shelf")]
            with ThreadPoolExecutor(max_workers=8) as pool:
                deep = dict(pool.map(lambda c: (c, fetch_bars(c, 260)), need))
            for it in items:
                rows = deep.get(it.get("code"))
                if not rows or len(rows) < 122:
                    continue
                price = it.get("price") or rows[-1]["c"]
                hi = max(r["h"] for r in rows[-251:-1])
                gap = (price / hi - 1) * 100
                got = (it.get("w52") or {}).get("gap")
                if got is None:
                    continue
                check(abs(gap - got) < 0.2,
                      f"{it.get('name')}: 52주 이격 재계산 {gap:+.2f}% vs {got}%",
                      f"{it.get('name')}: 52주 이격 불일치 {gap:+.2f}% vs {got}%")
                win = rows[-61:-1]
                shelf = max(win, key=lambda x: x["v"])
                sh = it.get("shelf") or {}
                if sh:
                    check(sh.get("date") == shelf["d"] and sh.get("high") == shelf["h"],
                          f"{it.get('name')}: 매물대 {shelf['d']} 고가 {shelf['h']} 일치",
                          f"{it.get('name')}: 매물대 불일치 {sh.get('date')}/{sh.get('high')} vs "
                          f"{shelf['d']}/{shelf['h']}")

        # 주도돌파 100점 — D+1 승률·기대수익을 260거래일 일봉으로 다시 계산해 대조
        if score_sc:
            codes_score = [h.get("code") for h in (score_sc.get("hits") or [])]
            with ThreadPoolExecutor(max_workers=8) as pool:
                bars_deep = dict(pool.map(lambda c: (c, fetch_bars(c, 260)), codes_score))
            for h in score_sc.get("hits") or []:
                rows = bars_deep.get(h.get("code"))
                if not rows or len(rows) < 122:
                    bad(f"[주도돌파] {h.get('name')}: 일봉을 받지 못해 대조 불가")
                    continue
                r = recompute_d1(rows)
                same_n = r["n"] == (h.get("winN") or 0)
                same_m = r["m"] == (h.get("winM") or 0)
                check(same_n and same_m,
                      f"[주도돌파] {h.get('name')}: D+1 {r['m']}/{r['n']}회 일치 ({r['rule']})",
                      f"[주도돌파] {h.get('name')}: D+1 불일치 재계산 {r['m']}/{r['n']} vs "
                      f"{h.get('winM')}/{h.get('winN')}")
                got = h.get("avgD1")
                if r["avg"] is not None and got not in (None, "—"):
                    try:
                        near = abs(float(str(got).replace("%", "").replace("+", "")) - r["avg"]) < 0.06
                    except ValueError:
                        near = False
                    check(near, f"[주도돌파] {h.get('name')}: 평균 {r['avg']:+.2f}% vs {got}",
                          f"[주도돌파] {h.get('name')}: 평균 불일치 {r['avg']:+.2f}% vs {got}")

    print(f"\n결과: 통과 {len(passes)} · 실패 {len(fails)}" +
          (f" · 확인 {len(notes)}" if notes else ""))
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
