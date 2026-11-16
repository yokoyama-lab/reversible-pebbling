"""可逆 Busy Beaver エンジン（候補5）。

対象: 2記号・両側無限テープ・ブランク 0 の 1 テープ Turing 機械。
二つの流儀を扱う。

- **五つ組（quintuple, 通常の BB と同じ形式）**
  規則 (q, a) -> (q', b, d)。1ステップで「読む・書く・移動」。
  *配置レベルの可逆性*の条件は「遷移関係が三つ組として単射」ではない。
  移動してしまうと直前のマスに何を書いたかを頭が見ていないため、逆向き決定性には
  次が必要十分である（Morita, および bbchallenge wiki と同じ条件）:

      ある状態 q' に入る全ての規則について
        (i) 移動方向 d が全て同じ         … 直前の頭位置が一意に決まる
        (ii) 書き込む記号 b が互いに異なる … どの規則が発火したかが読み取れる

  単なる三つ組の単射性は (i) を要求しないので配置レベルの可逆性より弱く、
  「可逆」と呼んではいけない。本モジュールは上の条件を採用する。

- **四つ組（quadruple, Morita 流）**
  規則は「書き込み型 [q, a, b, q']（読んで書く・移動しない）」と
  「移動型 [q, /, d, q']（読み書きせず移動）」の二種。1状態はどちらか一方の型のみ
  （前向き決定性）。可逆性は同じ右状態 q' に入る規則が
  すべて同型で、書き込み型なら b が互いに異なる／移動型なら d が互いに異なること。

停止判定に可逆性を使う（idea05 §3.3）:
配置遷移が単射なら、配置が再訪されるならその軌道は初期配置を含む純粋な巡回である。
よって「初期配置に戻ったか」だけで巡回型は判定でき、残るのは並進型である。
並進型は「頭位置を原点に揃えた配置の指紋」の再訪で厳密に検出する
（テープはブランク以外が有限台なので、力学は並進不変）。
"""

from __future__ import annotations

L, R = -1, 1
HALT = -1  # 停止状態 Z


# ---------------------------------------------------------------- 五つ組

def quintuple_reversible(rules: dict) -> bool:
    """rules: (q, a) -> (q', b, d)。配置レベルの可逆性条件を満たすか。"""
    incoming: dict[int, list[tuple[int, int]]] = {}
    for (_q, _a), (q2, b, d) in rules.items():
        incoming.setdefault(q2, []).append((b, d))
    for q2, arrivals in incoming.items():
        if len({d for _b, d in arrivals}) > 1:
            return False
        if len({b for b, _d in arrivals}) != len(arrivals):
            return False
    return True


def _quintuple_rule_ok(rules: dict, q2: int, b: int, d: int) -> bool:
    """規則 (…)->(q2, b, d) を追加しても可逆性を保てるか（増分判定）。"""
    for (_q, _a), (r2, rb, rd) in rules.items():
        if r2 == q2:
            if rd != d or rb == b:
                return False
    return True


class TranslatedCyclerDetector:
    """並進型非停止機械の厳密な検出器。

    右側の「記録更新時刻」（頭が過去最右セルを越えた時刻）だけを比較する。
    時刻 $t_1<t_2$ の記録更新で
      - 状態が等しい、
      - $\\Delta = h_2 - h_1 > 0$、
      - $m$ = 区間 $[t_1,t_2]$ での頭位置の最小値、
      - 時刻 $t_1$ のテープの $[m, h_1]$ が、時刻 $t_2$ のテープの $[m+\\Delta, h_2]$ と
        $\\Delta$ だけずらして一致する
    が成り立つなら、機械は永久に $\\Delta$ ずつ並進しながら同じ挙動を繰り返す
    （記録更新の定義より $h_i$ より右は両時刻でブランクであり、区間内で頭は $m$ より
    左に出ないので、$[m,h_1]$ の外側の内容は次の周回に影響しない）。
    左側も鏡映して同様に判定する。
    """

    __slots__ = ("recs", "cap")

    def __init__(self, cap=600):
        # side -> state -> list of [head, minhead_since, frozenset(1 のある位置)]
        self.recs = ({}, {})
        self.cap = cap

    def observe(self, side, q, head, tape):
        """side: 0=右記録, 1=左記録。並進型と判定できれば True。"""
        table = self.recs[side].setdefault(q, [])
        ones = frozenset(p for p, v in tape.items() if v)
        for rec in table:
            h1, m, snap = rec
            delta = head - h1
            if side == 0:
                if delta <= 0:
                    continue
                a = frozenset(p + delta for p in snap if p >= m)
                b = frozenset(p for p in ones if p >= m + delta)
            else:
                if delta >= 0:
                    continue
                a = frozenset(p + delta for p in snap if p <= m)
                b = frozenset(p for p in ones if p <= m + delta)
            if a == b:
                return True
        if len(table) < self.cap:
            table.append([head, head, ones])
        return False

    def step(self, head):
        for side in (0, 1):
            for table in self.recs[side].values():
                for rec in table:
                    if side == 0:
                        if head < rec[1]:
                            rec[1] = head
                    else:
                        if head > rec[1]:
                            rec[1] = head


def run_quintuple(rules, max_steps, k=None, blank_halt=True):
    """空テープから走らせる。戻り値は dict。

    status: 'halt' | 'nonhalt_cycle' | 'nonhalt_translated' | 'undefined' | 'undecided'
    'undefined' は未定義遷移に到達（TNF 枚挙では分岐点）。
    """
    tape: dict[int, int] = {}
    head = 0
    q = 0
    steps = 0
    seen: dict[tuple, tuple[int, int]] = {}  # 指紋 -> (時刻, 頭位置)
    init_sig = None
    det = TranslatedCyclerDetector()
    rmax = lmin = 0
    has_halt = any(t[0] == HALT for t in rules.values())
    while True:
        ones = sum(1 for v in tape.values() if v)
        sig = (q, frozenset(p - head for p, v in tape.items() if v))
        if init_sig is None:
            init_sig = sig
        if sig in seen:
            t0, h0 = seen[sig]
            offset = head - h0
            kind = "nonhalt_cycle" if offset == 0 else "nonhalt_translated"
            return {"status": kind, "steps": steps, "ones": ones,
                    "period_start": t0, "offset": offset,
                    "returned_to_initial": sig == init_sig}
        seen[sig] = (steps, head)
        a = tape.get(head, 0)
        if (q, a) not in rules:
            return {"status": "undefined", "steps": steps, "ones": ones,
                    "state": q, "symbol": a}
        q2, b, d = rules[(q, a)]
        if b:
            tape[head] = b
        else:
            tape.pop(head, None)
        steps += 1
        if q2 == HALT:
            return {"status": "halt", "steps": steps,
                    "ones": sum(1 for v in tape.values() if v)}
        head += d
        q = q2
        det.step(head)
        if head > rmax:
            rmax = head
            if det.observe(0, q, head, tape):
                return {"status": "nonhalt_translated", "steps": steps,
                        "ones": sum(1 for v in tape.values() if v),
                        "via": "right_record"}
        elif head < lmin:
            lmin = head
            if det.observe(1, q, head, tape):
                return {"status": "nonhalt_translated", "steps": steps,
                        "ones": sum(1 for v in tape.values() if v),
                        "via": "left_record"}
        if steps >= max_steps:
            # 停止規則を1本も持たない機械は原理的に停止しない（自明な証書）。
            if not has_halt:
                return {"status": "nonhalt_no_halt_rule", "steps": steps,
                        "ones": sum(1 for v in tape.values() if v)}
            return {"status": "undecided", "steps": steps,
                    "ones": sum(1 for v in tape.values() if v)}


def enumerate_quintuple(k, max_steps, reversible=True, on_halt=None,
                        collect_undecided=False):
    """k 状態・2記号の TNF 枚挙。

    Tree Normal Form: 空テープから走らせ、未定義遷移に達したらそこで分岐する。
    新しい状態は「未使用のうち最小番号」のみを許すことで状態の名前替え対称性を除去し、
    (A,0) の移動方向を R に固定して左右鏡映対称性を除去する。
    未定義遷移に達した機械は「そこで停止する」1台としても数える（標準 BB の流儀。
    停止規則は 1 を書くと Σ が最大になるので b=1, d=R を採る）。

    戻り値: 統計 dict。
    """
    stats = {"machines": 0, "halt": 0, "nonhalt_cycle": 0,
             "nonhalt_translated": 0, "nonhalt_no_halt_rule": 0,
             "undecided": 0,
             "best_steps": 0, "best_steps_machine": None,
             "best_ones": 0, "best_ones_machine": None,
             "cycle_not_initial": 0, "undecided_machines": []}

    def record(rules, res):
        stats["machines"] += 1
        st = res["status"]
        if st == "halt":
            stats["halt"] += 1
            if res["steps"] > stats["best_steps"]:
                stats["best_steps"] = res["steps"]
                stats["best_steps_machine"] = format_quintuple(rules, k)
            if res["ones"] > stats["best_ones"]:
                stats["best_ones"] = res["ones"]
                stats["best_ones_machine"] = format_quintuple(rules, k)
            if on_halt:
                on_halt(rules, res)
        elif st == "nonhalt_cycle":
            stats["nonhalt_cycle"] += 1
            if not res["returned_to_initial"]:
                stats["cycle_not_initial"] += 1
        elif st == "nonhalt_translated":
            stats["nonhalt_translated"] += 1
        elif st == "nonhalt_no_halt_rule":
            stats["nonhalt_no_halt_rule"] += 1
        else:
            stats["undecided"] += 1
            if collect_undecided:
                stats["undecided_machines"].append(format_quintuple(rules, k))

    def branch(rules, nstates):
        res = run_quintuple(rules, max_steps)
        if res["status"] != "undefined":
            record(rules, res)
            return
        q, a = res["state"], res["symbol"]
        # (1) ここで停止する機械
        if _quintuple_rule_ok(rules, HALT, 1, R) or not reversible:
            rules[(q, a)] = (HALT, 1, R)
            record(rules, run_quintuple(rules, max_steps))
            del rules[(q, a)]
        # (2) 継続する機械
        first = not rules
        targets = list(range(nstates)) + ([nstates] if nstates < k else [])
        for q2 in targets:
            for b in (0, 1):
                for d in (R,) if first else (L, R):
                    if reversible and not _quintuple_rule_ok(rules, q2, b, d):
                        continue
                    rules[(q, a)] = (q2, b, d)
                    branch(rules, max(nstates, q2 + 1))
                    del rules[(q, a)]

    branch({}, 1)
    return stats


def format_quintuple(rules, k):
    """bbchallenge 標準形式 '1RB1LB_1LA1RZ' に整形（未定義は '---'）。"""
    letters = "ABCDEFGH"
    out = []
    for q in range(k):
        blk = ""
        for a in (0, 1):
            if (q, a) not in rules:
                blk += "---"
            else:
                q2, b, d = rules[(q, a)]
                blk += f"{b}{'R' if d == R else 'L'}{'Z' if q2 == HALT else letters[q2]}"
        out.append(blk)
    return "_".join(out)


def parse_quintuple(text):
    """'1RB1LB_1LA1RZ' -> (rules, k)。"""
    letters = "ABCDEFGH"
    rules = {}
    blocks = text.split("_")
    for q, blk in enumerate(blocks):
        for a in (0, 1):
            t = blk[3 * a:3 * a + 3]
            if t == "---":
                continue
            b = int(t[0])
            d = R if t[1] == "R" else L
            q2 = HALT if t[2] == "Z" else letters.index(t[2])
            rules[(q, a)] = (q2, b, d)
    return rules, len(blocks)


# ---------------------------------------------------------------- 四つ組

# 四つ組規則の表現:
#   書き込み型状態 q: {(q, a): (q2, b)}      キー種別 'w'
#   移動型状態  q: {(q, None): (q2, d)}     キー種別 'm'
# 状態ごとに型が一つに決まる（前向き決定性）。

def quadruple_reversible(wr: dict, mv: dict) -> bool:
    """wr: (q,a)->(q2,b) / mv: q->(q2,d)。Morita 流の可逆性条件。

    逆機械の決定性から導く。逆規則は
      [q, a, b, q'] の逆 = [q', b, a, q]   （記号 b を読む＝読み guard がある）
      [q, /, d, q'] の逆 = [q', /, -d, q]  （読み guard が無い＝何にでも当たる）
    よって状態 q' に入る規則については
      - 移動型が1本でもあれば、それが q' への**唯一の**入り規則でなければならない
        （移動型の逆規則には読み guard が無いので、他のどの逆規則とも衝突する）
      - すべて書き込み型なら、書く記号 b が互いに異なること
    が必要十分である。「移動型2本を方向で区別できる」は**誤り**（移動規則は記号を
    書かないので、逆向きにどちらから来たかを読み取る材料が無い）。
    """
    arrivals: dict[int, list[tuple[str, int]]] = {}
    for (_q, _a), (q2, b) in wr.items():
        arrivals.setdefault(q2, []).append(("w", b))
    for _q, (q2, d) in mv.items():
        arrivals.setdefault(q2, []).append(("m", d))
    for _q2, arr in arrivals.items():
        if any(t == "m" for t, _v in arr):
            if len(arr) > 1:
                return False
        elif len({v for _t, v in arr}) != len(arr):
            return False
    return True


def _quadruple_arrival_ok(wr, mv, q2, kind, val):
    """規則を q2 へ1本追加しても可逆性を保てるか（増分判定）。"""
    for (_q, _a), (r2, b) in wr.items():
        if r2 == q2 and (kind == "m" or b == val):
            return False
    for _q, (r2, _d) in mv.items():
        if r2 == q2:
            return False
    return True


def run_quadruple(wr, mv, mtype, max_steps):
    """mtype: q -> 'w' | 'm' | None(未決定)。空テープから走らせる。"""
    tape: dict[int, int] = {}
    head = 0
    q = 0
    steps = 0
    seen: dict[tuple, tuple[int, int]] = {}
    init_sig = None
    det = TranslatedCyclerDetector()
    rmax = lmin = 0
    has_halt = (any(t[0] == HALT for t in wr.values())
                or any(t[0] == HALT for t in mv.values()))
    while True:
        sig = (q, frozenset(p - head for p, v in tape.items() if v))
        if init_sig is None:
            init_sig = sig
        if sig in seen:
            t0, h0 = seen[sig]
            offset = head - h0
            return {"status": "nonhalt_cycle" if offset == 0 else "nonhalt_translated",
                    "steps": steps, "ones": sum(1 for v in tape.values() if v),
                    "offset": offset, "returned_to_initial": sig == init_sig}
        seen[sig] = (steps, head)
        a = tape.get(head, 0)
        t = mtype.get(q)
        if t is None:
            return {"status": "undefined", "steps": steps, "state": q, "symbol": a,
                    "ones": sum(1 for v in tape.values() if v), "need": "type"}
        if t == "w":
            if (q, a) not in wr:
                return {"status": "undefined", "steps": steps, "state": q,
                        "symbol": a, "ones": sum(1 for v in tape.values() if v),
                        "need": "w"}
            q2, b = wr[(q, a)]
            if b:
                tape[head] = b
            else:
                tape.pop(head, None)
        else:
            if q not in mv:
                return {"status": "undefined", "steps": steps, "state": q,
                        "symbol": a, "ones": sum(1 for v in tape.values() if v),
                        "need": "m"}
            q2, d = mv[q]
        steps += 1
        if q2 == HALT:
            return {"status": "halt", "steps": steps,
                    "ones": sum(1 for v in tape.values() if v)}
        if t == "m":
            head += d
        q = q2
        det.step(head)
        if head > rmax:
            rmax = head
            if det.observe(0, q, head, tape):
                return {"status": "nonhalt_translated", "steps": steps,
                        "ones": sum(1 for v in tape.values() if v),
                        "via": "right_record"}
        elif head < lmin:
            lmin = head
            if det.observe(1, q, head, tape):
                return {"status": "nonhalt_translated", "steps": steps,
                        "ones": sum(1 for v in tape.values() if v),
                        "via": "left_record"}
        if steps >= max_steps:
            # 停止規則を1本も持たない機械は原理的に停止しない（自明な証書）。
            if not has_halt:
                return {"status": "nonhalt_no_halt_rule", "steps": steps,
                        "ones": sum(1 for v in tape.values() if v)}
            return {"status": "undecided", "steps": steps,
                    "ones": sum(1 for v in tape.values() if v)}


def enumerate_quadruple(k, max_steps, reversible=True):
    """四つ組形式の TNF 枚挙（状態 0 は移動型に固定＝鏡映対称性の除去に使う）。"""
    stats = {"machines": 0, "halt": 0, "nonhalt_cycle": 0,
             "nonhalt_translated": 0, "nonhalt_no_halt_rule": 0,
             "undecided": 0,
             "best_steps": 0, "best_steps_machine": None,
             "best_ones": 0, "best_ones_machine": None,
             "cycle_not_initial": 0}

    def fmt(wr, mv, mtype):
        parts = []
        for q in range(k):
            t = mtype.get(q)
            if t is None:
                parts.append("-")
            elif t == "w":
                cs = []
                for a in (0, 1):
                    if (q, a) in wr:
                        q2, b = wr[(q, a)]
                        cs.append(f"{a}/{b}->{'Z' if q2 == HALT else q2}")
                    else:
                        cs.append(f"{a}/-")
                parts.append("W[" + ",".join(cs) + "]")
            else:
                if q in mv:
                    q2, d = mv[q]
                    parts.append(f"M[{'R' if d == R else 'L'}->{'Z' if q2 == HALT else q2}]")
                else:
                    parts.append("M[-]")
        return " ".join(parts)

    def record(wr, mv, mtype, res):
        stats["machines"] += 1
        st = res["status"]
        if st == "halt":
            stats["halt"] += 1
            if res["steps"] > stats["best_steps"]:
                stats["best_steps"] = res["steps"]
                stats["best_steps_machine"] = fmt(wr, mv, mtype)
            if res["ones"] > stats["best_ones"]:
                stats["best_ones"] = res["ones"]
                stats["best_ones_machine"] = fmt(wr, mv, mtype)
        elif st == "nonhalt_cycle":
            stats["nonhalt_cycle"] += 1
            if not res["returned_to_initial"]:
                stats["cycle_not_initial"] += 1
        elif st == "nonhalt_translated":
            stats["nonhalt_translated"] += 1
        elif st == "nonhalt_no_halt_rule":
            stats["nonhalt_no_halt_rule"] += 1
        else:
            stats["undecided"] += 1

    def branch(wr, mv, mtype, nstates):
        res = run_quadruple(wr, mv, mtype, max_steps)
        if res["status"] != "undefined":
            record(wr, mv, mtype, res)
            return
        q = res["state"]
        if res["need"] == "type":
            # 状態 0 は移動型に固定（書き込み型で始めても対称なので両方試す）
            for t in ("m", "w"):
                mtype[q] = t
                branch(wr, mv, mtype, nstates)
                del mtype[q]
            return
        targets = list(range(nstates)) + ([nstates] if nstates < k else [])
        if res["need"] == "m":
            first = not wr and not mv
            for q2 in targets + [HALT]:
                for d in (R,) if first else (L, R):
                    if reversible and not _quadruple_arrival_ok(wr, mv, q2, "m", d):
                        continue
                    mv[q] = (q2, d)
                    branch(wr, mv, mtype, max(nstates, q2 + 1))
                    del mv[q]
        else:
            a = res["symbol"]
            for q2 in targets + [HALT]:
                for b in (0, 1):
                    if reversible and not _quadruple_arrival_ok(wr, mv, q2, "w", b):
                        continue
                    wr[(q, a)] = (q2, b)
                    branch(wr, mv, mtype, max(nstates, q2 + 1))
                    del wr[(q, a)]

    branch({}, {}, {}, 1)
    return stats
