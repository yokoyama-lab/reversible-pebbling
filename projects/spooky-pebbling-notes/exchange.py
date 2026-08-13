#!/usr/bin/env python3
r"""$T_{UP}$ 分解の $\ge$ 方向を、交換論法を使わずに証明する — その機械検査。

    python3 exchange.py            # 既定 n<=9, s<=5
    python3 exchange.py 9 5 300    # n<=9, s<=5、各組で無作為な妥当手順を 300 本
    python3 exchange.py --mutate   # 変異注入（k の選び方を壊して検出力を測る）

## 示すもの

$$T_{UP}(n,s)\ \ge\ \min_{k\in[1,n)}\ \bigl[\,2k-1 + T_{UP}(k,s) + T_{UP}(n-k,s-1)\,\bigr]
  \qquad (n\ge2)$$

`structure_check.py` の骨格では、段(ii) の「尻尾のペブル上限 $\le s-1$」を出すのに
KSS Lemma 4.1 の $P^\bot$ 交換論法（「すべての最適算法の中で $k$ を最大にするものを取る」）
の写しが要る、と見ていた。**それは要らなかった。** $k$ を*与えられた手順の内側*で選べばよい。

## 証明（層2。KSS の定理に依拠しない — 定義だけから出る）

$U$ を長さ $n$ の鎖の妥当な unpebbling とする（$P_0=\{v_n\}$, $G_0=\emptyset$,
$P_\tau=G_\tau=\emptyset$、$\max_t|P_t|\le s$、手数 $\tau$）。$n\ge2$ とする。

**$s^\dagger := \max_t |P_t|$** と置く。$n\ge2$ なら $s^\dagger\ge2$
（$v_n$ の最後のペブル除去は unpebble でなければならず、それは $v_{n-1}\in P$ を要求する。
ghost で消すと $G_\tau=\emptyset$ のため後で unghost＝再ペブルが必要になり矛盾）。

**$k$ の選び方（ここが要点）** 「満室の時刻」$F:=\{t : |P_t| = s^\dagger\}$ は空でない。

$$k\ :=\ \max_{t\in F}\ \min\{i : v_i\in P_t\},\qquad
  t_1\ :=\ \text{その最大を与える時刻}.$$

$|P_{t_1}| = s^\dagger \ge 2$ なので $P_{t_1}$ は 2 点以上を含み、ゆえに $1\le k\le n-1$。
頭を $H=\{v_1..v_k\}$、尻尾を $T=\{v_{k+1}..v_n\}$ と書く。

**(1) 尻尾のペブルは常に $\le s^\dagger-1$。**
ある $t$ で $|P_t\cap T|\ge s^\dagger$ とすると、$|P_t|\le s^\dagger$ より
$|P_t|=s^\dagger$（＝$t\in F$）かつ $P_t\cap H=\emptyset$、すなわち $\min P_t\ge k+1$。
ところが $t\in F$ なので $k$ の最大性から $\min P_t\le k$。矛盾。∎

*（KSS が交換論法で作り出すのはまさにこの性質である。$k$ を「満室時刻の最下位ペブル位置の
最大値」として取れば、性質は定義から直ちに出る。手順を作り変える必要がない。）*

**(2) 頭の手数 $\ge 2k-1 + T_{UP}(k,s)$。**
$\min P_{t_1}=k$ なので $P_{t_1}\cap H=\{v_k\}$ ちょうど。

- *$[1,t_1]$*: $k\le n-1$ より $v_k\notin P_0$ だから $v_k$ はどこかで置かれ、置く手
  （pebble / unghost）は $v_{k-1}\in P$ を要求するので $v_{k-1}$ も $t_1$ 以前に置かれる。
  下向き帰納で各 $v_i\ (i\le k)$ が 1 回以上置かれる（$k$ 手）。さらに $i<k$ は
  $v_i\notin P_{t_1}$ なので 1 回以上外される（$k-1$ 手）。合わせて $\ge 2k-1$。
- *$(t_1,\tau]$*: $H$ 上の手だけを順序を保って取り出すと、長さ $k$ の鎖の妥当な系列になる
  （$v_j\ (j\le k)$ の前提は $v_{j-1}$ のみで $H$ の内部、$v_1$ は前提なし。尻尾の手は
  $H$ の状態に影響しない）。始状態は「$v_k$ にペブル・$v_1..v_{k-1}$ は空・ゴースト $\Gamma$」、
  終状態は全空。**補題G**（下）より、$\Gamma$ が在っても手数は $T_{UP}(k,s^\dagger)$ 以上、
  上限の単調性から $\ge T_{UP}(k,s)$。

**(3) 尻尾の手数 $\ge T_{UP}(n-k,s-1)$。**
$T$ 上の手を取り出すと長さ $n-k$ の鎖の妥当な unpebbling（始 $P=\{v_n\}$・ゴースト無し、
終 全空。$v_{k+1}$ は孤立鎖では始点なので前提なし＝a fortiori 妥当）。
(1) よりペブル上限は $s^\dagger-1\le s-1$。

(2) と (3) の手は互いに素なので
$\tau \ge (2k-1) + T_{UP}(k,s) + T_{UP}(n-k,s-1) \ge \min_{k\in[1,n)}[\cdots]$。∎

**補題G（余分なゴーストは損にならない）** 「$v_k$ にペブル＋$v_1..v_{k-1}$ にゴースト
$\Gamma$」から全空への妥当な系列（長さ $L$・ペブル上限 $c$）があれば、
「$v_k$ にペブル・ゴースト無し」から全空へ長さ $L$・上限 $c$ の妥当な系列がある。
*証明*: 同じ手列を replay し、`unghost(v)` のうち新しい走りで $v$ がゴーストでないものだけを
`pebble(v)` に読み替える。前提（$v_{j-1}\in P$）も $P$ への効果も同一なので、帰納法で
$P^{new}_t=P^{old}_t$、$G^{new}_t\subseteq G^{old}_t$ が保たれる。ゆえに $L\ge T_{UP}(k,c)$。∎

## この実行が検査するもの

1. **不等式そのもの**（BFS の厳密値 vs 右辺）— $s=2$ を含む
2. **証明の構成を、無作為に生成した妥当な手順の上で**（最適とは限らない手順を含む。
   証明は任意の妥当手順について主張しているので、こちらの方が強い検定になる）:
   $k$ の範囲・(1) 尻尾上限・(2) 頭の 2 分割・(3) 尻尾の射影・和の不等式、
   および射影が実際に妥当な unpebbling になっていること（補題G の読み替えを含めて実機で再生）
3. `--mutate` で $k$ の選び方を壊し、検査に検出力があることを確かめる
"""
from __future__ import annotations

import random
import sys
from collections import deque

import kss
from spooky import EMPTY, GHOST, PEBBLE

_EFFECT = {"pebble": PEBBLE, "unpebble": EMPTY, "ghost": GHOST, "unghost": PEBBLE}


# --- 鎖の上の遷移規則（spooky.py / kss.py と同じ。ghost はペブルからのみ） ---

def legal_moves(st: tuple[int, ...], cap: int) -> list[tuple[str, int]]:
    """状態 `st`（0-indexed、鎖）でペブル上限 `cap` のもとで打てる手。"""
    n = len(st)
    npeb = sum(1 for x in st if x == PEBBLE)
    out: list[tuple[str, int]] = []
    for v in range(n):
        ready = v == 0 or st[v - 1] == PEBBLE
        cur = st[v]
        if cur == EMPTY:
            if ready and npeb < cap:
                out.append(("pebble", v))
        elif cur == PEBBLE:
            if ready:
                out.append(("unpebble", v))
            out.append(("ghost", v))
        else:  # GHOST
            if ready and npeb < cap:
                out.append(("unghost", v))
    return out


def apply_move(st: tuple[int, ...], op: str, v: int) -> tuple[int, ...]:
    new = list(st)
    new[v] = _EFFECT[op]
    return tuple(new)


def start_state(n: int) -> tuple[int, ...]:
    """unpebbling の始状態: v_n だけペブル。"""
    return tuple(PEBBLE if i == n - 1 else EMPTY for i in range(n))


def goal_state(n: int) -> tuple[int, ...]:
    return tuple([EMPTY] * n)


def replay(n: int, st0: tuple[int, ...], moves: list[tuple[str, int]],
           cap: int) -> tuple[bool, tuple[int, ...], int]:
    """`moves` を `st0` から再生し (妥当か, 終状態, ペブルの最大値) を返す。"""
    st = st0
    peak = sum(1 for x in st if x == PEBBLE)
    for op, v in moves:
        if (op, v) not in legal_moves(st, cap):
            return False, st, peak
        st = apply_move(st, op, v)
        peak = max(peak, sum(1 for x in st if x == PEBBLE))
    return True, st, peak


# --- 無作為な（最適とは限らない）妥当 unpebbling の生成 ---

def _dist_to_goal(n: int, cap: int) -> dict[tuple[int, ...], int]:
    """全状態からゴールまでの最短手数（逆向き BFS）。"""
    fwd: dict[tuple[int, ...], list[tuple[int, ...]]] = {}
    stack = [start_state(n), goal_state(n)]
    seen = set(stack)
    # 到達可能性ではなく「ゴールへ行けるか」が要るので、全状態を素直に展開する
    all_states: list[tuple[int, ...]] = []
    def gen(prefix: list[int]) -> None:
        if len(prefix) == n:
            all_states.append(tuple(prefix))
            return
        for d in (EMPTY, PEBBLE, GHOST):
            gen(prefix + [d])
    gen([])
    rev: dict[tuple[int, ...], list[tuple[int, ...]]] = {s: [] for s in all_states}
    for s in all_states:
        if sum(1 for x in s if x == PEBBLE) > cap:
            continue
        for op, v in legal_moves(s, cap):
            rev[apply_move(s, op, v)].append(s)
    del fwd, stack, seen
    dist = {goal_state(n): 0}
    q = deque([goal_state(n)])
    while q:
        cur = q.popleft()
        for prev in rev[cur]:
            if prev not in dist:
                dist[prev] = dist[cur] + 1
                q.append(prev)
    return dist


def random_run(n: int, cap: int, dist: dict[tuple[int, ...], int],
               rng: random.Random, detour: float = 0.35,
               budget: int | None = None) -> list[tuple[str, int]] | None:
    """始状態からゴールへの妥当な手順を無作為に 1 本作る（最適とは限らない）。"""
    st = start_state(n)
    if st not in dist:
        return None
    if budget is None:
        budget = 6 * dist[st] + 40
    moves: list[tuple[str, int]] = []
    goal = goal_state(n)
    while st != goal:
        if len(moves) >= budget:
            return None
        cand = [(op, v) for op, v in legal_moves(st, cap)
                if apply_move(st, op, v) in dist]
        if not cand:
            return None
        if rng.random() < detour:
            op, v = rng.choice(cand)
        else:
            op, v = min(cand, key=lambda m: dist[apply_move(st, m[0], m[1])])
        moves.append((op, v))
        st = apply_move(st, op, v)
    return moves


# --- 証明の構成をそのまま実装する ---

def choose_k(states: list[tuple[int, ...]]) -> tuple[int, int, int]:
    """(k, t_1, s_dagger) を返す。k・頂点は 1-indexed。

    s_dagger = max_t |P_t|、F = {t : |P_t| = s_dagger}、
    k = max_{t in F} min{i : v_i in P_t}、t_1 はその最大を与える時刻。
    """
    pebs = [[i + 1 for i, x in enumerate(st) if x == PEBBLE] for st in states]
    s_dagger = max(len(p) for p in pebs)
    best_k, best_t = -1, -1
    for t, p in enumerate(pebs):
        if len(p) == s_dagger:
            if min(p) > best_k:
                best_k, best_t = min(p), t
    return best_k, best_t, s_dagger


def check_run(n: int, s: int, moves: list[tuple[str, int]], fails: list[str],
              tag: str, k_rule=choose_k) -> None:
    """1 本の妥当な unpebbling について、証明の 3 段すべてを検査する。"""
    st = start_state(n)
    states = [st]
    for op, v in moves:
        st = apply_move(st, op, v)
        states.append(st)
    tau = len(moves)

    k, t1, s_dag = k_rule(states)

    if not (1 <= k <= n - 1):
        fails.append(f"{tag}: k={k} が [1,{n - 1}] の外（s†={s_dag}）")
        return

    # (1) 尻尾のペブル上限 <= s† - 1
    tail_peak = max(sum(1 for i in range(k, n) if st[i] == PEBBLE) for st in states)
    if tail_peak > s_dag - 1:
        fails.append(f"{tag}: (1) 破れ k={k} 尻尾ペブル {tail_peak} > s†-1={s_dag - 1}")

    # (2) 頭を t_1 で 2 分割
    head_before = [(op, v) for t, (op, v) in enumerate(moves, start=1)
                   if v + 1 <= k and t <= t1]
    head_after = [(op, v) for t, (op, v) in enumerate(moves, start=1)
                  if v + 1 <= k and t > t1]
    tail_moves = [(op, v) for op, v in moves if v + 1 > k]

    if len(head_before) < 2 * k - 1:
        fails.append(f"{tag}: (2) 前半 {len(head_before)} < 2k-1={2 * k - 1}（k={k}）")

    # (2) 頭の後半が、長さ k の鎖の妥当な unpebbling になっているか（補題G の読み替えつき）
    head_start = tuple(PEBBLE if i == k - 1 else EMPTY for i in range(k))
    translated = []
    sim = head_start
    ok = True
    for op, v in head_after:
        real_op = "pebble" if (op == "unghost" and sim[v] != GHOST) else op
        if (real_op, v) not in legal_moves(sim, s):
            ok = False
            fails.append(f"{tag}: (2) 頭の射影が非妥当 k={k} 手={real_op}(v{v + 1})")
            break
        translated.append((real_op, v))
        sim = apply_move(sim, real_op, v)
    if ok and sim != goal_state(k):
        fails.append(f"{tag}: (2) 頭の射影の終状態が空でない k={k}: {sim}")
    tup_head = kss.T_UP(k, s)
    if ok and tup_head is not None and len(head_after) < tup_head:
        fails.append(f"{tag}: (2) 後半 {len(head_after)} < T_UP({k},{s})={tup_head}")

    # (3) 尻尾の射影が、長さ n-k の鎖の妥当な unpebbling になっているか
    m = n - k
    sim = start_state(m)
    ok = True
    for op, v in tail_moves:
        vv = v - k
        if (op, vv) not in legal_moves(sim, s_dag - 1):
            ok = False
            fails.append(f"{tag}: (3) 尻尾の射影が非妥当 k={k} 手={op}(v{v + 1})")
            break
        sim = apply_move(sim, op, vv)
    if ok and sim != goal_state(m):
        fails.append(f"{tag}: (3) 尻尾の射影の終状態が空でない k={k}: {sim}")
    tup_tail = kss.T_UP(m, s - 1)
    if ok and tup_tail is not None and len(tail_moves) < tup_tail:
        fails.append(f"{tag}: (3) 尻尾 {len(tail_moves)} < T_UP({m},{s - 1})={tup_tail}")

    # 和の不等式
    if tup_head is not None and tup_tail is not None:
        rhs = 2 * k - 1 + tup_head + tup_tail
        if tau < rhs:
            fails.append(f"{tag}: 和 τ={tau} < 2k-1+T_UP({k},{s})+T_UP({m},{s - 1})={rhs}")


# --- 変異注入（検査に検出力があるかを測る） ---

def _mutant_min(states):
    """変異1: 満室時刻の最下位ペブルの *最小* を取る（証明は max を要求している）。"""
    pebs = [[i + 1 for i, x in enumerate(st) if x == PEBBLE] for st in states]
    s_dag = max(len(p) for p in pebs)
    cands = [(min(p), t) for t, p in enumerate(pebs) if len(p) == s_dag]
    k, t1 = min(cands)
    return k, t1, s_dag


def _mutant_off(delta: int):
    """変異2/3: 正しい k から 1 だけずらす（境界がちょうどであることを測る）。"""
    def rule(states):
        k, t1, s_dag = choose_k(states)
        return k + delta, t1, s_dag
    return rule


def _mutant_first(states):
    """変異4: 満室でない時刻 t=Last(v_n) から k を取る（旧 structure_check の選び方）。"""
    n = len(states[0])
    pebs = [[i + 1 for i, x in enumerate(st) if x == PEBBLE] for st in states]
    s_dag = max(len(p) for p in pebs)
    tstar = max(t for t, st in enumerate(states) if st[n - 1] == PEBBLE)
    lower = [i for i in pebs[tstar] if i < n]
    return (min(lower) if lower else -1), tstar, s_dag


# --- 検定の入口 ---

def check_inequality(nmax: int, smax: int) -> tuple[int, list[str]]:
    """厳密値 vs 右辺の不等式を BFS で直接確かめる（s=2 を含む）。"""
    fails, pts = [], 0
    for s in range(2, smax + 1):
        for n in range(2, nmax + 1):
            lhs = kss.T_UP(n, s)
            if lhs is None:
                continue
            best = None
            for k in range(1, n):
                a, b = kss.T_UP(k, s), kss.T_UP(n - k, s - 1)
                if a is None or b is None:
                    continue
                val = 2 * k - 1 + a + b
                best = val if best is None else min(best, val)
            if best is None:
                continue
            pts += 1
            if lhs < best:
                fails.append(f"不等式 破れ: T_UP({n},{s})={lhs} < 右辺 {best}")
    return pts, fails


def main(nmax: int = 9, smax: int = 5, runs: int = 200, seed: int = 20260813,
         mutate: bool = False) -> int:
    rng = random.Random(seed)

    pts, fails = check_inequality(max(nmax, 11), smax)
    print(f"[1] 不等式 T_UP(n,s) >= min_k[2k-1+T_UP(k,s)+T_UP(n-k,s-1)]: {pts} 点")
    if fails:
        for f in fails[:8]:
            print("  -", f)
        return 1
    print("    全点で成立（s=2 も含む。s=2 では等号は成り立たないが >= は成り立つ）")

    rules: list[tuple[str, object]] = [("証明どおり", choose_k)]
    if mutate:
        rules += [("変異1: 満室時刻の min を取る", _mutant_min),
                  ("変異2: k を +1 ずらす", _mutant_off(+1)),
                  ("変異3: k を -1 ずらす", _mutant_off(-1)),
                  ("変異4: Last(v_n) から取る（旧 structure_check）", _mutant_first)]

    total = 0
    caught: dict[str, list[str]] = {name: [] for name, _ in rules}
    for s in range(2, smax + 1):
        for n in range(2, nmax + 1):
            if kss.T_UP(n, s) is None:
                continue
            dist = _dist_to_goal(n, s)
            made = 0
            for _ in range(runs * 3):
                if made >= runs:
                    break
                mv = random_run(n, s, dist, rng)
                if mv is None:
                    continue
                made += 1
                total += 1
                ok, end, peak = replay(n, start_state(n), mv, s)
                assert ok and end == goal_state(n) and peak <= s, "生成器が壊れている"
                for name, rule in rules:
                    check_run(n, s, mv, caught[name], f"n={n} s={s}", k_rule=rule)

    rc = 0
    print(f"[2] 無作為な妥当手順 {total} 本（最適とは限らない）で証明の 3 段を検査")
    for i, (name, _) in enumerate(rules):
        bad = caught[name]
        mark = "" if (i == 0) == (not bad) else "  ⚠"
        print(f"    {name}: 不一致 {len(bad)} 件{mark}")
        for f in bad[:3]:
            print("      -", f)
        if i == 0 and bad:
            rc = 1
        if i > 0 and not bad:
            print("      ⚠ 変異が検出されなかった＝この検査に検出力が無い")
            rc = 1

    if rc == 0:
        print("\n証明の 3 段（尻尾上限 s†-1・頭の 2 分割・射影の妥当性）が、")
        print("最適とは限らない妥当手順すべての上で成立した。")
        print("=> T_UP 分解の >= 方向は交換論法なしで示せる。θ(s)=s(s+1)/2 は定理。")
    return rc


if __name__ == "__main__":
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    raise SystemExit(main(*[int(a) for a in args], mutate="--mutate" in sys.argv))
