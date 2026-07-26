"""完全二分木の可逆ペブリング: Aut 商グラフ上の厳密 BFS。

## なぜこれが必要か

`exp01b_engine` のビットマスク BFS でも `cbt(4)*`（= `cbt(5)` free-leaves、
ペブル対象 31 頂点）が上限だった（$p=10$ で 207 秒）。
次の $m=5$（63 頂点）は素の状態数が $\\sum_{k\\le8}\\binom{63}{k}\\approx4.5\\times10^9$ で届かない。

## 何をするか

完全二分木の自己同型群 Aut（各内部節点での兄弟入れ替え）で状態を割る。
$\\varnothing$ と目標状態 $\\{\\text{root}\\}$ はどちらも **Aut 不変**なので、
商グラフ上の最短距離は元のグラフ上の最短距離に**厳密に等しい**
（群作用が始点・終点を固定する場合の標準的事実。近似ではない）。

軌道数（= shape 数）の削減率は劇的:

| ペブル対象の高さ $m$ | 頂点数 | $p\\le8$ の全部分集合 | shape 数 | 削減率 |
|---|---|---|---|---|
| 4 | 31 | 1.1e7 | 45,972 | 249x |
| 5 | 63 | 4.5e9 | 1,000,496 | 4500x |
| 6 | 127 | 1.4e12 | 13,188,337 | 108819x |

## 表現

高さ $m$ の完全二分木（葉は free = ペブル対象外なので、ここでの「頂点」は
すべてペブル対象）の状態を、次の再帰的な正規形（shape）で表す。

  - 高さ 0: `b` ∈ {0,1}（その1頂点がペブル済みか）
  - 高さ $k$: `(b, i, j)` （$i \\le j$ は子部分木の shape の id）

`i \\le j` の正規化が兄弟入れ替えの商を取ることに対応する。
shape には出現順に id を振り、id → (popcount, root ビット, key) を配列で持つ。

遷移（隣接 shape）は子の遷移から構成できるので、子の高さでは**メモ化**し、
最上位の高さでは都度計算する（メモリ節約）。

## 正規化の対応

`cbt(h)` free-leaves（葉が free）のペブル対象は内部節点だけで、これは
**高さ $m = h-1$ の完全二分木**。したがって

    M*(cbt(h) free-leaves, p) = mstar_tree(h-1, p)
    M*(cbt(h) all-pebbled,  p) = mstar_tree(h,   p)

`tests/test_exp01c_treedp.py` が `exp01b_engine`（= `revpebble.bfs`）との
全域一致を確認する。
"""

from __future__ import annotations

_SHIFT = 27  # 子 id は 2^27 未満と仮定（assert で検査）

# 実測した到達範囲（2026-07-27, 61GB マシン。他の作業と共用）:
#   m<=5 (cbt(6) free-leaves, 63 頂点): p<=10 まで数分・数百MB で完走。
#   m=6  (cbt(7) free-leaves, 127 頂点): p=8 は 11 秒、p=9 は 104 秒でどちらも到達不能を確定。
#     p=10 は **未到達**。shape id が 2^27 を超えて上の assert が発火し、
#     その時点で 18〜20GB を消費していた。$M^*(T_7)$ を出すには
#     (a) 距離辞書を配列に、(b) レベル同期 BFS で 2 レベルのみ保持、(c) IDA*
#     のいずれかが必要（`data/exp01_results.md` §7-1）。
#   → **並行作業者がいる環境では必ず cap を渡すこと。**


class QuotientTree:
    """高さ m の完全二分木の状態を Aut で割った商グラフ。"""

    def __init__(self, m: int) -> None:
        assert m >= 0
        self.m = m
        # 高さ k ごとの shape テーブル
        self._key2id: list[dict[int, int]] = [{} for _ in range(m + 1)]
        self._keys: list[list[int]] = [[] for _ in range(m + 1)]
        self._pc: list[list[int]] = [[] for _ in range(m + 1)]
        self._rb: list[list[int]] = [[] for _ in range(m + 1)]
        self._nbr: list[dict[int, tuple[int, ...]]] = [{} for _ in range(m + 1)]
        # 高さ 0: b=0, b=1 を先に登録（id 0, 1 に固定）
        self._intern(0, 0)
        self._intern(0, 1)

    # -- shape の登録 -------------------------------------------------------

    def _intern(self, k: int, key: int) -> int:
        tab = self._key2id[k]
        got = tab.get(key)
        if got is not None:
            return got
        i = len(self._keys[k])
        assert i < (1 << _SHIFT), "shape id が想定を超えた（_SHIFT を上げる）"
        tab[key] = i
        self._keys[k].append(key)
        if k == 0:
            self._pc[k].append(key)
            self._rb[k].append(key)
        else:
            b = key & 1
            ci = (key >> 1) & ((1 << _SHIFT) - 1)
            cj = key >> (1 + _SHIFT)
            self._pc[k].append(b + self._pc[k - 1][ci] + self._pc[k - 1][cj])
            self._rb[k].append(b)
        return i

    def _pack(self, b: int, i: int, j: int) -> int:
        if i > j:
            i, j = j, i
        return b | (i << 1) | (j << (1 + _SHIFT))

    def _mk(self, k: int, b: int, i: int, j: int) -> int:
        return self._intern(k, self._pack(b, i, j))

    # -- 基本情報 -----------------------------------------------------------

    def popcount(self, k: int, sid: int) -> int:
        return self._pc[k][sid]

    def root_pebbled(self, k: int, sid: int) -> int:
        return self._rb[k][sid]

    def empty_id(self, k: int | None = None) -> int:
        """全て空の shape の id。"""
        k = self.m if k is None else k
        if k == 0:
            return 0
        e = self.empty_id(k - 1)
        return self._mk(k, 0, e, e)

    def goal_id(self, k: int | None = None) -> int:
        """根だけペブル済みの clean 状態の id。"""
        k = self.m if k is None else k
        if k == 0:
            return 1
        e = self.empty_id(k - 1)
        return self._mk(k, 1, e, e)

    # -- 遷移 ---------------------------------------------------------------

    def neighbors(self, k: int, sid: int) -> tuple[int, ...]:
        """shape sid から1手で移れる shape（ピーク制約は課さない）。"""
        if k == 0:
            return (1 - sid,)  # 子は free なので常にトグル可
        cache = self._nbr[k]
        got = cache.get(sid)
        if got is not None:
            return got
        key = self._keys[k][sid]
        b = key & 1
        ci = (key >> 1) & ((1 << _SHIFT) - 1)
        cj = key >> (1 + _SHIFT)
        out: list[int] = []
        # 根のトグル: 両方の子の根がペブル済みであること
        if self._rb[k - 1][ci] and self._rb[k - 1][cj]:
            out.append(self._mk(k, 1 - b, ci, cj))
        for c2 in self.neighbors(k - 1, ci):
            out.append(self._mk(k, b, c2, cj))
        if cj != ci:
            for c2 in self.neighbors(k - 1, cj):
                out.append(self._mk(k, b, ci, c2))
        res = tuple(out)
        # 最上位は状態数が多すぎるのでキャッシュしない
        if k < self.m:
            cache[sid] = res
        return res

    # -- 数え上げ（テスト用） ------------------------------------------------

    def count_shapes(self, kmax: int) -> list[int]:
        """popcount = 0..kmax の shape 数（全列挙。テストで軌道数公式と照合する）。"""
        m = self.m
        by_pc: list[list[list[int]]] = []  # by_pc[k][pc] = ids
        cur = [[0], [1]]  # 高さ 0
        by_pc.append(cur)
        for k in range(1, m + 1):
            prev = by_pc[k - 1]
            nxt: list[list[int]] = [[] for _ in range(kmax + 1)]
            for pi in range(min(len(prev), kmax + 1)):
                for pj in range(pi, min(len(prev), kmax + 1)):
                    for a, ii in enumerate(prev[pi]):
                        for jj in prev[pj][a:] if pi == pj else prev[pj]:
                            for b in (0, 1):
                                tot = b + pi + pj
                                if tot > kmax:
                                    continue
                                nxt[tot].append(self._mk(k, b, ii, jj))
            by_pc.append(nxt)
        return [len(set(x)) for x in by_pc[m][: kmax + 1]]


# ---------------------------------------------------------------------------
# 探索
# ---------------------------------------------------------------------------


def mstar_tree(
    m: int, p: int, *, cap: int | None = None, qt: QuotientTree | None = None
) -> int | None:
    """高さ m の完全二分木（葉 free）の $M^*$（ピーク上限 p）。到達不能なら None。

    商グラフ上の双方向 BFS。`cap` を超えたら RuntimeError。
    """
    if m < 0:
        return None
    qt = qt or QuotientTree(m)
    start = qt.empty_id()
    goal = qt.goal_id()
    if p < 1:
        return None
    if start == goal:
        return 0

    top = qt.m
    fpc = qt.popcount
    fseen = {start: 0}
    bseen = {goal: 0}
    fwd = [start]
    bwd = [goal]
    df = db = 0
    while fwd and bwd:
        if len(fwd) <= len(bwd):
            nxt: list[int] = []
            for s in fwd:
                for t in qt.neighbors(top, s):
                    if t not in fseen and fpc(top, t) <= p:
                        fseen[t] = df + 1
                        nxt.append(t)
            df += 1
            fwd = nxt
            for t in fwd:
                if t in bseen:
                    return df + bseen[t]
        else:
            nxt = []
            for s in bwd:
                for t in qt.neighbors(top, s):
                    if t not in bseen and fpc(top, t) <= p:
                        bseen[t] = db + 1
                        nxt.append(t)
            db += 1
            bwd = nxt
            for t in bwd:
                if t in fseen:
                    return db + fseen[t]
        if cap is not None and len(fseen) + len(bseen) > cap:
            raise RuntimeError(f"状態数が cap={cap} を超えた（m={m}, p={p}）: 到達できなかった")
    return None


def pmin_tree(m: int, pmax: int = 20, *, cap: int | None = None) -> int | None:
    """高さ m の完全二分木（葉 free）の $p_{\\min}$。"""
    for p in range(1, pmax + 1):
        if mstar_tree(m, p, cap=cap) is not None:
            return p
    return None


# ---------------------------------------------------------------------------
# 商グラフの最短路を「実際の頂点の手順」に戻す
# ---------------------------------------------------------------------------


def _offset(h: int, d: int) -> int:
    """`revpebble.complete_binary_tree(h)` のレベル d（d=0 が葉）の開始番号。"""
    return (1 << (h + 1)) - (1 << (h - d + 1))


def level_index(h: int, v: int) -> tuple[int, int]:
    """頂点番号 v を (レベル d, レベル内の位置 j) に分解する。"""
    for d in range(h + 1):
        o = _offset(h, d)
        if o <= v < o + (1 << (h - d)):
            return d, v - o
    raise ValueError(v)


class TreeRealizer:
    """`complete_binary_tree(h)` free-leaves 流儀の具体状態 ⟷ shape の対応。"""

    def __init__(self, h: int) -> None:
        self.h = h
        self.m = h - 1  # ペブル対象の完全二分木の高さ
        self.qt = QuotientTree(self.m)
        # ペブル対象はレベル 1..h。深さ d のノードの shape 高さは d-1。
        self.nodes: list[int] = []
        self.kids: dict[int, tuple[int, int] | None] = {}
        self.sheight: dict[int, int] = {}
        for d in range(1, h + 1):
            for j in range(1 << (h - d)):
                v = _offset(h, d) + j
                self.nodes.append(v)
                self.sheight[v] = d - 1
                if d == 1:
                    self.kids[v] = None  # 子は free な葉
                else:
                    o = _offset(h, d - 1)
                    self.kids[v] = (o + 2 * j, o + 2 * j + 1)
        self.root = _offset(h, h)

    def shape_of(self, mask: int) -> int:
        """具体状態（ビットマスク）の shape id。"""

        def rec(v: int) -> int:
            b = (mask >> v) & 1
            k = self.kids[v]
            if k is None:
                return b  # 高さ 0 の shape id は b そのもの
            return self.qt._mk(self.sheight[v], b, rec(k[0]), rec(k[1]))

        return rec(self.root)

    def legal(self, mask: int, v: int) -> bool:
        k = self.kids[v]
        if k is None:
            return True
        return bool((mask >> k[0]) & 1) and bool((mask >> k[1]) & 1)


def dist_to_goal(
    m: int, p: int, qt: QuotientTree | None = None, *, cap: int | None = None
) -> dict[int, int]:
    """目標 shape からの単方向 BFS 距離（ピーク上限 p）。realize 用。

    `cap` を超えたら RuntimeError（並行作業者がいる環境ではメモリ保護のため必ず渡す）。
    """
    qt = qt or QuotientTree(m)
    goal = qt.goal_id()
    dist = {goal: 0}
    frontier = [goal]
    d = 0
    while frontier:
        nxt = []
        for s in frontier:
            for t in qt.neighbors(qt.m, s):
                if t not in dist and qt.popcount(qt.m, t) <= p:
                    dist[t] = d + 1
                    nxt.append(t)
        d += 1
        frontier = nxt
        if cap is not None and len(dist) > cap:
            raise RuntimeError(f"状態数が cap={cap} を超えた（m={m}, p={p}）: 到達できなかった")
    return dist


def first_root_pebbled_depth(
    m: int, p: int, qt: QuotientTree | None = None, *, cap: int | None = None
) -> int | None:
    """$\\varnothing$ から「根がペブル済みの**何らかの**状態」への最小手数 $g_m(p)$。

    clean（根だけ）である必要がない点が $M^*$ との違い。**下界の材料**である:

    高さ $m+2$ の木の任意の手順を、部分木 $A$／部分木 $B$／根 の手に分解する
    （3 つは互いに素で、全体を覆う）。$A$ の制限手順は
    $\\varnothing \\to (a を含む状態) \\to \\varnothing$ を辿るので、
    その長さは $\\ge 2g_m(p)$（往復。状態グラフが無向なので復路も同じ距離）。
    根のトグルは $\\ge 1$ 回。よって

    $$M^*(T_{m+2},\\,p) \\;\\ge\\; 4\\,g_m(p) + 1 .$$

    $A$ に許すピークを全体の $p$ まで緩めているので**健全な下界**（緩い側に外す）。
    """
    qt = qt or QuotientTree(m)
    start = qt.empty_id()
    if qt.root_pebbled(qt.m, start):
        return 0
    seen = {start}
    frontier = [start]
    d = 0
    while frontier:
        nxt = []
        for s in frontier:
            for t in qt.neighbors(qt.m, s):
                if t in seen or qt.popcount(qt.m, t) > p:
                    continue
                if qt.root_pebbled(qt.m, t):
                    return d + 1
                seen.add(t)
                nxt.append(t)
        d += 1
        frontier = nxt
        if cap is not None and len(seen) > cap:
            raise RuntimeError(f"状態数が cap={cap} を超えた（m={m}, p={p}）: 到達できなかった")
    return None


def lower_bound_mstar(m: int, p: int, *, cap: int | None = None) -> int | None:
    """$M^*(T_{m+2},p) \\ge 4g_m(p)+1$ の下界（`first_root_pebbled_depth` の系）。"""
    g = first_root_pebbled_depth(m, p, cap=cap)
    return None if g is None else 4 * g + 1


def lower_bound_mstar_phased(m: int, p: int, *, cap: int | None = None) -> int | None:
    """$M^*(\\text{高さ }m{+}1,\\,p) \\ge 2\\big(g_m(p)+g_m(p-1)\\big)+1$（`lower_bound_mstar` の改良）。

    $t^*$ を「根が**最後に**置かれた時刻」とする（以後、根は最終状態まで盤上に残る）。
    部分木 $A$ の制限手順を $t^*$ で切ると:

    - $t^*$ 以前: $\\varnothing \\to S_A$（$a\\in S_A$）。ピーク $\\le p$。長さ $\\ge g_m(p)$。
    - $t^*$ 以降: $S_A \\to \\varnothing$。**根が 1 本占めている**のでピーク $\\le p-1$。
      長さ $\\ge \\mathrm{dist}_{p-1}(S_A,\\varnothing) \\ge g_m(p-1)$
      （状態グラフが無向なので $\\mathrm{dist}_{p-1}(S_A,\\varnothing)=\\mathrm{dist}_{p-1}(\\varnothing,S_A)$、
      これは $a$ を含む配置への最小距離以上）。

    $B$ も同様。$A$／$B$／根 の手は互いに素なので合計して上の式。
    $g_m$ は $p$ について非増加なので $g_m(p-1)\\ge g_m(p)$、
    よってこの下界は `lower_bound_mstar`（$4g_m(p)+1$）以上である。
    """
    a = first_root_pebbled_depth(m, p, cap=cap)
    b = first_root_pebbled_depth(m, p - 1, cap=cap)
    if a is None or b is None:
        return None
    return 2 * (a + b) + 1


def smin_tree(m: int, pmax: int = 20, *, cap: int | None = None) -> int | None:
    """**Královič の $S_{\\min}(Bt(m))$**（complete computation の最小空間）。

    彼の $Bt(m)$ = 高さ $m$ の完全二分木で**葉も空間に数える**流儀。
    これは `QuotientTree(m)` がそのまま対応する（高さ 0 の節点の子は free な葉ではなく、
    高さ 0 の節点自身が彼の葉である）。

    彼の complete computation は「空→空・全頂点を一度カバー」で、木では
    「根を一度カバーする」と同値（`scripts/exp01b_engine.py` の該当節）。
    → 根がペブル済みの配置が到達可能な最小ピーク。
    """
    for p in range(1, pmax + 1):
        if first_root_pebbled_depth(m, p, cap=cap) is not None:
            return p
    return None


def tmin_tree(m: int, p: int, *, cap: int | None = None) -> int | None:
    """**Královič の $T(Bt(m),p)$** = $2 g_m(p)$（往復するので片道の 2 倍）。"""
    g = first_root_pebbled_depth(m, p, cap=cap)
    return None if g is None else 2 * g


def realize_optimal(
    h: int, p: int, *, cap: int | None = None
) -> list[tuple[str, int]] | None:
    """`complete_binary_tree(h)` free-leaves の最適手順を実頂点番号で1本返す。

    商グラフ上の距離表を使って $\\varnothing$ から貪欲に降りる。長さは $M^*$ に一致する
    （`tests/test_exp01c_treedp.py` が検証器つきで確認する）。
    """
    tr = TreeRealizer(h)
    dist = dist_to_goal(tr.m, p, qt=tr.qt, cap=cap)
    mask = 0
    s = tr.shape_of(mask)
    if s not in dist:
        return None
    seq: list[tuple[str, int]] = []
    cur = dist[s]
    while cur > 0:
        for v in tr.nodes:
            if not tr.legal(mask, v):
                continue
            bit = 1 << v
            nm = mask ^ bit
            if nm.bit_count() > p:
                continue
            nd = dist.get(tr.shape_of(nm))
            if nd == cur - 1:
                seq.append(("put" if nm & bit else "take", v))
                mask = nm
                cur = nd
                break
        else:  # pragma: no cover
            raise AssertionError("距離表が不整合（realize 失敗）")
    return seq


def lift(h: int, seq_sub: list[tuple[str, int]], right: bool) -> list[tuple[str, int]]:
    """高さ h-1 の木の手順を、高さ h の木の左／右部分木の頂点番号へ移す。

    `complete_binary_tree` の番号付けでは、左部分木の レベル d は各レベルの前半、
    右部分木は後半 (+2^{h-1-d}) を占める。
    """
    out: list[tuple[str, int]] = []
    for kind, v in seq_sub:
        d, j = level_index(h - 1, v)
        if right:
            j += 1 << (h - 1 - d)
        out.append((kind, _offset(h, d) + j))
    return out


def invert(seq: list[tuple[str, int]]) -> list[tuple[str, int]]:
    """手順の逆（clean に戻す手順）。トグルは対合なので逆順＋put/take 反転。"""
    return [("take" if k == "put" else "put", v) for k, v in reversed(seq)]


def compose_schedule(h: int, sub: list[tuple[str, int]]) -> list[tuple[str, int]]:
    """部分木の手順から高さ h の木の手順を作る（逐次合成）。

    「左を作る → 右を作る → 根を置く → 右を片付ける → 左を片付ける」。
    部分木のピークを $q$ とするとこの手順のピークは $q+2$ 以下。
    → $p_{\\min}(T_h) \\le p_{\\min}(T_{h-1}) + 2$ の**構成的な証書**になる。
    """
    left = lift(h, sub, right=False)
    right = lift(h, sub, right=True)
    root = _offset(h, h)
    return left + right + [("put", root)] + invert(right) + invert(left)


def compose_asymmetric(
    h: int,
    build_a: list[tuple[str, int]],
    build_b: list[tuple[str, int]],
    clear_b: list[tuple[str, int]],
    clear_a: list[tuple[str, int]],
) -> list[tuple[str, int]]:
    """位相ごとに別のピーク予算を使う合成（`compose_schedule` の一般化）。

    「$A$ を作る → $B$ を作る → 根を置く → $B$ を片付ける → $A$ を片付ける」の各位相で
    **他方が盤上に占める本数が違う**ので、部分木に許されるピークも位相ごとに違う。
    全体ピークを $P$ とすると overhead は順に $0,1,(2),2,1$ なので、部分木の許容ピークは

    | 位相 | $A$ を作る | $B$ を作る | 根 | $B$ を片付ける | $A$ を片付ける |
    |---|---|---|---|---|---|
    | 盤上の他の駒 | なし | $a$ | $a,b$ | $a$,根 | 根 |
    | 部分木の許容ピーク | $P$ | $P-1$ | — | $P-2$ | $P-1$ |

    どの位相も $\\varnothing \\leftrightarrow \\{\\text{根}\\}$ をつなぐ手順であればよいので
    **位相ごとに違う手順を使ってよい**（`compose_schedule` は 4 位相すべてで同じ手順を
    使う特殊形で、そのぶん損をしている）。

    引数は4つとも「高さ $h-1$ の木の $\\varnothing\\to\\{\\text{根}\\}$ 手順」。
    `clear_*` は内部で `invert` して使う。
    """
    root = _offset(h, h)
    return (
        lift(h, build_a, right=False)
        + lift(h, build_b, right=True)
        + [("put", root)]
        + invert(lift(h, clear_b, right=True))
        + invert(lift(h, clear_a, right=False))
    )


if __name__ == "__main__":  # 手動確認
    import time

    for m in range(0, 6):
        t0 = time.time()
        p0 = pmin_tree(m)
        print(f"m={m} (cbt({m+1}) free-leaves, {2**(m+1)-1} 頂点): p_min={p0}", flush=True)
        if p0 is None:
            continue
        for k in range(0, 3):
            t1 = time.time()
            try:
                v = mstar_tree(m, p0 + k, cap=40_000_000)
            except RuntimeError as exc:
                print(f"   p={p0+k}: {exc}", flush=True)
                break
            print(f"   p={p0+k}: M*={v}  ({time.time()-t1:.1f}s)", flush=True)
    print(f"total {time.time()-t0:.1f}s")
