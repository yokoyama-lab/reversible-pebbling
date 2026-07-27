"""完全二分木の可逆ペブリング: **ZDD による記号的 BFS**。

> **このスクリプトは `.venv` を要求する**（`graphillion` 2.1 が `.venv` にある）。
> `.venv/bin/python scripts/exp01b_zdd.py` で実行すること。
> システム python では `HAS_GRAPHILLION = False` になり、各関数は `RuntimeError` を投げる。

## なぜ ZDD が噛むのか

我々の状態は**頂点部分集合**で、BFS の各レベルで扱うのは**部分集合の族**である。
ZDD（Zero-suppressed BDD, Minato 1993 / Knuth TAOCP 4A §7.1.4）はまさに
集合族を圧縮して表現するための構造なので、`dict[int,int]` で状態を1個ずつ持つ代わりに
**各距離レベルを1つの ZDD で持ち、1手の像を ZDD 演算で一括計算**できる。

さらにこのモデルは ZDD と相性が良い:

- **toggle 規則（R1/R2）で置く／取るの条件が同一**なので、1手の像は
  「guard を満たす集合に絞る → `flip(v)`」の 2 演算で書ける（put/take を分ける必要がない）。
  `setset.flip` は族の全要素で $v$ の有無を反転するので、置くと取るが同時に処理される。
- **ピーク上限 $p$ は「濃度 $\\le p$」** で、これは ZDD が得意な制約（`smaller(p+1)`）。

## 1手の像

頂点 $v$、guard $N(v)$（$v$ の非 free な先行点集合）に対し

    image_v(F) = { S △ {v} : S ∈ F, N(v) ⊆ S, |S △ {v}| ≤ p }

を `F.supersets({N(v)}) → flip(v) → smaller(p+1)` で計算し、全 $v$ で union する。

## 変数順序

ZDD のサイズは変数順序に強く依存する。木構造の制約では
**各部分木の頂点が連続ブロックになる順序（DFS 後順）**が定石なので `dfs_order` を使う。

## 検証

`tests/test_exp01e_zdd.py` が `exp01b_engine`（= `revpebble.bfs` と全域一致済み）と
重なる全域（$h\\le4$ の全 $p$、$h\\le6$ の $M^*$）で一致することを確認する。
**一致しない範囲の数値は使わない。**
"""

from __future__ import annotations

import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

HAS_GRAPHILLION = True
try:
    from graphillion import setset
except ImportError:  # システム python
    HAS_GRAPHILLION = False
    setset = None  # type: ignore[assignment]


def _require() -> None:
    if not HAS_GRAPHILLION:
        raise RuntimeError(
            "graphillion が無い。`.venv/bin/python` で実行すること "
            "（このスクリプトは .venv を要求する）。"
        )


# ---------------------------------------------------------------------------
# 木の構造（`revpebble.complete_binary_tree(h)` free-leaves 流儀）
# ---------------------------------------------------------------------------


def _offset(h: int, d: int) -> int:
    """レベル d（d=0 が葉）の開始番号。`treedp._offset` と同じ。"""
    return (1 << (h + 1)) - (1 << (h - d + 1))


def pebbleable(h: int) -> list[int]:
    """ペブル対象の頂点（内部節点＝レベル $1..h$。$2^h-1$ 個）。"""
    out: list[int] = []
    for d in range(1, h + 1):
        o = _offset(h, d)
        out.extend(o + j for j in range(1 << (h - d)))
    return out


def guards(h: int) -> dict[int, tuple[int, ...]]:
    """各ペブル対象頂点の guard = 非 free な先行点集合。

    レベル 1 の頂点の子は free な葉なので guard は空（＝いつでもトグル可）。
    """
    g: dict[int, tuple[int, ...]] = {}
    for d in range(1, h + 1):
        o = _offset(h, d)
        for j in range(1 << (h - d)):
            v = o + j
            if d == 1:
                g[v] = ()
            else:
                oc = _offset(h, d - 1)
                g[v] = (oc + 2 * j, oc + 2 * j + 1)
    return g


def root_of(h: int) -> int:
    return _offset(h, h)


def dfs_order(h: int) -> list[int]:
    """DFS 後順（部分木が連続ブロックになる）。ZDD の変数順序に使う。"""
    g = guards(h)
    order: list[int] = []

    def rec(v: int) -> None:
        for u in g[v]:
            rec(u)
        order.append(v)

    rec(root_of(h))
    return order


def set_universe_for(h: int) -> list[int]:
    """ZDD の台集合を DFS 後順で設定する。戻り値はその順序。"""
    _require()
    order = dfs_order(h)
    setset.set_universe(order)
    return order


# ---------------------------------------------------------------------------
# 記号的 BFS
# ---------------------------------------------------------------------------


def _guard_setsets(g: dict[int, tuple[int, ...]]) -> dict[int, object]:
    """guard を ZDD に前計算する（空 guard は None = フィルタ不要）。"""
    _require()
    out: dict[int, object] = {}
    for v, need in g.items():
        out[v] = setset([list(need)]) if need else None
    return out


def _union_tree(parts: list):
    """平衡二分木で union する。

    ZDD/BDD では巨大な族に小さい族を 127 回足し込む（線形累積）より、
    ペアごとに畳み上げるほうが中間結果が小さく保たれて速い。
    """
    while len(parts) > 1:
        merged = [
            parts[i].union(parts[i + 1]) if i + 1 < len(parts) else parts[i]
            for i in range(0, len(parts), 2)
        ]
        parts = merged
    return parts[0]


def one_move_image(F, g: dict[int, tuple[int, ...]], p: int, gz: dict | None = None):
    """族 $F$ から1手で到達できる状態族（ピーク $\\le p$）。

    3 つの最適化を入れてある:

    1. guard が空の頂点（レベル 1。子が free な葉）は `supersets` を省略。
       $h=7$ ではペブル対象 127 個のうち 64 個が空 guard なのでフィルタが半減する。
    2. **濃度制約 `smaller(p+1)` は union の後に 1 回だけ**適用する。
       濃度による制限は union と可換なので、127 回 → 1 回にできる。
    3. union は平衡二分木で畳む（`_union_tree`）。
    """
    _require()
    if gz is None:
        gz = _guard_setsets(g)
    parts = []
    for v in g:
        need = gz[v]
        sub = F if need is None else F.supersets(need)
        sub = sub.copy()
        sub.flip(v)
        parts.append(sub)
    if not parts:
        return setset()
    return _union_tree(parts).smaller(p + 1)


def mstar_zdd(
    h: int,
    p: int,
    *,
    max_levels: int | None = None,
    time_budget: float | None = None,
    log_every: int = 0,
    stats: list[dict] | None = None,
    checkpoint: Path | None = None,
    checkpoint_every: int = 50,
    two_level: bool = True,
    resume: tuple[int, object, object] | None = None,
) -> int | None:
    """$M^*$（高さ $h$ の完全二分木 free-leaves、ピーク上限 $p$）を記号的 BFS で。

    到達不能なら None。`max_levels` / `time_budget` を超えたら `TimeoutError`
    （「到達できなかった」ことを呼び出し側が正直に扱えるように例外で返す）。
    `stats` を渡すとレベルごとの秒数を記録する。

    `two_level=True`（既定）で**直前 2 レベルだけを保持する**:
    状態グラフは無向（toggle は対合）なので
    $\\mathrm{image}(L_d) \\subseteq L_{d-1}\\cup L_d\\cup L_{d+1}$ が成り立ち、

        $$L_{d+1} \\;=\\; \\mathrm{image}(L_d) \\setminus (L_d \\cup L_{d-1})$$

    で十分。訪問済み集合を累積する必要がなく、メモリが**レベル数に依存しなくなる**。
    無向グラフの BFS の標準的な事実で、近似ではない。
    `two_level=False` は累積 `visited` を持つ素朴版（照合用）。
    """
    _require()
    set_universe_for(h)
    g = guards(h)
    root = root_of(h)
    if p < 1:
        return None

    goal = setset([[root]])
    if resume is None:
        prev = setset()  # $L_{d-1}$
        frontier = setset([[]])  # $L_0 = \{\varnothing\}$
        d = 0
    else:
        d, prev, frontier = resume
        if not two_level:
            raise ValueError("resume は two_level=True 専用")
    visited = setset([[]])  # two_level=False のときだけ使う
    gz = _guard_setsets(g)
    t0 = time.time()
    while len(frontier) > 0:
        t1 = time.time()
        img = one_move_image(frontier, g, p, gz=gz)
        if two_level:
            nxt = img.difference(frontier).difference(prev)
        else:
            nxt = img.difference(visited)
        d += 1
        if len(nxt) == 0:
            return None
        if goal.issubset(nxt):
            if stats is not None:
                stats.append({"level": d, "found": True})
            return d
        if two_level:
            prev = frontier
        else:
            visited = visited.union(nxt)
        frontier = nxt
        # 診断（`dumps()` は重いので実際にログする時だけ計算する）
        logging_now = bool(log_every) and d % log_every == 0
        if stats is not None or logging_now:
            rec: dict = {"level": d, "sec": round(time.time() - t1, 2)}
            if logging_now:
                rec["states"] = len(nxt)
                rec["zdd_bytes"] = len(frontier.dumps())
                print(
                    f"  level {d}: frontier {rec['states']} 状態, "
                    f"ZDD {rec['zdd_bytes']/1e6:.2f}MB, {rec['sec']}s/level "
                    f"(累計 {time.time()-t0:.0f}s)",
                    flush=True,
                )
            if stats is not None:
                stats.append(rec)
        if checkpoint is not None and d % checkpoint_every == 0:
            save_checkpoint(checkpoint, h, p, d, prev, frontier)
        if max_levels is not None and d >= max_levels:
            if checkpoint is not None:
                save_checkpoint(checkpoint, h, p, d, prev, frontier)
            raise TimeoutError(f"レベル上限 {max_levels} に到達（h={h}, p={p}）: 未確定")
        if time_budget is not None and time.time() - t0 > time_budget:
            raise TimeoutError(
                f"時間上限 {time_budget}s を超過（h={h}, p={p}, レベル {d} まで）: 未確定"
            )
    return None


def save_checkpoint(path: Path, h: int, p: int, d: int, prev, frontier) -> None:
    """直前 2 レベルを保存する（`two_level` 前提）。

    **なぜプロセスを跨いで分割する必要があるか**: graphillion（SAPPOROBDD）の
    ノード表と演算キャッシュは**単調に増えるだけで GC されない**。
    2 レベル保持でロジカルな ZDD は小さく保てても、プロセスの RSS は伸び続ける
    （$h=7$ で毎秒 6MB 程度）。そこで一定レベルごとに
    「保存 → プロセス終了 → 再起動して再開」することで**ノード表をリセット**する。
    これが長時間計算を並行作業者と共存させる唯一の現実的な手段だった。
    """
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    with tmp.open("w") as fh:
        fh.write(f"{h}\n{p}\n{d}\n")
        fh.write(prev.dumps())
        fh.write("\n#SEP\n")
        fh.write(frontier.dumps())
    tmp.replace(path)  # 原子的に置き換える（途中で落ちても壊れない）


def load_checkpoint(path: Path) -> tuple[int, int, int, object, object]:
    """`save_checkpoint` の逆。戻り値 (h, p, d, prev, frontier)。"""
    _require()
    text = path.read_text()
    head, rest = text.split("\n", 3)[0], text.split("\n", 3)
    h = int(rest[0])
    p = int(rest[1])
    d = int(rest[2])
    body = rest[3]
    a, b = body.split("\n#SEP\n", 1)
    set_universe_for(h)  # 台集合を同じ順序で復元してから loads する
    return h, p, d, setset.loads(a), setset.loads(b)


def pmin_zdd(h: int, pmax: int = 20) -> int | None:
    """$p_{\\min}$（= Královič の $S'_{\\min}$。記号的 BFS 版）。"""
    for p in range(1, pmax + 1):
        if mstar_zdd(h, p) is not None:
            return p
    return None


# ---------------------------------------------------------------------------
# Královič の complete computation 側（$S_{\min}$, $T$）
# ---------------------------------------------------------------------------


def reach_target_dist_zdd(
    h: int,
    p: int,
    *,
    max_levels: int | None = None,
    time_budget: float | None = None,
    log_every: int = 0,
) -> int | None:
    """$\\varnothing$ から「根がペブル済みの**何らかの**配置」への最小手数（片道）。

    Královič の complete computation は「空→空・全頂点を一度カバー」で、木では
    「根を一度カバー」と同値。状態グラフが無向なので $T(Bt,\\,p) = 2\\times$ この値。
    （`exp01b_engine.reach_target_dist` の ZDD 版。）
    """
    _require()
    set_universe_for(h)
    g = guards(h)
    root = root_of(h)
    if p < 1:
        return None
    goal_up = setset([[root]])  # 「root を含む」判定に supersets で使う
    visited = setset([[]])
    frontier = setset([[]])
    gz = _guard_setsets(g)
    d = 0
    t0 = time.time()
    while len(frontier) > 0:
        nxt = one_move_image(frontier, g, p, gz=gz).difference(visited)
        d += 1
        if len(nxt) == 0:
            return None
        if len(nxt.supersets(goal_up)) > 0:
            return d
        visited = visited.union(nxt)
        frontier = nxt
        if log_every and d % log_every == 0:
            print(f"  [reach] level {d} (累計 {time.time()-t0:.0f}s)", flush=True)
        if max_levels is not None and d >= max_levels:
            raise TimeoutError(f"レベル上限 {max_levels}（h={h}, p={p}）: 未確定")
        if time_budget is not None and time.time() - t0 > time_budget:
            raise TimeoutError(f"時間上限 {time_budget}s（h={h}, p={p}, レベル {d}）: 未確定")
    return None


def smin_zdd(h: int, pmax: int = 20, **kw) -> int | None:
    """Královič の $S_{\\min}(Bt(h))$（complete computation の最小空間）。"""
    for p in range(1, pmax + 1):
        if reach_target_dist_zdd(h, p, **kw) is not None:
            return p
    return None


def tmin_zdd(h: int, p: int, **kw) -> int | None:
    """Královič の $T(Bt(h),p)$ = 片道の 2 倍。"""
    d = reach_target_dist_zdd(h, p, **kw)
    return None if d is None else 2 * d


if __name__ == "__main__":  # 手動確認
    _require()
    for h in range(1, 7):
        p = {1: 1, 2: 3, 3: 5, 4: 6, 5: 7, 6: 8}[h]
        t0 = time.time()
        st: list[dict] = []
        m = mstar_zdd(h, p, stats=st)
        peak = max((r.get("zdd_bytes", 0) for r in st), default=0)
        print(
            f"h={h} ({2**h-1} 頂点) p={p}: M*={m}  "
            f"({time.time()-t0:.1f}s, ZDD 最大 {peak/1e6:.2f}MB)",
            flush=True,
        )
