"""候補2: 合流（confluence）コストの定量化。

team-lead の依頼: 残差 $\\mathrm{res}(G) := R(G) - \\max(P(G), \\mathrm{chainR}(\\mathrm{depth}(G)))$
を定義し、それが何で説明できるかを $n\\le6$（→ n=7 も完走したので追加）の全数データで調べる。

`chainR(d)` は「深さ $d$（シンクへの最長パスの辺数）の鎖 1本」の可逆ペブル数
$\\mathrm{pmin\\_rev}$。仮説3（`exp02_separation.py` で既に反証済み: $\\mathrm{res}=0$ が
恒等的に成り立つわけではない）の**反証の大きさ**を、候補変数
（合流頂点数・分岐頂点数・幅）で説明できるか調べるのが目的。

候補変数（すべて同型不変量）:
- `num_confluent`: 入次数 >=2 の頂点数（値が複数の消費者から要求されている場所）。
- `num_branch`: 出次数 >=2 の非シンク頂点数（再利用が起きている場所。上と同じ集合とは限らない
  — 入次数は「その頂点を作るのに何本の辺を使うか」、出次数は「その頂点が何回使われるか」で
  意味が違う。合流コストの直感は本来「出次数>=2（再利用）」の方に近いはずだが、
  実データでは合流（入次数>=2 の頂点、複数の依存先が同時にペブル済みでなければならない）も
  効いている可能性があるため両方見る。
- `width`: 到達可能性の偏順序での最大反鎖（Dilworth）。$n\\le7$ は全探索で厳密に求める。
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from exp02_dags import edges_to_dag  # noqa: E402
from revpebble import pmin as pmin_rev  # noqa: E402


def depth_edges(edges: frozenset[tuple[int, int]], n: int) -> int:
    """シンク n-1 への最長パスの辺数。"""
    dp = [0] * n
    succs: list[list[int]] = [[] for _ in range(n)]
    for i, j in edges:
        succs[i].append(j)
    for v in range(n - 1):
        for w in succs[v]:
            dp[w] = max(dp[w], dp[v] + 1)
    return dp[n - 1]


def num_confluent(edges: frozenset[tuple[int, int]], n: int) -> int:
    """入次数 >=2 の頂点数（複数の先行点を同時に要求する箇所）。"""
    indeg = [0] * n
    for _, j in edges:
        indeg[j] += 1
    return sum(1 for d in indeg if d >= 2)


def num_branch(edges: frozenset[tuple[int, int]], n: int) -> int:
    """出次数 >=2 の非シンク頂点数（値が複数回再利用される箇所）。"""
    outdeg = [0] * (n - 1) if n > 1 else []
    for i, j in edges:
        if i < n - 1:
            outdeg[i] += 1
    return sum(1 for d in outdeg if d >= 2)


def reachable_matrix(edges: frozenset[tuple[int, int]], n: int) -> list[list[bool]]:
    """到達可能性の推移閉包（u -> v で u が v の祖先なら reach[u][v]=True）。"""
    succs: list[list[int]] = [[] for _ in range(n)]
    for i, j in edges:
        succs[i].append(j)
    reach = [[False] * n for _ in range(n)]
    for v in range(n - 1, -1, -1):
        for w in succs[v]:
            reach[v][w] = True
            for u in range(n):
                if reach[w][u]:
                    reach[v][u] = True
    return reach


def max_antichain(edges: frozenset[tuple[int, int]], n: int) -> int:
    """到達可能性の偏順序での最大反鎖の大きさ（Dilworth の幅）。n<=7 なので全探索でよい。"""
    reach = reachable_matrix(edges, n)
    comparable = [[reach[u][v] or reach[v][u] for v in range(n)] for u in range(n)]
    best = 0
    for mask in range(1, 1 << n):
        members = [v for v in range(n) if (mask >> v) & 1]
        if any(comparable[a][b] for i, a in enumerate(members) for b in members[i + 1 :]):
            continue
        best = max(best, len(members))
    return best


_chainR_cache: dict[int, int] = {}


def chain_r(depth: int) -> int:
    """深さ `depth`（辺数）の鎖1本の可逆ペブル数。"""
    if depth not in _chainR_cache:
        edges = frozenset((i, i + 1) for i in range(depth))
        g = edges_to_dag(edges, depth + 1)
        target = depth
        r = pmin_rev(g, target) if depth > 0 else 1
        _chainR_cache[depth] = r if r is not None else 1
    return _chainR_cache[depth]


def residual(edges: frozenset[tuple[int, int]], n: int, p: int, r: int) -> int:
    """仮説3の残差 R - max(P, chainR(depth))。0 なら仮説3が当たっていたことになる。"""
    d = depth_edges(edges, n)
    return r - max(p, chain_r(d))


if __name__ == "__main__":  # 手動確認用
    import sys as _sys

    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from exp02_dags import enumerate_nonisomorphic  # noqa: E402
    from stdpebble import pmin_std  # noqa: E402

    for n in range(1, 7):
        for edges in enumerate_nonisomorphic(n):
            g = edges_to_dag(edges, n)
            p = pmin_std(g, n - 1)
            r = pmin_rev(g, n - 1)
            res = residual(edges, n, p, r)
            if res != 0:
                print(
                    n,
                    sorted(edges),
                    "P=", p, "R=", r,
                    "res=", res,
                    "conf=", num_confluent(edges, n),
                    "branch=", num_branch(edges, n),
                    "width=", max_antichain(edges, n),
                )
    _sys.exit(0)
