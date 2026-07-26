"""候補2: nauty（`geng`/`directg`）を使った DAG 全数列挙（n>=7 向け）。

## 方針

1. `geng -c n`: 頂点数 n の**非同型・連結**無向グラフを全て生成（nauty が同型除去済み）。
2. `directg -a -o -T -q`: 各無向グラフの辺を非巡回向き付け（acyclic orientation）に
   する。`-o` は各辺を一方向のみに向ける、`-a` は非巡回なもののみ。**同じ入力から出た
   同型な有向グラフは directg 自身が除去する**。さらに、入力（無向グラフ）が非同型なら
   出力（有向グラフ）も非同型になる（相異なる無向骨格を持つ有向グラフが同型になることは
   ありえないため、これは nauty 固有の主張ではなく論理的に自明）。
   → **`geng -c n | directg -a -o -T -q` の出力は、頂点数 n の非同型な非巡回連結有向グラフ
   の全体と一致する（重複無し・漏れ無し）**。
3. 後段フィルタ（Python 側）: 出次数0の頂点がちょうど1個（単一シンク）のものだけ残す。
   `docs/idea02_separation_onset.md` §3-1 の解析により、単一シンクならば
   **全頂点がシンクへ到達可能なことは自動的に従う**（`exp02_dags.py` と同じ議論）。
   したがって単一シンク条件だけで、本プロジェクトが対象とする DAG 全体と一致する。
4. 出力のラベルは任意（トポロジカル順である保証が無い）ので、`revpebble.Dag` の要件
   （先行点のインデックスが自分より小さい）を満たすようにトポロジカル順で再ラベルし、
   シンクを頂点 n-1 に置く（既存モジュールとの整合を保つ）。

**正しさの裏取り**: `tests/test_exp02_nauty.py` で $n\\le6$ について、この経路で得られる
非同型類の集合（`exp02_dags.canonical_key` で比較）が自作の全数探索
（`exp02_dags.enumerate_nonisomorphic`）と**完全一致**することを検証する
（team-lead 指示の「二重実装照合」）。一致しなければ n>=7 の値は採用しないこと。
"""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from exp02_dags import edges_to_dag  # noqa: E402
from revpebble import Dag  # noqa: E402

EdgeSet = frozenset[tuple[int, int]]


def _run_geng_directg(n: int) -> str:
    """`geng -c n | directg -a -o -T -q` を実行し、テキスト出力を返す。"""
    if n == 1:
        # geng は n=1 を "1 0" として直接吐く。directg も同様に通す。
        pass
    geng = subprocess.run(["geng", "-c", str(n)], capture_output=True, check=True)
    directg = subprocess.run(
        ["directg", "-a", "-o", "-T", "-q"],
        input=geng.stdout,
        capture_output=True,
        check=True,
    )
    return directg.stdout.decode()


def _parse_directg_text(text: str, n: int) -> list[EdgeSet]:
    """directg -T の出力（各行 "nv ne e1a e1b e2a e2b ..."）を辺集合のリストにする。"""
    graphs: list[EdgeSet] = []
    for line in text.splitlines():
        line = line.strip()
        if not line:
            continue
        parts = [int(x) for x in line.split()]
        nv, ne = parts[0], parts[1]
        assert nv == n, (nv, n)
        rest = parts[2:]
        assert len(rest) == 2 * ne
        edges = frozenset((rest[2 * k], rest[2 * k + 1]) for k in range(ne))
        graphs.append(edges)
    return graphs


def _has_unique_sink(edges: EdgeSet, n: int) -> tuple[bool, int | None]:
    outdeg = [0] * n
    for i, _ in edges:
        outdeg[i] += 1
    sinks = [v for v in range(n) if outdeg[v] == 0]
    if len(sinks) == 1:
        return True, sinks[0]
    return False, None


def _topological_relabel(edges: EdgeSet, n: int, sink: int) -> EdgeSet:
    """シンクを n-1 に、他をトポロジカル順で 0..n-2 に再ラベルする。"""
    succs: list[list[int]] = [[] for _ in range(n)]
    indeg = [0] * n
    for i, j in edges:
        succs[i].append(j)
        indeg[j] += 1
    # Kahn 法（indeg 0 から順に処理）。単一シンクかつ全頂点到達可能な DAG なので、
    # シンク以外は必ずどこかで処理され、シンクが最後に残る。
    order: list[int] = []
    queue = [v for v in range(n) if indeg[v] == 0]
    indeg_work = indeg[:]
    while queue:
        v = queue.pop()
        order.append(v)
        for w in succs[v]:
            indeg_work[w] -= 1
            if indeg_work[w] == 0:
                queue.append(w)
    assert len(order) == n, "非巡回であるはずなのに全頂点を処理できなかった"
    assert order[-1] == sink, (order, sink)
    relabel = {old: new for new, old in enumerate(order)}
    return frozenset((relabel[i], relabel[j]) for i, j in edges)


def enumerate_nonisomorphic_nauty(n: int) -> list[EdgeSet]:
    """nauty 経路で頂点数 n の非同型 DAG（単一シンク・全頂点到達可能）を列挙する。

    `exp02_dags.enumerate_nonisomorphic` と同じ対象を返す（n<=6 で完全一致を
    `tests/test_exp02_nauty.py` で検証済み）。
    """
    text = _run_geng_directg(n)
    raw = _parse_directg_text(text, n)
    out: list[EdgeSet] = []
    for edges in raw:
        ok, sink = _has_unique_sink(edges, n)
        if not ok:
            continue
        assert sink is not None
        out.append(_topological_relabel(edges, n, sink))
    return out


def edges_to_dag_n(edges: EdgeSet, n: int, name: str = "g") -> Dag:
    return edges_to_dag(edges, n, name)


if __name__ == "__main__":  # 手動確認用
    for n in range(1, 8):
        classes = enumerate_nonisomorphic_nauty(n)
        print(f"n={n}: nauty経路の非同型類数={len(classes)}")
