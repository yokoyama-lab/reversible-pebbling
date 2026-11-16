"""候補2: 頂点数 n の DAG を全数列挙する（単一シンク・全頂点がシンクへ到達可能）。

## 列挙方針

頂点は 0..n-1、辺は i<j のみ許す（トポロジカル順で固定）。任意の DAG は
何らかのトポロジカル順を持つので、これは同型類を漏らさない
（=「ラベル付き・辺が前方のみ」の全列挙は、非同型 DAG の全同型類を
少なくとも1個は含む）。

目標頂点は常に n-1（トポロジカル順で最後）に固定する。

### 枝刈り（docs/idea02_separation_onset.md §3-1 準拠）

- **単一シンク**: 頂点 n-1 だけが出次数 0。他の頂点 0..n-2 は出次数 >= 1。
- **全頂点がシンクへ到達可能**: 実は上の「出次数>=1」制約から自動的に従う
  （トポロジカル順なので、各頂点は自分より大きい番号へしか辺を張れず、
  帰納的に最大番号側から遡って全頂点がシンクへ到達することが言える）。
  これは全数生成前の解析で確認済みで、`_all_reach_sink` にテストとして残す
  （生成コードの実際のフィルタは出次数条件のみで十分）。
- **弱連結**: 全頂点がシンクへ到達可能ならば、シンクを介して無向グラフとしても
  連結になる（各頂点からシンクへのパスが辺を共有するため）。よって別フィルタは不要。

### 同型除去（正規形）

シンクは同型写像で必ずシンクに写る（出次数0の頂点はグラフに1つしかないため）。
よって同型写像は n-1 を固定し、残り 0..n-2 の順列だけを試せば十分
（(n-1)! 通り。nauty 等は未導入のため使わない）。
各グラフに対し「(n-1)! 順列で辺集合を写した像のうち、辞書順最小のもの」を
正規形キーとして採用し、辞書で重複除去する。

n<=6 は完全に非同型類まで還元する。n=7 は候補数が数十万に達し
(n-1)!=720 通りの正規化を毎グラフに行うと 10 分では終わらないため、
既定では `nmax<=6`。n=7 を試すには `--raw7` で「重複除去しない生スキャン」を使う
（分離の存在・R-P最大化・R=P反例探索には非同型カウントは不要なため、これで十分）。
"""

from __future__ import annotations

import itertools
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from revpebble import Dag  # noqa: E402

EdgeSet = frozenset[tuple[int, int]]


def _all_pairs(n: int) -> list[tuple[int, int]]:
    return [(i, j) for i in range(n) for j in range(i + 1, n)]


def _out_ok(edges: EdgeSet, n: int) -> bool:
    """頂点 0..n-2 が出次数 >=1、頂点 n-1 は自動的に出次数 0（辺は前方のみ）。"""
    has_out = [False] * (n - 1)
    for i, j in edges:
        if i < n - 1:
            has_out[i] = True
    return all(has_out)


def _all_reach_sink(edges: EdgeSet, n: int) -> bool:
    """全頂点がシンク n-1 に到達可能か（直接検査。上の解析の裏取り用）。"""
    reach = [False] * n
    reach[n - 1] = True
    succs: list[list[int]] = [[] for _ in range(n)]
    for i, j in edges:
        succs[i].append(j)
    for v in range(n - 2, -1, -1):
        reach[v] = any(reach[w] for w in succs[v])
    return all(reach)


def generate_labeled(n: int) -> list[EdgeSet]:
    """出次数フィルタを満たす「ラベル付き・前方辺のみ」の DAG を全列挙する。

    n=1 は特別扱い（辺なし・単一頂点=シンク）。
    """
    if n == 1:
        return [frozenset()]
    pairs = _all_pairs(n)
    out: list[EdgeSet] = []
    for bits in range(2 ** len(pairs)):
        edges = frozenset(pairs[k] for k in range(len(pairs)) if (bits >> k) & 1)
        if _out_ok(edges, n):
            out.append(edges)
    return out


def _apply_perm(edges: EdgeSet, perm: tuple[int, ...]) -> EdgeSet:
    return frozenset((perm[i], perm[j]) for i, j in edges)


def canonical_key(edges: EdgeSet, n: int) -> tuple[tuple[int, int], ...]:
    """同型写像（シンク n-1 固定・残りの順列）で辞書順最小になる辺集合を正規形とする。"""
    if n <= 1:
        return tuple(sorted(edges))
    best: tuple[tuple[int, int], ...] | None = None
    for rest in itertools.permutations(range(n - 1)):
        perm = rest + (n - 1,)
        image = tuple(sorted(_apply_perm(edges, perm)))
        if best is None or image < best:
            best = image
    assert best is not None
    return best


def orbit_size(edges: EdgeSet, n: int) -> int:
    """同型写像群（(n-1)! 通り）の下での軌道の大きさ（= (n-1)!/|Aut(G)|）。"""
    if n <= 1:
        return 1
    images = {tuple(sorted(_apply_perm(edges, rest + (n - 1,)))) for rest in itertools.permutations(range(n - 1))}
    return len(images)


def enumerate_nonisomorphic(n: int) -> list[EdgeSet]:
    """頂点数 n の非同型 DAG（単一シンク n-1・全頂点到達可能）を1個ずつ返す。

    各同型類の代表元は「その類の中で辺集合が辞書順最小のもの」。
    """
    labeled = generate_labeled(n)
    seen: dict[tuple[tuple[int, int], ...], EdgeSet] = {}
    for edges in labeled:
        key = canonical_key(edges, n)
        if key not in seen:
            seen[key] = edges
    return list(seen.values())


def wl_invariant(edges: EdgeSet, n: int, rounds: int = 3) -> tuple:
    """1次元 Weisfeiler-Leman 色精緻化による同型不変量。

    各頂点の色を (自分の直前の色, 前駆点の色の多重集合, 後継点の色の多重集合) で
    `rounds` 回更新し、最終的な色の多重集合（ソート済みタプル）を返す。
    これは頂点の relabeling（同型写像）で不変（標準的な WL 色精緻化の性質:
    同型なグラフは各ラウンドで同じ色多重集合を持つ）。

    枝刈り用の**必要条件**（不変量が一致 => 同型かもしれない、一致しない => 非同型確定）
    として使う。十分条件ではないので、同じバケット内でも `canonical_key` による
    厳密な同型判定が必要（`enumerate_nonisomorphic_fast` 参照）。
    """
    preds_of: list[list[int]] = [[] for _ in range(n)]
    succs_of: list[list[int]] = [[] for _ in range(n)]
    for i, j in edges:
        succs_of[i].append(j)
        preds_of[j].append(i)

    color: list[tuple] = [(len(preds_of[v]), len(succs_of[v])) for v in range(n)]
    for _ in range(rounds):
        color = [
            (
                color[v],
                tuple(sorted(color[u] for u in preds_of[v])),
                tuple(sorted(color[w] for w in succs_of[v])),
            )
            for v in range(n)
        ]
    return tuple(sorted(color))


def enumerate_nonisomorphic_fast(n: int, wl_rounds: int = 3) -> list[EdgeSet]:
    """`enumerate_nonisomorphic` と同じ結果を、WL 不変量での事前バケット分割で高速に返す。

    手順: (1) 全ラベル付きグラフを WL 不変量でバケット分割（同型なら必ず同じバケット）。
    (2) バケットサイズ1は、他に同型の可能性を持つ候補が無いので**そのまま代表元**にできる
        （厳密な同型判定を省略できる — これが高速化の核）。
    (3) バケットサイズ>1のみ `canonical_key`（(n-1)! 順列の厳密同型判定）で正規化する。
    n<=6 で `enumerate_nonisomorphic` と完全一致することを
    `tests/test_exp02_dags.py` で検証済み。
    """
    labeled = generate_labeled(n)
    buckets: dict[tuple, list[EdgeSet]] = {}
    for edges in labeled:
        inv = wl_invariant(edges, n, rounds=wl_rounds)
        buckets.setdefault(inv, []).append(edges)

    reps: list[EdgeSet] = []
    for bucket in buckets.values():
        if len(bucket) == 1:
            reps.append(bucket[0])
            continue
        seen: dict[tuple[tuple[int, int], ...], EdgeSet] = {}
        for edges in bucket:
            key = canonical_key(edges, n)
            if key not in seen:
                seen[key] = edges
        reps.extend(seen.values())
    return reps


def edges_to_dag(edges: EdgeSet, n: int, name: str = "g") -> Dag:
    preds: list[frozenset[int]] = [frozenset() for _ in range(n)]
    for i, j in edges:
        preds[j] = preds[j] | {i}
    return Dag(n=n, preds=tuple(preds), free=frozenset(), name=name)


if __name__ == "__main__":  # 手動確認用
    for n in range(1, 7):
        labeled = generate_labeled(n)
        assert all(_all_reach_sink(e, n) for e in labeled), "解析の裏取りに失敗"
        classes = enumerate_nonisomorphic(n)
        print(f"n={n}: labeled={len(labeled)} non-isomorphic={len(classes)}")
