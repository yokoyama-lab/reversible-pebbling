"""可逆ペブリングの厳密値をとる**グラフ族**（`revpebble.py` は編集せずに足す）。

既に測ってある族: 鎖 `chain`・完全二分木 `complete_binary_tree`・ピラミッド `pyramid`
（`revpebble.py`）、spinal tree・バタフライ（`exp01b_engine.py`）、
メモ化 DAG（`memo_dags.py`）、小 DAG 全数（`exp02_dags.py`）。

ここで足すのは**まだ厳密値の表が無い 3 族**である。

| 族 | 定義 | なぜこの族か |
|---|---|---|
| `cylinder(k,h)` | 幅 $k$ を巻いたピラミッド（$h+1$ 段 × $k$ 頂点） | トーラス状の依存関係の DAG 対応物 |
| `kary_tree(k,h)` | 完全 $k$ 分木 | Královič の空間の $h+\\Theta(\\lg^* h)$ が $k$ でどう動くか |
| `bitrev(k)` | Lengauer–Tarjan のビット反転グラフ | 標準ペブリングの時空トレードオフの定番例 |

## トーラスについての但し書き（定義上の注意）

**トーラス（二方向に巻いた格子）は向きづけると必ず巡回するので、DAG にはならない。**
可逆ペブリングは DAG 上のゲームなので、トーラスそのものは対象にできない。
acyclic な対応物は**片方向だけ巻いた円筒**であり、本モジュールの `cylinder` がそれである
（メモリハード関数の文献で "wrapped pyramid" と呼ばれる形と同じ）。
「トーラスの厳密値」と書かないこと。書けるのは「円筒の厳密値」である。

## 番号づけの約束（全族共通）

- 頂点は 0..n-1 のトポロジカル順（`Dag.__post_init__` が検査する）。
- **終端は必ず最大番号 `n-1`**（`top_of`）。族ごとに終端の探し方を変えない。
- `free` は常時可用な入力源（ペブル数に数えない）。

測定は `anc()` で祖先に制限してから行う（非祖先は最適解で一度も置かれないので
$p_{\\min}$・$M^*$ は不変。頂点数 $N$ が減るので床 $2N-1$ が過大にならない）。
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from revpebble import Dag, restrict_to_ancestors  # noqa: E402


# ---------------------------------------------------------------------------
# 族
# ---------------------------------------------------------------------------


def cylinder(k: int, h: int) -> Dag:
    """幅 $k$・高さ $h$ の円筒 DAG（巻いたピラミッド）。

    頂点 $(i,j)$ = 番号 $ik+j$（$0\\le i\\le h$, $0\\le j<k$）。
    段 0 が free。段 $i\\ge1$ の $(i,j)$ の先行点は $(i-1,(j-1)\\bmod k)$ と $(i-1,j)$。
    終端は $(h,k-1)$ = 最大番号。

    退化:
      - $k=1$ で `chain(h)` に一致する（先行点が 1 個に潰れる）。
      - $k \\ge h+1$ で巻きが効かず `pyramid(h)` に一致する（祖先に制限したとき）。
    """
    assert k >= 1 and h >= 0, "k>=1, h>=0"
    n = k * (h + 1)
    preds: list[frozenset[int]] = [frozenset() for _ in range(n)]
    for i in range(1, h + 1):
        for j in range(k):
            preds[i * k + j] = frozenset(
                {(i - 1) * k + ((j - 1) % k), (i - 1) * k + j}
            )
    return Dag(
        n=n,
        preds=tuple(preds),
        free=frozenset(range(k)),
        name=f"cyl({k},{h})",
    )


def kary_tree(k: int, h: int) -> Dag:
    """高さ $h$ の完全 $k$ 分木（葉→根の向き）。葉は free、根が終端（最大番号）。

    頂点数 $(k^{h+1}-1)/(k-1)$。$k=2$ で `complete_binary_tree(h)` と同じ族。
    """
    assert k >= 2 and h >= 0, "k>=2, h>=0"
    levels: list[list[int]] = []
    counter = 0
    for lv in range(h, -1, -1):  # 葉（レベル h）から根（レベル 0）へ
        levels.append([])
        for _ in range(k**lv):
            levels[-1].append(counter)
            counter += 1
    preds: list[frozenset[int]] = [frozenset() for _ in range(counter)]
    for depth in range(1, len(levels)):
        children = levels[depth - 1]
        parents = levels[depth]
        for j, v in enumerate(parents):
            preds[v] = frozenset(children[k * j : k * (j + 1)])
    leaves = frozenset(levels[0]) if h > 0 else frozenset()
    return Dag(n=counter, preds=tuple(preds), free=leaves, name=f"kary({k},{h})")


def _bitrev_index(i: int, k: int) -> int:
    return int(format(i, f"0{k}b")[::-1], 2) if k > 0 else 0


def bitrev(k: int) -> Dag:
    """Lengauer–Tarjan のビット反転グラフ $BR_k$（$N=2^k$）。

    2 本の鎖 $u_0\\to\\cdots\\to u_{N-1}$ と $w_0\\to\\cdots\\to w_{N-1}$ に、
    交差辺 $u_{\\mathrm{bitrev}(i)}\\to w_i$ を加えたもの。$u_0$ が入力源（free）、
    終端は $w_{N-1}$（最大番号）。標準ペブリングで $\\Omega(n\\log n)$ の
    時空トレードオフを与える定番例で、可逆版の厳密値は無い。
    """
    assert k >= 1
    n = 2**k
    preds: list[frozenset[int]] = [frozenset() for _ in range(2 * n)]
    for i in range(1, n):
        preds[i] = frozenset({i - 1})
    for i in range(n):
        cross = _bitrev_index(i, k)
        preds[n + i] = frozenset({cross} | ({n + i - 1} if i > 0 else set()))
    return Dag(n=2 * n, preds=tuple(preds), free=frozenset({0}), name=f"bitrev({k})")


# ---------------------------------------------------------------------------
# 共通の道具
# ---------------------------------------------------------------------------


def top_of(g: Dag) -> int:
    """終端頂点。全族で最大番号と約束している（かつ sink であることを検査する）。"""
    t = g.n - 1
    for v in range(g.n):
        assert t not in g.preds[v], f"{g.name}: 最大番号 {t} が sink でない"
    return t


def anc(g: Dag) -> tuple[Dag, int]:
    """終端の祖先だけに制限した DAG と、付け替えた終端番号。

    非祖先は clean な最適戦略では一度も置かれないので $p_{\\min}$・$M^*$ は不変
    （`revpebble.restrict_to_ancestors` の docstring 参照）。
    """
    return restrict_to_ancestors(g, top_of(g))


#: 台帳生成と回帰テストが共有する族の登録簿。(表示名, 構築関数, パラメタ列)
FAMILIES: tuple[tuple[str, object, tuple[tuple[int, ...], ...]], ...] = (
    ("cylinder", cylinder, tuple((k, h) for k in (2, 3, 4, 5) for h in (2, 3, 4, 5, 6))),
    ("kary_tree", kary_tree, ((3, 1), (3, 2), (3, 3), (4, 1), (4, 2), (5, 1), (5, 2))),
    ("bitrev", bitrev, ((1,), (2,), (3,))),
)


def build(name: str, params: tuple[int, ...]) -> Dag:
    """登録簿の名前とパラメタから DAG を作る（台帳の行を再現するため）。"""
    for fam, fn, _ in FAMILIES:
        if fam == name:
            return fn(*params)  # type: ignore[operator]
    raise KeyError(f"未登録の族: {name}")


if __name__ == "__main__":
    for fam, fn, params in FAMILIES:
        for ps in params:
            g = fn(*ps)  # type: ignore[operator]
            ga, t = anc(g)
            print(f"{g.name:14s} n={g.n:4d} anc_n={ga.n:4d} free={len(g.free):3d} top={t}")
