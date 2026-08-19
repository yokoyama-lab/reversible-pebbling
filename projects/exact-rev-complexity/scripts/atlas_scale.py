"""資源アトラス Phase 2 — スケーリング（`docs/81_resource_atlas_plan.md` §3 Phase 2）。

パラメータ化できる 9 族について、原本の手続き部をそのまま使い **main だけを生成**して
入力サイズ $n$ を振り、資源の増え方を測る。

規約:
- 原本は不変。生成フィクスチャは `data/fixtures/scale/` に書く。
- 入力はすべて決定的（乱数なし）。族ごとの入力規則は下の FAMILIES に明記。
- **当てはめはしない**（4 回崩壊の教訓）。出力は実測列と隣接比まで。

使い方:
    python3 scripts/atlas_scale.py          # 全族を測って data/atlas/scaling.csv へ
"""

from __future__ import annotations

import csv
import sys
import time
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO / "scripts"))

from atlas_measure import measure  # noqa: E402

PYJ = Path.home() / "dev/github.com/yokoyama-lab/PyJanus/tests/jana2014/fixtures/examples"
# ⚠ PyJanus 側は 2026-08 に事例を「残すもの」で改名した（_g=ゴミを残す / _c=clean）。
# fib.ja -> fib_c.ja、gcd.ja -> gcd_g.ja（PyJanus commit d960817・f05527e）。
MEMO2017 = Path.home() / "dev/overleaf/2017_rev_memoization/program"
MEMO2021 = Path.home() / "dev/overleaf/2021_rev_memoization2/programs"
OUTDIR = REPO / "data/fixtures/scale"


def _head(path: Path) -> str:
    """原本から手続き部（`procedure main()` より前）を取り出す。"""
    text = path.read_text()
    return text[: text.index("procedure main()")]


def fib_iter(n: int) -> tuple[Path, str]:
    """反復対 Fibonacci（pyjanus/fib_c.ja）。n 段。"""
    src = PYJ / "fib_c.ja"
    return src, _head(src) + f"""procedure main()
    int x1
    int x2
    int n
    n += {n}
    call fib(x1, x2, n)
"""


def factorial(n: int) -> tuple[Path, str]:
    src = PYJ / "factorial_c.ja"
    return src, _head(src) + f"""procedure main()
  int n
  int res
  n += {n}
  call factR(n,res)
"""


def gcd_fib(k: int) -> tuple[Path, str]:
    """gcd の最悪ケース（連続 Fibonacci 対）。ガベージスタック log を使う族。"""
    a, b = 1, 1
    for _ in range(k):
        a, b = a + b, a
    src = PYJ / "gcd_g.ja"
    return src, _head(src) + f"""procedure main()
  int a
  int b
  stack log
  a += {a}
  b += {b}
  call gcd(a,b,log)
"""


def bubble_sort(n: int) -> tuple[Path, str]:
    """逆順配列（最悪ケース）。ガベージスタック gb を使う族。"""
    src = PYJ / "bubble_sort_g.ja"
    sets = "\n".join(f"  a[{i}] += {(n - i) * 10}" for i in range(n))
    return src, _head(src) + f"""procedure main()
  int a[{n}]
  int sz
  stack gb
  int ord[{n}]
  sz += {n}
{sets}
  call bsort(a,sz,gb)
"""


def edit_distance(n: int) -> tuple[Path, str]:
    """長さ n vs n。x は全て 1、y は全て 2（置換 n 回が答え）。"""
    src = PYJ / "edit_distance_c.ja"
    xs = "\n".join(f"  x[{i}] += 1" for i in range(1, n + 1))
    ys = "\n".join(f"  y[{i}] += 2" for i in range(1, n + 1))
    d = (n + 1) * (n + 1)
    return src, _head(src) + f"""procedure main()
  int x[{n + 1}]
  int y[{n + 1}]
  int m
  int n
  int D[{d}]
  m += {n}
  n += {n}
{xs}
{ys}
  call edit_distance(x,m,y,n,D)
"""


def lcs(n: int) -> tuple[Path, str]:
    """長さ n vs n の交互列（1,2,1,... と 2,1,2,...）。"""
    src = PYJ / "lcs_c.ja"
    xs = "\n".join(f"  x[{i}] += {1 + (i % 2)}" for i in range(1, n + 1))
    ys = "\n".join(f"  y[{i}] += {2 - (i % 2)}" for i in range(1, n + 1))
    d = (n + 1) * (n + 1)
    return src, _head(src) + f"""procedure main()
  int x[{n + 1}]
  int y[{n + 1}]
  int m
  int n
  int L[{d}]
  m += {n}
  n += {n}
{xs}
{ys}
  call lcs(x,m,y,n,L)
"""


def knapsack(n: int) -> tuple[Path, str]:
    """n 品目、wt[i] = (i mod 3)+1、val[i] = i、容量 n+2。"""
    src = PYJ / "knapsack_c.ja"
    cap = n + 2
    items = "\n".join(
        f"  wt[{i}] += {(i % 3) + 1}  val[{i}] += {i}" for i in range(1, n + 1)
    )
    k = (n + 1) * (cap + 1)
    return src, _head(src) + f"""procedure main()
  int wt[{n + 1}]
  int val[{n + 1}]
  int n
  int cap
  int K[{k}]
  n += {n}
  cap += {cap}
{items}
  call knapsack(wt,val,n,cap,K)
"""


def fib_pairs_2017(n: int) -> tuple[Path, str]:
    """2017 の対メモ化 Fibonacci（鎖に対応する族）。n は奇数。"""
    src = MEMO2017 / "fib.janus"
    return src, _head(src) + f"""procedure main()
  int M[{n + 1}]
  int n
  int r1
  int r2
  n += {n}
  call fib(M, n, r1, r2)
"""


def cutrod_linear(n: int) -> tuple[Path, str]:
    """2021 top-down cut rod。価格表は p[i] = i（線形・決定的）に拡張。"""
    src = MEMO2021 / "topDownCutRod.janus"
    prices = "{" + ",".join(str(i) for i in range(n + 1)) + "}"
    return src, _head(src) + f"""procedure main()
  int p[] = {prices}
  int r[size(p)] = {{0}}
  int res
  call memoizedCutRod(p,{n},r,res)
"""


FAMILIES: dict[str, tuple] = {
    # 名前: (生成関数, サイズ格子)
    "fib_iter": (fib_iter, [4, 8, 12, 16, 20, 24]),
    "factorial": (factorial, [2, 4, 6, 8, 10, 12]),
    "gcd_fib": (gcd_fib, [4, 6, 8, 10, 12, 14]),
    "bubble_sort": (bubble_sort, [4, 6, 8, 10, 12, 14]),
    "edit_distance": (edit_distance, [2, 3, 4, 5, 6, 7]),
    "lcs": (lcs, [2, 3, 4, 5, 6, 7]),
    "knapsack": (knapsack, [2, 3, 4, 5, 6, 7]),
    "fib_pairs_2017": (fib_pairs_2017, [3, 5, 7, 9, 11, 13]),
    "cutrod_linear": (cutrod_linear, [4, 6, 8, 10, 12, 14]),
}


def main() -> None:
    OUTDIR.mkdir(parents=True, exist_ok=True)
    rows: list[dict] = []
    t0 = time.monotonic()
    for fam, (gen, grid) in FAMILIES.items():
        for n in grid:
            src, text = gen(n)
            fx = OUTDIR / f"{fam}_{n}.janus"
            fx.write_text(text)
            try:
                m = measure(fx)
                row = {
                    "family": fam, "n": n, "steps": m["steps"],
                    "stack_peak": m["stack_peak"],
                    "final_live_bits": m["final_live_bits"],
                    "arrays_moves": sum(
                        a["puts"] + a["takes"] for a in m["arrays"].values()),
                    "error": "",
                }
            except Exception as exc:
                row = {"family": fam, "n": n, "steps": "", "stack_peak": "",
                       "final_live_bits": "", "arrays_moves": "",
                       "error": f"{type(exc).__name__}: {str(exc)[:80]}"}
            rows.append(row)
            print(f"{fam} n={n}: {row.get('error') or 'steps=' + str(row['steps'])}",
                  flush=True)
    out = REPO / "data/atlas/scaling.csv"
    with out.open("w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(rows[0].keys()))
        w.writeheader(); w.writerows(rows)
    print(f"\n完了 ({time.monotonic()-t0:.0f} 秒) → {out}", flush=True)


if __name__ == "__main__":
    main()
