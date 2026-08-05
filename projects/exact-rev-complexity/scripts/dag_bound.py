"""$A^*\\ge 2N-\\min(p,N)$ を**非同型な小 DAG 全数**で検査する（P1）。

## 何を確かめたいのか

`data/families/findings.md` §3.5.1 で、3 族・131 行にわたり

$$M^* = 4N - 2\\min(p,N) - 1 \\iff \\text{どの頂点も高々 2 回しか置かれない}$$

が成り立った。$M^*=2A^*-1$ なので、これは配置回数の下界

$$A^* \\;\\ge\\; 2N - \\min(p,N)$$

と、それが「高々 2 回」の領域で等号になることを言っている。

**この不等式が我々の 3 族に固有なのか、DAG 一般に成り立つのかを決める**のがこの単位である。

- DAG 一般に成り立つなら、紙の証明が族に依らない議論で書けるはずで、
  論文の核（層3→層2 への昇格）の見込みが立つ。
- 反例が出るなら、**族の性質と DAG 一般の性質の境目**が分かる。それも結果である。

## モデルの注意

`exp02_dags.edges_to_dag` は `free` を空にする（**全頂点がペブル対象**）。
我々の族は入力源を `free` にしていたので、そこだけ流儀が違う。
$N$ は「目標の祖先のうちペブル可能な頂点数」と定義しているので、
`revpebble.restrict_to_ancestors` を通してから数えれば両流儀で同じ意味になる。
"""

from __future__ import annotations

import csv
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import exp01b_engine as fast  # noqa: E402
from exp02_dags import edges_to_dag, enumerate_nonisomorphic  # noqa: E402
from revpebble import restrict_to_ancestors  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
CSV_PATH = ROOT / "data" / "families" / "dag_bound.csv"
FIELDS = ["n", "dag", "target", "N", "p", "mstar", "bound", "excess"]


def rows_for(n: int) -> list[dict]:
    """頂点数 `n` の非同型 DAG すべて × 全ての sink 目標 × 全ての $p$。"""
    out: list[dict] = []
    for idx, edges in enumerate(enumerate_nonisomorphic(n)):
        g = edges_to_dag(edges, n, name=f"d{n}_{idx}")
        for target in range(n):
            ga, t = restrict_to_ancestors(g, target)
            N = ga.n - len(ga.free)
            if N == 0:
                continue
            for p in range(1, N + 2):
                m = fast.mstar(ga, t, p)
                if m is None:
                    continue
                bound = 4 * N - 2 * min(p, N) - 1
                out.append({
                    "n": n, "dag": idx, "target": target, "N": N, "p": p,
                    "mstar": m, "bound": bound, "excess": (m - bound) // 2,
                })
    return out


def cmd_build(nmax: int) -> int:
    rows: list[dict] = []
    for n in range(1, nmax + 1):
        r = rows_for(n)
        bad = [x for x in r if x["mstar"] < x["bound"]]
        print(f"n={n}: {len(r)} 行 / 反例 {len(bad)}", flush=True)
        for b in bad[:5]:
            print(f"  反例 d{n}_{b['dag']} target={b['target']} N={b['N']} "
                  f"p={b['p']}: M*={b['mstar']} < {b['bound']}", flush=True)
        rows.extend(r)
    CSV_PATH.parent.mkdir(parents=True, exist_ok=True)
    with CSV_PATH.open("w", encoding="utf-8", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=FIELDS)
        w.writeheader()
        w.writerows(rows)
    bad = [x for x in rows if x["mstar"] < x["bound"]]
    tight = [x for x in rows if x["excess"] == 0]
    print(f"wrote {CSV_PATH}: {len(rows)} 行 / 反例 {len(bad)} / 等号 {len(tight)}")
    return 0


def cmd_verify() -> int:
    """反例が無いことだけを検査する（軽い）。"""
    if not CSV_PATH.exists():
        print("OK  dag_bound.csv はまだ無い（P1 未実施）")
        return 0
    bad = []
    n = 0
    with CSV_PATH.open(encoding="utf-8", newline="") as fh:
        for r in csv.DictReader(fh):
            n += 1
            if int(r["mstar"]) < int(r["bound"]):
                bad.append(f"d{r['n']}_{r['dag']} target={r['target']} p={r['p']}: "
                           f"M*={r['mstar']} < {r['bound']}")
    for b in bad[:10]:
        print(f"NG: {b}")
    if bad:
        return 1
    print(f"OK  小 DAG 全数 {n} 行で A* >= 2N-min(p,N) に反例なし")
    return 0


if __name__ == "__main__":
    import argparse

    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--build", action="store_true")
    ap.add_argument("--verify", action="store_true")
    ap.add_argument("--nmax", type=int, default=6)
    ns = ap.parse_args()
    if ns.build:
        raise SystemExit(cmd_build(ns.nmax))
    if ns.verify:
        raise SystemExit(cmd_verify())
    ap.print_help()
