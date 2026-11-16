"""幅 2 円筒のスケジュールを**構成する**（上界を取るため）。

## 着想（V1 の検問点構造から）

`cylinder(2,h)` では、レベル $i$ の 2 頂点はどちらも**レベル $i-1$ の 2 頂点の両方**を
先行点に持つ（$k=2$ なので $(j-1)\\bmod 2$ と $j$ が両方を尽くす）。したがって

> **レベルを 1 つの「超頂点」と見ると、幅 2 円筒はちょうど長さ $h$ の鎖である。**

祖先に制限すると、レベル $i$（$1\\le i\\le h-1$）は 2 頂点、**レベル $h$ は 1 頂点**
（終端だけ）、レベル 0 は free の 2 頂点になる。

そこで**鎖の最適スケジュールを持ち上げる**:

| 鎖の手 | 円筒の手 |
|---|---|
| `put v`（$v<h$） | `put 2v`, `put 2v+1` |
| `take v`（$v<h$） | `take 2v+1`, `take 2v` |
| `put h` / `take h` | `put 2h` / `take 2h`（終端は 1 頂点） |

持ち上げが合法なのは、レベル $v$ の頂点を置く／取るのに要るのが
**レベル $v-1$ が丸ごと載っていること**だけで、それは鎖の側の条件そのものだからである。

## これで何が言えるか

鎖の到達長は $\\mathrm{reach}(P)=2^{P-1}$（KF-03。Královič 2001 Thm 3.1 の系で**既知**）。
したがって長さ $h$ の鎖は $P=\\lceil\\log_2 h\\rceil+1$ 個のペブルで clean に計算でき、
持ち上げると**レベルが 2 頂点ずつなのでピークは $2P$** になる。すなわち

$$p_{\\min}(\\mathrm{cyl}(2,h)) \\le 2\\lceil\\log_2 h\\rceil + 2$$

が**すべての $h$ について**従う（有界事例の検証ではなく、鎖の既知定理からの帰結）。

## ⚠️ ただし予想には 1 だけ届いていない

`data/families/findings.md` §3.8.1 の予想（実測値）は
$p_{\\min}=2\\lceil\\log_2 h\\rceil+1$ であり、**この構成は 1 だけ大きい**。
差は $h\\ge4$ の全てでちょうど 1（$h=4$: 構成 6・実測 5）。

当初この docstring は「持ち上げのピークは $2P-1$」と書いていたが**誤りだった**。
$2P-1$ になるのはピークの瞬間に終端レベル（1 頂点しかない）が載っているときだけで、
鎖の最適スケジュールを機械的に持ち上げてもそうなるとは限らない。

→ **真の最適は、この持ち上げが取りこぼしている 1 個をどこかで節約している。**
どこかを特定するのが次の単位である。

**下界は別である。** 上界が構成で取れても予想全体はまだ予想のままである
（下界の全数確認は $h=17$ まで）。
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import exp01b_engine as fast  # noqa: E402
import revpebble as rp  # noqa: E402
from families import anc, cylinder  # noqa: E402


def lift(h: int, chain_seq: list[tuple[str, int]]) -> list[tuple[str, int]]:
    """鎖のスケジュールを幅 2 円筒へ持ち上げる。

    祖先に制限した `cylinder(2,h)` の番号づけ:
    レベル $i$（$1\\le i\\le h-1$）= 頂点 $2i, 2i+1$、レベル $h$ = 頂点 $2h$、
    レベル 0（free）= 頂点 $0,1$。
    （元の番号 $2h+1$ が制限後に $2h$ へ詰まることに注意。）
    """
    out: list[tuple[str, int]] = []
    for kind, v in chain_seq:
        if v == h:
            out.append((kind, 2 * h))
        elif kind == "put":
            out.extend([("put", 2 * v), ("put", 2 * v + 1)])
        else:
            out.extend([("take", 2 * v + 1), ("take", 2 * v)])
    return out


def peak(seq: list[tuple[str, int]]) -> int:
    cur = mx = 0
    for kind, _ in seq:
        cur += 1 if kind == "put" else -1
        mx = max(mx, cur)
    return mx


def construct(h: int, p_chain: int) -> tuple[list[tuple[str, int]], int] | None:
    """鎖を `p_chain` 個のペブルで解いて持ち上げる。(スケジュール, ピーク) を返す。

    鎖が `p_chain` で到達不能なら `None`。
    """
    g = rp.chain(h)
    seq = fast.schedule(g, h, p_chain)
    if seq is None:
        return None
    lifted = lift(h, seq)
    return lifted, peak(lifted)


def chain_pmin(h: int) -> int:
    """$\\lceil\\log_2 h\\rceil+1$（KF-04）。"""
    return (h - 1).bit_length() + 1


def upper_bound(h: int) -> int:
    """持ち上げ構成の**上界** $2\\lceil\\log_2 h\\rceil+2 = 2P$。

    $h\\ge4$ では**この値ちょうど**が達成される。$h=2,3$ では構成のほうが 1 小さい
    （$h=2$: 3、$h=3$: 5）ので、達成値そのものではなく上界として使うこと。
    実測の p_min より 1 大きい（module docstring の但し書きを参照）。"""
    return 2 * chain_pmin(h)


def check(h: int) -> dict:
    """1 つの `h` について構成し、検証器を通し、上界と突き合わせる。"""
    ga, t = anc(cylinder(2, h))
    r = construct(h, chain_pmin(h))
    if r is None:
        return {"h": h, "ok": False, "why": "鎖が到達不能"}
    seq, pk = r
    fast.verify_schedule(ga, t, pk, seq)  # 失敗すれば AssertionError
    return {"h": h, "ok": True, "peak": pk, "bound": upper_bound(h), "moves": len(seq)}


if __name__ == "__main__":
    import csv

    hi = int(sys.argv[1]) if len(sys.argv) > 1 else 24
    ledger: dict[int, tuple[int, int]] = {}
    with (Path(__file__).resolve().parents[1] / "data/families/atlas.csv").open(
        encoding="utf-8", newline=""
    ) as fh:
        for row in csv.DictReader(fh):
            if row["family"] == "cylinder" and row["status"] == "exhaustive":
                k, hh = (int(x) for x in row["params"].split(":"))
                if k == 2 and row["p"] == row["pmin"]:
                    ledger[hh] = (int(row["pmin"]), int(row["mstar"]))
    print(f"{'h':>3} {'構成のピーク':>7} {'上界':>5} {'台帳 p_min':>9} {'構成の手数':>7} {'台帳 M*':>7}")
    for h in range(2, hi + 1):
        r = check(h)
        if not r["ok"]:
            print(f"{h:>3}  {r['why']}")
            continue
        lp, lm = ledger.get(h, ("—", "—"))
        print(f"{h:>3} {r['peak']:>7} {r['bound']:>5} {str(lp):>9} {r['moves']:>7} {str(lm):>7}")
