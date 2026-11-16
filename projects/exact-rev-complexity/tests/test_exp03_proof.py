"""予想 A（現・定理 A）の証明の各ステップを実データで検査する。

    python3 tests/test_exp03_proof.py

証明の構造（`data/exp03_results.md` 2026-07-27b §A）:
  L1（剛性）  $M^*=2n-1$ のスケジュールでは各点 $1..n$ がちょうど 1 回 put され、
              $1..n-1$ がちょうど 1 回 take される。
  L2（順序）  ゆえに put は $1,2,\\dots,n$ の順に起きる。
  L3（消去数）不可逆消去の回数は $\\#\\{i\\in[2,n-1] : \\tau(i)>\\tau(i-1)\\}$（$\\tau$ の上昇数）。
  L4（連長）  $\\tau$ の極大下降連の長さは $p-1$ 以下。
  結論        消去数 $= (\\text{連数}) - 1 \\ge \\lceil (n-1)/(p-1)\\rceil - 1$。

L1〜L4 はすべて「実際に BFS が返す最適スケジュール」の上で検査できる。
ここが落ちれば証明が誤っている（または実装が誤っている）。
"""

from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import landauer as ld  # noqa: E402
import revpebble as rp  # noqa: E402

FAILURES: list[str] = []


def check(cond: bool, msg: str) -> None:
    if cond:
        print(f"  ok   {msg}")
    else:
        print(f"  FAIL {msg}")
        FAILURES.append(msg)


def eq(actual, expected, msg: str) -> None:
    check(actual == expected, f"{msg}: {actual!r} == {expected!r}")


def esat_formula(n: int, p: int) -> int:
    if n <= 1:
        return 0
    return -(-(n - 1) // (p - 1)) - 1


def test_structural_lemmas() -> None:
    """L1〜L4 を、飽和点ちょうどの最適スケジュール上で検査する。"""
    print("test_structural_lemmas (L1-L4)")
    for n in range(2, 15):
        for p in range(2, 8):
            e = esat_formula(n, p)
            seq = ld.landauer_schedule(rp.chain(n), n, p, e)
            if seq is None:
                continue
            a = ld.analyse_chain_schedule(n, seq)
            eq(a["moves"], 2 * n - 1, f"n={n} p={p} e={e} 手数 = 2n-1")
            check(a["rigid"], f"n={n} p={p} L1 剛性（各点 1 回 put / 1..n-1 が 1 回 take）")
            check(a["puts_sorted"], f"n={n} p={p} L2 put は昇順")
            eq(a["erasures"], a["ascents"], f"n={n} p={p} L3 消去数 = τ の上昇数")
            if a["runs"]:
                check(
                    max(a["runs"]) <= p - 1,
                    f"n={n} p={p} L4 極大下降連の長さ <= p-1（実測 {a['runs']}）",
                )
                eq(len(a["runs"]) - 1, a["erasures"], f"n={n} p={p} 連数-1 = 消去数")


def test_lemma4_is_tight_and_forced() -> None:
    """L4 の $p-1$ が真に必要（$p$ ではない）ことを、より少ない消去が不可能なことで確認。

    もし連長が $p$ まで許されるなら $e^* = \\lceil (n-1)/p\\rceil - 1$ になるはずで、
    多くの $(n,p)$ でそれは実測より小さい。その差が L4 の $-1$ の効き目である。
    """
    print("test_lemma4_is_tight_and_forced")
    diff_seen = 0
    for n in range(4, 16):
        for p in range(2, 8):
            want = esat_formula(n, p)
            weaker = -(-(n - 1) // p) - 1  # 連長 p を許した場合の（誤った）値
            budget = n + 1
            prof = ld.landauer_profile(rp.chain(n), n, p, budget)
            if prof[budget] is None:
                continue
            eq(ld.saturation(prof), want, f"n={n} p={p} e* = ceil((n-1)/(p-1))-1")
            if weaker < want:
                diff_seen += 1
                check(
                    prof[weaker] is None or prof[weaker] > 2 * n - 1,
                    f"n={n} p={p} 連長 p を許した値 e={weaker} では 2n-1 に届かない",
                )
    check(diff_seen >= 10, f"L4 の -1 が効く事例が十分ある（{diff_seen} 件）")


def test_upper_bound_construction() -> None:
    """定理 A の上界（構成）を明示的に組み立てて、規則を満たすことを検証する。

    構成: フロンティアを $p-1$ ずつ前進させる。各区間で
    「$p-1$ 本を連続配置 → 逆順に可逆で剥がす → 前区間の踏み台を 1 回だけ不可逆消去」。
    """
    print("test_upper_bound_construction")
    for n in range(2, 22):
        for p in range(2, 8):
            seq = _construct(n, p)
            ok, why = _simulate(n, p, seq)
            check(ok, f"n={n} p={p} 構成が規則を満たす（{why}）")
            if ok:
                eq(len(seq), 2 * n - 1, f"n={n} p={p} 構成の手数 = 2n-1")
                eq(
                    sum(1 for a, _v in seq if a == "erase"),
                    esat_formula(n, p),
                    f"n={n} p={p} 構成の消去回数 = ceil((n-1)/(p-1))-1",
                )


def _construct(n: int, p: int) -> list[tuple[str, int]]:
    """定理 A の上界の構成を明示的に生成する。

    証明の言葉どおりに組む: **取り除かれる点の集合 $[1,n-1]$ を長さ $\\le p-1$ の
    ブロックに分割**し、ブロック $[a,b]$ ごとに
    「$b+1$ まで置く → $b$ から $a$ へ降順に外す」を行う。降順なので $a+1..b$ は可逆に外れ、
    ブロック先頭 $a$ だけが（$a-1$ が前ブロックで外れているため）不可逆消去になる。
    第 1 ブロックの先頭は $a=1$ で、$a-1=0$ が常時可用なので消去にならない。
    → 消去回数 = ブロック数 $-1 = \\lceil (n-1)/(p-1)\\rceil - 1$。
    """
    seq: list[tuple[str, int]] = []
    placed = 0  # これまでに put した最大の頂点番号
    a = 1
    while a <= n - 1:
        b = min(a + (p - 1) - 1, n - 1)
        for v in range(placed + 1, b + 2):  # b+1 まで置く（put は昇順）
            seq.append(("put", v))
        placed = max(placed, b + 1)
        for v in range(b, a - 1, -1):  # b から a へ降順に外す
            seq.append(("erase" if v > 1 and v - 1 < a else "take", v))
        a = b + 1
    for v in range(placed + 1, n + 1):  # n=1 など、まだ置いていない分
        seq.append(("put", v))
    return seq


def _simulate(n: int, p: int, seq: list[tuple[str, int]]) -> tuple[bool, str]:
    """スケジュールがゲームの規則（先行点条件・ピーク・clean 終端）を満たすか検証する。"""
    state: set[int] = set()
    peak = 0
    for act, v in seq:
        ready = (v - 1) == 0 or (v - 1) in state
        if act == "put":
            if not ready:
                return False, f"put({v}) の先行点が未ペブル"
            if v in state:
                return False, f"put({v}) は既にペブル済み"
            state.add(v)
            peak = max(peak, len(state))
            if len(state) > p:
                return False, f"ピーク超過 {len(state)} > {p}"
        elif act == "take":
            if v not in state:
                return False, f"take({v}) は未ペブル"
            if not ready:
                return False, f"take({v}) は可逆でない（先行点が未ペブル）"
            state.discard(v)
        else:  # erase
            if v not in state:
                return False, f"erase({v}) は未ペブル"
            if ready:
                return False, f"erase({v}) は実は可逆（消去に数える必要がない）"
            state.discard(v)
    if state != {n}:
        return False, f"clean でない終端 {sorted(state)}"
    return True, f"peak={peak}"


def main() -> int:
    for fn in (
        test_upper_bound_construction,
        test_structural_lemmas,
        test_lemma4_is_tight_and_forced,
    ):
        fn()
    print()
    if FAILURES:
        print(f"FAILED: {len(FAILURES)} 件")
        for m in FAILURES[:20]:
            print("  -", m)
        return 1
    print("all tests passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
