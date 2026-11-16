"""holonomic guessing — 数列から P-recursive な漸化式を「確証つきで」推測する。

## なぜ必要か

`docs/00_overview.md` §2.1 のとおり、本プロジェクトでは少数点の当てはめが**4回連続で崩壊**した
（うち1件は OEIS の既知列に4点一致したが5点目で消滅）。原因は手法の弱さである:
素朴な多項式・指数の当てはめには「何点あれば信用してよいか」の基準が無い。

P-recursive（holonomic）な漸化式

    sum_{i=0..r} p_i(n) * a(n+i) = 0,   p_i は次数 <= d の多項式

を仮定すると、未知数は (r+1)(d+1) 個の線形方程式系になる。
**未知数の個数が分かる**ので、「確証に必要な余剰式の本数」を定量的に言える。
これが当てはめとの決定的な違いであり、本モジュールの存在理由である。

## 方針

- 厳密整数演算のみ（`fractions.Fraction`）。外部依存なし（sympy / ore_algebra 不要）。
- (r, d) を小さい順に走査し、**最小の (r, d)** で非自明解が出たものを採る。
- 解を得た後、**推測に使わなかった項（held-out）で必ず検証**する。
  held-out が足りない場合は「推測しない」（None を返す）。これが最重要の安全弁。

## 限界（正直に）

- ここで得られるのは**推測**であって証明ではない。証明には creative telescoping か、
  組合せ的な直接証明が要る。ただし「漸化式の形」が分かれば証明の的が定まる。
- P-recursive でない数列（例: 素数列、2^(2^n) 型）は原理的に見つからない。
  見つからないこと自体は「holonomic でない」証拠にはならない（探索範囲の問題）。
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from math import gcd


@dataclass(frozen=True)
class Recurrence:
    """sum_{i,j} coeffs[(i,j)] * n^j * a(n+i) = 0 （n は 0 始まりの添字）。"""

    order: int
    degree: int
    coeffs: dict[tuple[int, int], int]

    def apply(self, seq: list[int], n: int) -> int:
        """添字 n における左辺の値。seq[n+order] まで参照する。"""
        total = 0
        for (i, j), c in self.coeffs.items():
            if c:
                total += c * (n**j) * seq[n + i]
        return total

    def poly_str(self, i: int) -> str:
        terms = []
        for j in range(self.degree, -1, -1):
            c = self.coeffs.get((i, j), 0)
            if not c:
                continue
            if j == 0:
                terms.append(f"{c:+d}")
            elif j == 1:
                terms.append(f"{c:+d}*n")
            else:
                terms.append(f"{c:+d}*n^{j}")
        return "(" + " ".join(terms) + ")" if terms else "0"

    def __str__(self) -> str:
        parts = []
        for i in range(self.order + 1):
            p = self.poly_str(i)
            if p != "0":
                parts.append(f"{p}*a(n+{i})" if i else f"{p}*a(n)")
        return " + ".join(parts) + " = 0"


def min_terms_needed(order: int, degree: int, slack: int = 3) -> int:
    """(order, degree) の漸化式を slack 本の余剰式つきで確証するのに要る項数。

    未知数 (order+1)(degree+1) 個 → 同数の式で解け、さらに slack 本の独立な式が
    成り立って初めて「偶然ではない」と言える。式1本が seq[n..n+order] を使うので
    項数は式の本数 + order。
    """
    unknowns = (order + 1) * (degree + 1)
    return unknowns + slack + order


def _nullspace_vector(rows: list[list[Fraction]], ncols: int) -> list[Fraction] | None:
    """有理数行列の零空間から非自明ベクトルを1本返す（無ければ None）。"""
    mat = [row[:] for row in rows]
    pivot_of_col: dict[int, int] = {}
    r = 0
    for c in range(ncols):
        piv = None
        for k in range(r, len(mat)):
            if mat[k][c] != 0:
                piv = k
                break
        if piv is None:
            continue
        mat[r], mat[piv] = mat[piv], mat[r]
        inv = mat[r][c]
        mat[r] = [x / inv for x in mat[r]]
        for k in range(len(mat)):
            if k != r and mat[k][c] != 0:
                f = mat[k][c]
                mat[k] = [x - f * y for x, y in zip(mat[k], mat[r])]
        pivot_of_col[c] = r
        r += 1
        if r == len(mat):
            break

    free = [c for c in range(ncols) if c not in pivot_of_col]
    if not free:
        return None
    f0 = free[0]
    vec = [Fraction(0)] * ncols
    vec[f0] = Fraction(1)
    for c, row in pivot_of_col.items():
        vec[c] = -mat[row][f0]
    return vec


def _to_primitive_ints(vec: list[Fraction]) -> list[int]:
    """有理ベクトルを、内容が 1 の整数ベクトルに正規化する。"""
    den = 1
    for x in vec:
        den = den * x.denominator // gcd(den, x.denominator)
    ints = [int(x * den) for x in vec]
    g = 0
    for v in ints:
        g = gcd(g, abs(v))
    if g > 1:
        ints = [v // g for v in ints]
    for v in ints:  # 符号を正規化（最初の非零を正に）
        if v != 0:
            if v < 0:
                ints = [-v2 for v2 in ints]
            break
    return ints


def verify(rec: Recurrence, seq: list[int], start: int = 0) -> bool:
    """漸化式が seq 全域（参照可能な範囲）で成り立つか。"""
    ok_any = False
    for n in range(start, len(seq) - rec.order):
        if rec.apply(seq, n) != 0:
            return False
        ok_any = True
    return ok_any


def guess(
    seq: list[int],
    *,
    max_order: int = 4,
    max_degree: int = 4,
    min_slack: int = 3,
) -> Recurrence | None:
    """数列から最小の (order, degree) の P-recursive 漸化式を推測する。

    min_slack: 推測に使わずに取っておく検証用の式の本数（held-out）。
    これを満たせないときは **推測しない**（None）。当てはめ崩壊の再発防止。
    """
    n_terms = len(seq)
    for total in range(0, max_order + max_degree + 1):
        for order in range(0, min(total, max_order) + 1):
            degree = total - order
            if degree > max_degree or order < 1 and degree < 1:
                continue
            unknowns = (order + 1) * (degree + 1)
            n_eqs_avail = n_terms - order
            if n_eqs_avail < unknowns + min_slack:
                continue  # 確証に足る式が無い → この (order,degree) は評価しない

            # 推測に使う式は unknowns 本だけ。残りは held-out 検証に回す。
            n_fit = unknowns
            rows: list[list[Fraction]] = []
            for n in range(n_fit):
                row = [
                    Fraction((n**j) * seq[n + i])
                    for i in range(order + 1)
                    for j in range(degree + 1)
                ]
                rows.append(row)
            vec = _nullspace_vector(rows, unknowns)
            if vec is None:
                continue
            ints = _to_primitive_ints(vec)
            if all(v == 0 for v in ints):
                continue
            coeffs = {}
            idx = 0
            for i in range(order + 1):
                for j in range(degree + 1):
                    coeffs[(i, j)] = ints[idx]
                    idx += 1
            # 先頭係数が全て 0 なら order が実は小さい → 冗長解として棄却
            if all(coeffs.get((order, j), 0) == 0 for j in range(degree + 1)):
                continue
            rec = Recurrence(order=order, degree=degree, coeffs=coeffs)
            # held-out 検証（推測に使わなかった全ての n で成り立つこと）
            if not verify(rec, seq):
                continue
            return rec
    return None


def affordable(
    n_terms: int, *, max_order: int = 4, max_degree: int = 4, min_slack: int = 3
) -> list[tuple[int, int]]:
    """この項数で「確証つきで評価できた」(order, degree) の組を列挙する。

    見つからなかったときに**どこまで探せたのか**を報告するために使う。
    ここに現れない (r,d) は「探索していない」のであって「存在しない」ではない。
    """
    out = []
    for order in range(1, max_order + 1):
        for degree in range(0, max_degree + 1):
            if n_terms - order >= (order + 1) * (degree + 1) + min_slack:
                out.append((order, degree))
    return out


def report(name: str, seq: list[int], **kw) -> str:
    """1 数列分の判定を人間可読な 1 ブロックにする。"""
    rec = guess(seq, **kw)
    head = f"### {name}\n\n`{seq[:12]}{'...' if len(seq) > 12 else ''}` （{len(seq)} 項）\n\n"
    if rec is None:
        pairs = affordable(len(seq), **{k: v for k, v in kw.items() if k != "min_slack"})
        if not pairs:
            return head + (
                "**判定不能**: 項数が足りず、確証つきで評価できた $(order, degree)$ が1つも無い。\n"
                "→ 数列を伸ばすこと。当てはめてはいけない。\n"
            )
        maxo = max(o for o, _ in pairs)
        maxd = max(d for _, d in pairs)
        return head + (
            f"**漸化式は見つからなかった。** 確証つきで評価できたのは {len(pairs)} 組"
            f"（$order \\le {maxo}$, $degree \\le {maxd}$ の範囲内）。\n"
            "→ この範囲に低階の P-recursive 漸化式は無い。"
            "範囲外にある可能性は排除していない。\n"
        )
    unknowns = (rec.order + 1) * (rec.degree + 1)
    held_out = len(seq) - rec.order - unknowns
    return head + (
        f"- **推測**: `{rec}`\n"
        f"- order = {rec.order}, degree = {rec.degree}, 未知数 = {unknowns}\n"
        f"- 推測に使った式 {unknowns} 本、**held-out 検証 {held_out} 本すべて成立**\n"
    )


if __name__ == "__main__":  # 手動確認用
    fib = [0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233, 377, 610]
    print(report("Fibonacci（健全性確認）", fib))
