#!/usr/bin/env python3
"""$T_{UG}(n,s) \\le 4n-2s$ の**構成的証明**と、そこから出る $\\theta(s)=\\theta(s-1)+s$。

    python3 upper_bound.py        # 補題4・k の選び方・恒等式を s=3..9 で検定

## 定理（上界。KSS Cor 4.12 の $\\le$ 方向＝構成側だけを使う）

$s\\ge2$、$s \\le n \\le \\theta(s) := s(s+1)/2$ のとき $T_{UG}(n,s) \\le 4n-2s$。

**補題4**: $k \\le s$ なら $T_{UP}(k,s) = 2k-1$。
（$v_1..v_{k-1}$ を置き $k-1$ 手、$v_k$ を外して 1 手、戻して $k-1$ 手。下界は
補題3 と同じ数え上げで、$v_k$ は外されるだけなので $2k-1$。）

**証明**（$s$ についての帰納法）。Cor 4.12 の右辺で $k$ を次のように選ぶ。

**(a) $s \\le n \\le \\theta(s-1)+1$ のとき $k=1$**:
$$2\\cdot1-1 + T_{UP}(1,s) + T_{UG}(n-1,s-1) = 2 + T_{UG}(n-1,s-1)
 \\le 2 + \\bigl(4(n-1)-2(s-1)\\bigr) = 4n-2s .$$
帰納法の仮定が使えるのは $s-1 \\le n-1 \\le \\theta(s-1)$、すなわち $s \\le n \\le \\theta(s-1)+1$。

**(b) $\\theta(s-1)+1 \\le n \\le \\theta(s)$ のとき $k = n-\\theta(s-1)$**:
このとき $n-k = \\theta(s-1)$ で固定され、帰納法の仮定から
$T_{UG}(\\theta(s-1),s-1) = 4\\theta(s-1)-2(s-1) = 2(s-1)^2$。
また $k = n-\\theta(s-1) \\le \\theta(s)-\\theta(s-1) = s$ なので**補題4 が使えて**
$T_{UP}(k,s)=2k-1$。よって
$$2k-1 + (2k-1) + 2(s-1)^2 = 4k-2+2(s-1)^2 = 4n-2s .$$

**基底**: $n=s$ で $T_{UG}(s,s)=2s=4s-2s$（補題3）。∎

## ここから θ が出る

(b) が使えるのは $k\\le s$ のとき、すなわち $n \\le \\theta(s-1)+s$ まで。ゆえに

$$\\boxed{\\ \\theta(s) = \\theta(s-1) + s\\ } \\quad\\Longrightarrow\\quad \\theta(s) = \\frac{s(s+1)}{2}$$

**$\\theta$ の $s(s+1)/2$ という形は「$1+2+\\cdots+s$ の телескоп」だった。**
$n$ がこれを超えると $k>s$ が必要になり、補題4 が使えず $T_{UP}(k,s)>2k-1$ に
なるので、1 頂点あたりのコストが 4 から 6 へ上がる。

**未決（下界）**: 上の $k$ 以外の選び方が $4n-2s$ を下回らないこと。
Cor 4.12 は厳密なので、これを示せば等号が確定する。
"""
from __future__ import annotations

import closed

INF = float("inf")


def theta(s: int) -> int:
    return s * (s + 1) // 2


def main() -> int:
    fails: list[str] = []
    n_lemma4 = n_k = n_id = 0

    for s in range(3, 10):
        # --- 補題4: k <= s なら T_UP(k,s) = 2k-1 ---
        for k in range(1, s + 1):
            n_lemma4 += 1
            if closed.T_UP(k, s) != 2 * k - 1:
                fails.append(f"補題4 破れ: T_UP({k},{s})={closed.T_UP(k, s)}（2k-1={2 * k - 1}）")

        # --- 定理の主張そのもの ---
        for n in range(s, theta(s) + 1):
            n_id += 1
            if closed.T_UG(n, s) != 4 * n - 2 * s:
                fails.append(f"定理 破れ: T_UG({n},{s})={closed.T_UG(n, s)}（4n-2s={4 * n - 2 * s}）")

        # --- 証明で選んだ k が実際に最小を与えるか ---
        for n in range(s + 1, theta(s) + 1):
            k_proof = 1 if n <= theta(s - 1) + 1 else n - theta(s - 1)
            val = 2 * k_proof - 1 + closed.T_UP(k_proof, s) + closed.T_UG(n - k_proof, s - 1)
            best = min(2 * k - 1 + closed.T_UP(k, s) + closed.T_UG(n - k, s - 1)
                       for k in range(1, n))
            n_k += 1
            if val != best or val != 4 * n - 2 * s:
                fails.append(f"k の選び方 破れ: n={n} s={s} k={k_proof} で {val}、"
                             f"最小は {best}、目標 {4 * n - 2 * s}")

        # --- theta の漸化 ---
        if theta(s) != theta(s - 1) + s:
            fails.append(f"theta({s}) != theta({s - 1})+{s}")

    print(f"補題4（T_UP(k,s)=2k-1, k<=s）: {n_lemma4} 点")
    print(f"定理（T_UG=4n-2s, s<=n<=theta(s)）: {n_id} 点")
    print(f"証明で選んだ k が最小を与える: {n_k} 点")
    print("theta(s) = theta(s-1) + s: s=3..9 で成立")
    if fails:
        print(f"\nNG {len(fails)} 件（先頭 10）:")
        for f in fails[:10]:
            print("  -", f)
        return 1
    print("\nすべて成立。上界の構成的証明は機械でも裏づけられた（残るは下界）")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
