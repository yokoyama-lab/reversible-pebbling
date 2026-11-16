#!/usr/bin/env python3
"""候補10（最小ガベージ）の回帰テスト。依存は標準ライブラリのみ。

テストファースト: ここに書いた期待値は、実装より先に紙で決めたもの。
- 情報論的下界 lb(f) = ceil(log2 max_y |f^{-1}(y)|)
- 自由ガベージ模型の最小幅 g_free(f)（ガベージ値を任意に割り当ててよい）
- 射影ガベージ模型の最小幅 g_proj(f)（ガベージは入力ビットの部分集合のみ）
- ゲート引数個数制約下のパリティ（arity < N のゲートは偶置換を誘導する）

実行: python3 tests/test_exp10_garbage.py
"""

import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "scripts"))

from exp10_garbage import (  # noqa: E402
    g_proj_subcube,
    gate_permutation,
    generated_group_size,
    g_free,
    g_free_bruteforce,
    g_proj,
    lower_bound,
    perm_sign,
    truth_table,
)

FAILS = []


def check(name, got, want):
    if got != want:
        FAILS.append(f"{name}: got {got!r}, want {want!r}")
        print(f"  NG {name}: got {got!r}, want {want!r}")
    else:
        print(f"  ok {name} = {got!r}")


# ---------------------------------------------------------------- 具体関数
# n=3 の代表的な1出力関数。tt[x] = f(x)、x は 3 ビット整数（LSB = ビット0）。
MAJ3 = truth_table(3, lambda b: 1 if sum(b) >= 2 else 0)
XOR3 = truth_table(3, lambda b: sum(b) % 2)
AND3 = truth_table(3, lambda b: 1 if all(b) else 0)
CONST0 = truth_table(3, lambda b: 0)
ID3 = tuple(range(8))  # n=3, m=3 の恒等写像（単射）


def test_lower_bound():
    print("[lower_bound]")
    # MAJ3 のファイバーはどちらも 4 元 → ceil(log2 4) = 2
    check("lb(MAJ3)", lower_bound(MAJ3), 2)
    check("lb(XOR3)", lower_bound(XOR3), 2)
    # AND3 は f^{-1}(0) が 7 元 → ceil(log2 7) = 3
    check("lb(AND3)", lower_bound(AND3), 3)
    check("lb(CONST0)", lower_bound(CONST0), 3)
    # 単射なら 0
    check("lb(ID3)", lower_bound(ID3), 0)


def test_g_free_equals_lower_bound():
    print("[g_free] 自由ガベージ模型では下界と一致する（自明性の主張）")
    for name, tt in [("MAJ3", MAJ3), ("XOR3", XOR3), ("AND3", AND3),
                     ("CONST0", CONST0), ("ID3", ID3)]:
        check(f"g_free({name}) == lb({name})", g_free(tt), lower_bound(tt))
    print("[g_free] 素朴な全数探索（二重実装照合）")
    for name, tt in [("MAJ3", MAJ3), ("XOR3", XOR3), ("AND3", AND3), ("ID3", ID3)]:
        check(f"g_free_bruteforce({name})", g_free_bruteforce(tt), g_free(tt))


def test_g_proj():
    print("[g_proj] 射影ガベージ模型（Bennett 型で入力ビットの一部だけ残す）")
    # MAJ3: 2 ビット残しでは不十分。x1=x2 のとき多数決は x3 を決めない。
    check("g_proj(MAJ3)", g_proj(MAJ3, 3), 3)
    # XOR3: パリティと任意の 2 ビットから残り 1 ビットが決まる。
    check("g_proj(XOR3)", g_proj(XOR3, 3), 2)
    # AND3: 定数 0 側が 7 元 → 3 ビット全部必要。
    check("g_proj(AND3)", g_proj(AND3, 3), 3)
    check("g_proj(CONST0)", g_proj(CONST0, 3), 3)
    check("g_proj(ID3)", g_proj(ID3, 3), 0)
    print("[g_proj] 二重実装照合（部分キューブ単射性による独立実装）")
    for name, tt in [("MAJ3", MAJ3), ("XOR3", XOR3), ("AND3", AND3),
                     ("CONST0", CONST0), ("ID3", ID3)]:
        check(f"g_proj_subcube({name})", g_proj_subcube(tt, 3), g_proj(tt, 3))
    print("[g_proj] 下界は常に g_proj 以下（射影は自由ガベージの特殊形）")
    check("lb(MAJ3) < g_proj(MAJ3)", lower_bound(MAJ3) < g_proj(MAJ3, 3), True)


def test_parity_of_low_arity_gates():
    print("[parity] arity < N のゲートは {0,1}^N の偶置換を誘導する")
    # N=3、対象線 targets 上に {0,1}^k の任意の置換を載せたゲート。
    # k < N なら 2^{N-k} >= 2 個のブロックのコピーになるので符号は +1。
    n_checked = 0
    for N in (2, 3, 4):
        for k in range(1, N):
            import itertools

            for targets in itertools.permutations(range(N), k):
                for perm in itertools.permutations(range(1 << k)):
                    p = gate_permutation(N, targets, perm)
                    if perm_sign(p) != 1:
                        FAILS.append(f"parity: N={N} targets={targets} perm={perm} は奇置換")
                        return
                    n_checked += 1
    print(f"  ok すべて偶置換（{n_checked} 個のゲートを検査）")
    # 全線に作用するゲート（k=N）は奇置換になりうる（対照実験）
    swap01 = gate_permutation(3, (0, 1, 2), (1, 0, 2, 3, 4, 5, 6, 7))
    check("k=N の互換は奇置換", perm_sign(swap01), -1)


def test_nct_group_on_3_lines():
    print("[NCT] 3 線上の NOT/CNOT/Toffoli 生成群")
    size, all_even = generated_group_size(3)
    # 事前に紙で決まる上界: パリティ定理から A_8 に含まれる（Toffoli は 3 線=全線だが
    # {0,1}^3 上では 1 個の互換の 2^0=1 コピー…ではなく 1 個の互換なので奇に見える。
    # 実際 Toffoli(x1,x2;x3) は (110)<->(111) の 1 互換で奇置換。よって A_8 に留まらない。
    # したがって上界は |S_8| = 40320。ここは測定値を記録する。
    check("生成群は S_8 に含まれる", size <= 40320, True)
    print(f"  測定: |<NOT,CNOT,Toffoli> on 3 lines| = {size}, all_even={all_even}")
    # 測定後に固定した回帰値
    check("生成群の位数（測定値・回帰用）", size, 40320)
    check("奇置換を含む", all_even, False)


def main():
    test_lower_bound()
    test_g_free_equals_lower_bound()
    test_g_proj()
    test_parity_of_low_arity_gates()
    test_nct_group_on_3_lines()
    print()
    if FAILS:
        print(f"FAILED ({len(FAILS)})")
        for f in FAILS:
            print("  -", f)
        return 1
    print("all tests passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
