"""候補5（可逆 Busy Beaver）の回帰テスト。pytest 不要。

    python3 tests/test_exp05_revbb.py

方針: **まず通常 BB の既知値を自分のシミュレータ／枚挙器で再現する**。
これが実装の妥当性検証であり、可逆側の数値を信じる前提条件である。
"""

import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "scripts"))

import revbb  # noqa: E402
from revbb import (HALT, L, R, enumerate_quadruple, enumerate_quintuple,  # noqa: E402
                   parse_quintuple, quadruple_reversible,
                   quintuple_reversible, run_quintuple)

FAIL = []


def check(name, got, want):
    if got == want:
        print(f"  ok   {name}: {got}")
    else:
        print(f"  FAIL {name}: got {got!r}, want {want!r}")
        FAIL.append(name)


# --------------------------------------------------- 1. 可逆性判定の単体テスト

def test_reversibility_predicate():
    print("[1] 五つ組の可逆性条件")
    # BB(2) champion 1RB1LB_1LA1RZ: 状態 B に入る規則は (A,0)=1RB と (B,0)=1LB。
    # 方向が R と L で異なるので配置レベルでは可逆でない。
    rules, _ = parse_quintuple("1RB1LB_1LA1RZ")
    check("BB(2) champion は可逆でない", quintuple_reversible(rules), False)
    # 三つ組としての単射性は満たす（(q',b,d) が全て相異なる）ことを確認し、
    # 「三つ組の単射性 ≠ 配置レベルの可逆性」を明示する。
    images = list(rules.values())
    check("しかし三つ組としては単射", len(set(images)) == len(images), True)

    # 同じ状態に同じ方向・同じ記号で二本入るのは不可
    bad = {(0, 0): (1, 1, R), (0, 1): (1, 1, R)}
    check("同方向・同記号の二本入りは不可", quintuple_reversible(bad), False)
    # 同じ状態に同じ方向・異なる記号なら可
    good = {(0, 0): (1, 1, R), (0, 1): (1, 0, R)}
    check("同方向・異記号の二本入りは可", quintuple_reversible(good), True)

    print("[1b] 四つ組（Morita 流）の可逆性条件")
    check("書き込み型と移動型の混在入りは不可",
          quadruple_reversible({(0, 0): (1, 1)}, {2: (1, R)}), False)
    # 移動規則は記号を書かないので、逆向きに「どちらから来たか」を読み取る材料が無い。
    # よって移動型が入る状態は、入り規則がその1本だけでなければならない（方向が
    # 違っても2本は不可）。この点を取り違えると単射性が破れる（下の [7] で検出される）。
    check("移動型・異方向の二本入りも不可",
          quadruple_reversible({}, {0: (1, R), 2: (1, L)}), False)
    check("移動型・同方向の二本入りは不可",
          quadruple_reversible({}, {0: (1, R), 2: (1, R)}), False)
    check("移動型の一本入りは可", quadruple_reversible({}, {0: (1, R)}), True)
    check("書き込み型・異記号の二本入りは可",
          quadruple_reversible({(0, 0): (1, 0), (2, 0): (1, 1)}, {}), True)
    check("書き込み型・同記号の二本入りは不可",
          quadruple_reversible({(0, 0): (1, 1), (2, 0): (1, 1)}, {}), False)


# --------------------------------------------------- 2. シミュレータの検証

def test_simulator_known_machines():
    print("[2] 既知チャンピオン機械の直接シミュレーション")
    # 通常 BB のチャンピオン（bbchallenge 標準形式）
    for name, text, steps, ones in [
        ("BB(2) 1RB1LB_1LA1RZ", "1RB1LB_1LA1RZ", 6, 4),
        ("BB(3) 1RB1RZ_1LB0RC_1LC1LA", "1RB1RZ_1LB0RC_1LC1LA", 21, 5),
        ("BB(4) 1RB1LB_1LA0LC_1RZ1LD_1RD0RA", "1RB1LB_1LA0LC_1RZ1LD_1RD0RA", 107, 13),
    ]:
        rules, _k = parse_quintuple(text)
        res = run_quintuple(rules, 10_000)
        check(f"{name} status", res["status"], "halt")
        check(f"{name} steps", res["steps"], steps)
        check(f"{name} ones", res["ones"], ones)


def test_wiki_reversible_champions():
    print("[3] bbchallenge wiki の可逆チャンピオンを独立に検証")
    for k, text, steps in [
        (2, "0RB1RZ_1LA1RB", 6),
        (3, "0RB1RZ_0LC1RA_1RB1LC", 17),
        (4, "1RB0LD_0LC0RB_1LA1LD_1LC1RZ", 48),
        (5, "1RB0RD_1RC0RB_1RD1RZ_1LE1LA_0LE0LA", 388),
    ]:
        rules, kk = parse_quintuple(text)
        check(f"k={k} 状態数", kk, k)
        check(f"k={k} 可逆性", quintuple_reversible(rules), True)
        res = run_quintuple(rules, 10_000)
        check(f"k={k} status", res["status"], "halt")
        check(f"k={k} steps", res["steps"], steps)


# --------------------------------------------------- 3. 枚挙器の検証（通常 BB）

def test_ordinary_bb_enumeration():
    print("[4] 通常 BB の枚挙による再現（実装の妥当性検証）")
    # BB(2)=6, BB(3)=21 なので上限 400 で最大値の再現には十分
    # （未判定台数は駆動スクリプト側でより大きな上限で数える）。
    s2 = enumerate_quintuple(2, 400, reversible=False)
    check("BB(2)", s2["best_steps"], 6)
    check("Sigma(2)", s2["best_ones"], 4)
    s3 = enumerate_quintuple(3, 400, reversible=False)
    check("BB(3)", s3["best_steps"], 21)
    check("Sigma(3)", s3["best_ones"], 6)


def test_ordinary_bb4_enumeration():
    print("[5] 通常 BB(4) の枚挙による再現（やや重い）")
    # BB(4)=107 なので上限 1000 で最大値の再現には十分。上限を上げると非停止機械が
    # 上限まで走るので急激に重くなる（未判定台数の集計は駆動スクリプト側で行う）。
    s4 = enumerate_quintuple(4, 1_000, reversible=False)
    check("BB(4)", s4["best_steps"], 107)
    check("Sigma(4)", s4["best_ones"], 13)


# --------------------------------------------------- 4. 可逆側

def test_reversible_quintuple():
    print("[6] 可逆 BB / 五つ組の全数枚挙（k=1..3。k=4,5 は EXP05_SLOW）")
    # 確定値（未判定 0 台で全数判定済み）。k=2..5 は bbchallenge wiki と一致。
    for k, steps, ones, machines in [(1, 1, 1, 3), (2, 6, 2, 24),
                                     (3, 17, 4, 418)]:
        s = enumerate_quintuple(k, 1_000, reversible=True)
        check(f"BBrev({k})", s["best_steps"], steps)
        check(f"Sigma_rev({k})", s["best_ones"], ones)
        check(f"k={k} 枚挙台数", s["machines"], machines)
        check(f"k={k} 未判定台数", s["undecided"], 0)
        check(f"k={k} 巡回はすべて初期配置に戻る", s["cycle_not_initial"], 0)


def test_reversible_quintuple_slow():
    print("[6b] 可逆 BB / 五つ組 k=4,5（k=5 は約3分）")
    for k, steps, ones, machines in [(4, 48, 8, 11871), (5, 388, 16, 451479)]:
        s = enumerate_quintuple(k, 3_000, reversible=True)
        check(f"BBrev({k})", s["best_steps"], steps)
        check(f"Sigma_rev({k})", s["best_ones"], ones)
        check(f"k={k} 枚挙台数", s["machines"], machines)
        check(f"k={k} 未判定台数", s["undecided"], 0)
        check(f"k={k} 巡回はすべて初期配置に戻る", s["cycle_not_initial"], 0)


def test_reversible_quadruple():
    print("[6c] 可逆 BB / 四つ組（Morita 流）の全数枚挙 k=1..4")
    for k, steps, ones, machines in [(1, 2, 1, 8), (2, 4, 1, 70),
                                     (3, 6, 2, 706), (4, 12, 2, 9343)]:
        s = enumerate_quadruple(k, 2_000, reversible=True)
        check(f"BBrev4({k})", s["best_steps"], steps)
        check(f"Sigma_rev4({k})", s["best_ones"], ones)
        check(f"k={k} 枚挙台数", s["machines"], machines)
        check(f"k={k} 未判定台数", s["undecided"], 0)
        check(f"k={k} 巡回はすべて初期配置に戻る", s["cycle_not_initial"], 0)


def test_injectivity_lemma_empirical():
    print("[7] 単射性の補題: 可逆機械の巡回は必ず初期配置を含む")
    s = enumerate_quintuple(3, 1_000, reversible=True)
    check("反例台数", s["cycle_not_initial"], 0)
    # 非可逆側では初期配置に戻らない巡回が存在する（補題が可逆性に依存する証拠）
    ns = enumerate_quintuple(3, 400, reversible=False)
    check("非可逆側には初期配置に戻らない巡回がある",
          ns["cycle_not_initial"] > 0, True)


def main():
    test_reversibility_predicate()
    test_simulator_known_machines()
    test_wiki_reversible_champions()
    test_ordinary_bb_enumeration()
    test_reversible_quintuple()
    test_reversible_quadruple()
    test_injectivity_lemma_empirical()
    if os.environ.get("EXP05_SLOW"):
        test_ordinary_bb4_enumeration()
        test_reversible_quintuple_slow()
    else:
        print("[5][6b] skip (EXP05_SLOW=1 で通常 BB(4) と可逆 k=4,5 も実行)")
    print()
    if FAIL:
        print(f"FAILED: {len(FAIL)} -> {FAIL}")
        return 1
    print("all ok")
    return 0


if __name__ == "__main__":
    sys.exit(main())
