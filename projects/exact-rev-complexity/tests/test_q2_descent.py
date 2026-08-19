#!/usr/bin/env python3
"""`q2_descent_cnf.py`（降下問題への帰着）の検査（2026-08-18）。

守るのは 3 点:

1. **`1 + d(h) = p_min(h)`**（$h = 2..10$）: 降下 CNF が $d = p_{\\min}-1$ で SAT、
   $d = p_{\\min}-2$ で UNSAT。Lean `pmin_iff_descent`（`lean/Revgarbage/ParPebbleSym.lean`）
   の主張を CNF 生成器が正しく写していることの校正。
2. SAT の解は `verify_descent` を通り、**対称化して伸ばした列**は元の（素の）ペブリング規則を
   満たしてピークがちょうど $d+1$（`pebbling_of_descent` の構成を Python で再生）。
3. `verify_descent` は壊れた列（親無しの変化・強制時刻の欠落）を検出する。

⚠ 降下 CNF の UNSAT 証明書は「帰着定理 ＋ この生成器」に乗る。素の CNF の証明書とは
信頼の置き場が違うので、層ラベルを付けるときは区別すること。
"""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "scripts"))
import q2_cnf  # noqa: E402
import q2_descent_cnf as dc  # noqa: E402


def extend_symmetric(h, Q):
    """降下 Q（時刻 0..h-1）を対称化して T=2h-1 の列にする（`symOfDescent`）。"""
    par, sink = q2_cnf.pyramid(h)
    T = 2 * h - 1
    D = h - 1
    P = []
    for t in range(T + 1):
        if t <= D:
            P.append(set(Q[t]))
        else:
            P.append(set(Q[T - t]) | {sink})
    return P, par, sink, T


def check_pebbling(par, sink, P, T):
    bad = []
    if P[0]:
        bad.append("P0 が空でない")
    if P[T] != {sink}:
        bad.append("終状態が {sink} でない")
    for t in range(T):
        for v in P[t] ^ P[t + 1]:
            for u in par[v]:
                if u not in P[t] or u not in P[t + 1]:
                    bad.append(f"t={t}: {v} の親 {u} が両側に居ない")
    return bad


def main() -> int:
    bad = 0
    # 1. 1 + d(h) = p_min(h)
    for h in range(2, 11):
        p = dc.PMIN[h]
        Q = dc.solve(h, p - 1)
        Q2 = dc.solve(h, p - 2)
        ok = Q is not None and Q2 is None
        print(f"  h={h}: d={p-1} {'SAT' if Q else 'UNSAT'} / d={p-2} {'SAT' if Q2 else 'UNSAT'}"
              f"  {'○' if ok else '**✗**'}")
        bad += 0 if ok else 1
        if Q is None:
            continue
        # 2. 対称化して伸ばした列が合法でピーク d+1
        P, par, sink, T = extend_symmetric(h, Q)
        errs = check_pebbling(par, sink, P, T)
        peak = max(len(s) for s in P)
        ok2 = not errs and peak == p
        print(f"       対称化: {'合法' if not errs else errs[:2]} ピーク {peak}（期待 {p}）"
              f"  {'○' if ok2 else '**✗**'}")
        bad += 0 if ok2 else 1
    # 3. verify_descent が壊れた列を検出する
    h = 5
    Q = dc.solve(h, dc.PMIN[h] - 1)
    assert Q is not None
    par, sink = q2_cnf.pyramid(h)
    # 3a: 親無しの変化（層 2 の頂点を、親の居ない時刻 1 に置く）
    Qa = [set(s) for s in Q]
    v2 = [v for v in range(len(par)) if q2_cnf.depths(par)[v] == 2][0]
    Qa[1].add(v2)
    det_a = bool(dc.verify_descent(h, Qa))
    # 3b: 強制時刻の欠落（層 0 の頂点を時刻 2 から消す）
    Qb = [set(s) for s in Q]
    Qb[2].discard(0)
    det_b = bool(dc.verify_descent(h, Qb))
    print(f"  変異注入: 親無し変化 {'検出' if det_a else '**素通り**'} / "
          f"強制欠落 {'検出' if det_b else '**素通り**'}")
    bad += 0 if (det_a and det_b) else 1
    print("OK" if bad == 0 else f"**NG: {bad} 件**")
    return 1 if bad else 0


def test_descent_reduction():
    """pytest からも走らせる（`tests/` は pytest で毎回収集される場所なので、
    `main()` だけだと 0 件収集になり「走っていない検査」になる）。"""
    assert main() == 0


if __name__ == "__main__":
    sys.exit(main())
