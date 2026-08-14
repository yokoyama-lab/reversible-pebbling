#!/usr/bin/env python3
"""交互構成（alternating）が**合法なペブリングか**を全数検査する（2026-08-14）。

機械証明に投資する前の検査。構成:

* sink            : 時刻 `d+1` 以降ずっと居る
* 奇数深さの頂点  : 窓 `[dep+1, 2d-dep]` を丸ごと占有（チェックポイント）
* 偶数深さの頂点  : 両端の強制ブロック `[dep+1, dep+2]` と `[2d-dep-1, 2d-dep]` のみ

`layered`（全頂点が窓を丸ごと占有）より**厳密に少ないピーク**になるはず。
検査するのはペブリング規則そのもの（`P[0]=∅`・`P[T]={sink}`・変化した頂点の親が前後に居る）。
"""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "scripts"))
import q2_cnf  # noqa: E402


def alt_config(par, sink, dep, resident_parity: int):
    d = dep[sink]
    T = 2 * d + 1
    n = len(par)

    def inside(v, t):
        if v == sink:
            return t >= d + 1
        k = dep[v]
        if k % 2 == resident_parity:
            return k + 1 <= t <= 2 * d - k
        return (k + 1 <= t <= k + 2) or (2 * d - k - 1 <= t <= 2 * d - k)

    return [{v for v in range(n) if inside(v, t)} for t in range(T + 1)], T


def check(par, sink, P, T):
    bad = []
    if P[0]:
        bad.append(f"P[0]={sorted(P[0])} が空でない")
    if P[T] != {sink}:
        bad.append(f"P[T]={sorted(P[T])} != {{{sink}}}")
    for t in range(T):
        for v in P[t] ^ P[t + 1]:
            for u in par[v]:
                if u not in P[t] or u not in P[t + 1]:
                    bad.append(f"t={t}: v={v} が変化・親 u={u} が不在")
                    return bad
    return bad


def layered_peak(par, sink, dep):
    """比較対象: `layered` のピーク（= |V|、t=d+1 で全部）。"""
    return len(par)


def main() -> int:
    fails = 0
    print(f"{'族':>8} {'n/h':>4} {'|V|':>5} {'layered':>8} {'交互(奇)':>9} "
          f"{'交互(偶)':>9} {'判定':>6}")
    cases = ([("line", n) for n in range(2, 21)]
             + [("pyramid", h) for h in range(2, 15)])
    for fam, n in cases:
        par, sink = q2_cnf.FAMILIES[fam](n)
        dep = q2_cnf.depths(par)
        peaks = {}
        ok = True
        for par_ in (0, 1):
            P, T = alt_config(par, sink, dep, par_)
            bad = check(par, sink, P, T)
            if bad:
                ok = False
                peaks[par_] = f"✖{bad[0][:28]}"
            else:
                peaks[par_] = max(len(s) for s in P)
        if not ok:
            fails += 1
        print(f"{fam:>8} {n:>4} {len(par):>5} {layered_peak(par, sink, dep):>8} "
              f"{str(peaks[1]):>9} {str(peaks[0]):>9} {'OK' if ok else '不合格':>6}")
    if fails:
        print(f"\n✖ {fails} 件が合法でない。この構成を定理にしてはならない。")
        return 1
    print(f"\n✔ {len(cases)} 件すべて合法なペブリング（ペブリング規則を全ステップで確認）")
    return 0


if __name__ == "__main__":
    sys.exit(main())
