#!/usr/bin/env python3
"""手順の独立の再生検査器（witness.py・fbfs*.c・p5_tree_count.py を読み込まない）.

ゲームの規則だけを直接書く: T_h はヒープ順（根 0、v の子 2v+1, 2v+2）。
各手で頂点 v を toggle する。合法 ⇔ v が葉か、v の 2 つの子がともにペブル済み。
置いた後のペブル数が S を超えたら不合法。空の盤から始め、終端は根だけ。

    python3 check_seq.py <h> <S> <手順ファイル>
終了コード 0 = 合法で終端が根だけ、1 = 不合法。
"""
import sys


def main() -> int:
    h, S, path = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    n = (1 << h) - 1
    moves = [int(t) for t in open(path).read().split("\n") if t.strip() and not t.startswith("#")]
    peb = [False] * n
    count = peak = 0
    for i, v in enumerate(moves):
        if not 0 <= v < n:
            print(f"NG: 手 {i}: 頂点 {v} は範囲外")
            return 1
        lc, rc = 2 * v + 1, 2 * v + 2
        if lc < n and not (peb[lc] and peb[rc]):
            print(f"NG: 手 {i}: 頂点 {v} の子がそろっていない")
            return 1
        peb[v] = not peb[v]
        count += 1 if peb[v] else -1
        if count > S:
            print(f"NG: 手 {i}: ペブル数 {count} > S={S}")
            return 1
        peak = max(peak, count)
    final = [v for v in range(n) if peb[v]]
    if final != [0]:
        print(f"NG: 終端が根だけでない（{len(final)} 個: {final[:10]}）")
        return 1
    print(f"OK: h={h} S={S} 手数={len(moves)} ペブル数の最大={peak} 終端=根のみ")
    return 0


if __name__ == "__main__":
    sys.exit(main())
