#!/usr/bin/env python3
"""night80r2_quotbfs.py — M*(T_h, p) の独立 2 実装目（プロトタイプ）.

第 49 夜の `tools/night49_bitbfs128.py` とは**独立に**書いた（コードは読んでいない）。
違いは 2 点:

  * 状態表現: 128 ビットのビットマスクではなく、**部分木ごとの正準形を hash-cons した
    整数 id**（高さ j の節点 = (b, L, R)、L ≤ R は子の正準 id）。
  * 対称性: 根の左右交換だけでなく、**Aut(T_h) 全体**（反復環積・位数 2^(2^h-1)）で
    割った**商グラフ**の上で BFS する。始点 ∅ も終点 {root} も Aut 不変なので
    商の距離は元の距離に一致する。

モデル（`scripts/revpebble.py` の docstring と同じ）:
  葉は free（常に利用可能・ペブル数に数えない）。内部頂点 v を toggle できるのは
  v の両方の子が「ペブル済みまたは葉」のとき。ピーク p は内部頂点上の同時ペブル数。
  clean 終端 = 根のみ。

使い方:
    python3 tools/night80r2_quotbfs.py --h 5 --p 7
    python3 tools/night80r2_quotbfs.py --calibrate     # h=1..5 の既知値と突き合わせ
"""

from __future__ import annotations

import argparse
import json
import sys
import time


class Quotient:
    """高さ 0..h の正準部分木状態を hash-cons で管理する."""

    def __init__(self, h: int, p: int):
        self.h = h
        self.p = p
        # info[j][id] = (b, L, R, cnt);  高さ 0 は葉そのもの（内部頂点なし）
        self.info = [[(0, -1, -1, 0)]] + [[] for _ in range(h)]
        self.table = [dict() for _ in range(h + 1)]
        self.succ_memo = [dict() for _ in range(h + 1)]
        # 空状態 E_j
        self.empty = [0] * (h + 1)
        for j in range(1, h + 1):
            self.empty[j] = self.canon(j, 0, self.empty[j - 1], self.empty[j - 1])

    def canon(self, j: int, b: int, L: int, R: int) -> int:
        """(b, L, R) の正準 id。ペブル数が p を超えるなら -1。"""
        if L > R:
            L, R = R, L
        cnt = b + self.info[j - 1][L][3] + self.info[j - 1][R][3]
        if cnt > self.p:
            return -1
        key = (b, L, R)
        tab = self.table[j]
        v = tab.get(key)
        if v is None:
            v = len(self.info[j])
            tab[key] = v
            self.info[j].append((b, L, R, cnt))
        return v

    def avail(self, j: int, i: int) -> bool:
        """葉か、ペブル済みか。"""
        return j == 0 or self.info[j][i][0] == 1

    def succ(self, j: int, i: int):
        """高さ j の状態 i から 1 手 toggle で行ける正準 id の集合（p 超過は除く）。"""
        if j == 0:
            return ()
        memo = self.succ_memo[j]
        got = memo.get(i)
        if got is not None:
            return got
        b, L, R, _ = self.info[j][i]
        out = set()
        if self.avail(j - 1, L) and self.avail(j - 1, R):
            c = self.canon(j, 1 - b, L, R)
            if c >= 0:
                out.add(c)
        for L2 in self.succ(j - 1, L):
            c = self.canon(j, b, L2, R)
            if c >= 0:
                out.add(c)
        for R2 in self.succ(j - 1, R):
            c = self.canon(j, b, L, R2)
            if c >= 0:
                out.add(c)
        res = tuple(out)
        memo[i] = res
        return res

    def goal(self) -> int:
        return self.canon(self.h, 1, self.empty[self.h - 1], self.empty[self.h - 1])

    # ---- 最上段（高さ h）は id を作らず、(b, L, R) を 64 ビットに詰めた鍵で扱う ----
    # 最上段の節点は BFS で 1 回ずつしか要らないので、表に残すとそれだけが記憶を食う。

    def top_key(self, b: int, L: int, R: int) -> int:
        if L > R:
            L, R = R, L
        return b | (L << 1) | (R << 33)

    def succ_top(self, key: int):
        h, p = self.h, self.p
        b = key & 1
        L = (key >> 1) & 0xFFFFFFFF
        R = key >> 33
        c = self.info[h - 1]
        out = []
        if self.avail(h - 1, L) and self.avail(h - 1, R):
            if (1 - b) + c[L][3] + c[R][3] <= p:
                out.append(key ^ 1)
        base = b + c[R][3]
        for L2 in self.succ(h - 1, L):
            if base + c[L2][3] <= p:
                out.append(self.top_key(b, L2, R))
        base = b + c[L][3]
        for R2 in self.succ(h - 1, R):
            if base + c[R2][3] <= p:
                out.append(self.top_key(b, L, R2))
        return out


def bfs(h: int, p: int, verbose: bool = False, levels_out=None):
    """∅ から {root} までの商グラフ上の距離。

    商グラフは無向（toggle は対合で前提条件も対称）なので、レベル d の頂点の隣は
    必ずレベル d-1, d, d+1 のどれかにある。したがって**直前 2 レベルだけ**保持すれば
    重複は除ける（全訪問集合を持たない）。記憶は最大レベル幅に比例する。

    `levels_out` を与えると、**各深さのレベル幅を 1 行ずつ**追記して flush する
    （`d<TAB>|L_d|<TAB>累計<TAB>経過秒`）。これは打ち切られても残る中間成果であり、
    かつ別実装が再生して突き合わせられる検査可能な証拠（レベル集合の要約）である。
    """
    q = Quotient(h, p)
    e = q.empty[h - 1]
    start = q.top_key(0, e, e)
    goal = q.top_key(1, e, e)
    if q.info[h - 1][e][3] * 2 + 1 > p:
        return None, 0
    t0 = time.time()
    prev: set = set()
    cur = {start}
    seen = 1
    d = 0
    if levels_out is not None:
        levels_out.write("0\t1\t1\t0.0\n")
        levels_out.flush()
    while cur:
        d += 1
        nxt = set()
        for s in cur:
            for t in q.succ_top(s):
                if t not in cur and t not in prev:
                    nxt.add(t)
        if goal in nxt:
            if levels_out is not None:
                levels_out.write(f"{d}\t{len(nxt)}\t{seen + len(nxt)}\t"
                                 f"{time.time() - t0:.1f}\tGOAL\n")
                levels_out.flush()
            return d, seen + len(nxt)
        seen += len(nxt)
        prev, cur = cur, nxt
        if levels_out is not None:
            levels_out.write(f"{d}\t{len(cur)}\t{seen}\t{time.time() - t0:.1f}\n")
            levels_out.flush()
        if verbose and d % 25 == 0:
            print(f"  depth {d}: level {len(cur)} / seen {seen}",
                  file=sys.stderr, flush=True)
    return None, seen


def bfs_plain(h: int, p: int):
    """対称性を一切使わない素の BFS（正準化の監査用オラクル）.

    状態 = 内部頂点 1..2^h-1 の heap 番号を立てたビットマスク。h<=5 でしか回らない。
    """
    n = 2 ** h - 1
    full = 2 ** h  # 葉の最小番号

    def avail(mask: int, v: int) -> bool:
        return v >= full or ((mask >> v) & 1) == 1

    start, goal = 0, 1 << 1
    prev, cur, seen, d = set(), {start}, 1, 0
    while cur:
        d += 1
        nxt = set()
        for s in cur:
            for v in range(1, n + 1):
                if avail(s, 2 * v) and avail(s, 2 * v + 1):
                    t = s ^ (1 << v)
                    if bin(t).count("1") <= p and t not in cur and t not in prev:
                        nxt.add(t)
        if goal in nxt:
            return d, seen + len(nxt)
        seen += len(nxt)
        prev, cur = cur, nxt
    return None, seen


KNOWN_PMIN = {1: 1, 2: 3, 3: 5, 4: 6, 5: 7, 6: 8}
KNOWN_MSTAR = {1: 1, 2: 5, 3: 17, 4: 53, 5: 155, 6: 429}


def calibrate(hmax: int):
    ok = True
    for h in range(1, hmax + 1):
        # p_min を自分で探す（小さい p から最初に到達可能になる点）
        pmin = None
        for p in range(1, 2 ** h):
            m, _ = bfs(h, p)
            if m is not None:
                pmin = p
                mstar = m
                break
        exp_p = KNOWN_PMIN.get(h)
        exp_m = KNOWN_MSTAR.get(h)
        good = (pmin == exp_p) and (mstar == exp_m)
        ok = ok and good
        print(f"h={h}: p_min={pmin} (既知 {exp_p})  M*={mstar} (既知 {exp_m})  "
              f"{'OK' if good else 'NG'}", flush=True)
    return ok


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--h", type=int)
    ap.add_argument("--p", type=int)
    ap.add_argument("--calibrate", type=int, nargs="?", const=5)
    ap.add_argument("--oracle", action="store_true",
                    help="対称性なしの素の BFS と突き合わせる（h<=5）")
    ap.add_argument("--json", type=str)
    ap.add_argument("--levels", type=str,
                    help="各深さのレベル幅を 1 行ずつ追記する（打ち切られても残る）")
    args = ap.parse_args()

    if args.oracle:
        ok = True
        # ⚠ 素の BFS は p が大きいと 2^(2^h-1) に近づくので、p は p_min+3 で切る
        for h in range(1, 6):
            for p in range(1, min(2 ** h, KNOWN_PMIN[h] + 4)):
                a, _ = bfs(h, p)
                b, _ = bfs_plain(h, p)
                if a != b:
                    ok = False
                    print(f"NG h={h} p={p}: 商 {a} vs 素 {b}", flush=True)
            print(f"h={h}: 全 p で一致" if ok else f"h={h}: 不一致あり", flush=True)
        sys.exit(0 if ok else 1)

    if args.calibrate:
        sys.exit(0 if calibrate(args.calibrate) else 1)

    t0 = time.time()
    lv = open(args.levels, "w") if args.levels else None
    try:
        m, n = bfs(args.h, args.p, verbose=True, levels_out=lv)
    finally:
        if lv is not None:
            lv.close()
    dt = time.time() - t0
    rec = {"h": args.h, "p": args.p, "M": m, "states": n, "seconds": round(dt, 2)}
    print(json.dumps(rec), flush=True)
    if args.json:
        with open(args.json, "w") as fh:
            json.dump(rec, fh)


if __name__ == "__main__":
    main()
