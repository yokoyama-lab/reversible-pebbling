#!/usr/bin/env python3
"""night74_canonbfs.py -- M*(T_h, p) を Aut(T_h) による商グラフ上の BFS で求める。

第 74 夜（2026-10-07）周 2。目的は第 49 夜（`tools/night49_bitbfs128.py`）の
M*(T_7,10) = 1001 を **独立の 2 実装目** で再現すること。
第 49 夜のコードは読んでいない。意図的に別物にしてある:

  - 状態表現: heap 番号のビットマスクではなく **preorder ブロック符号化**。
    index 0 = 部分木の根、[1 .. S(m-1)] = 左部分木、
    [1+S(m-1) .. 2S(m-1)] = 右部分木（S(m) = 2^m - 1）。
  - 対称性: 「根の左右部分木の交換」1 個ではなく **Aut(T_h) 全体**
    （すべての内部頂点での兄弟部分木の交換。位数 2^(2^(h-1)-1)）で商を取る。
    各配置は子の正準形を降順に並べる再帰で**厳密な**正準形（128 bit 以下の整数）へ畳む。
    Aut は隣接関係・駒数・∅・{根} をすべて保つので、商グラフ上の BFS 距離は
    元のグラフの BFS 距離に等しい（ハッシュではなく厳密な正準形なので衝突は無い）。
  - 正準形は「preorder 符号化された配置そのもの」なので、商グラフの頂点を
    そのまま次の展開の入力に使える（復号が要らない）。

ゲームの定義（`scripts/revpebble.py` の docstring と同じ）:
  葉は free（常に利用可能・駒数に数えない・toggle しない）。
  内部頂点 v は v の両方の子がペブル済みまたは葉のとき toggle 可。
  ピーク = 内部頂点上の同時ペブル数 <= p。clean 終端 = 根のみ。

usage:
  python3 night74_canonbfs.py --h 6 --p 8
  python3 night74_canonbfs.py --h 7 --p 10 --levels out.tsv --max-depth 1001
  python3 night74_canonbfs.py --calibrate
"""
from __future__ import annotations

import argparse
import sys
import time


class Tree:
    """preorder ブロック符号化のための表。"""

    def __init__(self, h: int) -> None:
        self.h = h
        self.S = [(1 << m) - 1 for m in range(h + 1)]
        self.nv = self.S[h]
        n = self.nv
        self.ht = [0] * n          # 部分木の高さ（内部頂点の段数）
        self.lch = [-1] * n
        self.rch = [-1] * n
        self.parent = [-1] * n
        self.sib = [-1] * n
        self.sh = [0] * n          # 右の子を置くシフト量 = 1 + S(m-1)
        self.subm = [0] * n        # 部分木のビットマスク
        self._build(0, h)
        self._mask(0, h)
        self.parent[0] = -1
        # 高さ 1 の頂点（子が葉なので常に toggle 可）
        self.always_ready = [i for i in range(n) if self.ht[i] == 1]
        self.inner = [i for i in range(n) if self.ht[i] >= 2]

    def _build(self, idx: int, m: int) -> None:
        self.ht[idx] = m
        if m >= 2:
            li = idx + 1
            ri = idx + 1 + self.S[m - 1]
            self.lch[idx] = li
            self.rch[idx] = ri
            self.sh[idx] = 1 + self.S[m - 1]
            self.parent[li] = idx
            self.parent[ri] = idx
            self.sib[li] = ri
            self.sib[ri] = li
            self._build(li, m - 1)
            self._build(ri, m - 1)

    def _mask(self, idx: int, m: int) -> int:
        s = 1 << idx
        if m >= 2:
            s |= self._mask(self.lch[idx], m - 1)
            s |= self._mask(self.rch[idx], m - 1)
        self.subm[idx] = s
        return s

    def canon(self, s: int) -> int:
        """配置 s（preorder 符号化）の Aut 正準形を厳密に返す（参照実装）。"""
        cv = [0] * self.nv
        for idx in range(self.nv - 1, -1, -1):
            if not (s & self.subm[idx]):
                continue
            b = (s >> idx) & 1
            if self.ht[idx] == 1:
                cv[idx] = b
            else:
                a = cv[self.lch[idx]]
                c = cv[self.rch[idx]]
                if a < c:
                    a, c = c, a
                cv[idx] = b | (a << 1) | (c << self.sh[idx])
        return cv[0]

    def popcount(self, s: int) -> int:
        return bin(s).count("1")

    def decode_heap(self, s: int):
        """preorder 符号化 -> heap 番号の集合（manifest 契約の番号）。"""
        out = set()

        def rec(idx, m, hp):
            if m == 0:
                return
            if (s >> idx) & 1:
                out.add(hp)
            if m >= 2:
                rec(self.lch[idx], m - 1, 2 * hp)
                rec(self.rch[idx], m - 1, 2 * hp + 1)

        rec(0, self.h, 1)
        return out

    def ready_heap(self, pebbled) -> bool:
        """heap 番号集合が整合しているかの素朴な検査（校正用）。"""
        return all(1 <= v <= self.nv for v in pebbled)


def bfs(h: int, p: int, max_depth: int | None = None, levels_out=None,
        progress=None, frontier_only: bool = False):
    """∅ から {根} への商グラフ上の BFS。戻り値 (M, 状態数, レベル数の列)。

    `frontier_only=True` のときは**直前の 2 レベルだけ**を保持する。
    商グラフは無向（toggle は対合で、可否の条件は両向きで同じ）なので、
    レベル $d$ の頂点の隣接点は必ずレベル $d-1,d,d+1$ のどれかに居る。
    よって重複除去には直前 2 レベルで足り、全訪問集合を持つ必要が無い。
    この場合 2 番目の戻り値は**到達状態の総数ではなく**保持した最大レベル幅になる。
    """
    T = Tree(h)
    nv = T.nv
    ht = T.ht
    lch = T.lch
    rch = T.rch
    parent = T.parent
    sib = T.sib
    sh = T.sh
    subm = T.subm
    nodes = list(range(nv))
    goal = 1  # 根だけがペブル済み（正準形でもある）

    seen = {0}          # 全訪問集合（frontier_only のときは「直前 2 レベル」）
    cur = [0]
    depth = 0
    level_sizes = [1]
    kept = 1            # frontier_only のとき報告する「保持した状態数の最大」
    t0 = time.time()
    while True:
        if levels_out is not None:
            levels_out.write("%d\t%d\t%016x\n"
                             % (depth, len(cur), _fingerprint(cur)))
            levels_out.flush()
        if depth > 0 and goal in cur:
            return depth, (kept if frontier_only else len(seen)), level_sizes
        if not cur:
            return None, (kept if frontier_only else len(seen)), level_sizes
        if max_depth is not None and depth >= max_depth:
            return -depth, (kept if frontier_only else len(seen)), level_sizes
        if progress is not None and depth % progress == 0:
            print("  level %4d: frontier=%d kept=%d  %.1fs"
                  % (depth, len(cur), len(seen), time.time() - t0),
                  file=sys.stderr, flush=True)

        nxt = []
        cv = [0] * nv
        for s in cur:
            # --- 配置全体の正準値をボトムアップで埋める（空の部分木は 0 のまま）
            for idx in range(nv - 1, -1, -1):
                if not (s & subm[idx]):
                    cv[idx] = 0
                    continue
                b = (s >> idx) & 1
                if ht[idx] == 1:
                    cv[idx] = b
                else:
                    a = cv[lch[idx]]
                    c = cv[rch[idx]]
                    if a < c:
                        a, c = c, a
                    cv[idx] = b | (a << 1) | (c << sh[idx])
            np_ = bin(s).count("1")
            full = np_ >= p
            for i in nodes:
                if ht[i] >= 2:
                    if not ((s >> lch[i]) & 1) or not ((s >> rch[i]) & 1):
                        continue
                bit = (s >> i) & 1
                if bit == 0 and full:
                    continue
                # --- i を反転し、i から根までの正準値だけ更新する
                if ht[i] == 1:
                    val = bit ^ 1
                else:
                    a = cv[lch[i]]
                    c = cv[rch[i]]
                    if a < c:
                        a, c = c, a
                    val = (bit ^ 1) | (a << 1) | (c << sh[i])
                j = i
                while j:
                    q = parent[j]
                    o = cv[sib[j]]
                    if val < o:
                        a, c = o, val
                    else:
                        a, c = val, o
                    val = ((s >> q) & 1) | (a << 1) | (c << sh[q])
                    j = q
                if val not in seen:
                    seen.add(val)
                    nxt.append(val)
        if frontier_only:
            # 無向グラフなので、重複除去に要るのは直前 2 レベルだけ。
            # seen = prev(=depth-1) ∪ cur(=depth) ∪ nxt(=depth+1) を
            # 次の反復では cur ∪ nxt へ畳む。
            seen = set(cur)
            seen.update(nxt)
            kept = max(kept, len(seen))
        cur = nxt
        depth += 1
        level_sizes.append(len(cur))


def _fingerprint(states) -> int:
    """順序に依らないレベル集合の指紋（別実装が突き合わせられるように）。"""
    acc = 0
    for x in states:
        y = (x * 0x9E3779B97F4A7C15) & ((1 << 128) - 1)
        y ^= y >> 61
        y = (y * 0xBF58476D1CE4E5B9) & ((1 << 128) - 1)
        y ^= y >> 47
        acc = (acc + (y & ((1 << 64) - 1))) & ((1 << 64) - 1)
    return acc


KNOWN = [
    # (h, p, M*)  第 49 夜までに確定している校正点
    (1, 1, 1),
    (2, 3, 5),
    (3, 5, 17),
    (4, 6, 53),
    (5, 7, 155),
    (6, 8, 429),
    (6, 9, 339),
    (6, 10, 295),
    (6, 11, 261),
    (6, 12, 241),
]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--h", type=int)
    ap.add_argument("--p", type=int)
    ap.add_argument("--max-depth", type=int, default=None)
    ap.add_argument("--levels", default=None)
    ap.add_argument("--progress", type=int, default=None)
    ap.add_argument("--frontier-only", action="store_true",
                    help="直前 2 レベルだけ保持する（無向性を使う。省メモリ）")
    ap.add_argument("--calibrate", action="store_true")
    ap.add_argument("--selftest", action="store_true")
    args = ap.parse_args()

    if args.selftest:
        return selftest()

    if args.calibrate:
        bad = 0
        for (h, p, m) in KNOWN:
            t0 = time.time()
            got, nst, _ = bfs(h, p)
            ok = (got == m)
            bad += (0 if ok else 1)
            print("h=%d p=%2d  M*=%-5s expect %-5d %s  states=%-10d %.1fs"
                  % (h, p, got, m, "OK" if ok else "MISMATCH", nst,
                     time.time() - t0), flush=True)
        print("calibration: %d mismatch" % bad)
        return 1 if bad else 0

    if args.h is None or args.p is None:
        ap.error("--h and --p required")
    lf = open(args.levels, "w") if args.levels else None
    if lf:
        lf.write("# night74_canonbfs h=%d p=%d preorder/Aut-quotient\n"
                 % (args.h, args.p))
        lf.write("#depth\tcount\tfingerprint\n")
    t0 = time.time()
    got, nst, _ = bfs(args.h, args.p, max_depth=args.max_depth,
                      levels_out=lf, progress=args.progress,
                      frontier_only=args.frontier_only)
    dt = time.time() - t0
    what = "kept" if args.frontier_only else "states"
    if got is None:
        print("h=%d p=%d: UNREACHABLE (%s=%d, %.1fs)" % (args.h, args.p, what, nst, dt))
    elif got < 0:
        print("h=%d p=%d: M* > %d (cut at max-depth; %s=%d, %.1fs)"
              % (args.h, args.p, -got, what, nst, dt))
    else:
        print("h=%d p=%d: M* = %d (%s=%d, %.1fs)"
              % (args.h, args.p, got, what, nst, dt))
    if lf:
        lf.write("# result\t%s\n" % got)
        lf.close()
    return 0


def selftest() -> int:
    """符号化そのものの単体検査（BFS とは独立に正準形の性質を確かめる）。"""
    import random

    bad = 0
    for h in (2, 3, 4):
        T = Tree(h)
        # (a) 正準形は Aut 不変で、軌道をまたぐと異なる
        # Aut の生成元: 高さ m>=2 の頂点での兄弟部分木の交換
        def swap(s, idx):
            m = T.ht[idx]
            if m < 2:
                return s
            li, ri = T.lch[idx], T.rch[idx]
            sz = T.S[m - 1]
            lb = (s >> li) & ((1 << sz) - 1)
            rb = (s >> ri) & ((1 << sz) - 1)
            keep = s & ~(((1 << sz) - 1) << li) & ~(((1 << sz) - 1) << ri)
            return keep | (rb << li) | (lb << ri)

        allcfg = list(range(1 << T.nv))
        if T.nv > 15:
            allcfg = [random.getrandbits(T.nv) for _ in range(4000)]
        cls = {}
        for s in allcfg:
            c = T.canon(s)
            cls.setdefault(c, []).append(s)
            for idx in T.inner:
                if T.canon(swap(s, idx)) != c:
                    print("FAIL h=%d: canon not Aut-invariant at %d (s=%d)" % (h, idx, s))
                    bad += 1
        # 正準形は配置そのものの符号化なので canon(canon(s)) == canon(s)
        for s in allcfg:
            c = T.canon(s)
            if T.canon(c) != c:
                print("FAIL h=%d: canon not idempotent (s=%d)" % (h, s))
                bad += 1
            if bin(c).count("1") != bin(s).count("1"):
                print("FAIL h=%d: canon changes popcount (s=%d)" % (h, s))
                bad += 1
        # 軌道が本当に別物か: 代表の軌道を展開して一致を確かめる
        if T.nv <= 15:
            for c, members in list(cls.items())[:50]:
                orbit = {c}
                frontier = [c]
                while frontier:
                    x = frontier.pop()
                    for idx in T.inner:
                        y = swap(x, idx)
                        if y not in orbit:
                            orbit.add(y)
                            frontier.append(y)
                if orbit != set(members):
                    print("FAIL h=%d: orbit != canon class (c=%d)" % (h, c))
                    bad += 1
        print("selftest h=%d: %d configs, %d classes" % (h, len(allcfg), len(cls)))
    # (b) 既知の小さい値
    for (h, p, m) in KNOWN[:4]:
        got, _, _ = bfs(h, p)
        if got != m:
            print("FAIL bfs h=%d p=%d: %s != %d" % (h, p, got, m))
            bad += 1
    print("selftest: %d failures" % bad)
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
