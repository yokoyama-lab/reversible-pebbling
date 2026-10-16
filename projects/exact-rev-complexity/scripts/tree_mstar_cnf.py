#!/usr/bin/env python3
"""T_h（完全二分木・葉 free・heap 番号）clean 可逆ペブリングの CNF 符号化器。

夜間 autoresearch（木 M* 証明書化）の Python 版。2026-08-10 の初夜に jq で確立した
符号化（autoresearch/tools/pebble.jq）と変数番号まで完全に同一:

    X(t,v) = n*t + v                          t=0..K, v=1..n   (n = 2^h - 1)
    M(t,v) = n*(K+1) + (t-1)*(n+1) + v + 1    t=1..K, v=0..n（v=0 は noop）
    S(t,i,j) = n*(K+1) + K*(n+1) + t*n*p + (i-1)*p + j        Sinz LT-SEQ 補助

noop があるので「K 手で UNSAT」=「≤K 手の clean スケジュールが存在しない」。

⚠ 初夜は権限の壁で python3 が実行できず、このファイルは**未実行**。
   使う前に `pytest tests/test_tree_mstar_cnf.py` を必ず通すこと
   （jq 側と同じ校正: h≤4 で p_min=1,3,5,6 / M*=1,5,17,53、K=M* の satcheck）。

対称性破り（--symbreak; 下界の CDCL 探索を速くする狙い。生成 DRAT には使わない）:
  (i) M(1, 2^{h-1}) 単位節 — 最初の手は最左の最下段内部頂点
  (ii) [¬M(t,0), M(t+1,0)] — noop は末尾に寄せる
  健全性: 任意のスケジュールは noop を末尾へ移動でき、部分木交換の自己同型で
  最初の実手を最左最下段へ写せる（根は固定、合法性・ピーク・clean 終端は保存）。
"""

from __future__ import annotations

import argparse
import json
import sys
from collections import deque

Clause = list[int]


def nverts(h: int) -> int:
    return (1 << h) - 1


def togglable(mask: int, v: int, n: int) -> bool:
    """両子が「葉（>n）」または「ペブル済み」なら toggle 可。"""
    for c in (2 * v, 2 * v + 1):
        if c <= n and not (mask >> (c - 1)) & 1:
            return False
    return True


def bfs(h: int, p: int) -> tuple[dict[int, int], dict[int, tuple[int, int]]]:
    """(dist, parent)。dist は最短手数（= 累積到達 R_t の判定に使える）。"""
    n = nverts(h)
    dist: dict[int, int] = {0: 0}
    par: dict[int, tuple[int, int]] = {}
    q = deque([0])
    while q:
        s = q.popleft()
        for v in range(1, n + 1):
            if not togglable(s, v, n):
                continue
            ns = s ^ (1 << (v - 1))
            if ns.bit_count() > p or ns in dist:
                continue
            dist[ns] = dist[s] + 1
            par[ns] = (s, v)
            q.append(ns)
    return dist, par


def pminm(h: int, pmax: int = 20) -> tuple[int, int]:
    for p in range(1, pmax + 1):
        d, _ = bfs(h, p)
        if 1 in d:
            return p, d[1]
    raise RuntimeError(f"unreachable h={h}")


def schedule(h: int, p: int) -> list[int]:
    d, par = bfs(h, p)
    if 1 not in d:
        raise RuntimeError("goal unreachable")
    moves: list[int] = []
    s = 1
    while s != 0:
        prev, v = par[s]
        moves.append(v)
        s = prev
    return moves[::-1]


class _TotNode:
    """Totalizer 木の1ノード。leaf は元の literal 位置（1..n）、internal は子2つ。"""
    __slots__ = ("leaf", "left", "right", "real", "cap", "offset")

    def __init__(self) -> None:
        self.leaf: int | None = None
        self.left: "_TotNode | None" = None
        self.right: "_TotNode | None" = None
        self.real = 0   # 部分木の実際の leaf 数
        self.cap = 0    # 保持する出力本数 = min(real, P)（P=p+1、それ以上は<=p判定に不要）
        self.offset = 0  # 1タイムステップ内でのこのノードの出力の先頭オフセット（leaf は未使用）


def _build_tot_tree(idxs: list[int], P: int) -> _TotNode:
    """idxs: 元の literal 位置（1-based）のリスト。P=p+1（出力の上限本数、これで容量を打ち切る）。"""
    node = _TotNode()
    if len(idxs) == 1:
        node.leaf = idxs[0]
        node.real = 1
        node.cap = 1
        return node
    mid = len(idxs) // 2
    node.left = _build_tot_tree(idxs[:mid], P)
    node.right = _build_tot_tree(idxs[mid:], P)
    node.real = node.left.real + node.right.real
    node.cap = min(node.real, P)
    return node


def _assign_tot_offsets(node: _TotNode, counter: int) -> int:
    """post-order で internal ノードに offset を振り、1タイムステップ分の総補助変数数を返す。"""
    if node.leaf is not None:
        return counter
    counter = _assign_tot_offsets(node.left, counter)
    counter = _assign_tot_offsets(node.right, counter)
    node.offset = counter
    return counter + node.cap


class Enc:
    def __init__(self, h: int, p: int, K: int, card: str = "sinz"):
        assert card in ("sinz", "totalizer"), f"unknown card encoding: {card}"
        self.h, self.p, self.K, self.card = h, p, K, card
        self.n = nverts(h)
        if card == "totalizer":
            self._tot_root = _build_tot_tree(list(range(1, self.n + 1)), self.p + 1)
            self._tot_vars_per_step = _assign_tot_offsets(self._tot_root, 0)
            self._tot_base = self.n * (self.K + 1) + self.K * (self.n + 1)

    def X(self, t: int, v: int) -> int:
        return self.n * t + v

    def M(self, t: int, v: int) -> int:
        return self.n * (self.K + 1) + (t - 1) * (self.n + 1) + v + 1

    def S(self, t: int, i: int, j: int) -> int:
        return (self.n * (self.K + 1) + self.K * (self.n + 1)
                + t * self.n * self.p + (i - 1) * self.p + j)

    def _tot_out(self, t: int, node: _TotNode, k: int) -> int:
        """totalizer ノード node の k 番目の出力（「入力の少なくとも k 個が真」）の変数番号。
        leaf ノードは補助変数を持たず、元の literal（X(t,v)）そのものを返す（k は無視、常に1）。
        """
        if node.leaf is not None:
            return self.X(t, node.leaf)
        return self._tot_base + t * self._tot_vars_per_step + node.offset + k

    def _tot_clauses(self, t: int, node: _TotNode) -> list[Clause]:
        """totalizer の「上向き」含意節のみ（<=p の判定に必要な向きだけ）。
        子の出力 l_i, r_j から親の出力 o_{i+j} への含意 l_i ∧ r_j → o_{i+j}
        （i=0 または j=0 のときは該当リテラルを省略）を全ノードについて再帰的に積む。
        """
        if node.leaf is not None:
            return []
        L, R = node.left, node.right
        cs = self._tot_clauses(t, L) + self._tot_clauses(t, R)
        for k in range(1, node.cap + 1):
            lo = max(0, k - R.cap)
            hi = min(k, L.cap)
            for i in range(lo, hi + 1):
                j = k - i
                if j < 0 or j > R.cap:
                    continue
                lits: Clause = []
                if i > 0:
                    lits.append(-self._tot_out(t, L, i))
                if j > 0:
                    lits.append(-self._tot_out(t, R, j))
                lits.append(self._tot_out(t, node, k))
                cs.append(lits)
        return cs

    def _fill_tot(self, t: int, node: _TotNode, mask: int, A: dict[int, bool]) -> int:
        """状態 mask（時刻 t）から、node 配下の真の leaf 数を計算しつつ、
        node の全出力の真理値を A に書き込む（sum>=k と定義通り）。leaf は書き込み不要。
        """
        if node.leaf is not None:
            return (mask >> (node.leaf - 1)) & 1
        cnt = self._fill_tot(t, node.left, mask, A) + self._fill_tot(t, node.right, mask, A)
        for k in range(1, node.cap + 1):
            A[self._tot_out(t, node, k)] = cnt >= k
        return cnt

    @property
    def nvars(self) -> int:
        base = self.n * (self.K + 1) + self.K * (self.n + 1)
        if self.card == "sinz":
            return base + (self.K + 1) * self.n * self.p
        return base + (self.K + 1) * self._tot_vars_per_step

    def clauses(self, symbreak: bool = False) -> list[Clause]:
        n, K, p = self.n, self.K, self.p
        X, M, S = self.X, self.M, self.S
        cs: list[Clause] = []
        cs += [[-X(0, v)] for v in range(1, n + 1)]              # init: 空
        cs.append([X(K, 1)])                                     # goal: {1} ちょうど
        cs += [[-X(K, v)] for v in range(2, n + 1)]
        for t in range(1, K + 1):
            cs.append([M(t, v) for v in range(0, n + 1)])        # ALO
            for a in range(0, n + 1):                            # AMO（対ごと）
                for b in range(a + 1, n + 1):
                    cs.append([-M(t, a), -M(t, b)])
            for v in range(1, n + 1):
                cs.append([-M(t, v), -X(t - 1, v), -X(t, v)])    # toggle 効果
                cs.append([-M(t, v), X(t - 1, v), X(t, v)])
                for c in (2 * v, 2 * v + 1):                     # toggle 可能性
                    if c <= n:
                        cs.append([-M(t, v), X(t - 1, c)])
            for u in range(1, n + 1):                            # フレーム
                cs.append([X(t, u), -X(t - 1, u), M(t, u)])
                cs.append([-X(t, u), X(t - 1, u), M(t, u)])
        if self.card == "sinz":
            for t in range(0, K + 1):                            # Sinz LT-SEQ ≤p
                cs.append([-X(t, 1), S(t, 1, 1)])
                for i in range(2, n + 1):
                    cs.append([-X(t, i), S(t, i, 1)])
                    cs.append([-S(t, i - 1, 1), S(t, i, 1)])
                    for j in range(2, p + 1):
                        cs.append([-X(t, i), -S(t, i - 1, j - 1), S(t, i, j)])
                        cs.append([-S(t, i - 1, j), S(t, i, j)])
                    cs.append([-X(t, i), -S(t, i - 1, p)])
        else:                                                    # totalizer ≤p（上向き節のみ）
            for t in range(0, K + 1):
                cs += self._tot_clauses(t, self._tot_root)
                if self._tot_root.cap == p + 1:                  # n<=p なら制約自体が不要
                    cs.append([-self._tot_out(t, self._tot_root, p + 1)])
        if symbreak and K >= 1:
            cs.append([M(1, 1 << (self.h - 1))])                 # 最初の手は最左最下段
            for t in range(1, K):                                # noop は末尾へ
                cs.append([-M(t, 0), M(t + 1, 0)])
        return cs

    def dimacs(self, symbreak: bool = False) -> str:
        cs = self.clauses(symbreak)
        if self.card == "sinz":                                  # 既定: 従来と完全に同一のヘッダ
            varline = ("c vars: X(t,v)=n*t+v M(t,v)=n*(K+1)+(t-1)*(n+1)+v+1 (v=0 noop)"
                       " S(t,i,j)=n*(K+1)+K*(n+1)+t*n*p+(i-1)*p+j")
            nline = f"c n={self.n} K={self.K} p={self.p} symbreak={int(symbreak)}"
        else:
            varline = ("c vars: X(t,v)=n*t+v M(t,v)=n*(K+1)+(t-1)*(n+1)+v+1 (v=0 noop)"
                       " totalizer aux vars from base=n*(K+1)+K*(n+1), up-only clauses, cap=p+1")
            nline = f"c n={self.n} K={self.K} p={self.p} card={self.card} symbreak={int(symbreak)}"
        head = [
            f"c T_{self.h} clean reversible pebbling (heap numbering, free leaves),"
            f" peak<={self.p}, <={self.K} moves (noop allowed)",
            "c generator: scripts/tree_mstar_cnf.py (mirror of autoresearch/tools/pebble.jq)",
            varline,
            nline,
            f"p cnf {self.nvars} {len(cs)}",
        ]
        return "\n".join(head + [" ".join(map(str, c)) + " 0" for c in cs]) + "\n"

    def assignment(self, moves: list[int]) -> dict[int, bool]:
        """実スケジュール（長さ K・noop なし）から全変数の充足割当を作る。"""
        assert len(moves) == self.K
        st = [0]
        for v in moves:
            st.append(st[-1] ^ (1 << (v - 1)))
        A: dict[int, bool] = {}
        for t in range(self.K + 1):
            for u in range(1, self.n + 1):
                A[self.X(t, u)] = bool((st[t] >> (u - 1)) & 1)
        for t in range(1, self.K + 1):
            for v in range(0, self.n + 1):
                A[self.M(t, v)] = (moves[t - 1] == v)
        if self.card == "sinz":
            for t in range(self.K + 1):
                cnt = 0
                for i in range(1, self.n + 1):
                    cnt += (st[t] >> (i - 1)) & 1
                    for j in range(1, self.p + 1):
                        A[self.S(t, i, j)] = (cnt >= j)
        else:
            for t in range(self.K + 1):
                self._fill_tot(t, self._tot_root, st[t], A)
        return A

    def satcheck(self, moves: list[int]) -> list[Clause]:
        """割当が破る節の一覧（空なら合格）。symbreak なし版に対する検査。"""
        A = self.assignment(moves)
        return [c for c in self.clauses()
                if not any(A[abs(lit)] == (lit > 0) for lit in c)]


def decode_model(enc: Enc, model: set[int]) -> list[int]:
    """SAT ソルバのモデル（真のリテラル集合）→ noop を除いた手順列。"""
    moves = []
    for t in range(1, enc.K + 1):
        vs = [v for v in range(0, enc.n + 1) if enc.M(t, v) in model]
        assert len(vs) == 1, f"t={t}: move vars {vs}"
        if vs[0] != 0:
            moves.append(vs[0])
    return moves


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--h", type=int, required=True)
    ap.add_argument("--p", type=int, required=True)
    ap.add_argument("--K", type=int, required=True)
    ap.add_argument("--symbreak", action="store_true")
    ap.add_argument("--card", choices=["sinz", "totalizer"], default="sinz",
                    help="カーディナリティ符号化（既定 sinz、totalizer は実験的・opt-in）")
    ap.add_argument("--out", type=str, default="-")
    ap.add_argument("--selftest", action="store_true",
                    help="h≤4 校正 + K=M* satcheck（cadical 不要）")
    a = ap.parse_args()
    if a.selftest:
        expect = {1: (1, 1), 2: (3, 5), 3: (5, 17), 4: (6, 53)}
        ok = True
        for h, (ep, em) in expect.items():
            p, m = pminm(h)
            good = (p, m) == (ep, em)
            ok &= good
            print(f"{'ok  ' if good else 'FAIL'} T_{h}: p_min={p} M*={m} (期待 {ep},{em})")
            bad = Enc(h, p, m).satcheck(schedule(h, p))
            print(f"{'ok  ' if not bad else 'FAIL'} satcheck K=M*: violated={len(bad)}")
            ok &= not bad
        return 0 if ok else 1
    enc = Enc(a.h, a.p, a.K, card=a.card)
    text = enc.dimacs(a.symbreak)
    if a.out == "-":
        sys.stdout.write(text)
    else:
        with open(a.out, "w") as f:
            f.write(text)
        print(json.dumps({"h": a.h, "p": a.p, "K": a.K, "nvars": enc.nvars,
                          "card": a.card, "symbreak": a.symbreak, "out": a.out}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
