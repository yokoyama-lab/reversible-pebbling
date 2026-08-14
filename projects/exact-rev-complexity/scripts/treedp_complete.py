"""Královič の complete computation の最小空間 Smin(h) を商木 BFS で求める。

## 目的（docs/25 §3.1・第3ジャンプの確定）

S̄min(7)（= 我々の pmin(cbt(7))）の直接計算はメモリで詰む（treedp.py 冒頭の実測）。
**Lemma 4.3: S̄min(h+1) = Smin(h) + 2**（raw テキストで bar 割り当てを確認済み）を
使うと、高さ 7 の semicomplete の代わりに高さ 6 の complete を計算すればよい。

## 帰着（complete = 「根が載る任意の配置」への到達）

Královič §2 の定義（逐語確認）: complete computation = 最初と最後が空配置で、
全頂点がどこかで被覆される計算。次の 2 つの観察で到達問題に落ちる:

1. **被覆は自動**: 根に put するには子が載っている必要があり、子の put も帰納的に
   その子を要求する。ゆえに空配置から根が載る配置に至る任意の計算は全頂点を被覆する。
2. **往復は同コスト**: 遷移は対称（(C1,C2) が遷移なら (C2,C1) も遷移。§2 逐語）なので、
   空 → C の最小ピーク = C → 空 の最小ピーク。行きの最適経路の逆行で帰れる。

したがって
    Smin(h) = min { p : 空配置から「根にペブルが載る何らかの配置」へ
                    ピーク ≤ p で到達可能 }。

## 添字の対応（3 つの規約が全部ずれている。docs/25 §3.3）

treedp の QuotientTree(m) = 我々の cbt(m+1) の非 free 部分 = Královič の Bt(m+1)。
ゆえに本モジュールの smin_tree(m) = Smin(m+1)。

## 検証（これが通った範囲でのみ値を使う）

- Lemma 4.3 + 実測 S̄min(2..6) = [3,5,6,7,8]（pmin_tree(1..5)）から
  Smin(1..5) = [1,3,4,5,6] が**理論的に**導出される。smin_tree(0..4) がこれを
  再現することを確認してから smin_tree(5) を読む（__main__ がこの順で走る）
- さらに m ≤ 2 は独立実装（revpebble 規則の (配置, 被覆集合) 総当り。商を使わない）
  と照合する（--brute）

    .venv/bin/python scripts/treedp_complete.py          # 検証 → Smin(6) の決定
    .venv/bin/python scripts/treedp_complete.py --brute  # 独立実装との照合のみ
"""

from __future__ import annotations

import sys
from collections import deque
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from treedp import QuotientTree  # noqa: E402


def reachable_root_pebbled(qt: QuotientTree, p: int, *, cap: int | None = None) -> bool:
    """空配置から「根が載る配置」へピーク ≤ p で到達できるか（商グラフ上の BFS）。"""
    top = qt.m
    start = qt.empty_id()
    if qt.popcount(top, start) > p:
        return False
    seen = {start}
    queue: deque[int] = deque([start])
    fpc = qt.popcount
    frb = qt.root_pebbled
    while queue:
        s = queue.popleft()
        if frb(top, s):
            return True
        for t in qt.neighbors(top, s):
            if t not in seen and fpc(top, t) <= p:
                seen.add(t)
                queue.append(t)
        if cap is not None and len(seen) > cap:
            raise RuntimeError(f"状態数が cap={cap} を超えた（m={qt.m}, p={p}）")
    return False


def smin_tree(m: int, pmax: int = 20, *, cap: int | None = None,
              qt: QuotientTree | None = None) -> int | None:
    """Smin(m+1)（Královič の complete computation の最小空間）。"""
    qt = qt or QuotientTree(m)
    for p in range(1, pmax + 1):
        if reachable_root_pebbled(qt, p, cap=cap):
            return p
    return None


# ---------------------------------------------------------------------------
# 独立実装（商なし・被覆集合を明示的に持つ総当り）。m <= 2 の照合用
# ---------------------------------------------------------------------------


def smin_brute(m: int, pmax: int = 10) -> int | None:
    """complete computation の定義（空→空・全被覆・ピーク ≤ p）を直接探索する。

    頂点集合 = 高さ m の完全二分木（2^(m+1)-1 頂点）。葉の直前者条件は空。
    状態 = (配置ビットマスク, 被覆ビットマスク)。
    """
    n = (1 << (m + 1)) - 1
    # ヒープ順: root=0, 子は 2i+1, 2i+2。葉は i >= 2^m - 1
    first_leaf = (1 << m) - 1
    children = [
        (2 * i + 1, 2 * i + 2) if i < first_leaf else None for i in range(n)
    ]

    def movable(cfg: int, v: int) -> bool:
        ch = children[v]
        if ch is None:
            return True
        return (cfg >> ch[0]) & 1 and (cfg >> ch[1]) & 1

    full = (1 << n) - 1
    for p in range(1, pmax + 1):
        start = (0, 0)
        seen = {start}
        queue: deque[tuple[int, int]] = deque([start])
        ok = False
        while queue and not ok:
            cfg, cov = queue.popleft()
            if cfg == 0 and cov == full:
                ok = True
                break
            for v in range(n):
                if not movable(cfg, v):
                    continue
                bit = 1 << v
                if cfg & bit:
                    nxt = (cfg ^ bit, cov)
                else:
                    if bin(cfg).count("1") + 1 > p:
                        continue
                    nxt = (cfg | bit, cov | bit)
                if nxt not in seen:
                    seen.add(nxt)
                    queue.append(nxt)
        if ok:
            return p
    return None


if __name__ == "__main__":
    if "--brute" in sys.argv:
        for m in (0, 1, 2):
            b = smin_brute(m)
            q = smin_tree(m)
            mark = "○" if b == q else "**×**"
            print(f"m={m} (Bt({m+1})): brute={b} quotient={q}  {mark}", flush=True)
        sys.exit(0)

    # 第 1 層: Lemma 4.3 + 実測 S̄min から導出した真値との照合
    derived = {0: 1, 1: 3, 2: 4, 3: 5, 4: 6}  # smin_tree(m) = Smin(m+1)
    print("== 検証: Smin(1..5) = [1,3,4,5,6]（Lemma 4.3 + pmin_tree 実測から導出）")
    for m, want in derived.items():
        got = smin_tree(m)
        mark = "○" if got == want else "**×**"
        print(f"m={m}: Smin({m+1}) = {got}（導出値 {want}） {mark}", flush=True)
        if got != want:
            sys.exit(f"検証失敗: m={m}。定義か実装の取り違え。ここで停止")

    # 第 2 層: 独立実装（m<=2）
    print("== 検証: 独立実装（商なし総当り）との照合")
    for m in (0, 1, 2):
        b = smin_brute(m)
        q = smin_tree(m)
        mark = "○" if b == q else "**×**"
        print(f"m={m}: brute={b} quotient={q}  {mark}", flush=True)
        if b != q:
            sys.exit(f"照合失敗: m={m}")

    # 決定計算: Smin(6) は 7 か 8 か（Lemma 4.2 の挟み撃ちで 2 択）
    print("== 決定: Smin(6)（= 第 3 ジャンプが h=6 にあるか）")
    qt = QuotientTree(5)
    for p in (6, 7, 8):
        r = reachable_root_pebbled(qt, p)
        print(f"m=5, p={p}: {'到達可能' if r else '到達不能'}", flush=True)
        if r:
            print(f"→ Smin(6) = {p}")
            print(f"→ S̄min(7) = Smin(6) + 2 = {p + 2}（Lemma 4.3）")
            if p == 8:
                print("→ ジャンプ i*=6: reach_cbt(p,0) = p-2 は **p=9 で崩壊**（reach(9,0)=6）")
            elif p == 7:
                print("→ h=6 にジャンプ無し: S̄min(7)=9、p-2 は p=9 でも成立（reach(9,0)=7）。"
                      "第 3 ジャンプは i* >= 7")
            break
