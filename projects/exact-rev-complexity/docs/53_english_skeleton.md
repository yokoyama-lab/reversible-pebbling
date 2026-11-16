# 53 — 英文骨子（RAIRO-ITA 向け）

`docs/51_paper_plan_candidate3.md` §4 の穴 4（英文化）。
**本文はまだ日本語でも書かれていない**ので、ここでは
**題目・abstract・節見出し・主定理の英文ステートメント**だけを確定させる
（これが決まれば以降は埋めるだけになる）。

---

## Title（候補）

1. **Exact time–space–erasure trade-offs for reversible pebbling**（推奨。3 資源が入る）
2. Reversible pebbling with a bounded number of irreversible erasures: exact values and trade-offs
3. How many bit erasures buy how many pebbles? Exact trade-offs in reversible pebbling

## Abstract（草案・約 180 語）

> Reversible simulation of an irreversible computation trades space for time: Bennett's
> pebble game and its exact analysis by Knill give the minimum number of moves for a given
> peak number of pebbles. Li, Tromp and Vitányi introduced the *m-erasure pebble game*, in
> which a bounded number of irreversible removals is allowed, and showed how erasures buy
> space. **The dual question — how erasures buy *time* — has not been studied.**
>
> We determine it exactly. Writing $M^*(n,p,e)$ for the minimum number of moves to pebble a
> chain of length $n$ cleanly with peak $p$ and at most $e$ irreversible removals, we prove
> that $M^*(n,p,e)$ attains Knill's absolute floor $2n-1$ **if and only if**
> $e \ge \lceil (n-1)/(p-1)\rceil - 1$, and we improve the reachability construction of
> Li–Tromp–Vitányi by one block, from $(e+1)2^{p-2}$ to $(e+2)2^{p-2}$.
>
> We complement the proofs with exact values obtained by exhaustive search, by CP-SAT
> ($n \le 160$), and — for the lower bound — by SAT with **DRAT certificates independently
> checked by drat-trim**. We report the cost of certification. Finally we measure two existing
> reversible memoization implementations and show that both sit at extreme points of the
> trade-off surface, neither using erasures at all.

**注意**: 「$e$ が時間を買う」という言い方は
`docs/52_gw_response.md` の位置づけ（$e$ は熱ではなく機会の数）と整合する範囲で使う。
abstract では "irreversible removals" と操作の言葉で書き、熱は §3 で扱う。

## 節見出し（英文）

1. Introduction
2. Preliminaries
   2.1 The clean reversible pebbling game (= Královič's *semicomplete* computation)
   2.2 The $m$-erasure pebble game of Li–Tromp–Vitányi
3. Related work, and the gap we fill
   3.1 What is known: Knill, Královič (no erasures); LTV, BTV (erasures, no time bound)
   3.2 On measuring dissipation by counting erasures ← `docs/52_gw_response.md`
4. The saturation theorem
   4.1 The floor $2n-1$ (Knill) and the rigidity lemma
   4.2 Erasures = ascents: proof of Theorem A
5. Reachability: improving the LTV construction
   5.1 Theorem B1 and its verified construction
   5.2 Reimplementing LTV's Procedure A in our model: a measured comparison
6. Exact values
7. The equality conjecture and what machine search says about it
8. Certified computation: what is proved, what is checked, and at what price
9. Implications for implementations
10. Conclusion

## 主定理の英文ステートメント（確定形）

> **Theorem A (saturation).** For $p \ge 2$ and $n \ge 1$,
> $$M^*(n,p,e) = 2n-1 \iff e \ \ge\ e^*(n,p) := \left\lceil\frac{n-1}{p-1}\right\rceil - 1 .$$
> The value $2n-1$ is Knill's floor, attained without erasures only when $p \ge n$
> [Knill 1995, Observation 2.2(i)].

> **Theorem B1 (reachability).** For $p\ge2$ and $e\ge0$, a chain of length
> $(e+2)2^{p-2}$ can be pebbled cleanly with peak $p$ and $e$ irreversible removals.
> For $e \ge 1$ this exceeds the length $(e+1)2^{p-2}$ guaranteed by
> [Li–Tromp–Vitányi 1998, Lemma 1] by one block; for $e=0$ both reduce to the optimum
> $2^{p-1}$ [Královič 2004, Theorem 3.1].

> **Conjecture B2 (equality).** $\mathrm{reach}(p,e) = (e+2)2^{p-2}$.
> Verified for $p\le6$ by exhaustive search and for $p\le5$ by two independent IC3 engines.

## 用語の対応表（訳語を固定する）

| 日本語 | English | 注 |
|---|---|---|
| clean 到達 | clean(ly) pebbling / clean terminal configuration | Královič の semicomplete と同一 |
| ピーク | peak (number of pebbles) | space と書かない（混乱するため） |
| 不可逆消去 | irreversible removal | "erasure" は熱の含みがあるので操作名は removal に寄せる |
| 消去予算 | erasure budget | $e$ |
| 飽和点 | saturation point | $e^*$ |
| 手数 | number of moves | time と書かない |
| 保持区間 | retention interval | CP-SAT 定式化 |
| ガベージスタック | garbage stack | 実装側の用語 |
| 認証 | certification | DRAT 等 |

## 未確定（先生の判断が必要）

- **英文単著 or 共著**。共著なら誰をどの節に割り当てるか。
- **投稿先の最終決定**（RAIRO-ITA / TCS / IPL）。IPL なら §6〜9 を大幅に削る必要がある。
- **国内先行発表を挟むか**（PPL/JSSST）。挟むなら英文版との差分を明示する必要がある。
