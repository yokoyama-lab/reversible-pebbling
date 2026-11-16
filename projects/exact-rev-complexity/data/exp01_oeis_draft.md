# OEIS 登録用ドラフト（**未投稿**。投稿前に必ず人間がレビューする）

2026-07-27 作成。候補1 で厳密確定した数列のうち、**OEIS 未登録を確認済み**のものを
登録用の体裁でまとめる。**このファイルの存在は投稿を意味しない。**

投稿前チェックリスト:

- [ ] 数列の最終項まで**独立実装 2 つで一致**しているか（本リポジトリは 3 層で照合済み）
- [ ] 定義文が単独で読めるか（モデルの規則 R1/R2 と終端条件を明記）
- [ ] Královič 2004 との**量の違い**を comment に書いたか（下記の注意を参照）
- [ ] 生成プログラムが standalone で動くか（`程序` 欄。依存は標準ライブラリのみ）
- [ ] 著者名・日付を実際の投稿者に置き換えたか
- [ ] b-file が必要な長さか（項数が少ないので不要の見込み）

## 用語の統一（全エントリ共通の前置き）

可逆ペブリングゲーム（reversible pebble game, Bennett 1989）:
有向非巡回グラフ上で、頂点 v の直接先行点すべてがペブル済みのとき、v にペブルを
置くことも取ることもできる（R1/R2, Královič 2004 §2）。同時に盤上にあるペブル数の
最大値を p（空間）で抑え、手数（時間）を最小化する。

**終端条件が2種類あるので必ず区別する。**

| 記号 | 終端条件 | Královič 2004 での名前 |
|---|---|---|
| $M^*(G,p)$ | 空配置から始め、**目標頂点だけ**がペブルされた配置で終わる | semicomplete computation の時間（Def 4.1） |
| $T(G,p)$ | 空配置から始め**空配置で終わる**。各頂点が途中で一度カバーされる | complete computation の時間（§2） |

$p_{\min}(G)$ = $M^*$ が有限になる最小の $p$（= 彼の $S'_{\min}$）。
$S_{\min}(G)$ = $T$ が有限になる最小の $p$（= 彼の $S_{\min}$）。
両者は Lem 4.2/4.3 で結ばれる: $S_{\min}(h)\le S'_{\min}(h)\le S_{\min}(h)+1$、
$S'_{\min}(h+1)=S_{\min}(h)+2$。

**Královič 2004 は木・バタフライについて空間のみを扱っており、時間の厳密値表は無い**
（§4 冒頭 "we shall discuss the space complexity"）。したがって下記の時間の数列は新しい。

---

## エントリ1: 完全二分木の最小手数（最小空間の下で）

**%N** Minimum number of moves in the reversible pebble game on the complete binary tree
of height n (all vertices countable, root is the target), using the minimum possible
number of pebbles, ending in the configuration where only the root is pebbled.

**%D** データ（offset 1）:

```
1, 5, 17, 53, 155, 429
```

**%O** 1,2

**%C** 可逆ペブリングは Bennett (1989) 由来。規則は Královič (2004) §2 の R1/R2。
終端条件は同論文 Def 4.1 の semicomplete computation（根だけがペブルされた配置）。
使用ペブル数は各 n における最小値 $p_{\min}(n)$ = 1, 3, 5, 6, 7, 8（n=1..6）に固定。

**%C** Královič (2004) Thm 4.9 はこの位相の**空間**が $n+\Theta(\lg^* n)$ であることを
示しているが、**手数の厳密値は与えていない**。

**%C** 予想 $a(n) = 2\cdot3^{n-1}-1$（1, 5, 17, 53, **161**, **485**）は $n\le4$ で成立するが
$n=5,6$ で偽（155 ≠ 161、429 ≠ 485）。成長比 $a(n)/a(n-1)$ は
5, 3.40, 3.12, 2.92, 2.77 と単調減少しており指数型ではない。

**%C** $a(n)$ は $p_{\min}(n)$ の増分が 2 になる n（n=7 が次）の前後で不規則に振る舞う。
関連する族（ピラミッド・spinal tree）では同じ位置で対応する数列が**減少**する。

**%H** R. Královič, *Time and space complexity of reversible pebbling*,
RAIRO-Inf. Theor. Appl. **38** (2004), 137-161, doi:10.1051/ita:2004008.

**%H** C. H. Bennett, *Time/space trade-offs for reversible computation*,
SIAM J. Comput. **18** (1989), 766-776.

**%p** 生成プログラム: 本リポジトリ `scripts/treedp.py`（Aut 商グラフ上の厳密 BFS）。
`python3 -c "import sys; sys.path.insert(0,'scripts'); from treedp import mstar_tree, pmin_tree; print([mstar_tree(m, pmin_tree(m)) for m in range(6)])"`

**%K** nonn,hard,more

**%Y** 関連: エントリ2（ピラミッド）、エントリ3（spinal tree）、エントリ4（complete computation の時間）。

**未確定**: $a(7)$ は $603 \le a(7) \le 1403$ の範囲にあることまでしか分かっていない
（`data/exp01b_bounds_t7.md`）。$p_{\min}(7)=10$ 自体は厳密に確定している。
→ **`more` キーワードを付け、$a(7)$ は載せない。上界を値として載せてはいけない。**

---

## エントリ2: ピラミッド DAG の最小手数（最小空間の下で）

**%N** Minimum number of moves in the reversible pebble game on the pyramid dag of height n
(n+1 levels of sizes n+1, n, ..., 1; all vertices countable; apex is the target), using the
minimum possible number of pebbles, ending with only the apex pebbled.

**%D** データ（offset 1）:

```
5, 13, 27, 47, 105, 99
```

**%O** 1,1

**%C** 規則・終端条件はエントリ1 と同じ。使用ペブル数は最小値
$p_{\min}(n)$ = 3, 5, 6, 7, 8, 10（n=1..6）に固定。

**%C** **この数列は単調増加ではない**（$a(5)=105 > a(6)=99$）。原因は
$p_{\min}$ の増分が n=6 でのみ 2 になること: n=5 では $p_{\min}=8$ が限界ぎりぎりで
最適手順が頂点の再計算（1 頂点あたり最大 5 回の再配置）を強いられるが、
n=6 では余裕が復活するため頂点数が増えても手数が減る。

**%C** $a(n)=3n^2-n+3$ は $n\le4$ で完全に一致するが n=5 で偽（予測 73、実際 105）。

**%H** （エントリ1 と同じ 2 件）

**%p** 本リポジトリ `scripts/exp01b_tradeoff.py`（ビットマスク双方向 BFS）。

**%K** nonn,hard,more

---

## エントリ3: spinal tree の最小手数（最小空間の下で）

**%N** Minimum number of moves in the reversible pebble game on the spinal tree S_n
(a path of n vertices, each carrying one extra leaf child; 2n+1 vertices, all countable;
the top spine vertex is the target), using the minimum possible number of pebbles,
ending with only the target pebbled.

**%D** データ（offset 1）:

```
5, 11, 19, 25, 35, 45, 61, 57, 71, 85, 101, 119, 137, 155, 179, 153
```

**%O** 1,1

**%C** 規則・終端条件はエントリ1 と同じ。
**$p_{\min}(S_n) = \lfloor\log_2 n\rfloor + 3$ が n=1..16 の全点で厳密に成立**する。
したがって $p_{\min}$ の増分が起きる位置は**ちょうど 2 の冪** n=2,4,8,16 であり、
事前に予測できる。

**%C** $a(n)$ は $p_{\min}$ が増える位置で**減少**する（$a(7)=61>a(8)=57$、
$a(15)=179>a(16)=153$）。ブロック内（$p_{\min}$ 一定の区間）では増加する。

**%C** 葉を「常時利用可能でペブル数に数えない入力源」とする流儀では
$M^*(S_n,p)$ は長さ n の鎖の値に**厳密に一致する**（側枝が制約にならない）。
上の数列は葉も数える流儀のもの。

**%H** （エントリ1 と同じ 2 件）

**%p** 本リポジトリ `scripts/exp01b_saturation.py`。

**%K** nonn,hard,more

---

## エントリ4: 完全二分木の complete computation の最小時間

**%N** Minimum number of moves of a complete computation of the reversible pebble game on
the complete binary tree of height n (start and end with no pebbles; every vertex is
pebbled at some point), using the minimum possible number of pebbles.

**%D** データ（offset 1）:

```
2, 6, 20, 58, 168, 380
```

**%O** 1,1

**%C** これは Královič (2004) §2 の complete computation（空→空・全頂点を一度カバー）
に対する $T(Bt(n), S_{\min}(n))$ である。エントリ1 とは**終端条件が違う**。
使用ペブル数は $S_{\min}(n)$ = 1, 3, 4, 5, 6, 8（n=1..6）。

**%C** 木では「全頂点がカバーされる」は「根がカバーされる」と同値（根を置くには
両方の子が同時にペブル済みでなければならず、再帰的に全祖先が過去にカバーされる）。
状態グラフが無向なので $T = 2\times$（空から根を含む配置への最小手数）。

**%C** Královič (2004) は鎖について時間の漸近（Cor 3.5: $O(n^{\lg 3})$ かつ
$\ne o(n\lg n)$）と漸化不等式（Thm 3.4）を与えたが、木については**空間のみ**であり
この数列は与えていない。

**%C** $a(6)=380$ は $a(5)=168$ からの比が 2.26 で、それ以前の比（3, 3.33, 2.9, 2.9）から
外れる。$S_{\min}$ の増分が n=6 で 2 になるため（4→5→6→8）。

**%H** （エントリ1 と同じ 2 件）

**%p** 本リポジトリ `scripts/treedp.py::tmin_tree`。

**%K** nonn,hard,more

**%Y** 鎖に対する同じ量 $T(2^p-1,p) = 2, 8, 26, 76, 218$（p=1..5）も未登録。
これは先行プロジェクト `2026_exact_reversible_pebbling` の測定値で、本リポジトリが
独立に再現した（`tests/test_exp01d_kralovic.py`）。別エントリにする候補。

---

## 登録しない判断をしたもの

| 数列 | 理由 |
|---|---|
| $p_{\min}$ の各族の数列（$1,3,5,6,7,8,10$ 等） | 短く、汎用的な数列と偶然一致するため識別性が低い |
| バタフライ全出力の $2,12,44$ | 3 点しかない。$k=4$ が計算不能で伸ばせない |
| $\sigma$（飽和指標）の値 | 有理数列であり整数列ではない |

## 偶然一致の記録（登録時の注意）

`5,17,53,155,429`（エントリ1 の n≥2）は **A263678**
（"Number of length n arrays of permutations of 0..n-1 with each element moved by
-3 to 3 places..."）の $a(3..7)$ と 5 項一致する。対象に構造的関係は無く、
A263678 に載る式は経験的な 20 階線形漸化式のみ。**偶然と判断した**が、
登録時には `%Y` で相互参照して「5 項の一致は偶然」と明記するのが親切である。
