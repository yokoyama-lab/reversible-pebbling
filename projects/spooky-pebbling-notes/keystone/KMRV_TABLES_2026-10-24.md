# KMRV（Kahanamoku-Meyer・Ragavan・Van Kirk）arXiv:2510.08432v3 の鎖の数値の抜き書き

作成 2026-10-24．目的: 彼らの鎖（線グラフ）の spooky pebbling の数値を，こちらの厳密式（`KEYSTONE_delta.md`，Envelope.lean の `T_UP = max_m(2mn − β_m(s))`）と突き合わせられる形にする．

- 読んだもの: 手元 PDF `~/dev/notes/spooky-pebbling/tree-gap/novelty/pdf/arxiv_2510.08432.pdf`．**先頭頁の arXiv 行は `arXiv:2510.08432v3 [quant-ph] 3 Jul 2026`，日付行 July 7, 2026**（v3 で間違いない．再取得はしていない）．
- 本文化: `pdftotext -layout`（2383 行）．**本文（1〜4 節）と付録 A・B・D・F・G は全文を読んだ．** 付録 C（格子）・E（Fibonacci 版 Regev）は数値の有無だけを確かめた（鎖の数値は無い）．参考文献は BHL22・BHL25・Gid19a・KSS25・KMRV25 の項だけ読んだ．
- 「頁」は PDF の印字頁番号（PDF ファイルの頁番号は +2．例: 図 2 は印字 16 頁 = PDF 18 頁目）．
- 逐語は「」で囲んで英語のまま置く．それ以外の文は私の要約・推測で，推測には【推測】を付ける．
- **PDF には EUROCRYPT 2026 の記載は無い**（本文・脚注を grep．依頼文の情報としてのみ扱う）．

---

## 1. 鎖のモデルの定義（2.1 節，9〜10 頁）

### 1.1 頂点数とインデックス（Definition 2.1，9 頁）

「A pebbling game is specified by a target length ℓ. At any point, the state of the game will be a vector state ∈ {pebble, ghost, empty}^{ℓ+1}. We index the elements of state by indices in [0, ℓ]」

「The initial and final states of the pebbling game will both be (pebble, empty, empty, …, empty). (The first entry of the state is a dummy variable which will always be pebble.) We require that one of the intermediate states of the pebbling game has a pebble in position ℓ i.e. state_ℓ = pebble, and the target end state will be (pebble, empty, …, empty).」

- **頂点は 0..ℓ の ℓ+1 個．位置 0 は常に pebble のダミー（入力）．ℓ は辺の本数 = 計算する関数の反復回数 H^ℓ（1 節 1 頁「compute H^ℓ(x)」「a line graph of length ℓ」）．**
- **初期状態 = 終了状態 = (pebble, empty, …, empty)．** 途中で一度 state_ℓ = pebble になることを要求．**終端にペブルを残さず，ゴーストも残さず，全部 empty に戻す**（こちらの用語では T_UP 型．終端をゴーストで残す T_UG 型の量は定義していない）．
- 【推測】こちらの「頂点数 n」の数え方との対応: こちらが「n 頂点の鎖で始点を含めない（辺 n 本）」なら n = ℓ．始点を含めるなら n = ℓ+1．突き合わせの前にこちらの定義を確認する．

### 1.2 操作（Definition 2.2，9〜10 頁）

- 「Pebble(i) for some i ∈ [1, ℓ]: this is applicable when state_{i−1} = pebble and state_i ∈ {ghost, empty}. It will produce state′ which is identical to state in all positions except state′_i which will now be pebble. Its active set is {i − 1, i}.」
  - **ゴーストの上に Pebble できる**（ゴースト→ペブルの復元を Pebble で行う．Unghost という別操作は 2 節には無い．4 節の Algorithm 4.2 に「Unghost(t)」が出るが，これは t レジスタの話）．
- 「Unpebble(i) for some i ∈ [1, ℓ]: this is applicable when state_{i−1} = state_i = pebble. It will produce state′ … state′_i which will now be empty. Its active set is {i − 1, i}.」
  - **Unpebble は ghost からは不可（pebble からのみ）．** 位相の除去（exorcise）は Unpebble に暗黙に含める（1.1.1 節 6 頁「We implicitly assume that when unpebbling we will also “exorcise” any phases that were accumulated earlier from this stage of the pebbling game」）．
- 「Ghost(i) for some i ∈ [1, ℓ]: this is applicable when state_i = pebble. … state′_i which will now be ghost. Its active set is {i}.」
  - **Ghost に前提条件なし**（隣の状態を問わない）．

### 1.3 逐次と並列（Definition 2.3，10 頁）

「In a pebbling game, each time step consists of two phases that are applied in sequence:
- In the first phase of a sequential pebbling game, we can make at most one call to Pebble, Unpebble. In the first phase of a parallel pebbling game, we can make an arbitrary number of parallel calls to Pebble, Unpebble, provided that their active sets are pairwise disjoint.
- In the second phase, we can make an arbitrary number of parallel calls to Ghost.」

- **逐次ゲームでも 1 時間ステップに Ghost は何個でも打てる．**

### 1.4 数える量（Definition 2.4，Remark 2.5〜2.7，10 頁）

- 「The pebbling cost of a pebbling game is the total number of calls to Pebble, Unpebble.」
- 「We define pebbling depth as the total number of time steps」
- Remark 2.5「in the case of a sequential pebbling game, the pebbling cost and pebbling depth will always be equal.」
- Remark 2.6「We exclude calls to Ghost when calculating pebbling cost, because in typical applications Ghost will be significantly cheaper than the other three operations.」
- Remark 2.7「a parallel pebbling game of length ℓ must necessarily have depth ≥ 2ℓ. This is because the position of the rightmost pebble/ghost changes by at most ±1 in each time step.」

→ **逐次の cost = Pebble + Unpebble の回数（Ghost は 0）．** これはこちらの `SpookyTree/Work.lean`・`SpookyDag/` の「仕事量 W（置く手＋外す手，ゴーストは 0）」と同じ数え方（10-20 の handoff「LLJ の仕事量」とも同じ）．**こちらの T_UP（手数）とは Ghost を数えるかで異なる**ので，突き合わせは W の側で行う．

### 1.5 空間（Definition 2.8，10 頁）

「For each t = 1, …, T, we define the space usage s_t of time step t as the number of indices i ∈ [1, ℓ] such that at least one of state[t−1]_i, state[t]_i is pebble. … Then we define the pebbling space of the pebbling game to be max_{t∈[1,T]} s_t.」

- **ゴーストは数えない．位置 0 のダミーは数えない（i ∈ [1, ℓ]）．** 1 ステップの前後どちらかでペブルだった位置を数えるので，「Unpebble(i) の瞬間に i も数える」（置く側・外す側の両方を占有とみなす）．
- 【推測】こちらの s（ペブル数の上限）との対応: こちらが「同時に盤上にあるペブルの最大数（始点を含めない）」なら，彼らの s_t は Pebble(i) の直後の盤面のペブル数と一致し，Unpebble(i) 直前の盤面のペブル数とも一致するので，最大値は同じ．**始点のペブルを数えるかだけがずれの原因になりうる．**

---

## 2. 逐次の鎖について彼らが報告している値（2.2 節，10 頁，Theorem 2.9）

**彼ら自身の逐次の新結果は無い．** 先行結果の引用のみ（表も式も A* の逐次結果も無い）．逐語:

「Theorem 2.9 (Sequential Spooky Pebbling). There exist sequential spooky pebbling games achieving any of the following guarantees:
- Pebbling space 3 and pebbling cost O(ℓ²) [Gid19a];
- Pebbling space (1 + o(1)) log ℓ and pebbling cost (1 + o(1))ℓ log ℓ [Gid19a];
- Pebbling space s and pebbling cost O(mℓ) provided C(m+s−2, s−2) ≥ ℓ [KSS25, Lemma 3.5].
Moreover, the third item here is asymptotically tight: for any s, m such that n > C(m+s−2, s−2), a sequential spooky pebbling of length ℓ must use at least Ω(mℓ) steps [KSS25, Theorem 4.13].」

- 3 項目目の「n >」は原文のまま（ℓ の誤植とみられる【推測】）．
- 表 1（2 頁）の該当行: 「[Gid19a, KSS25] | N | Y | ≈ log ℓ | ≈ ℓ log ℓ」．
- 1.1.1 節 6 頁: 「naive square-and-multiply uses 2ℓ − 1 multiplications (“pebbling steps”) and ℓ n-qubit registers (“pebbles”). In comparison, Gidney’s proposed pebbling scheme uses ≈ ℓ log ℓ pebbling steps (which is slightly worse), but manages to do so using only ≈ log ℓ pebbles.」
- 1 節 1 頁（可逆・非 spooky）: 「for any ϵ > 0 we can use O(ϵ2^{1/ϵ} · log ℓ) pebbles to complete the computation in O(ℓ^{1+ϵ}) time steps [Ben89, LS90].」
- 1 節 2 頁: KSS の上界を「ℓ ≤ C(m+s−2, s−2) + 1」の形でも引く（Theorem 2.9 では「≥ ℓ」．+1 の有無が 2 箇所で違う）．

### 具体の (ℓ, s, cost) の値

- **2 節には逐次の具体値は 1 つも無い．**
- 付録 F（40 頁，Shor の並列化）に小さい鎖の値が 2 つある（**並列を許す設定で，操作の深さ**．逐次かどうかは明記なし）:
  「For p = 3 the final spooky pebble game is trivial, it uses 2 registers and has depth 3. For p = 5 the spooky pebble game is not quite trivial, one can get away with only using 3 extra registers for a multiplication depth of 8.」
  鎖の長さは「a spooky pebble game on a line graph of length p − 1」なので **ℓ = 2 でレジスタ 2・深さ 3，ℓ = 4 で追加レジスタ 3・深さ 8**．
  【推測】ここの「registers」はペブル数に相当するが，部分積のレジスタ p 個が入力として既にある特殊な状況（入力が複数）なので，2 節の鎖の定義とは初期状態が違う．突き合わせの対象にしない方がよい．
- Remark 4.3（23 頁）: 「s = 4 is the only smaller value for which solutions to the pebble game exist at all; the depth and multiplication count of those solutions are very large (in the thousands)」（ℓ は表 5・6 の log D から決まる 50〜70 台．下の 4 節）．
  → **s = 3 では（ℓ がこの大きさでは）解が存在しない**と述べている．Theorem 2.9 の 1 項目目「space 3 で O(ℓ²)」と矛盾して見えるが，4 節の s はアンシラ込みの重み付きの数え方（Pebble(i) に追加の空間が要る位置がある，付録 B 末尾）なので同じ s ではない【推測】．図 2 左では ℓ = 3 で s = 3 が深さ 2ℓ を達成しており，2 節の定義の下で s = 3 の解は存在する．

---

## 3. 並列の鎖の結果（2.3〜2.4 節，付録 A・B）

### 3.1 構成（Theorem 2.12，11 頁）

「Let α ≈ 1.32 be the real solution to α³ − α − 1 = 0. Then for any ℓ ≥ 7, there exists a parallel spooky pebbling scheme with pebbling space ⌈(log ℓ − log 0.94)/log α − 3⌉ ≤ ⌈2.47 log ℓ − 2.77⌉ and pebbling depth exactly 2ℓ (which is optimal).」

- 脚注 2（2 頁）: 「The prefactor is equal to 1/log α, where α ≈ 1.32 is the real solution to α³ − α − 1 = 0.」
- A 列（Definition 2.13，12 頁）: 「A_1 = 1, A_2 = 2, A_3 = 2, and the recurrence relation A_k = A_{k−2} + A_{k−3}」．A_k（k=1..17）= 1, 2, 2, 3, 4, 5, 7, 9, 12, 16, 21, 28, 37, 49, 65, 86, 114（私の計算．付録 A.1 29 頁に A_4 = 3, A_5 = 4, A.6 32 頁に A_6 = 5, A_7 = 7, A_8 = 9 が明記されており一致）．
- Proposition 2.14（12 頁）: 「For all k ≥ 7, we have A_k ≥ 0.94 α^k」，「For any k ≥ 6, we have A_k = A_{k−1} + A_{k−5}」．
- 証明（15 頁）: k ≥ 7 を A_k ≥ ℓ となる最小とし，空間は「≤ k − 3 ≤ ⌈2.47 log ℓ − 2.77⌉」．長さ A_k のゲームを長さ ℓ に切り詰めても深さは「exactly 2ℓ」．
- Blast は A_k − 1 ステップ，Unblast も A_k − 1 ステップ（Lemma 2.15・2.16，13 頁）．Algorithm 2.1（13 頁）は Blast(0, ℓ−1) → Pebble(ℓ), Unpebble(ℓ) → Unblast(0, ℓ−1) で合計 2(A_k − 1) + 2 = 2A_k = 2ℓ．
- 1.1.1 節 7 頁: 「run steps 2 and 3 in parallel. This would give a pebbling scheme with optimal depth 2ℓ and ≈ 3 log ℓ pebbles.」（Gidney の 2 分割を素朴に並列化した場合）．
- 空間の内訳（Lemma 2.18，14 頁）: blast 中は b_k(t) = ⌈(k − A^{−1}(A_k − t + 1))/2⌉ + 1；unblast の具体値（付録 A.6，32 頁）: 「k = 6: A_k = 5, u_k([1,4]) = [3, 3, 2, 1]」「k = 7: A_k = 7, u_k([1,6]) = [4, 4, 4, 3, 2, 1]」「k = 8: A_k = 9, u_k([1,8]) = [4, 5, 5, 4, 3, 3, 2, 1]」（いずれも i_start のペブルを除いた数）．

### 3.2 下界（Corollary 2.11，11 頁）

「For any s, m such that ℓ > C(m+s−2, s−2), a parallel spooky pebbling game of length ℓ must have depth at least Ω(mℓ/s).」「for any real constant c ≥ 2 there exists another constant c′ > 0 such that at least c′ log ℓ pebbles are needed to achieve depth < cℓ.」

証明は KSS25 Theorem 4.13 の逐次下界を「並列の 1 ステップは高々 s 操作」で割ったもの（「any parallel spooky pebbling game can be converted into a sequential spooky pebbling game where the total number of operations is at most s× the depth of the parallel game」）．**定数は出していない．**

### 3.3 逐次との比較

- **本文で逐次の値と並列の値を数値で並べた箇所は無い．** 比較は表 1（2 頁）の漸近行のみ:
  「[Gid19a, KSS25] | N | Y | ≈ log ℓ | ≈ ℓ log ℓ」 vs 「This work | Y | Y | ≈ 2.47 log ℓ | 2ℓ」．
- 2.4 節 15 頁，A* を作った理由の 1 つ: 「It is not clear from established lower bounds that the constant factor on this pebble count is tight」「One may desire to hold the number of pebbles s constant, and find the optimal-depth solution under that constraint (which may be greater than 2ℓ)」「There may be many solutions achieving that same optimal depth for a given s, and it may be desirable to use some other metric (e.g. minimizing total number of pebble operations) to choose among them」．
  → **総操作数（= 逐次 cost に相当する量）の最小化は「他の指標」として挙げるだけで，値は出していない．**

### 3.4 A* 探索の結果（図 2，16 頁．**本文に数値表は無く図のみ**）

キャプション逐語: 「Figure 2: Results of the A* search for optimal parallel pebble games. In the left figure, we plot the minimum number of pebbles s with which it is possible to achieve the absolute optimal depth 2ℓ, and compare with the space used by the A-sequence construction of Theorem 2.12. In the right figure, we plot the depth as a function of ℓ, for different constant values of the number of pebbles s.」

本文 16 頁: 「We find that while the algorithm of Theorem 2.12 is nearly optimal, the constant factor still has room to be improved slightly.」「once it is no longer possible to achieve the optimal depth of 2ℓ, the optimal depth for very small numbers of pebbles increases dramatically; meanwhile, for slightly larger numbers of pebbles, the depth remains close to optimal even as the pebble game length ℓ continues to increase.」

**図の数値は PDF のベクタデータから取り出した**（`pdftocairo -svg` で PDF 18 頁目を SVG 化し，目盛線の座標で軸を較正して折れ線の頂点を整数に丸めた．x は 1 目盛 = 20ℓ，左 y は 1 目盛 = 2 ペブル，右 y は 1 目盛 = 深さ 20．丸め前の値は全て格子点から 0.01 目盛以内に乗っており，読み違いは無いと判断．**ただし線の s への割り当ては「出発点が早い順 = s 小」という推測**．色は SVG の style に残っていなかった．図の目視〔左の凡例「Minimum possible for depth 2ℓ」が実線，「A sequence」が破線〕と整合）．**彼らの本文の数値ではなく図からの復元値**として扱うこと．
作業ファイル: `/work/tmp/claude-1000/-work-a-dev-overleaf-2026-WiNF/d49e8e11-cce9-471f-8672-db4b28a73333/scratchpad/kmrv/`（`fig2p18.svg`，`fig2_table.md`，`fig2c-18.png`．セッション終了で消える）．

#### 左図（図 2 左）: 深さ 2ℓ を達成する最小ペブル数 s と A 列の構成の空間

折れ線 (19 点): s=3 for ℓ∈[3,3]; s=4 for ℓ∈[4,5]; s=5 for ℓ∈[6,8]; s=6 for ℓ∈[9,12]; s=7 for ℓ∈[13,18]; s=8 for ℓ∈[19,26]; s=9 for ℓ∈[27,37]; s=10 for ℓ∈[38,53]; s=11 for ℓ∈[54,76]; s=12 for ℓ∈[77,107]
折れ線 (22 点): s=5 for ℓ∈[3,7]; s=6 for ℓ∈[8,9]; s=7 for ℓ∈[10,12]; s=8 for ℓ∈[13,16]; s=9 for ℓ∈[17,21]; s=10 for ℓ∈[22,28]; s=11 for ℓ∈[29,37]; s=12 for ℓ∈[38,49]; s=13 for ℓ∈[50,65]; s=14 for ℓ∈[66,86]; s=15 for ℓ∈[87,107]

#### 右図（図 2 右）: ペブル数 s を固定したときの最適深さ d の 2ℓ からの超過 d−2ℓ（点は折れ線の頂点のみ．中間は線形補間）

##### s=4（色の順と出発点から同定）: d=2ℓ は ℓ≤5 まで．描画の終端 ℓ=28（d−2ℓ=136）
頂点: (6,1) (8,3) (9,5) (10,7) (12,13) (13,17) (14,21) (15,26) (16,31) (17,37) (18,43) (20,57) (21,65) (22,73) (23,82) (24,91) (25,101) (26,111) (27,122) (28,133) (28,136)
ℓ:d−2ℓ（ℓ≤60，* は補間値）: 3:0 4:0 5:0 6:1 7:2 8:3 9:5 10:7 11:10 12:13 13:17 14:21 15:26 16:31 17:37 18:43 19:50 20:57 21:65 22:73 23:82 24:91 25:101 26:111 27:122 28:133

##### s=5（色の順と出発点から同定）: d=2ℓ は ℓ≤8 まで．描画の終端 ℓ=52（d−2ℓ=136）
頂点: (9,1) (12,4) (13,5) (15,7) (16,9) (17,11) (18,13) (19,15) (20,17) (21,19) (22,21) (23,23) (24,26) (25,29) (28,38) (29,41) (32,50) (33,53) (35,61) (36,65) (37,69) (39,77) (40,81) (41,85) (42,89) (43,93) (44,97) (45,101) (46,106) (47,111) (48,116) (49,121) (50,126) (51,131) (52,136)
ℓ:d−2ℓ（ℓ≤60，* は補間値）: 3:0 4:0 5:0 6:0 7:0 8:0 9:1 10:2 11:3 12:4 13:5 14:6 15:7 16:9 17:11 18:13 19:15 20:17 21:19 22:21 23:23 24:26 25:29 26:32 27:35 28:38 29:41 30:44 31:47 32:50 33:53 34:57 35:61 36:65 37:69 38:73 39:77 40:81 41:85 42:89 43:93 44:97 45:101 46:106 47:111 48:116 49:121 50:126 51:131 52:136

##### s=6（色の順と出発点から同定）: d=2ℓ は ℓ≤12 まで．描画の終端 ℓ=75（d−2ℓ=136）
頂点: (13,1) (14,2) (15,2) (16,3) (17,4) (18,5) (20,7) (21,8) (23,10) (24,11) (25,12) (26,14) (27,15) (28,17) (29,18) (30,20) (31,22) (32,24) (33,26) (34,28) (35,30) (36,32) (37,34) (39,38) (40,40) (41,42) (42,44) (43,46) (44,48) (46,52) (47,55) (48,57) (49,60) (50,62) (51,65) (52,68) (55,77) (56,80) (59,89) (60,92) (61,95) (63,101) (64,104) (67,113) (68,116) (69,119) (70,122) (71,125) (74,134) (75,136)
ℓ:d−2ℓ（ℓ≤60，* は補間値）: 3:0 4:0 5:0 6:0 7:0 8:0 9:0 10:0 11:0 12:0 13:1 14:2 15:2 16:3 17:4 18:5 19:6 20:7 21:8 22:9 23:10 24:11 25:12 26:14 27:15 28:17 29:18 30:20 31:22 32:24 33:26 34:28 35:30 36:32 37:34 38:36 39:38 40:40 41:42 42:44 43:46 44:48 45:50 46:52 47:55 48:57 49:60 50:62 51:65 52:68 53:71 54:74 55:77 56:80 57:83 58:86 59:89 60:92

##### s=7（色の順と出発点から同定）: d=2ℓ は ℓ≤18 まで．描画の終端 ℓ=105（d−2ℓ=136）
頂点: (19,1) (20,2) (22,2) (24,4) (25,4) (26,5) (28,7) (29,8) (31,10) (32,11) (33,12) (35,14) (36,15) (37,16) (38,17) (39,18) (40,19) (42,21) (43,22) (44,23) (45,24) (46,25) (47,26) (48,28) (50,30) (51,32) (52,33) (53,35) (54,36) (55,38) (56,39) (57,41) (58,43) (59,44) (60,46) (61,47) (62,49) (63,50) (64,52) (65,54) (66,56) (67,58) (68,60) (69,62) (70,63) (71,65) (72,67) (73,69) (74,71) (75,73) (76,75) (78,79) (79,81) (80,83) (81,85) (82,87) (83,89) (84,91) (85,93) (86,95) (87,97) (88,99) (89,101) (90,103) (91,105) (92,107) (93,110) (94,112) (95,114) (96,116) (97,118) (98,120) (99,122) (101,126) (102,129) (103,131) (104,133) (105,135) (105,136)
ℓ:d−2ℓ（ℓ≤60，* は補間値）: 3:0 4:0 5:0 6:0 7:0 8:0 9:0 10:0 11:0 12:0 13:0 14:0 15:0 16:0 17:0 18:0 19:1 20:2 21:2 22:2 23:3 24:4 25:4 26:5 27:6 28:7 29:8 30:9 31:10 32:11 33:12 34:13 35:14 36:15 37:16 38:17 39:18 40:19 41:20 42:21 43:22 44:23 45:24 46:25 47:26 48:28 49:29 50:30 51:32 52:33 53:35 54:36 55:38 56:39 57:41 58:43 59:44 60:46

##### s=8（色の順と出発点から同定）: d=2ℓ は ℓ≤26 まで．描画の終端 ℓ=127（d−2ℓ=112）
頂点: (27,1) (29,1) (30,2) (31,2) (32,3) (34,3) (35,4) (36,5) (37,5) (38,6) (39,6) (40,7) (41,8) (42,8) (43,9) (44,10) (45,11) (46,11) (47,12) (48,13) (49,14) (50,15) (51,16) (52,17) (53,17) (54,18) (55,19) (56,20) (57,21) (58,22) (59,23) (60,24) (61,25) (63,27) (64,28) (67,31) (68,32) (70,34) (71,35) (73,37) (74,38) (75,39) (77,41) (78,42) (79,44) (80,45) (82,47) (83,48) (84,49) (85,51) (86,52) (87,53) (88,54) (89,56) (90,57) (91,58) (92,59) (93,61) (94,62) (95,63) (96,65) (97,66) (98,68) (99,69) (100,70) (101,72) (102,73) (103,75) (104,76) (105,78) (106,79) (107,81) (108,82) (109,84) (110,85) (111,87) (112,88) (113,90) (114,91) (115,92) (116,94) (117,96) (118,97) (119,99) (120,101) (121,102) (122,104) (123,105) (124,107) (125,108) (126,110) (127,112)
ℓ:d−2ℓ（ℓ≤60，* は補間値）: 3:0 4:0 5:0 6:0 7:0 8:0 9:0 10:0 11:0 12:0 13:0 14:0 15:0 16:0 17:0 18:0 19:0 20:0 21:0 22:0 23:0 24:0 25:0 26:0 27:1 28:1 29:1 30:2 31:2 32:3 33:3 34:3 35:4 36:5 37:5 38:6 39:6 40:7 41:8 42:8 43:9 44:10 45:11 46:11 47:12 48:13 49:14 50:15 51:16 52:17 53:17 54:18 55:19 56:20 57:21 58:22 59:23 60:24

##### s=9（色の順と出発点から同定）: d=2ℓ は ℓ≤37 まで．描画の終端 ℓ=102（d−2ℓ=43）
頂点: (38,1) (40,1) (41,2) (43,2) (44,3) (46,3) (47,4) (49,4) (50,5) (51,5) (52,6) (53,6) (54,7) (56,7) (57,8) (58,9) (60,9) (61,10) (62,10) (63,11) (64,12) (65,12) (67,14) (68,14) (69,15) (70,16) (71,17) (72,17) (73,18) (74,19) (75,20) (76,20) (77,21) (78,22) (79,23) (80,24) (81,24) (82,25) (83,26) (84,27) (85,27) (86,28) (87,29) (89,31) (90,32) (91,33) (92,33) (93,34) (94,35) (95,36) (96,37) (97,38) (98,39) (100,41) (101,42) (102,43)
ℓ:d−2ℓ（ℓ≤60，* は補間値）: 3:0 4:0 5:0 6:0 7:0 8:0 9:0 10:0 11:0 12:0 13:0 14:0 15:0 16:0 17:0 18:0 19:0 20:0 21:0 22:0 23:0 24:0 25:0 26:0 27:0 28:0 29:0 30:0 31:0 32:0 33:0 34:0 35:0 36:0 37:0 38:1 39:1 40:1 41:2 42:2 43:2 44:3 45:3 46:3 47:4 48:4 49:4 50:5 51:5 52:6 53:6 54:7 55:7 56:7 57:8 58:9 59:9 60:9

##### s=10（色の順と出発点から同定）: d=2ℓ は ℓ≤53 まで．描画の終端 ℓ=91（d−2ℓ=14）
頂点: (54,1) (57,1) (58,2) (60,2) (61,3) (64,3) (65,4) (67,4) (68,5) (70,5) (71,6) (72,6) (73,7) (75,7) (76,8) (77,8) (78,9) (80,9) (81,10) (82,10) (83,11) (84,11) (85,12) (87,12) (88,13) (89,13) (90,14) (91,14)
ℓ:d−2ℓ（ℓ≤60，* は補間値）: 3:0 4:0 5:0 6:0 7:0 8:0 9:0 10:0 11:0 12:0 13:0 14:0 15:0 16:0 17:0 18:0 19:0 20:0 21:0 22:0 23:0 24:0 25:0 26:0 27:0 28:0 29:0 30:0 31:0 32:0 33:0 34:0 35:0 36:0 37:0 38:0 39:0 40:0 41:0 42:0 43:0 44:0 45:0 46:0 47:0 48:0 49:0 50:0 51:0 52:0 53:0 54:1 55:1 56:1 57:1 58:2 59:2 60:2

##### s=11（色の順と出発点から同定）: d=2ℓ は ℓ≤76 まで．描画の終端 ℓ=88（d−2ℓ=3）
頂点: (77,1) (81,1) (82,2) (85,2) (86,3) (88,3)
ℓ:d−2ℓ（ℓ≤60，* は補間値）: 3:0 4:0 5:0 6:0 7:0 8:0 9:0 10:0 11:0 12:0 13:0 14:0 15:0 16:0 17:0 18:0 19:0 20:0 21:0 22:0 23:0 24:0 25:0 26:0 27:0 28:0 29:0 30:0 31:0 32:0 33:0 34:0 35:0 36:0 37:0 38:0 39:0 40:0 41:0 42:0 43:0 44:0 45:0 46:0 47:0 48:0 49:0 50:0 51:0 52:0 53:0 54:0 55:0 56:0 57:0 58:0 59:0 60:0


#### 図 2 からの読み取りに対する注記

- 左図の実線（深さ 2ℓ を達成する最小 s）と右図の各 s の「d − 2ℓ = 0 である最大の ℓ」は完全に一致する（s=4→5，5→8，6→12，7→18，8→26，9→37，10→53，11→76）．独立に復元した 2 本が一致するので，復元と s の割り当ては信頼してよい．
- 左図の破線「A sequence」は，ℓ ∈ [3,7] で 5，[8,9] で 6，[10,12] で 7，…，[87,107] で 15．これは「k ≥ 7 を A_k ≥ ℓ となる最小とした k − 2」に等しい．**Theorem 2.12 の主張は k − 3** なので，**図の破線は定理の上界より 1 大きい**（私の計算: ℓ=7 → k=7 → k−3=4 だが図は 5）．位置 0 のダミーのペブルを数えたか，描画コードの規約違いかは不明【推測】．突き合わせでは定理本文の k − 3 を正とし，図の破線は参考に留める．
- 右図の縦軸は「Depth above optimal d − 2ℓ」で，描画は d − 2ℓ ≤ 136 で切れている（s=4 は ℓ=28，s=5 は 52，s=6 は 75，s=7 は 105 まで）．s=8 は ℓ=127，s=9 は 102，s=10 は 91，s=11 は 88 で描画が終わる（計算資源の限界【推測】．Remark 4.3 に n=4096・BKZ-60 で s=12 が計算できなかったとある）．
- 右図は折れ線なので，頂点の間の ℓ は線形補間値（上の表で * 付き）．頂点は整数格子に乗っている．
- **右図は並列の深さ**であり，こちらの逐次の T_UP・W と直接は比較できない．比較できるのは次の形: (a) 彼らの並列深さ d(ℓ, s) ≤ こちらの逐次 cost（並列は逐次を含む）．(b) Corollary 2.11 の形で，こちらの逐次 cost の厳密値から並列深さの下界 ⌈cost(ℓ, s)/⌊s/2⌋⌉ 程度【推測: 1 ステップに同時に動かせる操作は active set が互いに素なので高々 ⌊s/2⌋ 程度】を出し，図の値と比べる．

### 3.5 公開コード（GitHub GregDMeyer/parallel-spooky-pebbling v0.1，Zenodo 10.5281/zenodo.17298960）

本文 16 頁・脚注 3（2 頁）が指す．リポジトリの中身は `README.md`，`find_pebblings.jl`（12.9 KB），`PebbleGraph.jl`（2.6 KB），`.zenodo.json`，`LICENSE`，`.gitignore` の 6 ファイルで，**結果のデータファイルは入っていない**（2026-10-24 に GitHub API で一覧を確認．個人情報は送っていない）．

README 逐語: 「The code in this repository finds the lowest-depth parallel spooky pebbling scheme to pebble a length-`l` line graph, given a constant number of pebbles `s`. In "save" mode, it will save to disk an optimal-depth pebbling for all line graphs of length up to `l`. It can also compute "touch-and-go" pebblings, in which the final pebble (output register) is taken to be measured immediately once it obtains a value, and its qubits reused during the rest of the pebble game.」

コードを読んで分かること（`find_pebblings.jl`）:
- 終状態から逆向きの幅優先（層ごと）探索．ゴーストは状態に持たず，付録 B の「ゴースト配置はペブル配置から決まる」を使う．
- `max_pebbles = s−1`（非 touch-and-go）「because the final pebble is sitting around」．touch-and-go では `s`．
- 深さの表示は `depth - (2l-1)`（save モードの標準出力）で，**本文の 2ℓ と 1 ずれる規約**．コード内の `l = get_rightmost_idx(state)+2`．**本文の ℓ とコードの l の対応は未確認**【推測: 1 ずれる可能性】．
- **逐次の cost（総操作数）を数える機能は無い．** 付録 B 末尾にある「アンシラの重み付き最適化」も v0.1 には入っていない（4 節の表 5・6 を再現するコードではない）．
- Julia は手元に無い（`which julia` 空）．再実行はしていない．

---

## 4. Regev 因数分解への応用で使う鎖の長さと s（4 節，19〜24 頁，表 5・6 は 44 頁）

- 鎖の長さの定義（4.3 節 23 頁）: 「we then experimentally (see Section 2.4) find the optimal-depth pebbling game with length ℓ := (w + 1)⌊(log D − 1)/w⌋ + 1 and s pebbles」．窓は w = 2 のみ（「We report results for w = 2」）．
- 理論版（Theorem 4.1，19 頁；付録 D 37〜38 頁）: 「a line graph of length 2 log D」「Here ℓ = 2 log D, so the depth will be 4 log D n-bit multiplications」，空間「at most 1.3(2n + S_×(n) + o(n)) log log D」（付録 D の計算では 1.24）．
- s の範囲（4.2 節 22 頁）: 「We restrict attention to s ∈ [5, 12] since each additional pebble adds n qubits.」Remark 4.3（23 頁）: 「we record results for s ∈ {5, 7, 12}」「s = 4 is the only smaller value for which solutions to the pebble game exist at all; the depth and multiplication count of those solutions are very large (in the thousands)」「s = 12 achieves the absolute optimal depth of 2ℓ for most settings of the parameters」「for n = 4096 and BKZ-β = 60, we report results for s = 8 instead of s = 12, as our computational resources were not sufficient」．
- **表 5・6 の s はアンシラの重み付き（Pebble(i) で i ≡ 1 (mod w+1) の位置は t レジスタ分の空間を余分に使う）なので，2 節の s とは同じでない**（付録 B 末尾「we include the space cost of the temporary ancillas needed to hold the value t … in the optimization」）．
- Depth・Per run は「mod N multiplications」の数（4.2 節 21 頁: Algorithm 4.1・4.2 で out を変える操作 1 回 = 1）．**Per run は彼らの pebbling cost（Pebble + Unpebble の総数）に等しい**【推測: Pebble(i)・Unpebble(i) が各 1 乗算で，t の計算は数えないため】．

### 表 5（44 頁）: n = 2048，w = 2．列 = BKZ-β，d，m，log D，s，Depth，Per run，Overall，Qubits/n

| β | d | m | log D | ℓ = 3⌊(log D−1)/2⌋+1（私の計算） | s | Depth | Per run | Overall | Qubits/n |
|---|---|---|---|---|---|---|---|---|---|
| 60 | 90 | 203 | 59 | 88 | 5 | 465 | 500 | 101500 | 7.6 |
| 60 | | | | | 7 | 263 | 370 | 75110 | 9.6 |
| 60 | | | | | 12 | 175 | 295 | 59885 | 14.6 |
| 120 | 90 | 242 | 56 | 82 | 5 | 418 | 451 | 109142 | 7.5 |
| 120 | | | | | 7 | 240 | 341 | 82522 | 9.5 |
| 120 | | | | | 12 | 163 | 266 | 64372 | 14.5 |
| 160 | 94 | 242 | 54 | 79 | 5 | 396 | 429 | 103818 | 7.5 |
| 160 | | | | | 7 | 229 | 326 | 78892 | 9.5 |
| 160 | | | | | 12 | 157 | 253 | 61226 | 14.5 |
| 200 | 94 | 255 | 53 | 79 | 5 | 396 | 429 | 109395 | 7.4 |
| 200 | | | | | 7 | 229 | 326 | 83130 | 9.4 |
| 200 | | | | | 12 | 157 | 253 | 64515 | 14.4 |

### 表 6（44 頁）: n = 4096，w = 2

| β | d | m | log D | ℓ（私の計算） | s | Depth | Per run | Overall | Qubits/n |
|---|---|---|---|---|---|---|---|---|---|
| 60 | 162 | 314 | 72 | 106 | 5 | 610 | 652 | 204728 | 7.8 |
| 60 | | | | | 7 | 334 | 475 | 149150 | 9.8 |
| 60 | | | | | 8 | 287 | 444 | 139416 | 10.8 |
| 120 | 166 | 371 | 67 | 100 | 5 | 561 | 600 | 222600 | 7.7 |
| 120 | | | | | 7 | 310 | 446 | 165466 | 9.7 |
| 120 | | | | | 12 | 200 | 381 | 141351 | 14.7 |
| 160 | 166 | 388 | 65 | 97 | 5 | 537 | 575 | 223100 | 7.6 |
| 160 | | | | | 7 | 298 | 432 | 167616 | 9.6 |
| 160 | | | | | 12 | 193 | 345 | 133860 | 14.6 |
| 200 | 162 | 401 | 64 | 94 | 5 | 513 | 550 | 220550 | 7.5 |
| 200 | | | | | 7 | 286 | 419 | 168019 | 9.5 |
| 200 | | | | | 12 | 187 | 326 | 130726 | 14.5 |

検算メモ（私の計算）: 表 5 β=160/200 の s=12 で Depth 157 = 2ℓ − 1（ℓ = 79）．β=120 で 163 = 2·82 − 1，β=60 で 175 = 2·88 − 1．表 6 β=120 で 200 = 2·100，β=160 で 193 = 2·97 − 1，β=200 で 187 = 2·94 − 1．**s=12 の Depth は 2ℓ か 2ℓ − 1 で，「2ℓ − 1」が出るのは 4 節の最適化が終端のペブルを即測定して外す（4.1 節 19 頁 項目 2「We immediately measure the final value … rather than insisting on keeping it around」= コードの touch-and-go）ためと解釈できる**【推測】．Remark 4.3 の「s = 12 achieves the absolute optimal depth of 2ℓ for most settings」と整合．Overall = Per run × m（例: 500 × 203 = 101500 ✓，295 × 203 = 59885 ✓）．

### 4.3.1 節（23〜24 頁）の要約文（逐語）

- 「For n = 2048, Fibonacci-based approaches (Table 4) … multiplication depth of 560-620 … However when using spooky pebbling with a similar qubit count (s = 12), our results requiring a multiplication depth of only 157-175 (Table 5). Using 5 or 7 pebbles yields somewhat worse multiplication depth (396-465 and 229-263, respectively)」
- 「For n = 4096, … spooky pebbling with 8-12 pebbles fares better, requiring a multiplication depth of only 187-200 (for BKZ-120/160/200 using 12 pebbles) or 287 (for BKZ-60 using 8 pebbles) (Table 6). Even with 5 pebbles, the multiplication depth is only 513-610.」
- 「for n = 2048 when using spooky pebbling with 12 pebbles, the total number of mod N multiplications per run ranges from 253-295, and for n = 4096 it ranges from 326-345.」
- 「the gap between depth and total # of mod N multiplications per run is small. This is in contrast to the Fibonacci case (Table 4) where there is a gap of a factor of 2.」

（表 3〔Shor〕・表 4〔Fibonacci 版 Regev〕は鎖の数値ではないので省く．必要なら PDF 41〜43 頁．）

---

## 5. 未解決・今後の課題として書いているもの

鎖の spooky pebbling に関して「open problem」「future work」と明示した節は無い．それに相当する記述:

1. 2.4 節 15 頁（A* を作った動機として）: 「It is not clear from established lower bounds that the constant factor on this pebble count is tight」（≈2.47 log ℓ の定数が最適かは不明）．16 頁: 「the constant factor still has room to be improved slightly」．
2. 同 15 頁: 「One may desire to hold the number of pebbles s constant, and find the optimal-depth solution under that constraint (which may be greater than 2ℓ)」—— s 固定の最適深さは A* の数値のみで，**閉じた式も漸近式も与えていない**．
3. 同 15 頁: 「it may be desirable to use some other metric (e.g. minimizing total number of pebble operations) to choose among them」—— **総操作数（逐次 cost に相当）の最小化は未着手．**
4. Corollary 2.11（11 頁）: 下界は Ω(mℓ/s) の形で定数無し．c′ の値も陽に出していない．
5. 2.3 節冒頭 11 頁: 「We focus on the case of a logarithmic number of pebbles because with O(1) pebbles we cannot asymptotically benefit from parallelism」—— **O(1) ペブルの並列は扱わない**（右図の s=4..11 は数値のみ）．
6. 「Outlook and caveats」（4 頁）は Regev 側の話: 「we see no inherent obstacle to further optimization that builds on top of these ideas」「we are certain that further improvements are possible」．
7. Remark 4.3（23 頁）: n=4096・BKZ-60 の s=12 は計算資源不足で未計算．
8. 「Other applications」（5 頁）: 「our pebbling techniques will find applications in quantum cryptanalysis beyond integer factorization, and in quantum circuit compilation more broadly」（要旨）．

**彼らは逐次の鎖の厳密値（任意の s, ℓ の cost の閉じた式）には触れていない．** KSS25 の Lemma 3.5 / Theorem 4.13 を「tight up to constant factors」と引くのみ（10 頁）．したがって，こちらの `T_UP = max_m(2mn − β_m(s))`（Envelope.lean）と W の恒等式（Work.lean）は，この論文の結果と重ならず，彼らの「総操作数の最小化」という未着手の指標に答える形になる【推測．新規性の判定は novelty 側で】．

---

## 6. 突き合わせの前に決めること（こちら側の作業）

1. こちらの n と彼らの ℓ の対応（始点を含むか）．彼らは位置 0..ℓ，位置 0 は常にペブルで空間に数えない．
2. こちらの s（ペブル数上限）が始点を含むか．彼らは含まない（i ∈ [1, ℓ]）．
3. 比較する量は W（Pebble+Unpebble の総数，Ghost 0）．彼らの Remark 2.5 により逐次では cost = depth．こちらの T_UP（Ghost を数える手数）とは別．
4. 終端の扱い: 彼らの定義は全部 empty に戻す（こちらの UP 型）．4 節の表の Depth は touch-and-go（終端を即測定）で 2ℓ − 1 が出る【推測】．
5. 並列の値（図 2 右）は上界側の参考にしかならない．下界側は Corollary 2.11 の割り算（1 ステップの操作数 ≤ ⌊s/2⌋ 程度）で，こちらの逐次厳密値から出せる．

## 読んだ範囲

- PDF 全 44 頁のうち，1〜2 節（1〜16 頁）・4 節（18〜24 頁）・付録 A（29〜34 頁）・B（35〜36 頁）・D（37〜38 頁）・F（39〜40 頁）・G（41〜44 頁）は全文．3 節（16〜18 頁）・付録 C（36〜37 頁）・E（38〜39 頁）は grep と流し読みのみ（鎖の数値は無いことを確認）．
- 図 2 は PDF のベクタから数値化（上記）．図 1 は Regev の時間-空間図なので扱わない．
- 外部アクセス: GitHub API（リポジトリのファイル一覧と 3 ファイルの取得）のみ．arXiv への再取得はしていない．個人情報は送っていない．
