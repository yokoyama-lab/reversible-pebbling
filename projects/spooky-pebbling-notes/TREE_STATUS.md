# 完全二分木の spooky pebble game（台帳 Q35 / WiNF 原稿 P2）

鎖（Q7）の状態は README.md の現状節。こちらは木（2026-09-29〜10-02 のセッション「P2」）だけを扱う。

> ✅ **2026-10-06: 下の「次の作業候補 2」（log log n の差）は決着した。** 最小ペブル数 h+1 での時間は
> **Θ(n log n / log log n)**（上界をブロック構成で改良。KSS Thm 5.5 の O(n log n) は漸近最適でない）。
> Lean: `spooky-pebbling-lean` の `SpookyTree/Upper*.lean`（commit 124dc44・14f9c87・4294897、`time_theta`・`time_theta_kss`）。
> 経緯と検査は `tree-gap/RESULT.md`、台帳は R-Q35-03。**定数は詰まっていない**（下界 1/2・上界 8（Lean）/2（紙））。
> **原稿 P2 は未更新**（「改良の余地は高々 log log n 因子」のまま）。P1 は穴 (b) で言及済み。

## 現在の状態（handoff: 2026-10-02）

### 読む順
1. `SKETCH_2026-09-29_tree_lower_bound.md` — 下界の全経緯（第 1〜7 回。第 6 回が定理の整理、第 7 回が Lean）。撤回・訂正の記録を含む
2. `FINDINGS_2026-09-29_binary_tree_time.md` — 厳密値・上界・下界・正規形の否定の要約
3. `~/dev/github.com/yokoyama-lab/spooky-pebbling-lean/README.md` の「木（完全二分木）」節と `SpookyTree/`（機械証明）
4. `~/dev/overleaf/2026-WiNF/P2-spooky-tree.tex`（2 ページ原稿）と `code/p2_*`（数値の正本）
5. `PREREG_2026-09-29_tree_h5.md`・`PREREG_2026-09-29_tree_equality_threshold.md`（事前登録と結果）

### 確定している事実（再確認不要）
- **下界（層 1・Lean）**: 上限 h+1 の正しい手順の手数 T について
  T + 1 ≥ 2(2^h−1) + (⌊(h−1)/(2⌊log₂h⌋+3)⌋ − 2)·2^h、すなわち T(T_h,h+1) = Ω(n log n / log log n)。
  `SpookyTree.time_lower_bound_log`（spooky-pebbling-lean commit a96d392、7 モジュール約 930 行）。公理は標準 3 つ、sorry 0、
  変異注入 6 種で検出、proof-gatekeeper の独立 5 点ゲート緑。ghost 無条件の広いモデルなので KSS の意味論に移る
- **一般の下界（紙）**: T(T_h,p) ≥ 4n−2p−1。等号になる最小の p は h=2..5 で 3,5,7,9（h=6 は未確定。候補 A=2h−1 は h≥10 で偽という紙の証明あり・未査読）
- **厳密値（層 2）**: T(T_h,h+1) = 5,21,57,141（h=2..5）。h=5: p=7 で 121、p=8 で 111。p=h では到達不能（h≤5）
- **KSS Thm 5.5 の構成**: (2h−3)2^h+1 手（h=2..10、ペブルの無い頂点への remove は数えない解釈）。h≥3 で非最適
- **h=6 の上界**: 333（証人 `~/dev/overleaf/2026-WiNF/code/results_P2_h6_witness333.txt`、2 再生器で合法）
- **棄却済み**: 候補式 (h−1)2^h+4h−7（h=6 の 333 で）、T(h)=2T(h−1)+4h−1（h=5 で）。深さ d で区切る正規形の族（h=d+3 で外れる）。
  「主張 K＋補題 R」の割り振り（証人 333 で 73/76）
- **新規性**: KSS の前方引用 10 本の全文で、木の時間下界・改良構成・厳密値は出現 0（KSS を引用しない独立な先行は未調査）
- 台帳: Q35（partial・層 1）、R-Q35-01（層 2、厳密値と非最適性）、R-Q35-02（層 1、下界）

### 次の作業候補
1. `spooky-pebbling-lean` を公開するか決める（原稿 P1・P2 が URL を引用。paper_check で NG）— **ユーザー判断**
2. log log n の差: 交換論法（SKETCH 第 5 回末尾の算術）で Ω(n log n) を狙うか、逆に O(n log n / log log n) の構成を探す
3. KSS を引用しない独立な先行の novelty-check（木の spooky / 測定つき可逆計算の時間下界）

### 注意
- 道具: `code/p2_symbfs.cpp`（h≤5 の厳密値。自己同型で割った BFS、64 ビット）、`code/p2_lift2.cpp`（上界探索。h=6 CSPAN=3 VMODE=1 で 333、
  CSPAN=4 や h=7 は 40GB で打ち切り）、`code/p2_sat.py`（木の SAT。h≥5 には弱い）、`code/p2_normal.cpp`（正規形の族）
- 下界の解析スクリプトは `lb/`（`critic3/` `critic4/` `review_chain/` は批判者・検算者のもの）
- SKETCH の前半（第 1〜3 回）には撤回した主張がある。冒頭の訂正ブロックを先に読むこと
- `notes/spooky-pebbling/` の未追跡ファイル（one_T.py、spooky_bfs.c など）と `sat_spooky.py` の変更は別セッションのもの。触らない
