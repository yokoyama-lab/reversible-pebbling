# 完全二分木の spooky pebble game（台帳 Q35 / WiNF 原稿 P2）

鎖（Q7）の状態は README.md の現状節。こちらは木だけを扱う
（2026-09-29〜10-02 のセッション「P2」、10-06 のセッション「spooky-tree-gap」と「winf-spooky」）。

## 現在の状態（handoff: 2026-10-07）

**2026-10-06 に決着した。** 最小ペブル数 h+1 での最小手数は
**T(T_h, h+1) = (2 + o(1))·2^h·h/log₂h = (2 + o(1))·n log₂n / log₂log₂n**。
増大度（Θ(n log n / log log n)）も先頭の係数（2）も Lean で証明済み。KSS Thm 5.5 の O(n log n) の構成は漸近最適でない。

### 読む順
1. `tree-gap/RESULT.md` — 決着の全記録（結論・Lean の定理文・紙の証明・検査・「追記」「追記 2」・誤りの一覧）
2. `~/dev/github.com/yokoyama-lab/spooky-pebbling-lean/README.md` の「木（完全二分木）」節と `SpookyTree/`
   （下界 7 ファイル、上界 `Upper*.lean` 5 ファイル、係数 2 の `Sharp*.lean` 3 ファイル）
3. `~/dev/overleaf/2026-WiNF/P2-spooky-tree.tex`（原稿。3 ページ、上限 4 ページ、締切 2026-10-23 23:59）と `code/p2_*`（厳密値の正本）
4. `tree-gap/novelty/COUNTS.md`（新規性の計数）と `~/dev/notes/paper-index/取得待ち.md` の #35・#57〜#59
5. `SKETCH_2026-09-29_tree_lower_bound.md`（下界の旧経緯。固定の深さでの切断まで。冒頭の訂正ブロックを先に読む）と
   `FINDINGS_2026-09-29_binary_tree_time.md`（厳密値と棄却した式。**増大度についての記述は古い**）

### 確定している事実（再確認不要）
- **Lean（spooky-pebbling-lean。origin/main = a5b10ab に載っている。リポジトリは private）**
  - 下界 `time_lower_bound_log`（a96d392）: T + 1 ≥ 2(2^h−1) + (⌊(h−1)/(2⌊log₂h⌋+3)⌋ − 2)·2^h
  - 上界 `time_upper_bound`・`time_upper_bound_log`（124dc44）: h ≥ 4 で ⌊log₂h⌋(T+3) ≤ 2(4h+⌊log₂h⌋)2^h の妥当な手順がある。`time_theta` が上下を並べた形
  - KSS の意味論（ゴーストは導出）への移行 `validK_of_valid`・`time_theta_kss`（14f9c87）。`ValidK` と KSS Def 2.6/2.7 の集合列との対応だけは紙（鎖の `KSSModel.lean` と同じ扱い）
  - 係数 2（18c8977）: `time_lower_bound_sharp`: T + 1 ≥ 2(2^h−1) + 2·2^h·(h − 3⌈log₂(h+1)⌉ − 1)/(log₂(h+1)+4)。
    `time_upper_bound_sharp`: h ≥ 32、lg = ⌊log₂h⌋、ll = ⌊log₂lg⌋ で lg·(lg−2ll)·(T+3) ≤ 2(lg·h+4h+lg²)·2^h。`time_sharp_kss` が KSS の意味論で並べた形
  - 公理はどれも標準 3 つ、sorry 0、新しい 8 ファイルの警告 0。既存の 7 ファイルは a96d392 から無変更（`Game.lean:69`・`Arith.lean:19` に警告が 1 件ずつある）
  - 検査: 上界 5 ファイルは proof-gatekeeper の独立 5 点ゲートを通過（別設計の変異 16 種すべて検出）。作成時の変異は上界 10/10、係数 2 が 6/6、対照はすべて通過。
    **係数 2 の 3 ファイルには独立のゲートをまだ通していない**
- **収束は非常に遅い**（o(1) は log log h / log h）。係数（÷ 2^h·h/log₂h）は h = 128 で下界 1.13・再生した構成 3.06、h = 2^20 で下界 1.67・上界 4.0。実用的な高さでは 2 倍ほどの差が残る
- **ブロック構成（KSS の意味論。紙の証明＋再生）**: 切り 0 = d_0 < … < d_m = h に対し手数 2(m·2^h − Σ2^{d_j}) − 1。条件は RESULT.md の定理 U。
  生成器 `tree-gap/blockgen.py`、再生器 `tree-gap/replay.py`（C++ 版あり）。h ≤ 27 と h = 31 で上限 h+1 に合格。h ≥ 7 で KSS より短い（h = 7 で 977 対 1409）。
  3 ≤ h ≤ 6 では最小手数に届かない
- **KSS Thm 5.5 の構成**: (2h−3)2^h+1 手（ペブルの無い頂点への remove は数えない解釈。h = 2..24 で確認。KSS が述べた値ではない）
- **一般の下界（紙）**: T(T_h,p) ≥ 4n−2p−1。等号になる最小の p は h=2..5 で 3,5,7,9（h=6 は未確定）
- **厳密値（層 2）**: T(T_h,h+1) = 5,21,57,141（h=2..5）。h=5: p=7 で 121、p=8 で 111。p=h では到達不能（h≤5）。h=6 の上界 333
  （証人 `~/dev/overleaf/2026-WiNF/code/results_P2_h6_witness333.txt`）
- **棄却済み**: 候補式 (h−1)2^h+4h−7、T(h)=2T(h−1)+4h−1、深さ d で区切る正規形の族、「主張 K＋補題 R」の割り振り、
  **Ω(n log n)（偽。交換論法の線は成り立たない）**
- **新規性**: 語（tree・spooky・log log）を事前登録して全文 19 本を数え、木の spooky pebbling の手数の改良・下界・増大度の決定は出現 0。
  **2026-10-11 に未取得の 4 本（#35 は ePrint 版，#57・#58・#59）と #36 を全文で数え，該当 0．全文で数えた範囲では閉じた**（`tree-gap/novelty/COUNTS.md` の追補 2026-10-11）
- 反映済み: 原稿 P2（Overleaf 2e2520e まで）、P1 の言及、台帳 Q35（partial）・R-Q35-01〜04

### 一般空間への拡張（2026-10-07、有限上下界をLean化）

`tree-gap/TRADEOFF_2026-10-07.md` に一般ペブル上限の導出を追加した。
ゴースト数無制限、h+1 ≤ p ≤ 2^h−1 で T(T_h,p)=Θ(2^h·h/log₂ p)。
さらに log₂ p=o(h) なら先頭係数は2。既存の `sharp_main` の一般 cap への特殊化と、
p≥2h での等幅ブロック構成から従う。
**一般下界と同じ主項の構成上界、全域の一様な不等式をLeanで証明した**
（`SpookyTree/Tradeoff{Lower,Upper,Final,Theta}.lean`、11定理）。
検査と紙の有限上界との差は `tree-gap/LEAN_2026-10-07_tradeoff.md`。
新しいモジュールの警告0、標準3公理のみ、変異8種類をすべて検出。
独立査読とlittle-o表記自体の極限形式化は未実施。
新規性は 2026-10-11 に全文で数えた範囲で閉じた（#35 だけ ePrint 版）。係数2を全 p に主張していない。

一般上限のブロック族内最適化 `tree-gap/tradeoff.py` と検査 `test_tradeoff.py` を追加。
全切り510通り、最適構成の再生53件、等幅構成の再生19件、BFS5点、
算術条件3,031点、全整数上限968点で不一致0。全戦略の厳密値とは区別する。
次は独立検査と極限形式化、p=n^ε での鋭い定数、有限高さの厳密値。

### 2026-10-19〜24 の追記（Lee–Lee–Jeong，仕事量，投稿後）

- **Lee–Lee–Jeong arXiv:2610.09434（10-07 公開，v1 のみ，全文読了 10-19）が木の Θ(n log n/log log n) と一般 s の Θ(nh/log(s+1))，並列の深さ，全ての充満二分木での下界を先に出した。** 定数は無い。
  10-20 ユーザー決定: 重なっても P2 を WiNF で発表（増大度は同論文に帰属，係数 2・Lean・仕事量・厳密値を本稿の寄与に。Overleaf 2e286bb）。
- **仕事量の恒等式** `SpookyTree/Work.lean`（d12c362）: LLJ の仕事量 W = #Peb + #Unp（ghost 0）で **W* = (T*+1)/2 + 2^h − 2**（全 h≥1・全 cap，`work_feasible_iff`）。
  仕事量での先頭の係数は 1。独立 proof-gatekeeper 緑（限定つき，`tree-gap/GATE_WORK_2026-10-20.md`）。台帳 R-Q35-05 層 1。
  **⚠ 等式は LLJ の規則（ghost に前提なし＝`Valid`）でだけ成り立つ。KSS の定義（`ValidK`）では h=3・cap=4 で W*=20≠17**（独立 2 実装）。手数は両定義で等しい。
  新規性: 等式そのものは見当たらないが，Unp→Ghost の置き換えは鎖で KSS v1 Lemma 24・KMRV 付録 B に既出。等式は LLJ の 2 行の組合せで出る＝系の位置づけ（`tree-gap/novelty/WORK_IDENTITY_2026-10-20.md`）。
- 鎖側: `EnvelopeBinom.lean`（d4358d6）も独立ゲート緑（`keystone/GATE_BINOM_2026-10-20.md`）。
- **一般の p の先頭係数（10-24 に棚卸し）**: 上の 10-07 節の `Tradeoff{Lower,Upper,Final,Theta}.lean` は **未コミットのまま**（Lean リポの作業ツリー，0 sorry，10-07 の olean あり）。
  そこにある下界 `time_lower_bound_cap_sharp`（T+1 ≥ 2(2^h−1) + 2·2^h(h − 3⌈log₂p⌉ − 1)/(log₂p + 4)）と上界 `time_upper_bound_cap_log`（p ≥ 2h で T+3 ≤ 2((h−1)/(⌊log₂p⌋−1) + 2)2^h）から，
  **log₂p = o(h) なら係数 2 は既に出ている**。P2 の「おわりに」が次の課題と書いた「一般のペブル数での係数」で残るのは **p = n^ε（log₂p = εh）の領域**だけで，
  上の 2 式は 2(1−3ε)/ε ≤ c(ε) ≤ 2/ε + 4 までしか挟まない（ε<1/3）。
  10-24 の実測（`tree-gap/tradeoff_eps.py`，ブロック族内の最良，上界側のみ）: T/(2^h·h/log₂p) は **ε=1/4 で 2.4687（5 ブロック），ε=1/2 で 2.75（3 ブロック）** に h=24 以降で収束（h≤64）。
  Lean の `time_upper_bound_cap_log` の係数 2(1+2ε)（3.0・4.0）より小さい。下界側は ε=1/4 で 2(1−3ε)=0.5，ε=1/2 では自明。**c(ε) の決定は未着手**（下界が弱い）。
- 締切 2026-10-23 23:59 は過ぎた。Lean リポは PRIVATE のまま（P1・P2 の bibitem「（非公開の証明資料）」も残る）。公開前の片づけは WiNF の CLAUDE.md 10-12 節 1。

### 次の作業候補
1. ~~未読 4 本を読んで新規性を閉じる~~（2026-10-11 済。次は原稿の関連研究の書き換え）。 ユーザーがブラウザで取得（`~/dev/notes/paper-index/取得待ち.md` の #35 が最優先）→ 索引を refresh →
   `tree-gap/novelty/count.sh` で同じ語を数える。0 なら原稿の関連研究を書き換えられる
2. ~~係数 2 の 3 ファイル（`SpookyTree/Sharp*.lean`）に独立の proof-gatekeeper を通す~~（2026-10-11 PASS，`tree-gap/GATE_SHARP_2026-10-11.md`）（上界のときは約 7.6 万トークン。投稿前に）
3. `spooky-pebbling-lean` を公開するか決める（原稿 P1・P2 が URL を引用）— **ユーザー判断**
4. 研究の続き（任意）: 二次の項（log log h/log h の係数）と実用的な h での 2 倍の差、p > h+1 のトレードオフ（定理 U は上限が一般でも成り立つ）、小さい h の厳密値の式

### 注意
- `tree-gap/` は dev リポジトリで**未追跡**（37MB。うち 32MB は `novelty/pdf/` の論文 PDF）。コミットするなら PDF・実行ファイル
  （`blockgen_cpp`・`replay_cpp`・`kss_gen`）・`__pycache__` を除く
- Lean のビルドは <host> で回すしかない（Mathlib のビルド済み成果物が艦隊に無い。sf1 への転送は毎秒 1MB 弱）。`nice -n 19`・`LEAN_NUM_THREADS=2`・1 本ずつ。
  変異注入は `tree-gap/lean_mutants.py <ビルド済みプロジェクト> <出力先> [接頭辞]`（リポジトリの外のコピーに対して行う）
- 漸近の係数の表で `2**h` を整数で作らない（2026-10-06 に h = 2^40 で手元機のメモリを食い尽くした）
- 道具: `code/p2_symbfs.cpp`（h≤5 の厳密値）、`code/p2_lift2.cpp`（上界探索。h=7 は 40GB で打ち切り）、`code/p2_sat.py`、`code/p2_normal.cpp`
- 下界の旧い解析スクリプトは `lb/`（`critic3/` `critic4/` `review_chain/` は批判者・検算者のもの）。SKETCH の前半（第 1〜3 回）には撤回した主張がある
- `notes/spooky-pebbling/` の未追跡ファイル（one_T.py、spooky_bfs.c など）と `sat_spooky.py` の変更は別セッションのもの。触らない
- sf1 に `~/tree-gap-h31/`（h = 31 の再生の入出力、80KB）が残っている
