# さくらい（外部の AI 作業者）の spooky pebbling 監査・研究成果（2026-11-15 夜）の取り込み

取り込み: 2026-11-16（艦長2 の依頼）。元のファイルは **読むだけ**で、変更・移動していない。
元の zip・tar.gz・olean・ログはこのディレクトリに入れていない。sha256 と元のパスは `ARCHIVES.sha256` にある。

- 元の置き場: `<local>/paper-audits/spooky-*`, `overnight-save-20261115-2206/`, `overnight-drive-additions-20261115-2208/`,
  `<local>/dev/proj/showa-import/drive/さくらい/`（FLEET 系の完了版・独立再検査 R1・R2 査読・原稿の改訂）
- 対象の模型: **Lee–Lee–Jeong（LLJ, arXiv:2610.09434）§2.2–2.3 の並列 spooky pebbling**（二相のラウンド、
  active set の互いに素、空間は |P_before ∪ P_after-first-phase|、work = Pebble+Unpebble、ghost は work 0・深さ 1）。
  Lean では `SpookyRound.PaperRuns`（`lean/ConcreteRound.lean`）。**この模型と LLJ の本文の対応は人と AI の読み合わせだけ**
  （`reports/n7.*.md`, `reports/r2-independent-review.md`）で、Lean の定理ではない。
- Lean は **Std のみ（Mathlib なし）・Lean 4.35.0**。手元の `spooky-pebbling-lean`（Mathlib、別の定式化）とは独立の開発。

## 0. 結論（要約）

| | 中身 | 手元の再検査 |
|---|---|---|
| **新しい主張（本命）** | `Sandwich.sandwich`: H ≥ 16384、n = 2^H−1、s_H = ⌈6·2^H/H⌉、**W ≤ 3n** で、空 → 根だけ（ghost なし）の最小の深さ D は H⌊log₂H⌋/16 ≤ D ≤ 3H⌊log₂H⌋+2H。下界の一般形 `LogLower.paper_explicit_log_lower`（W ≤ 3n、Hs ≤ cn、H ≥ 2^{2(⌊log₂16c⌋+1)} ⇒ H⌊log₂H⌋ ≤ 2cd）と `Excess.paper_ratio`（W ≤ 3n+e） | **緑**（4.35.0 で 39 モジュールを source から再ビルド、定理 1111 本すべて標準 3 公理、変異 2/2 検出） |
| 新しい主張（有界） | `ExactFrontier.exact_frontier`: 7 頂点の完全二分木で (D,W,S) の Pareto 極小はちょうど (5,13,7),(7,14,6),(8,16,5),(9,15,5),(12,17,4)（深さは無制限で量化） | **緑・ただし native_decide 23 個に依存**（標準 3 公理の外）。変異 2/2 検出 |
| 既知の型の再発見 | W ≥ 3n − s − 1（最後の根の計算での切断）＝逐次の T ≥ 4n−2p−1 と仕事量の恒等式 R-Q35-05 から出る形の並列版。上界側（block/skeleton 構成、W ≤ (j+3)n−1・深さ O(H·log^{(j+1)}H)）は LLJ §3.4・Lemma 3.6/3.7 の技法（さくらい自身が「先行」と明記） | 構成の一部は Lean 緑（`SkeletonUnfill.height_upper`） |
| 未解決（C4 の線） | W ≤ 4n で D = Ω(H log log H) か、という予想（C4-Area）。証明の試みと、試みの障害の反例（局所）だけ | 反例・部品は緑。予想そのものは未証明 |
| 食い違い | **既存の結果との食い違いは見つからなかった**（§3） | |

## 1. 一覧（1 件 1 行）

rc は「最後の試行の rc（それ以前の失敗試行）」。−24 は CPU 上限の SIGXCPU で、**結果ではない**。
「再検査」は手元で source から再ビルドしたもの（§2）。✅ = rc0・標準 3 公理（propext, Classical.choice, Quot.sound）以内・sorryAx なし。
⚠native = rc0 だが native_decide の公理に依存。— = Lean なし。

### 1a. 有限の DP と 7 頂点の厳密な Pareto 前線（準備・有界）

| 件 | 主題 | 主張 | 証拠 | rc | 再検査 |
|---|---|---|---|---|---|
| dp | 抽象 DP | 有限の後続リストの DP と長さ d の実行の同値（`mem_dp_iff`） | Lean | A2:0（A1 は起動前失敗） | ✅ BoundedDP |
| round | 具体ラウンドの列挙 | LLJ の Legal を全列挙する後続関数と PaperRuns の同値（`dp_iff_paperRuns`） | Lean | A2–A4:0 | ✅ ConcreteRound |
| serialization | 並列→逐次の直列化 | 予算は増えないが、**ピークの等号は偽**（3 頂点で並列 2・除去先行の直列化 1）。終端だけで数える空間は不健全 | Python 有限全数（葉 1・2、鎖 3、二分木 3・5） | 0 | —（Lean なし） |
| pareto | n=3・7 の Pareto | n=3: (W,D,S)=(5,3,3)。n=7: 5 点（上）。5 本の手順は Lean の検査器で可行 | Python 全 2187 状態＋Lean 証人 | 最終 0（PY3/PY7/CERT7/LEAN3 が先に失敗） | ✅ pareto/Certificates（propext のみ） |
| pruning | 同一状態の支配による枝刈り・検査器の健全性 | `check_sound`・`same_state_prune_safe`。n=3 の最小深さ 3（`depth_min_three`） | Lean | SOUND6:0（1・3・5 失敗、3 はカーネル decide が 1GiB 超過） | ⚠native（`depth_min_three`・`no_goal_lt_three` だけ native_decide） |
| closure | 閉じた前線の証明書 | 表の上で 5 点が全深さの下界（`five_point_lower`） | Lean（汎用部は標準、具体表は native_decide 3） | NATIVE7B:0 | ⚠native（NativeCertificate。3.5MB のため本ディレクトリには入れていない） |
| edgebridge | Legal → 辺表の橋 | 0..271 の状態は検査済み、残りの 256 状態の束は CPU 30 秒で打ち切り | Lean | SHARD1–8:−24（打ち切り）、TRANSFER:0 | Transfer ⚠native。Shard1–8 は再ビルドしていない（手元でも Shard1 は 120 秒で打ち切り） |
| edgefast（exact-frontier） | **7 頂点の厳密な前線** | `exact_frontier`（上の 5 点、深さ無制限）。辺の正規化を速くした 15 の束で全 2187 状態 | Lean＋native_decide 23 | EXACT2:0、COMPLETE4:0（以前に 4 回失敗） | ⚠native ✅rc0（公理 23 個を手元で数え一致） |
| n7 監査 | 模型と LLJ 本文の対応 | §2.1–2.3 と Lean の定義を 1 項ずつ照合し、意味を変える不一致なし | 人／AI の読み合わせ（再コンパイルなし） | — | — |

### 1b. W ≤ 3n の深さの下界（C3 の線）

| 件 | 主題 | 主張 | 証拠 | rc | 再検査 |
|---|---|---|---|---|---|
| potential | 位相関数の橋 | 局所の不等式 ⇒ 全実行で φ(start) ≤ aW + bD + φ(end) | Lean（一般 n） | P2:0（P1 失敗） | ✅ |
| cleanfringe | 清掃つきの縁の構成 | W = 4km−3 < 4n、D・S の式。n=15 の 3 本の証人 | 紙＋Lean（代数・証人）＋Python 494 例 | CERT15:0（CERT1 は 31 頂点でメモリ 1GiB 超過） | ✅（**31 頂点の `AttemptWith31` も手元の 2GiB では rc0・標準公理**。さくらいは未完扱い） |
| reverse | ラウンドの逆転 | ghost なしのラウンドは pebble/unpebble の入れ替えで合法に戻る（`reverse_step`）。新規性の訂正: 縁の構成は LLJ の Resolve の切り詰めに吸収される | Lean＋紙 | R4:0（R1 失敗） | ✅ |
| fixedc | 仕事量の係数 | W ≤ (j+3)n − 1、D = O(H·log^{(j+1)}H)（LLJ の構成から）。よって「W ≤ 4n ⇒ D = Ω(H log H)」は偽（LLJ の保証を前提に） | 紙＋Lean（抽象の漸化式）＋Python 247 例 | 0 | ✅ FixedWork（抽象のみ） |
| cutbound | 切断による work 下界 | W ≥ 3n − p − 1 ≥ 3n − s − 1（紙）。C3 の深さの下界の証明の下書き | 紙＋Lean 部品（CutBound, Intervals）＋Python 49 例 | B1:0, INTERVAL2:0（INTERVAL1 失敗） | ✅ |
| tracebridge | 実行 → スカラーの跡 | 親の計算は子の計算と子の除去で挟まれる（`parent_bracketed`） | Lean（一般 n） | T7:0（T2,T3,T5 失敗） | ✅ |
| rootcut | 最後の根の計算での切断 | `last_root_cut`・例外の課金 | Lean | R4:0（R1,R3 失敗） | ✅ |
| descendants | 子孫への清掃の伝搬 | `descendant_cleanup` | Lean | D4:0（D1,D3 失敗） | ✅ |
| heappath | ヒープの道 | 根から全頂点への道、清掃の伝搬 | Lean | H3:0（H1 失敗） | ✅ |
| workbridge | 仕事量の厳密な分解 | 実行の work = 頂点ごとの計数の和、共通の切断 | Lean | W3:0（W1 失敗） | ✅ |
| precut | 切断前の計算 | 切断前に全頂点が計算される | Lean | C3:0（C1 失敗） | ✅ |
| exceptions | 例外の数 | W ≤ 3n+e ⇒ B ≤ e+2s+1（切断の仮定つき） | Lean | E5:0（E1,E3,E4 失敗） | ✅ |
| cutspace | 仮定なしの例外の数 | PaperRuns から直接 B ≤ e+2s+1（`paper_exception_bound`） | Lean | S2:0（S1 失敗） | ✅ |
| area | 占有の面積 | boundary ≤ volume ≤ d·s（`paper_area_cap`） | Lean | A3:0（A1 失敗） | ✅ |
| goodinterval | 良い頂点の区間 | 計算 1 回・除去 1 回の頂点の実際の区間 | Lean | G4:0（G3 失敗） | ✅ |
| nesting | 入れ子 | c(子) < c(親) < u(親) < u(子)、区間の和 ≤ 実行長·s | Lean | N5:0（N1 失敗） | ✅ |
| forest | 二分森 | 成分数 K ≤ 2B+1、段ごとの数 ≤ K·2^k | Lean | F4:0（F1,F3 失敗） | ✅ |
| heapforest | ヒープのラベル | 良い頂点の述語と森の接続（全高さの被覆は仮定） | Lean | H3:0（H1 失敗） | ✅ |
| coverage | 全高さの被覆 | 被覆の仮定を外す、K ≤ 2e+4s+3 | Lean | V2:0 | ✅ |
| deptharea | 浅い頂点の数・深さの幅 | 幅 ≥ 2·深さ+1 | Lean | D3:0 | ✅ |
| sumarea | **有限の下界** | `paper_finite_lower`: (2ℓ+1)(n−(e+2s+1)−(2e+4s+3)(2^ℓ−1)) ≤ d·s | Lean | S3:0（S1 失敗） | ✅ |
| loglower | **H log H の下界** | `paper_explicit_log_lower`（§0） | Lean | L3:0（L1,L2 失敗） | ✅ |
| excess | W ≤ 3n+e への一般化 | 8(s+e+1) ≤ n ⇒ n(2⌊log₂⌊n/8(s+e+1)⌋⌋+1) ≤ 2ds | Lean | E3:0（E2 失敗） | ✅ |

### 1c. W ≤ 3n の上界の構成（LLJ の技法の形式化）

| 件 | 主張（すべて実際の PaperRuns） | rc | 再検査 |
|---|---|---|---|
| batchupper | 計算と ghost の一括ラウンド、ヒープの層の独立性 | B3:0（B1 失敗） | ✅ |
| fillupper | 高さ H の全格納の埋めと清掃（D=2H, W=2n） | F5:0（F1,F2,F4 失敗） | ✅ |
| frameupper | 根を保持したままの実行（空間 +1） | R4:0（R1,R3 失敗） | ✅ |
| fringeembed | 部分木の局所実行を全体へ埋め込む | E7:0（E3,E5 失敗） | ✅ |
| liftcost | 埋め込みの work・空間の厳密な移送 | C3:0（C1 失敗） | ✅ |
| parallelmerge | 干渉しない 2 ラウンドの同時実行 | M5:0（M1,M2,M4 失敗） | ✅ |
| synctrace | 2 つの縁の同期した跡 | T4:0（T2 失敗） | ✅ |
| familysync | K 個の縁（RoundProduct は仮定） | K4:0（K1,K2 失敗） | ✅ |
| familyround | K 個の縁の復号と同時ラウンドの合法性 | F13:0（10 回失敗） | ✅ |
| familycost | K 個の縁の同期した跡（仮定なし） | C6:0（C1–C3,C5 失敗） | ✅ |
| batchedcleanup | 縁の一括清掃 | B4:0（B2,B3 失敗） | ✅ |
| retainroot | 根を残す縁の準備 | R8:0（4 回失敗） | ✅ |
| initialghost | 縁の初期準備（W=m） | I6:0（I1,I5 失敗） | ✅ |
| fullpartition | 全頂点の縁への分割と境界 | P6:0（P1,P5 失敗） | ✅ |
| retainbatches | 根を残す一括準備（W ≤ 3n には不十分と自己申告） | B4:0（B1,B3 失敗） | ✅ |
| rootcleanup | 根を含む縁の清掃 | C7:0（C1,C3,C5 失敗） | ✅ |
| skeleton | 境界 → 骨格 → 根 | S6:0（S1,S3,S5 失敗） | ✅ |
| skeletonunfill | **`height_upper`**: すべての H ≥ 2 で W ≤ 3n、D ≤ 3H⌊log₂H⌋+2H、H·S ≤ 6·2^H | U6:0（U1,U3,U5 失敗） | ✅ |
| sandwich | **`sandwich`**（§0）。s_H ≤ n ⇔ H ≥ 7（`budget_range_iff`） | S1,S2:0 | ✅（変異 2/2） |
| repro | 39 モジュールを source だけから組み直す手順（olean を使わない） | — | 手元で同じ 39 本を別に組み直して一致（§2） |
| independent-s2 R1 | 別の作業者が Sandwich.lean だけを再コンパイル（依存の olean は流用） | 0 | — |
| r2 査読 | 定理と数値に不整合なし。KSS・KMRV・Quist–Laarman・LLJ の一次文献で同種の下界の含有なし（LLJ Eq.38 は Ω(H(log* n)²) どまり） | — | — |
| draftreview / draftrevision / texaudit / cleanuptext | 原稿「A Fixed-Work Depth Bound for Parallel Spooky Pebbling of Complete Binary Trees」の下書きと改訂（著者・投稿先は未定）。最新は `draft/paper-draft-C2-cleanuptext.tex` | texaudit compile6:0 | 原稿の再ビルドはしていない |

### 1d. W ≤ 4n（C4）の線: 未解決。部品と「証明の試みの障害」の反例

| 件 | 主張 | 証拠 | rc | 再検査 |
|---|---|---|---|---|
| fourbarrier | C3 の有限の下界は e = n（W ≤ 4n）で空になる。2 回計算する頂点では連続した占有が崩れる | Lean（局所） | F2:0（F1 失敗） | ✅ |
| epochcharge | 2 つの親の参照の間で C = G + U。同じ区間を 2 度数えると二重課金になる反例 | Lean | P3:0（P1 失敗） | ✅ |
| ghostbudget | 切断後の ghost の数 ≤ e+s+1（`paper_ghost_budget`） | Lean | G5:0（G1,G4 失敗） | ✅ |
| refpartition / refsum / refglobal | 参照による実行の分割と、課金が二重にならないこと | Lean | R6:0 / S4:0 / V3:0（それぞれ失敗あり） | ✅ |
| refarea | 「両端で参照されれば間は占有が続く」は**偽**（2 頂点の反例）。※ `reference_area` は暗黙の引数が固定の定数に当たっていて主張が狭かった（refselect で訂正） | Lean | A2:0（A1 失敗） | ✅ |
| refselect | 再計算 0 の区間の選択（`kept_gap_live`、b は全称と確認） | Lean | K3:0（K1,K2 失敗） | ✅ |
| gaplength | 再計算の回数から隙間の長さは抑えられない（局所の反例） | Lean | L4:0（L1,L2 失敗） | ✅ |
| lastlive | 最後の計算から参照までの区間は占有が続く | Lean | T2:0 | ✅ |
| treesuffix | 3 頂点の完全二分木で、木の依存と清掃終了だけでは各辺の正の長さは強制されない（反例） | Lean | Z1:0 | ✅ |
| c4areatarget | 予想 C4-Area: W ≤ 4n、8s·2^{2^ℓ} ≤ n ⇒ 8A ≥ n(ℓ+1)（定数 8 は試し値） | 紙（予想）・Python | Q1:0 | — |
| c4samples | H=10,12,16 の遅い手順で予想の前提が真の場合に違反なし（証拠ではないと明記） | Python | B1:0 | — |
| c4chargefailure | C3 の議論が C4 で破れる場所は「質量の評価」（3n+B ≤ W+2p+1）。帳簿だけでは良い頂点 0 もありうる（`no_good_mass`）。H=16 の実際の手順で約 94% が (1,2,1,0,0) 型 | Lean＋Python | F2:0（F1 失敗） | ✅ |
| spacepath | 右端の道の接尾はすべて長さ 0（H 3 例）。道に沿った議論では足りない | Python | P3:0（P1,P2 失敗） | — |
| epochreuse | エポックの接続の予想（係数 2）。「子のエポックの再利用には子の再計算が要る」は偽（7 頂点の反例） | Lean（反例と重なりの補題） | E2:0 | ✅ |
| epochincidence | ランダム 200 例で予想を満たす。保存済みの大きい手順の監査は**メモリ 6.7GB で SIGXCPU**（結果なし） | Python | RANDOM:0、AUDIT:−24 | — |
| epochstatic / incidenceguard / oslimitcheck L1・F2 | 証明の計画（Lean なし）と、資源上限の仕組みの確認（研究の計算ではない） | 静的・運用 | G1 は AUDIT −24 を再確認 | — |
| fleetepoch F1 | 順序のついたエポックの共有は高々 1（`overlap_card_le_one` 他） | Lean | F1:0 | ✅ EpochOverlap |
| fleetprefix P2 | 参照時のエポック番号は正、単調 | Lean | P2:0（P1 失敗） | ✅ EpochPrefix |
| fleetcontinuity R2 | 同じ番号の区間は除去を含まない（`removal_forces_new_id` 他） | Lean | R2:0（C1・D1 失敗） | ✅ ContinuityCombined（R2 版） |
| fleetorigin O1 | 最後の計算の位置は一意 | Lean | O1:0 | ✅ OriginCombined |
| fleetorder S2 | 親のエポックの順序と子のラベルの単調性、共有の一意性 | Lean | T1,S2:0 | ✅ OrderT1, OrderCombined |
| fleetenum E4 | 参照集合の構成的な列挙と `Member` の同値、共有 ≤ 1 | Lean | E4:0（E1–E3 失敗） | ✅ EnumCombined |
| fleetincidence I2 | 接続行列の行・列の和の一致（参照集合に具体化） | Lean | I2:0（I1 失敗） | ✅ IncidenceCombined |
| **fleetnozero** | — | 2026-11-16 08:04 時点で START/STOP/rc が揃っていない | — | **進行中として取り込まず** |

## 2. 手元の再検査（2026-11-16、<host>）

- 方法: zip から展開した source（同名の .lean は全 zip で同一。例外は `Certificates.lean` の 2 版（pareto 版は `lean/pareto/`）と、FLEET の `ContinuityCombined.lean`（失敗した C1 版と成功した R2 版。R2 版を採用））を
  依存順に 1 本ずつ `systemd-run --user --wait --pipe -p MemoryMax=2G -p RuntimeMaxSec=120 -p Nice=19 lean -j1 -o X.olean X.lean`。
  **さくらいの olean は使っていない**。スクリプトは `recheck/build.py`・`recheck/axcheck.py`。
- **Lean 4.35.0（さくらいと同じ版・同じコミット系列）**: 105 本中 **97 本 rc0・olean 生成**。残る 8 本は edgebridge の `Shard1..8`
  （さくらい側でも CPU 打ち切り。手元でも Shard1 が 120 秒で打ち切り → 残りは実行しなかった。exact_frontier はこれらを使わない）。
  pareto 版 Certificates も rc0。repro の 39 本の source は手元の source とバイト一致。
- 公理: 葉のモジュール 27 本ごとに、閉包内の**全定理**の公理を `collectAxioms` で数えた（`recheck/axioms-4.35.0.txt`）。
  標準 3 公理の外にあるのは native_decide 由来だけ（ExactFrontier 閉包 30 定理、Transfer 9、NativeCertificate 6、FullBridge 7、Pruning 3）。
  **sorryAx は 0**。Sandwich の閉包は 39 モジュール・定理 1111 本、すべて標準 3 公理以内。
- 変異（`recheck/mutations.txt`）: Sandwich.lower の仮定を W ≤ 4n に → rc1（型の不一致）、結論の 16 を 15 に → rc1。
  ExactFrontier の点 (12,17,4) を (12,16,4) に → rc1、点 (9,15,5) を削る → rc1。無変更の写しは rc0（対照）。
- **Lean 4.31.0**（依頼の既定の版）: `recheck/build-4.31.0.json`。rc0 は 49 本（ExactFrontier・Pruning・Certificates を含む）。
  エラー 4 本: `Exceptions.lean`（88 行の `rw` の引数が解決しない）と `EnumCombined`・`IncidenceCombined`・`EpochOverlap`
  （`List.Pairwise.length_le_of_subset` が 4.31.0 の標準ライブラリに無い）。Exceptions の下流 44 本（Sandwich・LogLower・SumArea を含む）は
  4.31.0 では組めない。**標準ライブラリの版の違いであって主張の偽を意味しない**。さくらいと同じ 4.35.0 の結果を正とする。
- Mathlib は使っていないので「未再検査」は無い。巨大な表を持つ `FullBridge.lean`・`NativeCertificate.lean`（各 3.5MB）は
  取り込んでいない（sha256 は ARCHIVES.sha256。手元では組んで rc0）。`BridgeBase.lean`（3.5MB）は exact_frontier に要るので入れた。

## 3. 既存の結果との突き合わせ

- **食い違いは無し。**
- 7 頂点の前線を深さ–空間に射影すると s = 4,5,6,7 で最小の深さ 12, 8, 7, 5。手元の SAT と BFS の値
  D⋆(B_3,s) = 12, 8, 7, 5（`tree-gap/PARALLEL_DEPTH_2026-11.md` 118 行）と**一致**。
- R-Q35-26（D⋆ ≤ 2h ⇔ s ≥ 3·2^{h−2}+1）の h = 3 は s ≥ 7。前線（s=6 で深さ 7、s=7 で深さ 5）と一致。
  R-Q35-21 の閾値 7·2^{h−3}+1 は h ≥ 4 に限った主張で、h = 3 では 7 で足りる（手元の注記「h = 3 は 7」と一致）。
- 空間 4 の最小仕事量 17 は、手元の逐次の値（`DAG_CONSTANT_2026-11.md` 38 行の B_3・空間 4 の最小仕事量 17）と同じ。
- 紙の下界 W ≥ 3n − s − 1 は 7 頂点の前線で s = 5,6,7 のとき等号（15, 14, 13）、s = 4 で 16 < 17。矛盾なし。
  逐次では T ≥ 4n − 2p − 1 と R-Q35-05 の W* = (T*+1)/2 + n − 1 から W ≥ 3n − p − 1 がすぐ出る（**並列版は既知の型の再発見**）。
- spooky-pebbling-lean の Envelope.lean・Slope6Exact.lean は鎖（Q7）の逐次の結果で、木の並列の深さとは対象が重ならない。
- LLJ の Eq.(38) の L について、さくらいの初期の報告は λ(n) と書き、R2 査読は L = 1 + log* n と読んでいる。
  台帳 R-Q35-21 (D) の「LLJ の log* の下界」と同じ読みは後者。

## 4. 層の判断の材料（台帳は触っていない）

- Sandwich（W ≤ 3n、s = s_H、H ≥ 16384）: Lean 緑（手元で再ビルド・標準公理・変異検出）＝層 1 の条件は満たす。
  ただし (i) 模型と LLJ 本文の対応は読み合わせ、(ii) 新規性は R2 査読の範囲（KSS・KMRV・QL・LLJ）だけ、(iii) 定数・閾値は最適化していない。
- 7 頂点の前線: native_decide に依存し、有界事例 ⇒ 層 2。
- C4: 未解決の問題として扱う。
