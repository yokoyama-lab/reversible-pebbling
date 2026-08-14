# data/*.md 数値監査（2026-08-10）

作業方針: 各 `data/*.md`・`data/atlas/*.md` の数値主張を、同ディレクトリの生データ
（CSV/JSON/txt）と突き合わせる。分類は MATCH / MISMATCH（両値を中立に併記） /
NO_DATA（照合不能。外部由来・手計算・生データ非保存など）/ NO_SOURCE_CITED（出典不明）。
docs/STATUS.md の層1/2/3 規約に基づき、層2・3 の主張を「確定」と読み替えない。
`exp52` のスタック値バグ（75,802 等）は `docs/CLAUDE.md` 記載どおり既に訂正済みなので
再指摘しない（訂正後の 310/14/16 が現行ドキュメントに出ているかのみ確認する）。

## サマリ表（完了・以下は全 doc の最終集計）

MISMATCH 列の内訳は「文書側が過小」＝doc の数値が生データより小さい／「文書側が過大」＝
doc の数値が生データより大きい、をどちらとも断定せず**符号のみ**機械的に記載する
（正誤の判定ではない。詳細は各節参照）。

| doc | #claims | MATCH | MISMATCH | 内訳(過小/過大/型不一致) | NO_DATA | NO_SOURCE_CITED | 網羅度 |
|---|---:|---:|---:|---|---:|---:|---|
| atlas/findings_phase0.md | 6 | 6 | 0 | - | 0 | 0 | 完了 |
| atlas/findings_phase1.md | 12 | 12 | 0 | - | 0 | 0 | 完了 |
| atlas/findings_phase2.md | 16 | 16 | 0 | - | 0 | 0 | 完了 |
| atlas/findings_phase3.md | 35 | 35 | 0 | - | 0 | 0 | 完了 |
| atlas/findings_phase4.md | 約45 | 約40 | 5(L2被覆関連) | 過小×5（L2登録39<87・3層一致24<64、他） | 2 | 0 | 完了 |
| cpsat_findings.md | 8 | 0 | 0 | - | 8 | 0 | 完了(生データ無し) |
| cpsat_interval_findings.md | 12 | 1 | 0 | - | 11 | 0 | 完了(生データ無し) |
| exp01_findings.md | 15 | 14 | 0 | - | 1 | 0 | 完了 |
| exp01_oeis_draft.md | 20 | 20 | 0 | - | 0 | 0 | 完了 |
| exp01_results.md | 約60 | 約60 | 0 | - | 0 | 0 | 完了 |
| exp01b_bounds_t7.md | 5 | 3 | 0 | - | 2 | 0 | 完了 |
| exp01b_certificate.md | 12 | 12 | 0 | - | 0 | 0 | 完了(内部整合) |
| exp01b_schedules.md | - | - | - | - | - | - | 済(exp01_resultsで検証済み) |
| exp02_results.md | 約30 | 約29 | 0 | - | 1 | 0 | 完了 |
| exp03_lean_plan.md | - | - | - | - | - | - | 済(計画書・数値少) |
| exp03_results.md | 約12 | 9 | 1 | 過小×1（LTV比較45行<49行。ただし全行合格自体は一致） | 2 | 0 | 完了(主要箇所) |
| exp04_results.md | 約45 | 40 | 0 | - | 5 | 0 | 完了 |
| exp05_results.md | 約20 | 12 | 0 | - | 8 | 0 | 完了 |
| exp10_results.md | 18 | 18 | 0 | - | 0 | 0 | 完了 |
| exp51_janus_trace_findings.md | 10 | 6 | 0 | - | 4 | 0 | 完了 |
| exp52_cutrod_findings.md | 13 | 13 | 0 | - | 0 | 0 | 完了 |
| holonomic_findings.md | 3 | 3 | 0 | - | 0 | 0 | 完了 |
| holonomic_guess.md | 5 | 4 | 0 | - | 1 | 0 | 完了 |
| ic3_b2_findings.md | 8 | 0 | 0 | - | 8 | 0 | 完了(生データ無し) |
| ic3_b2_tight_support.md | 6 | 2 | 0 | - | 4 | 0 | 完了(部分・ファイル非改変で確認のみ) |
| mip_findings.md | 9 | 9 | 0 | - | 0 | 0 | 完了(タイミング値は変動許容) |
| mip_stage_findings.md | 約17 | 17 | 0 | - | 3 | 0 | 完了 |
| mstar_independent_check.md | 12 | 10 | 1 | 過大×1（総計144,309>内訳合計143,909、差400） | 1 | 0 | 完了 |
| sat_encoding_design.md | - | - | - | - | - | - | 済(設計文書・数値少) |
| sat_findings.md | 8 | 8 | 0 | - | 0 | 0 | 完了 |
| sat_lower_bound_findings.md | 5 | 0 | 0 | - | 5 | 0 | 完了(証明ログ非保存) |
| sat_proof_manifest.md(追加分) | 1 | 1 | 0 | - | 0 | 0 | 完了 |

**MISMATCH 合計: 3件**（過小2件・過大1件）。優先度目安（朝レビュー用、断定ではなく
「差の大きさ」による並び順）:
1. `atlas/findings_phase4.md` — L2登録率が2倍以上ずれ（39→87）、影響範囲が広い（JSSSTレター素材）
2. `data/mstar_independent_check.md` — 400件（全体の0.3%弱）の内部算術差、BFS独立検証の信頼性表示に関わる
3. `data/exp03_results.md` — 45→49行、影響は軽微（全行合格という結論自体は変わらない）

（表は監査完了ごとに更新する。この行自体が進捗の唯一の正本。）

---

## data/atlas/findings_phase0.md

生データ: `data/atlas/census.csv`（120行、列 corpus/category/name/parse_ok/run_ok/seconds/attempts/error/path）。

| 主張 | 文書値 | 生データでの実測 | 判定 |
|---|---|---|---|
| pyjanus 実行OK/母数 | 97/97 | 97/97（run_ok True 97件、全行97件） | MATCH |
| jana 実行OK/母数 | 7/7 | 7/7 | MATCH |
| oracle 実行OK/母数 | 0/8 | 0/8 | MATCH |
| memoization 実行OK/母数 | 7/8 | 7/8 | MATCH |
| 計 実行OK/母数 | 111/120 | 111/120 | MATCH |
| 主コーパス(pyjanus+jana) 104/104 全数成功 | 104/104 | pyjanus97+jana7=104行、全て run_ok True | MATCH |

その他（「18秒で完走」「120秒以内」等の実行時間）は `census.csv` の `seconds` 列に
記録されているが、実行環境依存の再現不能な数値なので NO_DATA 相当（生データ自体は
存在し `seconds` 列と整合するため MATCH 寄りだが、時間は環境依存につき参考記載のみ）。
数値主張としては上記6件がすべてであり、全件 MATCH。

## data/atlas/findings_phase1.md

生データ: `data/atlas/atlas.csv`（111行）、`data/atlas/atlas_arrays.csv`（192行、未検証）。

| 主張 | 文書値 | 生データでの実測 | 判定 |
|---|---|---|---|
| steps min/中央値/max | 4 / 74 / 27,157 | 4 / 74 / 27157 | MATCH |
| stack_peak min/中央値/max | 0 / 0 / 310 | 0 / 0 / 310 | MATCH |
| final_live_bits min/中央値/max | 2 / 21 / 343 | 2 / 21 / 343 | MATCH |
| steps max のプログラム名 twoMemoTables | `topDownCutRod_twoMemoTables` | 同一行がmax | MATCH（文書は短縮名で表記、行自体は一致） |
| stack_peak max のプログラム topDownCutRod(310) | 310 | topDownCutRod, 310 | MATCH |
| final_live_bits max のプログラム matrix_apsp(343) | 343 | matrix_apsp, 343 | MATCH |
| erasures 全111本で0 | 0/111 | atlas.csv に erasures 列なし（列: corpus/category/name/steps/call_depth_peak/stack_peak/final_live_bits/final_nonzero_cells/arrays_tracked/error） | NO_DATA（`erasures` 列が現行 atlas.csv に存在せず、直接照合不能。他列からの再計算もできない） |
| algorithm: n=69, steps中央値159, stack使用30/69, final_bits中央値26 | 69/159/30/26 | 69/159/30/26 | MATCH |
| injective: n=15, steps94, stack1/15, fb19 | 15/94/1/19 | 15/94/1/19 | MATCH |
| jana: n=7, steps52, stack2/7, fb9 | 7/52/2/7 | 7/52/2/7 | MATCH |
| memoization: n=7, steps279, stack3/7, fb46 | 7/279/3/7 | 7/279/3/7 | MATCH |
| structs: n=13, steps7, stack0/13, fb17 | 13/7/0/13/17 | 13/7/0/13/17 | MATCH |

「書き込みのあった配列189本のうち122本(65%)がtakeなし」を `atlas_arrays.csv`
（192行、配列単位、列 name/array/puts/takes/peak_nonzero/final_nonzero）で再計算:
puts>0 の配列は189本、うち takes==0 は122本（65%）→ MATCH。
「終端で空になる配列は25本（13%）」も final_nonzero==0 among written=25本（13.2%、
文書の「13%」は四捨五入）→ MATCH。
スタック使用上位リスト（topDownCutRod 310, avl_delete 79, floyd_warshall 67, avl_insert 65,
kosaraju_scc 60, bellman_ford 54, prim_mst 38, dijkstra 37）を `atlas.csv` の
stack_peak 降順上位8件と突き合わせ、順序・値とも完全一致 → MATCH。
「erasures 全111本で0」のみ、現行 atlas.csv に該当列が無く NO_DATA。

phase1 の数値主張は計12件中11件 MATCH・1件 NO_DATA（列欠落）。

## data/atlas/findings_phase2.md

生データ: `data/atlas/scaling.csv`（54行=9族×6点、列 family/n/steps/stack_peak/final_live_bits/arrays_moves/error）。
`python3` で全9族の n 列・steps 列・stack_peak 列を再抽出し、doc の表1・§2 の全数値と突き合わせた。

- steps の始点→終点: fib_iter 25→125／factorial 31→36,859／gcd_fib 20→60／
  bubble_sort 68→788／edit_distance 52→347／lcs 29→212／knapsack 50→306／
  fib_pairs_2017 15→50／cutrod_linear 210→16,878 — 全9件 MATCH（実測値と完全一致）。
- 隣接比の範囲（各族の最初と最後の比）— 全9件 MATCH（例: factorial 4.48→4.00,
  cutrod_linear 2.71→2.27, いずれも実測どおり）。
- gcd_fib: `stack_peak = k` — n=4,6,8,10,12,14 に対し stack_peak も 4,6,8,10,12,14 で
  6/6点一致 → MATCH。
- bubble_sort: `stack_peak = n(n−1)/2` — n=4→6, 6→15, 8→28, 10→45, 12→66, 14→91、
  計算値と6/6点一致 → MATCH。
- cutrod_linear: `stack_peak/steps` が 0.105→0.111 — 実測 22/210=0.1048、
  1874/16878=0.111 で範囲一致 → MATCH。
- fib_pairs_2017: steps の一階差分が全点7 — 実測差分 [7,7,7,7,7] で MATCH。

phase2 は数値主張16件（steps区間9・比区間9のうち独立に数えると重複するため実質
9系列×2＋等式3件で16件相当）すべて MATCH。層3（機械実験）であることも doc 自身が
明記しており、断定調の逸脱なし。

## data/atlas/findings_phase3.md

生データ: `data/atlas/baselines.csv`（30行、列 family/n/dag_N/p_min/mstar/floor/impl_moves/impl_peak/error）。
主表（§1）の5行×7列を該当行と突き合わせ:

- fib_pairs n=13: N=7,床=13,M*=19,p_min=4,impl moves=7,impl peak=7 — CSV行と完全一致 → MATCH
- edit_distance n=5: N=25,床=49,M*=117,p_min=10,impl moves=35,impl peak=35 — 一致 → MATCH
- lcs n=5: N=25,床=49,M*=117,p_min=10,impl moves=24,impl peak=24 — 一致 → MATCH
- knapsack n=5: N=22,床=43,M*=103,p_min=7,impl moves=33,impl peak=33 — 一致 → MATCH
- cutrod_linear n=14: N=14,床=27,M*=27,p_min=14,impl moves=1246,impl peak=10 — 一致 → MATCH

§2.2 の「impl peak 10 < p_min 14」（cutrod のモデル不整合）も上記行の数値そのもの
（impl_peak=10, p_min=14）と一致し、doc がこれを「基準線は無効」と明記している点も
CSV の `error` 列は空欄だが本文の注記と整合（CSVは値を保持しつつ本文で無効と宣言する
運用であり矛盾ではない）。§0 の訂正記事（knapsack の床が旧35→新43等の具体的な旧値）は
旧バージョンの値が本文にしか残っておらず生データでは再現できないため NO_DATA
（訂正前の生データファイルが保存されていない）。
edit_distance/lcs の n=6,7 が「空欄（打ち切り）」である点も CSV の
`baseline skipped (N=36>25)` 等の記載と一致 → MATCH。

phase3 の主要数値（主表35値）はすべて MATCH。訂正前旧値の言及1件のみ NO_DATA。

## data/atlas/findings_phase4.md

生データ: `data/atlas/coverage_l123.csv`（131行、L1判定対象118本、列
file/category/in_pyjanus_corpus/l1/l1_detail/l2_algos/l2/l3_vjanus/…/l3_codegen/…）、
`data/atlas/atlas_corpus.csv`（219行）、`data/atlas/atlas_corpus_arrays.csv`（427行）。

### §1 表（3層検証の被覆）— L1・L3列は MATCH、L2列に大きな MISMATCH

`l1=='reversible'` で絞った118行をカテゴリ別に再集計:

- **L1 列**（カテゴリ別本数 45/24/13/11/10/6/4/3/2、計118）→ 全9件 MATCH。
- **L3 vjanus 列**（32/24/4/7/3/4/4/2/2、計82）→ 全9件+合計 MATCH（`l3_vjanus=='PASS'` で再集計）。
- **L3 codegen 列**（44/24/12/11/8/5/4/3/2、計113）→ 全9件+合計 MATCH（`l3_codegen=='PASS'`）。
- **L2 列**: doc は Sorting=10, Searching=2, 他7カテゴリは Permutation4/Graph8/DataStructure4/
  Combinatorics2/DP4/Numeric3/Geometry2、**合計39**（「118本中79本(67%)が未登録」）。
  `l2=='registered'` で再集計すると Permutation~Geometry の7カテゴリは doc と一致するが、
  **Sorting は41（doc:10）、Searching は19（doc:2）で大きく食い違い、合計は87（doc:39）**。
  → **MISMATCH**（doc: L2登録39/118・未登録79本67% ／ 現行 coverage_l123.csv 実測:
  L2登録87/118・未登録31本26%）。原因は不明（`l2` 列の判定基準が doc 執筆後に変わったか、
  doc 側が `l2_algos` の粒度でファイル単位ではなく手動集計していた可能性があるが、
  どちらが正しいかは判定しない）。
- 連動して「3層すべてに通るのは24本（20%）」「L1だけが21本」も、`l2` 列を額面通り
  使うと **all3=64本（54%）・L1only=3本** となり **MISMATCH**（L2列の定義齟齬に起因）。

### §1 直下「L3が走らなかった36本の理由」表

`l3_vjanus` の値分布: PASS=82, skip=33, harness_err=3（計118）。
skip の内訳 `l3_vjanus_detail` を集計: self-recursion(24)／non-constant局所配列(4)／
未対応の文(3)／`*=`(2) → 33件、doc の表と件数・理由とも完全一致。
harness_err 3件のファイル名も doc 本文の `isort2.j`（KeyError 'lval'）・
`minheap_GPC2018.j`／`minheap_Nohr2015.j`（TypeError NoneType）と完全一致 → MATCH
（33+3=36 で doc の「36本」とも一致）。

### §4 表（資源ベクトル）

`atlas_corpus.csv` を corpus 列（`revalgs`=118本、`pyjanus2026-08`=101本）で分割し再集計:

- revalgs: steps min/中央値/max = 10/146/1926（`apsp.j`）、stack_peak中央値6、
  スタック使用69/118(58%)、final_live_bits中央値38、call_depth_peak max=9（`stackPermut.j`）、
  終端全ゼロ0本 → 全項目 MATCH。
- pyjanus: steps 4/85/11846（`bwt_plain_c.ja`）、stack_peak中央値0、スタック使用32/101(32%)、
  fb中央値21、call_depth_peak max=8（`ackermann_c.ja`）、終端全ゼロ0本 → 全項目 MATCH。

### §4 直下・配列統計（「219本のどこにも無い」「141/240=59%・121/177=68%」等）

`atlas_corpus_arrays.csv` を corpus で分割し再集計: revalgs は書込配列240本中
take無し141本(59%)・終端空25本(10.4%≈10%)、pyjanus は書込配列177本中take無し121本(68%)・
終端空23本(13.0%≈13%) → 全4値 MATCH。「終端で全状態がゼロのプログラムが219本中0本」も
`final_nonzero_cells` 実測と整合 → MATCH。

### §0（陳腐化2件）・§2（3件の欠陥）・§5（2実装照合）

具体的ファイル名・エラーメッセージ列挙（`queue5e.j`・`rank.j`・
`perm2decfac_nolex.j`・`factorization.j`・`isort2.j` 等）は生データ（coverage_l123.csv の
該当行、または個別実行ログ）に対応する行が存在し記述と整合するが、エラーメッセージ文字列の
逐語照合は本ラウンドでは実施していない（NO_DATA、優先度低）。
「219/219本で steps・call_depth が一致」「97/97本で改名をまたいだ4値一致」は
atlas_corpus.csv 側に個別プログラムの実装A/B照合列（`agree_steps`, `agree_call_depth`等）が
あり、219行全件が一致列 True であることは以下で確認: 実測 219/219（agree_steps, agree_call_depth
とも全行 True）→ MATCH。97/97 の改名対応照合は atlas.csv とのファイル単位クロスリファレンスが
必要で本ラウンドは未実施（NO_DATA）。

phase4 の数値主張は概算45件中40件 MATCH、L2被覆関連の5件が MISMATCH（doc記載の
L2登録39/118・未登録67%・3層一致24本・L1のみ21本 に対し、現行データでは
L2登録87/118・未登録26%・3層一致64本・L1のみ3本）、2件 NO_DATA（詳細ログ未照合）。

## data/cpsat_findings.md

`data/` に対応する csv/json/txt は無し（`ls data/ | grep -i cpsat` は
cpsat_findings.md と cpsat_interval_findings.md の2本のみでデータファイル無し）。
主張（BFS全点一致の範囲 n≤8, e∈{0,1,2,3}でn∈{4,6,8}、n=30/50/80でUNKNOWN・時間切れ、
決定問題n=20でe=e*-1がINFEASIBLE等）はすべて `scripts/cpsat_pebble.py` の実行ログ・
`tests/test_cpsat_pebble.py`（23件pass、テストコード自体はリポジトリに存在し確認可能だが
実行結果csvは保存されていない）に依存する。**永続化された生データファイルが存在しない
ため、本ラウンドの照合方針（csv/json/txt との突合）では8件すべて NO_DATA**（テストコード
自体は `tests/test_cpsat_pebble.py` に実在することは確認したが、個々の探索結果ログは
再実行しないと再現できず、本タスクは重い計算の再実行を禁じられている）。

## data/cpsat_interval_findings.md

対応する csv/json/txt は無し（`scripts/cpsat_interval.py`・`tests/test_cpsat_interval.py`
の実行ログに依存し、永続化された生データファイルは `data/` に存在しない）。
§3の到達範囲表（n=30,50,80,120,160でM*=59,99,159,239,319、いずれも2n-1と一致してOPTIMAL、
n=250はUNKNOWN）・§4の上界表（e=e*-1でn=30が69・n=50が113）・完全二分木の系列
1,5,17,53,155,429・ピラミッド系列5,13,27,47,105,99は、いずれも再実行ログでしか
確認できずNO_DATA。ただし完全二分木の M*(T5)=155, M*(T6)=429 は `docs/STATUS.md` の
「候補1 M*(T5)=155, M*(T6)=429（層3・三層照合）」という独立記載と一致するため、
生データファイルではなく別ドキュメントとの整合という限定的な意味で MATCH と扱う。
残り11件は NO_DATA（再実行禁止のため照合不能。手計算・ソルバログのみに存在する数値）。

## data/exp01_findings.md

生データ: `data/exp01_trees.csv`（31行、chain/cbt/pyr の各正規化）。

- 鎖 $M^*$ 列 chain(1)..chain(14): CSVの `M*_p_min+0` 列を抽出すると
  `1,3,5,9,11,15,19,25,25,29,33,39,45,53` で doc記載の数列と完全一致 → MATCH。
- 「cbt(h) all-pebbled = cbt(h+1) free-leaves」: h=1→2、2→3、3→4 の3組すべて
  (p_min, M*, M*+1, M*+2) が行単位で完全一致 → MATCH（3件）。
- 「pyr(h) all-pebbled = pyr(h+1) free-base」: h=1→2、2→3、3→4 の3組も同様に完全一致
  → MATCH（3件）。
- §3 完全二分木表（h=1,2,3 の vertices/p_min/M*/M*+1/M*+2）: CSVの該当行と全項目一致
  → MATCH（3行）。
- §4 ピラミッド表 h=1..4（vertices/p_min/M*）: CSVと一致 → MATCH（4行）。
  **h=5 行（vertices21, p_min8, M*=105）は `exp01_trees.csv` に all-pebbled 版が
  収録されておらず**（同ファイルは `pyr(5) free-base` までしかない）、この生データ単体では
  照合不能 → NO_DATA。ただし後続の `data/exp01_results.md`（L91, L115, L119）が
  「初回測定の M*(P5)=105 はCSVには未収録だったので独立に裏取りした」と明記した上で
  p_min=8, M*=105, 3, 67/63/61 等を再測定・収録しており、そちらでは MATCH する
  （クロスドキュメントでの裏取りは取れている）。

exp01_findings.md は15件中14件 MATCH、1件（pyr h=5の元データ欠落）NO_DATA
（別ファイルでの独立再測定はある）。

## data/exp01_oeis_draft.md

生データ: `data/exp01b_tradeoff.csv`（cbt*/pyr*/spinal*/chain/butterfly 各系列）、
`data/exp01b_saturation.csv`（spinal, k=1..16）、`data/exp01_results.md`（T6=429等の追加確定値）。

- エントリ1（完全二分木 $M^*$）: `1,5,17,53,155,429`、p_min `1,3,5,6,7,8` —
  tradeoff.csv の cbt* 行（5,17,53,155）と exp01_results.md L91-96（155,429,p_min 7,8）を
  合わせて完全一致 → MATCH。成長比 `5,3.40,3.12,2.92,2.77` も実測値の比と一致 → MATCH。
  予想式 $2\cdot3^{n-1}-1$ の n=5,6予測値 161,485 も計算どおり → MATCH。
- エントリ2（ピラミッド）: `5,13,27,47,105,99`、p_min `3,5,6,7,8,10` — tradeoff.csv の
  pyr* 行と完全一致 → MATCH。式 $3n^2-n+3$ の n=1..4予測 5,13,27,47 と n=5予測73も
  計算どおり → MATCH。
- エントリ3（spinal tree）: 16項の数列とp_min公式 $\lfloor\log_2 n\rfloor+3$ を
  `exp01b_saturation.csv` の `M*_p_min`・`p_min` 列と全16点照合 → 完全一致 MATCH。
- エントリ4（complete computation）: `2,6,20,58,168,380`、$S_{\min}$=`1,3,4,5,6,8` —
  `exp01_results.md` L509-514 の表と一致 → MATCH。比の推移 `3,3.33,2.9,2.9`→2.26も
  計算どおり → MATCH。
- 「バタフライ全出力 2,12,44」は `exp01b_butterfly.csv` の
  `butterfly all-outputs` 行 k=1,2,3 の `M*_p0` 列と一致 → MATCH。
- OEIS A263678 との5項一致（5,17,53,155,429）は外部データベースとの照合であり
  本リポジトリのデータでは確認できないため NO_DATA（ただし数列自体はエントリ1と同一で
  そちらはMATCH済み。A263678自体への一致主張のみ照合不能）。

exp01_oeis_draft.md は主要20件相当がすべて MATCH（外部OEIS照合1件のみ言及するが
数値主張としては前段のMATCH済み数列の再掲であり二重計上しない）。

## data/exp01_results.md（822行、大規模ファイル。主要表・数値を全数照合）

生データ: `data/exp01b_tradeoff.csv`（chain/cbt*/pyr*/spinal free-leaves/spinal*/butterfly、
全11系列）、`data/exp01b_saturation.csv`（spinal k=1..16）、`data/exp01b_schedules.md`
（put多重度の実測記述）。

- §2.1 完全二分木表（h=1..6、7列×6行）: tradeoff.csv の cbt* 行と h=7段（p_min=10,
  超過分3）は exp01b_certificate.md の確定値と突き合わせ → 全項目 MATCH。
- §2.2 ピラミッド表（h=1..6）: tradeoff.csv pyr* 行と完全一致（p_min-h列 2,3,3,3,3,4含む）
  → MATCH。
- §2.3 spinal $S_k^*$ 表（k=1..16、p_min・M*(pmin)・M*(pmin+1)の3行）と
  バタフライ表（k=1..3）: saturation.csv・butterfly.csv の該当列と全数一致 → MATCH。
- §3.1 put多重度表（総put/頂点数・最大put・比率6行）: `exp01b_schedules.md` の
  該当プログラム出力（例: 「頂点数21、総put53(平均2.52回/頂点)、最大put5回」等）と
  文言レベルで6件とも完全一致 → MATCH。
- §3.3 飽和指標σの全表（鎖 n=4..16、spinal k=8..16、ピラミッドh=5,6）:
  tradeoff.csv/saturation.csv の M*_p_min と M*_p_min+1 から σ=M*(pmin)/M*(pmin+1) を
  再計算し、鎖(1.286,1.222,1.154,1.118,1.190,1.087,...,1.233,1.298,1.392)・
  spinal(1.075,1.164,1.197,1.247,1.308,1.305,1.281,1.307,1.224)・
  ピラミッド(1.567, 1.112) をすべて小数第3位まで再現 → MATCH（saturation.csv には
  σ列がそのまま存在し直接照合できた）。
- §4.1 予想式 $2\cdot3^{h-1}-1$ の反証表（h=2..6の予想値5,17,53,161,485 vs 厳密値
  5,17,53,155,429）、成長比3.40/3.12/2.92/2.77、n比2.43/3.53/5.00/6.81、階差4,12,36,102,274
  — すべて実測値からの再計算と一致 → MATCH（計約10件）。
- §5 OEIS照合結果（`null`＝未登録、A263678部分一致）は外部APIレスポンスに依存し
  本リポジトリのcsv/jsonでは再現できないため NO_DATA（ただし対象の数列自体は上記で
  MATCH 済み）。

exp01_results.md は主要な数値主張（表・比率・予想反証）を計60件程度サンプリング検証し
全件 MATCH。OEIS照会結果の生データ非保存のみ NO_DATA 扱い（数列自体は別途MATCH）。

## data/exp01b_bounds_t7.md・exp01b_certificate.md・exp01b_schedules.md

いずれも自動生成（手編集禁止）だが対応する永続csvは無く、スクリプト再実行ログに依存。
- bounds_t7.md: 上界の合成表（295+339+1+429+339=1403）は文書内の数値どうしの
  算術が一致 → MATCH（3件: 合計1403、下界561=4×140+1、改善後下界603=2×(140+161)+1）。
  ただし基礎値 $g_5(10)=140$, $g_5(9)=161$ 自体は生データファイルが無く NO_DATA（2件）。
- certificate.md: 「部分木の手数」列(5,17,53,155,429系列)は `exp01_trees.csv`/
  `exp01b_tradeoff.csv` の cbt* 系列（5,17,53,155,429）と一致 → MATCH。
  「合成後の手数」列(21,69,213,621,1717)は `4×部分木手数+1` の関係で内部無矛盾
  （21=4×5+1、69=4×17+1、213=4×53+1、621=4×155+1、1717=4×429+1）→ MATCH（内部整合、
  1717はexp01b_bounds_t7.mdの上界計算にも再登場し相互整合）。h=7段のp_min=10・
  超過分列0,1,2,2,2,2,3もexp01_results.md §4.3と一致 → MATCH。
- schedules.md: 数値（頂点数・総put・最大put・比率）は exp01_results.md §3.1 の
  照合で6件ともすでに突合済み（重複計上しない）。

## data/exp02_results.md

生データ: `data/exp02_n7_classes.json`（13.7MB）、`data/exp02_n7_pr.json`（17.2MB、
`{n:7, rows:[{edges,p,r}×138101]}`）、`data/exp02_n7_checkpoint.json`（27.3MB、途中経過）。
巨大ファイルは全読込せず Python で集計のみ実施。

- 非同型類数列 `1,1,3,16,164,3341`（n=1..6）は OEIS A350415 との一致主張。数値自体は
  文書内表（§②）の行数と自己整合（1,1,3,16,164,3341の各nでの分布個数合計と一致）→ MATCH
  （A350415への一致は外部DBの話でNO_DATA、数列自体はMATCH）。
- **n=7 の主要結果を `exp02_n7_pr.json` で完全再集計**: 非同型類数 138,101 件 → MATCH
  （doc §⑨「n=7の非同型類数は138,101」）。$(P,R)$ 分布表14行すべて再集計値と完全一致
  → MATCH（(2,4)=1, (3,4)=182, (3,5)=1429, (3,6)=13, (4,4)=117, (4,5)=19747, (4,6)=12544,
  (4,7)=27, (5,5)=8964, (5,6)=53567, (5,7)=2609, (6,6)=21061, (6,7)=11856, (7,7)=5984）。
  R=P個数36,126・R>P個数101,975・最大ギャップ3、いずれも再集計と完全一致 → MATCH。
  これは `docs/STATUS.md` の「候補2 n≤7 全数: 非同型類138,101、R−P最大3」とも整合 → MATCH。
- n≤6の分布表（§②、5行）・n=7部分スキャン(280秒・28.1%・172,563/615,195件)・
  合流コスト解析(§⑩、141,627件・n=7で2件の反例等)は、対応する生データファイルが
  無い（n≤6は集計結果のみ文書に残り元の非同型類挙上は保存されていない）ため NO_DATA
  として1件計上（n=7大量データで検証できた9件超は上記でMATCH計上済み）。

exp02_results.md は主要主張（特にn=7の全数データ、最も重要な数値群）を生データで
完全照合でき全件 MATCH。n≤6分布・部分スキャン統計など一部は生データ非保存で NO_DATA。

## data/exp03_lean_plan.md・exp03_results.md（大規模51.6KB、代表箇所を精査）

生データ: `exp03_surface_ops.csv`（561行）、`exp03_reach.csv`（25行）、
`exp03_ltv_compare.csv`（49行）、`exp03_ltv_vs_ours.csv`（49行）、他 esat/pmin_e 系。

- 定理A §A.5「$M^*(16,5,1)=45$」を `exp03_surface_ops.csv` で直接照合
  （n=16,p=5,e=1 の行が mstar=45）→ MATCH。
- 定理B1 §B.1「$\mathrm{reach}(p,e)=(e+2)2^{p-2}$」の再帰式は `exp03_reach.csv`
  （p=1..5, e=0..4、25行、`formula`列・`match`列すべて1）で全数一致 → MATCH。
  ただし doc 本文が主張する検証範囲「$2\le p\le8$, $0\le e\le6$ の63組」は
  `exp03_reach.csv`（p=1..5のみ）には収録されておらず、対応する生データが
  リポジトリに存在しない → **NO_DATA**（範囲外・別実行のログのみで再現不能）。
- §B.1.1「LTV Procedure A は $(e+1)2^{p-2}$、`data/exp03_ltv_compare.csv` の
  **全45行**が検証器を通過、$p\in\{4..8\}\times e\in\{1..6\}$ の**30点**すべてで一致」:
  `exp03_ltv_compare.csv` を再カウントすると **49行**（全て ok=1）であり、
  doc記載の「45行」と食い違う → **MISMATCH**（doc: 45行 ／ 実データ: 49行、いずれも
  全件パス）。一方「30点」の部分主張（p=4..8×e=1..6 のサブセット）は再計算で
  30/30件が式と一致し MATCH（内訳は正しいが総行数の記述が古い可能性）。
- §A.4 の検証範囲（n≤21,p≤7で943assertion、n≤14,p≤7の最適解照合、42事例のoff-by-one
  検出）は `tests/test_exp03_proof.py` の実行結果でありcsv化されていないため NO_DATA。

exp03_results.md は精査した12件相当のうち9件 MATCH、1件 MISMATCH（LTV比較行数
45 vs 49）、2件 NO_DATA（範囲外・テストログ由来）。ファイル全体（51KB）は
大部分が証明の記述で数値主張は上記付近に集中しており、他の小節は概ね上記と
同型の値の再掲（二重計上を避けるため個別列挙はしない）。

## data/exp04_results.md

生データ: `exp04_fib.csv`（fib(1..29)）、`exp04_grid.csv`（grid(1,1)..(5,5)）、
`exp04_pascal.csv`（pascal(1..6)）。

- §5 グリッド表（k=1..5、6列×5行）: `exp04_grid.csv` と完全一致 → MATCH。
  「$M^*(k,k)$=1,7,25,63（4点）」「$p_{\min}$=1,4,6,8（4点）」も csv の該当列
  （k=2..5）から再現 → MATCH。
- §6 パスカル表（n=1..6）: `exp04_pascal.csv` と完全一致 → MATCH。
- fib表（本文冒頭、n=1..29）: `exp04_fib.csv` と全29行完全一致 → MATCH。
- §11.3/§11.5/§13.1-13.5 の拡張値（fib n=30..49、grid(6,6)、grid(7,7)）は
  `exp04_fib.csv`・`exp04_grid.csv` に該当行が無く（両csvともn=29／k=5までしか
  持たない）、フロンティアDP拡張実行のログにのみ存在するため **NO_DATA**
  （fib(33)=125、fib(49)=231、grid(6,6)p=10=117、grid(7,7)のp_min=12・M*=195等、
  計5件相当）。ただしdoc内で「§11.3, §11.5と一致」のように独立算出2回の
  相互参照がある旨が明記されており、外部生データが無いことと数値自体の
  不確からしさは別問題である。

exp04_results.mdは基本表（グリッド・パスカル・fib、計約40件相当）が全てcsvとMATCH。
フロンティアDPで拡張した後段の値（5件相当）はcsv非保存でNO_DATA。

## data/exp05_results.md

生データ: `data/exp05_quintuple_k5.json`（k=5五つ組の全数枚挙、458B）、
`exp05_ordinary_k4.json`（0B、空）、`exp05_k5.err`（EXIT=0）、`exp05_ord4.err`（EXIT=124＝
タイムアウト）、`exp05_slowtests.log`（アサーション形式のテストログ）。

- §④五つ組表 k=5行（枚挙451,479・停止223,444・巡回2,740・並進216,565・停止規則なし8,730・
  未判定0・BB_rev=388・Σ_rev=16）: `exp05_quintuple_k5.json` の該当フィールドと
  1対1で完全一致 → MATCH。チャンピオン機械文字列
  `1RB0RD_1RC0RB_1RD1RZ_1LE1LA_0LE0LA` も json の `best_steps_machine` と一致 → MATCH。
- §93「TNF全数枚挙 k=4 は未完走・保留」: `exp05_ordinary_k4.json` が空(0B)かつ
  `exp05_ord4.err` が `EXIT=124`（タイムアウト）であり、doc の「未完走」記述と
  整合 → MATCH（doc は正直に不完全と報告しており、値の捏造は無い）。
- チャンピオン直接実行3件（BB(2)=6/4, BB(3)=21/5, BB(4)=107/13）は
  `exp05_slowtests.log` のアサーション出力と一致（steps/ones とも） → MATCH。
- 五つ組 k=1..4 の表・四つ組 k=1..6 の表・§⑥通常BBとの比較表・§⑦単射性の集計
  （計8件相当）は対応する生データファイルが `data/` に保存されておらず
  （k=5以外の枚挙結果は永続化されていない）NO_DATA。

exp05_results.md は生データが存在する部分（k=5五つ組の全数値、k=4未完走の記録、
チャンピオン直接実行）はすべて MATCH。それ以外の枚挙表はcsv/json非保存で NO_DATA。

## data/exp10_results.md

生データ: `data/exp10_scan.txt`（スクリプトの生出力ログ、実験A〜Eを保持）。

実験A（n=3全4140分割でg_free=lb不一致0件、素朴後戻り探索照合198件不一致0）、
実験B（n=3全4140分割の(lb,g_proj)分布表: (0,0)1,(1,1)495,(1,2)252,(1,3)16,
(2,2)2363,(2,3)668,(3,3)345、gapヒストグラム{0:3204,1:920,2:16}、gap>0が936件、
最大gap=2）、実験B2（二重実装照合4140件不一致0）、実験C（n=4,m=1全65536関数、
(3,3)942・(3,4)11928・(4,4)52666、gapヒスト{0:53608,1:11928}、最大gap1）、
実験D（N=2:4個・N=3:150個・N=4:967976個すべて偶置換、生成群位数N=2:24・N=3:40320）
のすべての数値を `exp10_scan.txt` の該当行とテキストレベルで突き合わせ、
18件すべて完全一致 → MATCH。docs/STATUS.mdの層1[Lean済]主張（候補10の下界特徴づけ・
パリティ障害）とも整合。

exp10_results.md は精査した数値主張すべて MATCH（生ログとの一字一句の対応が確認できた）。

## data/exp51_janus_trace_findings.md

永続csv/jsonは無いが、軽量スクリプト `scripts/exp51_janus_trace.py` を読み取り専用で
再実行して照合（重い禁止スクリプトには該当しない）。
§2表: fib.janus（異なる配置71・正規化後手数70・ピーク10・終端0-9全部）、
fac.janus（9・8・6・終端0,1,2,3,4,6）を再実行し、出力が文書の表と完全一致 → MATCH（6件）。
§7「1回呼び版」の数値（手数5・ピーク5、対単位の比較表4行）は対応するCLIが
`data/fixtures/fib_once.janus` を直接取れる形で存在せず、再実行による照合ができないため
NO_DATA（4件。ただし §2 の元スクリプトの正しさが確認できているので、手法自体の
信頼性は間接的に裏付けられる）。

exp51_janus_trace_findings.md は再実行で確認できた§2の6件が MATCH、
§7の4件は再現手段がなくNO_DATA。

## data/exp52_cutrod_findings.md（既知の測定バグ・訂正済みファイル）

`~/dev/CLAUDE.md`／本リポジトリ CLAUDE.md が言及する「exp52のスタック値(75,802等)は
測定バグ。正は310/14/16」の訂正が、このファイル自身の §7（2026-07-28訂正）に
明記されており、旧版の値も訂正後の値も両方文書内に残っている。

- §1旧表（steps 8497/959/27157、メモpeak7/10/20、旧stack peak 75802/39/45）と
  §7訂正表（正しいstack peak 310/14/16）を `data/atlas/atlas.csv` の
  `topDownCutRod`(steps8497,stack310)・`topDownCutRod_symmetric`(steps959,stack14)・
  `topDownCutRod_twoMemoTables`(steps27157,stack16)の3行と突き合わせ、
  steps・訂正後stack_peakとも完全一致 → MATCH（訂正後の値が「正」として現行データと
  一致することを確認。旧値はdoc自身が「誤り」と明記しているため誤りとして扱う）。
  典拠済み訂正のため再指摘はしない、との指示どおり新規の指摘はしていない。
- §7末尾の再評価数値（317=7+310、24=10+14で約13倍、317対34で約9倍）も
  算術として内部無矛盾 → MATCH。

exp52_cutrod_findings.md は訂正済みの状態が現行atlas.csvと完全に整合しており
13件相当すべて MATCH。CLAUDE.mdが言及する既知修正の再指摘は行っていない。

## data/holonomic_findings.md・data/holonomic_guess.md

生データは `holonomic_guess.md` 自身（`scripts/exp_guess_sequences.py` の自動生成）。

- 「15本中0本」の主張: `holonomic_guess.md` 内の `### ` 見出し数を数えると15、
  各節すべてが「見つからなかった」または「判定不能」（見つかった0件）→ MATCH。
- Σ_rev(k)（可逆BBの最大1の個数）の引用数列 `[1,2,4,8,16]`（k=1..5）を
  `data/exp05_results.md` の Σ_rev 列（1,2,4,8,16）と突き合わせ → MATCH。
- 健全性チェック表（Fibonacci/Catalan/Motzkin/中央Delannoy等の既知の漸化式発見）は
  スクリプトの再現実行が必要で本ラウンドでは未実施のため NO_DATA（1件。数式自体は
  標準的に正しいものだが実行確認はしていない）。

holonomic_findings.md・holonomic_guess.md は主要主張が内部・cross-file整合で
MATCH（計7件相当）、健全性チェック式の実行未確認1件のみ NO_DATA。

## data/ic3_b2_findings.md・data/ic3_b2_tight_support.md

ic3_b2_findings.md: `data/`配下に対応するcsv/jsonが無い（nuXmv/ABCの実行ログのみに
依存）。§2の(p,e)検証表・§5.3の2エンジン比較表・時間切れ表（400秒/240秒）は
すべて NO_DATA（8件相当。再実行にはnuXmv/ABCという外部ツールが要り、本ラウンドの
方針（重い計算再実行禁止・自己完結ツールでの照合優先）から見送った）。

ic3_b2_tight_support.md: `data/tight_support/`ディレクトリ（34インスタンスjson＋
`pdr_matrix.json`、計35ファイル）が実在し、doc冒頭「34インスタンス」の記述と
ファイル数が一致 → MATCH。個々のjsonの構造（`n,p,e,claim,layer_sizes,staircase,
tip_minsupp_by_u,minsupp_by_u,maxgap_by_u`等のキー）も存在確認 → MATCH。
「2905照合点・反例0」「約270万点・反例0（予想U）」等の集計数値は、生データが
存在するものの本ラウンドでは全ファイルを走査した独立再集計まで至らず NO_DATA
（4件相当。ファイルの実在とスキーマの妥当性は確認済みだが、合計値の桁までは
突合していない）。

ic3系2ファイルはic3_b2_findings.mdが生データ非保存で全件NO_DATA、
ic3_b2_tight_support.mdはデータディレクトリの実在・件数はMATCHしたが、
内部の集計数値までは今回照合できずNO_DATAとした。

## data/mip_findings.md・data/mip_stage_findings.md

生データ: `data/mip_stage_bench.csv`（32行=4solver×8case）、
`data/mip_stage_scale.csv`（54行）。

- mip_findings.md §2の解法状況（CP-SAT 7/8・Gurobi 7/8・SCIP 5/8、chain(12)e=0が
  3ソルバとも解けない）を `mip_stage_bench.csv` の `interval-cpsat` 系列8行の
  status・moves列と突き合わせ（このcsvはmip_stage実験用に後日採取されたものだが
  同じ8ケースのinterval版として整合）→ 解けた/解けない・move値とも一致 → MATCH
  （タイミング秒数は実行毎に変動するため厳密一致は求めず参考値として扱う）。
- mip_stage_findings.md §0/§3の headline（stage-Gurobi 8/8最悪3.0秒、stage-CPSAT
  0.19秒、旧interval 7/8）を `mip_stage_bench.csv` で再集計: stage-cpsat 8/8
  (max 0.19s)・stage-gurobi 8/8(max 3.01s)・stage-scip 8/8(max48.99s)・
  interval-cpsat 7/8(max60.03s) → 全項目 MATCH。
- §4境界域スケーリング表（chain(16..32)・cbt・pyr、18行、BFS値・stage-CPSAT値・
  FEASIBLE上界値含む）を `mip_stage_scale.csv`（54行）と突き合わせ、
  5件の「×」（FEASIBLE時のmoves≠bfs: 113/109, 205/145, 103/91, 237/193, 71/69）を
  含め全項目一致（doc自身がFEASIBLEは非最適上界と明記しており、不一致ではなく
  想定どおりの挙動） → MATCH。
- 変数・制約数の比較表（interval 4257/7063/5748 vs stage 900/2063/0）、
  「143ケース×3ソルバ」照合、cbt(5)のtreedp照合(M*=155、既に他ファイルでMATCH済み)は
  対応する生ログ・csvが無く NO_DATA（3件相当）。

mip_findings.md・mip_stage_findings.mdは、生データ（bench.csv・scale.csv）と
照合できた主要数値（計約17件）がすべてMATCH。単一実行の内部統計3件のみNO_DATA。

## data/mstar_independent_check.md

このファイル自身が「正本」（生ログはスクラッチパスにあり本リポジトリにはコミットしない
と明記）なので、外部csv/jsonとの照合ではなく**文書内の算術の自己整合性**を検査した。

- 族グラフ検査（55インスタンス・2286チェック）と小DAG全数（7050インスタンス・
  141000チェック）の小計 2286+141000=143286 → 表の「合計」欄と一致 → MATCH。
- 小DAG非同型類の内訳 $n=2..6$: 1,3,16,164,3341 の和 3525、×2(free変種)=7050
  → 本文中の数値と一致し、`data/exp02_n7_pr.json`裏取り済みのA350415数列
  （n=1..6: 1,1,3,16,164,3341）とも整合 → MATCH。
- 「個別の裏取り」表（chain(4,6,8,12)のe=0,1値: 9/7,15/11,25/17,39/29）を
  `data/exp03_surface_ops.csv`・`exp03_reach.csv`等の既確認値と突き合わせ → MATCH。
- **「総計144,309チェック」の再計算で不整合を検出**: 結果概要の表(143,286)＋
  直接比較103件＋80件＋standard_bfs比較104件＋p_min境界比較336件 の合計は
  143,286+103+80+104+336=**143,909**であり、本文が結論部で述べる
  **「144,309チェック」と400件の差がある** → **MISMATCH**（doc内の算術不整合。
  どちらの数字が意図された値かは判定しない。内訳表自体は各項目ともMATCHしている
  ため、合計の記載のみの問題と考えられる）。
- 「$n\le6$ 未検査領域」等の定性的記述はNO_DATA（生ログがスクラッチパスにしかなく
  本ラウンドでは参照できない、1件）。

mstar_independent_check.mdは10件MATCH、合計値の算術に1件MISMATCH（143,909 vs
144,309）、生ログ非参照1件NO_DATA。

## data/sat_encoding_design.md・data/sat_findings.md・data/sat_lower_bound_findings.md・data/sat_proof_manifest.md

sat_proof_manifest.md 自身が明記するとおり、DRAT証明の本体はリポジトリ外
（`<local>/proofs/...`）にあり `data/` には永続化されていない。

- **cross-file整合の発見**: `sat_findings.md` §表の「k=M*-2」列の値
  （chain4: 7,5／chain6: 13,9／chain8: 23,15／chain12: 37,27）が、
  `sat_proof_manifest.md` のインスタンス名（`chain4_p3_e0_k7`等）の
  k値と完全に一致 → MATCH（8件）。BFS $M^*$ 列（9,7,15,11,25,17,39,29）も
  `exp03_surface_ops.csv`/`mip_stage_bench.csv` の同じchainケースのbfs値と
  一致 → 既に他ファイルでMATCH済みのため二重計上しない。
- sat_proof_manifest.md の「VERIFIED 8件/NOT VERIFIED 8件」は列挙された16行を
  実際に数えて確認 → MATCH（1件）。ただしVERIFIED/NOT VERIFIEDの判定自体が
  正しいかはDRAT証明本体（リポジトリ外）を検査しないと分からないため、
  判定内容の真偽はNO_DATA（件数の内部整合のみMATCH）。
- sat_lower_bound_findings.md の証明サイズ表（変数・節・DRATサイズ・検査秒、
  n=8,12,16,20の4行+n=30時間切れ）は対応する生ファイル（DRAT証明・CNF）が
  リポジトリに無く NO_DATA（5件）。
- sat_encoding_design.mdは符号化方式の設計文書で具体的な数値実測はほとんど
  含まないため対象外（データ有無の判定を要する数値主張なし）。

SAT系ファイル群は、cross-file整合が取れる部分（8+1=9件）はMATCH、
証明ログ本体に依存する数値（5件）はリポジトリ外のためNO_DATA。

---

## 進捗（全体まとめ）

### 完全にカバーした（生データと数値レベルで突合した）

- `data/atlas/findings_phase0-4.md`（5本、atlas/*.csv・*.json 全種で照合。phase4で
  L2被覆に関するMISMATCHを発見）
- `data/exp01_findings.md`・`exp01_oeis_draft.md`・`exp01_results.md`・
  `exp01b_bounds_t7.md`・`exp01b_certificate.md`・`exp01b_schedules.md`
  （exp01_trees.csv, exp01b_tradeoff.csv, exp01b_saturation.csv, exp01b_butterfly.csv
  で照合。ほぼ全件MATCH）
- `data/exp02_results.md`（exp02_n7_pr.json 13.7〜17.2MBをPythonで集計しMATCH確認）
- `data/exp03_results.md`（主要な定理A/B1周辺をexp03_surface_ops.csv・exp03_reach.csv・
  exp03_ltv_compare.csvで照合。LTV比較行数45 vs 49のMISMATCHを発見）
- `data/exp04_results.md`（exp04_fib/grid/pascal.csvで基本表を完全照合）
- `data/exp05_results.md`（exp05_quintuple_k5.json・.errファイルで照合。k=4未完走の
  記録が空ファイル+タイムアウトerrと整合することを確認）
- `data/exp10_results.md`（exp10_scan.txtの生ログと全数値を一字一句突合）
- `data/exp51_janus_trace_findings.md`（軽量スクリプトを実際に再実行して§2を確認）
- `data/exp52_cutrod_findings.md`（既知の訂正がatlas.csvと完全整合することを確認）
- `data/holonomic_findings.md`・`holonomic_guess.md`（節数と cross-file の Σ_rev 列で確認）
- `data/mip_findings.md`・`mip_stage_findings.md`（mip_stage_bench.csv・
  mip_stage_scale.csvで主要数値を全件照合）
- `data/mstar_independent_check.md`（文書内算術の自己検算で合計値の不整合を発見）
- `data/sat_findings.md`・`sat_proof_manifest.md`（インスタンス名とk値のcross-file
  整合を確認）
- `data/exp10_scan.txt`／`data/atlas/*.csv`／`data/exp0*.csv`等の生データファイルは
  すべて実測・再集計した（大きいjson3本は集計のみでフル読込はしていない）。

### 部分的にしかカバーできなかった／生データが無くNO_DATAとしたもの

- `data/cpsat_findings.md`・`cpsat_interval_findings.md`：対応する永続csv/jsonが
  リポジトリに存在せず、スクリプト実行ログにのみ依存する主張がほとんど
  （重い計算の再実行は本タスクの方針で見送った）。
- `data/exp03_lean_plan.md`：計画書で数値主張が少ない。
- `data/ic3_b2_findings.md`：nuXmv/ABCの実行ログのみに依存し永続データなし。
- `data/ic3_b2_tight_support.md`：`data/tight_support/`ディレクトリ（34+1ファイル）の
  実在・スキーマは確認したが、2905点・270万点規模の集計値の独立再計算までは
  時間の制約で実施していない。
- `data/sat_lower_bound_findings.md`：DRAT証明・CNF本体がリポジトリ外
  （`<local>/proofs/...`）にあり照合不能。
- `data/sat_encoding_design.md`：設計文書で数値実測がほぼ無い。

### 見つかった問題点（要フォローアップ）

1. **MISMATCH**: `data/atlas/findings_phase4.md` の L2 被覆率（39/118・67%未登録・
   3層一致24本・L1のみ21本）が、現行 `coverage_l123.csv` の再集計（87/118・26%未登録・
   3層一致64本・L1のみ3本）と一致しない。Sorting・Searchingカテゴリで特に大きく食い違う。
2. **MISMATCH**: `data/exp03_results.md` の「LTV比較 `exp03_ltv_compare.csv` の全45行が
   検証器通過」に対し、実ファイルは49行（全て合格）。
3. **MISMATCH**: `data/mstar_independent_check.md` の「総計144,309チェック」が、
   本文が列挙する内訳の合計143,909と一致しない（400件の差）。
4. 上記いずれも「どちらが正しいか」の判定はしていない（指示どおり中立に両値を併記）。

### 今回チェックしなかったこと（範囲外・時間制約）

- 各docが引用する外部OEIS照会結果の再現（`oeis.org/search`は本ラウンドで呼んでいない）。
- `docs/`配下（STATUS.md等）とdataの整合性チェックは、data側の裏取りに使った限りでのみ実施。
- 重い計算スクリプト（`scripts/mip_*.py`, `sat_pebble.py`, `mstar_indep.py`,
  `frontier_run.py`, `support_truth.py`, `pdr_tighten.py`）は指示どおり実行していない。
- `git`操作・ファイル編集（本監査ファイル以外）は一切行っていない。

### 全体状況（2026-08-10 追記）

`data/*.md`・`data/atlas/*.md` 全32本（本監査ファイル自身を除く）を上のサマリ表で
網羅した。**MISMATCH と NO_DATA は分類上厳密に区別しており、「元データが無い」ことを
「誤り」として扱った箇所はない**（NO_DATA は照合不能を意味するのみで、doc の主張の
真偽について何も述べていない）。`data/ic3_b2_tight_support.md`・`scripts/mip_*.py` 等
の制約対象ファイルは編集・実行していない（`ic3_b2_tight_support.md` は既存記述との
突合のための読み取りのみ）。追加で見つかった数値主張・新規docが今後追加された場合は
このファイルに追記する。
