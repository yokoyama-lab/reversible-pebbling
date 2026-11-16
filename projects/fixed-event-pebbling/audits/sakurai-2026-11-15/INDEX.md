# さくらいの監査（2026-11-14〜15）: 和文 IPSJ 原稿「配置回数と実消去位置を固定した最短鎖ペブリングの全順序分類と厳密な半順序被覆数」と Lean 化

> **正本の移転（2026-11-16）**: 原稿（v16）・Lean・この監査記録の正本は private リポジトリ `yokoyama-lab/fixed-event-pebbling`（ghq: `github.com/yokoyama-lab/fixed-event-pebbling`）に移った。以下の「新しいリポジトリは作らず」はそれ以前の記述。

作成 2026-11-16（取り込み担当のサブエージェント）。**これは記録であって取り込みではない**（理由は「正本の所在」）。
入力は `<local>/paper-audits/` の 44 件（読むだけ。変更・削除・移動はしていない）と、
showa の写し `proj/showa-import/drive/さくらい/`（11-16 追加分。読むだけ）。

## 正本の所在

- 原稿の正本は**手元のどの git リポジトリにも無い**。
  - v15 の `manuscript.tex`（sha256 2cd638db…fd94）と `main_ipsj.tex`（2b704aac…bab9a）は
    `<local>/paper-audits/ipsj-v15-official-build-20261114T1600/received/ipsj_v15_residual_1600/` と `source/` にだけある。
    showa の写しには v12・v13 の zip／tar.gz と v15 の tar.gz（`20261114T1600-IPSJ-v15-build-results.tar.gz`）がある。
  - `overleaf/` の .tex に題名は無い（`rg --no-ignore -g '*.tex'`）。`2026_erasure_pebbling`（英文 IEICE・Exact Time–Space–Erasure）は
    v13 README が明記するとおり**別原稿**。pubtrack の outputs.tsv・exits.tsv にもこの和文原稿の行は無い。
  - Lean の識別子（`pairTrace`・`SignatureInvariant`・`LocalCertificate`・`CommonExtension`・`ErasureCover`）は
    `github.com/yokoyama-lab/*pebbling*` 10 本に無い（`rg -L --no-ignore -g '*.lean' -g '!.lake/**'` と `find -L -name` の 2 手）。
    Lean は paper-audits の各単位の平置きのソースにだけある。
  - 原稿には著者「著者未確定」・所属「TBD」・「投稿準備稿」とあり、「v14 正本／Overleaf は変更なし」とあるが、その Overleaf は手元で見つからない。
- 依頼の規則に従い、**新しいリポジトリは作らず**、この記録（INDEX.md・NOTES.md・recheck/）だけを置いた。
  `proj/showa-import/` は `<local>/dev` の .gitignore（`/*`）で追跡外なので **commit していない**。
- **置き場の提案**（人の判断）:
  1. 推奨: `github.com/yokoyama-lab/fixed-event-pebbling`（private）を新設し、`paper/`（v15 一式）・`lean/`（下表の緑 25 単位のソースを
     1 つの lake プロジェクトに統合。依存の重複は sha が同じなら 1 本に）・`audits/sakurai-2026-11-15/`（この記録）を置く。
     Mathlib は `reversible-pebbling-lean-lowend` と同じ fabf563a に固定。
  2. 代替: 既存の `yokoyama-lab/reversible-pebbling-lean` に `FixedEvent/` として入れる（ただし原稿とは別リポになる）。
  3. Overleaf の和文プロジェクトが実在するなら（「v14 正本／Overleaf」）それを正本とし、Lean だけ 1 か 2。

## 44 件の内訳

| 種類 | 件数 | 中身 |
|---|---|---|
| `PEBBLING-*-20261115-A1/A2` | 34 | Lean 4.31.0・`-j1`・`-M1800`・MemoryMax 2G・CPU 30 秒（Q-CONVERSE だけ Python・CPU 10 秒）。下の表 |
| `ipsj-v13-official-build-20261114T0900`（＋attempt2〜4） | 4 | platex＋pbibtex。初回は 3 段目 rc=1（9 頁）、attempt2 は 4 段目 rc=1（`\newblock` 未定義＝ipsjunsrt.bst と ipsj.cls の PRO 既定の組み合わせ。CAUSE.md）、attempt3・4 は 5 段とも rc=0（10 頁） |
| `ipsj-v14-official-build-20261114T1000` | 1 | 5 段 rc=0・10 頁・PDF sha 252a2386… |
| `ipsj-v15-official-build-20261114T1600` | 1 | 5 段 rc=0・10 頁・PDF sha 9b981c44…。v15 は「完了数 0 の扱い・重み付き次手・ID 枝の重複・形式検証の境界」を本文に足しただけ（NOTES.md）。新しい Lean 定理なし |
| `ipsj-state-fuel-lean-20261114T1200`（＋attempt2） | 2 | どちらも CommonExtension で rc=-6（`failed to create thread`＝環境の失敗。ソースの誤りではない）。定理の結果なし |
| `pebbling-physical-boundary-20261115/` | 1 | 適用の監査メモ（評価 C）。要約は NOTES.md |
| `pebbling-signature-reviewed-20261115T0900/` | 1 | zip（sha 5573fd4e…）: 一般定理の紙の証明 PROOF.md と独立レビュー INDEPENDENT_REVIEW.md。Lean なし・新規性未評価 |

tex のビルドは手元では再現していない（⚠ 未再検査。依頼の範囲外）。

## Lean 34 単位の表

- rc は STOP.json、sorryAx と公理は lean.log の `#print axioms`（依存のものを含む和集合）、評価は SCOPE.txt／REPORT.txt の文言（さくらいの自己評価）。
- 「手元の再ビルド」: paper-audits から `.lean` だけを scratchpad に写し、SHA256SUMS と照合（**25 単位すべて一致**）、
  依存の閉包を**ソースから全部ビルドし直し**（さくらいの .olean は使っていない）、各コンパイルを
  `systemd-run --user --wait --pipe -p MemoryMax=2G -p MemorySwapMax=0 -p RuntimeMaxSec=120` の下で
  `~/.elan/toolchains/leanprover--lean4---v4.31.0/bin/lean -j1 -M1800` で回した（<host>・2026-11-16 08 時台・1 コンパイル最大 46 秒）。
  **緑** = 全段 rc=0・.olean 生成・`error` 行なし・`sorryAx` なし・印字された公理が標準 3 公理以内、の全部。
- Mathlib が要る 2 単位（COVER-CARD・COVER-UNIQUE）は、`reversible-pebbling-lean-lowend/.lake/packages/mathlib`（HEAD fabf563a）の
  **既存のビルド**を読むだけで使った（MATHLIB_SHA256SUMS の 6 行と一致を確認。Mathlib のビルドはしていない）。
- 手元で印字された 79 定理の公理は、さくらいの lean.log の印字と**全部一致**。
| 単位（試行） | rc | sorryAx | 印字された公理（和集合） | SCOPE の評価 | 主な定理 | 手元の再ビルド |
|---|---|---|---|---|---|---|
| BEFORE-TRACE-A1 | 0 | なし | Quot.sound, propext | C | pairTrace_eq_pair_iff_before, sameSignature_before_iff, pairTrace_eq_pair_iff_before_of_mem | **緑** |
| CAPACITY-COMMON-EDGES-A1 | 247 | なし | Classical.choice, Quot.sound, propext | 記載なし | physical_enumeration_iff, perm_of_nodup_subset_length, isPermutation_iff_perm_range … | 対象外（rc≠0） |
| CAPACITY-EDGE-I-A1 | 0 | なし | Classical.choice, Quot.sound, propext | 記載なし | checked, capacity_common_edge | **緑** |
| CAPACITY-EDGE-M-A1 | 0 | なし | Classical.choice, Quot.sound, propext | 記載なし | checked, capacity_common_edge | **緑** |
| COMPLETION-EXACT-A1 | 0 | なし | Quot.sound, propext | B候補 | pairwise_of_forall_before, pairwise_no_reverse_iff_respects, completion_extensions_iff | **緑** |
| COMPLETION-GUARD-A1 | 1 | 印字なし | — | 記載なし | — | 対象外（rc≠0） |
| COMPLETION-MAP-A1 | 0 | なし | Classical.choice, Quot.sound, propext | B候補 | completion_preserves_signword | **緑** |
| COMPLETION-ORDER-A1 | 0 | なし | Quot.sound, propext | C | before_trans_of_nodup, completion_before, completion_irrefl … | **緑** |
| CONSTANT-COST-SIGNATURE-A1 | 0 | なし | Classical.choice, Quot.sound, propext | B候補 | path_constant_cost_signature, constant_cost_signature | **緑** |
| COST-GUARD-A1 | 0 | なし | Classical.choice, Quot.sound, propext | 記載なし | guarded_sub_iff, shift_of_insufficient, shift_at_exact_sum … | **緑** |
| COST-MAP-A1 | 0 | なし | propext | C | cost_eq_of_map_eq | **緑** |
| EXTENSION-BEFORE-A1 | なし（runner.py line16 unterminated string literal） | 印字なし | — | 記載なし | — | 対象外（rc≠0） |
| EXTENSION-BEFORE-A2 | 0 | なし | Quot.sound, propext | C | before_total_of_mem, pairwise_base_edge_before, permutation_pairwise_respects_base … | **緑** |
| GUARD-ASSEMBLY-A1 | 0 | なし | Classical.choice, Quot.sound, propext | C | completion_preserves_cost_and_guard | **緑** |
| NONCAPACITY-COUNTEREXAMPLE-A1 | 0 | なし | propext | 記載なし | I_permutation, M_permutation, I_noncapacity_success … | **緑** |
| PAIRWISE-CONNECTIVITY-A1 | 1 | あり | Classical.choice, Quot.sound, propext, sorryAx | 記載なし | perm, pairwise, bubble … | 対象外（rc≠0） |
| PAIRWISE-CONNECTIVITY-A2 | 0 | なし | Classical.choice, Quot.sound, propext | B候補（既知の形式化） | perm, pairwise, bubble … | **緑** |
| PATH-MAP-A1 | 0 | なし | propext | C | path_map_eq_of_comparable | **緑** |
| PHYSICAL-CAPACITY-A1 | 0 | なし | Classical.choice, Quot.sound, propext | 記載なし | step_true_iff_false_and_capacity, replay_false, replay_true_iff_capacityTrace | **緑** |
| PHYSICAL-PREFIX-GUARD-A1 | 0 | なし | Classical.choice, Quot.sound, propext | 記載なし | successful_replay_post_nonnegative, capacityTrace_iff_postUpper_of_replay_false, replay_true_iff_false_and_postUpper … | **緑** |
| PHYSICAL-REPLAY-A1 | 1 | あり | Classical.choice, Quot.sound, propext, sorryAx | 記載なし | successful_replay_cons_decompose, successful_replay_ids_exist, successful_replay_length_sum … | 対象外（rc≠0） |
| PHYSICAL-REPLAY-A2 | 0 | なし | Classical.choice, Quot.sound, propext | 記載なし | successful_replay_cons_decompose, successful_replay_ids_exist, successful_replay_length_sum … | **緑** |
| PHYSICAL-REPLAY-COST-A1 | 1 | あり | Classical.choice, Quot.sound, propext, sorryAx | 記載なし | replayWithCost_projection, successful_replayWithCost_cost, successful_replay_has_cost | 対象外（rc≠0） |
| PHYSICAL-REPLAY-COST-A2 | 0 | なし | Classical.choice, Quot.sound, propext | 記載なし | replayWithCost_projection, successful_replayWithCost_cost, successful_replay_has_cost | **緑** |
| PHYSICAL-STEP-HEIGHT-A1 | 1 | あり | Classical.choice, Quot.sound, propext, sorryAx | 記載なし | commonExtension, badCommonExtension, witnessAssignmentInjective … | 対象外（rc≠0） |
| PHYSICAL-STEP-HEIGHT-A2 | 0 | なし | Classical.choice, Quot.sound, propext | 記載なし | successful_remove_shape, successful_place_shape, successful_step_length_increment … | **緑** |
| Q-CONVERSE-A1 | 0 | 印字なし | — | 記載なし | — | 対象外（Python のみ。同一コードで再実行し一致） |
| SHIFT-COMP-A1 | 0 | なし | Quot.sound, propext | 記載なし | shift_comp | **緑** |
| SIGNATURE-COST-A1 | 1 | 印字なし | — | C（失敗） | — | 対象外（rc≠0） |
| SIGNATURE-COVER-CARD-A1 | 0 | なし | Classical.choice, Quot.sound, propext | A候補 | layerWordVector_injective, signature_number_le_cover_card, signature_cover_attains_minimum | **緑**（Mathlib 既存ビルド使用） |
| SIGNATURE-COVER-CORE-A1 | 0 | なし | Classical.choice, Quot.sound, propext | 記載なし（S ではない） | cover_class_injection, completion_class_cover | **緑** |
| SIGNATURE-COVER-UNIQUE-A1 | 0 | なし | Classical.choice, Quot.sound, propext | A候補 | minimum_cover_language_bijection, minimum_cover_unique_fiber, minimum_cover_no_empty_component | **緑**（Mathlib 既存ビルド使用） |
| SIGNATURE-INVARIANT-A1 | 0 | なし | Quot.sound, propext | C | same_sign_swap_pairTrace, same_sign_swap_signature, same_sign_swap_signword | **緑** |
| SIGNATURE-SWAP-STD-A1 | 0 | なし | Classical.choice, Quot.sound, propext | C | cost_adjacent_swap, equal_cost_swap_iff | **緑** |

### 集計

- 34 単位: rc=0 が 26（Lean 25・Python 1）、失敗 8（CAPACITY-COMMON-EDGES-A1 rc=247＝CPU 上限で候補未到達、COMPLETION-GUARD-A1 と SIGNATURE-COST-A1 は壁時計 60 秒の打ち切り（CPU はそれぞれ 0.4 秒・2.7 秒＝計算が重かったのではなく待ち）、
  EXTENSION-BEFORE-A1 は runner.py の構文誤りで Lean 未起動、PAIRWISE-CONNECTIVITY-A1・PHYSICAL-REPLAY-A1・PHYSICAL-REPLAY-COST-A1・PHYSICAL-STEP-HEIGHT-A1 は rc=1 で sorryAx あり＝エラー回復の印字）。
  失敗した 8 本はどれも後継（A2 や別単位）がある。ただし COMPLETION-GUARD-A1 の版（8ee7a5ae…）は再試行されず、GUARD-ASSEMBLY-A1 が**別のソース**（940caebf…、CompletionMap と CostMap を組む形）で同名定理を緑にした。
- **再検査: 緑 25・赤 0・未再検査 0**（Lean の rc=0 全 25 単位）。Q-CONVERSE（Python）は同じ check.py を同じ入力で再実行して RESULT が一致（独立実装ではない）。
- CAPACITY-COMMON-EDGES-A1 の「sorryAx なし」は依存（EnumerationCorrectness）の印字であって候補の結果ではない。

### 変異注入（主定理の主張をずらして落ちるか）

| id | 単位 | 定理 | 変異 | 結果 |
|---|---|---|---|---|
| M1 | SIGNATURE-COVER-CARD | `signature_number_le_cover_card` | `signatureNumber D ≤ card I` → `signatureNumber D + 1 ≤ card I` | 落ちた（44 行 Type mismatch） |
| M2 | SIGNATURE-COVER-UNIQUE | `minimum_cover_language_bijection` | 仮定 `card I = signatureNumber D` → `= signatureNumber D + 1` | 落ちた（98 行 `change` 失敗。⚠ 意味の矛盾でなく証明の字面で落ちた） |
| M3 | PHYSICAL-CAPACITY | `step_true_iff_false_and_capacity` | 容量 `≤ 5` → `≤ 4` | 落ちた（grind 失敗） |
| M4 | CAPACITY-EDGE-I | `capacity_common_edge` | `idxOf 1 < idxOf 8` → `idxOf 8 < idxOf 1` | 落ちた |
| M5 | PHYSICAL-REPLAY-COST-A2 | `successful_replayWithCost_cost` | 初期高さ `board.length` → `board.length + 1` | 落ちた（rewrite 失敗） |

5/5 が落ちた。詳細は `recheck/mutations.json`。

## 原稿（v15）の主張との対応

- **v15 の Lean の節（§「Leanによる検証範囲と未接続部分」の 1〜5）が根拠にしているのは 11-12〜14 の別の Lean 単位**
  （321 依存の再構築、多重度 binomial、先行制約、mixture 証明書。showa の `ペブリング_*_Lean検証報告_*.md` 群）で、**この 34 単位ではない**。
  それらは今回の対象外で、手元では再検査していない（⚠ 検査していません）。
- この 34 単位が機械で閉じたのは、v15 に**まだ書かれていない**次の一般定理とその部品（下の「層の提案」）:
  厳密累積費用層 L_a の通常半順序による最小正確被覆数＝実現された異符号署名の数、最小被覆の言語族は一意。
  仮定は有限 ID・Nodup の全体語・台つき狭義半順序 Q・**重み列だけに依存するガード**・厳密な費用値。
  （紙の証明と独立レビューは `pebbling-signature-reviewed-0900.zip`。Lean の言明は `SignatureCoverCore.lean` の `LayerSpec`・`ExactLayer`・`IsExactCover`。）
- 物理模型の部品（1 手の高さ ±1・再生の高さと費用の累積・容量つき再生の成功と接頭辞の上限の同値・I/M の局所の共通辺 1<8 と 2<10・容量なしの物理的反例）も緑。
- **条件つき**: この一般定理を原稿の固定イベントのペブリング族（I・M・大域の k）に当てはめること。
  義務 1〜6 のうち 2・3 は部品が緑、1 は半分、4〜6 は未（NOTES.md）。v15 の 472/2916・200/584 は有限検査の数で Lean の定理ではない。
  また一般定理は**厳密費用の層**の定理で、v15 の全言語の 6·14^{k−1} の被覆数を置き換えるものではない。
- 新規性: 隣接交換の連結性は既知（Chan–Pak survey §12.3 の folklore、Naatz 2000）。署名による被覆数の定理は poset cover・trace/heap 理論との比較が未了（さくらい自身が「未確立」）。

## 層の提案（台帳は触っていない）

- 候補 id（仮）: `R-fixedpeb-01`「厳密累積費用層の最小正確 poset 被覆数＝異符号署名数・最小被覆の言語族の一意性（重み列ガード・有限 ID）」
  → **層 1 の候補**（一般の言明が Lean で緑・手元で再ビルドと変異 5/5）。根拠: `PEBBLING-SIGNATURE-COVER-CARD-20261115-A1/SignatureCoverCard.lean`
  の `signature_cover_attains_minimum`、`PEBBLING-SIGNATURE-COVER-UNIQUE-20261115-A1/SignatureCoverUnique.lean` の `minimum_cover_language_bijection`・`minimum_cover_unique_fiber`、
  本記録の `recheck/rebuild_results.json`。⚠ ただし「原稿の主張と言明が一致するもの」に限る規則では、**v15 にこの定理は書かれていない**ので、
  原稿の主張としての層 1 にはならない。原稿に入れるなら NOTES.md の「書いてよい言い方」の範囲で。
- `R-fixedpeb-02`「この定理の原稿の I/M・大域 k への適用」→ **層 3（保留）**。理由: 義務 1・4・5・6 が未。物理側の部品（`successful_step_length_increment`・
  `successful_replayWithCost_cost`・`replay_true_iff_false_and_postUpper`・`capacity_common_edge`）は緑だが、Q 言語との同値が無い。
- `R-fixedpeb-03`「容量なし局所言語＝小さい DAG R_X の線形拡張（I 1200・M 15840）」→ 層 3（紙の証明・未レビュー・未形式化。数は Python 検査と一致）。
- 原稿 v15 の主定理（区間直積・400·584^{k−1}・6·14^{k−1}・16k+9 等）の層は 11-12〜14 の Lean 単位を再検査してから決める（今回は判定しない）。

## 入れなかったもの

`.olean`・`.tar.gz`・`.zip`・PDF・dvi は写していない。sha256 と元のパスは `recheck/excluded_sha256.txt`（223 件）。
`.lean` のソースも**写していない**（正本の置き場が決まっていないため。sha256 は `recheck/lean_sources_sha256.txt`、165 件。
showa の写しの平置き `.lean` 21 本はすべて paper-audits の SHA256SUMS と一致）。

## 再現

```
python3 -I recheck/rebuild.py <空の作業ディレクトリ>          # 25 単位を再ビルド（約 10 分・<host> で 1 コンパイル最大 46 秒）
python3 -I recheck/mutate.py <上の作業ディレクトリの絶対パス> <変異用の絶対パス>
python3 -I recheck/table.py <作業ディレクトリ>/results.json  # 上の表
```

---

## 追記 2026-11-16 後半（艦長2の依頼 1〜3 と I 節の振り分け）

### 1. 既存 4 原稿との重なり → `OVERLAP.md`

v15 の結論は 4 本（erasure_pebbling、spooky_pebbling、exact_reversible_pebbling、同 autoresearch）のどれにも無い。
重なるのはモデルの定義（erasure_pebbling の Def. erasure budget）だけ。**独立の原稿として扱う**。

### 2. v15 の Lean の節が根拠にしている 11-12〜14 の単位の再検査 → `recheck12/`

- 入力: showa の写しにある 10 個の束（sha は `recheck12/input_bundles_sha256.txt`）。321 依存の束、mixture、先行制約の被覆、成分の多重度、先行ガード、
  v11_followup（最短値・DFA・語数・被覆）、11-14 の residual・recurrence・remaining-perm・board-perm。
  同名のモジュールは束どうしで全部同じバイト列だった（`attempt1` を除く）。v15 の主張に対応する定理 39 本（31 モジュール）の import 閉包は 455 モジュール。
- 手順は 11-15 の単位と同じ。ソースから 1 つのディレクトリに順にビルドした。各モジュールは systemd-run（MemoryMax 2G、RuntimeMaxSec 120、
  CPUWeight idle）の下で `lean -j1 -M1800` を使った。
- **結果: 255 モジュールが緑、4 モジュールが上限内で通らず、196 モジュールはその下流で未着手。sorryAx は 0。**
  - 通らなかった 4 本: `InitialSegment`、`MiddleSegment`、`IStates` はカーネルの「excessive memory consumption」（大きな `decide`）。
    `MUpperVerified` は壁時計 120 秒の打ち切り（<host> の負荷 43、さくらいの記録では 74 秒）。
    さくらいの元の再構築は 6GiB・180 秒・`-s4096`（`-M` なし）で通している。2G のまま上限を上げる再試行は auto mode に拒否されたので、していない。
  - そのため v15 の Lean の節 1〜5 などに対応する定理 39 本のうち、**再検査で緑は 2 本だけ**。`PricedRecurrence.C_affine`（[propext, Quot.sound]）と
    `ActualCheckpoint.actual_checkpoint_board`（標準 3 公理）。変異（`+1` を外す、盤面の頂点をずらす）は 2/2 で落ちた。
  - 被覆 $6\cdot14^{k-1}$、語数、成分、DFA、最短値 $16k+9$、先行制約、mixture、residual や recurrence の各定理は**未再検査**。
    依存先が上限内で通らないため（⚠ 検査していません）。
- 次の手: 艦隊のホストで、さくらいの元の上限（6GiB・180 秒）で同じスクリプトを回す。上限を変えるかは人の判断。

### 3. 一般の署名被覆定理を入れた v16 → `v16/`（README.md）と `v16_vs_v15.diff`

### I 節の振り分けで回ってきた 24 件（`../EI-triage-20261116/triage.tsv`）

- `CostGuard.lean`、`ShiftComposition.lean`、`PhysicalPrefixGuard-candidate-20261115.lean` は、上の表で緑の単位のソースと同じバイト列（sha 一致）。
- `CommonRelationCounterexamples-candidate`（097af8f9…）と `ExtensionEnumerationComplete-candidate`（49ae4f6e…）は、さくらい自身が未コンパイルとしている候補。今回もコンパイルしていない。
- `MaximalAlternation.lean`（b71cfe62…）: 最大費用層の語が交互の語に一致すること。`LocalCounts` に依存し、手元の 2G 上限では依存先が通らないため未検査。
- `NOVELTY_BOUNDARY.md`: 累積費用の尺度（Blocki–Zhou、Blocki–Holman–Lee）と poset cover（Yuan–Wang）は既知、という整理。OVERLAP.md と v16 の引用に使った。
- `ペブリング_期待累積石数と分散_v3初実運用_20261115.md`: 全語一様のときの累積石数の期待値と分散。紙と Python だけで、Lean は無い。記録のみ。
- `*-reservation.json` 11 件と `RESERVATION.json`: 作業の予約票。中身の検査はしていない。

### 2'. 艦隊での再検査（2026-11-16 09:15〜09:35、op）→ `recheck12/fleet-op-20261116/`

- 仕様は idea-factory の `jobs.d/SMF-LEANGATE3-fixedpeb.json`（commit 421b7bc、ユーザー指示「再検査する」）。gate.py は SMF-LEANGATE2 と同じもの（sha ebf678b2…）。
  4 ホスト（op・sf1・sf2・s3）の `~/work/smf-leangate-1116/fixedpeb/` に同じ束を置き、dispatch は op に配った。
  上限は作者の元の値で、MemoryMax 6G、`--trust=0 -j 1 -s4096`、1 モジュール 600 秒。
- **VERDICT: GREEN。** 各段の結果は次のとおり。
  - S0 sha 照合 0 件の不一致、G0 禁止語 0。
  - B1: 455/455 を白紙からコンパイル（1183 秒）。B2 の鮮度は 455/455。
  - A1: 監査ファイルで 37 本の公理がすべて標準 3 つ以内。
  - A3: B1 の全ログの `#print axioms` 1,043 行がすべて標準 3 つ以内。sorryAx は 0。
  - C1: 対照は A1 と一致。
- A1 に入れなかった `Recurrence` と `RemainingPerm` の 5 本（`BoardPerm` と同名のため）は、それぞれの B1 ログで標準 3 つ以内（`B1_selected_axioms.txt`）。
- **主張の定理 39 本: 緑 39・赤 0・未 0。**
- 変異 5 本はすべてコンパイルで落ちた。
  - M6: C_affine の `+1` を外す。
  - M7: checkpoint の盤面の頂点をずらす。
  - MC: 被覆の成分数 6·14^r → 5·14^r。
  - MW: 語数 400·584^r → 401·584^r。
  - MO: 最短長 16k+9 → 16k+8。
- <host>（2G・120 秒）で通らなかった 4 本（InitialSegment・MiddleSegment・IStates・MUpperVerified）は、6G では通った。原因は上限であって、ソースではない。
- 層の提案（台帳は触っていない）: v15 の Lean の節 1〜5 の定理は「定理証明系が別の機械で白紙から緑」になった。
  層 1 にしてよいかは、原稿の各主張と Lean の言明が一致するかを読んでから決める。v15 の本文自身も、そこにずれ（漸化式の経路と物理の直接証明、occurrence-labelled 語、DFA の範囲）があると書いている。
