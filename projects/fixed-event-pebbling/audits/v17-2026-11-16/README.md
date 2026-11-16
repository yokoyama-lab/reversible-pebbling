# v17 の検査記録（2026-11-16）

原稿 v17 の変更点は `../../paper/README.md` の v17 節。ここは検査の入力と出力だけを置く。

## 局所因子の費用層（Python の有限検査）

- `layers.py`: `lean/general-2026-11-15/CAPACITY-EDGE-I-A1/LocalCertificate.lean`（sha256 ab087e2a…a9cf を検査）の I・M のイベント表から、
  容量つきの局所言語・容量なしの合法語・共通先行関係 Q_X^∩・LE(Q_X^∩) を独立に列挙し、費用層ごとの語数と署名の数を数える。
  さらに各署名 σ について closure(Q_X^∩ ∪ σ) の線形拡張がその署名の類に一致するかを確かめる（上界の直接の証明書）。
- 実行: `python3 -I audits/v17-2026-11-16/layers.py lean/general-2026-11-15/CAPACITY-EDGE-I-A1/LocalCertificate.lean audits/v17-2026-11-16/layers.json`（1 秒未満）。
  出力 `layers.json`（Q の辺を含む）と `layers.txt`。
- 結果: I は LE(Q)=472、容量つき 200、容量なし 1,200、LE(Q)⊆容量なし、ガード後＝容量つき。費用 27〜45 の 10 層で署名の数の和 138。
  M は 2,916・584・15,840、同じく成立。費用 34〜54 の 11 層で和 352。全署名で closure の線形拡張＝類。
- 変異 2 本（scratchpad で実施）: closure から Q を外す → `all_P_sigma_exact` が I・M とも False。初期高さを 5 にする → ガード後≠容量つき（I・M とも）。
  どちらも検出された。
- `q_converse_rerun_RESULT.json`: v15 の有限検査 `<local>/paper-audits/PEBBLING-Q-CONVERSE-20261115-A1/check.py`（sha256 f5807b66…8d25）を同じ入力で再実行した結果。
  472/2,916・200/584・1,200/15,840 が一致（同じコードの再実行で、独立実装は `layers.py` の側）。

## Lean のソースの注記の修正

- `lean/general-2026-11-15/` の 32 ファイルで、冒頭コメントの「Uncompiled …」を「compiled (green 2026-11-15/16)」に直した。コメントの 1 行内の置換だけで、
  言明・証明・行数は不変（`git diff` の 32 行の差はすべてコメント行）。
- 変更前後の sha256: `lean_sha256_before.txt`・`lean_sha256_after.txt`（129 ファイル）、差分 `lean_sha256_changed.tsv`（前 後 パス、32 行）。
  各単位の `SHA256SUMS` も新しい sha に更新した。
- 再ビルド: `rebuild_repo.py`（`../sakurai-2026-11-15/recheck/rebuild.py` の入力元を repo の `lean/general-2026-11-15/` に替えただけ）。
  変えたファイルを含む 14 単位を、各コンパイル `systemd-run --user --wait --pipe -p MemoryMax=2G -p MemorySwapMax=0 -p RuntimeMaxSec=120`、
  Lean 4.31.0 の `lean -j1 -M1800` で白紙から再ビルドした（<host>）。結果は `rebuild_results.json`。
- 結果: **14 単位すべて緑**（全段 rc=0・.olean 生成・`error` 行なし・`sorryAx` なし・SHA256SUMS と一致）。主たるモジュールで印字された 49 定理の公理は
  標準 3 つ（propext・Classical.choice・Quot.sound）以内。1 コンパイルの最長は 26.6 秒（LocalCertificate）。Mathlib の 2 単位（COVER-CARD・COVER-UNIQUE）は
  `reversible-pebbling-lean-lowend/.lake/packages/mathlib`（fabf563a）の既存ビルドを読むだけで使った。

## v18 で足した検査（同じ `layers.py` を拡張・再実行）

- 下界の証明書: 各層の署名の代表の全対（I 1,308 対・M 8,565 対）について、両語の共通順序を守り層の外にある語を 1 つずつ保存し
  （`layers.json` の `I_lower_bound_certificates`・`M_lower_bound_certificates`）、置換であること・共通順序を守ること・層の外であることを検査。全対で成立。
- Q_X^∩ の推移閉包の辺のうち容量を外した合法語のどれかで破れるもの: I 9/28 本（R_2<P_9 を含む）、M 17/42 本。
- k=1: L_1 = F0 I F1 T1 の語の大域の費用＝局所の費用＋19+18、T の 2 語の費用は 13・15。L_1 の 11 層の署名の数は I の層と T の層の畳み込みに一致。
  一般の k は確かめていない。
