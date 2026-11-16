# Lean ソース

Lean 4.31.0（`lean-toolchain`）。`.olean` は入れていない。どちらの系統も lake プロジェクトではなく、
平置きのソースを `lean` で 1 本ずつ依存順にコンパイルする形のまま置いている（作者の検査の形を変えないため）。

## `general-2026-11-15/` — 一般定理の単位（25 単位・のべ 129 ファイル）

2026-11-15 の監査で rc=0 だった Lean の 25 単位と、それぞれの import 閉包。
単位ごとに 1 ディレクトリで、同じモジュールが複数の単位に重複して入っている（バイト列は同じ。`SHA256SUMS` で照合できる）。

- `TARGETS`: その単位の主たるモジュール。`SHA256SUMS` の並びが依存順（先に書いたものから順にコンパイルする）。
- 主定理: `SIGNATURE-COVER-CARD-A1/SignatureCoverCard.lean` の `signature_cover_attains_minimum`、
  `SIGNATURE-COVER-UNIQUE-A1/SignatureCoverUnique.lean` の `minimum_cover_language_bijection`・`minimum_cover_unique_fiber`。
  定義（`LayerSpec`・`ExactLayer`・`IsExactCover`）は `SignatureCoverCore.lean`。
- Mathlib が要るのは `SIGNATURE-COVER-CARD-A1` と `SIGNATURE-COVER-UNIQUE-A1` だけ。
  Mathlib は `v4.31.0` タグ（commit `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`）でビルドしたものを使う。
- `COST-GUARD-A1/CostGuard-20261115.lean` はモジュール名 `CostGuard` として出力する（`-o CostGuard.olean`）。

ビルドの例（1 単位。作業用の空ディレクトリに写してから）:

```sh
cd <単位の写し>
sha256sum -c SHA256SUMS
for f in $(awk '{print $2}' SHA256SUMS); do
  m=${f%.lean}; [ "$m" = CostGuard-20261115 ] && m=CostGuard
  LEAN_PATH=.:<Mathlib の各パッケージの .lake/build/lib/lean> lean -j1 -o "$m.olean" "$f" || break
done
```

各ファイル末尾の `#print axioms` の印字が標準 3 公理（`propext`・`Classical.choice`・`Quot.sound`）以内で、
`sorryAx` が出ないことを確かめる。監査時の上限は 1 コンパイルあたりメモリ 2GiB・120 秒（`-M1800`）で、全単位が通った。

## `v15-main-2026-11-12to14/` — v15 の主定理（455 モジュール）

原稿 v15 の「Lean による検証範囲」の節が根拠にする 11-12〜14 の Lean。主張の定理 39 本の import 閉包 455 モジュール。
`src/` の全ファイルの sha256 は `SHA256SUMS` にあり、白紙ビルドの検査に使った束と一致する。

- `job.json`: ビルド順（`modules`）、公理を監査する定理名（`audit_names`）、言明の変異 5 本（`mutations`）。
- `gate.py`・`run.sh`: 検査器。段は S0（sha256 照合）・L0（Lean の版）・G0（禁止語）・B1（`--trust=0 -j 1 -s4096` で全モジュールを白紙コンパイル）・
  B2（.olean の鮮度）・A1／A3（`#print axioms` が標準 3 公理以内）・M（変異がコンパイルで落ちる）・C1（対照）。
- 実行: このディレクトリを写した先で `bash run.sh`（Lean 4.31.0 の `lean` を環境変数 `LEAN_BIN` で指す。未設定なら elan の既定の場所の v4.31.0 を使う）。`build/` に .olean、`logs/` にログ、`DONE` に判定を書く。
- 必要な資源: 一部のモジュール（`InitialSegment`・`MiddleSegment`・`IStates` の大きな `decide`、`MUpperVerified`）は
  メモリ 2GiB では通らない。1 モジュールあたりメモリ 6GiB・600 秒で全 455 本が通った（約 20 分）。

検査の結果（2026-11-16）は `../audits/sakurai-2026-11-15/recheck12/fleet-op-20261116/` にある。
