# drive-drafts — Google Drive 上にあった Lean の草稿と束

2026-11-16 に Google Drive から集めた。**このリポジトリのどのコミットにも同じ内容（git blob が一致するもの）が
無い `.lean` だけ**を置いている（27 本）。それ以外の `.lean`（約 270 本）は `projects/fixed-event-pebbling/` などの
履歴に既に入っていたので除いた。そのため `fleet-20261115/` の各束は**依存ファイルが欠けた部分集合**であり、
単独ではビルドできない。依存は `projects/fixed-event-pebbling/` の履歴から補うこと。

**検証状態は一様ではない。ここにあるものを「証明済み」と書かないこと。**

| ディレクトリ | 出所 | 日付（出所側の記録） | 状態 |
|---|---|---|---|
| `gdrive-root/<zip名>/` | Drive 直下の `erasure_lean_*.zip`・`pebbling_*.zip`・`消去ペブリング_*.zip` などを展開したもの | 2026-11-11〜12（Drive の更新日時） | **大半が未コンパイル**。`*_UNCOMPILED.lean`・`incomplete/` は名前のとおり。`ErasurePebbling_*.lean`・`Saturation.lean`・`Compression.lean` は本体の旧版の写しで、正本は `ErasurePebbling/` |
| `showa-import-sakurai/` | `~/dev/proj/showa-import/drive/さくらい/` の単体 `.lean` | 2026-11-15 | 下の束の主ファイルの写し（ピン留め版を含む） |
| `fleet-20261115/<束名>/` | 同じ場所の `PEBBLING-*-20261115-*.tar.gz`（34 個）を展開したもの。`.olean` 等の生成物は除いた | 2026-11-15〜16 | 束ごとに `RESULT.json`・`SCOPE.txt`・`SHA256SUMS`・ログがある。**コンパイルされた束だが、このリポジトリの CI では再検査していない** |

- 束どうしで同じファイルが重複している（各束がその時点の依存一式を同梱しているため）。
- `fleet-20261115/` の内容は、固定事象ペブリング（`projects/fixed-event-pebbling/`）の
  general-2026-11-15 系の作業の途中経過と思われる。ただし対応関係は確認していない。
