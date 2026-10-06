# keystone/ — 鎖の δ の符号と上包絡（状態ファイル）

## 現在の状態（handoff: 2026-10-07）

**実行中のジョブは無い。** このセッション（spooky-keystone）の作業は完了している。
鎖の厳密値について残っていた 2 点（δ の符号の全域、傾き 8 以降の上界）は、どちらも Lean で緑になった。

### 読む順

1. `keystone/RESULT.md` — 結論、定理名と仮定、検査、まだやっていないこと、誤りの一覧。前半が要石、後半の「追記」が上包絡と独立検査
2. `keystone/GATE_REPORT.md` — 独立検査（`proof-gatekeeper`）の全文
3. Lean の 2 ファイルの冒頭コメント — `spooky-pebbling-lean/SpookyPebblingExtra/Keystone.lean` と `Envelope.lean`（証明の筋が書いてある）
4. `keystone/REQUEST.md` — 最初の依頼文（依頼元 winf-spooky のファイル。未追跡のまま）

### 確定している事実（再確認不要。根拠は RESULT.md と GATE_REPORT.md）

- リポジトリ: `<local>/dev/github.com/yokoyama-lab/spooky-pebbling-lean`（private。Lean 4.31.0、mathlib v4.31.0）
- **要石**: コミット `ce36c6e`、`SpookyPebblingExtra/Keystone.lean`。
  `s ≥ 2`、`θ(s) ≤ n` で `T_UP(n,s) = T_UG(n,s) + 1`（`n` に上限なし）。
  定理は `TUP_eq_TUG_add_one_of_theta_le`、`keystone`、`keystone_delta`、`delta_sign`
- **上包絡**: コミット `bb4a144`、`SpookyPebblingExtra/Envelope.lean`。
  すべての `n ≥ 1`、`s ≥ 2` で `T_UP(n,s) = max_m (2mn − β_m(s))`。
  定理は `TUP_eq_envelope`、`exists_brk_interval`、`TUP_upper_envelope`、`TUG_eq_envelope`、`bb_succ_eq_add_brk`、`brk_two`、`brk_three`
- 折れ目の定義 `brk`: `brk 0 s = 1`、`brk 1 s = s`、`brk m 2 = m`（`m ≥ 2`）、`brk (m+1) (s+1) = brk m (s+1) + brk (m+1) s`。
  **Lean の区間 `[brk m s, brk (m+1) s]` は傾き `2(m+1)`**（添字が 1 つずれる）
- 2 コミットとも `origin/main` に入っている（push は別セッションが行った。このセッションは push していない）
- 検査: 定理 27 本とも標準 3 公理の範囲内、sorry 0、2 ファイルの警告 0。
  自分の変異は要石 13 本・上包絡 13 本をすべて検出。独立検査はクリーンな写しで Built 35・Replayed 0、独自の変異 25 本をすべて拒否
- 原稿 P1（`<local>/dev/overleaf/2026-WiNF/P1-spooky-exact.tex`）は、担当セッション winf-spooky が要石と上包絡を反映済み（2026-10-07 に grep で確認。補遺 3 モジュールとして引いている）
- `bb4a144` は最初の依頼文の範囲を超えている（除外されていた問題、触ってよいファイルの外）。ユーザーの「つづき」の指示で進めた。戻すなら `git revert bb4a144`

### まだ古いままの記述（このセッションは編集していない）

- Lean リポジトリの `README.md` — 層表に Keystone・Envelope が無く、「残っているもの（層3）」に (a) が残っている
- この README（`notes/spooky-pebbling/README.md`）の「残るのは層3: (a) 傾き 8 以降の上界」— 冒頭に案内を 1 か所足しただけで、本文は直していない
- `theorem_slope_tight.py` の「緊密性（構成側）は未証明で層2 のまま」、`spooky-pebbling-lean/docs/request_slope8_upper.md`（目標は達成済み）
- 研究台帳（topic-mining の registry）— 依頼文が触ることを禁じていた。Q7 の (a) の状態は動いている

### 次の作業候補

1. **台帳と README 2 本の更新**。層の判定と台帳は担当セッションかユーザーが行う。台帳は同時に 1 セッションだけが触る決まり
2. **系を 2 本足す**（未着手・未検証の見込み）: `T_P` の閉じた式（KSS Thm 4.11 `TP_eq_TUG_succ` で `T_UG` から移す）と、KSS の意味論への移送（`KSSModel.lean` の `TUP_eq_K`・`TUG_eq_K`）。独立検査は `KSSModel.lean` を見ていない
3. **IEICE 向け原稿**（`notes/spooky-pebbling/paper-ieice/`）で「任意の傾きで緊密」を無条件の定理として書けるようになった。主定理の書き直し

### 注意（踏むと痛い）

- **`~/dev` 配下に単発の `.lean` を置かない。** Stop フックの証明ゲートが「成果物が無い」と止める。変異や反証は
  `mutate_*.py` が出力ディレクトリ（リポジトリの外）に書き出す。検査は `lake env lean --root=<dir> -o <olean> <file>`
- **検査エージェントを起動する前に、作業ディレクトリをこの `keystone/` か `~/dev` に戻す。** Lean リポジトリを作業ディレクトリにしたまま
  起動すると「このフォルダを信頼するか」で止まる（2026-10-06 に踏んだ。確認は代わりに押さない）
- `mutate_keystone.py`・`mutate_envelope.py` の引数（出力先）は必ずリポジトリの外。約 2〜4 分、1 コア
- Lean リポジトリは他セッションが同じ作業ツリーで動いている。`docs/` に他人の未コミット変更がある。コミットは名指しで
- `~/dev` にはリモートが無い。この `keystone/` の成果物は `~/dev` のコミット `f664bea`、`aeb9acd`、`25cae37` と、この状態ファイルのコミットにある

### 再現

```sh
cd ~/dev/notes/spooky-pebbling/keystone
python3 check_keystone.py 14 1000      # 要石の数値検定（約 2 秒）
python3 check_envelope.py 14 1000      # 上包絡の数値検定（約 2 秒）
python3 mutate_keystone.py /path/outside/the/repo
python3 mutate_envelope.py /path/outside/the/repo
```
