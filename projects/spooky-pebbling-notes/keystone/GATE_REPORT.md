# 機械証明検査報告 — spooky-pebbling-lean `bb4a144`（Keystone.lean / Envelope.lean）

検査日: 2026-10-06 / 検査官: 著者と独立 / 作業場: `<作業場>` = `/work/tmp/claude-1000/-work-a-dev-notes-spooky-pebbling-keystone/4342765b-0a09-4037-a2cf-1fcad5d32ef7/scratchpad/gate/`

## 総合判定: **緑（通過）**

クリーンな写し（`git archive bb4a144`、Mathlib はハードリンクで借用・再ビルドなし）で 35 モジュールが Built（Replayed 0）・rc=0・警告 0（対象 2 ファイル）。
27 定理すべてが標準 3 公理の範囲、穴 0、独自の変異 25 本は全て拒否・無変異の対照 2 本は通過。言明は看板と一致（食い違い・空虚真は見つからなかった）。
ただし下の「走らせなかった検査」（`KSSModel.lean` ほか）は未確認。

## 5 点ゲート

| # | ゲート | 判定 | 根拠（コマンド → 結果） |
|---|---|---|---|
| 1 | ビルド | ✅ | `systemd-run --user --scope -p MemoryMax=24G -p MemorySwapMax=0 -p CPUQuota=400% nice -n 19 timeout 3000 lake build SpookyPebblingExtra > build.log`（`runbuild.sh`）→ **rc=0**、`Build completed successfully (8593 jobs)`、18:53:15→18:57:23（4 分 8 秒）。OOM/SIGTERM の形跡なし（rc=0、`killed|terminated|error` の grep 0 件）。事前の乾式 `lake build --no-build Mathlib` → `All targets up-to-date (8557 jobs)` rc=0。ビルドログの番号は 8558〜8592 が欠番なしで連続＝Mathlib 側 8557 ジョブは 1 件も走っていない |
| 2 | 公理 | ✅ | 2 ファイルの `theorem` 27 本（Keystone 11 + Envelope 16）全件に `#print axioms`（`probe/axioms.lean`、rc=0）。**20 本が `[propext, Classical.choice, Quot.sound]`、7 本が `[propext, Quot.sound]`**。`sorryAx` / `Lean.ofReduceBool` / `Lean.trustCompiler` / 独自 axiom は **0 件**。`example`（Keystone 1・Envelope 2）は theorem に直して確認（`ex_K` `ex_E1` `ex_E2`）→ 同じく標準公理内 |
| 3 | sorry/axiom/admit 計数 | ✅ | コメント除去（ブロック・行コメント）して数える `probe/count_holes.py`（自己検査で合成した `sorry`/`axiom`/`native_decide` を検出することを確認済み）。**リポ全 51 ファイルで `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`/`implemented_by`/`opaque`/`partial`/`extern`/`ofReduceBool` = 0 件**、2 ファイルでも 0 件。生の字面 grep（コメント含む）も `sorry|admit|axiom` 0 件。`decide` は 3 か所のみ（Keystone 261, 263 / Envelope 296）で、いずれも `theta 3 ≤ …`・`B4 3 ≤ 9` 等の**具体値の小さい判定**で、有界全数検査ではない。`set_option`・`macro`・`syntax`・`attribute`・`local` も 0 件。**警告: 対象 2 ファイル 0 件**（ビルドログの `warning:` は全 12 件で、本体の `Decomp`4・`PlaceI`2・`Sweep`2・`Ghost`/`Lemma48`/`Lemma48Gen`/`Reghost` 各 1。いずれも linter（simpa→simp、未使用 simp 引数）で、既存モジュール） |
| 4 | 変異注入 | ✅ | 27 本（対照 2 + 変異 25）を `lake env lean --root=<dir> -o <dir>/X.olean`（作業場の単発コピー `mut/<ID>/`、リポ内に置かず）。**対照 K0・E0: rc=0・error 0・olean 生成＝通過。変異: Keystone 10 本・Envelope 15 本 = 25 本すべて rc=1・error≥1・olean 無し＝拒否。通ってしまった変異 0、未確定 0。** 種別: stmt-range 6 / stmt-constant 9 / stmt-direction 1 / def 3 / proof-critical 3 / example-value 3。各置換は「元の文字列がちょうど 1 回」を assert して生成（空振り変異なし）。個別一覧は下 |
| 5 | 成果物の実在 | ✅ | 写しの `.lake/build/lib/lean/` に olean 35 個（SpookyPebbling 30 + Extra 4 + ルート 1）。**すべて BUILD_START より新しい**（`find -newer`: 35 個全部、古いもの 0）。Keystone.olean 18:57:01 (918,416 B)、Envelope.olean 18:57:16 (1,086,168 B)。ログ: **Built 35（✔28 + ⚠7）・Replayed 0**・パッケージ（Mathlib/Batteries/Aesop/Qq/Plausible/ProofWidgets…）のモジュール Built 0 件。元リポの olean とは別 inode（47193636 vs 82859627）。元リポの `.lake/packages` に BUILD_START 以降に更新されたファイルは 0（ハードリンク越しの書換えなし） |

### 変異の一覧（全件 拒否。エラー位置が変異箇所かその直接の使用箇所であることを確認）

| ID | 変異 | 判定（rc / error 数 / 最初の error 位置） |
|---|---|---|
| K0 | 無変異（対照） | **PASSED** rc=0 / 0 / olean 有 |
| K1 | `TUG_le_TUP_of_theta_le` の仮定 `θ(s) ≤ n` → `θ(s) ≤ n+1`（n=θ(s)−1 で偽） | REJECTED rc=1 / 4 / L194（base の omega）ほか |
| K2 | `TUP_eq_TUG_add_one_of_theta_le` の結論を反転 | REJECTED / 3 / L223 |
| K3 | `delta_sign` の δ=−1 側 `+1`→`+2` | REJECTED / 1 / L243 |
| K4 | `TUG_succ_le_TUP_add_five` の `5`→`4`（docstring は「改善できない」） | REJECTED / 1 / L183（s≤q 枝の omega） |
| K5 | 補題2 の増分 `4`→`5` | REJECTED / 1 / L167 |
| K6 | 場合B で補題2（4 手得）を補題1（2 手得）に差し替え | REJECTED / 1 / L209（最後の omega） |
| K7 | `delta_sign` の δ=+1 側 `n+1 ≤ θ(s)` → `n ≤ θ(s)` | REJECTED / 1 / L248 |
| K8 | 補題1 の仮定 `1 ≤ m` → `0 ≤ m` | REJECTED / 2 / L101, L115 |
| K9 | `example` の値 38/39 → 37/38 | REJECTED / 1 / L264 |
| K10 | `TUP_split_attained` の仮定 `2 ≤ n` → `1 ≤ n` | REJECTED / 1 / L80 |
| E0 | 無変異（対照） | **PASSED** rc=0 / 0 / olean 有 |
| E1 | `brk 1 s = s` → `s+1` | REJECTED / 1 / L89（brk_one） |
| E2 | `brk` の漸化式に `+1` | REJECTED / 3 / L102（brk_step）, 288, 293 |
| E3 | `TUP_le_envelope` の区間右端を `+1` 緩める | REJECTED / 4 / L146, L165（補題内部）ほか |
| E4 | `TUP_le_envelope` の傾き `2(m+1)`→`2(m+2)` | REJECTED / 1 / L202（※下記の注） |
| E5 | `TUP_upper_envelope` の「ある m で等号」を `+1` ずらす | REJECTED / 1 / L222 |
| E6 | `exists_brk_interval` の `1 ≤ n` → `0 ≤ n` | REJECTED / 2 / L211, L221 |
| E7 | `bb_succ_eq_add_brk` の `2·brk`→`brk` | REJECTED / 5 / L245 ほか |
| E8 | `brk_eq_half_diff` の `/2`→`/3` | REJECTED / 1 / L268 |
| E9 | `brk_two` の `+1` を落とす | REJECTED / 1 / L275 |
| E10 | `TUP_le_envelope` の場合分け境界を `+1` | REJECTED / 1 / L185 |
| E11 | `brk (t+2) 2 = t+2` → `t+3` | REJECTED / 3 / L92, 288, 293 |
| E12 | `example` の `brk 4 3 = 12` → `13` | REJECTED / 1 / L288 |
| E13 | `example` の `T_UP(24,3)`/`T_UG` を入れ替え（δ 符号反転） | REJECTED / 1 / L297 |
| E14 | `TUG_eq_envelope` の δ=−1 側 `+1`→`+2` | REJECTED / 1 / L233 |
| E15 | `TUP_eq_envelope` の下界の指数 `m+1`→`m` | REJECTED / 2 / L203 |

注（E4）: 傾きを 2(m+2) に緩めた `TUP_le_envelope` は**局所では真で弱い命題**なので補題自体は通り、下流の `TUP_eq_envelope`（等号の組み立て）で落ちる。補題単体の強さは下流定理が担保している、という読み。

検査器自体の健全性（偽命題プローブ）: リポ外 `probe/false1/F.lean`（`example : (1:Nat) = 2 := rfl`、`brk 2 3 = 6`、`TUP 9 3 = 40`）→ **rc=1・error 3・olean 無し**。`probe/sorry1/S.lean`（`theorem … := by sorry`）→ **rc=0・olean 有・`warning: declaration uses 'sorry'`**。つまり rc=0 だけでは sorry を除外できないので、ゲート 2・3（`#print axioms` ＋ 警告 0 ＋ 字面計数）を併用して除外した。

## 言明が看板どおりか（読んだもの）

読んだ: `Keystone.lean`・`Envelope.lean` 全文、`Defs.lean` 全文（`Cell`/`Op`/`legal`/`ok`/`Run`/`UPLengths`/`UGLengths`/`TUP`/`TUG`）、`Theta.lean` の `theta`、`Slope6Exact.lean` の `B4`、`SlopeTight.lean` の `bb`・`bb_step`・`bb_base`・`TUP_ge_slope_tight`、`Breakpoints.lean`。`#check` で主要定理の型を出力（`probe/axioms.out`, `probe/defs_probe.out`）。

1. **看板 1（Keystone）は型どおり。** `TUP_eq_TUG_add_one_of_theta_le : 2 ≤ s → theta s ≤ n → TUP n s = TUG n s + 1`（n に上限なし）。`keystone_delta : 3 ≤ s → B4 s ≤ n → TUP n s = TUG n s + 1`。`theta_lt_B4`（`θ(s)+1 ≤ B4 s`, s≥2）で一般形の特殊例になっている。
2. **`delta_sign` は n ≥ 1・s ≥ 2 の全域を尽くす。** 型は `(n + 1 ≤ theta s → TUG = TUP + 1) ∧ (theta s ≤ n → TUP = TUG + 1)`。2 つの前件 `n < θ(s)` と `θ(s) ≤ n` は自然数で排反かつ網羅（`n+1 ≤ θ(s)` の否定が `θ(s) ≤ n`）なので隙間なし。証明側も `n < s`（`TUG_eq_of_le'`/`TUP_eq_of_le'`）と `s ≤ n`（`TUG_eq_TUP_add_one`）で尽くしている。変異 K7（境界を 1 つずらすと矛盾）で右端が効いていることも確認。
3. **空虚真・`sInf ∅ = 0` 退化は無い。** `TUP`/`TUG` は `sInf (UPLengths n s)`／`sInf (UGLengths n s)`。`UPLengths_nonempty : 2 ≤ s → 1 ≤ n → (UPLengths n s).Nonempty`（`UGLengths_nonempty` も）が定理として在り、`TUP_eq_TUG_add_one_of_theta_le` はこれを実際に使って `TUG_TUP_diff_one` を呼んでいる。空集合なら `0 = 0 + 1` が偽になるので等式は空虚に真にならない。Envelope の `TUP + bb = 2(m+1)n` も空なら成立しない。仮定は矛盾していない（独立 BFS と 30 点一致、下記）。
4. **`brk` は docstring の漸化式どおり。** 定義: `brk 0 _ = 1`、`brk 1 s = s`、`brk (t+2) {0,1,2} = t+2`、`brk (t+2) (s+3) = brk (t+1) (s+3) + brk (t+2) (s+2)`。`(t+2, s+3)` → `m+1=t+2, s'+1=s+3`（`s'=s+2 ≥ 2`）で `brk (m+1) (s'+1) = brk m (s'+1) + brk (m+1) s'` と一致。**漸化式から手計算した期待値 14 点を `simp [brk]` で証明し全て一致**: `brk 0 7=1, brk 1 5=5, brk 3 2=3, brk 7 2=7, brk 2 3=5, brk 3 3=8, brk 2 4=9, brk 3 4=17, brk 2 5=14, brk 3 5=31, brk 4 4=29, brk 4 3=12, brk 3 6=51, brk 4 6=111`。`#eval` の 8×8 表で `brk 2 s`＝2,5,9,14,20,27,35,44（＝θ(s)−1）、`brk 3 s`＝3,8,17,31,51,…（＝B4(s)−1。B4(5)=32, B4(6)=52 を `decide` で確認）。`s ∈ {0,1}` の `brk (t+2) _ = t+2` は使われない値（docstring 通り）で、定理は全て `2 ≤ s` を仮定（`brk_zero`/`brk_one` だけ無条件だが定義どおり真）。
5. **`TUP_upper_envelope` の「ある m で等号・すべての m で ≥」は max を正しく表す。** 型: `(∃ m, 1 ≤ m ∧ TUP n s + bb m s = 2*m*n) ∧ ∀ m, 1 ≤ m → 2*m*n ≤ TUP n s + bb m s`。足し算の形なので自然数の切り捨ては入らず、ℤ 上で `TUP = max_{m≥1}(2mn − β_m(s))`（m は非有界、最大値は存在量化で達成）と同値。
6. **区間の被覆に隙間なし。** `exists_brk_interval : 2 ≤ s → 1 ≤ n → ∃ m, brk m s ≤ n ∧ n ≤ brk (m+1) s`。n=0 は覆えない（`brk 0 s = 1`）ことを変異 E6 で確認。`TUP_eq_envelope` は `2 ≤ s`・両端の仮定のみで、`n ≥ 1` は `brk_pos` から導いている（`h1 : brk m s ≤ n` と `brk m s ≥ 1`）。
7. **区間は点で重なりうるが矛盾しない。** `brk 1 2 = brk 2 2 = 2`（s=2）で m=0,1,2 が n=2 を同時に含む。3 つの m で `2(m+1)n − β_{m+1}(2)` はいずれも 3 で、BFS の `T_UP(2,2)=3` と一致。`exists_brk_interval` は m の一意性を主張していない（正しい）。
8. **`brk_eq_half_diff`**: `(bb (m+1) s - bb m s) / 2 = brk m s`。ℕ の切り捨て減算・切り捨て除算を使うが、真の等式は別定理 `bb_succ_eq_add_brk : bb (m+1) s = bb m s + 2 * brk m s`（m≥1, s≥2）で与えられ、かつ `brk ≥ 1` なので切り捨てで 0 に落ちて偶然成り立つ余地もない。意味は崩れていない。
9. **docstring の数値主張を独立値で確認**: 「T_UP(s,s) − T_UP(s−1,s) = 2」（s=3: 5−3）、「定数 5 は改善できない（s≤q で差ちょうど 5）」（s=4,q=4: T_UG(5,4)=12, T_UP(4,4)=7 → 5。q=2: 6−3=3）、「場合B は実際に起きる」（s=3→4: n=θ(4)=10, k=5, q=θ(3)−1=5 で `T_UP(10,4)+1 = 34 = 2·5 + T_UP(5,4) + T_UP(5,3) = 10+11+13`）。いずれも BFS の値で成立。

**見つからなかった食い違い・弱点**: 上記の読みでは、暗黙の強い仮定・空虚真・切り捨てによる意味のずれ・範囲の隙間はいずれも見つからなかった。気づきとして次の 2 点だけ（誤りではない）:
- 看板の「区間 `brk m s ≤ n ≤ brk (m+1) s` 上の厳密値」の傾き番号は **`m` でなく `m+1`**（`2(m+1)n − β_{m+1}(s)`）。docstring には書いてあるが、読み手が `β_m` と取り違えやすい（m=0 が傾き 2）。
- 本体 `SpookyPebbling` の 7 モジュールに linter warning が 12 件（既存。対象 2 ファイルは 0）。

## 独立の数値照合（余力分・実施）

`probe/xcheck.py`（Lean の定義を字面から再実装した `bb`/`brk`/`theta` で予言値を作り、`kss.py` の BFS（`<local>/dev/notes/spooky-pebbling/kss.py`。`python3 -I -B` で読むだけ・pyc も書かない）と照合）。**30 点で不一致 0**: s=2: n=2..10（`n²+n−3`、δ=−1 は n≥3）、s=3: n=2..12（T_UP: 2n−1 / 4n−7 / 6n−17 / 8n−33（n=8..12 で 63 まで）、δ の反転は n=6 から）、s=4: n=2..11（4n−9 / 6n−27、δ の反転は n=θ(4)=10）。特に **s=3, n=9,10,11 で T_UP=39,47,55（=8n−33）、T_UG=38,46,54（δ=−1）**。区間 m の式 `T_UP + β_{m+1} = 2(m+1)n` も区間に入る全 m で成立。
限界: BFS が届く範囲は s=3 で n≤12、s=4 で n≤11 まで。**B4(4)=18 以降・傾き ≥10 の区間（s=3 では n=12 の 8/10 の境界 1 点のみ）は BFS で突き合わせていない**。そこは Lean の機械証明のみが根拠。

## 走らなかった検査・未確定（⚠ 検査していません）

- ⚠ **`SpookyPebbling/KSSModel.lean` と `SpookyPebbling/Tests.lean` は今回のビルドに含まれていない**（`SpookyPebblingExtra` の依存閉包の外。`SpookyPebbling` 32 ファイル中 olean が出たのは 30）。特に `KSSModel.lean` は「Lean の `TUP`/`TUG`（`ghost` が `ready` でも打てる広い意味論）が KSS の量に等しい」（`TUP_eq_K` 等）を担う。**この同値は本検査で再確認していない**。ただし、Keystone/Envelope の言明は Lean の `TUP`/`TUG`（`Defs.lean`）そのものについて真であることは検査済みで、`kss.py` の BFS（QL 規則）との 30 点の一致が間接的な傍証。
- ⚠ `SpookyTree/*` は検査していません（対象外・ビルドせず）。
- ⚠ `lake build` の他ターゲット（`SpookyPebbling` 全体、`SpookyTree`）は未実施。
- ⚠ 元リポジトリのビルド済み olean は使っていない・検査していない（写しだけを検査）。
- 検査対象はコミット `bb4a144`（`git archive`）。元リポの HEAD は検査中に `c987d63` に進んだ（`bb4a144..HEAD` は README の 1 コミット。`SpookyPebbling/`・`SpookyPebblingExtra.lean`・2 ファイルは bb4a144 と差分なし。写しの blob hash も一致: Keystone `29b95293…`、Envelope `395d587c…`）。
- 未確定（rc 124/137/143 等）は 0 件。

## 自分の誤り（型別）

- **名前の推測**: 乾式確認で実在しないモジュール名 `Mathlib.Data.Nat.Defs` を指定し rc=1（`probe` ではなく `dryrun.log`）。パッケージの状態の判定には使っておらず、`lake build --no-build Mathlib` でやり直して rc=0（`All targets up-to-date (8557 jobs)`）を判定に使った。
- **シェルの癖**: ① zsh で未一致の glob（`ls .../*.olean`）がエラーを出した（olean が無いことの確認＝期待どおりの出力。判定には影響なし）。② `grep … | head; echo "(grep rc=$?)"` は `head` の rc を印字する形になっていた（意味のない値）。結論は「出力が空＝一致 0 件」に基づき、rc は使っていない。
- **hook の警告**: 「手元で CPU 律速の仕事を起動」の警告が出た。理由（チームリードの明示指示・写しの検証には 7.7GB のハードリンク済み Mathlib が手元にしか無い・nice 19・CPUQuota 4 コア/2 コア・計 4 分ほど）を書いて続行。
- `| head` は表示専用でのみ使い、判定は全てファイルに受けた出力で行った。

## 主な成果物（`<作業場>` 配下）

`build.log` / `build_start.txt` / `build_end.txt` / `probe/axioms.lean`+`.out` / `probe/defs_probe.lean`+`.out` / `probe/count_holes.py` / `probe/xcheck.py`+`.out` / `probe/false1/` `probe/sorry1/` / `make_mutants.py` / `run_mutants.sh` / `mut/MANIFEST.tsv` / `mut/results.tsv` / `mut/<ID>/{X.lean,out.log,rc.txt}`
元リポジトリへの変更: なし（`git status` は開始時と同一、`.lake/packages`・`.lake/build` に検査中の更新なし、`.lean` を `<local>/dev` 配下に置いていない）。リポ内に置いたプローブはないので削除対象もなし。
