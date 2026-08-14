# 検証状態台帳（本プロジェクトの正本）

運用ルール（`~/.claude` の記憶 `proof-status-lean-bar` / periodic-tm の台帳に準拠）:
**「確定」を名乗れるのは層1のみ。**

**昇格の権限**（2026-08-11 にユーザーが Claude へ委任）:
- **層1 への昇格は Claude が行ってよい。ただし 5 検査を全部通したときのみ**——
  ① `sorry`/`axiom` なし ② ルートモジュールが import している ③ `lake build` 通過
  ④ `#print axioms` が標準 3 つ ⑤ **変異注入で落ち、復元で通る**。
  **5 つとも機械的に確かめられるので委任が成立する。**
  ⚠ ③だけでは足りない（`Replayed` はキャッシュ。⑤ が無いと緑が本物か分からない）
- **層2 への昇格も Claude が行ってよいが、判断が入るので根拠と
  「まだ確かめていないこと」を必ず併記する**（AI 導出の紙証明は場合分けの網羅漏れが起きる。
  2026-08-10〜11 に Claude の主張が 5 回反証された実績がある）

- **層1 [Lean済]** — sorry ゼロで `lake build` が通る機械証明。確定。
- **層2 [紙証明]** — Claude が書き下し検算した紙の証明。未機械化。
  指導教員のレビューか機械化を経るまで断定しない。
- **層3 [骨格]** — 証明の骨格＋機械実験の裏付けのみ。実質は予想。

⚠️ **有界事例の機械検証（`decide`・DRAT 証明書・全数探索）は層1ではない。**
「$n\le20$ で検証済み」は「すべての $n$ で証明済み」ではない。混同しやすいので明記する。

| 結果 | 内容 | 層 | 根拠 |
|---|---|---|---|
| 定理 A 上界 | $e^*$ 回の消去で $2n-1$ に到達する構成 | **2 [紙証明]** | `data/exp03_results.md` §A。CP-SAT で $n\le160$ の事例を確認 |
| 定理 A 下界 | $e<e^*$ では $2n-1$ 不可能 | **2 [紙証明]** | 同 §A.2（剛性→消去数=$\tau$の上昇数）。**$n\le20$ は DRAT 証明書つき**（`data/sat_lower_bound_findings.md`）だが一般証明は未機械化 |
| 定理 B1 | $\reach(p,e)\ge(e+2)2^{p-2}$ | **1 [Lean済]** | **B2 の系**。`(PebbleDP.reach_eq p e hp).1` で導出でき、`#print axioms` は標準 3 つのみ（2026-08-11 に確認）。**紙証明（旧 §B.1）を経由する必要が無くなった** |
| 命題（LTV 比較） | LTV Procedure A は $(e+1)2^{p-2}$ | **3 [機械実験]** | `data/exp03_ltv_compare.csv` 全45行が検証器通過、30 点で比較 |
| **定理 B2** | 到達則の等号 $\reach(p,e)=(e+2)2^{p-2}$（鎖・$p\ge2$） | **1 [Lean済]** | `lean/Revgarbage/PebbleB1.lean` の `reach_eq`。**両方向**（構成側と上界側）を含む。`Reach`（`PebbleModel.lean`）は忠実な遷移系（`erase` が消去を 1 消費）。**5 検査を 2026-08-11 に実施**: `sorry`/`axiom` なし・ルートが import・`lake build` 通過・`#print axioms` = `[propext, Classical.choice, Quot.sound]`・**変異注入（`(e+2)→(e+3)`）で 11 件のエラーが出て復元で通る** |
| $M^*=2A-1$ | 手数 = 2×配置回数 − 1 | **2 [紙証明]**（かつ**既知**） | Knill 1995 の表に既出（`docs/60_novelty_audit.md` §1） |
| $M^*\ge2n-1$ | 絶対下界 | **既知** | Knill 1995 Observation 2.2(i)。**自分の補題として書かない** |
| 候補10 の下界特徴づけ | 自由ガベージ模型の下界はタイト | **1 [Lean済]** | `lean/Revgarbage/Garbage.lean`（`sorry` なし・`native_decide` なし）。ただし**既知**（Maslov–Dueck 2004 Thm 1） |
| 候補10 パリティ障害 | 奇置換は arity $<N$ のゲートでは作れない | **1 [Lean済]** | 同 `odd_perm_not_in_closure` |
| 候補1 $M^*(T_5)=155$ | 完全二分木の厳密値 | **2 [証明書つき・無条件]** | **下界を独立な 2 経路で証明**（2026-08-12）。いずれも `drat-trim` が **`s VERIFIED`**、RAT 補題 0（純粋 RUP）:<br>① 対称性破りあり: 探索 4h06m・DRAT 16GB・核 2245万/1億5563万・6.73億 resolution・検証 5842 秒<br>② **対称性破りなし**: 探索 9h36m・DRAT 14GB・核 2805万/1億5051万・8.30億 resolution・検証 7267 秒<br>**②により「対称性破りが健全」という前提が不要になった。** 核の中身が異なる（2245万 vs 2805万）＝同じ結論に異なる証明で到達している。上界は既存の 155 手スケジュール。⚠ **有界事例なので層1 ではない**（すべての $h$ で証明したわけではない）。証明書は `oci:/tmp/t5_k154_{sym,plain}.drat`（**14.9GB / 16.2GB**）、CNF と検証ログは `exact-rev-complexity-autoresearch/autoresearch/results/`。**2026-08-14 に同一性を確認**: ローカルの CNF の sha256 が oci 側の証明対象と完全一致（`t5_k154_sym.cnf` = `d158099243…`、`t5_k154_plain.cnf` = `1ba8f7ce38…`）。**したがってローカルの CNF から再現可能**（再探索 4h06m/9h36m ＋ 検証 5842/7267 秒）。⚠ **DRAT 本体は oci の `/tmp` にあり、OCI の試用は 2026-09-07 まで**。回収するなら 31GB の転送が要る。しない場合は「CNF ＋ 検証ログから再現可能」を根拠とする |
| 候補1 $M^*(T_6)=429$ | 完全二分木の厳密値 | **3 [機械実験]** | 三層照合（素朴BFS ⟷ ビットマスク双方向 ⟷ Aut商）で一致。**証明書は未取得** |
| 候補1 $p_{\min}(T_7)=10$ | 下界=全数探索・上界=構成証書 | **3 [機械実験]** | Královič Lem 4.3 の予測とも一致 |
| **1 回組 $\le\min(p,N)$**（したがって $M^*\ge4N-2\min(p,N)-1$） | どの合法 clean スケジュールでも 1 回だけ置かれる頂点は $\min(p,N)$ 個以下 | **2 [紙証明]** | `data/families/findings.md` §3.22。$n\le6$ の DAG 全数 46,287 行・全スケジュールで裏取り済み。**⚠️ 証明が約 10 行と短く folklore の可能性が高い**（§3.22 末尾） |
| **Q2 $T_\parallel(G)=2\,\mathrm{depth}(G)-1$** | 並列可逆ペブリングの時間最適値（一般の有限 DAG） | **1 [Lean済]** | `lean/Revgarbage/ParPebbleWindow.lean` の `par_time_exact_dag_two_sided`。⚠ **2026-08-14 訂正**: 旧 `time_lower_bound_path` は無限前方路を要求し有限 DAG で充足不能だった（`paD_no_infinite_path` で機械証明）。有限区間版に直して両側が閉じた。**新規性は主張しない**（逐次版 $M^*\ge2n-1$ は Knill 1995 Obs 2.2(i) で既知。並列版は BHL Def.1 から初等的） |
| **Q2 時間窓・余裕ゼロ** | 時間最適なら各頂点は窓 $[k+1,T-k-1]$ にしか居ず、**両端では必ず居る** | **1 [Lean済]** | 同ファイル `time_window_seg` / `no_slack` / 深さ関数版 `time_window_dep` / `present_at_dep` / `present_at_end_dep`。5 検査全通過（変異注入 6/6・4/4）。⚠ **Královič 2004 Lemma 3.2（時間最適な計算は対称）と同方向**なので言及必須（`docs/34`） |
| **Q2 構造補題 L1 / L2** | 初出時刻 $=i+1$・最終存在時刻 $=2n-2-i$（厳密な等式） | **1 [Lean済]** | `chain_window` / `chain_sink_stays`。**L1 が未証明だったため `--fix-first` の UNSAT を使えなかった制限が外れた** |
| **Q2 交互構成・持ち上げ** | `layered` より真に良い構成／深さの鎖のペブリングは DAG に持ち上がる | **1 [Lean済]** | `alt_par_time_exact` / `lift_par_time`。持ち上げにより **CP-SAT のレベル一様最適値がすべて証明つき上界**になった。⚠ **最適性は主張しない**（ピラミッド $h\ge9$・鎖 $n\ge6$ で最適でない） |
| **Q2 ピラミッド $p_{\min}(h)$（$h \le 5$）** | $3, 6, 8, 10$ | **1 [Lean済]** | `lean/Revgarbage/ParPebbleWindow.lean` の `pyr3_pmin_eq_six` / `pyr4_pmin_eq_eight` / `pyr5_pmin_eq_ten`。**下界（`peak_lower_right`）と上界（`alt_par_time_exact`）が一致**するので両側とも機械証明。`sorry` 0・公理は標準・変異注入 4/4 検出。⚠ **定義がピラミッドであること自体も `paPk_is_pyramid` で固定**（親を 1 本落とす変異が素通りしたため追加）。$h \ge 6$ は下界 $2h$ と上界が離れるので未決 |
| **Q2 完全二分木の $p_{\min}$** | $p_{\min} = 3\cdot2^{D-1}+1$（深さ $D \ge 2$） | **1 [Lean済]** | `lean/Revgarbage/ParPebbleWindow.lean` の `tree_pmin_exact`。**上界（`alt` のピーク）も下界（層 0・層 1 の大きさ）も一般の $D$ で機械証明**し、値が一致する。`sorry` 0・公理は標準・変異注入で $D\ge3 \to D\ge2$ の改良を発見（$D\ge1$ では落ちる＝境界）。⭐**空間最適は $\Theta(D)$（Královič 2004 Thm 4.9）なので、時間最適性の空間コストは指数的**。文献（Knill/Královič/Komarath+/Chan）は一貫して「空間を固定して時間を問う」側で、我々は反対側（`docs/34` §9–12） |
| **Q2 ピークの下界** | 時刻 $k+2$ に深さ $k, k+1$ の頂点が全部同時に居る。$p \ge \max_k(\#\{dep=k\}+\#\{dep=k+1\})$ | **1 [Lean済]** | `peak_lower_left` / `peak_lower_card` / `peak_lower_right`。`present_at_dep` の系で証明は 10 行。ピラミッドに当てると $p_{\min}(h) \ge 2h$ で $h \le 5$ ではタイト。$h=18$ で 36 対 58（0.62 倍）。⚠ 鎖には効かない |
| **Q2 ピラミッドの $p_{\min}$** | $3,6,8,10,13,16,20,23,26,29,32,37,41,45,49,54,58$（$h=2..18$） | **2 [証明書つき]**（$h=3..18$） | 下界（$p_{\min}-1$ が UNSAT）を **素の CNF** で DRAT 化し `drat-trim` が全点 `s VERIFIED`（`data/q2_pyr_cert_log.csv`。$h=18$ で **2.7GB**・検証 5581 秒）。⚠ **`--window` ではなく素の CNF で取った**——証明書が Lean の定理を CNF 生成器へ写した正しさに依存しないようにするため。上界は SAT の解を独立検査（`scripts/q2_profile.py`）。**OEIS 該当なし**。⚠ 予測 $4h-15$ は $h=17$ で外れた（6 回目） |
| **Q2 逐次では自明** | 逐次模型では $n^*(p)=p$ | **既知** | **Knill 1995 Observation 2.2(i)**（`F(n,S)=2n-1$ for $S\ge n$）。**自分の補題として書かない。** CP-SAT で 14 点再現（`tests/test_sequential_trivial.py`） |
| 候補2 $n\le7$ 全数 | 非同型類 138,101、$R-P$ 最大 3 | **3 [機械実験]** | OEIS A350415 と一致（実装の裏取り） |

## 運用

- **新しい定理を書いたら本表に1行追加する。**
- 論文ドラフトの定理見出しにも層ラベルを書く
  （`~/dev/overleaf/2026_erasure_pebbling/main.tex` §7 に対応表がある）。
- 層2・層3 に「証明済み」「確定」という断定調を使わない。
