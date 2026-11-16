# ブロック標準形 MIP の結果（2026-08-10）— **MIP は interval-CP-SAT に勝った。勝因はソルバではなく定式化**

`data/mip_findings.md` §4 の宿題（「MIP 一般が弱いのか、interval 定式化が MIP に
不利なのか」）への回答。実装は `scripts/mip_stage.py`（Gurobi / SCIP）・
`scripts/cpsat_stage.py`（同一定式化の CP-SAT 版・統制用）、テストは
`tests/test_mip_stage.py`（23 件 pass）。

## 0. 要旨（4 行）

1. **put 添字の「ブロック標準形」定式化**に書き直したら、Gurobi は 8 ケース全部を
   最悪 3.0 秒で解いた（旧王者 interval-CP-SAT は 7/8、chain(12) e=0 は 60 秒で未解決）。
2. しかし同じ定式化を CP-SAT に載せると 0.19 秒。**定式化を統制すると CP-SAT が再び最速**。
3. つまり mip_findings §4 の答えは「**interval 定式化が MIP に不利だった**」。ソルバは
   どれも悪くなかった。定式化の変更だけで SCIP まで 5/8 → 8/8 になった。
4. ただし境界域（n = 2^{p-1}）では、最良の定式化でも MIP は閉じない（LP 緩和が
   超線形下界を構造的に見えない。§5）。**境界域は stage-CP-SAT、線形領域は
   interval-CP-SAT、の使い分けが結論**（§6）。

## 1. ブロック標準形（定式化の核となる正規化補題）

clean 可逆ペブリングの初期状態は空なので、スケジュールは必ず put で始まる。
したがって任意のスケジュールは **「put 1 回 + その後の take 集合」のブロック列**に
一意に分割できる。さらに:

> **補題（ブロック内 take の順序正規化）** ブロック内の take はトポロジカル降順に
> 並べ替えてよい。put 直後がブロック内の状態の極大点で以後は縮むだけなので、
> take の可逆性は「put 直後の状態に先行点が揃っているか」だけで決まり、
> 並べ替えで不可逆消去の回数が増えることはない。

これで**ブロック内の順序変数が消える**。ステージ k のモデルは

| 変数 | 意味 |
|---|---|
| $x_{v,k}$ | ブロック k 終了時に v がペブル済み |
| $\mathrm{put}_{v,k}, \mathrm{tk}_{v,k}$ | ブロック k で v を put / take |
| $\mathrm{act}_k$ | ブロック k が有効（有効ブロックはちょうど 1 put） |

制約は全て {0, ±1, p−2} 係数の**純 0/1 線形**: 遷移 $x_{v,k} = x_{v,k-1} +
\mathrm{put}_{v,k} - \mathrm{tk}_{v,k}$、ピーク $\sum_v x_{v,k-1} \le p-1$（有効時）、
可用性 $\mathrm{put}_{v,k} \le x_{u,k-1}$、可逆性 $\mathrm{tk}_{v,k} \le x_{u,k-1} +
\mathrm{put}_{u,k}$（e>0 では違反を irr 変数で計上し $\sum \mathrm{irr} \le e$）、
「各祖先は少なくとも 1 回 put」（e に依らず有効）。目的は $A = \sum_k \mathrm{act}_k$ の
最小化で、保存則から take 総数 = A−1、**$M = 2A-1$**（`cpsat_interval_findings.md` §1 の
恒等式そのまま）。

### interval 版 MIP との構造比較（chain(12), p=5, e=0 の実測）

| | 変数 | 制約 | **indicator** | ホライズン |
|---|---:|---:|---:|---|
| interval（C=3） | 4,257 | 7,063 | **5,748** | 時刻 0..2nC+2 |
| **stage（K=24）** | **900** | **2,063** | **0** | put 番号 1..K |

interval 版の敗因だったイベント点方式の $O((nC)^2)$ 二値と indicator の山が消え、
LP 緩和が空でなくなる。さらに:

- **1 頂点あたりの区間数上限 C が不要**。feasibility は K について単調
  （トポ最小の非 free 頂点の put-take 対を先頭に足すと A→A+1）なので、
  **K_max ≥ A\* でありさえすれば OPTIMAL の返り値は真の A\***。interval 版の
  「cap を増やして改善が止まるまで」ループも cap_tight の疑いも要らない。
- 目標頂点の最終区間の take 免除（interval 版で e=0 が INFEASIBLE になるバグを
  生んだ例外処理）が構造的に不要（最終ペブルは単に take されないだけ）。
- 支配カット $\mathrm{tk}_{v,k} + \mathrm{put}_{v,k+1} \le 1$（ブロック k で取った
  頂点を直後のブロックの put にしない。両者を消してブロックを併合すれば 2 手縮む
  ことから、どの最適解もこれを満たす）。既定で入れているが、Gurobi には
  逆効果の場合がある（§5 の消し込み）。

### mip_findings §4 の 3 案との対応

- **Checkmate 型の時間展開**: 本定式化はその洗練版。時刻（2A−1 幅）ではなく
  **put 番号（A 幅）で展開**するのが要点で、ホライズン半減・idle 対称性の消滅・
  「1 ステージ 1 put」による順序対称性の圧縮を同時に得る。危惧された $O(n^2)$
  変数は残るが（chain(12) で 900 個）、indicator ゼロなので presolve が効く。
- **フロー型**: 遷移制約 $x_{v,k} = x_{v,k-1} + \mathrm{put} - \mathrm{tk}$ が
  そのまま頂点ごとの流量保存であり、フロー構造は本定式化に内蔵されている。
- **区間グラフのクリーク不等式**: 不要になった。重なり変数 $o_{j,k}$ 自体を
  消したため、強化すべき対象が存在しない。ピークは各ステージの
  基数制約（クリーク不等式の役割を果たす）に置き換わった。

## 2. 検証（この一致確認が通った範囲でのみ値を使う）

| 層 | 内容 | 結果 |
|---|---|---|
| 既知真値 | 指揮者提供の 8 値（chain 4/6/8/12 × e=0,1） | 3 バックエンドとも全一致 |
| BFS 全面照合 | 鎖 n≤8 (p, p±1, e≤2)・木・ピラミッド・決定的乱数 DAG、**143 ケース × 3 ソルバ**（`scripts/mip_stage_verify.py`） | **誤値 0 件**（未完 4 件は SCIP が到達不能インスタンスの INFEASIBLE 証明を 60 秒で出せなかったもの。誤値ではない） |
| 独立 DP | cbt(5)（素朴 BFS は状態 3.4M で重い）を treedp（商グラフ双方向 BFS）の M\*=155 と照合 | stage-CP-SAT の暫定解 155 が DP 真値と一致（最適性証明は 600 秒で未完・bound 69）。pyr(5) は 0.8 秒で OPTIMAL=47（BFS と一致） |
| 奇数性 | M = 2A−1 は構成上奇数（偶数が出たら AssertionError で停止） | 違反なし |
| 回帰テスト | `tests/test_mip_stage.py`（K 自動昇格・到達不能検出・hint 不変性を含む） | 23 件 pass |

## 3. 統一ベンチマーク（8 ケース、60 秒/solve、<host> 同日同負荷、workers=8）

秒は auto ループ（interval は cap 昇格、stage は K 昇格）込みの end-to-end。
interval-Gurobi / interval-SCIP は同日の `scripts/mip_interval.py` 再実行値
（公表値 `data/mip_findings.md` §2 より今日は負荷でやや遅く、chain(12) e=0 は
正しい暫定解 39 を出しながら証明未完 = FEASIBLE）。

| case | BFS | interval-CPSAT | interval-Gurobi | interval-SCIP | **stage-CPSAT** | **stage-Gurobi** | **stage-SCIP** |
|---|---:|---:|---:|---:|---:|---:|---:|
| chain(4) e=0 | 9 | 0.06 | 0.16 | 0.24 | 0.01 | 0.03 | 0.04 |
| chain(4) e=1 | 7 | 0.05 | 0.08 | 0.14 | 0.02 | 0.01 | 0.02 |
| chain(6) e=0 | 15 | 0.17 | 1.05 | 3.53 | 0.02 | 0.03 | 0.07 |
| chain(6) e=1 | 11 | 0.06 | 0.24 | 0.23 | 0.02 | 0.02 | 0.06 |
| chain(8) e=0 | 25 | 20.50 | 75.28 | 120† | **0.09** | **0.24** | **0.77** |
| chain(8) e=1 | 17 | 0.21 | 0.80 | 1.61 | 0.04 | 0.07 | 0.11 |
| chain(12) e=0 | 39 | UNKNOWN†† | 121† | 121† | **0.19** | **3.01** | **48.99** |
| chain(12) e=1 | 29 | 21.78 | 86.87 | 120† | 0.17 | 2.75 | 46.02 |
| 解けた数 | | 7/8 | 7/8 | 5/8 | **8/8** | **8/8** | **8/8** |

† FEASIBLE（正しい暫定解はあるが最適性未証明）。†† UNKNOWN（解なし）。

- **chain(12) e=0（3 ソルバ×interval が全滅していたケース）を stage は 3 ソルバとも解いた**。
  CP-SAT 0.19 秒、Gurobi 3.0 秒、SCIP 49.0 秒。
- interval → stage の同一ソルバ比較: CP-SAT で chain(8) e=0 が 20.5 → 0.09 秒（**228 倍**）、
  Gurobi で 75.3 → 0.24 秒（**314 倍**）。**ソルバを替えるより定式化を替える方が 2 桁効く**。

## 4. 境界域スケーリング（n = 2^{p-1} 近傍、60 秒/solve、K_start=4n 一律）

`scripts/mip_stage_scale.py`。値は moves（M\*）、秒は end-to-end。
FEASIBLE = 暫定解あり最適性未証明（暫定値は常に真値以上で、健全性違反は 1 件もない）。

| case | e | BFS | stage-CPSAT | stage-Gurobi | stage-SCIP |
|---|---:|---:|---|---|---|
| chain(16) p=5 | 0 | 71 | **71 (2.4s)** | UNKNOWN, bd20 | UNKNOWN, bd17 |
| chain(16) p=5 | 1 | 45 | **45 (3.8s)** | UNKNOWN, bd17 | UNKNOWN, bd17 |
| chain(20) p=6 | 0 | 77 | **77 (9.7s)** | UNKNOWN, bd23 | UNKNOWN, bd26 |
| chain(20) p=6 | 1 | 57 | **57 (44.5s)** | UNKNOWN, bd21 | UNKNOWN, bd20 |
| chain(24) p=6 | 0 | 109 | FEAS 113, bd49 | UNKNOWN, bd26 | UNKNOWN, bd24 |
| chain(24) p=6 | 1 | 73 | FEAS 73, bd32 | UNKNOWN, bd24 | UNKNOWN, bd24 |
| chain(28) p=6 | 0 | 145 | FEAS 205, bd55 | UNKNOWN, bd30 | UNKNOWN, bd28 |
| chain(28) p=6 | 1 | 91 | FEAS 103, bd36 | UNKNOWN, bd29 | UNKNOWN, bd28 |
| chain(32) p=6 | 0 | 193 | FEAS 237, bd59 | UNKNOWN, bd34 | UNKNOWN, bd32 |
| chain(32) p=6 | 1 | 115 | UNKNOWN | UNKNOWN, bd32 | UNKNOWN, bd32 |
| chain(16) p=6 | 0 | 51 | **51 (1.4s)** | **51 (43.3s)** | UNKNOWN, bd18 |
| chain(16) p=6 | 1 | 41 | **41 (3.3s)** | FEAS 41, bd18 | UNKNOWN, bd16 |
| chain(24) p=7 | 0 | 85 | **85 (26.5s)** | UNKNOWN, bd26 | UNKNOWN, bd24 |
| chain(24) p=7 | 1 | 69 | FEAS 71, bd31 | UNKNOWN, bd24 | UNKNOWN, bd24 |
| cbt(3) p=5 | 0 | 17 | 17 (0.06s) | 17 (0.18s) | 17 (0.34s) |
| cbt(4) p=6 | 0 | 53 | **53 (1.2s)** | UNKNOWN, bd15 | UNKNOWN, bd15 |
| pyr(3) p=5 | 0 | 13 | 13 (0.04s) | 13 (0.07s) | 13 (0.17s) |
| pyr(4) p=6 | 0 | 27 | 27 (0.16s) | 27 (1.2s) | 27 (6.7s) |

- **stage-CP-SAT の 60 秒フロンティア（e=0, pmin 境界）は chain(20)**。600 秒に延ばすと
  **chain(24) が 97 秒（OPTIMAL 109）・chain(24) e=1 が 286 秒（73）・chain(28) が
  396 秒（145）で閉じ、いずれも BFS と一致**。chain(32) は 600 秒でも未解決
  （暫定 213 / bound 74、真値 193）。木・ピラミッドは cbt(4)・pyr(4) まで数秒。
- **Gurobi は境界から 1 離れると解けるようになる**: chain(16) は p=5（A\*=36）で全滅だが
  p=6（A\*=26）なら 43.3 秒で OPTIMAL。再計算の雪崩（超線形性）が消えると MIP でも
  届く。「境界域の超線形性こそが MIP に不利」の直接証拠。
- interval-CP-SAT は chain(16) p=5 e=0・chain(20) p=6 e=0 とも 60 秒 UNKNOWN
  （同日実測）。**e=0 境界域のフロンティアを stage 定式化が動かした**:
  `cpsat_interval_findings.md` §4 の「e=0 側は interval-CP-SAT の圏外（BFS のみ）」が
  stage-CP-SAT で覆り、chain(16) は 2.4 秒・chain(20) は 9.7 秒で OPTIMAL。
- **BFS との公平な比較**: 今夜測った範囲（p ≤ 7）では、鎖の生値の計算は BFS が
  依然最速（chain(28) p=6 を 9 秒。状態数 $\sum_{k\le p}\binom{n+1}{k}$ が小さいため）。
  stage の価値は (1) ソルバ系ツールの中でのフロンティアを 2 桁動かしたこと、
  (2) 列挙に依らない**下界証明**（下記）、(3) 専用 DP の無い一般 DAG への適用性、に
  ある。BFS が RAM で死ぬ領域（p ≥ 8 の長鎖）は stage-CP-SAT にもまだ届いていない。

### 下界の機械証明という新能力

K_max = A\*−1 の INFEASIBLE 証明は「put 回数 ≤ A\*−1 のスケジュールが存在しない」
ことの機械証明（= BFS に依存しない下界検証。`cpsat_interval_findings.md` §5.1 の宿題）。

| 命題 | CP-SAT | Gurobi |
|---|---:|---:|
| chain(12) p=5: A\* > 19 | **0.19 秒** | 2.70 秒 |
| chain(16) p=5: A\* > 35 | **0.42 秒** | 123.2 秒 |

両ソルバとも証明には成功する（Gurobi は最適化だと 60 秒で bound 20 止まりだが、
判定問題に落とせば 123 秒で閉じる）。

### e 曲面の一括計算デモ（§8-1 の最初の一歩・全点検証済み）

chain(20) p=6 の $M^*(e)$ を e=0..8 で stage-CP-SAT により計算し、
`landauer_profile`（BFS）と**全 9 点一致**: 77, 57, 47, 39, 39, …（$e^*=3$ で
飽和値 $2n-1=39$ に到達）。単調非増加・奇数性も成立。超線形領域の 3 点が
13.7 / 61.2 / 47.1 秒、飽和後は約 1 秒。証明書を外部検証可能にする VIPR 経路は、
この環境の SCIP（pyscipopt 6.2.1 同梱・`~/.venvs/urtm` とも）が exact solve
無効ビルドのため今は使えない（`enableExactSolving` → 「SCIP was compiled without
exact solve support」）。SCIP 自体が境界域の INFEASIBLE を時間内に出せていない
（§2 の未完 4 件）ので、再ビルドは速度問題が解けてからでよい。

## 5. なぜ境界域で MIP は閉じないのか（診断）

一言で言えば **LP 緩和が超線形下界を構造的に持てない**。

- **LP 緩和の実測**（`scripts/mip_stage_diag2.py`。gurobipy の遅延 update に注意:
  `relax()` の前に `update()` が要る。初版 diag の LP=0.00 はこのバグ）:
  chain(12): LP = **12.00 = n ちょうど**（真値 A\*=20）。chain(16): LP = 16.00（真値 36）。
  「各祖先 ≥1 put」がそのまま張り付き、再ペブリングの雪崩は LP に映らない。
- **証明つきの鎖専用カット**を足しても足りない。補題「非 target の v の put が 1 回なら、
  v の唯一の区間内で v+1..n の生涯が完結する必要があり、そこは p−1 個で clean に
  解けなければならない。ゆえに n−v > reach(p−1) = 2^{p-2} なら put(v) ≥ 2」
  （reach は既知の定理）で、LP は chain(12): 12→15、chain(16): 16→23。真値 20 / 36 には
  遠く、**60 秒の分枝探索後も bound は 23 のまま**（カットが無いときの 20〜21 より僅かに
  良いだけ）。
  超線形性は加法的カットでは届かず、**乗法的な再帰**（v が支えるエポックの数だけ
  put が要る）を線形不等式の族に落とす方法は未発見。
- **パラメータでは動かない**（`scripts/mip_stage_diag.py`、chain(16) p=5 e=0、60 秒）:
  MIPFocus ∈ {2,3}・Cuts=3・Symmetry=2 のどれも bound 19〜21 / 真値 36 のまま。
- **ヒントで最適解を与えても閉じない**（発見と証明の分離実験）: chain(16) p=5 e=0 で
  BFS の最適スケジュールを primal start として渡すと incumbent 71 は即座に受理されるが、
  **120 秒後の双対 bound は 23**（ヒント無しなら 21）。ボトルネックは解の発見ではなく
  **証明側（双対）** であることが確定。
- **支配カットの消し込み**（`scripts/mip_stage_diag2.py`）: CP-SAT には有効
  （chain(20): あり 4.1 秒 / なし 10.5 秒）、Gurobi では K が大きいと逆効果
  （chain(12) K=48: あり 9.6 秒 / なし 1.8 秒。K=2n なら差なし）。既定は「あり」のまま
  （auto の既定 K=2n では両ソルバとも害がなく、CP-SAT が速くなるため）。

CP-SAT が同じモデルで閉じるのは、clause learning が「この状態集合からは K 段で
届かない」という組合せ的事実を学習できるからで、これは多面体の言葉に翻訳しにくい。
**このギャップの正体が「問題族が MIP に不利」の中身**である。

なお CP-SAT 側のチューニング余地も小さい（`scripts/cpsat_stage_tune.py`、
chain(24) p=6 e=0・120 秒）: default 67.4 秒に対し linearization_level=2 が 64.5 秒で
僅差の最良、workers=16・決定戦略・symmetry_level=4 はいずれも同等か悪化。
既定パラメータのままで良い。

## 6. 線形領域（e ≥ e\*）では interval が優位のまま

`scripts/mip_stage_linear.py`（60 秒/solve、K_start ∈ {n+4, 2n} の両方式）。
この領域は各頂点 1 put（A = n、M = 2n−1）なので interval 版は C=1 の O(n) モデルに
潰れるのに対し、stage 版は K ≈ n 段 × n 頂点の **O(n²) 変数**を抱える。

| case | interval-CPSAT（`cpsat_interval_findings.md` §3） | stage-CPSAT | stage-Gurobi |
|---|---:|---:|---:|
| chain(30) p=7 e=4 | 0.2 秒 | 1.4 秒 | 1.9 秒 |
| chain(50) p=8 e=6 | 5.8 秒 | UNKNOWN (60s) | UNKNOWN (60s) |
| chain(80) p=9 e=9 | 18.2 秒 | UNKNOWN (60s) | UNKNOWN (60s) |

予想どおり **線形領域は interval の圧勝**（interval-CP-SAT は n=160 まで到達済み）。
stage が勝つのは再計算の雪崩で A ≫ n になる超線形領域で、両定式化は**相補的**:

| 領域 | 最適な組み合わせ | 到達範囲（60 秒） |
|---|---|---|
| 超線形（e=0 近傍・pmin 境界） | **stage-CP-SAT** | chain(20)・cbt(4)・pyr(4) |
| 線形（e ≥ e\*） | **interval-CP-SAT** | chain(160)（既報） |
| 下界の機械検証 | stage の判定問題（K 固定 INFEASIBLE） | chain(16) を 0.42 秒 |

## 7. 教訓

- **「定式化 > ソルバ」を正方向で再確認**: `cpsat_findings.md`（定式化を変えず
  ソルバだけ替えても勝てない）の裏返しで、今回は**ソルバを固定して定式化を替えたら
  2 桁速くなった**。道具の輸入とは定式化の輸入である。
- **正規化補題が最強の前処理**: ブロック標準形はモデルを小さくしただけでなく、
  idle 対称性・ブロック内順序・cap 不完全性・終端 take 例外を一掃した。
  ソルバに渡す前に「解空間の同値類を数学で潰す」のが一番効く。
- **MIP の弱点は原理的**: 境界域の超線形下界は LP 緩和に映らない（§5）。
  「MIP 一般が弱い」は誤りだが、「この問題族の下界証明は多面体的手法に不利」は正しい。
- **判定問題に落とすと MIP も証明できる**（chain(16) の下界を 123 秒）。
  最適化で bound が止まっても、下界検証が目的なら K を固定した INFEASIBLE 判定が有効。

## 8. 次の一手

1. **stage-CP-SAT で e 曲面の表を境界域まで拡張する**（chain(20..32) の e=0..e\* を
   一括計算し、`data/exp03` 系の表を n>20 へ延ばす。BFS の限界だった領域が開いた）。
2. **下界証明の外部検証**: SCIP exact ビルド（GMP + certificate）で VIPR を出す。
   ただし SCIP の速度が境界域に届いてから。
3. **一般 DAG の支配カット強化**: 鎖専用カットの一般化（「v の 1 区間が支えられる
   後続部分 DAG の大きさ」による put 下限）は、reach の代わりに部分 DAG の
   p−1 ペブル可解性判定が要る。判定自体を前処理で回す設計はあり得る。
4. **ハイブリッド**: 線形領域は interval-CP-SAT、境界域は stage-CP-SAT、
   下界検証は stage の判定問題、と使い分ける表を方法節に書く。
5. **新規性監査**: ブロック標準形の正規化補題と「put 番号で時間展開する」定式化が
   スケジューリング/rematerialization 文献（Checkmate・MOCCASIN 等）に既出でないか、
   `docs/60_novelty_audit.md` の手順で本文 PDF まで当たる（論文に載せる前に必須）。

## 9. 再現手順

```bash
cd ~/dev/github.com/tetsuo-jp/exact-rev-complexity
.venv/bin/python -m pytest tests/test_mip_stage.py -q   # 23 件
.venv/bin/python scripts/mip_stage_verify.py            # 143 ケース × 3 ソルバ照合
.venv/bin/python scripts/cpsat_stage.py                 # 8 ケース（CP-SAT、〜1 秒）
.venv/bin/python scripts/mip_stage.py --only-gurobi     # 8 ケース（Gurobi、〜10 秒）
.venv/bin/python scripts/mip_stage_bench.py             # 統一ベンチ（§3 の表）
.venv/bin/python scripts/mip_stage_scale.py --seconds 60  # 境界域（§4 の表）
.venv/bin/python scripts/mip_stage_diag2.py             # LP 緩和と消し込み（§5）
.venv/bin/python scripts/mip_stage_linear.py            # 線形領域（§6）
```

Gurobi は `GRB_LICENSE_FILE=~/.config/gurobi/gurobi.lic`（スクリプト内で設定済み）。
