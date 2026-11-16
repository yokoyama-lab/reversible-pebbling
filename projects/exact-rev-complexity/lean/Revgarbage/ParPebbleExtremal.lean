/-
  # 極値予想（「並列可逆ペブリングでは鎖が極値グラフ」）の**反証**（2026-09-05）

  ## 何を主張しているか

  模型は `ParPebbleDAG` / `ParPebbleWindow` と同じ clean な並列可逆ペブリング
  （Blocki–Holman–Lee, arXiv:2110.04191v3 Definition 1）。頂点は `0..n-1` の
  トポロジカル順、入次数 `≤ 2`、sink は `n-1` ただ 1 つ。`d` を sink で終わる
  最長路の**辺数**とすると時間最適な歩数は `T = 2d+1`（`ParPebbleDAG` で両側とも
  機械証明済み）。`p_min(G)` は時間最適な走行のピーク `max_t |C_t|` の最小値。

  $$M(p) := \max\{\,n : \exists G \in \mathcal D(n),\ p_{\min}(G) \le p\,\},\qquad
    n^*(p) := \max\{\,n : p_{\min}(L_n) \le p\,\}$$

  **極値予想**は `M(p) = n^*(p)`（鎖 `L_n` が極値グラフ）。

  ## このファイルで閉じたこと

  * **(A)** `M(5) ≥ 12`。12 頂点の DAG と 21 歩のスケジュールを**具体的に与える**
    存在証明（`witness_run` / `M5_ge_12`）。有界全数検査ではない。
  * **(B)** 12 頂点の**鎖**は時間最適 `T = 23` でピーク 5 に収まらない
    （`chain12_peak5_impossible`）。これは**有界全数検査**（`native_decide`）。
  * **(A)+(B)** 「鎖が極値グラフ」の**点ごとの形** `ChainIsExtremal` は偽
    （`chain_not_extremal`）。
  * 鎖の族が下に閉じている（`R-Q2-01` の「`T_par(n,p)=2n-1 ⟺ n ≤ n*(p)`」）を
    **仮定として明示した**うえで `M(5) > n^*(5)` を導く
    （`extremal_false_of_chain_monotone`）。⚠ その単調性は**本ファイルでは
    証明していない**。どれが無条件でどれが有界全数かは `lean/EXTREMAL_MANIFEST.md`。

  証人（EXT-alloy 発見・ren-fe 検算・本セッションで独立に再検算）:
  `par = [[], [0], [1], [1], [2,3], [4], [5], [4,6], [4,7], [4,8], [4,9], [10]]`
-/
import Revgarbage.ParPebbleWindow
import Mathlib.Data.Finset.Powerset

namespace ParPebbleExtremal

open ParPebbleDAG

/-! ## 1. 決定可能な合法性判定

`LegalStep` は `∀ v : ℕ` を走るので、そのままでは決定可能でない。
**変化した頂点は必ず `P ∪ Q` に居る**ので、その有限集合に制限してよい。 -/

instance instDecidableChanged (P Q : Finset ℕ) (v : ℕ) : Decidable (Changed P Q v) := by
  unfold Changed; infer_instance

/-- `LegalStep` の決定可能版（`P ∪ Q` に制限したもの）。 -/
def LegalOn (pa : ℕ → Finset ℕ) (P Q : Finset ℕ) : Prop :=
  ∀ v ∈ P ∪ Q, Changed P Q v → ∀ u ∈ pa v, u ∈ P ∧ u ∈ Q

instance instDecidableLegalOn (pa : ℕ → Finset ℕ) (P Q : Finset ℕ) :
    Decidable (LegalOn pa P Q) := by unfold LegalOn; infer_instance

theorem changed_mem_union {P Q : Finset ℕ} {v : ℕ} (h : Changed P Q v) : v ∈ P ∪ Q := by
  rcases h with ⟨h1, _⟩ | ⟨_, h2⟩
  · exact Finset.mem_union_left _ h1
  · exact Finset.mem_union_right _ h2

/-- **制限しても同値**。以後 `decide` はこちらを使う。 -/
theorem legalStep_iff_legalOn (pa : ℕ → Finset ℕ) (P Q : Finset ℕ) :
    LegalStep pa P Q ↔ LegalOn pa P Q :=
  ⟨fun h v _ hch u hu => h v hch u hu,
   fun h v hch u hu => h v (changed_mem_union hch) hch u hu⟩

/-! ## 2. clean な走行とグラフの族 `D(n)` -/

/-- **`T` 歩・ピーク `p` の clean な走行**:
    `C_0 = ∅`、各歩が合法、`C_T = {sink}`、どの時刻も `|C_t| ≤ p`。

    ⚠ 「配置は頂点集合の中に収まる」は**課していない**。課さないほうが
    非存在の主張（B）は強くなる。制限は `CleanRun.restrict` で後から取る。 -/
structure CleanRun (pa : ℕ → Finset ℕ) (sink : ℕ) (P : ℕ → Finset ℕ) (T p : ℕ) : Prop where
  start  : P 0 = ∅
  legal  : ∀ t, t < T → LegalStep pa (P t) (P (t + 1))
  finish : P T = {sink}
  peak   : ∀ t, t ≤ T → (P t).card ≤ p

theorem CleanRun.toPebbling {pa : ℕ → Finset ℕ} {sink : ℕ} {P : ℕ → Finset ℕ} {T p : ℕ}
    (h : CleanRun pa sink P T p) : Pebbling pa P T := ⟨h.start, h.legal⟩

/-- **頂点集合への制限**（無条件・一般）。親が `V` に閉じていて `sink ∈ V` なら、
    走行を `V` へ切り落としても走行のまま。ピークは増えない。

    これにより、(B) の全数検査を「`V` の部分集合だけ」で行ってよいことが正当化される
    ——`V` の外にペブルを置く走行があったとしても、切り落とせば `V` の中の走行になる。 -/
theorem CleanRun.restrict {pa : ℕ → Finset ℕ} {sink : ℕ} {P : ℕ → Finset ℕ} {T p : ℕ}
    {V : Finset ℕ} (h : CleanRun pa sink P T p) (hsink : sink ∈ V)
    (hcl : ∀ v ∈ V, ∀ u ∈ pa v, u ∈ V) :
    CleanRun pa sink (fun t => P t ∩ V) T p := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [h.start]
  · intro t ht v hch u hu
    have hvV : v ∈ V := by
      rcases hch with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact (Finset.mem_inter.mp h1).2
      · exact (Finset.mem_inter.mp h2).2
    have hch' : Changed (P t) (P (t + 1)) v := by
      rcases hch with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨(Finset.mem_inter.mp h1).1,
          fun hc => h2 (Finset.mem_inter.mpr ⟨hc, hvV⟩)⟩
      · exact Or.inr ⟨fun hc => h1 (Finset.mem_inter.mpr ⟨hc, hvV⟩),
          (Finset.mem_inter.mp h2).1⟩
    have hp := h.legal t ht v hch' u hu
    exact ⟨Finset.mem_inter.mpr ⟨hp.1, hcl v hvV u hu⟩,
           Finset.mem_inter.mpr ⟨hp.2, hcl v hvV u hu⟩⟩
  · show P T ∩ V = {sink}
    rw [h.finish]
    ext x
    simp only [Finset.mem_inter, Finset.mem_singleton]
    exact ⟨fun hx => hx.1, fun hx => ⟨hx, hx ▸ hsink⟩⟩
  · intro t ht
    exact le_trans (Finset.card_le_card Finset.inter_subset_left) (h.peak t ht)

/-- **族 `D(n)`**: 頂点 `0..n-1` がトポロジカル順・入次数 `≤ 2`・
    sink は `n-1` ただ 1 つ（他はすべて子を持つ）・`n` 以上の頂点には辺が無い。 -/
structure InClass (pa : ℕ → Finset ℕ) (n : ℕ) : Prop where
  topo    : ∀ v ∈ Finset.range n, ∀ u ∈ pa v, u < v
  indeg   : ∀ v ∈ Finset.range n, (pa v).card ≤ 2
  child   : ∀ v ∈ Finset.range n, v ≠ n - 1 → ∃ w ∈ Finset.range n, v ∈ pa w
  outside : ∀ v, n ≤ v → pa v = ∅

/-- **深さの証明書（両側）**: 「sink で終わる最長路の辺数がちょうど `d`」。

    * **上から**: 親で真に増える深さラベル `dep` が在り、`D(n)` 上の最大値は `d` で
      それを取るのは sink `n-1` だけ ⇒ どの路も `d` 辺以下。
    * **下から**: `d` 辺の路 `w 0 → ⋯ → w d = n-1` が**実在する** ⇒ 最長路は `d` 辺以上。

    ⚠ **上からだけでは足りない**（`dep` が飛べば真の深さは `d` より小さくなりうる。
    そうなると `T = 2d+1` は時間最適より**長い**時間を与えたことになり、
    「反例は時間をもらって勝っているのではない」という主張が崩れる）。
    2 つ揃えて初めて `ParPebbleDAG.par_time_exact_dag_two_sided` の両側が当たる。 -/
def HasDepth (pa : ℕ → Finset ℕ) (n d : ℕ) : Prop :=
  (∃ dep : ℕ → ℕ,
    dep (n - 1) = d ∧
    (∀ v ∈ Finset.range n, dep v ≤ d) ∧
    (∀ v ∈ Finset.range n, ∀ u ∈ pa v, dep u < dep v) ∧
    (∀ v ∈ Finset.range n, dep v = d → v = n - 1)) ∧
  (∃ w : ℕ → ℕ, (∀ j, j < d → w j ∈ pa (w (j + 1))) ∧ w d = n - 1)

/-- `M(p) ≥ n` の主張（`D(n)` に時間最適・ピーク `p` の走行を持つ DAG が在る）。 -/
def Achieves (n p : ℕ) : Prop :=
  ∃ (pa : ℕ → Finset ℕ) (d : ℕ) (P : ℕ → Finset ℕ),
    InClass pa n ∧ HasDepth pa n d ∧ CleanRun pa (n - 1) P (2 * d + 1) p

/-- `n` 頂点の鎖 `L_n`（`v` の親は `v-1`）。 -/
def chainPa (n : ℕ) : ℕ → Finset ℕ := fun v => if 0 < v ∧ v < n then {v - 1} else ∅

/-- `n^*(p) ≥ n` の主張（鎖 `L_n` が時間最適 `T = 2(n-1)+1` でピーク `p` に収まる）。 -/
def ChainAchieves (n p : ℕ) : Prop :=
  ∃ P, CleanRun (chainPa n) (n - 1) P (2 * (n - 1) + 1) p

/-- **極値予想の点ごとの形**: `D(n)` の誰かがピーク `p` で時間最適に走れるなら、
    `n` 頂点の**鎖**も走れる。これが成り立てば `M(p) = n^*(p)` が従う。 -/
def ChainIsExtremal : Prop :=
  ∀ (n p d : ℕ) (pa : ℕ → Finset ℕ),
    InClass pa n → HasDepth pa n d →
    (∃ P, CleanRun pa (n - 1) P (2 * d + 1) p) → ChainAchieves n p

/-! ## 3. 有界全数検査のための到達集合（(B) だけが使う） -/

/-- `V` の部分集合で大きさ `p` 以下のもの全体。 -/
def cfgs (V : Finset ℕ) (p : ℕ) : Finset (Finset ℕ) :=
  V.powerset.filter (fun s => s.card ≤ p)

theorem mem_cfgs {V s : Finset ℕ} {p : ℕ} (h1 : s ⊆ V) (h2 : s.card ≤ p) : s ∈ cfgs V p := by
  simp only [cfgs, Finset.mem_filter, Finset.mem_powerset]
  exact ⟨h1, h2⟩

def reachStep (pa : ℕ → Finset ℕ) (V : Finset ℕ) (p : ℕ)
    (R : Finset (Finset ℕ)) : Finset (Finset ℕ) :=
  (cfgs V p).filter (fun Q => ∃ P ∈ R, LegalOn pa P Q)

/-- 時刻 `t` に在りうる配置の**上からの近似**。`∅` から出発して合法な 1 歩を
    ピーク `p`・頂点集合 `V` の枠内で繰り返す。 -/
def reach (pa : ℕ → Finset ℕ) (V : Finset ℕ) (p : ℕ) : ℕ → Finset (Finset ℕ)
  | 0     => {∅}
  | t + 1 => reachStep pa V p (reach pa V p t)

/-- **健全性**: `V` に収まるピーク `p` 以下の走行の配置は、必ず `reach` に入っている。
    したがって `reach T` に `{sink}` が居なければ、そのような走行は**存在しない**。 -/
theorem mem_reach {pa : ℕ → Finset ℕ} {sink : ℕ} {P : ℕ → Finset ℕ} {T p : ℕ} {V : Finset ℕ}
    (h : CleanRun pa sink P T p) (hin : ∀ t, t ≤ T → P t ⊆ V) :
    ∀ t, t ≤ T → P t ∈ reach pa V p t := by
  intro t
  induction t with
  | zero => intro _; rw [h.start]; simp [reach]
  | succ t IH =>
      intro ht
      simp only [reach, reachStep, Finset.mem_filter]
      refine ⟨mem_cfgs (hin (t + 1) ht) (h.peak (t + 1) ht), P t, IH (by omega), ?_⟩
      exact (legalStep_iff_legalOn _ _ _).mp (h.legal t (by omega))


/-! ## 4. 証人（12 頂点・深さ 10・時間最適 T = 21・ピーク 5）

  `par = [[], [0], [1], [1], [2,3], [4], [5], [4,6], [4,7], [4,8], [4,9], [10]]`
  EXT-alloy が Alloy / TLC / SAT / 全数 DP で見つけ、ren-fe が独立に再検算し、
  本セッションでもさらに独立の Python 検査器で再検算した。 -/

/-- 証人 DAG の親関数。頂点 12 以上には辺が無い。 -/
def wPa (v : ℕ) : Finset ℕ :=
  if v = 1 then {0} else
  if v = 2 then {1} else
  if v = 3 then {1} else
  if v = 4 then {2, 3} else
  if v = 5 then {4} else
  if v = 6 then {5} else
  if v = 7 then {4, 6} else
  if v = 8 then {4, 7} else
  if v = 9 then {4, 8} else
  if v = 10 then {4, 9} else
  if v = 11 then {10} else ∅

theorem wPa_outside : ∀ v, 12 ≤ v → wPa v = ∅ := by
  intro v hv
  unfold wPa
  rw [if_neg (by omega : ¬ v = 1), if_neg (by omega : ¬ v = 2),
      if_neg (by omega : ¬ v = 3), if_neg (by omega : ¬ v = 4),
      if_neg (by omega : ¬ v = 5), if_neg (by omega : ¬ v = 6),
      if_neg (by omega : ¬ v = 7), if_neg (by omega : ¬ v = 8),
      if_neg (by omega : ¬ v = 9), if_neg (by omega : ¬ v = 10),
      if_neg (by omega : ¬ v = 11)]

/-- 深さラベル（親で真に増える）。最大値 10 を取るのは sink `11` だけ。 -/
def wDep (v : ℕ) : ℕ := if v ≤ 2 then v else v - 1

/-- 最長路 `0 → 1 → 2 → 4 → 5 → ⋯ → 11`（辺数 10）。 -/
def wPath (j : ℕ) : ℕ := if j ≤ 2 then j else j + 1

/-- ピーク 5 の 21 歩スケジュール（`t = 22` 以降は使わない）。 -/
def wSched : ℕ → Finset ℕ
  | 0 => ∅
  | 1 => {0}
  | 2 => {0, 1}
  | 3 => {1, 2, 3}
  | 4 => {1, 2, 3, 4}
  | 5 => {1, 4, 5}
  | 6 => {0, 1, 4, 5, 6}
  | 7 => {0, 4, 6, 7}
  | 8 => {4, 5, 6, 7, 8}
  | 9 => {4, 5, 7, 8, 9}
  | 10 => {4, 7, 9, 10}
  | 11 => {4, 7, 9, 10, 11}
  | 12 => {4, 7, 8, 9, 11}
  | 13 => {4, 5, 7, 8, 11}
  | 14 => {4, 5, 6, 7, 11}
  | 15 => {0, 4, 5, 6, 11}
  | 16 => {0, 1, 4, 5, 11}
  | 17 => {1, 2, 3, 4, 11}
  | 18 => {1, 2, 3, 11}
  | 19 => {0, 1, 11}
  | 20 => {0, 11}
  | _ => {11}

/-! ### 4.1 テストファースト — 証人が満たすべき性質を計算で確かめる -/

/-- 入次数 ≤ 2。 -/
example : ∀ v ∈ Finset.range 12, (wPa v).card ≤ 2 := by decide
/-- sink は 11 ただ 1 つ（他はすべて子を持つ）。 -/
example : ∀ v ∈ Finset.range 12, v ≠ 11 → ∃ w ∈ Finset.range 12, v ∈ wPa w := by decide
/-- 深さ 10 の路が実在する。 -/
example : ∀ j < 10, wPath j ∈ wPa (wPath (j + 1)) := by decide
example : wPath 10 = 11 := by decide
/-- ピークはちょうど 5（4 以下ではない）。 -/
example : ∀ t ≤ 21, (wSched t).card ≤ 5 := by decide
example : ¬ (∀ t ≤ 21, (wSched t).card ≤ 4) := by decide
/-- 始点は空・終点は sink のみ。 -/
example : wSched 0 = ∅ := by decide
example : wSched 21 = {11} := by decide

/-! ### 4.2 (A) の証明 — **存在**（証人 1 個。有界全数検査ではない） -/

theorem wSched_legal : ∀ t < 21, LegalOn wPa (wSched t) (wSched (t + 1)) := by decide

theorem wSched_peak : ∀ t ≤ 21, (wSched t).card ≤ 5 := by decide

/-- **証人のスケジュールは合法な clean 走行で、ピークは 5。** -/
theorem witness_run : CleanRun wPa 11 wSched 21 5 where
  start := by decide
  legal := fun t ht => (legalStep_iff_legalOn _ _ _).mpr (wSched_legal t ht)
  finish := by decide
  peak := wSched_peak

/-- **証人は `D(12)` に属する。** -/
theorem witness_class : InClass wPa 12 where
  topo := by decide
  indeg := by decide
  child := by decide
  outside := wPa_outside

/-- **証人の深さは 10**（したがって時間最適な歩数は `2·10+1 = 21`）。 -/
theorem witness_depth : HasDepth wPa 12 10 :=
  ⟨⟨wDep, by decide, by decide, by decide, by decide⟩, wPath, by decide, by decide⟩

/-- **`T = 21` は本当に時間最適**（もらった時間で勝っているのではない）。
    `ParPebbleWindow.par_time_exact_dag_two_sided` の下界側をそのまま当てる。 -/
theorem witness_time_optimal :
    ∀ (P : ℕ → Finset ℕ) (T : ℕ), Pebbling wPa P T → 11 ∈ P T →
      (∀ j, j < 10 → wPath j ∉ P T) → 2 * 10 + 1 ≤ T :=
  (par_time_exact_dag_two_sided (pa := wPa) (V := Finset.range 12) (dep := wDep)
    (sink := 11) (d := 10) (w := wPath)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)).2

/-- ⭐ **(A) `M(5) ≥ 12`。** 12 頂点の DAG が時間最適・ピーク 5 で走れる。
    **存在の主張なので証人 1 個で閉じる**（有界全数検査ではない）。 -/
theorem M5_ge_12 : Achieves 12 5 :=
  ⟨wPa, 10, wSched, witness_class, witness_depth, witness_run⟩


/-! ## 5. 鎖 — 既知値の再現と (B)

  台帳（`Q13` / `R-Q2-01`、層 2・DRAT 証明書つき）は `n^*(5) = 11` と言う。
  **その値が本ファイルの定義から出ることを先に確かめる**:
  鎖 `n=11` はピーク 5 で走れて 4 では走れない、鎖 `n=12` は 6 で走れて 5 では走れない。 -/

/-- 鎖はトポロジカル順・入次数 1・sink 一意（無条件・任意の `n`）。 -/
theorem chain_class (n : ℕ) : InClass (chainPa n) n where
  topo := by
    intro v _ u hu
    unfold chainPa at hu
    split at hu
    · rename_i hc; rw [Finset.mem_singleton] at hu; omega
    · simp at hu
  indeg := by
    intro v _
    unfold chainPa
    split
    · simp
    · simp
  child := by
    intro v hv hne
    rw [Finset.mem_range] at hv
    refine ⟨v + 1, Finset.mem_range.mpr (by omega), ?_⟩
    unfold chainPa
    rw [if_pos (by omega)]
    simp
  outside := by
    intro v hv
    unfold chainPa
    rw [if_neg (by omega)]

/-- 鎖の深さは `n-1`（無条件・任意の `n`）。 -/
theorem chain_depth (n : ℕ) : HasDepth (chainPa n) n (n - 1) := by
  refine ⟨⟨id, rfl, ?_, ?_, ?_⟩, id, ?_, rfl⟩
  · intro v hv; rw [Finset.mem_range] at hv; simp; omega
  · intro v hv u hu; exact (chain_class n).topo v hv u hu
  · intro _ _ h; exact h
  · intro j hj
    show j ∈ chainPa n (j + 1)
    unfold chainPa
    rw [if_pos (by omega)]
    simp

/-- 鎖も `D(n)` の一員なので `n^*(p) ≤ M(p)`（無条件）。 -/
theorem Achieves_of_chainAchieves {n p : ℕ} (h : ChainAchieves n p) : Achieves n p := by
  obtain ⟨P, hP⟩ := h
  exact ⟨chainPa n, n - 1, P, chain_class n, chain_depth n, hP⟩

/-- **鎖でも `T = 2(n-1)+1` が時間最適**（下界側・無条件・任意の `n ≥ 2`）。
    証人の `T = 21` も鎖 `L_12` の `T = 23` も、それぞれ自分の時間最適値である。
    ⇒ 反例は「時間を余分にもらって」勝っているのではない。 -/
theorem chain_time_lower (n : ℕ) (hn : 2 ≤ n) :
    ∀ (P : ℕ → Finset ℕ) (T : ℕ), Pebbling (chainPa n) P T → (n - 1) ∈ P T →
      (∀ j, j < n - 1 → j ∉ P T) → 2 * (n - 1) + 1 ≤ T :=
  (par_time_exact_dag_two_sided (pa := chainPa n) (V := Finset.range n) (dep := id)
    (sink := n - 1) (d := n - 1) (w := id)
    (Finset.mem_range.mpr (by omega)) rfl (by omega)
    (fun v hv => by rw [Finset.mem_range] at hv; simp; omega)
    (fun _ _ h => h)
    (fun v hv u hu => by
      have := (chain_class n).topo v hv u hu
      rw [Finset.mem_range] at hv ⊢; omega)
    (fun v hv u hu => (chain_class n).topo v hv u hu)
    (fun j hj => by
      show j ∈ chainPa n (j + 1)
      unfold chainPa
      rw [if_pos (by omega)]
      simp)
    rfl).2

/-- 鎖 `L_11` のピーク 5・21 歩スケジュール。 -/
def c11Sched : ℕ → Finset ℕ
  | 0 => ∅
  | 1 => {0}
  | 2 => {0, 1}
  | 3 => {1, 2}
  | 4 => {1, 2, 3}
  | 5 => {1, 3, 4}
  | 6 => {0, 1, 3, 4, 5}
  | 7 => {0, 3, 5, 6}
  | 8 => {3, 4, 5, 6, 7}
  | 9 => {3, 4, 6, 7, 8}
  | 10 => {3, 6, 8, 9}
  | 11 => {3, 6, 8, 9, 10}
  | 12 => {3, 6, 7, 8, 10}
  | 13 => {3, 4, 6, 7, 10}
  | 14 => {3, 4, 5, 6, 10}
  | 15 => {0, 3, 4, 5, 10}
  | 16 => {0, 1, 3, 4, 10}
  | 17 => {1, 2, 3, 10}
  | 18 => {1, 2, 10}
  | 19 => {0, 1, 10}
  | 20 => {0, 10}
  | _ => {10}

/-- 鎖 `L_12` のピーク 6・23 歩スケジュール。 -/
def c12Sched : ℕ → Finset ℕ
  | 0 => ∅
  | 1 => {0}
  | 2 => {0, 1}
  | 3 => {1, 2}
  | 4 => {1, 2, 3}
  | 5 => {1, 3, 4}
  | 6 => {1, 3, 4, 5}
  | 7 => {1, 3, 5, 6}
  | 8 => {1, 3, 5, 6, 7}
  | 9 => {0, 1, 3, 5, 7, 8}
  | 10 => {0, 3, 5, 7, 8, 9}
  | 11 => {3, 5, 7, 9, 10}
  | 12 => {3, 5, 7, 9, 10, 11}
  | 13 => {3, 5, 7, 8, 9, 11}
  | 14 => {3, 5, 7, 8, 11}
  | 15 => {3, 5, 6, 7, 11}
  | 16 => {3, 5, 6, 11}
  | 17 => {0, 3, 4, 5, 11}
  | 18 => {0, 1, 3, 4, 11}
  | 19 => {1, 2, 3, 11}
  | 20 => {1, 2, 11}
  | 21 => {0, 1, 11}
  | 22 => {0, 11}
  | _ => {11}

/-- 鎖 `L_11` はピーク 5 で時間最適に走れる（`n^*(5) ≥ 11`。**存在**）。 -/
theorem chain11_peak5 : ChainAchieves 11 5 :=
  ⟨c11Sched, by
    refine ⟨by decide, fun t ht => (legalStep_iff_legalOn _ _ _).mpr ?_, by decide, by decide⟩
    revert t ht
    decide⟩

/-- 鎖 `L_12` はピーク 6 なら時間最適に走れる（**存在**）。5 で落ちるのが本質。 -/
theorem chain12_peak6 : ChainAchieves 12 6 :=
  ⟨c12Sched, by
    refine ⟨by decide, fun t ht => (legalStep_iff_legalOn _ _ _).mpr ?_, by decide, by decide⟩
    revert t ht
    decide⟩

/-! ### 5.1 (B) — **有界全数検査**（`native_decide`）

`mem_reach`（無条件の補題）で「走行が在れば `reach` に居る」を保証したうえで、
`reach` の中身を**計算**して `{sink}` が居ないことを見る。⚠ ここだけが
`Lean.ofReduceBool` を使う。 -/

/-- 鎖 `L_12`・ピーク 5・23 歩の到達集合に `{11}` は居ない（**有界全数検査**）。 -/
theorem chain12_sink_unreachable :
    ({11} : Finset ℕ) ∉ reach (chainPa 12) (Finset.range 12) 5 23 := by
  native_decide

/-- 鎖 `L_11`・ピーク 4・21 歩の到達集合に `{10}` は居ない（**有界全数検査**）。 -/
theorem chain11_sink_unreachable_p4 :
    ({10} : Finset ℕ) ∉ reach (chainPa 11) (Finset.range 11) 4 21 := by
  native_decide

/-- 一般の橋渡し（無条件）: 到達集合に `{sink}` が居なければ走行は存在しない。 -/
theorem not_chainAchieves_of_unreachable {n p : ℕ}
    (hne : 0 < n)
    (hun : ({n - 1} : Finset ℕ) ∉ reach (chainPa n) (Finset.range n) p (2 * (n - 1) + 1)) :
    ¬ ChainAchieves n p := by
  rintro ⟨P, h⟩
  have hcl : ∀ v ∈ Finset.range n, ∀ u ∈ chainPa n v, u ∈ Finset.range n := by
    intro v hv u hu
    have := (chain_class n).topo v hv u hu
    rw [Finset.mem_range] at hv ⊢
    omega
  have hsink : (n - 1) ∈ Finset.range n := Finset.mem_range.mpr (by omega)
  have h' := h.restrict hsink hcl
  have hin : ∀ t, t ≤ 2 * (n - 1) + 1 → (fun t => P t ∩ Finset.range n) t ⊆ Finset.range n :=
    fun _ _ => Finset.inter_subset_right
  have hm := mem_reach h' hin (2 * (n - 1) + 1) le_rfl
  rw [h'.finish] at hm
  exact hun hm

/-- ⭐ **(B) 鎖 `L_12` は時間最適 `T = 23` でピーク 5 に収まらない。**
    したがって `p_min(L_12) = 6`（`chain12_peak6` と合わせて）。 -/
theorem chain12_peak5_impossible : ¬ ChainAchieves 12 5 :=
  not_chainAchieves_of_unreachable (by norm_num) chain12_sink_unreachable

/-- 鎖 `L_11` はピーク 4 では走れない。したがって `p_min(L_11) = 5`
    （台帳 `Q13` / `R-Q2-01` の `n^*(5) = 11` を本ファイルの定義が再現している）。 -/
theorem chain11_peak4_impossible : ¬ ChainAchieves 11 4 :=
  not_chainAchieves_of_unreachable (by norm_num) chain11_sink_unreachable_p4

/-! ## 6. 反証 -/

/-- ⭐⭐ **極値予想（点ごとの形）は偽。**
    12 頂点の DAG がピーク 5 で時間最適に走れるのに、12 頂点の**鎖**は走れない。 -/
theorem chain_not_extremal : ¬ ChainIsExtremal := fun h =>
  chain12_peak5_impossible (h 12 5 10 wPa witness_class witness_depth ⟨wSched, witness_run⟩)

/-- ⭐ **`M(5) ≥ 12` と `n^*(5) ≤ 11` を並べた形。**

    第 2 の主張（`n^*(5) ≤ 11`）は「鎖の族が下に閉じている」
    ——`R-Q2-01` の `T_par(n,p) = 2n-1 ⟺ n ≤ n^*(p)`——を**仮定**する。
    ⚠ **その単調性は本ファイルでは証明していない**（台帳では層 2）。
    仮定なしで閉じているのは `chain12_peak5_impossible`（`n = 12` の 1 点）まで。 -/
theorem extremal_false_of_chain_monotone
    (hmono : ∀ m n p : ℕ, m ≤ n → ChainAchieves n p → ChainAchieves m p) :
    Achieves 12 5 ∧ (∀ n, ChainAchieves n 5 → n ≤ 11) := by
  refine ⟨M5_ge_12, fun n hn => ?_⟩
  by_contra hlt
  exact chain12_peak5_impossible (hmono 12 n 5 (by omega) hn)

end ParPebbleExtremal
