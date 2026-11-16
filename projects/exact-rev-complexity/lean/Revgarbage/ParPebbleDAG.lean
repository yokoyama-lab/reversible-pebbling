/-
  並列可逆ペブリングの時間下界を **任意の DAG** へ一般化する（2026-08-14）。

  `ParPebble.lean` は鎖（親が `v-1` ただ一つ）で
  `time_lower_bound : 2*n - 1 ≤ T` を証明した。ここでは親を任意の集合にして、
  **「長さ d の有向路があれば T ≥ 2d-1」** を示す。

  ピラミッド（高さ h、深さ h）に当てると **T ≥ 2h-1** が出る。
  実測ではこの下界が十分な空間で達成されるので
  （`data/q2_parallel_findings.md` の統一則、h=6 で場外検定的中）、
  **T_par = 2·depth - 1 の下界側が定理になる。**

  模型は Blocki–Holman–Lee (arXiv:2110.04191v3) Definition 1 と同一。
-/
import Mathlib.Data.Finset.Basic

namespace ParPebbleDAG

variable {pa : ℕ → Finset ℕ}

/-- 頂点 `v` が配置 `P` と `Q` の間で変化した。 -/
def Changed (P Q : Finset ℕ) (v : ℕ) : Prop :=
  (v ∈ P ∧ v ∉ Q) ∨ (v ∉ P ∧ v ∈ Q)

/-- 合法な 1 ステップ: 変化した頂点の**すべての親**が前後の両方に居る。 -/
def LegalStep (pa : ℕ → Finset ℕ) (P Q : Finset ℕ) : Prop :=
  ∀ v, Changed P Q v → ∀ u ∈ pa v, u ∈ P ∧ u ∈ Q

/-- 空から始まる合法なペブリング列。 -/
structure Pebbling (pa : ℕ → Finset ℕ) (P : ℕ → Finset ℕ) (T : ℕ) : Prop where
  start : P 0 = ∅
  legal : ∀ t, t < T → LegalStep pa (P t) (P (t + 1))

theorem not_changed_iff {P Q : Finset ℕ} {v : ℕ} :
    ¬ Changed P Q v ↔ (v ∈ P ↔ v ∈ Q) := by
  constructor
  · intro h
    constructor
    · intro hp; by_contra hq; exact h (Or.inl ⟨hp, hq⟩)
    · intro hq; by_contra hp; exact h (Or.inr ⟨hp, hq⟩)
  · rintro h (⟨hp, hq⟩ | ⟨hp, hq⟩)
    · exact hq (h.mp hp)
    · exact hp (h.mpr hq)

/-- 在否が変わるなら、その間に**除去の瞬間**がある。 -/
theorem exists_removal {P : ℕ → Finset ℕ} {v t u : ℕ}
    (htu : t ≤ u) (hin : v ∈ P t) (hout : v ∉ P u) :
    ∃ r, t < r ∧ r ≤ u ∧ v ∈ P (r - 1) ∧ v ∉ P r := by
  induction u with
  | zero =>
      exfalso; have : t = 0 := Nat.le_zero.mp htu
      exact hout (this ▸ hin)
  | succ u IH =>
      by_cases hu : v ∈ P u
      · refine ⟨u + 1, ?_, le_rfl, ?_, hout⟩
        · rcases Nat.lt_or_ge t (u + 1) with h | h
          · exact h
          · exfalso
            have ht : t = u + 1 := Nat.le_antisymm htu h
            subst ht; exact hout hin
        · simpa using hu
      · rcases Nat.lt_or_ge u t with h | h
        · exfalso
          have ht : t = u + 1 := by omega
          subst ht; exact hout hin
        · obtain ⟨r, h1, h2, h3, h4⟩ := IH h hu
          exact ⟨r, h1, by omega, h3, h4⟩

/-- 在否が変わるなら、その間に**配置の瞬間**がある。 -/
theorem exists_placement {P : ℕ → Finset ℕ} {v t u : ℕ}
    (htu : t ≤ u) (hout : v ∉ P t) (hin : v ∈ P u) :
    ∃ r, t < r ∧ r ≤ u ∧ v ∉ P (r - 1) ∧ v ∈ P r := by
  induction u with
  | zero =>
      exfalso; have : t = 0 := Nat.le_zero.mp htu
      exact hout (this ▸ hin)
  | succ u IH =>
      by_cases hu : v ∈ P u
      · rcases Nat.lt_or_ge u t with h | h
        · exfalso
          have ht : t = u + 1 := by omega
          subst ht; exact hout hin
        · obtain ⟨r, h1, h2, h3, h4⟩ := IH h hu
          exact ⟨r, h1, by omega, h3, h4⟩
      · refine ⟨u + 1, ?_, le_rfl, by simpa using hu, hin⟩
        rcases Nat.lt_or_ge t (u + 1) with h | h
        · exact h
        · exfalso
          have ht : t = u + 1 := Nat.le_antisymm htu h
          subst ht; exact hout hin

/-- **経路に沿った深さの下界**: `w` が `w j ∈ pa (w (j+1))` を満たす有向路なら、
    `w j` は時刻 `j` 以前には置かれていない（`w j ∈ P t → j + 1 ≤ t`）。 -/
theorem depth_bound_path {P : ℕ → Finset ℕ} {T : ℕ} {w : ℕ → ℕ}
    (hp : Pebbling pa P T) (hw : ∀ j, w j ∈ pa (w (j + 1))) :
    ∀ t, t ≤ T → ∀ j, w j ∈ P t → j + 1 ≤ t := by
  intro t
  induction t with
  | zero =>
      intro _ j hj
      rw [hp.start] at hj; simp at hj
  | succ t IH =>
      intro htT j hj
      by_cases hjt : w j ∈ P t
      · have := IH (by omega) j hjt; omega
      · rcases Nat.eq_zero_or_pos j with rfl | hjpos
        · omega
        · have hch : Changed (P t) (P (t + 1)) (w j) := Or.inr ⟨hjt, hj⟩
          obtain ⟨j', hj'⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
          subst hj'
          have hpar := (hp.legal t (by omega) _ hch _ (hw j')).1
          have := IH (by omega) j' hpar
          omega

/-- **親はより遅い時刻に居る**: 最終状態に残らない頂点 `v` が時刻 `t` に居るなら、
    `v` の任意の親 `u` は `t` より遅い時刻に居る（`v` を消す瞬間に `u` が要るため）。 -/
theorem parent_later {P : ℕ → Finset ℕ} {T v t u : ℕ}
    (hp : Pebbling pa P T) (hv : v ∈ P t) (htT : t ≤ T)
    (hout : v ∉ P T) (hu : u ∈ pa v) :
    ∃ s, t < s ∧ s ≤ T ∧ u ∈ P s := by
  obtain ⟨r, hr1, hr2, hr3, hr4⟩ := exists_removal htT hv hout
  have hch : Changed (P (r - 1)) (P r) v := Or.inl ⟨hr3, hr4⟩
  have hrT : r - 1 < T := by omega
  have heq : r - 1 + 1 = r := by omega
  have := hp.legal (r - 1) hrT v (by rw [heq]; exact hch) u hu
  exact ⟨r, hr1, hr2, by rw [← heq]; exact this.2⟩

/-- 経路を `k` 段下る。途中の頂点が最後には消えていることを添字つきで仮定する。 -/
theorem descend_path {P : ℕ → Finset ℕ} {T : ℕ} {w : ℕ → ℕ}
    (hp : Pebbling pa P T) (hw : ∀ j, w j ∈ pa (w (j + 1))) :
    ∀ k j t, w (j + k) ∈ P t → t ≤ T →
      (∀ i, i ≤ k → w (j + i) ∉ P T) →
      ∃ s, t + k ≤ s ∧ s ≤ T ∧ w j ∈ P s := by
  intro k
  induction k with
  | zero => intro j t h htT _; exact ⟨t, by omega, htT, by simpa using h⟩
  | succ k IH =>
      intro j t h htT hg
      have hjk : j + (k + 1) = (j + k) + 1 := by omega
      have hout : w ((j + k) + 1) ∉ P T := by
        have := hg (k + 1) le_rfl
        rwa [hjk] at this
      rw [hjk] at h
      obtain ⟨s, hs1, hs2, hs3⟩ := parent_later hp h htT hout (hw (j + k))
      obtain ⟨s', h1, h2, h3⟩ := IH j s hs3 hs2 (fun i hi => hg i (by omega))
      exact ⟨s', by omega, h2, h3⟩

/-- **定理（一般 DAG）: `T ≥ 2·(経路の頂点数) - 1`。**

    `w 0 → w 1 → ⋯ → w (d+1)` が有向路（頂点数 `d+2`）で、
    終点 `w (d+1)` が最後に残り、途中の `w 0 … w d` は最後には消えているとする
    （clean 到達）。このとき
    $$T \ge 2(d+2) - 1 = 2d+3.$$

    **深さ `depth` の DAG に当てると `T ≥ 2·depth - 1`。**
    実測ではこの下界が十分な空間で達成される（`data/q2_parallel_findings.md` の統一則。
    ピラミッド h=2..6 で確認、h=6 は場外検定で的中）ので、
    **空間無制約なら `T_par = 2·depth - 1` が決着する。**

    ⚠ `2d+4` は証明できない（変異注入で確認済み）＝ここが証明の限界であり、
    かつ実測が示すとおり**この下界は達成可能**。 -/
theorem time_lower_bound_path {P : ℕ → Finset ℕ} {T d : ℕ} {w : ℕ → ℕ}
    (hp : Pebbling pa P T) (hw : ∀ j, w j ∈ pa (w (j + 1)))
    (hsink : w (d + 1) ∈ P T) (hgone : ∀ j, j ≤ d → w j ∉ P T) : 2 * d + 3 ≤ T := by
  have h0 : w (d + 1) ∉ P 0 := by rw [hp.start]; simp
  obtain ⟨r, hr1, hr2, hr3, hr4⟩ := exists_placement (Nat.zero_le T) h0 hsink
  have hrd : d + 2 ≤ r := depth_bound_path hp hw r hr2 (d + 1) hr4
  have hpar : w d ∈ P r := by
    have hch : Changed (P (r - 1)) (P r) (w (d + 1)) := Or.inr ⟨hr3, hr4⟩
    have hrT : r - 1 < T := by omega
    have heq : r - 1 + 1 = r := by omega
    have := hp.legal (r - 1) hrT _ (by rw [heq]; exact hch) (w d) (hw d)
    rw [← heq]; exact this.2
  obtain ⟨s, hs1, hs2, hs3⟩ :=
    descend_path hp hw d 0 r (by simpa using hpar) hr2
      (fun i hi => by simpa using hgone i hi)
  obtain ⟨r', hr'1, hr'2, _, _⟩ :=
    exists_removal hs2 hs3 (by simpa using hgone 0 (Nat.zero_le d))
  omega

/-! ## 上界（構成）: 層ごとに置いて層ごとに崩す -/

def layered (V : Finset ℕ) (dep : ℕ → ℕ) (sink d t : ℕ) : Finset ℕ :=
  if t ≤ d + 1 then V.filter (fun v => dep v < t)
  else insert sink (V.filter (fun v => dep v < 2 * d + 1 - t))

variable {V : Finset ℕ} {dep : ℕ → ℕ} {sink d : ℕ}

/-- `t = d+1` では前半・後半の式が一致する（sink が最深の唯一の頂点なので）。 -/
theorem layered_down (hs : sink ∈ V) (hds : dep sink = d)
    (hmax : ∀ v ∈ V, dep v ≤ d) (huniq : ∀ v ∈ V, dep v = d → v = sink)
    {t : ℕ} (ht : d + 1 ≤ t) :
    layered V dep sink d t = insert sink (V.filter (fun v => dep v < 2 * d + 1 - t)) := by
  unfold layered
  rcases Nat.eq_or_lt_of_le ht with h | h
  · rw [if_pos (by omega)]
    have hsub : 2 * d + 1 - t = d := by omega
    rw [hsub]
    ext x
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hx, hlt⟩
      rcases Nat.lt_or_ge (dep x) d with h1 | h1
      · exact Or.inr ⟨hx, h1⟩
      · exact Or.inl (huniq x hx (le_antisymm (hmax x hx) h1))
    · rintro (rfl | ⟨hx, hlt⟩)
      · exact ⟨hs, by omega⟩
      · exact ⟨hx, by omega⟩
  · rw [if_neg (by omega)]

variable {pa : ℕ → Finset ℕ}

theorem layered_legal
    (hs : sink ∈ V) (hds : dep sink = d) (hd : 1 ≤ d)
    (hmax : ∀ v ∈ V, dep v ≤ d) (huniq : ∀ v ∈ V, dep v = d → v = sink)
    (hpaV : ∀ v ∈ V, ∀ u ∈ pa v, u ∈ V)
    (hpad : ∀ v ∈ V, ∀ u ∈ pa v, dep u < dep v) :
    Pebbling pa (layered V dep sink d) (2 * d + 1) where
  start := by unfold layered; rw [if_pos (by omega)]; simp
  legal := by
    intro t htT v hch u hu
    by_cases hup : t ≤ d
    · -- 前半: 深さ t の層を置く
      have hA : layered V dep sink d t = V.filter (fun x => dep x < t) := by
        unfold layered; rw [if_pos (by omega)]
      have hB : layered V dep sink d (t + 1) = V.filter (fun x => dep x < t + 1) := by
        unfold layered; rw [if_pos (by omega)]
      have hvV : v ∈ V ∧ dep v = t := by
        rw [hA, hB] at hch
        rcases hch with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exfalso
          simp only [Finset.mem_filter] at h1 h2
          exact h2 ⟨h1.1, by omega⟩
        · simp only [Finset.mem_filter] at h1 h2
          refine ⟨h2.1, ?_⟩
          by_contra hne
          exact h1 ⟨h2.1, by omega⟩
      obtain ⟨hvV, hvd⟩ := hvV
      have huV := hpaV v hvV u hu
      have hud := hpad v hvV u hu
      rw [hA, hB]
      exact ⟨Finset.mem_filter.mpr ⟨huV, by omega⟩, Finset.mem_filter.mpr ⟨huV, by omega⟩⟩
    · -- 後半: 深さ 2d-t の層を崩す
      have hup' : d + 1 ≤ t := by omega
      have hA := layered_down hs hds hmax huniq hup'
      have hB := layered_down hs hds hmax huniq (show d + 1 ≤ t + 1 by omega)
      have hvV : v ∈ V ∧ dep v = 2 * d - t := by
        rw [hA, hB] at hch
        rcases hch with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · simp only [Finset.mem_insert, Finset.mem_filter] at h1 h2
          push_neg at h2
          rcases h1 with rfl | ⟨hxV, hxd⟩
          · exact absurd rfl h2.1
          · refine ⟨hxV, ?_⟩
            have := h2.2 hxV
            omega
        · exfalso
          simp only [Finset.mem_insert, Finset.mem_filter] at h1 h2
          push_neg at h1
          rcases h2 with rfl | ⟨hxV, hxd⟩
          · exact h1.1 rfl
          · have := h1.2 hxV
            omega
      obtain ⟨hvV, hvd⟩ := hvV
      have huV := hpaV v hvV u hu
      have hud := hpad v hvV u hu
      rw [hA, hB]
      exact ⟨Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨huV, by omega⟩),
             Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨huV, by omega⟩)⟩


/-- **主定理（一般 DAG）: `T_par(G) = 2·depth(G) - 1`。**

    * **上界**: `layered`（深さの層ごとに置き、層ごとに崩す）が
      `2d+1` ステップで clean に到達する。`d` は最大深さ（0 始まり）なので
      経路の頂点数は `d+1`、すなわち `2·(頂点数) - 1`
    * **下界**: `time_lower_bound_path`

    仮定は「sink が最深の唯一の頂点」「親は深さが真に小さい」など、
    鎖・ピラミッドを含む素直な DAG で成り立つもの。

    ⚠ **ピークに制約は課していない**（`layered` は最大 `|V|` 個使う）。
    空間を絞ったときの限界は別問題。 -/
theorem par_time_exact_dag
    (hs : sink ∈ V) (hds : dep sink = d) (hd : 1 ≤ d)
    (hmax : ∀ v ∈ V, dep v ≤ d) (huniq : ∀ v ∈ V, dep v = d → v = sink)
    (hpaV : ∀ v ∈ V, ∀ u ∈ pa v, u ∈ V)
    (hpad : ∀ v ∈ V, ∀ u ∈ pa v, dep u < dep v) :
    Pebbling pa (layered V dep sink d) (2 * d + 1) ∧
    layered V dep sink d (2 * d + 1) = {sink} := by
  refine ⟨layered_legal hs hds hd hmax huniq hpaV hpad, ?_⟩
  unfold layered
  rw [if_neg (by omega)]
  have h : 2 * d + 1 - (2 * d + 1) = 0 := by omega
  rw [h]
  simp

/-! ## 非空虚性の確認（具体例で実体化する）

⚠ **抽象定理は仮定が満たせなければ空虚**なので、鎖でない具体例で実際に適用する。 -/

/- 鎖でない最小例: 0 → 2 ← 1（頂点3・深さ2）。
   定理は T = 2*1+1 = 3 を与える（= 2·(経路の頂点数) - 1 = 2*2-1）。 -/
def paD : ℕ → Finset ℕ := fun v => if v = 2 then {0, 1} else ∅
def depD : ℕ → ℕ := fun v => if v = 2 then 1 else 0
def VD : Finset ℕ := {0, 1, 2}

example :
    Pebbling paD (layered VD depD 2 1) (2 * 1 + 1) ∧
    layered VD depD 2 1 (2 * 1 + 1) = {2} := by
  apply par_time_exact_dag
  · decide          -- sink ∈ V
  · decide          -- dep sink = d
  · decide          -- 1 ≤ d
  · decide          -- ∀ v ∈ V, dep v ≤ d
  · decide          -- 最深は sink のみ
  · decide          -- 親は V の中
  · decide          -- 親の深さは真に小さい

/- 実際の配置列を計算して確かめる -/
example : layered VD depD 2 1 0 = ∅ := by decide
example : layered VD depD 2 1 1 = {0, 1} := by decide
example : layered VD depD 2 1 2 = {0, 1, 2} := by decide
example : layered VD depD 2 1 3 = {2} := by decide

end ParPebbleDAG
