/-
# 補題3・補題4 — 小さい `n`（`k`）での厳密値

$$T_{UP}(k,s)=2k-1\ (k\le s),\qquad T_{UG}(n,s)=2n\ (n\le s)$$

下界は `Small.lean` で済んでいるので、ここは**上界＝構成**だけ。どちらも
「上って下る」だけの素朴な手順で足りる（ペブルに余裕があるのでゴーストが要らない）。

- $T_{UP}$: `v_0..v_{k-2}` を順に置き（`k-1` 手）、`v_{k-1}..v_0` を順に外す（`k` 手）
- $T_{UG}$: `v_0..v_{n-2}` を順に置き（`n-1` 手）、`v_{n-1}` を `unghost`（1 手）、
  `v_{n-1}..v_0` を順に外す（`n` 手）

**上限の検査は要らない**: `pcount n c ≤ n` は常に成り立つので、`n ≤ s` なら自動で通る。
-/
import SpookyPebbling.Slope4

namespace Spooky

/-- 鎖の上のペブルは高々 `n` 個。 -/
theorem pcount_le_self (n : ℕ) (c : Config) : pcount n c ≤ n := by
  unfold pcount
  calc ((Finset.range n).filter (fun v => c v = Cell.pebble)).card
      ≤ (Finset.range n).card := Finset.card_filter_le _ _
    _ = n := Finset.card_range n

/-- `0..m-1` がペブル、それ以外は `c` のまま。 -/
def pebBelow (m : ℕ) (c : Config) : Config := fun i => if i < m then Cell.pebble else c i

/-- `v_0, …, v_{m-1}` を順に置く（`m` 手）。 -/
def upTo : ℕ → List Move
  | 0 => []
  | m + 1 => upTo m ++ [⟨Op.pebble, m⟩]

/-- `v_{m-1}, …, v_0` を順に外す（`m` 手）。 -/
def downFrom : ℕ → List Move
  | 0 => []
  | m + 1 => ⟨Op.unpebble, m⟩ :: downFrom m

@[simp] theorem upTo_length (m : ℕ) : (upTo m).length = m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [upTo, ih]

@[simp] theorem downFrom_length (m : ℕ) : (downFrom m).length = m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [downFrom, ih]

/-- **上りの仕様**。 -/
theorem upTo_spec (n : ℕ) : ∀ (m : ℕ) (c : Config), m ≤ n → (∀ i, i < m → c i = Cell.empty) →
    valid n c (upTo m) = true ∧ exec c (upTo m) = pebBelow m c := by
  intro m
  induction m with
  | zero =>
      intro c _ _
      refine ⟨rfl, ?_⟩
      funext i
      show c i = pebBelow 0 c i
      unfold pebBelow
      rw [if_neg (by omega)]
  | succ m ih =>
      intro c hmn hc
      obtain ⟨hv, he⟩ := ih c (by omega) (fun i hi => hc i (by omega))
      have hcell : pebBelow m c m = Cell.empty := by
        unfold pebBelow; rw [if_neg (by omega)]; exact hc m (by omega)
      have hleg : legal n (pebBelow m c) ⟨Op.pebble, m⟩ = true := by
        unfold legal ready
        simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
        refine ⟨by omega, hcell, ?_⟩
        by_cases hm : m = 0
        · exact Or.inl hm
        · refine Or.inr ?_
          unfold pebBelow
          rw [if_pos (by omega)]
      have hstep : step (pebBelow m c) (⟨Op.pebble, m⟩ : Move) = pebBelow (m + 1) c := by
        funext i
        show Function.update (pebBelow m c) m (result Op.pebble) i = pebBelow (m + 1) c i
        by_cases him : i = m
        · subst him
          rw [Function.update_self]
          unfold pebBelow; rw [if_pos (by omega)]; rfl
        · rw [Function.update_of_ne him]
          unfold pebBelow
          by_cases hlt : i < m
          · rw [if_pos hlt, if_pos (by omega)]
          · rw [if_neg hlt, if_neg (by omega)]
      constructor
      · show valid n c (upTo m ++ [⟨Op.pebble, m⟩]) = true
        refine valid_append _ _ c hv ?_
        rw [he]
        simp only [valid_cons, valid_nil, Bool.and_true]
        exact hleg
      · show exec c (upTo m ++ [⟨Op.pebble, m⟩]) = _
        rw [exec_append, he]
        exact hstep

/-- **下りの仕様**。 -/
theorem downFrom_spec (n : ℕ) : ∀ (m : ℕ) (d : Config), m ≤ n →
    (∀ i, i < m → d i = Cell.pebble) →
    valid n d (downFrom m) = true ∧
      exec d (downFrom m) = fun i => if i < m then Cell.empty else d i := by
  intro m
  induction m with
  | zero =>
      intro d _ _
      refine ⟨rfl, ?_⟩
      funext i
      rw [if_neg (by omega)]
      rfl
  | succ m ih =>
      intro d hmn hd
      have hleg : legal n d ⟨Op.unpebble, m⟩ = true := by
        unfold legal ready
        simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
        refine ⟨by omega, hd m (by omega), ?_⟩
        by_cases hm : m = 0
        · exact Or.inl hm
        · exact Or.inr (hd (m - 1) (by omega))
      have hd' : ∀ i, i < m → step d (⟨Op.unpebble, m⟩ : Move) i = Cell.pebble := by
        intro i hi
        rw [step_ne_of_ne (by simp; omega)]
        exact hd i (by omega)
      obtain ⟨hv, he⟩ := ih (step d ⟨Op.unpebble, m⟩) (by omega) hd'
      have hself : step d (⟨Op.unpebble, m⟩ : Move) m = Cell.empty := Function.update_self _ _ _
      refine ⟨by simp only [downFrom, valid_cons, Bool.and_eq_true]; exact ⟨hleg, hv⟩, ?_⟩
      show exec (step d ⟨Op.unpebble, m⟩) (downFrom m) = _
      rw [he]
      funext i
      by_cases hlt : i < m
      · rw [if_pos hlt, if_pos (by omega)]
      · rw [if_neg hlt]
        by_cases him : i = m
        · subst him; rw [if_pos (by omega), hself]
        · rw [if_neg (by omega), step_ne_of_ne (by simp; omega)]

/-! ## 補題4: `T_UP(k,s) = 2k-1`（`k ≤ s`） -/

/-- 構成そのもの（長さ `2k-1` の手順が在る）。 -/
theorem UP_witness_of_le {j s : ℕ} (hjs : j + 1 ≤ s) :
    (2 * j + 1) ∈ UPLengths (j + 1) s := by
  have hc : ∀ i, i < j → sinkPebble (j + 1) i = Cell.empty := by
    intro i hi; rw [sinkPebble_apply, if_neg (by omega)]
  obtain ⟨hv1, he1⟩ := upTo_spec (j + 1) j (sinkPebble (j + 1)) (by omega) hc
  have hall : ∀ i, i < j + 1 → pebBelow j (sinkPebble (j + 1)) i = Cell.pebble := by
    intro i hi
    unfold pebBelow
    by_cases hij : i < j
    · rw [if_pos hij]
    · rw [if_neg hij, sinkPebble_apply, if_pos (by omega)]
  obtain ⟨hv2, he2⟩ :=
    downFrom_spec (j + 1) (j + 1) (pebBelow j (sinkPebble (j + 1))) le_rfl hall
  refine ⟨upTo j ++ downFrom (j + 1), ?_, (ok_iff _ _).mpr ⟨?_, ?_⟩, ?_⟩
  · simp only [List.length_append, upTo_length, downFrom_length]; omega
  · exact valid_append _ _ _ hv1 (by rw [he1]; exact hv2)
  · intro d _
    exact le_trans (pcount_le_self _ d) hjs
  · intro v hv
    rw [exec_append, he1, he2]
    simp [hv, allEmpty]

theorem TUP_le_of_le {j s : ℕ} (hjs : j + 1 ≤ s) : TUP (j + 1) s ≤ 2 * j + 1 :=
  TUP_le (UP_witness_of_le hjs)

/-- **補題4**: `k ≤ s` なら `T_UP(k,s) = 2k-1`。 -/
theorem TUP_eq_of_le {j s : ℕ} (hjs : j + 1 ≤ s) : TUP (j + 1) s = 2 * j + 1 := by
  have hub := TUP_le_of_le hjs
  have hlb := two_mul_sub_one_le_TUP (k := j + 1) (s := s) (by omega)
    ⟨2 * j + 1, UP_witness_of_le hjs⟩
  omega

/-! ## 補題3: `T_UG(n,s) = 2n`（`n ≤ s`） -/

/-- 構成そのもの（長さ `2n` の手順が在る）。 -/
theorem UG_witness_of_le {j s : ℕ} (hjs : j + 1 ≤ s) :
    (2 * (j + 1)) ∈ UGLengths (j + 1) s := by
  have hc : ∀ i, i < j → sinkGhost (j + 1) i = Cell.empty := by
    intro i hi; rw [sinkGhost_apply, if_neg (by omega)]
  obtain ⟨hv1, he1⟩ := upTo_spec (j + 1) j (sinkGhost (j + 1)) (by omega) hc
  have hgh : pebBelow j (sinkGhost (j + 1)) j = Cell.ghost := by
    unfold pebBelow
    rw [if_neg (by omega), sinkGhost_apply, if_pos (by omega)]
  have hleg : legal (j + 1) (pebBelow j (sinkGhost (j + 1))) ⟨Op.unghost, j⟩ = true := by
    unfold legal ready
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
    refine ⟨by omega, hgh, ?_⟩
    by_cases hm : j = 0
    · exact Or.inl hm
    · refine Or.inr ?_
      unfold pebBelow
      rw [if_pos (by omega)]
  have hstep : step (pebBelow j (sinkGhost (j + 1))) (⟨Op.unghost, j⟩ : Move)
      = pebBelow (j + 1) (sinkGhost (j + 1)) := by
    funext i
    show Function.update (pebBelow j (sinkGhost (j + 1))) j (result Op.unghost) i = _
    by_cases hij : i = j
    · subst hij
      rw [Function.update_self]
      unfold pebBelow; rw [if_pos (by omega)]; rfl
    · rw [Function.update_of_ne hij]
      unfold pebBelow
      by_cases hlt : i < j
      · rw [if_pos hlt, if_pos (by omega)]
      · rw [if_neg hlt, if_neg (by omega)]
  have hall : ∀ i, i < j + 1 → pebBelow (j + 1) (sinkGhost (j + 1)) i = Cell.pebble := by
    intro i hi; unfold pebBelow; rw [if_pos hi]
  obtain ⟨hv2, he2⟩ :=
    downFrom_spec (j + 1) (j + 1) (pebBelow (j + 1) (sinkGhost (j + 1))) le_rfl hall
  refine ⟨upTo j ++ [⟨Op.unghost, j⟩] ++ downFrom (j + 1), ?_,
    (ok_iff _ _).mpr ⟨?_, ?_⟩, ?_⟩
  · simp only [List.length_append, upTo_length, downFrom_length, List.length_cons,
      List.length_nil]
    omega
  · refine valid_append _ _ _ (valid_append _ _ _ hv1 ?_) ?_
    · rw [he1]; simp only [valid_cons, valid_nil, Bool.and_true]; exact hleg
    · rw [exec_append, he1]
      show valid (j + 1) (step (pebBelow j (sinkGhost (j + 1))) ⟨Op.unghost, j⟩) _ = true
      rw [hstep]; exact hv2
  · intro d _
    exact le_trans (pcount_le_self _ d) hjs
  · intro v hv
    rw [exec_append, exec_append, he1]
    show exec (step (pebBelow j (sinkGhost (j + 1))) ⟨Op.unghost, j⟩) (downFrom (j + 1)) v
        = allEmpty v
    rw [hstep, he2]
    simp [hv, allEmpty]

theorem TUG_le_of_le {j s : ℕ} (hjs : j + 1 ≤ s) : TUG (j + 1) s ≤ 2 * (j + 1) :=
  TUG_le (UG_witness_of_le hjs)

/-- **補題3**: `n ≤ s` なら `T_UG(n,s) = 2n`。 -/
theorem TUG_eq_of_le {j s : ℕ} (hjs : j + 1 ≤ s) : TUG (j + 1) s = 2 * (j + 1) := by
  have hub := TUG_le_of_le hjs
  have hlb := two_mul_le_TUG (n := j + 1) (s := s) (by omega)
    ⟨2 * (j + 1), UG_witness_of_le hjs⟩
  omega

end Spooky
