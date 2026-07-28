import RevPebbling.CountRecursion

/-!
# Composition theorem: finite DP certificates → unconditional midpoint bounds

(追記42.)  Fix a space level `s` and let `m = midv s` be the midpoint
value of row S = s+2.  For any "certificate" function `L : Nat → Nat →
Nat` that satisfies the *pure split recursion* laws

  * `L 0 v ≤ 1`,
  * `L (t+1) v ≤ L t v + min (L t (v-w)) (L (t+1) w)` for some split
    `w < v` (or plain monotone fallback `L (t+1) v ≤ L t v`),

the scale-covariance of `count_recursion_split` gives, keeping every
"+1" of the recursion (which exactly compensates the −1 of the base
count `C_S(m_S) ≥ 2^s − 1`):

  `2^s · L t v ≤ C_{S+t}(m_S · v) + 1`      (count_composition)

Consequently a finite certificate `L t v* ≥ 2^t` yields the
unconditional midpoint bound `m_{S+t} ≤ m_S · v*` FOR EVERY S
(midpoint_composition) — the finite-computation → unconditional-bound
scheme of 追記37/42.  Iterating the chain (with the proven midpoint
monotonicity) gives `d ≤ (v*)^{1/t}` and `c = 2d ≤ 2·(v*)^{1/t}`.

Bounded instance here: the exact integer DP table for t ≤ 8, v ≤ 44
(computed by scripts/m5_exact_anchor.py-style full DP, embedded as a
literal and re-verified against its defining recursion by
native_decide) has `L 8 44 = 256 = 2^8`, giving the fully machine-
checked, general-in-S theorem `midpoint_anchor_44 : m_{S+8} ≤ 44·m_S`.
The large anchors (T₀ = 200: v* = 7157336700599306027008, hence
c ≤ 2.5788) use the same theorem with a Python-certified exact bigint
DP; their Lean-internal replay is future work (Array DP + native_decide).
-/

namespace RevPebbling.CompositionAnchor

open RevPebbling.MergeLemma RevPebbling.CountRecursion

/-- countLe is monotone in the threshold. -/
theorem countLe_mono_val (l : List Nat) {v v' : Nat} (h : v ≤ v') :
    countLe l v ≤ countLe l v' := by
  unfold countLe
  apply countP_mono_pointwise l l _ _ (Nat.le_refl _)
  intro i _ _ hp
  simp only [decide_eq_true_eq] at hp ⊢
  omega

/-- The midpoint value m_S = δ(2^{S−2}, S) of row S = s+2 (0-based
index 2^s − 2 in the sorted row of length 2^{s+1} − 1). -/
def midv (s : Nat) : Nat :=
  (rowIter s)[2 ^ s - 2]'(by
    rw [rowIter_length]
    have h1 := two_pow_ge_one s
    have h3 : (2:Nat) ^ s + 2 ^ s = 2 ^ (s + 1) := by
      rw [Nat.pow_succ]; omega
    omega)

theorem midv_pos (s : Nat) : 1 ≤ midv s := by
  obtain ⟨_, hpos⟩ := rowIter_invariant s
  exact hpos _ (List.getElem_mem _)

/-- Base count: the entries up to and including the midpoint give
C_S(m_S) ≥ 2^s − 1. -/
theorem countLe_midv (s : Nat) : 2 ^ s - 1 ≤ countLe (rowIter s) (midv s) := by
  obtain ⟨hsort, _⟩ := rowIter_invariant s
  have hmlen : 2 ^ s - 1 ≤ (rowIter s).length := by
    rw [rowIter_length]
    have h1 := two_pow_ge_one s
    have h3 : (2:Nat) ^ s + 2 ^ s = 2 ^ (s + 1) := by
      rw [Nat.pow_succ]; omega
    omega
  unfold countLe
  apply countP_ge_prefix _ _ _ hmlen
  intro i hi
  simp only [decide_eq_true_eq]
  exact sorted_getElem_le hsort (by omega) _

/-- Every row starts with the entry 1, so any positive threshold
counts at least one entry. -/
theorem countLe_pos (s x : Nat) (hx : 1 ≤ x) :
    1 ≤ countLe (rowIter s) x := by
  have hhead : ∃ t, rowIter s = 1 :: t := by
    match s with
    | 0 => exact ⟨[], rfl⟩
    | s + 1 => exact ⟨_, rowIter_succ_rep s⟩
  obtain ⟨t, ht⟩ := hhead
  rw [ht, countLe_cons]
  simp [hx]

/-- Position-to-value: enough mass below v pins the midpoint under v. -/
theorem midv_le_of_countLe (s v : Nat) (hv : 1 ≤ v)
    (h : 2 ^ s - 1 ≤ countLe (rowIter s) v) : midv s ≤ v := by
  obtain ⟨hsort, _⟩ := rowIter_invariant s
  have h1 := two_pow_ge_one s
  have hpos := countLe_pos s v hv
  unfold midv
  exact sorted_getElem_le_of_countLe _ _ _ hsort _ (by omega)

/-- One row up never loses a positive count (and gains the +1). -/
theorem countLe_succ_row (s x : Nat) (hx : 1 ≤ x) :
    countLe (rowIter s) x + 1 ≤ countLe (rowIter (s + 1)) x := by
  have h := count_recursion_split s x 0 (by omega)
  simp only [Nat.add_zero] at h
  omega

/-- COMPOSITION THEOREM.  Scale covariance of the split recursion:
any certificate function L is transported to scale m_S with mass
factor 2^s, the "+1"s of the recursion exactly absorbing the −1 of
the base count. -/
theorem count_composition (s V : Nat) (L : Nat → Nat → Nat)
    (hL0 : ∀ v, 1 ≤ v → v ≤ V → L 0 v ≤ 1)
    (hstep : ∀ t v, 1 ≤ v → v ≤ V →
      L (t + 1) v ≤ L t v ∨
      ∃ w, 1 ≤ w ∧ w < v ∧
        L (t + 1) v ≤ L t v + min (L t (v - w)) (L (t + 1) w)) :
    ∀ t v, 1 ≤ v → v ≤ V →
      2 ^ s * L t v ≤ countLe (rowIter (s + t)) (midv s * v) + 1 := by
  intro t
  induction t with
  | zero =>
      intro v hv hV
      have hbase := countLe_midv s
      have hmono : countLe (rowIter s) (midv s)
          ≤ countLe (rowIter s) (midv s * v) := by
        apply countLe_mono_val
        have := Nat.mul_le_mul_left (midv s) hv
        simpa using this
      have hmul : 2 ^ s * L 0 v ≤ 2 ^ s := by
        calc 2 ^ s * L 0 v ≤ 2 ^ s * 1 :=
              Nat.mul_le_mul_left _ (hL0 v hv hV)
          _ = 2 ^ s := Nat.mul_one _
      have h1 := two_pow_ge_one s
      simp only [Nat.add_zero]
      omega
  | succ t iht =>
      intro v
      induction v using Nat.strongRecOn with
      | ind v ihv =>
        intro hv hV
        have hmvpos : 1 ≤ midv s * v := Nat.mul_pos (midv_pos s) hv
        rcases hstep t v hv hV with hmono | ⟨w, hw1, hwv, hle⟩
        · have h1 := iht v hv hV
          have h2 := countLe_succ_row (s + t) (midv s * v) hmvpos
          have h3 : 2 ^ s * L (t + 1) v ≤ 2 ^ s * L t v :=
            Nat.mul_le_mul_left _ hmono
          show 2 ^ s * L (t + 1) v
              ≤ countLe (rowIter (s + t + 1)) (midv s * v) + 1
          omega
        · have ha1 : 1 ≤ v - w := by omega
          have haV : v - w ≤ V := by omega
          have hwV : w ≤ V := by omega
          have h1 := iht v hv hV
          have h2 := iht (v - w) ha1 haV
          have h3 := ihv w hwv hw1 hwV
          have hmvw : midv s * (v - w) + midv s * w = midv s * v := by
            rw [← Nat.mul_add]
            congr 1
            omega
          have hsplit := count_recursion_split (s + t)
            (midv s * (v - w)) (midv s * w) (by rw [hmvw]; exact hmvpos)
          rw [hmvw] at hsplit
          have hA : 2 ^ s * min (L t (v - w)) (L (t + 1) w)
              ≤ countLe (rowIter (s + t)) (midv s * (v - w)) + 1 :=
            Nat.le_trans
              (Nat.mul_le_mul_left _ (Nat.min_le_left _ _)) h2
          have hB : 2 ^ s * min (L t (v - w)) (L (t + 1) w)
              ≤ countLe (rowIter (s + t + 1)) (midv s * w) + 1 :=
            Nat.le_trans
              (Nat.mul_le_mul_left _ (Nat.min_le_right _ _)) h3
          have hmul : 2 ^ s * L (t + 1) v
              ≤ 2 ^ s * L t v + 2 ^ s * min (L t (v - w)) (L (t + 1) w) := by
            calc 2 ^ s * L (t + 1) v
                ≤ 2 ^ s * (L t v + min (L t (v - w)) (L (t + 1) w)) :=
                  Nat.mul_le_mul_left _ hle
              _ = _ := Nat.mul_add _ _ _
          show 2 ^ s * L (t + 1) v
              ≤ countLe (rowIter (s + t + 1)) (midv s * v) + 1
          omega

/-- MIDPOINT TRANSPORT: a finite certificate L t v ≥ 2^t forces
m_{S+t} ≤ m_S · v for every S. -/
theorem midpoint_composition (s V t v : Nat) (L : Nat → Nat → Nat)
    (hL0 : ∀ v, 1 ≤ v → v ≤ V → L 0 v ≤ 1)
    (hstep : ∀ t v, 1 ≤ v → v ≤ V →
      L (t + 1) v ≤ L t v ∨
      ∃ w, 1 ≤ w ∧ w < v ∧
        L (t + 1) v ≤ L t v + min (L t (v - w)) (L (t + 1) w))
    (hv : 1 ≤ v) (hV : v ≤ V) (hcert : 2 ^ t ≤ L t v) :
    midv (s + t) ≤ midv s * v := by
  have h := count_composition s V L hL0 hstep t v hv hV
  have hcnt : 2 ^ (s + t) ≤ countLe (rowIter (s + t)) (midv s * v) + 1 := by
    calc 2 ^ (s + t) = 2 ^ s * 2 ^ t := Nat.pow_add 2 s t
      _ ≤ 2 ^ s * L t v := Nat.mul_le_mul_left _ hcert
      _ ≤ _ := h
  have h1 := two_pow_ge_one (s + t)
  have hmvpos : 1 ≤ midv s * v := Nat.mul_pos (midv_pos s) hv
  exact midv_le_of_countLe _ _ hmvpos (by omega)

-- ------------------------------------------------------------------
-- Bounded certificate instance: exact integer DP, t ≤ 8, v ≤ 44.
-- L 8 44 = 256 = 2^8, so m_{S+8} ≤ 44 m_S for every S.
-- ------------------------------------------------------------------

/-- Exact full-integer DP table (rows t = 0..8, columns v = 0..44)
for L(t,v) = L(t−1,v) + max_{0<w<v} min(L(t−1,v−w), L(t,w)),
L(0,v) = 1.  Verified against its defining laws by native_decide in
`Lanchor_hL0` / `Lanchor_hstep`. -/
def anchorRows : List (List Nat) := [
  [0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1],
  [0,1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2],
  [0,1,3,3,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4],
  [0,1,4,4,7,7,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8],
  [0,1,5,5,11,11,13,13,15,15,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],
  [0,1,6,6,16,16,19,19,26,26,29,29,31,31,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32],
  [0,1,7,7,22,22,26,26,42,42,48,48,53,53,58,58,58,58,61,61,63,63,64,64,64,64,64,64,64,64,64,64,64,64,64,64,64,64,64,64,64,64,64,64,64],
  [0,1,8,8,29,29,34,34,64,64,74,74,82,82,92,92,100,100,109,109,116,116,122,122,122,122,125,125,127,127,128,128,128,128,128,128,128,128,128,128,128,128,128,128,128],
  [0,1,9,9,37,37,43,43,93,93,108,108,119,119,135,135,164,164,183,183,198,198,214,214,215,215,225,225,235,235,237,237,244,244,247,247,250,250,250,250,253,253,255,255,256]]

def Lanchor (t v : Nat) : Nat :=
  if t < 9 then (anchorRows.getD t []).getD v 0 else 0

theorem Lanchor_hL0 : ∀ v, 1 ≤ v → v ≤ 44 → Lanchor 0 v ≤ 1 := by
  have key : ∀ v, v < 45 → 1 ≤ v → Lanchor 0 v ≤ 1 := by native_decide
  intro v h1 h2
  exact key v (by omega) h1

theorem Lanchor_hstep : ∀ t v, 1 ≤ v → v ≤ 44 →
    Lanchor (t + 1) v ≤ Lanchor t v ∨
    ∃ w, 1 ≤ w ∧ w < v ∧
      Lanchor (t + 1) v ≤ Lanchor t v
        + min (Lanchor t (v - w)) (Lanchor (t + 1) w) := by
  intro t v hv hV
  by_cases ht : t < 8
  · have key : ∀ t', t' < 8 → ∀ v', v' < 45 → 1 ≤ v' →
        Lanchor (t' + 1) v' ≤ Lanchor t' v' ∨
        ∃ w, w < v' ∧ (1 ≤ w ∧
          Lanchor (t' + 1) v' ≤ Lanchor t' v'
            + min (Lanchor t' (v' - w)) (Lanchor (t' + 1) w)) := by
      native_decide
    rcases key t ht v (by omega) hv with h | ⟨w, hwv, hw1, hle⟩
    · exact Or.inl h
    · exact Or.inr ⟨w, hw1, hwv, hle⟩
  · left
    have hnot : ¬ (t + 1 < 9) := by omega
    simp [Lanchor, hnot]

theorem Lanchor_cert : 2 ^ 8 ≤ Lanchor 8 44 := by native_decide

/-- ANCHOR THEOREM (fully machine-checked, general in S):
m_{S+8} ≤ 44 · m_S for every space level S — hence
d ≤ 44^{1/8} ≈ 1.605 by iteration.  The scheme is the Lean core of
the Python-certified anchors (T₀ = 200 → c ≤ 2.5788, 追記42). -/
theorem midpoint_anchor_44 (s : Nat) : midv (s + 8) ≤ midv s * 44 :=
  midpoint_composition s 44 8 44 Lanchor Lanchor_hL0 Lanchor_hstep
    (by omega) (Nat.le_refl _) Lanchor_cert

end RevPebbling.CompositionAnchor
