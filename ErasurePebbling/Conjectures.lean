import ErasurePebbling.Saturation
import ErasurePebbling.Reach

/-!
# Conjecture B2, the erasure/pebble inequality, and two corollaries

Statements (as `def`s of type `Prop`) of the open claims of RC-02 and of
the topic card, with what is provable about them in general:

* `ConjB2 p e` : `reach(p, e) = (e + 2)·2^(p−2)`.  The `≥` half is
  `theoremB1`; at `e = 0` the conjecture is Knill's theorem
  `reach(p, 0) = 2^(p−1)`, proved here in full generality
  (`reachIs_zero`) from `RevPebbling.PebblingFoundations`.  Bounded
  certificates for `p ≤ 5` are in `Bounded.lean`.
* `IneqM n p e` : `M*(n, p, e+1) ≤ M*(n, p+1, e)` — read as "every clean
  plan with peak `p+1` and `e` erasures can be matched by one with peak `p`
  and `e+1` erasures".  It is **false** in general (counterexample
  `(n, p, e) = (10, 3, 2)`, `Bounded.lean`); the tables suggest it holds
  exactly for `n ≤ 2^(p−1)`, which is the form stated in `IneqM_conj`.
* `drop_threshold` : the first `n` at which one more erasure lowers the move
  count below the `e`-budget optimum is `n = (p−1)(e+1) + 2`, a corollary of
  Theorem A (matches `data/erasure/drops.md`).
-/

namespace ErasurePebbling

open RevPebbling.PebblingFoundations

/-- Conjecture B2 of RC-02. -/
def ConjB2 (p e : Nat) : Prop := ReachIs p e ((e + 2) * 2 ^ (p - 2))

/-- The inequality of the topic card, in the plan-matching form. -/
def IneqM (n p e : Nat) : Prop :=
  ∀ s, IsPlay n (p + 1) e s → ∃ t, IsPlay n p (e + 1) t ∧ t.length ≤ s.length

/-- The restricted form suggested by the tables (`data/erasure/inequality.md`):
the inequality for all `n ≤ 2^(p−1)`. -/
def IneqM_conj : Prop := ∀ n p e, 2 ≤ p → n ≤ 2 ^ (p - 1) → IneqM n p e

/-! ## `e = 0`: Knill's exact reach -/

/-- A play with no erasure is a play of the reversible game. -/
theorem legalB_of_erasures_zero : ∀ (s : List Nat) (b : Board),
    legalE b s = true → erasures b s = 0 → legalB b s = true
  | [], _, _, _ => rfl
  | i :: rest, b, hleg, her => by
      simp only [legalE_cons, Bool.and_eq_true] at hleg
      simp only [erasures_cons] at her
      have h1 : isErase b i = false := by
        cases h : isErase b i
        · rfl
        · rw [h] at her; simp at her
      have h2 : erasures (toggle b i) rest = 0 := by
        rw [h1] at her; simpa using her
      have hok : okMove b i = true := by
        have := hleg.1
        unfold okE at this
        unfold isErase at h1
        cases hm : okMove b i
        · rw [hm] at this h1; simp at this; rw [this] at h1; simp at h1
        · rfl
      show (okMove b i && legalB (toggle b i) rest) = true
      rw [hok, legalB_of_erasures_zero rest _ hleg.2 h2]; rfl

/-- **Knill's reach theorem in the erasure model**: `reach(p, 0) = 2^(p−1)`, i.e.
Conjecture B2 at `e = 0`, for every `p ≥ 2`. -/
theorem reachIs_zero (p : Nat) (hp : 2 ≤ p) : ConjB2 p 0 := by
  unfold ConjB2 ReachIs
  have hpow : (0 + 2) * 2 ^ (p - 2) = 2 ^ (p - 1) := by
    have : p - 1 = (p - 2) + 1 := by omega
    rw [this, Nat.pow_succ]; omega
  have hB1 := ErasurePebbling.theoremB1 p 0 hp
  rw [hpow] at hB1
  rw [hpow]
  refine ⟨hB1, ?_⟩
  intro n ⟨s, hs⟩
  have hleg : legalB (empty n) s = true :=
    legalB_of_erasures_zero s _ hs.legal (Nat.eq_zero_of_le_zero hs.budget)
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; exact Nat.zero_le _
  · have hon : nth (execB (empty n) s) (n - 1) = true := by
      rw [hs.final, nth_target n (n - 1) hn]; simp
    have hmin : ∀ j, j < n - 1 → nth (execB (empty n) s) j = false := by
      intro j hj
      rw [hs.final, nth_target n j hn]; simp; omega
    have := reach_impossible_general hleg hs.peak hon hmin
    omega

/-! ## Where an extra erasure starts to pay -/

theorem estar_threshold (p e : Nat) (hp : 2 ≤ p) :
    estar ((p - 1) * (e + 1) + 1) p = e ∧ estar ((p - 1) * (e + 1) + 2) p = e + 1 := by
  have hp1 : 0 < p - 1 := by omega
  constructor
  · unfold estar
    have e1 : (p - 1) * (e + 1) + 1 - 1 + (p - 1) - 1 = (p - 1) * (e + 1) + (p - 2) := by omega
    rw [e1, Nat.mul_add_div hp1, Nat.div_eq_of_lt (by omega)]
    omega
  · unfold estar
    have e1 : (p - 1) * (e + 1) + 2 - 1 + (p - 1) - 1 = (p - 1) * (e + 2) := by
      rw [Nat.mul_add, Nat.mul_add]; omega
    rw [e1, Nat.mul_div_cancel_left _ hp1]
    omega

/-- **Drop threshold.**  At `n = (p−1)(e+1) + 1` both budgets `e` and `e+1`
attain the floor `2n − 1`; at `n = (p−1)(e+1) + 2` the budget `e+1` still
attains it while every plan with budget `e` is strictly longer.  So the first
`n` at which an extra erasure helps is `(p−1)(e+1) + 2`. -/
theorem drop_threshold (p e : Nat) (hp : 2 ≤ p) :
    (MstarIs ((p - 1) * (e + 1) + 1) p e (2 * ((p - 1) * (e + 1) + 1) - 1) ∧
     MstarIs ((p - 1) * (e + 1) + 1) p (e + 1) (2 * ((p - 1) * (e + 1) + 1) - 1)) ∧
    (MstarIs ((p - 1) * (e + 1) + 2) p (e + 1) (2 * ((p - 1) * (e + 1) + 2) - 1) ∧
     ∀ s, IsPlay ((p - 1) * (e + 1) + 2) p e s → 2 * ((p - 1) * (e + 1) + 2) - 1 < s.length) := by
  obtain ⟨h1, h2⟩ := estar_threshold p e hp
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · exact (theoremA _ p e hp (by omega)).mpr (by rw [h1]; exact Nat.le_refl _)
  · exact (theoremA _ p (e + 1) hp (by omega)).mpr (by rw [h1]; omega)
  · exact (theoremA _ p (e + 1) hp (by omega)).mpr (by rw [h2]; exact Nat.le_refl _)
  · intro s hs
    exact floor_not_attained _ p e hp (by omega) (by rw [h2]; omega) s hs

end ErasurePebbling
