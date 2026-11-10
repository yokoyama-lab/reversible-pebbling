import ErasurePebbling.Reach
import ErasurePebbling.Conjectures

/-!
# The additive upper bound for `M*` at the maximal reach

`theoremB1` reaches `(e + 2)·2^(p−2)` with Bennett's binary schedule in both
phases.  The construction does not depend on that choice: any clean plan for
the chain of length `2^(p−1)` with peak `p`, followed by `e` times any clean
plan for the chain of length `2^(p−2)` with peak `p − 1` lifted above a stone
and one irreversible removal of the stone, is a clean plan for the chain of
length `(e + 2)·2^(p−2)` with peak `p` and `e` irreversible removals.  With
optimal sub-plans this gives (`mstar_reach_le`)

  `M*((e+2)·2^(p−2), p, e) ≤ M*(2^(p−1), p, 0) + e·(M*(2^(p−2), p−1, 0) + 1)`.

The exhaustive tables in `data/erasure/` show equality for `p ≤ 6`,
`e ≤ 6`; the reverse inequality is **not** proved here.

Two board lemmas carry the construction: a play on a short board runs
unchanged on the same board extended to the right (`extend_right`), and a
clean play lifted onto an empty window above a pebble (or the source) places
exactly the top cell of the window (`embed`).

No `sorry`; axioms `propext`, `Classical.choice`, `Quot.sound` at most.
-/

namespace ErasurePebbling
namespace Additive

open RevPebbling.PebblingFoundations
open RevPebbling.LiftAbove

/-! ## Extending a board to the right -/

theorem nth_append_left' (d c : Board) {j : Nat} (h : j < d.length) :
    nth (d ++ c) j = nth d j := by
  simp [nth, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem toggle_append_left (d c : Board) {i : Nat} (h : i < d.length) :
    toggle (d ++ c) i = toggle d i ++ c := by
  simp only [toggle, nth_append_left' d c h]
  exact List.set_append_left _ _ h

theorem ones_append (d c : Board) : ones (d ++ c) = ones d + ones c := by
  simp [ones, List.count_append]

theorem length_toggle' (d : Board) (i : Nat) : (toggle d i).length = d.length := by
  simp [toggle]

/-- A play whose moves stay below `d.length` runs unchanged on `d ++ c`. -/
theorem extend_right (c : Board) : ∀ (s : List Nat) (d : Board), (∀ i ∈ s, i < d.length) →
    legalB d s = true →
    legalB (d ++ c) s = true ∧ execB (d ++ c) s = execB d s ++ c ∧
      maxOnes (d ++ c) s = maxOnes d s + ones c
  | [], d, _, _ => ⟨rfl, rfl, by simp [maxOnes, ones_append]⟩
  | i :: rest, d, hb, hl => by
      have hi : i < d.length := hb i (by simp)
      have h' : okMove d i = true ∧ legalB (toggle d i) rest = true := by
        simpa [legalB, Bool.and_eq_true] using hl
      have ih := extend_right c rest (toggle d i)
        (fun j hj => by rw [length_toggle']; exact hb j (by simp [hj])) h'.2
      have hok : okMove (d ++ c) i = okMove d i := by
        cases i with
        | zero => rfl
        | succ k =>
            simp only [okMove]
            rw [show k + 1 - 1 = k from rfl, nth_append_left' d c (by omega)]
      have ht := toggle_append_left d c hi
      refine ⟨?_, ?_, ?_⟩
      · show (okMove (d ++ c) i && legalB (toggle (d ++ c) i) rest) = true
        rw [hok, h'.1, ht, ih.1]; rfl
      · show execB (toggle (d ++ c) i) rest = execB (toggle d i) rest ++ c
        rw [ht, ih.2.1]
      · show max (ones (d ++ c)) (maxOnes (toggle (d ++ c) i) rest)
            = max (ones d) (maxOnes (toggle d i) rest) + ones c
        rw [ht, ih.2.2, ones_append, Nat.add_max_add_right]

/-! ## Lifting a clean play onto an empty window -/

theorem target_append (m : Nat) (hm : 1 ≤ m) (c : Board) :
    (empty m ++ c).set (m - 1) true = target m ++ c := by
  unfold target empty
  exact List.set_append_left _ _ (by simp; omega)

/-- A clean play `s` for the chain of length `m`, lifted to start at `base`,
on a board whose window `[base, base + m)` is empty and whose cell `base − 1`
is pebbled (or `base = 0`): legal, places exactly the top cell of the window,
and raises the pebble count by at most the play's own peak. -/
theorem embed (b : Board) (base m : Nat) (s : List Nat) (hm : 1 ≤ m)
    (hbm : base + m ≤ b.length)
    (hfound : base = 0 ∨ nth b (base - 1) = true)
    (hfree : ∀ j, base ≤ j → j < base + m → nth b j = false)
    (hs : ∀ i ∈ s, i < m) (hl : legalB (empty m) s = true)
    (hx : execB (empty m) s = target m) :
    legalB b (liftAbove base s) = true ∧
    execB b (liftAbove base s) = b.set (base + m - 1) true ∧
    maxOnes b (liftAbove base s) ≤ ones b + maxOnes (empty m) s := by
  -- the part of `b` above the cut is the empty window followed by the rest
  have hwin : (b.drop base).take m = empty m := by
    unfold empty
    refine take_all_false_replicate (by simp; omega) (fun j hj => ?_)
    rw [nth_drop]; exact hfree (base + j) (by omega) (by omega)
  obtain ⟨c, hc⟩ : ∃ c, b.drop base = empty m ++ c :=
    ⟨(b.drop base).drop m, by
      conv => lhs; rw [← List.take_append_drop m (b.drop base)]
      rw [hwin]⟩
  have hext := extend_right c s (empty m) (by rw [length_empty]; exact hs) hl
  rw [← hc] at hext
  refine ⟨legalB_liftAbove base s b hfound hext.1, ?_, ?_⟩
  · have ht := execB_liftAbove_take base s b
    have hd := execB_liftAbove_drop base s b
    rw [hext.2.1, hx] at hd
    have hk : base + m - 1 = (m - 1) + base := by omega
    have hd' : (b.set (base + m - 1) true).drop base = target m ++ c := by
      rw [hk, drop_set_add, hc, target_append m hm]
    have ht' : (b.set (base + m - 1) true).take base = b.take base := by
      rw [hk]; exact take_set_add b base (m - 1) true
    rw [← List.take_append_drop base (execB b (liftAbove base s)),
      ← List.take_append_drop base (b.set (base + m - 1) true), ht, hd, ht', hd']
  · have hp := maxOnes_liftAbove base s b
    rw [hext.2.2] at hp
    have hb := ones_take_drop b base
    rw [hc, ones_append, ones_empty] at hb
    omega

/-! ## The construction with arbitrary sub-plans -/

theorem liftAbove_zero (s : List Nat) : liftAbove 0 s = s := by
  simp [liftAbove]

/-- Phase 0 with an arbitrary clean plan for the chain of length `m`. -/
theorem first_seg (n m q : Nat) (s : List Nat) (hm : 1 ≤ m) (hmn : m ≤ n)
    (hs : IsPlay m q 0 s) :
    Seg n (empty n) (blk n (m - 1) 1 n) q 0 s.length s := by
  have hlB := legalB_of_erasures_zero s (empty m) hs.legal (Nat.le_zero.mp hs.budget)
  have h := embed (empty n) 0 m s hm (by rw [length_empty]; omega) (Or.inl rfl)
    (fun j _ _ => nth_empty n j) hs.bounds hlB hs.final
  rw [liftAbove_zero] at h
  refine ⟨legalE_of_legalB _ _ h.1, ?_, ?_, erasures_of_legalB _ _ h.1, rfl, ?_⟩
  · rw [h.2.1, Nat.zero_add, set_empty_eq_blk n _ (by omega)]
  · have := h.2.2; have := hs.peak; rw [ones_empty] at *; omega
  · intro i hi; have := hs.bounds i hi; omega

/-- One erasure phase with an arbitrary clean plan for the chain of length `m`
and peak `p − 1`, lifted above the stone `x`, followed by the erasure of `x`. -/
theorem phase_seg' (n p x m : Nat) (s : List Nat) (hp : 2 ≤ p) (hm : 1 ≤ m) (hx : 1 ≤ x)
    (hn : x + m < n) (hs : IsPlay m (p - 1) 0 s) :
    Seg n (blk n x 1 n) (blk n (x + m) 1 n) p 1 (s.length + 1) (liftAbove (x + 1) s ++ [x]) := by
  have hlB := legalB_of_erasures_zero s (empty m) hs.legal (Nat.le_zero.mp hs.budget)
  have hxn : x < n := by omega
  have h := embed (blk n x 1 n) (x + 1) m s hm (by rw [length_blk]; omega)
    (Or.inr (by rw [Nat.add_sub_cancel, nth_blk _ _ _ hxn]; simp))
    (fun j hj1 hj2 => by rw [nth_blk _ _ _ (by omega)]; simp; omega)
    hs.bounds hlB hs.final
  have e1 : x + 1 + m - 1 = x + m := by omega
  rw [e1, set_blk_eq_blk n x _ hn] at h
  have hones : ones (blk n x 1 n) ≤ 1 := ones_blk_le_of_ge n x 1 n (Nat.le_refl _)
  have h1 : Seg n (blk n x 1 n) (blk n x 1 (x + m)) p 0 s.length (liftAbove (x + 1) s) := by
    refine ⟨legalE_of_legalB _ _ h.1, h.2.1, ?_, erasures_of_legalB _ _ h.1, by simp, ?_⟩
    · have := h.2.2; have := hs.peak; omega
    · intro i hi
      simp only [liftAbove, List.mem_map] at hi
      obtain ⟨j, hj, rfl⟩ := hi
      have := hs.bounds j hj; omega
  have h2 := (erase_step n x (x + m) hx (by omega) hn).peak_mono (q' := p) (by omega)
  have := h1.append h2
  rwa [Nat.zero_add] at this

/-- `e` phases in a row. -/
theorem phases_seg' (n p m : Nat) (s : List Nat) (hp : 2 ≤ p) (hm : 1 ≤ m)
    (hs : IsPlay m (p - 1) 0 s) :
    ∀ (e x : Nat), 1 ≤ x → x + e * m < n →
      ∃ t, Seg n (blk n x 1 n) (blk n (x + e * m) 1 n) p e (e * (s.length + 1)) t := by
  intro e
  induction e with
  | zero =>
      intro x hx hn
      refine ⟨[], ?_⟩
      simp only [Nat.zero_mul, Nat.add_zero]
      exact Seg.nil (Nat.le_trans (ones_blk_le_of_ge n x 1 n (Nat.le_refl _)) (by omega))
  | succ e ih =>
      intro x hx hn
      have em : (e + 1) * m = e * m + m := Nat.succ_mul e m
      rw [em] at hn
      have hstep := phase_seg' n p x m s hp hm hx (by omega) hs
      obtain ⟨t, ht⟩ := ih (x + m) (by omega) (by omega)
      have e2 : x + m + e * m = x + (e + 1) * m := by rw [em]; omega
      rw [e2] at ht
      have h := hstep.append ht
      have e3 : 1 + e = e + 1 := by omega
      have e4 : s.length + 1 + e * (s.length + 1) = (e + 1) * (s.length + 1) := by
        rw [Nat.succ_mul]; omega
      rw [e3, e4] at h
      exact ⟨_, h⟩

/-- **The additive upper bound.**  For `p ≥ 2`, a clean plan for `2^(p−1)` with
peak `p` and `a` moves and a clean plan for `2^(p−2)` with peak `p − 1` and
`b` moves give a clean plan for `(e + 2)·2^(p−2)` with peak `p`, `e`
irreversible removals and at most `a + e·(b + 1)` moves. -/
theorem mstar_reach_le (p e a b : Nat) (hp : 2 ≤ p) (ha : MstarLe (2 ^ (p - 1)) p 0 a)
    (hb : MstarLe (2 ^ (p - 2)) (p - 1) 0 b) :
    MstarLe ((e + 2) * 2 ^ (p - 2)) p e (a + e * (b + 1)) := by
  obtain ⟨sA, hA, hAl⟩ := ha
  obtain ⟨sB, hB, hBl⟩ := hb
  have hpos : 1 ≤ 2 ^ (p - 2) := Nat.one_le_two_pow
  have hpow : 2 ^ (p - 1) = 2 ^ (p - 2) + 2 ^ (p - 2) := by
    have : p - 1 = (p - 2) + 1 := by omega
    rw [this, Nat.pow_succ]; omega
  have hmul : (e + 2) * 2 ^ (p - 2) = e * 2 ^ (p - 2) + 2 ^ (p - 2) + 2 ^ (p - 2) := by
    rw [Nat.add_mul]; omega
  have hn1 : 2 ^ (p - 1) ≤ (e + 2) * 2 ^ (p - 2) := by rw [hpow, hmul]; omega
  have h0 := first_seg ((e + 2) * 2 ^ (p - 2)) (2 ^ (p - 1)) p sA (by omega) hn1 hA
  have hx : 1 ≤ 2 ^ (p - 1) - 1 := by rw [hpow]; omega
  have hend : 2 ^ (p - 1) - 1 + e * 2 ^ (p - 2) = (e + 2) * 2 ^ (p - 2) - 1 := by
    rw [hpow, hmul]; omega
  obtain ⟨t, ht⟩ := phases_seg' ((e + 2) * 2 ^ (p - 2)) p (2 ^ (p - 2)) sB hp hpos hB e
    (2 ^ (p - 1) - 1) hx (by rw [hend, hmul]; omega)
  rw [hend] at ht
  have h := h0.append ht
  have h' := h.cast (blk_single_eq_target _ (by rw [hmul]; omega))
  refine ⟨_, ⟨h'.bounds, h'.legal, h'.peak, by rw [h'.eras, Nat.zero_add]; exact Nat.le_refl _,
    h'.exec⟩, ?_⟩
  rw [h'.len]
  exact Nat.add_le_add hAl (Nat.mul_le_mul_left e (Nat.add_le_add_right hBl 1))

/-- Bennett's 9-move plan for the chain of length 4 with peak 3 (`M*(4,3,0) = 9`). -/
theorem play_4_3 : IsPlay 4 3 0 [0, 1, 0, 2, 3, 2, 0, 1, 0] :=
  ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- The 3-move plan for the chain of length 2 with peak 2 (`M*(2,2,0) = 3`). -/
theorem play_2_2 : IsPlay 2 2 0 [0, 1, 0] :=
  ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- Non-vacuity anchor: the construction yields `M*(6,3,1) ≤ 9 + 1·(3 + 1) = 13`,
which is the value in `data/erasure/mstar.csv` (so the bound is attained there). -/
theorem anchor_6_3_1 : MstarLe 6 3 1 13 :=
  mstar_reach_le 3 1 9 3 (by omega) ⟨_, play_4_3, by decide⟩ ⟨_, play_2_2, by decide⟩

end Additive
end ErasurePebbling
