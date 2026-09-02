import RevPebbling.CutOptimal
import RevPebbling.LiftAbove

/-!
# Exact decomposition of a half-reach (this work)

`HalfReachIn n S t` says that a play of at most `t` moves starts on the
empty `n`-chain, uses at most `S` pebbles, and ends at any configuration
containing the last cell.  The zero-length chain is included explicitly.

The two main theorems are the two directions of the exact min-plus
recurrence

  H(n,S) = min_m (F(m,S) + H(n-m,S-1)).

They are stated at the bounded-cost predicate level, avoiding any convention
for the minimum of an empty set:

* `halfReach_compose` constructs a half-reach from a clean checkpoint and a
  shifted smaller half-reach;
* `halfReach_decompose` cuts an arbitrary half-reach at the maximum, over its
  trace, of the leftmost pebbled cell.  The lower prefix is a clean reach and
  the whole upper restriction is a half-reach with one fewer pebble, while
  their move sets are disjoint.
-/

namespace RevPebbling.HalfReachRecurrence

open RevPebbling.PebblingFoundations RevPebbling.GameReach
open RevPebbling.LiftAbove RevPebbling.PeakRestriction
open RevPebbling.CutAccounting RevPebbling.CutPlays RevPebbling.CutOptimal

/-- A half-reach of an `n`-cell chain in at most `t` moves and peak `S`.
The `n = 0` clause supplies the boundary value `H(0,S)=0`. -/
def HalfReachIn (n S t : Nat) : Prop :=
  n = 0 ∨ ∃ s : List Nat, s.length ≤ t ∧ (∀ i ∈ s, i < n) ∧
    legalB (emptyBoard n) s = true ∧
    nth (execB (emptyBoard n) s) (n - 1) = true ∧
    maxOnes (emptyBoard n) s ≤ S

theorem HalfReachIn.zero (S t : Nat) : HalfReachIn 0 S t := Or.inl rfl

theorem HalfReachIn.mono {n S t t' : Nat} (h : HalfReachIn n S t)
    (ht : t ≤ t') : HalfReachIn n S t' := by
  rcases h with rfl | ⟨s, hlen, hr, hleg, hend, hpk⟩
  · exact HalfReachIn.zero S t'
  · exact Or.inr ⟨s, Nat.le_trans hlen ht, hr, hleg, hend, hpk⟩

/-- A clean reach is in particular a half-reach. -/
theorem halfReach_of_reach {n S t : Nat} (hn : 1 ≤ n) (h : ReachIn n S t) :
    HalfReachIn n S t := by
  obtain ⟨s, hlen, hr, hleg, hex, hpk⟩ := h
  refine Or.inr ⟨s, hlen, hr, hleg, ?_, hpk⟩
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  rw [hex]
  exact RevPebbling.ReachLimit.nth_doneBoard_self j

/-- Raising the pebble budget preserves a half-reach. -/
theorem halfReach_mono_space {n S S' t : Nat} (hS : S ≤ S')
    (h : HalfReachIn n S t) : HalfReachIn n S' t := by
  rcases h with rfl | ⟨s, hlen, hr, hleg, hend, hpk⟩
  · exact HalfReachIn.zero S' t
  · exact Or.inr ⟨s, hlen, hr, hleg, hend, Nat.le_trans hpk hS⟩

/-- **THE CONSTRUCTIVE HALF OF (H).**  Cleanly reach a checkpoint of
length `m`, keep its last pebble as a foundation, and run a shifted
half-reach of length `k` with one fewer pebble. -/
theorem halfReach_compose {m k S tf th : Nat} (hm : 1 ≤ m) (hS : 1 ≤ S)
    (hf : ReachIn m S tf) (hh : HalfReachIn k (S - 1) th) :
    HalfReachIn (m + k) S (tf + th) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using HalfReachIn.mono (halfReach_of_reach hm hf)
      (Nat.le_add_right tf th)
  · rcases hh with hk0 | ⟨u, hulen, hur, huleg, huend, hupk⟩
    · omega
    · obtain ⟨s, hslen, hsr, hsleg, hsex, hspk⟩ := hf
      have hsr' : ∀ i ∈ s, i < (emptyBoard m).length := by
        intro i hi; rw [emptyBoard_length]; exact hsr i hi
      have hsleg' : legalB (emptyBoard (m + k)) s = true := by
        rw [emptyBoard_split, legalB_pad _ _ _ hsr']
        exact hsleg
      have hsboard : execB (emptyBoard (m + k)) s
          = doneBoard m ++ emptyBoard k := by
        rw [emptyBoard_split, execB_pad _ _ _ hsr', hsex]
      have hspeak : maxOnes (emptyBoard (m + k)) s ≤ S := by
        rw [emptyBoard_split, maxOnes_pad _ _ _ hsr', ones_emptyBoard]
        simpa using hspk
      have hdrop : (doneBoard m ++ emptyBoard k).drop m = emptyBoard k := by
        exact List.drop_left' (doneBoard_length m)
      have htake : (doneBoard m ++ emptyBoard k).take m = doneBoard m := by
        exact List.take_left' (doneBoard_length m)
      have hfoundation : nth (doneBoard m ++ emptyBoard k) (m - 1) = true := by
        obtain ⟨a, rfl⟩ : ∃ a, m = a + 1 := ⟨m - 1, by omega⟩
        exact nth_doneBoard_last a (emptyBoard k)
      have huleg' : legalB (doneBoard m ++ emptyBoard k) (liftAbove m u) = true := by
        exact legalB_liftAbove m u _ (Or.inr hfoundation) (by rwa [hdrop])
      have huend' : nth
          (execB (doneBoard m ++ emptyBoard k) (liftAbove m u)) (m + k - 1)
          = true := by
        have hd := execB_liftAbove_drop m u (doneBoard m ++ emptyBoard k)
        rw [hdrop] at hd
        have hnth : nth
            ((execB (doneBoard m ++ emptyBoard k) (liftAbove m u)).drop m)
            (k - 1) = true := by rw [hd]; exact huend
        rw [nth_drop] at hnth
        have : m + (k - 1) = m + k - 1 := by omega
        rwa [this] at hnth
      have hupeak : maxOnes (doneBoard m ++ emptyBoard k) (liftAbove m u) ≤ S := by
        have hp := maxOnes_liftAbove m u (doneBoard m ++ emptyBoard k)
        rw [htake, hdrop] at hp
        obtain ⟨a, rfl⟩ : ∃ a, m = a + 1 := ⟨m - 1, by omega⟩
        rw [ones_doneBoard] at hp
        omega
      refine Or.inr ⟨s ++ liftAbove m u, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [List.length_append, liftAbove_length]
        omega
      · intro i hi
        rcases List.mem_append.mp hi with hi | hi
        · have := hsr i hi; omega
        · obtain ⟨j, hj, rfl⟩ : ∃ j ∈ u, j + m = i := by
            simpa [liftAbove] using hi
          have := hur j hj
          omega
      · rw [legal_append, hsleg', hsboard, huleg']
        simp
      · rw [exec_append, hsboard]
        exact huend'
      · rw [maxOnes_append, hsboard]
        omega

/-- The maximum leftmost pebble is attained at a nonempty configuration,
provided the final configuration is nonempty. -/
theorem midX_attained_some {n : Nat} {s : List Nat}
    (hend : nth (cfg n s s.length) (n - 1) = true) :
    ∃ a, a ≤ s.length ∧ firstOn (cfg n s a) = some (midX n s) := by
  let x := midX n s
  rcases Nat.eq_zero_or_pos x with hx | hx
  · cases hf : firstOn (cfg n s s.length) with
    | none =>
        rw [firstOn_none _ hf (n - 1)] at hend
        simp at hend
    | some w =>
        have hw := midX_ge n s s.length
        rw [hf] at hw
        change w ≤ x at hw
        rw [hx] at hw
        have : w = 0 := by simpa using hw
        subst w
        exact ⟨s.length, Nat.le_refl _, by simpa [x, hx] using hf⟩
  · rcases midX_attained n s with h0 | ⟨a, ha, hval⟩
    · exact absurd h0 (by omega)
    · cases hf : firstOn (cfg n s a) with
      | none => simp [hf] at hval; omega
      | some w =>
          simp only [hf, Option.getD_some] at hval
          subst w
          exact ⟨a, ha, by simpa [x] using hf⟩

/-- **THE DECOMPOSITION HALF OF (H).**  Every positive-length half-reach
contains a clean lower prefix and a whole upper half-reach with one fewer
pebble.  Their lengths add to at most the original time bound. -/
theorem halfReach_decompose {n S t : Nat} (hn : 1 ≤ n) (hS : 1 ≤ S)
    (h : HalfReachIn n S t) :
    ∃ m tf th, 1 ≤ m ∧ m ≤ n ∧ ReachIn m S tf ∧
      HalfReachIn (n - m) (S - 1) th ∧ tf + th ≤ t := by
  rcases h with hn0 | ⟨s, hlen, hr, hleg, hend, hpk⟩
  · omega
  · have hendcfg : nth (cfg n s s.length) (n - 1) = true := by
      unfold cfg
      rw [List.take_of_length_le (Nat.le_refl _)]
      exact hend
    obtain ⟨a, ha, hfirst⟩ := midX_attained_some hendcfg
    let x := midX n s
    let m := x + 1
    have hxlt : x < n := by
      obtain ⟨hon, _⟩ := firstOn_spec _ x (by simpa [x] using hfirst)
      have hlenCfg := nth_true_lt_length hon
      have hcfglen : (cfg n s a).length = n := by
        unfold cfg
        rw [RevPebbling.CutVocabulary.execB_length]
        simp
      rwa [hcfglen] at hlenCfg
    let low := keepBelow m (s.take a)
    let high := shiftAbove x s
    have hlowReach : ReachIn m S low.length := by
      have hlegA : legalB (emptyBoard n) (s.take a) = true := legal_take a hleg
      have htake : (emptyBoard n).take m = emptyBoard m := by
        simp [emptyBoard, m]
        omega
      refine ⟨low, Nat.le_refl _, ?_, ?_, ?_, ?_⟩
      · intro i hi
        have := List.of_mem_filter hi
        simpa [low, keepBelow, m] using this
      · have hl := legalB_keepBelow m (s.take a) (emptyBoard n) hlegA
        rwa [htake] at hl
      · have he := execB_keepBelow m (s.take a) (emptyBoard n)
        rw [htake] at he
        rw [← he]
        change firstOn (execB (emptyBoard n) (s.take a)) = some x at hfirst
        exact lower_cfg_eq_doneBoard hxlt hfirst
      · have hp := maxOnes_keepBelow_le m (emptyBoard n) (s.take a)
        rw [htake] at hp
        have hpt := maxOnes_take_le (emptyBoard n) s a
        change maxOnes (emptyBoard m) low ≤
          maxOnes (emptyBoard n) (s.take a) at hp
        omega
    have hhighHalf : HalfReachIn (n - m) (S - 1) high.length := by
      by_cases hk : n - m = 0
      · exact Or.inl hk
      · refine Or.inr ⟨high, Nat.le_refl _, ?_, ?_, ?_, ?_⟩
        · intro i hi
          simp [high, shiftAbove] at hi
          obtain ⟨j, ⟨hj, hxj⟩, hji⟩ := hi
          have hjn := hr j hj
          omega
        · have hl := legalB_shiftAbove x s (emptyBoard n) hleg
          unfold emptyBoard at hl
          rw [drop_replicate] at hl
          simpa [high, m, emptyBoard] using hl
        · have he := execB_shiftAbove x s (emptyBoard n)
          unfold emptyBoard at he
          rw [drop_replicate] at he
          have hnth : nth ((execB (emptyBoard n) s).drop (x + 1))
              (n - m - 1) = true := by
            rw [nth_drop]
            have : x + 1 + (n - m - 1) = n - 1 := by omega
            rwa [this]
          change nth ((execB (List.replicate n false) s).drop (x + 1))
              (n - m - 1) = true at hnth
          rw [he] at hnth
          simpa [high, m, emptyBoard] using hnth
        · have hp := maxOnes_shiftAbove_midX (n := n) (P := S - 1)
              (s := s) (by
                have hp0 : maxOnes (List.replicate n false) s ≤ S := by
                  simpa [emptyBoard] using hpk
                have hsum : S - 1 + 1 = S := Nat.sub_add_cancel hS
                rw [hsum]
                exact hp0)
          simpa [high, x, m, emptyBoard] using hp
    refine ⟨m, low.length, high.length, by simp [m], by simp [m]; omega,
      hlowReach, hhighHalf, ?_⟩
    have hcut := length_cut x s
    have hprefix : low.length ≤ (keepBelow m s).length := by
      have hsplit : keepBelow m s = low ++ keepBelow m (s.drop a) := by
        dsimp [low]
        rw [← keepBelow_append, List.take_append_drop]
      rw [hsplit, List.length_append]
      omega
    dsimp [high, m] at hcut hprefix ⊢
    omega

/-- **EXACT PREDICATE FORM OF (H).**  For a positive chain and a positive
space bound, a half-reach within time `t` exists exactly when some positive
checkpoint split consists of a clean lower reach and an upper half-reach
whose move counts add to at most `t`.  This is equivalent to the numerical
min-plus recurrence wherever the optimum costs are defined. -/
theorem halfReach_iff_decomposition {n S t : Nat} (hn : 1 ≤ n) (hS : 1 ≤ S) :
    HalfReachIn n S t ↔
      ∃ m tf th, 1 ≤ m ∧ m ≤ n ∧ ReachIn m S tf ∧
        HalfReachIn (n - m) (S - 1) th ∧ tf + th ≤ t := by
  constructor
  · exact halfReach_decompose hn hS
  · rintro ⟨m, tf, th, hm, hmn, hf, hh, htime⟩
    have hc := halfReach_compose hm hS hf hh
    have hlen : m + (n - m) = n := Nat.add_sub_of_le hmn
    rw [hlen] at hc
    exact HalfReachIn.mono hc htime

end RevPebbling.HalfReachRecurrence
