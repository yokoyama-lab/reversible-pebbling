import FamilyGlobalCounts
namespace FamilyCut
open LocalCertificate ChainTrace ChainFamilyArithmetic

theorem block_prefix_closed_counts
    (k j s : Nat) (erasures : List Nat) (pre post : List Event) (t : Event)
    (hj : j < k) (hs : s = 5+6*j) (htp : t.place = true) (htv : t.vertex = s+6)
    (model : Trace k erasures (pre ++ t :: post)) (v : Nat) (hv : 0 < v)
    (hvn : v ≤ 5+6*k) :
    (pre ++ [t]).countP (P v) =
      (if v < s then placementCount v else if v ≤ s+6 then 1 else 0) ∧
    (pre ++ [t]).countP (R v) =
      (if v < s then placementCount v else if v = s+1 ∨ v = s+3 then 1 else 0) := by
  by_cases hl : v < s
  · simpa only [if_pos hl] using
      left_prefix_complete_counts k j s erasures pre post t hj hs htp htv model v hv hl
  have sig := all_block_cut_signature k j s erasures pre post t hj hs htp htv model
  obtain ⟨board,left,right,stable,one,three⟩ := sig
  by_cases hr : v ≤ s+6
  · have cases : v = s ∨ v = s+1 ∨ v = s+2 ∨ v = s+3 ∨
        v = s+4 ∨ v = s+5 ∨ v = s+6 := by omega
    rcases cases with h | h | h | h | h | h | h
    · subst v
      simpa [show ¬s < s by omega, show ¬(s = s+1 ∨ s = s+3) by omega] using stable s (by simp)
    · subst v
      simpa [show ¬s+1 < s by omega, show s+1 ≤ s+6 by omega] using one
    · subst v
      simpa [show ¬s+2 < s by omega, show s+2 ≤ s+6 by omega,
        show ¬(s+2 = s+1 ∨ s+2 = s+3) by omega] using stable (s+2) (by simp)
    · subst v
      simpa [show ¬s+3 < s by omega, show s+3 ≤ s+6 by omega] using three
    · subst v
      simpa [show ¬s+4 < s by omega, show s+4 ≤ s+6 by omega,
        show ¬(s+4 = s+1 ∨ s+4 = s+3) by omega] using stable (s+4) (by simp)
    · subst v
      simpa [show ¬s+5 < s by omega, show s+5 ≤ s+6 by omega,
        show ¬(s+5 = s+1 ∨ s+5 = s+3) by omega] using stable (s+5) (by simp)
    · subst v
      simpa [show ¬s+6 < s by omega,
        show ¬(s+6 = s+1 ∨ s+6 = s+3) by omega] using stable (s+6) (by simp)
  · have absent : ∀ e ∈ pre ++ [t], e.vertex ≠ v := by
      intro e he
      rcases List.mem_append.mp he with hp | ht
      · have := right e hp; omega
      · have et : e = t := by simpa using ht
        subst e
        omega
    have pc : (pre ++ [t]).countP (P v) = 0 := by
      apply List.countP_eq_zero.mpr
      intro e he
      simp [P, RemovalOrder.isPlacement, absent e he]
    have rc : (pre ++ [t]).countP (R v) = 0 := by
      apply List.countP_eq_zero.mpr
      intro e he
      simp [R, ChainUniqueLifetime.isRemoval, absent e he]
    simpa [hl,hr,show ¬(v=s+1 ∨ v=s+3) by omega] using And.intro pc rc

/-- Closed placement count after the checkpoint at s+6. -/
def prefixPCount (s v : Nat) : Nat :=
  if v < s then placementCount v else if v ≤ s+6 then 1 else 0

/-- Closed removal count after the checkpoint at s+6. -/
def prefixRCount (s v : Nat) : Nat :=
  if v < s then placementCount v else if v = s+1 ∨ v = s+3 then 1 else 0

theorem block_prefix_P_count
    (k j s : Nat) (erasures : List Nat) (pre post : List Event) (t : Event)
    (hj : j < k) (hs : s = 5+6*j) (htp : t.place = true) (htv : t.vertex = s+6)
    (model : Trace k erasures (pre ++ t :: post)) (v : Nat) (hv : 0 < v)
    (hvn : v ≤ 5+6*k) :
    (pre ++ [t]).countP (P v) = prefixPCount s v :=
  (block_prefix_closed_counts k j s erasures pre post t hj hs htp htv model v hv hvn).1

theorem block_prefix_R_count
    (k j s : Nat) (erasures : List Nat) (pre post : List Event) (t : Event)
    (hj : j < k) (hs : s = 5+6*j) (htp : t.place = true) (htv : t.vertex = s+6)
    (model : Trace k erasures (pre ++ t :: post)) (v : Nat) (hv : 0 < v)
    (hvn : v ≤ 5+6*k) :
    (pre ++ [t]).countP (R v) = prefixRCount s v :=
  (block_prefix_closed_counts k j s erasures pre post t hj hs htp htv model v hv hvn).2

#print axioms block_prefix_P_count
#print axioms block_prefix_R_count
#print axioms block_prefix_closed_counts
end FamilyCut
