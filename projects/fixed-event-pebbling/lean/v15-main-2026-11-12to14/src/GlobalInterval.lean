import PrefixFormula
import MiddleDifference
namespace FamilyCut
open LocalCertificate ChainTrace ChainFamilyArithmetic

theorem middle_interval_perm
    (k j s : Nat) (erasures : List Nat) (pre middle post nextpre : List Event)
    (t nextt : Event) (hj : j+1 < k) (hs : s = 5+6*j)
    (htp : t.place = true) (htv : t.vertex = s+6)
    (hnp : nextt.place = true) (hnv : nextt.vertex = s+12)
    (splitnext : (pre ++ [t]) ++ middle = nextpre ++ [nextt])
    (model : Trace k erasures (((pre ++ [t]) ++ middle) ++ post)) :
    middle.Perm (MiddleDifference.events s) := by
  have firstModel : Trace k erasures (pre ++ t :: (middle ++ post)) := by
    simpa only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using model
  have nextModel : Trace k erasures (nextpre ++ nextt :: post) := by
    rw [splitnext] at model
    simpa only [List.append_assoc,List.singleton_append] using model
  have counts (v : Nat) (hv : 0 < v) (hvn : v ≤ 5+6*k) :
      middle.countP (P v) = (MiddleDifference.events s).countP (P v) ∧
      middle.countP (R v) = (MiddleDifference.events s).countP (R v) := by
    have a := block_prefix_closed_counts k j s erasures pre (middle ++ post) t
      (by omega) hs htp htv firstModel v hv hvn
    have b := block_prefix_closed_counts k (j+1) (s+6) erasures nextpre post nextt
      hj (by omega) hnp (by omega) nextModel v hv hvn
    have d := MiddleDifference.middle_count_difference j v
    rw [← hs] at d
    change MiddleDifference.prefixP (s+6) v =
      MiddleDifference.prefixP s v + (MiddleDifference.events s).countP (P v) ∧
      MiddleDifference.prefixR (s+6) v =
      MiddleDifference.prefixR s v + (MiddleDifference.events s).countP (R v) at d
    change (pre ++ [t]).countP (P v) = MiddleDifference.prefixP s v ∧
      (pre ++ [t]).countP (R v) = MiddleDifference.prefixR s v at a
    change (nextpre ++ [nextt]).countP (P v) = MiddleDifference.prefixP (s+6) v ∧
      (nextpre ++ [nextt]).countP (R v) = MiddleDifference.prefixR (s+6) v at b
    rw [← splitnext] at b
    simp only [List.countP_append] at a b
    constructor <;> omega
  have middleBound : ∀ e ∈ middle, 0 < e.vertex ∧ e.vertex ≤ 5+6*k := by
    intro e he
    apply model.bounded e
    simp only [List.mem_append]
    exact Or.inl (Or.inr he)
  have tableBound : ∀ e ∈ MiddleDifference.events s, 0 < e.vertex ∧ e.vertex ≤ 5+6*k := by
    intro e he
    simp only [MiddleDifference.events,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst e <;> dsimp <;> constructor <;> omega
  have absentCounts (xs : List Event)
      (hb : ∀ e ∈ xs, 0 < e.vertex ∧ e.vertex ≤ 5+6*k)
      (v : Nat) (hi : ¬(0 < v ∧ v ≤ 5+6*k)) :
      xs.countP (P v) = 0 ∧ xs.countP (R v) = 0 := by
    have ne : ∀ e ∈ xs, e.vertex ≠ v := by
      intro e he hh
      have := hb e he
      omega
    constructor
    · apply List.countP_eq_zero.mpr
      intro e he
      simp [P,RemovalOrder.isPlacement,ne e he]
    · apply List.countP_eq_zero.mpr
      intro e he
      simp [R,ChainUniqueLifetime.isRemoval,ne e he]
  apply SegmentDifference.perm_of_event_counts
  · intro v
    by_cases h : 0 < v ∧ v ≤ 5+6*k
    · exact (counts v h.1 h.2).1
    · rw [(absentCounts middle middleBound v h).1,
        (absentCounts (MiddleDifference.events s) tableBound v h).1]
  · intro v
    by_cases h : 0 < v ∧ v ≤ 5+6*k
    · exact (counts v h.1 h.2).2
    · rw [(absentCounts middle middleBound v h).2,
        (absentCounts (MiddleDifference.events s) tableBound v h).2]
#print axioms middle_interval_perm
end FamilyCut
