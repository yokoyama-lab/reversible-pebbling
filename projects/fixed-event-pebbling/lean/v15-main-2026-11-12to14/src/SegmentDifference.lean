import EventEncoding
import SinglePlacementOrder
import UniqueLifetime
namespace SegmentDifference
open LocalCertificate ChainTrace ChainEventEncoding
abbrev P := RemovalOrder.isPlacement
abbrev R := ChainUniqueLifetime.isRemoval

theorem count_place_event (es : List Event) (v : Nat) :
    es.count ⟨true,v⟩ = es.countP (P v) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨b,w⟩ := e
    cases b <;> simp_all [List.count_cons,List.countP_cons,P,RemovalOrder.isPlacement,beq_iff_eq]

theorem count_remove_event (es : List Event) (v : Nat) :
    es.count ⟨false,v⟩ = es.countP (R v) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨b,w⟩ := e
    cases b <;> simp_all [List.count_cons,List.countP_cons,R,ChainUniqueLifetime.isRemoval,beq_iff_eq]

/-- An event multiset is determined by its per-vertex P/R counts. -/
theorem perm_of_event_counts (xs ys : List Event)
    (hp : ∀ v, xs.countP (P v) = ys.countP (P v))
    (hr : ∀ v, xs.countP (R v) = ys.countP (R v)) : xs.Perm ys := by
  apply List.perm_iff_count.mpr
  intro e
  obtain ⟨b,v⟩ := e
  cases b
  · simpa only [count_remove_event] using hr v
  · simpa only [count_place_event] using hp v

/-- Prefix count differences certify the concrete interval table.
This is the bridge from global cut signatures to local legal languages. -/
theorem segment_perm_of_prefix_differences (pre segment table : List Event)
    (hp : ∀ v, (pre ++ segment).countP (P v) = pre.countP (P v) + table.countP (P v))
    (hr : ∀ v, (pre ++ segment).countP (R v) = pre.countP (R v) + table.countP (R v)) :
    segment.Perm table := by
  apply perm_of_event_counts
  · intro v
    have h := hp v
    rw [List.countP_append] at h
    omega
  · intro v
    have h := hr v
    rw [List.countP_append] at h
    omega

theorem segment_encoded_legal_iff (pre segment table : List Event)
    (initial final erasures : List Nat) (nd : table.Nodup)
    (hp : ∀ v, (pre ++ segment).countP (P v) = pre.countP (P v) + table.countP (P v))
    (hr : ∀ v, (pre ++ segment).countP (R v) = pre.countP (R v) + table.countP (R v)) :
    legal table initial final erasures (encode table segment) ↔
      ∃ after, run erasures initial segment = some after ∧ sameBoard after final = true := by
  exact legal_encode_iff_run table segment initial final erasures nd
    (segment_perm_of_prefix_differences pre segment table hp hr)
#print axioms count_place_event
#print axioms count_remove_event
#print axioms perm_of_event_counts
#print axioms segment_perm_of_prefix_differences
#print axioms segment_encoded_legal_iff
end SegmentDifference
