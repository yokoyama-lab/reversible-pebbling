import SinglePlacementOrder
namespace RemovalOrder
open LocalCertificate ChainTrace

/-- Once the placement budget has been consumed in a prefix, no further
placement of that vertex occurs in the suffix. Valid for every budget. -/
theorem exhausted_placement_budget (v budget : Nat) (pre post : List Event)
    (hpre : budget ≤ pre.countP (isPlacement v))
    (hall : (pre ++ post).countP (isPlacement v) ≤ budget) :
    ∀ f ∈ post, f.place = true → f.vertex ≠ v := by
  have hz : post.countP (isPlacement v) = 0 := by
    rw [List.countP_append] at hall
    omega
  intro f hf hp hv
  have hn := List.countP_eq_zero.mp hz f hf
  exact hn (by simp [isPlacement,hp,hv])

/-- Removal after exhausting a placement budget is final; the order of
all successor events follows from the physical transition relation. -/
theorem successor_before_budget_exhausted_removal
    (erasures final : List Nat) (pre post : List Event) (e f : Event)
    (v budget : Nat) (hv : 0 < v) (hp : e.place = false) (he : e.vertex = v)
    (her : v+1 ∉ erasures)
    (hpre : budget ≤ pre.countP (isPlacement v))
    (hall : (pre ++ e :: post).countP (isPlacement v) ≤ budget)
    (hr : run erasures [] (pre ++ e :: post) = some final)
    (hf : f ∈ pre ++ e :: post) (hfv : f.vertex = v+1) : f ∈ pre := by
  have hn := exhausted_placement_budget v budget pre (e::post) hpre hall
  exact successor_precedes_last_removal erasures final pre post e f v hv hp he her
    (fun g hg => hn g (List.mem_cons_of_mem e hg)) hr hf hfv

/-- Two explicitly located placements consume a two-placement budget.
The intervals may contain arbitrary other events. -/
theorem two_placements_consume_budget (v : Nat) (a b c : List Event) (p q : Event)
    (hp : p.place = true) (hpv : p.vertex = v)
    (hq : q.place = true) (hqv : q.vertex = v) :
    2 ≤ (a ++ p :: (b ++ q :: c)).countP (isPlacement v) := by
  simp only [List.countP_append, List.countP_cons]
  simp [isPlacement,hp,hpv,hq,hqv]
  omega

/-- In a successful empty-start trace with at most two placements of v,
any removal following both placements is after every operation on v+1,
provided v+1 is not an erasure site. -/
theorem successor_before_removal_after_two_placements
    (erasures final : List Nat) (a b c post : List Event) (p q e f : Event)
    (v : Nat) (hv : 0 < v)
    (hp : p.place = true) (hpv : p.vertex = v)
    (hq : q.place = true) (hqv : q.vertex = v)
    (he : e.place = false) (hev : e.vertex = v)
    (her : v+1 ∉ erasures)
    (hall : ((a ++ p :: (b ++ q :: c)) ++ e :: post).countP (isPlacement v) ≤ 2)
    (hr : run erasures [] ((a ++ p :: (b ++ q :: c)) ++ e :: post) = some final)
    (hf : f ∈ (a ++ p :: (b ++ q :: c)) ++ e :: post)
    (hfv : f.vertex = v+1) : f ∈ a ++ p :: (b ++ q :: c) := by
  exact successor_before_budget_exhausted_removal erasures final
    (a ++ p :: (b ++ q :: c)) post e f v 2 hv he hev her
    (two_placements_consume_budget v a b c p q hp hpv hq hqv) hall hr hf hfv

#print axioms exhausted_placement_budget
#print axioms successor_before_budget_exhausted_removal
#print axioms two_placements_consume_budget
#print axioms successor_before_removal_after_two_placements
end RemovalOrder
