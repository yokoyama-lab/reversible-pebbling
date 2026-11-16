import TwoProjection
namespace ChainCutPresence
open LocalCertificate ChainTrace ChainUniqueLifetime ChainTwoLifetimeExact

/-- A future removal with no intervening placement forces presence at the cut. -/
theorem future_removal_requires_initial_presence (erasures board final : List Nat)
    (suffix : List Event) (v : Nat)
    (noP : ∀ e ∈ suffix, e.place = true → e.vertex ≠ v)
    (hasR : ∃ e ∈ suffix, e.place = false ∧ e.vertex = v)
    (hr : run erasures board suffix = some final) : v ∈ board := by
  by_cases hm : v ∈ board
  · exact hm
  · have hz := absent_no_placement_no_removal erasures board final suffix v hm noP hr
    obtain ⟨e,he,hp,hv⟩ := hasR
    have pos : 0 < suffix.countP (isRemoval v) :=
      List.countP_pos_iff.mpr ⟨e,he,by simp [isRemoval,hp,hv]⟩
    omega

/-- A placement in the pre exhausts an at-most-one placement budget. -/
theorem prefix_placement_exhausts_one (pre suffix : List Event) (v : Nat)
    (hasP : ∃ e ∈ pre, e.place = true ∧ e.vertex = v)
    (budget : (pre ++ suffix).countP (isPlacement v) ≤ 1) :
    ∀ e ∈ suffix, e.place = true → e.vertex ≠ v := by
  obtain ⟨e,he,hp,hv⟩ := hasP
  have pos : 0 < pre.countP (isPlacement v) :=
    List.countP_pos_iff.mpr ⟨e,he,by simp [isPlacement,hp,hv]⟩
  have hz : suffix.countP (isPlacement v) = 0 := by
    rw [List.countP_append] at budget
    omega
  exact zero_placements v suffix hz

/-- Cut-state liveness from a past placement and a future removal.
The successful pre identifies the cut board; the placement budget is global. -/
theorem single_placement_cut_presence (erasures initial cut final : List Nat)
    (pre suffix : List Event) (v : Nat)
    (hasP : ∃ e ∈ pre, e.place = true ∧ e.vertex = v)
    (budget : (pre ++ suffix).countP (isPlacement v) ≤ 1)
    (hasR : ∃ e ∈ suffix, e.place = false ∧ e.vertex = v)
    (hp : run erasures initial pre = some cut)
    (hr : run erasures initial (pre ++ suffix) = some final) : v ∈ cut := by
  have hs : run erasures cut suffix = some final := by
    rw [run_append, hp] at hr
    exact hr
  exact future_removal_requires_initial_presence erasures cut final suffix v
    (prefix_placement_exhausts_one pre suffix v hasP budget) hasR hs

/-- Simultaneous liveness for any family of single-placement vertices. -/
theorem single_placement_family_cut_presence (erasures initial cut final : List Nat)
    (pre suffix : List Event) (vertices : List Nat)
    (hasP : ∀ v ∈ vertices, ∃ e ∈ pre, e.place = true ∧ e.vertex = v)
    (budget : ∀ v ∈ vertices, (pre ++ suffix).countP (isPlacement v) ≤ 1)
    (hasR : ∀ v ∈ vertices, ∃ e ∈ suffix, e.place = false ∧ e.vertex = v)
    (hp : run erasures initial pre = some cut)
    (hr : run erasures initial (pre ++ suffix) = some final) :
    ∀ v ∈ vertices, v ∈ cut := by
  intro v hv
  exact single_placement_cut_presence erasures initial cut final pre suffix v
    (hasP v hv) (budget v hv) (hasR v hv) hp hr

#print axioms future_removal_requires_initial_presence
#print axioms prefix_placement_exhausts_one
#print axioms single_placement_cut_presence
#print axioms single_placement_family_cut_presence
end ChainCutPresence
