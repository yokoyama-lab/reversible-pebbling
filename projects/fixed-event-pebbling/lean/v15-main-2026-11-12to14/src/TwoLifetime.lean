import Lifetime
namespace ChainTwoLifetime
open LocalCertificate ChainTrace ChainLifetime

/-- Extract the actual boards surrounding two selected events. -/
theorem two_event_boards (erasures board final : List Nat)
    (pre middle post : List Event) (a b : Event)
    (h : run erasures board (pre ++ a :: (middle ++ b :: post)) = some final) :
    ∃ beforeA afterA beforeB afterB,
      run erasures board pre = some beforeA ∧
      step true erasures beforeA a = some afterA ∧
      run erasures afterA middle = some beforeB ∧
      step true erasures beforeB b = some afterB := by
  rw [run_append] at h
  cases hp : run erasures board pre with
  | none => simp [hp] at h
  | some ba =>
    simp only [hp, Option.bind_some] at h
    cases ha : step true erasures ba a with
    | none => simp [run, ha] at h
    | some aa =>
      have hm : run erasures aa (middle ++ b :: post) = some final := by
        simpa only [run, ha, Option.bind_some] using h
      rw [run_append] at hm
      cases hmid : run erasures aa middle with
      | none => simp [hmid] at hm
      | some bb =>
        simp only [hmid, Option.bind_some] at hm
        cases hb : step true erasures bb b with
        | none => simp [run, hb] at hm
        | some ab => exact ⟨ba, aa, bb, ab, rfl, ha, hmid, hb⟩

/-- Two placements of one vertex in any successful trace require an intervening removal.
No uniqueness or Nodup assumption is needed for this direction. -/
theorem between_placements_exists_removal (erasures board final : List Nat)
    (pre middle post : List Event) (a b : Event)
    (ha : a.place = true) (hb : b.place = true) (same : b.vertex = a.vertex)
    (h : run erasures board (pre ++ a :: (middle ++ b :: post)) = some final) :
    ∃ e ∈ middle, e.place = false ∧ e.vertex = a.vertex := by
  obtain ⟨ba, aa, bb, ab, hp, hsa, hm, hsb⟩ :=
    two_event_boards erasures board final pre middle post a b h
  have present := placement_present erasures ba aa a ha hsa
  have absent : a.vertex ∉ bb := by
    simpa only [same] using ((placement_step erasures bb ab b hb).mp hsb).1
  exact disappearance_requires_removal erasures aa bb middle a.vertex present absent hm

/-- Conversely, on a duplicate-free board two removals require a placement between them. -/
theorem between_removals_exists_placement (erasures board final : List Nat)
    (pre middle post : List Event) (a b : Event) (hn : board.Nodup)
    (ha : a.place = false) (hb : b.place = false) (same : b.vertex = a.vertex)
    (h : run erasures board (pre ++ a :: (middle ++ b :: post)) = some final) :
    ∃ e ∈ middle, e.place = true ∧ e.vertex = a.vertex := by
  obtain ⟨ba, aa, bb, ab, hp, hsa, hm, hsb⟩ :=
    two_event_boards erasures board final pre middle post a b h
  have absent := removal_absent erasures ba aa a (run_nodup erasures board ba pre hn hp) ha hsa
  have present : a.vertex ∈ bb := by
    simpa only [same] using removal_requires_present erasures bb ab b hb hsb
  exact (run_support erasures aa bb middle hm a.vertex present).resolve_left absent

#print axioms two_event_boards
#print axioms between_placements_exists_removal
#print axioms between_removals_exists_placement
/-- Any placement whose vertex is absent finally has a later removal.
In particular this applies to the second placement; no count assumption is needed. -/
theorem placement_before_absent_final_has_removal (erasures board final : List Nat)
    (pre suffix : List Event) (a : Event) (ha : a.place = true)
    (absent : a.vertex ∉ final)
    (h : run erasures board (pre ++ a :: suffix) = some final) :
    ∃ e ∈ suffix, e.place = false ∧ e.vertex = a.vertex := by
  rw [run_append] at h
  cases hp : run erasures board pre with
  | none => simp [hp] at h
  | some before =>
    simp only [hp, Option.bind_some] at h
    cases hs : step true erasures before a with
    | none => simp [run, hs] at h
    | some after =>
      have hr : run erasures after suffix = some final := by
        simpa only [run, hs, Option.bind_some] using h
      exact disappearance_requires_removal erasures after final suffix a.vertex
        (placement_present erasures before after a ha hs) absent hr

#print axioms placement_before_absent_final_has_removal
end ChainTwoLifetime
