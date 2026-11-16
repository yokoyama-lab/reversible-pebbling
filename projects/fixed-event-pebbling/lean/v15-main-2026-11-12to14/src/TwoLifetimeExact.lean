import UniqueLifetime
namespace ChainTwoLifetimeExact
open LocalCertificate ChainTrace ChainLifetime ChainTwoLifetime ChainUniqueLifetime

def isPlacement (v : Nat) (e : Event) : Bool := e.place && (e.vertex == v)

theorem zero_placements (v : Nat) (es : List Event)
    (hz : es.countP (isPlacement v) = 0) :
    ∀ e ∈ es, e.place = true → e.vertex ≠ v := by
  intro e he hp hv
  exact (List.countP_eq_zero.mp hz e he) (by simp [isPlacement, hp, hv])

/-- Two explicit placements exhaust the budget, so each intervening region
has zero placements of the chosen vertex. -/
theorem gaps_no_placements (v : Nat) (a b c : List Event) (p q : Event)
    (hp : p.place = true) (hpv : p.vertex = v)
    (hq : q.place = true) (hqv : q.vertex = v)
    (budget : (a ++ p :: (b ++ q :: c)).countP (isPlacement v) ≤ 2) :
    a.countP (isPlacement v) = 0 ∧ b.countP (isPlacement v) = 0 ∧
      c.countP (isPlacement v) = 0 := by
  simp only [List.countP_append, List.countP_cons] at budget
  simp only [isPlacement, hp, hpv, hq, hqv, BEq.rfl, Bool.and_self, ite_true] at budget
  omega

/-- Exact removal counts in the three gaps around the two placements.
This is physical trace semantics, not enumeration of local words. -/
theorem two_lifetimes_exact_gap_counts (erasures board final : List Nat)
    (v : Nat) (a b c : List Event) (p q : Event)
    (nd : board.Nodup) (initialAbsent : v ∉ board) (finalAbsent : v ∉ final)
    (hp : p.place = true) (hpv : p.vertex = v)
    (hq : q.place = true) (hqv : q.vertex = v)
    (budget : (a ++ p :: (b ++ q :: c)).countP (isPlacement v) ≤ 2)
    (hr : run erasures board (a ++ p :: (b ++ q :: c)) = some final) :
    a.countP (isRemoval v) = 0 ∧ b.countP (isRemoval v) = 1 ∧
      c.countP (isRemoval v) = 1 := by
  obtain ⟨za, zb, zc⟩ := gaps_no_placements v a b c p q hp hpv hq hqv budget
  obtain ⟨bp, ap, bq, aq, hra, hsp, hrb, hsq⟩ :=
    two_event_boards erasures board final a b c p q hr
  have hrc : run erasures aq c = some final := by
    rw [run_append] at hr
    simp only [hra, Option.bind_some, run, hsp] at hr
    rw [run_append] at hr
    simpa only [hrb, Option.bind_some, run, hsq] using hr
  have nda := run_nodup erasures board bp a nd hra
  have ndap := step_nodup erasures bp ap p nda hsp
  have ndbq := run_nodup erasures ap bq b ndap hrb
  have ndaq := step_nodup erasures bq aq q ndbq hsq
  have ca := absent_no_placement_no_removal erasures board bp a v initialAbsent
    (zero_placements v a za) hra
  have ub := no_placement_at_most_one_removal erasures ap bq b v ndap
    (zero_placements v b zb) hrb
  have uc := no_placement_at_most_one_removal erasures aq final c v ndaq
    (zero_placements v c zc) hrc
  have presentp : v ∈ ap := hpv ▸ placement_present erasures bp ap p hp hsp
  have absentq : v ∉ bq := hqv ▸ ((placement_step erasures bq aq q hq).mp hsq).1
  obtain ⟨e, he, hep, hev⟩ := disappearance_requires_removal erasures ap bq b v presentp absentq hrb
  have lb : 0 < b.countP (isRemoval v) := List.countP_pos_iff.mpr
    ⟨e, he, by simp [isRemoval, hep, hev]⟩
  have presentq : v ∈ aq := hqv ▸ placement_present erasures bq aq q hq hsq
  obtain ⟨f, hf, hfp, hfv⟩ := disappearance_requires_removal erasures aq final c v presentq finalAbsent hrc
  have lc : 0 < c.countP (isRemoval v) := List.countP_pos_iff.mpr
    ⟨f, hf, by simp [isRemoval, hfp, hfv]⟩
  exact ⟨ca, by omega, by omega⟩

#print axioms zero_placements
#print axioms gaps_no_placements
#print axioms two_lifetimes_exact_gap_counts
end ChainTwoLifetimeExact
