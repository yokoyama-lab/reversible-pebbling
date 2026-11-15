import BridgeBase
namespace EdgeBridge
def lift (e : SpookyDP.Result (Fin 2187)) : SpookyDP.Result (SpookyRound.Config 7) :=
  ⟨decode e.state,e.work,e.space⟩

theorem checkOne_sound (i : Fin 2187) (h : checkOne i = true) (r) :
    r ∈ realEdges i ↔ r ∈ tableEdges i := by
  have heq : canon (realEdges i) = canon (tableEdges i) := by simpa [checkOne] using h
  rw [← mem_canon r (realEdges i),heq,mem_canon]

theorem mem_real (i : Fin 2187) (r) : r ∈ realEdges i ↔ SpookyRound.PaperStep pred (decode i) r := by
  rw [← SpookyRound.mem_next]
  change r ∈ (SpookyRound.optActions pred (decode i)).map (SpookyRound.edge (decode i)) ↔ _
  simp only [SpookyRound.next,List.mem_map,SpookyRound.mem_optActions]

theorem step_transfer (hall : ∀ i r, r ∈ realEdges i ↔ r ∈ tableEdges i) (i : Fin 2187)
    (h : SpookyRound.PaperStep pred (decode i) r) :
    ∃ e ∈ NativeTable.next i, lift e = r := by
  have hm := (hall i r).mp ((mem_real i r).mpr h)
  exact List.mem_map.mp hm

theorem transfer_runs (hall : ∀ i r, r ∈ realEdges i ↔ r ∈ tableEdges i)
    (h : SpookyRound.PaperRuns pred d q r) (i : Fin 2187) (hi : decode i = q) :
    ∃ t, SpookyDP.Runs NativeTable.next d i t ∧ lift t = r := by
  induction h generalizing i with
  | zero q =>
    refine ⟨⟨i,0,0⟩,SpookyDP.Runs.zero i,?_⟩
    simp [lift,hi]
  | @step d q e r he hr ih =>
    have he' : SpookyRound.PaperStep pred (decode i) e := by simpa [hi] using he
    obtain ⟨t,ht,hte⟩ := step_transfer hall i he'
    have hst : decode t.state = e.state := congrArg SpookyDP.Result.state hte
    obtain ⟨u,hu,hue⟩ := ih t.state hst
    refine ⟨SpookyDP.prepend t u, SpookyDP.Runs.step ht hu,?_⟩
    have hl : lift (SpookyDP.prepend t u) = SpookyDP.prepend (lift t) (lift u) := rfl
    rw [hl,hte,hue]

def goalCfg (q : SpookyRound.Config 7) : Bool :=
  (List.finRange 7).all fun v => q.peb v == (v.val == 0) && !q.ghost v

theorem goal_decode : ∀ i : Fin 2187, goalCfg (decode i) = true ↔ i = NativeTable.goal := by native_decide

theorem physical_lower (hall : ∀ i r, r ∈ realEdges i ↔ r ∈ tableEdges i)
    (h : SpookyRound.PaperRuns pred d (decode NativeTable.start) r)
    (hg : goalCfg r.state = true) :
    ∃ f ∈ ([⟨5,13,7⟩,⟨7,14,6⟩,⟨8,16,5⟩,⟨9,15,5⟩,⟨12,17,4⟩] : List ClosedFrontier.Cost),
      f.depth ≤ d ∧ f.work ≤ r.work ∧ f.space ≤ r.space := by
  obtain ⟨t,ht,htr⟩ := transfer_runs hall h NativeTable.start rfl
  have hs : decode t.state = r.state := congrArg SpookyDP.Result.state htr
  have hw : t.work = r.work := congrArg SpookyDP.Result.work htr
  have hp : t.space = r.space := congrArg SpookyDP.Result.space htr
  have htgoal : t.state = NativeTable.goal := (goal_decode t.state).mp (by simpa [hs] using hg)
  simpa [hw,hp] using NativeTable.five_point_lower ht htgoal
#print axioms transfer_runs
#print axioms physical_lower
end EdgeBridge
