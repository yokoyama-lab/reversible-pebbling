import WorkBridge
namespace Precut
open SpookyRound TraceBridge
variable {n : Nat} {q : Config n} {r : SpookyDP.Result (Config n)}

theorem compute_propagates {pred : Fin n → Fin n → Bool}
    (h : ActionRuns pred q as r) (v u : Fin n) (he : pred v u = true)
    (hs : kind q u ≠ .pebble) (hv : ∃ a ∈ as, firstAt a v ≠ .idle) :
    ∃ b ∈ as, firstAt b u = .pebble := by
  obtain ⟨a,ha,hh⟩ := hv
  obtain ⟨xs,ys,heq⟩ := Descendants.split_mem ha
  subst as
  obtain ⟨b,hb,hc⟩ := compute_before_occurrence xs ys h v u hh he hs
  exact ⟨b,by simp [hb],hc⟩

theorem all_computed (hn : 0 < n) (h : ActionRuns HeapPath.pred q as r)
    (hs : ∀ u, kind q u ≠ .pebble)
    (hr : ∃ a ∈ as, firstAt a ⟨0,hn⟩ = .pebble) :
    ∀ u : Fin n, ∃ a ∈ as, firstAt a u = .pebble := by
  have gen : ∀ k, ∀ u : Fin n, u.val = k → ∃ a ∈ as, firstAt a u = .pebble := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro u hk
      by_cases hz : k = 0
      · have hu : u = ⟨0,hn⟩ := by apply Fin.ext; change u.val=0; omega
        rw [hu]; exact hr
      · let p : Fin n := ⟨(u.val-1)/2,by omega⟩
        obtain ⟨a,ha,hh⟩ := ih p.val (by dsimp [p]; omega) p rfl
        apply compute_propagates h p u
        · simp [HeapPath.pred,p]; omega
        · exact hs u
        · exact ⟨a,ha,by simp [hh]⟩
  intro u
  exact gen u.val u rfl

theorem precut_all (hn : 0 < n)
    (h : ActionRuns HeapPath.pred q (pre ++ a :: post) r)
    (hs : ∀ u, kind q u ≠ .pebble) (hr : firstAt a ⟨0,hn⟩ = .pebble) :
    ∀ u : Fin n, ∃ b ∈ pre ++ [a], firstAt b u = .pebble := by
  have he : pre ++ a :: post = (pre ++ [a]) ++ post := by simp
  rw [he] at h
  obtain ⟨p,t,hp,ht,heq⟩ := split_actions (pre++[a]) post h
  exact all_computed hn hp hs ⟨a,by simp,hr⟩

theorem events_append (v : Fin n) (as bs : List Action) :
    events v (as++bs) = events v as ++ events v bs := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [events,ih]

theorem counts_split (v : Fin n) (as bs : List Action) (e : CutBound.Event) :
    CutBound.count e (events v (as++bs)) =
      CutBound.count e (events v as) + CutBound.count e (events v bs) := by
  simp [events_append,CutBound.count,List.filter_append]
def pairCounts (as : List Action) (v : Fin n) : Nat × Nat :=
  (CutBound.count .compute (events v as), CutBound.count .uncompute (events v as))

theorem selected_exceptions {pred : Fin n → Fin n → Bool}
    (h : ActionRuns pred q as r) (vs : List (Fin n))
    (hs : ∀ v ∈ vs, kind q v ≠ .pebble)
    (hu : ∀ v ∈ vs, ∃ a ∈ as, firstAt a v = .unpebble) :
    ((vs.map (pairCounts as)).map RootCut.bad).sum ≤
      ((vs.map (pairCounts as)).map RootCut.extra).sum := by
  apply RootCut.bad_count_bound
  intro cu hc
  obtain ⟨v,hv,he⟩ := List.mem_map.mp hc
  subst cu
  have hh := RootCut.actual_suffix_charge h v (hs v hv) (hu v hv)
  exact ⟨hh.1,hh.2.1⟩
#print axioms selected_exceptions
#print axioms precut_all
#print axioms counts_split
end Precut
