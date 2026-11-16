import HeapPath
namespace WorkBridge
open SpookyRound TraceBridge

def cost (m : Move) : Nat := if m = .idle then 0 else 1

theorem indexed_moves (a : Action) (hl : a.first.length = n) :
    (List.finRange n).map (firstAt a) = a.first := by
  apply List.ext_getElem
  · simp [hl]
  · intro i h1 h2
    simp [firstAt,List.getElem?_eq_getElem,h2]

theorem filtered_cost (ms : List Move) :
    (ms.filter fun m => m != .idle).length = (ms.map cost).sum := by
  induction ms with
  | nil => rfl
  | cons m ms ih => cases m <;> simp_all [cost] <;> omega

theorem indexed_work (a : Action) (hl : a.first.length = n) :
    roundWork a = ((List.finRange n).map fun v => cost (firstAt a v)).sum := by
  rw [roundWork,filtered_cost,← indexed_moves a hl,List.map_map]
  rfl

theorem scalar_cost (v : Fin n) (as : List Action) :
    CutBound.count .compute (events v as) + CutBound.count .uncompute (events v as) =
      (as.map fun a => cost (firstAt a v)).sum := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    cases hm : firstAt a v <;> cases hg : ghostAt a v <;>
      simp_all [events,firstEvent,secondEvent,CutBound.count,cost] <;> omega

theorem work_by_vertices {pred : Fin n → Fin n → Bool}
    (h : ActionRuns pred q as r) :
    r.work = ((List.finRange n).map fun v =>
      CutBound.count .compute (events v as) + CutBound.count .uncompute (events v as)).sum := by
  have hall : ∀ a ∈ as, a.first.length = n := by
    induction h with
    | nil q => simp
    | cons hm hg hl ht ih => intro a ha; simp only [List.mem_cons] at ha; rcases ha with ha|ha; subst a; exact hm; exact ih a ha
  rw [Descendants.actual_work_sum h]
  have he : as.map roundWork = as.map (fun a => ((List.finRange n).map fun v => cost (firstAt a v)).sum) := by
    apply List.map_congr_left
    intro a ha
    exact indexed_work a (hall a ha)
  rw [he,HeapPath.exchange]
  congr 1
  apply List.map_congr_left
  intro v hv
  exact (scalar_cost v as).symm
theorem paper_work_by_vertices {pred : Fin n → Fin n → Bool}
    (h : PaperRuns pred d q r) :
    ∃ as, as.length = d ∧ ActionRuns pred q as r ∧
    r.work = ((List.finRange n).map fun v =>
      CutBound.count .compute (events v as) + CutBound.count .uncompute (events v as)).sum := by
  obtain ⟨as,hd,ha⟩ := extract_actions h
  exact ⟨as,hd,ha,work_by_vertices ha⟩

theorem common_root_cut (hn : 0 < n)
    (h : PaperRuns HeapPath.pred d q r)
    (hs : kind q ⟨0,hn⟩ ≠ .pebble) (hr : kind r.state ⟨0,hn⟩ = .pebble)
    (hf : ∀ u : Fin n, 0 < u.val → kind r.state u = .empty) :
    ∃ pre a post c t, (pre ++ a :: post).length = d ∧
      ActionRuns HeapPath.pred q (pre ++ a :: post) r ∧
      firstAt a ⟨0,hn⟩ = .pebble ∧
      (∀ b ∈ post, firstAt b ⟨0,hn⟩ ≠ .pebble) ∧
      ActionRuns HeapPath.pred c post t ∧ t.state = r.state ∧
      (∀ u : Fin n, 0 < u.val → ∃ b ∈ post, firstAt b u = .unpebble) := by
  obtain ⟨pre,a,post,hd,ha,hroot,hlast⟩ := RootCut.last_root_cut h ⟨0,hn⟩ hs hr
  obtain ⟨p,t,hpre,ht,hstate⟩ := split_actions pre (a::post) ha
  cases ht with
  | cons hm hg hl htail =>
    rename_i rt
    have hfinal : rt.state = r.state := by simpa [SpookyDP.prepend] using hstate
    have hcleanup : ∀ u : Fin n, 0 < u.val → ∃ b ∈ post, firstAt b u = .unpebble := by
      apply HeapPath.heap_cleanup hn htail
      · intro u hu; rw [hfinal]; exact hf u hu
      · intro u hu
        have hh : 0 < u.val ∧ 0 = (u.val-1)/2 := by simpa [HeapPath.pred] using hu
        have hpos := hh.1
        apply cleanup_after_occurrence pre post ha ⟨0,hn⟩ u
        · intro heq; have hh := congrArg Fin.val heq; simp at hh; omega
        · simp [hroot]
        · exact hu
        · exact hf u hpos
    exact ⟨pre,a,post,_,rt,hd,ha,hroot,hlast,htail,hfinal,hcleanup⟩
#print axioms common_root_cut
#print axioms paper_work_by_vertices
#print axioms work_by_vertices
end WorkBridge
