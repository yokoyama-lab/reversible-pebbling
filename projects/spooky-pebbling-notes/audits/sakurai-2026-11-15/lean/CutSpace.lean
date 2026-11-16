import Exceptions
namespace CutSpace
open SpookyRound TraceBridge
variable {n : Nat} {q : Config n} {r : SpookyDP.Result (Config n)}

def pebs (c : Config n) : Nat := ((List.finRange n).map fun v => if c.peb v then 1 else 0).sum

theorem filter_sum (xs : List α) (p : α → Bool) :
    (xs.filter p).length = (xs.map fun x => if p x then 1 else 0).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases hp : p x <;> simp_all <;> omega

theorem after_space (q : Config n) (a : Action) : pebs (afterRound q a) ≤ roundSpace q a := by
  rw [roundSpace,filter_sum]
  apply Exceptions.sum_le
  intro v hv
  cases hp : q.peb v <;> cases ht : (afterFirst q a).peb v <;>
    cases hg : ghostAt a v <;> simp [afterRound,hp,ht,hg]

theorem occurrence (pre post : List Action) {pred : Fin n → Fin n → Bool}
    (h : ActionRuns pred q (pre ++ a :: post) r) :
    ∃ c t, ActionRuns pred (afterRound c a) post t ∧ t.state = r.state ∧
      roundSpace c a ≤ r.space := by
  induction pre generalizing q r with
  | nil =>
    cases h with
    | cons hm hg hl ht => exact ⟨_,_,ht,rfl,Nat.le_max_left _ _⟩
  | cons b pre ih =>
    cases h with
    | cons hm hg hl ht =>
      obtain ⟨c,t,hc,hs,hb⟩ := ih ht
      exact ⟨c,t,hc,hs,Nat.le_trans hb (Nat.le_max_right _ _)⟩

theorem root_stays {pred : Fin n → Fin n → Bool}
    (h : ActionRuns pred c post t) (root : Fin n)
    (hf : kind t.state root = .pebble)
    (hn : ∀ a ∈ post, firstAt a root ≠ .pebble) : c.peb root = true := by
  by_cases hp : c.peb root = true
  · exact hp
  · have hs : kind c root ≠ .pebble := by cases hg : c.ghost root <;> simp [kind,hp,hg]
    obtain ⟨a,ha,hh⟩ := compute_action_exists h root hs hf
    exact False.elim (hn a ha hh)

theorem account_pebs (pre post : List Action) (c : Config n) (root : Fin n) :
    CutBound.pebbles (Exceptions.accounts pre post c root) = pebs c := by
  simp [CutBound.pebbles,Exceptions.accounts,pebs,List.map_map,Function.comp_def]

-- Entire exception bound from original PaperRuns work and union-space budgets.
theorem paper_exception_bound (hn : 0 < n)
    (h : PaperRuns HeapPath.pred d q r)
    (hs : ∀ u, kind q u ≠ .pebble)
    (hr : kind r.state ⟨0,hn⟩ = .pebble)
    (hf : ∀ u : Fin n, 0 < u.val → kind r.state u = .empty)
    (hw : r.work ≤ 3*n+e) (hspace : r.space ≤ s) :
    ∃ pre a post c, (pre ++ a :: post).length = d ∧
      ActionRuns HeapPath.pred q (pre ++ a :: post) r ∧
      c.peb ⟨0,hn⟩ = true ∧ pebs c ≤ s ∧
      Exceptions.removed (Exceptions.accounts (pre++[a]) post c ⟨0,hn⟩) ≤ e+2*s+1 := by
  obtain ⟨pre,a,post,c0,t0,hd,ha,hroot,hlast,ht0,hfinal0,hclean⟩ :=
    WorkBridge.common_root_cut hn h (hs _) hr hf
  obtain ⟨c,t,ht,hfinal,hsp⟩ := occurrence pre post ha
  have hrootcut : (afterRound c a).peb ⟨0,hn⟩ = true := by
    apply root_stays ht _ _ hlast
    rw [hfinal]; exact hr
  have hpebs : pebs (afterRound c a) ≤ s := Nat.le_trans (after_space c a) (Nat.le_trans hsp hspace)
  refine ⟨pre,a,post,afterRound c a,hd,ha,hrootcut,hpebs,?_⟩
  apply Exceptions.semantic_exception_bound (pre := pre++[a]) (post := post) (c := afterRound c a)
  · simpa using ha
  · exact ht
  · exact hrootcut
  · exact Precut.precut_all hn ha hs hroot
  · intro u hu
    apply hclean u
    have hh : u.val ≠ 0 := by intro hz; apply hu; apply Fin.ext; exact hz
    omega
  · exact hw
  · rw [account_pebs]; exact hpebs
#print axioms paper_exception_bound
end CutSpace
