import TraceBridge
namespace RootCut
open SpookyRound TraceBridge

theorem last_witness (P : α → Prop) (xs : List α) (h : ∃ a ∈ xs, P a) :
    ∃ pre a post, xs = pre ++ a :: post ∧ P a ∧ ∀ b ∈ post, ¬ P b := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
    by_cases ht : ∃ a ∈ xs, P a
    · obtain ⟨pre,a,post,he,hp,hn⟩ := ih ht
      exact ⟨x::pre,a,post,by simp [he],hp,hn⟩
    · have hx : P x := by simpa [ht] using h
      exact ⟨[],x,xs,rfl,hx,by simpa using ht⟩

theorem last_root_cut {pred : Fin n → Fin n → Bool}
    (h : PaperRuns pred d q r) (root : Fin n)
    (hs : kind q root ≠ .pebble) (hf : kind r.state root = .pebble) :
    ∃ pre a post, (pre ++ a :: post).length = d ∧
      ActionRuns pred q (pre ++ a :: post) r ∧
      firstAt a root = .pebble ∧
      (∀ b ∈ post, firstAt b root ≠ .pebble) := by
  obtain ⟨as,hd,ha⟩ := extract_actions h
  obtain ⟨pre,a,post,he,hp,hn⟩ := last_witness (fun a => firstAt a root = .pebble) as
    (compute_action_exists ha root hs hf)
  subst as
  exact ⟨pre,a,post,hd,ha,hp,hn⟩

-- Cut after the chosen occurrence; root children have a real later cleanup.
theorem root_child_cut {pred : Fin n → Fin n → Bool}
    (h : ActionRuns pred q (pre ++ a :: post) r)
    (root u : Fin n) (hne : root ≠ u) (hp : firstAt a root = .pebble)
    (he : pred root u = true) (hf : kind r.state u = .empty) :
    ∃ c t, ActionRuns pred c post t ∧ t.state = r.state ∧
      kind c u ≠ .empty ∧ 1 ≤ CutBound.count .uncompute (events u post) ∧
      (kind c u ≠ .pebble → 1 ≤ CutBound.count .compute (events u post)) := by
  obtain ⟨p,t,hpre,ht,hstate⟩ := split_actions pre (a::post) h
  cases ht with
  | cons hm hg hl htail =>
    rename_i rtail
    have hactive : firstAt a root ≠ .idle := by simp [hp]
    have hnep := dependency_nonempty_after hl root u hne hactive he
    have htfinal : kind rtail.state u = .empty := by simpa [SpookyDP.prepend] using (hstate ▸ hf)
    have tr := actionruns_scalar htail u
    rw [htfinal] at tr
    have hc := CutBound.cleanup_required tr hnep
    have hex := cleanup_action_exists htail u hnep htfinal
    have hmem := (uncompute_in_events u post).mpr hex
    exact ⟨_,_,htail,by simpa [SpookyDP.prepend] using hstate,hnep,hc,
      fun hn => CutBound.missing_requires_recompute tr hmem hn⟩
#print axioms last_root_cut
#print axioms root_child_cut
-- A nonpebbled cut vertex with a mandatory cleanup has both charges.
def extra (cu : Nat × Nat) : Nat := cu.1 + cu.2 - 2
def bad (cu : Nat × Nat) : Nat := if cu = (1,1) then 0 else 1

theorem bad_charge (cu : Nat × Nat) (hc : 1 ≤ cu.1) (hu : 1 ≤ cu.2) :
    bad cu ≤ extra cu := by
  rcases cu with ⟨c,u⟩
  simp only [bad,extra,Prod.mk.injEq] at *
  split <;> omega

theorem bad_count_bound (cs : List (Nat × Nat))
    (h : ∀ cu ∈ cs, 1 ≤ cu.1 ∧ 1 ≤ cu.2) :
    (cs.map bad).sum ≤ (cs.map extra).sum := by
  induction cs with
  | nil => simp
  | cons cu cs ih =>
    have hh := h cu (by simp)
    have hb := bad_charge cu hh.1 hh.2
    have ht := ih (fun x hx => h x (by simp [hx]))
    simp only [List.map_cons,List.sum_cons]
    omega

theorem actual_suffix_charge {pred : Fin n → Fin n → Bool}
    (h : ActionRuns pred q as r) (v : Fin n)
    (hq : kind q v ≠ .pebble)
    (hu : ∃ a ∈ as, firstAt a v = .unpebble) :
    let c := CutBound.count .compute (events v as)
    let u := CutBound.count .uncompute (events v as)
    1 ≤ c ∧ 1 ≤ u ∧ bad (c,u) ≤ extra (c,u) := by
  have hm := (uncompute_in_events v as).mpr hu
  have hc := CutBound.missing_requires_recompute (actionruns_scalar h v) hm hq
  have hu' : 1 ≤ CutBound.count .uncompute (events v as) := by
    unfold CutBound.count
    have hh : CutBound.Event.uncompute ∈ (events v as).filter (fun e => e == .uncompute) := by simp [hm]
    have hh' := List.length_pos_of_mem hh
    omega
  exact ⟨hc,hu',bad_charge _ hc hu'⟩
#print axioms bad_count_bound
#print axioms actual_suffix_charge
end RootCut
