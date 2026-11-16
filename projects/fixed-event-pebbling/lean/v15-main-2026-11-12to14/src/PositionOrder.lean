import TwoPlacementOrder
import PlacementOrder
namespace PositionOrder
open LocalCertificate ChainTrace RemovalOrder

/-- Every occurrence is bounded, even when identical raw events repeat. -/
theorem occurrence_before_suffix_exclusion
    (pre suffix : List Event) (f : Event) (i v : Nat)
    (hn : ∀ e ∈ suffix, e.vertex ≠ v)
    (hi : (pre ++ suffix)[i]? = some f) (hv : f.vertex = v) :
    i < pre.length := by
  by_cases h : i < pre.length
  · exact h
  · have hle : pre.length ≤ i := by omega
    rw [List.getElem?_append_right hle] at hi
    exact False.elim (hn f (List.mem_of_getElem? hi) hv)

/-- A physical index version of the final-removal order theorem. Unlike
idxOf, this identifies every chosen occurrence of a repeated event. -/
theorem successor_index_before_exhausted_removal
    (erasures final : List Nat) (pre post : List Event) (e f : Event)
    (v budget i : Nat) (hv : 0 < v) (hp : e.place = false) (he : e.vertex = v)
    (her : v+1 ∉ erasures)
    (hpre : budget ≤ pre.countP (isPlacement v))
    (hall : (pre ++ e :: post).countP (isPlacement v) ≤ budget)
    (hr : run erasures [] (pre ++ e :: post) = some final)
    (hf : (pre ++ e :: post)[i]? = some f) (hfv : f.vertex = v+1) :
    i < pre.length := by
  have hn := exhausted_placement_budget v budget pre (e::post) hpre hall
  rw [run_append] at hr
  cases hs : run erasures [] pre with
  | none => simp [hs] at hr
  | some mid =>
    have hrest : run erasures mid (e :: post) = some final := by simpa [hs] using hr
    have hinv := run_invariants erasures [] mid pre (by simp) hs
    have hb := last_removal_blocks_successor erasures mid final e post v hv hinv.1 hp he her
      (fun g hg => hn g (List.mem_cons_of_mem e hg)) hrest
    apply occurrence_before_suffix_exclusion pre (e::post) f i (v+1) _ hf hfv
    intro g hg
    rcases List.mem_cons.mp hg with hsame | hpost
    · subst g; omega
    · exact hb.1 g hpost

/-- Explicitly indexed removal after the budget is exhausted. This
predicate does not itself assume any successor order. -/
def ExhaustedRemovalAt (word : List Event) (v budget index : Nat) : Prop :=
  ∃ pre post e, word = pre ++ e :: post ∧ pre.length = index ∧
    e.place = false ∧ e.vertex = v ∧ budget ≤ pre.countP (isPlacement v) ∧
    word.countP (isPlacement v) ≤ budget

theorem exhausted_removal_index_order
    (erasures final : List Nat) (word : List Event) (v budget i j : Nat)
    (hv : 0 < v) (her : v+1 ∉ erasures)
    (hr : run erasures [] word = some final)
    (hj : ExhaustedRemovalAt word v budget j)
    (f : Event) (hf : word[i]? = some f) (hfv : f.vertex = v+1) : i < j := by
  obtain ⟨pre,post,e,hw,hj,hp,he,hpre,hall⟩ := hj
  subst word
  rw [← hj]
  exact successor_index_before_exhausted_removal erasures final pre post e f v budget i
    hv hp he her hpre hall hr hf hfv

#print axioms occurrence_before_suffix_exclusion
#print axioms successor_index_before_exhausted_removal
#print axioms exhausted_removal_index_order
theorem exhausted_removal_event (word : List Event) (v budget j : Nat)
    (h : ExhaustedRemovalAt word v budget j) :
    ∃ e, word[j]? = some e ∧ e.vertex = v := by
  obtain ⟨pre,post,e,hw,hj,hp,he,hpre,hall⟩ := h
  subst word
  rw [← hj]
  refine ⟨e, ?_, he⟩
  rw [List.getElem?_append_right (Nat.le_refl _)]
  simp

/-- The whole six-link checkpoint order chain follows from physical
success and explicitly located budget-exhausting removals. Existence
of these certificates for the specific family is a separate obligation. -/
theorem checkpoint_order_chain
    (erasures final : List Nat) (word : List Event) (s rs ra rb rc rd rh pt : Nat)
    (hs : 0 < s) (hr : run erasures [] word = some final)
    (hno : ∀ v, s < v → v ≤ s+5 → v ∉ erasures)
    (hS : ExhaustedRemovalAt word s 1 rs)
    (hA : ExhaustedRemovalAt word (s+1) 2 ra)
    (hB : ExhaustedRemovalAt word (s+2) 1 rb)
    (hC : ExhaustedRemovalAt word (s+3) 2 rc)
    (hD : ExhaustedRemovalAt word (s+4) 1 rd)
    (hH : ExhaustedRemovalAt word (s+5) 1 rh)
    (t : Event) (ht : word[pt]? = some t) (htv : t.vertex = s+6) (htp : t.place = true) :
    pt < rh ∧ rh < rd ∧ rd < rc ∧ rc < rb ∧ rb < ra ∧ ra < rs := by
  obtain ⟨a,ha,hav⟩ := exhausted_removal_event word (s+1) 2 ra hA
  obtain ⟨b,hb,hbv⟩ := exhausted_removal_event word (s+2) 1 rb hB
  obtain ⟨c,hc,hcv⟩ := exhausted_removal_event word (s+3) 2 rc hC
  obtain ⟨d,hd,hdv⟩ := exhausted_removal_event word (s+4) 1 rd hD
  obtain ⟨h,hh,hhv⟩ := exhausted_removal_event word (s+5) 1 rh hH
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · obtain ⟨pre,post,e,hw,hidx,hp,he,hpre,hall⟩ := hH
    subst word
    rw [← hidx]
    exact PlacementOrder.placement_index_before_exhausted_removal erasures final pre post e t
      (s+5) 1 pt (by omega) hp he hpre hall hr ht htp (by omega)
  · exact exhausted_removal_index_order erasures final word (s+4) 1 rh rd
      (by omega) (hno _ (by omega) (by omega)) hr hD h hh (by omega)
  · exact exhausted_removal_index_order erasures final word (s+3) 2 rd rc
      (by omega) (hno _ (by omega) (by omega)) hr hC d hd (by omega)
  · exact exhausted_removal_index_order erasures final word (s+2) 1 rc rb
      (by omega) (hno _ (by omega) (by omega)) hr hB c hc (by omega)
  · exact exhausted_removal_index_order erasures final word (s+1) 2 rb ra
      (by omega) (hno _ (by omega) (by omega)) hr hA b hb (by omega)
  · exact exhausted_removal_index_order erasures final word s 1 ra rs
      hs (hno _ (by omega) (by omega)) hr hS a ha hav
#print axioms exhausted_removal_event
#print axioms checkpoint_order_chain
end PositionOrder
