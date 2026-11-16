import TwoPlacementOrder
namespace PlacementOrder
open LocalCertificate ChainTrace RemovalOrder

theorem absent_blocks_child_placements
    (erasures board final : List Nat) (es : List Event) (v : Nat)
    (hv : 0 < v) (hb : v ∉ board)
    (hn : ∀ e ∈ es, e.place = true → e.vertex ≠ v)
    (hr : run erasures board es = some final) :
    ∀ e ∈ es, e.place = true → e.vertex ≠ v+1 := by
  induction es generalizing board with
  | nil => simp
  | cons e es ih =>
    cases hs : step true erasures board e with
    | none => simp [run,hs] at hr
    | some mid =>
      have hm : v ∉ mid := by
        intro hmem
        rcases step_support erasures board mid e hs v hmem with hmem | hnew
        · exact hb hmem
        · exact hn e (by simp) hnew.1 hnew.2
      have ht := ih mid hm (fun f hf => hn f (List.mem_cons_of_mem e hf))
        (by simpa [run,hs] using hr)
      intro f hf hp hfval
      rcases List.mem_cons.mp hf with hh | hh
      · subst f
        have hd := (placement_step erasures board mid e hp).mp hs
        rcases hd.2.1 with h1 | hm
        · omega
        · apply hb
          simpa [hfval] using hm
      · exact ht f hh hp hfval

/-- Child placement needs its predecessor even when the child is erasable. -/
theorem placement_index_before_exhausted_removal
    (erasures final : List Nat) (pre post : List Event) (e f : Event)
    (v budget i : Nat) (hv : 0 < v) (hp : e.place = false) (he : e.vertex = v)
    (hpre : budget ≤ pre.countP (isPlacement v))
    (hall : (pre ++ e :: post).countP (isPlacement v) ≤ budget)
    (hr : run erasures [] (pre ++ e :: post) = some final)
    (hf : (pre ++ e :: post)[i]? = some f) (hfp : f.place = true)
    (hfv : f.vertex = v+1) : i < pre.length := by
  have hn := exhausted_placement_budget v budget pre (e::post) hpre hall
  rw [run_append] at hr
  cases hs : run erasures [] pre with
  | none => simp [hs] at hr
  | some mid =>
    have hrest : run erasures mid (e :: post) = some final := by simpa [hs] using hr
    have hinv := run_invariants erasures [] mid pre (by simp) hs
    cases ht : step true erasures mid e with
    | none => simp [run,ht] at hrest
    | some after =>
      have ha : v ∉ after := by
        rw [removal_step_after erasures mid after e hp ht, he]
        simp [hinv.1.mem_erase_iff]
      have hb := absent_blocks_child_placements erasures after final post v hv ha
        (fun g hg => hn g (List.mem_cons_of_mem e hg))
        (by simpa [run,ht] using hrest)
      by_cases hi : i < pre.length
      · exact hi
      · have hle : pre.length ≤ i := by omega
        rw [List.getElem?_append_right hle] at hf
        rcases List.mem_cons.mp (List.mem_of_getElem? hf) with hh | hh
        · subst f; simp [hp] at hfp
        · exact False.elim (hb f hh hfp hfv)
#print axioms absent_blocks_child_placements
#print axioms placement_index_before_exhausted_removal
end PlacementOrder
