import ActualCheckpoint
import CutEventCounts
namespace BlockProfile
open LocalCertificate ChainTrace ChainLifetime PositionOrder RemovalExistence ReachPrefix ActualCheckpoint
abbrev P := RemovalOrder.isPlacement
abbrev R := ChainUniqueLifetime.isRemoval

theorem repeated_vertex_prefix_counts
    (erasures before after final : List Nat) (pre post : List Event) (t : Event)
    (v j : Nat) (hv : 0 < v) (hlt : v ≤ t.vertex) (htp : t.place = true)
    (hp : run erasures [] pre = some before)
    (hs : step true erasures before t = some after)
    (hr : run erasures [] (pre ++ t :: post) = some final)
    (absent : v ∉ after)
    (hc : (pre ++ t :: post).countP (P v) = 2)
    (hj : ExhaustedRemovalAt (pre ++ t :: post) v 2 j) (hafter : pre.length < j) :
    (pre ++ [t]).countP (P v) = 1 ∧ (pre ++ [t]).countP (R v) = 1 := by
  have seen := after_placement_all_predecessors_seen erasures before after pre t v hv hlt hp hs
  obtain ⟨e,he,hep,hev⟩ := exhausted_removal_get (pre ++ t :: post) v 2 j hj
  have hemem : e ∈ post := by
    rw [List.getElem?_append_right (by omega)] at he
    rcases List.mem_cons.mp (List.mem_of_getElem? he) with hsame | hmem
    · subst e; simp [htp] at hep
    · exact hmem
  have budget : ((pre ++ [t]) ++ post).countP (ChainTwoLifetimeExact.isPlacement v) ≤ 2 := by
    change ((pre ++ [t]) ++ post).countP (P v) ≤ 2
    simpa [List.append_assoc] using Nat.le_of_eq hc
  have cutrun : run erasures [] (pre ++ [t]) = some after := by
    rw [run_append]; simp [hp,run,hs]
  have allrun : run erasures [] ((pre ++ [t]) ++ post) = some final := by
    simpa [List.append_assoc] using hr
  have out := ChainCutEventCounts.absent_cut_exact_prefix_counts erasures [] after final
    (pre ++ [t]) post v (by simp) (by simp) absent seen ⟨e,hemem,hep,hev⟩ budget cutrun allrun
  exact ⟨out.1,out.2.1⟩

theorem block_prefix_event_counts
    (erasures final : List Nat) (pre post : List Event) (t : Event) (s : Nat)
    (hpos : 0 < s) (htp : t.place = true) (htv : t.vertex = s+6)
    (hr : run erasures [] (pre ++ t :: post) = some final)
    (hno : ∀ v, s < v → v ≤ s+5 → v ∉ erasures)
    (hfinal : ∀ v, s ≤ v → v ≤ s+5 → v ∉ final)
    (hcounts : (pre ++ t :: post).countP (P s) = 1 ∧
      (pre ++ t :: post).countP (P (s+1)) = 2 ∧
      (pre ++ t :: post).countP (P (s+2)) = 1 ∧
      (pre ++ t :: post).countP (P (s+3)) = 2 ∧
      (pre ++ t :: post).countP (P (s+4)) = 1 ∧
      (pre ++ t :: post).countP (P (s+5)) = 1)
    (htcount : (pre ++ t :: post).countP (P (s+6)) = 1) :
    (∀ v ∈ [s,s+2,s+4,s+5,s+6],
      (pre ++ [t]).countP (P v) = 1 ∧ (pre ++ [t]).countP (R v) = 0) ∧
    ((pre ++ [t]).countP (P (s+1)) = 1 ∧ (pre ++ [t]).countP (R (s+1)) = 1) ∧
    ((pre ++ [t]).countP (P (s+3)) = 1 ∧ (pre ++ [t]).countP (R (s+3)) = 1) := by
  obtain ⟨before,after,hp,hs,hboard⟩ := actual_checkpoint_board erasures final pre post t s
    hpos htp htv hr hno hfinal hcounts
  have ht : (pre ++ t :: post)[pre.length]? = some t := by
    rw [List.getElem?_append_right (Nat.le_refl _)]; simp
  obtain ⟨rs,ra,rb,rc,rd,rh,hS,hA,hB,hC,hD,hH,h0,h1,h2,h3,h4,h5⟩ :=
    checkpoint_order_chain_exists erasures final (pre ++ t :: post) s pre.length
      hpos hr hno hfinal hcounts t ht htv htp
  obtain ⟨cs,ca,cb,cc,cd,ch⟩ := hcounts
  have absentA : s+1 ∉ after := by
    rw [hboard]; simp only [List.mem_cons,List.not_mem_nil,or_false]; omega
  have absentC : s+3 ∉ after := by
    rw [hboard]; simp only [List.mem_cons,List.not_mem_nil,or_false]; omega
  refine ⟨?_,?_,?_⟩
  · intro v hv
    have present := (hboard v).mpr hv
    have cv : (pre ++ t :: post).countP (P v) = 1 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
      rcases hv with h | h | h | h | h <;> subst v <;> assumption
    apply ChainCutEventCounts.live_cut_exact_prefix_counts erasures [] after (pre ++ [t]) post v
      (by simp) (by simp) present
    · change ((pre ++ [t]) ++ post).countP (P v) ≤ 1
      simpa [List.append_assoc] using Nat.le_of_eq cv
    · rw [run_append]; simp [hp,run,hs]
  · exact repeated_vertex_prefix_counts erasures before after final pre post t (s+1) ra
      (by omega) (by omega) htp hp hs hr absentA ca hA (by omega)
  · exact repeated_vertex_prefix_counts erasures before after final pre post t (s+3) rc
      (by omega) (by omega) htp hp hs hr absentC cc hC (by omega)
#print axioms repeated_vertex_prefix_counts
#print axioms block_prefix_event_counts
end BlockProfile
