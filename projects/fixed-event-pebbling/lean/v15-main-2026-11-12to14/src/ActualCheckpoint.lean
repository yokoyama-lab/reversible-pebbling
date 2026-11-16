import RemovalExistence
import ReachPrefix
import CutPresence
import CheckpointCapacity
namespace ActualCheckpoint
open LocalCertificate ChainTrace ChainLifetime RemovalOrder PositionOrder RemovalExistence ReachPrefix

theorem exhausted_removal_get (word : List Event) (v budget j : Nat)
    (h : ExhaustedRemovalAt word v budget j) :
    ∃ e, word[j]? = some e ∧ e.place = false ∧ e.vertex = v := by
  obtain ⟨pre,post,e,hw,hj,hp,he,hpre,hall⟩ := h
  subst word
  rw [← hj]
  refine ⟨e, ?_,hp,he⟩
  rw [List.getElem?_append_right (Nat.le_refl _)]
  simp

theorem cut_single_vertex_present
    (erasures before after final : List Nat) (pre post : List Event) (t : Event)
    (v j : Nat) (hv : 0 < v) (hlt : v ≤ t.vertex) (htp : t.place = true)
    (hp : run erasures [] pre = some before)
    (hs : step true erasures before t = some after)
    (hr : run erasures [] (pre ++ t :: post) = some final)
    (hc : (pre ++ t :: post).countP (isPlacement v) = 1)
    (hj : ExhaustedRemovalAt (pre ++ t :: post) v 1 j) (hafter : pre.length < j) :
    v ∈ after := by
  have hseen := after_placement_all_predecessors_seen erasures before after pre t v hv hlt hp hs
  obtain ⟨e,he,hep,hev⟩ := exhausted_removal_get (pre ++ t :: post) v 1 j hj
  have hemem : e ∈ post := by
    rw [List.getElem?_append_right (by omega)] at he
    rcases List.mem_cons.mp (List.mem_of_getElem? he) with hsame | hmem
    · subst e; simp [htp] at hep
    · exact hmem
  apply ChainCutPresence.single_placement_cut_presence erasures [] after final (pre ++ [t]) post v hseen
  · change ((pre ++ [t]) ++ post).countP (isPlacement v) ≤ 1
    simpa [List.append_assoc] using (Nat.le_of_eq hc)
  · exact ⟨e,hemem,hep,hev⟩
  · rw [run_append]; simp [hp,run,hs]
  · simpa [List.append_assoc] using hr

/-- A concrete physical checkpoint: no assumed lifetime interpretation,
no assumed removal-order certificates, and no assumed five-vertex liveness. -/
theorem actual_checkpoint_board
    (erasures final : List Nat) (pre post : List Event) (t : Event) (s : Nat)
    (hpos : 0 < s) (htp : t.place = true) (htv : t.vertex = s+6)
    (hr : run erasures [] (pre ++ t :: post) = some final)
    (hno : ∀ v, s < v → v ≤ s+5 → v ∉ erasures)
    (hfinal : ∀ v, s ≤ v → v ≤ s+5 → v ∉ final)
    (hcounts : (pre ++ t :: post).countP (isPlacement s) = 1 ∧
      (pre ++ t :: post).countP (isPlacement (s+1)) = 2 ∧
      (pre ++ t :: post).countP (isPlacement (s+2)) = 1 ∧
      (pre ++ t :: post).countP (isPlacement (s+3)) = 2 ∧
      (pre ++ t :: post).countP (isPlacement (s+4)) = 1 ∧
      (pre ++ t :: post).countP (isPlacement (s+5)) = 1) :
    ∃ before after, run erasures [] pre = some before ∧
      step true erasures before t = some after ∧
      (∀ v, v ∈ after ↔ v ∈ [s,s+2,s+4,s+5,s+6]) := by
  have ht : (pre ++ t :: post)[pre.length]? = some t := by
    rw [List.getElem?_append_right (Nat.le_refl _)]
    simp
  obtain ⟨rs,ra,rb,rc,rd,rh,hS,hA,hB,hC,hD,hH,hchain⟩ :=
    checkpoint_order_chain_exists erasures final (pre ++ t :: post) s pre.length
      hpos hr hno hfinal hcounts t ht htv htp
  have hrun := hr
  rw [run_append] at hrun
  cases hp : run erasures [] pre with
  | none => simp [hp] at hrun
  | some before =>
    have hrest : run erasures before (t :: post) = some final := by simpa [hp] using hrun
    cases hs : step true erasures before t with
    | none => simp [run,hs] at hrest
    | some after =>
      obtain ⟨cs,ca,cb,cc,cd,ch⟩ := hcounts
      obtain ⟨h0,h1,h2,h3,h4,h5⟩ := hchain
      have aliveS := cut_single_vertex_present erasures before after final pre post t s rs
        hpos (by omega) htp hp hs hr cs hS (by omega)
      have aliveB := cut_single_vertex_present erasures before after final pre post t (s+2) rb
        (by omega) (by omega) htp hp hs hr cb hB (by omega)
      have aliveD := cut_single_vertex_present erasures before after final pre post t (s+4) rd
        (by omega) (by omega) htp hp hs hr cd hD (by omega)
      have aliveH := cut_single_vertex_present erasures before after final pre post t (s+5) rh
        (by omega) (by omega) htp hp hs hr ch hH (by omega)
      have aliveT : s+6 ∈ after := by simpa [htv] using placement_present erasures before after t htp hs
      refine ⟨before,after,rfl,hs,?_⟩
      apply CheckpointCapacity.saturated_board [s,s+2,s+4,s+5,s+6] after
        (CheckpointCapacity.forcedVertices_distinct s)
      · intro v hv
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
        rcases hv with h | h | h | h | h <;> subst v <;> assumption
      · simpa using step_capacity erasures before after t hs
#print axioms exhausted_removal_get
#print axioms cut_single_vertex_present
#print axioms actual_checkpoint_board
end ActualCheckpoint
