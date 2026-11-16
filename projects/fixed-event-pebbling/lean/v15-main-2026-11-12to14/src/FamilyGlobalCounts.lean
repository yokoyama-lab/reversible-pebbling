import FamilyCut
import FamilyRemovalCounts
namespace FamilyCut
open LocalCertificate ChainTrace ChainFamilyArithmetic ChainFamilyRemovalCounts

theorem family_total_removals (k : Nat) (erasures : List Nat) (word : List Event)
    (model : Trace k erasures word) (v : Nat) (hv : 0 < v) (hvn : v < 5+6*k) :
    word.countP (R v) = placementCount v := by
  have absent : v ∉ [5+6*k] := by simp; omega
  have count := model.counts v hv (by omega)
  rcases placement_count_one_or_two v with h1 | h2
  · rw [h1]
    exact ChainTwoCutCounts.closed_single_placement_single_removal erasures [] [5+6*k] word v
      (by simp) (by simp) absent (by change word.countP (P v) = 1; omega) model.legal
  · rw [h2]
    exact closed_two_placements_two_removals erasures [] [5+6*k] word v
      (by simp) (by simp) absent (by change word.countP (P v) = 2; omega) model.legal

theorem block_placement_exists (k j : Nat) (erasures : List Nat) (word : List Event)
    (hj : j < k) (model : Trace k erasures word) :
    ∃ pre t post, word = pre ++ t :: post ∧ t.place = true ∧ t.vertex = 5+6*j+6 := by
  have cv := model.counts (5+6*j+6) (by omega) (by omega)
  have hcount := (block_placement_counts j).2.2.2.2.2.2
  have one : word.countP (P (5+6*j+6)) = 1 := by rw [cv,hcount]
  obtain ⟨pre,t,post,hw,ht,_,_⟩ := ChainTwoProjection.split_first_count (P (5+6*j+6)) word 0 one
  have ht' : t.place = true ∧ t.vertex = 5+6*j+6 := by simpa [P,RemovalOrder.isPlacement] using ht
  exact ⟨pre,t,post,hw,ht'.1,ht'.2⟩

theorem left_prefix_complete_counts
    (k j s : Nat) (erasures : List Nat) (pre post : List Event) (t : Event)
    (hj : j < k) (hs : s = 5+6*j) (htp : t.place = true) (htv : t.vertex = s+6)
    (model : Trace k erasures (pre ++ t :: post)) (v : Nat) (hv : 0 < v) (hvs : v < s) :
    (pre ++ [t]).countP (P v) = placementCount v ∧
    (pre ++ [t]).countP (R v) = placementCount v := by
  have sig := all_block_cut_signature k j s erasures pre post t hj hs htp htv model
  have done := LeftRegion.completed_vertex_prefix_counts (pre ++ [t]) post v (sig.2.1 v hv hvs)
  have pc := model.counts v hv (by omega)
  have rc := family_total_removals k erasures (pre ++ t :: post) model v hv (by omega)
  constructor
  · change (pre ++ [t]).countP (LeftRegion.P v) = placementCount v
    rw [done.1]
    change ((pre ++ [t]) ++ post).countP (P v) = placementCount v
    simpa only [List.append_assoc,List.singleton_append] using pc
  · rw [done.2]
    simpa [List.append_assoc] using rc
#print axioms family_total_removals
#print axioms block_placement_exists
#print axioms left_prefix_complete_counts
end FamilyCut
