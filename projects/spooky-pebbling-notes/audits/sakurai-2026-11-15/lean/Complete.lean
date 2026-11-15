import Physical
import Shard0
import Fast0
import Fast1
import Fast2
import Fast3
import Fast4
import Fast5
import Fast6
import Fast7
import Fast8
import Fast9
import Fast10
import Fast11
import Fast12
import Fast13
import Fast14
namespace EdgeBridge
set_option maxSynthPendingDepth 128

theorem index_coverage : ∀ i : Fin 2187, i ∈ ((List.finRange 2187).take 16) ∨ i ∈ (((List.finRange 2187).drop 16).take 256) ∨ i ∈ (((List.finRange 2187).drop 272).take 128) ∨ i ∈ (((List.finRange 2187).drop 400).take 128) ∨ i ∈ (((List.finRange 2187).drop 528).take 128) ∨ i ∈ (((List.finRange 2187).drop 656).take 128) ∨ i ∈ (((List.finRange 2187).drop 784).take 128) ∨ i ∈ (((List.finRange 2187).drop 912).take 128) ∨ i ∈ (((List.finRange 2187).drop 1040).take 128) ∨ i ∈ (((List.finRange 2187).drop 1168).take 128) ∨ i ∈ (((List.finRange 2187).drop 1296).take 128) ∨ i ∈ (((List.finRange 2187).drop 1424).take 128) ∨ i ∈ (((List.finRange 2187).drop 1552).take 128) ∨ i ∈ (((List.finRange 2187).drop 1680).take 128) ∨ i ∈ (((List.finRange 2187).drop 1808).take 128) ∨ i ∈ (((List.finRange 2187).drop 1936).take 128) ∨ i ∈ (((List.finRange 2187).drop 2064).take 123) := by
  have heq : List.finRange 2187 = ((List.finRange 2187).take 16) ++ (((List.finRange 2187).drop 16).take 256) ++ (((List.finRange 2187).drop 272).take 128) ++ (((List.finRange 2187).drop 400).take 128) ++ (((List.finRange 2187).drop 528).take 128) ++ (((List.finRange 2187).drop 656).take 128) ++ (((List.finRange 2187).drop 784).take 128) ++ (((List.finRange 2187).drop 912).take 128) ++ (((List.finRange 2187).drop 1040).take 128) ++ (((List.finRange 2187).drop 1168).take 128) ++ (((List.finRange 2187).drop 1296).take 128) ++ (((List.finRange 2187).drop 1424).take 128) ++ (((List.finRange 2187).drop 1552).take 128) ++ (((List.finRange 2187).drop 1680).take 128) ++ (((List.finRange 2187).drop 1808).take 128) ++ (((List.finRange 2187).drop 1936).take 128) ++ (((List.finRange 2187).drop 2064).take 123) := by native_decide
  intro i
  have hi : i ∈ List.finRange 2187 := by simp
  rw [heq] at hi
  simpa only [List.mem_append, or_assoc] using hi
theorem all_edges (i : Fin 2187) (r) : r ∈ realEdges i ↔ r ∈ tableEdges i := by
  rcases index_coverage i with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16
  · exact checkOne_sound i (List.all_eq_true.mp check_first16 i h0) r
  · exact checkOne_sound i (List.all_eq_true.mp shard0 i h1) r
  · exact checkFast_sound i (List.all_eq_true.mp fast0 i h2) r
  · exact checkFast_sound i (List.all_eq_true.mp fast1 i h3) r
  · exact checkFast_sound i (List.all_eq_true.mp fast2 i h4) r
  · exact checkFast_sound i (List.all_eq_true.mp fast3 i h5) r
  · exact checkFast_sound i (List.all_eq_true.mp fast4 i h6) r
  · exact checkFast_sound i (List.all_eq_true.mp fast5 i h7) r
  · exact checkFast_sound i (List.all_eq_true.mp fast6 i h8) r
  · exact checkFast_sound i (List.all_eq_true.mp fast7 i h9) r
  · exact checkFast_sound i (List.all_eq_true.mp fast8 i h10) r
  · exact checkFast_sound i (List.all_eq_true.mp fast9 i h11) r
  · exact checkFast_sound i (List.all_eq_true.mp fast10 i h12) r
  · exact checkFast_sound i (List.all_eq_true.mp fast11 i h13) r
  · exact checkFast_sound i (List.all_eq_true.mp fast12 i h14) r
  · exact checkFast_sound i (List.all_eq_true.mp fast13 i h15) r
  · exact checkFast_sound i (List.all_eq_true.mp fast14 i h16) r
def empty : SpookyRound.Config 7 := ⟨fun _ => false, fun _ => false⟩
theorem start_empty : decode NativeTable.start = empty := by native_decide

theorem physical_lower_complete
    (h : SpookyRound.PaperRuns pred d empty r) (hg : goalCfg r.state = true) :
    ∃ f ∈ ([⟨5,13,7⟩,⟨7,14,6⟩,⟨8,16,5⟩,⟨9,15,5⟩,⟨12,17,4⟩] : List ClosedFrontier.Cost),
      f.depth ≤ d ∧ f.work ≤ r.work ∧ f.space ≤ r.space := by
  apply physical_lower all_edges (r := r) (d := d) _ hg
  simpa [start_empty] using h
#print axioms all_edges
#print axioms physical_lower_complete
end EdgeBridge
