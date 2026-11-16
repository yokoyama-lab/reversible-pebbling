import BlockProfile
import LeftRegion
import FamilyArithmetic
namespace FamilyCut
open LocalCertificate ChainTrace ChainFamilyArithmetic ActualCheckpoint BlockProfile CompletedEvents LeftRegion
abbrev P := RemovalOrder.isPlacement
abbrev R := ChainUniqueLifetime.isRemoval

structure Trace (k : Nat) (erasures : List Nat) (word : List Event) : Prop where
  bounded : ∀ e ∈ word, 0 < e.vertex ∧ e.vertex ≤ 5+6*k
  legal : run erasures [] word = some [5+6*k]
  erasure_sites : ∀ v, v ∈ erasures ↔ IsErasure k v
  counts : ∀ v, 0 < v → v ≤ 5+6*k → word.countP (P v) = placementCount v

theorem placement_count_le_two (v : Nat) : placementCount v ≤ 2 := by
  unfold placementCount
  split
  · omega
  · split <;> omega

/-- A simultaneous cut signature for every block of the concrete family.
No explicit removal positions or lifetime hypotheses occur in Trace. -/
theorem all_block_cut_signature
    (k j s : Nat) (erasures : List Nat) (pre post : List Event) (t : Event)
    (hj : j < k) (hs : s = 5+6*j) (htp : t.place = true) (htv : t.vertex = s+6)
    (model : Trace k erasures (pre ++ t :: post)) :
    (∃ before cut, run erasures [] pre = some before ∧
      step true erasures before t = some cut ∧
      (∀ v, v ∈ cut ↔ v ∈ [s,s+2,s+4,s+5,s+6])) ∧
    (∀ v, 0 < v → v < s → ∀ e ∈ post, e.vertex ≠ v) ∧
    (∀ e ∈ pre, e.vertex < s+6) ∧
    (∀ v ∈ [s,s+2,s+4,s+5,s+6],
      (pre ++ [t]).countP (P v) = 1 ∧ (pre ++ [t]).countP (R v) = 0) ∧
    ((pre ++ [t]).countP (P (s+1)) = 1 ∧ (pre ++ [t]).countP (R (s+1)) = 1) ∧
    ((pre ++ [t]).countP (P (s+3)) = 1 ∧ (pre ++ [t]).countP (R (s+3)) = 1) := by
  have spos : 0 < s := by omega
  have maxs : s+6 ≤ 5+6*k := by omega
  have hno : ∀ v, s < v → v ≤ s+5 → v ∉ erasures := by
    intro v hv hmax hm
    have he := (model.erasure_sites v).mp hm
    have hid : v = 5+6*j+(v-s) := by omega
    rw [hid] at he
    exact interior_not_erasure j k (v-s) (by omega) (by omega) he
  have hfinal : ∀ v, s ≤ v → v ≤ s+5 → v ∉ [5+6*k] := by
    intro v hv hmax
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    omega
  have bc := block_placement_counts j
  rw [← hs] at bc
  obtain ⟨cs,ca,cb,cc,cd,ch,ct⟩ := bc
  have cnt : ∀ v, s ≤ v → v ≤ s+6 → (pre ++ t :: post).countP (P v) = placementCount v := by
    intro v hv hmax; exact model.counts v (by omega) (by omega)
  have allcounts : (pre ++ t :: post).countP (P s) = 1 ∧
      (pre ++ t :: post).countP (P (s+1)) = 2 ∧
      (pre ++ t :: post).countP (P (s+2)) = 1 ∧
      (pre ++ t :: post).countP (P (s+3)) = 2 ∧
      (pre ++ t :: post).countP (P (s+4)) = 1 ∧
      (pre ++ t :: post).countP (P (s+5)) = 1 := by
    refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> rw [cnt _ (by omega) (by omega)] <;> assumption
  have tcount : (pre ++ t :: post).countP (P (s+6)) = 1 := by rw [cnt _ (by omega) (by omega),ct]
  obtain ⟨before,cut,hp,ht,hboard⟩ := actual_checkpoint_board erasures [5+6*k] pre post t s
    spos htp htv model.legal hno hfinal allcounts
  have left : ∀ v, 0 < v → v < s → ∀ e ∈ post, e.vertex ≠ v := by
    apply left_region_completed erasures before cut [5+6*k] pre post t s htp htv hp ht model.legal hboard
    intro v hv hvs
    have cv := model.counts v hv (by omega)
    by_cases hsingle : placementCount v ≤ 1
    · apply Or.inl
      change (pre ++ t :: post).countP (P v) ≤ 1
      rw [cv]
      exact hsingle
    · have htwo : placementCount v = 2 := by have := placement_count_le_two v; omega
      obtain ⟨hgt,hpred⟩ := repeated_predecessor_single v hv htwo
      refine Or.inr ⟨hgt,?_,?_⟩
      · change (pre ++ t :: post).countP (P (v-1)) ≤ 1
        rw [model.counts (v-1) (by omega) (by omega),hpred]
        omega
      · intro hm
        obtain ⟨i,hi,he⟩ := (model.erasure_sites v).mp hm
        have hanchor := (block_placement_counts i).1
        rw [← he] at hanchor
        omega
  have right := (sole_placement_bounds_prefix erasures [5+6*k] pre post t (by omega) htp
    (by change (pre ++ t :: post).countP (P t.vertex) ≤ 1; rw [htv,tcount]; omega) model.legal).1
  have profile := block_prefix_event_counts erasures [5+6*k] pre post t s spos htp htv
    model.legal hno hfinal allcounts tcount
  exact ⟨⟨before,cut,hp,ht,hboard⟩,left,(by simpa [htv] using right),profile⟩
#print axioms placement_count_le_two
#print axioms all_block_cut_signature
end FamilyCut
