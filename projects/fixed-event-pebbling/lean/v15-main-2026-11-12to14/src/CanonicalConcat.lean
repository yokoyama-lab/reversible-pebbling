import CanonicalDecode
import PaddedRelation
namespace ChainOccurrence
open LocalCertificate ChainTrace ReplayBridge

def concatSlots (n : Nat) (wa wb : List Nat) := wa ++ wb.map (fun i=>i+n)

theorem permutation_mem (n : Nat) (w : List Nat) (h : isPermutation n w)
    (i : Nat) (hi : i<n) : i∈w :=
  ((EnumerationCorrectness.isPermutation_iff_perm_range n w).mp h).mem_iff.mpr
    (List.mem_range.mpr hi)

theorem concat_permutation (n m : Nat) (wa wb : List Nat)
    (ha : isPermutation n wa) (hb : isPermutation m wb) :
    isPermutation (n+m) (concatSlots n wa wb) := by
  apply (EnumerationCorrectness.isPermutation_iff_perm_range _ _).mpr
  have a := (EnumerationCorrectness.isPermutation_iff_perm_range _ _).mp ha
  have b := (EnumerationCorrectness.isPermutation_iff_perm_range _ _).mp hb
  have p := a.append (b.map (fun i=>i+n))
  simpa [concatSlots,List.range_add,Nat.add_comm] using p

theorem concat_idx_left (n : Nat) (wa wb : List Nat) (h : isPermutation n wa)
    (i : Nat) (hi : i<n) :
    (concatSlots n wa wb).idxOf i=wa.idxOf i := by
  simp [concatSlots,List.idxOf_append,permutation_mem n wa h i hi]

theorem concat_idx_right (n : Nat) (wa wb : List Nat) (h : isPermutation n wa) (i : Nat) :
    (concatSlots n wa wb).idxOf (i+n)=wa.length+wb.idxOf i := by
  have absent : i+n∉wa := by intro hm; have := h.2.2 (i+n) hm; omega
  unfold concatSlots
  rw [List.idxOf_append,if_neg absent,ChainPaddedRelation.idx_map_add]
  omega

theorem canonical_concat (a b : List Event) (wa wb : List Nat)
    (pa : isPermutation a.length wa) (pb : isPermutation b.length wb)
    (ca : canonical a wa) (cb : canonical b wb) :
    canonical (a++b) (concatSlots a.length wa wb) := by
  intro i j hij he
  have il := i.isLt
  have jl := j.isLt
  simp only [List.length_append] at il jl
  by_cases hi : i.val<a.length
  · by_cases hj : j.val<a.length
    · rw [concat_idx_left _ _ _ pa i.val hi,concat_idx_left _ _ _ pa j.val hj]
      apply ca ⟨i.val,hi⟩ ⟨j.val,hj⟩ hij
      simpa only [List.getElem_append,hi,hj,↓reduceDIte] using he
    · have jrep : j.val=(j.val-a.length)+a.length := by omega
      rw [concat_idx_left _ _ _ pa i.val hi,jrep,concat_idx_right _ _ _ pa]
      have := List.idxOf_lt_length_of_mem (permutation_mem _ _ pa i.val hi)
      omega
  · have hj : ¬j.val<a.length := by omega
    have ir : i.val=(i.val-a.length)+a.length := by omega
    have jr : j.val=(j.val-a.length)+a.length := by omega
    have hloc : wb.idxOf (i.val-a.length) < wb.idxOf (j.val-a.length) :=
      cb ⟨i.val-a.length,by omega⟩ ⟨j.val-a.length,by omega⟩
      (show i.val-a.length < j.val-a.length by omega)
      (by simpa only [List.getElem_append,hi,hj,↓reduceDIte] using he)
    rw [ir,jr,concat_idx_right _ _ _ pa,concat_idx_right _ _ _ pa]
    omega

theorem canonical_shift_iff (offset : Nat) (table : List Event) (w : List Nat) :
    canonical (shiftEvents offset table) w ↔ canonical table w := by
  constructor
  · intro h i j hij he
    have hi : i.val<(shiftEvents offset table).length := by simpa [shiftEvents] using i.isLt
    have hj : j.val<(shiftEvents offset table).length := by simpa [shiftEvents] using j.isLt
    apply h ⟨i.val,hi⟩ ⟨j.val,hj⟩ hij
    simpa [shiftEvents,shiftEvent] using congrArg (fun v=>v+offset) he
  · intro h i j hij he
    have hi : i.val<table.length := by simpa [shiftEvents] using i.isLt
    have hj : j.val<table.length := by simpa [shiftEvents] using j.isLt
    apply h ⟨i.val,hi⟩ ⟨j.val,hj⟩ hij
    simpa [shiftEvents,shiftEvent] using he

#print axioms concat_permutation
#print axioms concat_idx_left
#print axioms concat_idx_right
#print axioms canonical_concat
#print axioms canonical_shift_iff
end ChainOccurrence
