import MSmallExact
import MBridge
namespace MComponentCover
open LocalCertificate ErasureCover
abbrev Small (w : List Nat) : Prop := M.Legal w ∧ w∈MSmallSwap.component
abbrev Large (w : List Nat) : Prop := M.Legal w ∧ w∉MSmallSwap.component
def smallIndex (i : Fin 2) : Fin 14 := ⟨i.val+6,by omega⟩
def largeIndex (i : Fin 12) : Fin 14 := ⟨if i.val<6 then i.val else i.val+2,by split <;> omega⟩
theorem smallIndex_injective (i j : Fin 2) (h : smallIndex i=smallIndex j) : i=j := by
 have hh := congrArg Fin.val h;apply Fin.ext;dsimp [smallIndex] at hh;omega
theorem largeIndex_injective (i j : Fin 12) (h : largeIndex i=largeIndex j) : i=j := by
 have hh := congrArg Fin.val h;apply Fin.ext;dsimp [largeIndex] at hh;split at hh <;> split at hh <;> omega
theorem witness_membership : ∀i : Fin 14,M.witness i∈MSmallSwap.component ↔ i.val=6 ∨ i.val=7 := by decide

theorem small_witness (i : Fin 2) : Small (M.witness (smallIndex i)) := by
 refine ⟨M.witnesses_legal _,(witness_membership _).mpr ?_⟩
 dsimp [smallIndex];have hi:=i.isLt;omega
theorem large_witness (i : Fin 12) : Large (M.witness (largeIndex i)) := by
 refine ⟨M.witnesses_legal _,?_⟩
 rw [witness_membership];dsimp [largeIndex];split <;> omega

theorem restricted_lower {m : Nat} (select : Fin m → Fin 14)
 (inj : ∀i j,select i=select j→i=j) (L : List Nat→Prop)
 (subset : ∀w,L w→M.Legal w) (wit : ∀i,L (M.witness (select i)))
 (n : Nat) (relation : Fin n→Fin 12→Fin 12→Prop)
 (sound : ∀c,Sound M.S L (relation c))
 (covered : ∀w,L w→∃c,Extends M.S (relation c) w) : m≤n := by
 obtain ⟨choose,assigned⟩ := ErasureLocalLowerBounds.finite_choice m
  (fun i c=>Extends M.S (relation c) (M.witness (select i)))
  (fun i=>covered _ (wit i))
 apply ErasureCardinality.fin_injection_bound choose
 intro i j eq
 apply inj i j
 by_cases same : select i=select j
 · exact same
 · exact False.elim (M.no_sound_relation_covers_pair (relation (choose i)) (select i) (select j) same
     (fun w hw=>subset w (sound _ w hw)) (assigned i)
     (by simpa only [eq] using assigned j))

theorem small_lower (n : Nat) (relation : Fin n→Fin 12→Fin 12→Prop)
 (sound : ∀c,Sound M.S Small (relation c))
 (covered : ∀w,Small w→∃c,Extends M.S (relation c) w) : 2≤n :=
 restricted_lower smallIndex smallIndex_injective Small (fun _ h=>h.1) small_witness n relation sound covered

theorem large_lower (n : Nat) (relation : Fin n→Fin 12→Fin 12→Prop)
 (sound : ∀c,Sound M.S Large (relation c))
 (covered : ∀w,Large w→∃c,Extends M.S (relation c) w) : 12≤n :=
 restricted_lower largeIndex largeIndex_injective Large (fun _ h=>h.1) large_witness n relation sound covered
#print axioms witness_membership
#print axioms small_lower
#print axioms large_lower
end MComponentCover
