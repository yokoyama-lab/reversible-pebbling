import FinSlotBridge
namespace ChainFinNumericBridge
open LocalCertificate ErasureCover
 theorem permutation_lifts (n : Nat) (w : List Nat) (hw : isPermutation n w) :
   ∃ u : List (Fin n), u.Perm (List.finRange n) ∧ u.map Fin.val=w := by
   cases n with
   | zero =>
     have he : w=[] := List.eq_nil_of_length_eq_zero hw.1
     subst w
     exact ⟨[],List.Perm.refl [],rfl⟩
   | succ n =>
     let f : Nat → Fin (n+1) := fun i => ⟨i%(n+1),Nat.mod_lt _ (by omega)⟩
     have rangeEq : (List.range (n+1)).map f = List.finRange (n+1) := by
       apply List.ext_getElem
       · simp
       · intro i h1 h2
         have hi : i<n+1 := by simpa using h2
         apply Fin.ext
         simp [f,Nat.mod_eq_of_lt hi]
     have hp := ((EnumerationCorrectness.isPermutation_iff_perm_range _ _).mp hw).map f
     rw [rangeEq] at hp
     refine ⟨w.map f,hp,?_⟩
     have he : (w.map f).map Fin.val = w.map (fun i => i) := by
       simp only [List.map_map]
       apply List.map_congr_left
       intro i hi
       exact Nat.mod_eq_of_lt (hw.2.2 i hi)
     simpa only [List.map_id'] using he
 theorem numeric_sound {n : Nat} (Q : Fin n → Fin n → Prop) (L : List Nat → Prop)
   (hs : Sound (SlotConcat.semantics (List.finRange n))
     (fun u => L (u.map Fin.val)) Q) : Sound (LocalCertificate.semantics n) L Q := by
   intro w hw
   obtain ⟨u,hp,he⟩ := permutation_lifts n w hw.1
   have hu := (ChainFinSlotBridge.slot_extends_iff Q u hp).mpr (by simpa [he] using hw)
   simpa [he] using hs u hu
 theorem numeric_cover {n : Nat} {C : Type} (Q : C → Fin n → Fin n → Prop) (L : List Nat → Prop)
   (admissible : ∀w,L w→isPermutation n w)
   (hc : ∀u,L (u.map Fin.val) → ∃c,Extends (SlotConcat.semantics (List.finRange n)) (Q c) u) :
   ∀w,L w → ∃c,Extends (LocalCertificate.semantics n) (Q c) w := by
   intro w hw
   obtain ⟨u,hp,he⟩ := permutation_lifts n w (admissible w hw)
   obtain ⟨c,hc⟩ := hc u (by simpa [he] using hw)
   exact ⟨c,by simpa [he] using (ChainFinSlotBridge.slot_extends_iff (Q c) u hp).mp hc⟩
#print axioms permutation_lifts
#print axioms numeric_sound
#print axioms numeric_cover
end ChainFinNumericBridge
