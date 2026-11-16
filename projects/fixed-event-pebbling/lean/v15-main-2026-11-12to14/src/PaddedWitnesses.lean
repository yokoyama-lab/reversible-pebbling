import FactorUnique
import RecursiveBlockedCover
import PaddingObstruction
namespace ChainPaddedWitnesses
open LocalCertificate ErasureCover ChainFinSlotBridge ChainPaddedRelation

def finize (n : Nat) (w : List Nat) : List (Fin (n+1)) :=
  w.map (fun i => ⟨i%(n+1),Nat.mod_lt _ (by omega)⟩)

theorem finize_vals (n : Nat) (w : List Nat) (h : ∀ i∈w, i<n+1) :
    (finize n w).map Fin.val = w := by
  rw [finize,List.map_map]
  apply Eq.trans (b:=w.map (fun i=>i))
  · apply List.map_congr_left
    intro i hi
    exact Nat.mod_eq_of_lt (h i hi)
  · exact List.map_id' _

theorem finize_range (n : Nat) : finize n (List.range (n+1)) = List.finRange (n+1) := by
  apply List.ext_getElem
  · simp [finize]
  · intro i hi hj
    apply Fin.ext
    have hi2 : i<n+1 := by simpa using hj
    simp [finize,Nat.mod_eq_of_lt hi2]

theorem finize_perm (n : Nat) (w : List Nat) (h : isPermutation (n+1) w) :
    (finize n w).Perm (List.finRange (n+1)) := by
  have hp := ((EnumerationCorrectness.isPermutation_iff_perm_range _ _).mp h).map
    (fun i => (⟨i%(n+1),Nat.mod_lt _ (by omega)⟩ : Fin (n+1)))
  simpa [←finize_range n,finize] using hp

theorem finize_common (n : Nat) (s t z : List Nat)
    (hs : isPermutation (n+1) s) (ht : isPermutation (n+1) t)
    (hz : Extends (semantics (n+1)) (Common (semantics (n+1)) s t) z) :
    Extends (SlotConcat.semantics (List.finRange (n+1)))
      (Common (SlotConcat.semantics (List.finRange (n+1))) (finize n s) (finize n t)) (finize n z) := by
  refine ⟨finize_perm n z hz.1,?_⟩
  intro a b hab
  have eqs := finize_vals n s hs.2.2
  have eqt := finize_vals n t ht.2.2
  have eqz := finize_vals n z hz.1.2.2
  have hbefore (u : List Nat) (hu : isPermutation (n+1) u) (x y : Fin (n+1)) :
      (finize n u).idxOf x < (finize n u).idxOf y ↔ u.idxOf x.val < u.idxOf y.val := by
    rw [← idx_vals (finize n u) x,←idx_vals (finize n u) y,finize_vals n u hu.2.2]
  apply (hbefore z hz.1 a b).mpr
  exact hz.2 a b ⟨(hbefore s hs a b).mp hab.1,(hbefore t ht a b).mp hab.2⟩

def iw (i : Fin 6) : List (Fin 17) := finize 16 (ChainInitialConverse.liftWord (I.witness i))
def mw (i : Fin 14) : List (Fin 16) := finize 15 (ChainMiddleConverse.liftWord (M.witness i))

theorem iw_legal (i : Fin 6) : slotLegal 17 IL (iw i) := by
  have h := ChainInitialConverse.local_legal_lifts _ (I.witnesses_legal i)
  refine ⟨finize_perm _ _ h.1,?_⟩
  change IL ((finize 16 (ChainInitialConverse.liftWord (I.witness i))).map Fin.val)
  rw [finize_vals 16 _ (show ∀ a∈ChainInitialConverse.liftWord (I.witness i), a<17 from h.1.2.2)]
  exact h
theorem mw_legal (i : Fin 14) : slotLegal 16 ML (mw i) := by
  have h := ChainMiddleConverse.local_legal_lifts _ (M.witnesses_legal i)
  refine ⟨finize_perm _ _ h.1,?_⟩
  change ML ((finize 15 (ChainMiddleConverse.liftWord (M.witness i))).map Fin.val)
  rw [finize_vals 15 _ (show ∀ a∈ChainMiddleConverse.liftWord (M.witness i), a<16 from h.1.2.2)]
  exact h

theorem I_bad_lift (z : List Nat) (bad : ¬I.Legal z) : ¬ IL (ChainInitialConverse.liftWord z) := by
  intro h
  obtain ⟨u,hu,he⟩ := (ChainFactorRecovery.initial_legal_iff_factor _).mp h
  exact bad ((ChainFactorUnique.initial_lift_injective z u he).symm ▸ hu)
theorem M_bad_lift (z : List Nat) (bad : ¬M.Legal z) : ¬ ML (ChainMiddleConverse.liftWord z) := by
  intro h
  obtain ⟨u,hu,he⟩ := (ChainFactorRecovery.middle_legal_iff_factor _).mp h
  exact bad ((ChainFactorUnique.middle_lift_injective z u he).symm ▸ hu)

theorem iw_obstruction (i j : Fin 6) (hne : i≠j) :
    ∃ z, Extends (SlotConcat.semantics (List.finRange 17))
      (Common (SlotConcat.semantics (List.finRange 17)) (iw i) (iw j)) z ∧ ¬slotLegal 17 IL z := by
  have h := I.obstructions_checked i j hne
  have lift := ChainPaddingObstruction.common_extension_lift 6 _ _ _
    (I.witnesses_legal i).1 (I.witnesses_legal j).1 h.1
  refine ⟨finize 16 (liftWord 6 10 (I.obstruction i j)),finize_common 16 _ _ _
    (lift_permutation _ _ _ (I.witnesses_legal i).1)
    (lift_permutation _ _ _ (I.witnesses_legal j).1) lift,?_⟩
  intro hz
  have hh := hz.2
  rw [finize_vals 16 _ (show ∀ a∈liftWord 6 10 (I.obstruction i j), a<17 from lift.1.2.2)] at hh
  exact I_bad_lift _ h.2 hh

theorem mw_obstruction (i j : Fin 14) (hne : i≠j) :
    ∃ z, Extends (SlotConcat.semantics (List.finRange 16))
      (Common (SlotConcat.semantics (List.finRange 16)) (mw i) (mw j)) z ∧ ¬slotLegal 16 ML z := by
  have h := M.obstructions_checked i j hne
  have lift := ChainPaddingObstruction.common_extension_lift 3 _ _ _
    (M.witnesses_legal i).1 (M.witnesses_legal j).1 h.1
  refine ⟨finize 15 (liftWord 3 12 (M.obstruction i j)),finize_common 15 _ _ _
    (lift_permutation _ _ _ (M.witnesses_legal i).1)
    (lift_permutation _ _ _ (M.witnesses_legal j).1) lift,?_⟩
  intro hz
  have hh := hz.2
  rw [finize_vals 15 _ (show ∀ a∈liftWord 3 12 (M.obstruction i j), a<16 from lift.1.2.2)] at hh
  exact M_bad_lift _ h.2 hh

#print axioms iw_legal
#print axioms mw_legal
#print axioms iw_obstruction
#print axioms mw_obstruction
end ChainPaddedWitnesses
