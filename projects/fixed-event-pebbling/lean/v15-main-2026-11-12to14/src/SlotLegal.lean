import FinNumericBridge
import SlotWords
namespace ChainSlotNumbering
open LocalCertificate ChainRecursiveBlockedCover ChainFinSlotBridge ChainFullSlotAssembly
open ChainOccurrence ChainFamilyArithmetic SlotConcat

theorem rest_factors (r : Nat) (w : List (Rest r)) (hw : restLegal r w) :
    ∃ (mw : Nat → List (Fin 16)) (tw : List (Fin 8)),
      w=restWord r mw tw ∧ (∀ j, j<r → slotLegal 16 ML (mw j)) ∧
      slotLegal 8 ChainTailCover.Legal tw := by
  induction r with
  | zero => exact ⟨fun _=>[],w,rfl,by intro j hj; omega,hw⟩
  | succ r ih =>
    obtain ⟨a,b,rfl,ha,hb⟩ := hw
    obtain ⟨mw,tw,rfl,hm,ht⟩ := ih b hb
    let mw' := fun j => if j=0 then a else mw (j-1)
    refine ⟨mw',tw,?_,?_,ht⟩
    · simp [restWord,mw']
    · intro j hj
      cases j with
      | zero => simpa [mw'] using ha
      | succ j => simpa [mw'] using hm j (by omega)

theorem rest_from_factors (r : Nat) (mw : Nat → List (Fin 16)) (tw : List (Fin 8))
    (hm : ∀ j, j<r → slotLegal 16 ML (mw j))
    (ht : slotLegal 8 ChainTailCover.Legal tw) :
    restLegal r (restWord r mw tw) := by
  induction r generalizing mw with
  | zero => exact ht
  | succ r ih =>
    exact ⟨mw 0,restWord r (fun j=>mw (j+1)) tw,rfl,hm 0 (by omega),
      ih _ (fun j hj=>hm (j+1) (by omega))⟩

theorem legal_factors (r : Nat) (w : List (Slots r)) (hw : Legal r w) :
    ∃ (iw : List (Fin 17)) (mw : Nat → List (Fin 16)) (tw : List (Fin 8)),
      w=word r iw mw tw ∧ slotLegal 17 IL iw ∧
      (∀ j, j<r → slotLegal 16 ML (mw j)) ∧ slotLegal 8 ChainTailCover.Legal tw := by
  obtain ⟨iw,rest,rfl,hi,hr⟩ := hw
  obtain ⟨mw,tw,rfl,hm,ht⟩ := rest_factors r rest hr
  exact ⟨iw,mw,tw,rfl,hi,hm,ht⟩

theorem legal_from_factors (r : Nat) (iw : List (Fin 17))
    (mw : Nat → List (Fin 16)) (tw : List (Fin 8))
    (hi : slotLegal 17 IL iw) (hm : ∀ j, j<r → slotLegal 16 ML (mw j))
    (ht : slotLegal 8 ChainTailCover.Legal tw) :
    Legal r (word r iw mw tw) :=
  ⟨iw,restWord r mw tw,rfl,hi,rest_from_factors r mw tw hm ht⟩

theorem legal_numbered (r : Nat) (E : List Nat) (w : List (Slots r))
    (he : ∀ v, v∈E ↔ IsErasure (r+1) v) (hw : Legal r w) :
    labelledLegal r E ((w.map (number r)).map Fin.val) := by
  obtain ⟨iw,mw,tw,rfl,hi,hm,ht⟩ := legal_factors r w hw
  let iu := ChainInitialSegment.middle (iw.map Fin.val)
  let mu := fun j=>ChainMiddleSegment.middle ((mw j).map Fin.val)
  have ig := ChainInitialSegment.all_legal_factor _ hi.2
  have mg := fun j hj => ChainMiddleSegment.all_legal_factor _ (hm j hj).2
  have ie : iw.map Fin.val=ChainInitialConverse.liftWord iu :=
    ChainFactorRecovery.initial_recovery _ hi.2.1 ig
  have me (j : Nat) (hj : j<r) :
      (mw j).map Fin.val=ChainMiddleConverse.liftWord (mu j) :=
    ChainFactorRecovery.middle_recovery _ (hm j hj).2.1 (mg j hj)
  have te := (ChainTailSegment.legal_iff_two _).mp ht.2
  rw [word_eq_fullSlots r iw mw tw iu mu ie me]
  exact full_slots_legal r E iu _ mu he ig.2.2 (fun j hj=>(mg j hj).2.2) te

theorem numbered_injective (r : Nat) (xs ys : List (Slots r))
    (h : (xs.map (number r)).map Fin.val=(ys.map (number r)).map Fin.val) :
    xs=ys := by
  have he := map_val_injective _ _ h
  have hh := congrArg (List.map (unnumber r)) he
  simpa only [List.map_map,Function.comp_def,number_left,List.map_id'] using hh

theorem numbered_legal (r : Nat) (E : List Nat) (w : List (Slots r))
    (hw : labelledLegal r E ((w.map (number r)).map Fin.val)) : Legal r w := by
  classical
  obtain ⟨iu,tw,mu,hi,hm,ht,eqw⟩ := labelled_legal_factor r E _ hw
  obtain ⟨iw,ip,iv⟩ := ChainFinNumericBridge.permutation_lifts 17
    (ChainInitialConverse.liftWord iu) (ChainInitialConverse.local_legal_lifts iu hi).1
  obtain ⟨tf,tp,tv⟩ := ChainFinNumericBridge.permutation_lifts 8 tw
    ((ChainTailSegment.legal_iff_two tw).mpr ht).1
  have em (j : Nat) (hj : j<r) : ∃ u : List (Fin 16),
      u.Perm (List.finRange 16) ∧ u.map Fin.val=ChainMiddleConverse.liftWord (mu j) :=
    ChainFinNumericBridge.permutation_lifts 16 _ (ChainMiddleConverse.local_legal_lifts _ (hm j hj)).1
  let mf : Nat → List (Fin 16) := fun j =>
    if h : j<r then Classical.choose (em j h) else []
  have mp (j : Nat) (hj : j<r) :
      (mf j).Perm (List.finRange 16) ∧
      (mf j).map Fin.val=ChainMiddleConverse.liftWord (mu j) := by
    simpa only [mf,dif_pos hj] using Classical.choose_spec (em j hj)
  have il : slotLegal 17 IL iw := ⟨ip,by rw [iv]; exact ChainInitialConverse.local_legal_lifts iu hi⟩
  have ml : ∀ j, j<r → slotLegal 16 ML (mf j) := by
    intro j hj
    refine ⟨(mp j hj).1,?_⟩
    rw [(mp j hj).2]
    exact ChainMiddleConverse.local_legal_lifts _ (hm j hj)
  have tl : slotLegal 8 ChainTailCover.Legal tf := by
    refine ⟨tp,?_⟩
    rw [tv]
    exact (ChainTailSegment.legal_iff_two tw).mpr ht
  have hl := legal_from_factors r iw mf tf il ml tl
  have mapped := word_eq_fullSlots r iw mf tf iu mu iv (fun j hj=>(mp j hj).2)
  rw [tv] at mapped
  have we : w=word r iw mf tf := numbered_injective r _ _ (eqw.trans mapped.symm)
  rw [we]
  exact hl

theorem legalmapiff (r : Nat) (E : List Nat)
    (he : ∀ v, v∈E ↔ IsErasure (r+1) v) (w : List (Slots r)) :
    labelledLegal r E ((w.map (number r)).map Fin.val) ↔ Legal r w :=
  ⟨numbered_legal r E w,legal_numbered r E w he⟩

#print axioms numbered_injective
#print axioms numbered_legal
#print axioms legalmapiff
#print axioms rest_factors
#print axioms rest_from_factors
#print axioms legal_factors
#print axioms legal_from_factors
#print axioms legal_numbered
end ChainSlotNumbering
