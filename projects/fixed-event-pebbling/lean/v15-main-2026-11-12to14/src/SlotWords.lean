import SlotNumbering
namespace ChainSlotNumbering
open ChainRecursiveBlockedCover SlotConcat ChainFullSlotAssembly ChainOccurrence
open ChainAssembledTrace ChainGlobalReassembly

def restWord : (r : Nat) → (Nat → List (Fin 16)) → List (Fin 8) → List (Rest r)
  | 0,_,tw => tw
  | r+1,mw,tw => join (mw 0) (restWord r (fun j=>mw (j+1)) tw)
def word (r : Nat) (iw : List (Fin 17)) (mw : Nat → List (Fin 16)) (tw : List (Fin 8)) :=
  join iw (restWord r mw tw)

def numericMids (words : Nat → List Nat) (r offset : Nat) : List Nat :=
  (List.range r).flatMap (fun j=>(words j).map (fun i=>i+(offset+16*j)))

theorem restWord_numbered (r : Nat) (mw : Nat → List (Fin 16)) (tw : List (Fin 8)) :
    (restWord r mw tw).map (restNat r) =
      numericMids (fun j=>(mw j).map Fin.val) r 0 ++
        (tw.map Fin.val).map (fun i=>i+16*r) := by
  induction r generalizing mw with
  | zero => simp [Rest,restWord,restNat,numericMids,Function.comp_def]
  | succ r ih =>
    simp only [Rest,restWord,join,List.map_append,List.map_map,Function.comp_def,restNat]
    have he : (restWord r (fun j=>mw (j+1)) tw).map (fun b=>16+restNat r b) =
        ((restWord r (fun j=>mw (j+1)) tw).map (restNat r)).map (fun i=>i+16) := by
      simp [List.map_map,Function.comp_def,Nat.add_comm]
    rw [he,ih]
    simp [numericMids,List.range_succ_eq_map,List.flatMap_map,List.map_flatMap,
      List.map_map,Function.comp_def,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem word_numbered (r : Nat) (iw : List (Fin 17)) (mw : Nat → List (Fin 16)) (tw : List (Fin 8)) :
    ((word r iw mw tw).map (number r)).map Fin.val =
      iw.map Fin.val ++ numericMids (fun j=>(mw j).map Fin.val) r 17 ++
        (tw.map Fin.val).map (fun i=>i+(17+16*r)) := by
  simp only [word,join,List.map_append,List.map_map,Function.comp_def,number]
  have he : (restWord r mw tw).map (fun b=>17+restNat r b) =
      ((restWord r mw tw).map (restNat r)).map (fun i=>i+17) := by
    simp [List.map_map,Function.comp_def,Nat.add_comm]
  rw [he,restWord_numbered]
  simp [numericMids,List.map_flatMap,List.map_map,Function.comp_def,List.append_assoc,
    Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem preTable_length (r : Nat) : (preTable r).length=17+16*r := by
  have h := ChainOccurrence.table_length r
  have ht : (TailActual.events (5+6*r)).length=8 := by rfl
  simp only [fullTable,List.length_append,ht] at h
  omega

theorem prefixSlots_normal (r : Nat) (iu : List Nat) (mu : Nat → List Nat) :
    prefixSlots r iu mu =
      ChainInitialConverse.liftWord iu ++
        numericMids (fun j=>ChainMiddleConverse.liftWord (mu j)) r 17 := by
  induction r with
  | zero => simp [prefixSlots,foldSlots,numericMids]
  | succ r ih =>
    change concatSlots (preTable r).length (prefixSlots r iu mu)
      (ChainMiddleConverse.liftWord (mu r)) = _
    rw [preTable_length,ih]
    simp [concatSlots,numericMids,List.range_succ,List.append_assoc]

theorem fullSlots_normal (r : Nat) (iu tw : List Nat) (mu : Nat → List Nat) :
    fullSlots r iu mu tw =
      ChainInitialConverse.liftWord iu ++
        numericMids (fun j=>ChainMiddleConverse.liftWord (mu j)) r 17 ++
          tw.map (fun i=>i+(17+16*r)) := by
  rw [fullSlots,preTable_length,prefixSlots_normal]
  rfl

theorem word_eq_fullSlots (r : Nat) (iw : List (Fin 17))
    (mw : Nat → List (Fin 16)) (tw : List (Fin 8))
    (iu : List Nat) (mu : Nat → List Nat)
    (hi : iw.map Fin.val=ChainInitialConverse.liftWord iu)
    (hm : ∀ j, j<r → (mw j).map Fin.val=ChainMiddleConverse.liftWord (mu j)) :
    ((word r iw mw tw).map (number r)).map Fin.val =
      fullSlots r iu mu (tw.map Fin.val) := by
  rw [word_numbered,fullSlots_normal,hi]
  have eqmid : numericMids (fun j=>(mw j).map Fin.val) r 17 =
      numericMids (fun j=>ChainMiddleConverse.liftWord (mu j)) r 17 := by
    unfold numericMids
    simp only [List.flatMap_def]
    apply congrArg List.flatten
    apply List.map_congr_left
    intro j hj
    rw [hm j (List.mem_range.mp hj)]
  rw [eqmid]

#print axioms restWord_numbered
#print axioms word_numbered
#print axioms preTable_length
#print axioms prefixSlots_normal
#print axioms fullSlots_normal
#print axioms word_eq_fullSlots
end ChainSlotNumbering
