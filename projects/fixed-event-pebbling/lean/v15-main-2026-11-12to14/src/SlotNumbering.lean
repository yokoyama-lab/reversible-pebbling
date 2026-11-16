import RecursiveBlockedCover
import FullSlotAssembly
namespace ChainSlotNumbering
open ChainRecursiveBlockedCover SlotConcat

def restNat : (r : Nat) → Rest r → Nat
  | 0,a => a.val
  | r+1,.inl a => a.val
  | r+1,.inr b => 16+restNat r b

theorem restNat_bound (r : Nat) (a : Rest r) : restNat r a < 8+16*r := by
  induction r with
  | zero => exact a.isLt
  | succ r ih =>
    cases a with
    | inl a => have := a.isLt; simp [restNat]; omega
    | inr a => have := ih a; simp [restNat]; omega

def restFin (r : Nat) (a : Rest r) : Fin (8+16*r) := ⟨restNat r a,restNat_bound r a⟩

def restInv : (r : Nat) → Fin (8+16*r) → Rest r
  | 0,a => ⟨a.val,by have := a.isLt; omega⟩
  | r+1,a => if h : a.val<16 then .inl ⟨a.val,h⟩
      else .inr (restInv r ⟨a.val-16,by have := a.isLt; omega⟩)

theorem rest_left (r : Nat) (a : Rest r) : restInv r (restFin r a)=a := by
  induction r with
  | zero => rfl
  | succ r ih =>
    cases a with
    | inl a => simp [restInv,restFin,restNat,a.isLt]
    | inr a =>
      have he : ¬16+restNat r a<16 := by omega
      simp only [restInv,restFin,restNat,he,↓reduceDIte,Nat.add_sub_cancel_left]
      exact congrArg (Sum.inr : Rest r → Sum (Fin 16) (Rest r)) (ih a)

theorem rest_right (r : Nat) (a : Fin (8+16*r)) : restFin r (restInv r a)=a := by
  apply Fin.ext
  induction r with
  | zero => rfl
  | succ r ih =>
    by_cases h : a.val<16
    · simp [restInv,h,restFin,restNat]
    · have hh := ih ⟨a.val-16,by have := a.isLt; omega⟩
      change restNat r (restInv r _) = a.val-16 at hh
      simp only [restInv,h,↓reduceDIte,restFin,restNat]
      rw [hh]
      omega

def number (r : Nat) : Slots r → Fin (25+16*r)
  | .inl a => ⟨a.val,by have := a.isLt; omega⟩
  | .inr b => ⟨17+restNat r b,by have := restNat_bound r b; omega⟩

def unnumber (r : Nat) (a : Fin (25+16*r)) : Slots r :=
  if h : a.val<17 then .inl ⟨a.val,h⟩
  else .inr (restInv r ⟨a.val-17,by have := a.isLt; omega⟩)

theorem number_left (r : Nat) (a : Slots r) : unnumber r (number r a)=a := by
  cases a with
  | inl a => simp [unnumber,number,a.isLt]
  | inr a =>
    have he : ¬17+restNat r a<17 := by omega
    simp only [unnumber,number,he,↓reduceDIte,Nat.add_sub_cancel_left]
    exact congrArg (Sum.inr : Rest r → Slots r) (rest_left r a)

theorem number_right (r : Nat) (a : Fin (25+16*r)) : number r (unnumber r a)=a := by
  apply Fin.ext
  by_cases h : a.val<17
  · simp [unnumber,number,h]
  · have hh := congrArg Fin.val (rest_right r ⟨a.val-17,by have := a.isLt; omega⟩)
    change restNat r (restInv r _) = a.val-17 at hh
    simp only [unnumber,h,↓reduceDIte,number]
    rw [hh]
    omega

set_option backward.isDefEq.respectTransparency false in
theorem rest_universe_numbered (r : Nat) :
    (restUniverse r).map (restNat r)=List.range (8+16*r) := by
  induction r with
  | zero => exact ChainFinSlotBridge.range_vals 8
  | succ r ih =>
    simp only [Rest,restUniverse,join,List.map_append,List.map_map,Function.comp_def,restNat]
    rw [ChainFinSlotBridge.range_vals 16]
    have he : (restUniverse r).map (fun b=>16+restNat r b) =
        ((restUniverse r).map (restNat r)).map (fun i=>16+i) := by simp [List.map_map,Function.comp_def]
    rw [he,ih]
    have hn : 8+16*(r+1)=16+(8+16*r) := by omega
    rw [hn]
    exact (List.range_add).symm

theorem universe_values (r : Nat) :
    ((allSlots r).map (number r)).map Fin.val=List.range (25+16*r) := by
  simp only [allSlots,join,List.map_append,List.map_map,Function.comp_def,number]
  rw [ChainFinSlotBridge.range_vals 17]
  have he : (restUniverse r).map (fun b=>17+restNat r b) =
      ((restUniverse r).map (restNat r)).map (fun i=>17+i) := by simp [List.map_map,Function.comp_def]
  rw [he,rest_universe_numbered]
  have hn : 25+16*r=17+(8+16*r) := by omega
  rw [hn]
  exact (List.range_add).symm

theorem map_val_injective {n : Nat} (xs ys : List (Fin n))
    (h : xs.map Fin.val=ys.map Fin.val) : xs=ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons a xs ih =>
    cases ys with
    | nil => simp at h
    | cons b ys =>
      have hh := List.cons.inj h
      have ab : a=b := Fin.ext hh.1
      subst b
      exact congrArg (List.cons a) (ih ys hh.2)

theorem universe_numbered (r : Nat) :
    (allSlots r).map (number r)=List.finRange (25+16*r) := by
  apply map_val_injective
  rw [universe_values,ChainFinSlotBridge.range_vals]

#print axioms rest_left
#print axioms rest_right
#print axioms number_left
#print axioms number_right
#print axioms rest_universe_numbered
#print axioms universe_values
#print axioms universe_numbered
end ChainSlotNumbering
