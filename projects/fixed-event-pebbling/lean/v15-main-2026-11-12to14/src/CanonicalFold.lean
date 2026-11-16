import CanonicalConcat
namespace ChainOccurrence
open LocalCertificate ChainTrace ChainGlobalReassembly

theorem decode_append (table : List Event) (xs ys : List Nat) :
    decodeTrace table (xs++ys) =
      (decodeTrace table xs).bind (fun a => (decodeTrace table ys).map (a++·)) := by
  induction xs with
  | nil => simp [decodeTrace]
  | cons i xs ih =>
    cases hi : table[i]? <;> cases hx : decodeTrace table xs <;>
      cases hy : decodeTrace table ys <;> simp [decodeTrace,hi,hx,hy,ih]

theorem decode_left_append (a b : List Event) (w : List Nat)
    (hw : ∀ i∈w, i<a.length) :
    decodeTrace (a++b) w=decodeTrace a w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    have hi := List.getElem?_append_left (l₂:=b) (hw i (by simp))
    have ht := ih (fun j hj => hw j (by simp [hj]))
    simp only [decodeTrace,hi,ht]

theorem decode_right_append (a b : List Event) (w : List Nat) :
    decodeTrace (a++b) (w.map (fun i=>i+a.length))=decodeTrace b w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    have hi : (a++b)[i+a.length]?=b[i]? := by
      rw [List.getElem?_append_right (by omega)]
      congr 1
      omega
    simp only [List.map_cons,decodeTrace,hi,ih]

theorem decode_concat (a b : List Event) (wa wb : List Nat) (ea eb : List Event)
    (pa : isPermutation a.length wa)
    (da : decodeTrace a wa=some ea) (db : decodeTrace b wb=some eb) :
    decodeTrace (a++b) (concatSlots a.length wa wb)=some (ea++eb) := by
  rw [concatSlots,decode_append,decode_left_append a b wa pa.2.2,
    decode_right_append,da,db]
  rfl

def foldSlots (initial : List Event) (tables : Nat → List Event)
    (iw : List Nat) (words : Nat → List Nat) : Nat → List Nat
  | 0 => iw
  | n+1 => concatSlots (initial ++ assemble tables n).length
      (foldSlots initial tables iw words n) (words n)

theorem fold_canonical (initial : List Event) (tables : Nat → List Event)
    (iw : List Nat) (words : Nat → List Nat) (n : Nat)
    (pi : isPermutation initial.length iw) (ci : canonical initial iw)
    (ps : ∀ j, j<n → isPermutation (tables j).length (words j))
    (cs : ∀ j, j<n → canonical (tables j) (words j)) :
    isPermutation (initial ++ assemble tables n).length (foldSlots initial tables iw words n) ∧
    canonical (initial ++ assemble tables n) (foldSlots initial tables iw words n) := by
  induction n with
  | zero => simpa [assemble,foldSlots] using And.intro pi ci
  | succ n ih =>
    have hh := ih (fun j hj => ps j (by omega)) (fun j hj => cs j (by omega))
    have pp := concat_permutation _ _ _ _ hh.1 (ps n (by omega))
    have cc := canonical_concat _ _ _ _ hh.1 (ps n (by omega)) hh.2 (cs n (by omega))
    constructor
    · simpa [foldSlots,assemble,List.length_append,Nat.add_assoc] using pp
    · simpa only [foldSlots,assemble,List.append_assoc] using cc

theorem fold_decode (initial : List Event) (tables : Nat → List Event)
    (iw : List Nat) (words : Nat → List Nat) (n : Nat)
    (rawInitial : List Event) (raws : Nat → List Event)
    (pi : isPermutation initial.length iw) (ci : canonical initial iw)
    (ps : ∀ j, j<n → isPermutation (tables j).length (words j))
    (cs : ∀ j, j<n → canonical (tables j) (words j))
    (di : decodeTrace initial iw=some rawInitial)
    (ds : ∀ j, j<n → decodeTrace (tables j) (words j)=some (raws j)) :
    decodeTrace (initial ++ assemble tables n) (foldSlots initial tables iw words n) =
      some (rawInitial ++ assemble raws n) := by
  induction n with
  | zero => simpa [assemble,foldSlots] using di
  | succ n ih =>
    have pp := (fold_canonical initial tables iw words n pi ci
      (fun j hj => ps j (by omega)) (fun j hj => cs j (by omega))).1
    have dd := ih (fun j hj => ps j (by omega)) (fun j hj => cs j (by omega))
      (fun j hj => ds j (by omega))
    have h := decode_concat _ _ _ _ _ _ pp dd (ds n (by omega))
    simpa only [foldSlots,assemble,List.append_assoc] using h

#print axioms decode_append
#print axioms decode_left_append
#print axioms decode_right_append
#print axioms decode_concat
#print axioms fold_canonical
#print axioms fold_decode
end ChainOccurrence
