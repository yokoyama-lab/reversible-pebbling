import UpperCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace UpperShards
abbrev words := UpperCertificate.M.physicalWords
abbrev covered (w : List Nat) : Bool :=
  UpperCertificate.M.covers.any (fun p => UpperCertificate.satisfiesPredecessors p w)

def chunk (i : Nat) := (words.drop (32*i)).take 32

theorem word_count : words.length = 584 := by decide

theorem join_take_drop {α : Type} (p : α → Bool) (xs : List α) (n : Nat)
    (hTake : (xs.take n).all p = true) (hDrop : (xs.drop n).all p = true) :
    xs.all p = true := by
  rw [← List.take_append_drop n xs, List.all_append]
  rw [hTake, hDrop]
  rfl

#print axioms word_count
#print axioms join_take_drop
end UpperShards
