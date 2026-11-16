import PrefixStateCorrectness
import LocalStateLanguages
import MUpperVerified
namespace ChainMStateShards
open ChainPrefixStates
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def candidates : List (List Nat) := [[], [1], [1, 4], [1, 3, 4], [1, 2, 3, 4], [0, 1, 2, 3, 4], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5, 7], [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 7, 8], [0, 1, 2, 3, 4, 5, 6, 7, 8, 10], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], [0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 11], [0, 1, 2, 3, 4, 5, 7, 8], [0, 1, 2, 3, 4, 5, 7, 8, 10], [0, 1, 2, 3, 4, 5, 7, 8, 9, 10], [0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 11], [1, 2, 3, 4, 5], [1, 2, 3, 4, 5, 7], [1, 2, 3, 4, 5, 6, 7], [1, 2, 3, 4, 5, 6, 7, 8], [1, 2, 3, 4, 5, 6, 7, 8, 10], [1, 2, 3, 4, 5, 6, 7, 8, 9, 10], [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], [1, 2, 3, 4, 5, 7, 8], [1, 3, 4, 5], [1, 3, 4, 5, 7], [1, 3, 4, 5, 6, 7], [1, 3, 4, 5, 6, 7, 8], [1, 4, 5], [4], [4, 5], [4, 5, 7], [4, 5, 6, 7], [1, 4, 5, 6, 7], [5]]
def covered (w : List Nat) : Bool := (setsOfWord 12 w).all candidates.contains
abbrev words := UpperCertificate.M.physicalWords
def chunk (i : Nat) := (words.drop (32*i)).take 32
theorem candidate_count : candidates.length = 37 := by decide
theorem candidate_nodup : candidates.Nodup := by decide
theorem join_take_drop (p : α → Bool) (xs : List α) (n : Nat)
    (ht : (xs.take n).all p = true) (hd : (xs.drop n).all p = true) : xs.all p = true := by
  have h := List.take_append_drop n xs
  calc
    xs.all p = ((xs.take n) ++ xs.drop n).all p := congrArg (fun ys => ys.all p) h.symm
    _ = true := by simp only [List.all_append,ht,hd,Bool.and_self]
end ChainMStateShards
