import LocalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace UpperCertificate
open LocalCertificate

/-- Enumerate only physically legal next steps; each branch removes one event. -/
def enumeratePhysical (events : List Event) (erasures final : List Nat) :
    Nat → List Nat → List Nat → List (List Nat)
  | 0, board, remaining => if remaining.isEmpty && sameBoard board final then [[]] else []
  | fuel + 1, board, remaining => remaining.flatMap fun e =>
      match events[e]? with
      | none => []
      | some event => match step true erasures board event with
        | none => []
        | some after => (enumeratePhysical events erasures final fuel after (remaining.erase e)).map (e :: ·)

/-- Enumerate only predecessor-enabled next steps, not all n! permutations. -/
def enumerateExtensions (preds : List (List Nat)) : Nat → List Nat → List (List Nat)
  | 0, remaining => if remaining.isEmpty then [[]] else []
  | fuel + 1, remaining => remaining.flatMap fun e =>
      if (preds.getD e []).all (fun p => !(remaining.contains p))
      then (enumerateExtensions preds fuel (remaining.erase e)).map (e :: ·)
      else []

def strictPoset (n : Nat) (preds : List (List Nat)) : Bool :=
  preds.length == n && (List.range n).all fun e =>
    !(preds.getD e []).contains e &&
    (preds.getD e []).all fun p =>
      decide (p < n) && (preds.getD p []).all (fun q => (preds.getD e []).contains q)


def satisfiesPredecessors (preds : List (List Nat)) (word : List Nat) : Bool :=
  (List.range preds.length).all fun e =>
    (preds.getD e []).all fun p => decide (word.idxOf p < word.idxOf e)

namespace I
def covers : List (List (List Nat)) := [[[1, 2], [2], [], [], [2, 3, 5], [2, 3], [1, 2, 3, 5], [0, 1, 2, 3, 5, 6, 8], [0, 1, 2, 3, 5, 6], [0, 1, 2, 3, 4, 5, 6, 8]], [[1, 2], [2], [], [], [2, 3, 5], [2, 3], [1, 2, 3, 5], [1, 2, 3, 4, 5, 6, 8], [1, 2, 3, 4, 5, 6], [0, 1, 2, 3, 4, 5, 6, 8]], [[1, 2], [2], [], [], [2, 3, 5], [2, 3], [2, 3, 4, 5], [1, 2, 3, 4, 5, 6, 8], [1, 2, 3, 4, 5, 6], [1, 2, 3, 4, 5, 6, 7, 8]], [[1, 2], [2], [], [], [2, 3, 5], [2, 3], [1, 2, 3, 5], [0, 1, 2, 3, 5, 6, 8], [0, 1, 2, 3, 5, 6], [0, 1, 2, 3, 5, 6, 7, 8]], [[1, 2], [2], [], [], [2, 3, 5], [2, 3], [1, 2, 3, 5], [1, 2, 3, 4, 5, 6, 8], [1, 2, 3, 4, 5, 6], [1, 2, 3, 4, 5, 6, 7, 8]], [[1, 2], [2], [], [], [2, 3, 5], [2, 3], [2, 3, 4, 5], [1, 2, 3, 4, 5, 6, 8], [1, 2, 3, 4, 5, 6], [0, 1, 2, 3, 4, 5, 6, 8]]]
def physicalWords := enumeratePhysical LocalCertificate.I.events LocalCertificate.I.erasures
  LocalCertificate.I.final 10 LocalCertificate.I.initial (List.range 10)
def coverWords := covers.flatMap (fun p => enumerateExtensions p 10 (List.range 10))


end I

namespace M
def covers : List (List (List Nat)) := [[[1, 2, 3, 4], [], [1, 3, 4], [1, 4], [], [4], [1, 3, 4, 5, 7], [1, 3, 4, 5], [1, 2, 3, 4, 5, 7], [0, 1, 2, 3, 4, 5, 7, 8, 10], [0, 1, 2, 3, 4, 5, 7, 8], [0, 1, 2, 3, 4, 5, 6, 7, 8, 10]], [[1, 2, 3, 4], [4], [1, 3, 4], [1, 4], [], [], [1, 3, 4, 5, 7], [1, 3, 4, 5], [1, 2, 3, 4, 5, 7], [1, 2, 3, 4, 5, 6, 7, 8, 10], [1, 2, 3, 4, 5, 6, 7, 8], [0, 1, 2, 3, 4, 5, 6, 7, 8, 10]], [[1, 2, 3, 4], [], [1, 3, 4], [1, 4], [], [4], [1, 3, 4, 5, 7], [1, 3, 4, 5], [1, 2, 3, 4, 5, 7], [1, 2, 3, 4, 5, 6, 7, 8, 10], [1, 2, 3, 4, 5, 6, 7, 8], [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]], [[1, 2, 3, 4], [4], [1, 3, 4], [1, 4], [], [], [1, 3, 4, 5, 7], [1, 3, 4, 5], [1, 2, 3, 4, 5, 7], [0, 1, 2, 3, 4, 5, 7, 8, 10], [0, 1, 2, 3, 4, 5, 7, 8], [0, 1, 2, 3, 4, 5, 7, 8, 9, 10]], [[1, 2, 3, 4], [], [1, 3, 4], [1, 4], [], [4], [1, 3, 4, 5, 7], [1, 3, 4, 5], [1, 3, 4, 5, 6, 7], [1, 2, 3, 4, 5, 6, 7, 8, 10], [1, 2, 3, 4, 5, 6, 7, 8], [0, 1, 2, 3, 4, 5, 6, 7, 8, 10]], [[1, 2, 3, 4, 5, 6, 7], [4, 5, 6, 7], [1, 3, 4, 5, 6, 7], [1, 4, 5, 6, 7], [], [], [4, 5, 7], [4, 5], [1, 3, 4, 5, 6, 7], [1, 2, 3, 4, 5, 6, 7, 8, 10], [1, 2, 3, 4, 5, 6, 7, 8], [0, 1, 2, 3, 4, 5, 6, 7, 8, 10]], [[1, 2, 3, 4], [], [1, 3, 4], [1, 4], [], [4], [1, 3, 4, 5, 7], [1, 3, 4, 5], [1, 2, 3, 4, 5, 7], [0, 1, 2, 3, 4, 5, 7, 8, 10], [0, 1, 2, 3, 4, 5, 7, 8], [0, 1, 2, 3, 4, 5, 7, 8, 9, 10]], [[1, 2, 3, 4], [4], [1, 3, 4], [1, 4], [], [], [1, 3, 4, 5, 7], [1, 3, 4, 5], [1, 3, 4, 5, 6, 7], [1, 2, 3, 4, 5, 6, 7, 8, 10], [1, 2, 3, 4, 5, 6, 7, 8], [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]], [[1, 2, 3, 4], [], [1, 3, 4], [1, 4], [], [4], [1, 3, 4, 5, 7], [1, 3, 4, 5], [1, 2, 3, 4, 5, 7], [1, 2, 3, 4, 5, 6, 7, 8, 10], [1, 2, 3, 4, 5, 6, 7, 8], [0, 1, 2, 3, 4, 5, 6, 7, 8, 10]], [[1, 2, 3, 4], [4], [1, 3, 4], [1, 4], [], [], [1, 3, 4, 5, 7], [1, 3, 4, 5], [1, 2, 3, 4, 5, 7], [0, 1, 2, 3, 4, 5, 7, 8, 10], [0, 1, 2, 3, 4, 5, 7, 8], [0, 1, 2, 3, 4, 5, 6, 7, 8, 10]], [[1, 2, 3, 4, 5, 6, 7], [4, 5, 6, 7], [1, 3, 4, 5, 6, 7], [1, 4, 5, 6, 7], [], [], [4, 5, 7], [4, 5], [1, 3, 4, 5, 6, 7], [1, 2, 3, 4, 5, 6, 7, 8, 10], [1, 2, 3, 4, 5, 6, 7, 8], [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]], [[1, 2, 3, 4], [], [1, 3, 4], [1, 4], [], [4], [1, 3, 4, 5, 7], [1, 3, 4, 5], [1, 3, 4, 5, 6, 7], [1, 2, 3, 4, 5, 6, 7, 8, 10], [1, 2, 3, 4, 5, 6, 7, 8], [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]], [[1, 2, 3, 4], [4], [1, 3, 4], [1, 4], [], [], [1, 3, 4, 5, 7], [1, 3, 4, 5], [1, 3, 4, 5, 6, 7], [1, 2, 3, 4, 5, 6, 7, 8, 10], [1, 2, 3, 4, 5, 6, 7, 8], [0, 1, 2, 3, 4, 5, 6, 7, 8, 10]], [[1, 2, 3, 4], [4], [1, 3, 4], [1, 4], [], [], [1, 3, 4, 5, 7], [1, 3, 4, 5], [1, 2, 3, 4, 5, 7], [1, 2, 3, 4, 5, 6, 7, 8, 10], [1, 2, 3, 4, 5, 6, 7, 8], [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]]
def physicalWords := enumeratePhysical LocalCertificate.M.events LocalCertificate.M.erasures
  LocalCertificate.M.final 12 LocalCertificate.M.initial (List.range 12)
def coverWords := covers.flatMap (fun p => enumerateExtensions p 12 (List.range 12))


end M
end UpperCertificate
