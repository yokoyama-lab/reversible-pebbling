import Std
import CommonExtension
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace LocalCertificate
structure Event where
  place : Bool
  vertex : Nat
  deriving Repr, DecidableEq

def isPermutation (n : Nat) (t : List Nat) : Prop :=
  t.length = n ∧ t.Nodup ∧ ∀ e ∈ t, e < n
instance (n : Nat) (t : List Nat) : Decidable (isPermutation n t) := inferInstanceAs (Decidable (t.length = n ∧ t.Nodup ∧ ∀ e ∈ t, e < n))

def semantics (n : Nat) : ErasureCover.Semantics (Fin n) (List Nat) where
  admissible := isPermutation n
  before t a b := t.idxOf a.val < t.idxOf b.val

def step (capacity : Bool) (erasures board : List Nat) (e : Event) : Option (List Nat) := do
  let pred := e.vertex == 1 || board.contains (e.vertex - 1)
  let next ← if e.place then
      if !(board.contains e.vertex) && pred then some (e.vertex :: board) else none
    else
      if board.contains e.vertex && ((!pred) == erasures.contains e.vertex)
      then some (board.erase e.vertex) else none
  if capacity && decide (next.length > 5) then none else some next

def replay (capacity : Bool) (events : List Event) (erasures : List Nat) : List Nat → List Nat → Option (List Nat)
  | board, [] => some board
  | board, e :: rest => do
      let event ← events[e]?
      let after ← step capacity erasures board event
      replay capacity events erasures after rest

def sameBoard (a b : List Nat) : Bool :=
  a.length == b.length && a.all (fun x => b.contains x)

def legal (events : List Event) (initial final erasures : List Nat) (t : List Nat) : Prop :=
  isPermutation events.length t ∧
  (match replay true events erasures initial t with
   | none => false
   | some board => sameBoard board final) = true
instance (events : List Event) (initial final erasures t : List Nat) : Decidable (legal events initial final erasures t) :=
  inferInstanceAs (Decidable (_ ∧ _))

namespace I
def events : List Event := [⟨false, 1⟩, ⟨false, 2⟩, ⟨false, 3⟩, ⟨true, 6⟩, ⟨false, 6⟩, ⟨true, 7⟩, ⟨true, 8⟩, ⟨false, 8⟩, ⟨true, 9⟩, ⟨true, 10⟩]
def initial : List Nat := [1, 2, 3, 5]
def final : List Nat := [5, 7, 9, 10]
def erasures : List Nat := [5]
def words : List (List Nat) := [[3, 2, 5, 4, 6, 1, 8, 7, 9, 0], [3, 2, 5, 4, 6, 1, 8, 0, 9, 7], [3, 2, 5, 1, 6, 4, 8, 7, 9, 0], [3, 2, 5, 1, 6, 4, 8, 0, 9, 7], [3, 2, 5, 1, 6, 0, 8, 7, 9, 4], [3, 2, 5, 1, 6, 0, 8, 4, 9, 7]]
def witness (i : Fin 6) : List Nat := words.getD i.val []
def obstructionTable : List (List (List Nat)) := [[[], [3, 2, 5, 4, 6, 1, 8, 9, 0, 7], [3, 2, 5, 6, 1, 4, 8, 7, 9, 0], [3, 2, 5, 1, 4, 6, 8, 9, 0, 7], [3, 2, 5, 1, 6, 8, 0, 4, 7, 9], [3, 2, 5, 1, 4, 6, 8, 9, 0, 7]], [[3, 2, 5, 4, 6, 1, 8, 9, 0, 7], [], [3, 2, 5, 1, 4, 6, 8, 9, 0, 7], [3, 2, 5, 6, 1, 4, 8, 0, 9, 7], [3, 2, 5, 1, 6, 0, 8, 9, 4, 7], [3, 2, 5, 1, 6, 8, 0, 4, 9, 7]], [[3, 2, 5, 6, 1, 4, 8, 7, 9, 0], [3, 2, 5, 1, 4, 6, 8, 9, 0, 7], [], [3, 2, 5, 1, 6, 4, 8, 9, 0, 7], [3, 2, 5, 1, 6, 8, 0, 4, 7, 9], [3, 2, 5, 1, 6, 4, 8, 9, 0, 7]], [[3, 2, 5, 1, 4, 6, 8, 9, 0, 7], [3, 2, 5, 6, 1, 4, 8, 0, 9, 7], [3, 2, 5, 1, 6, 4, 8, 9, 0, 7], [], [3, 2, 5, 1, 6, 0, 8, 9, 4, 7], [3, 2, 5, 1, 6, 8, 0, 4, 9, 7]], [[3, 2, 5, 1, 6, 8, 0, 4, 7, 9], [3, 2, 5, 1, 6, 0, 8, 9, 4, 7], [3, 2, 5, 1, 6, 8, 0, 4, 7, 9], [3, 2, 5, 1, 6, 0, 8, 9, 4, 7], [], [3, 2, 5, 1, 6, 0, 8, 9, 4, 7]], [[3, 2, 5, 1, 4, 6, 8, 9, 0, 7], [3, 2, 5, 1, 6, 8, 0, 4, 9, 7], [3, 2, 5, 1, 6, 4, 8, 9, 0, 7], [3, 2, 5, 1, 6, 8, 0, 4, 9, 7], [3, 2, 5, 1, 6, 0, 8, 9, 4, 7], []]]
def obstruction (i j : Fin 6) : List Nat := (obstructionTable.getD i.val []).getD j.val []
abbrev S := semantics 10
abbrev Legal := legal events initial final erasures

theorem witnesses_legal : ∀ i : Fin 6, Legal (witness i) := by decide

theorem obstructions_checked : ∀ i j : Fin 6, i ≠ j →
  ErasureCover.Extends S (ErasureCover.Common S (witness i) (witness j)) (obstruction i j) ∧
  ¬ Legal (obstruction i j) := by
  dsimp [ErasureCover.Extends, ErasureCover.Common, S, semantics]
  decide

theorem obstructions_noncapacity_legal : ∀ i j : Fin 6, i ≠ j →
  (match replay false events erasures initial (obstruction i j) with
  | none => false
  | some board => sameBoard board final) = true := by decide

theorem no_sound_relation_covers_pair (P : Fin 10 → Fin 10 → Prop)
    (i j : Fin 6) (hne : i ≠ j) (sound : ErasureCover.Sound S Legal P)
    (hi : ErasureCover.Extends S P (witness i))
    (hj : ErasureCover.Extends S P (witness j)) : False := by
  have hz := obstructions_checked i j hne
  exact ErasureCover.badCommonExtension S Legal P (witness i) (witness j)
    (obstruction i j) sound hi hj hz.1 hz.2

theorem cover_assignment_injective {Cover : Type}
    (relation : Cover → Fin 10 → Fin 10 → Prop)
    (choose : Fin 6 → Cover)
    (sound : ∀ c, ErasureCover.Sound S Legal (relation c))
    (covered : ∀ i, ErasureCover.Extends S (relation (choose i)) (witness i)) :
    ∀ i j, choose i = choose j → i = j := by
  apply ErasureCover.witnessAssignmentInjective S Legal witness relation choose sound covered
  intro i j hne
  exact ⟨obstruction i j, obstructions_checked i j hne⟩

#print axioms witnesses_legal
#print axioms obstructions_checked
#print axioms obstructions_noncapacity_legal
#print axioms no_sound_relation_covers_pair
#print axioms cover_assignment_injective
end I

namespace M
def events : List Event := [⟨false, 5⟩, ⟨true, 6⟩, ⟨false, 6⟩, ⟨false, 7⟩, ⟨false, 8⟩, ⟨true, 12⟩, ⟨false, 12⟩, ⟨true, 13⟩, ⟨true, 14⟩, ⟨false, 14⟩, ⟨true, 15⟩, ⟨true, 16⟩]
def initial : List Nat := [5, 7, 8, 11]
def final : List Nat := [11, 13, 15, 16]
def erasures : List Nat := [5, 11]
def words : List (List Nat) := [[5, 4, 1, 3, 7, 6, 8, 2, 10, 9, 11, 0], [5, 4, 1, 3, 7, 6, 8, 2, 10, 0, 11, 9], [5, 4, 1, 3, 7, 2, 8, 6, 10, 9, 11, 0], [5, 4, 1, 3, 7, 2, 8, 6, 10, 0, 11, 9], [5, 4, 1, 3, 7, 2, 8, 0, 10, 9, 11, 6], [5, 4, 1, 3, 7, 2, 8, 0, 10, 6, 11, 9], [5, 4, 7, 6, 1, 3, 8, 2, 10, 9, 11, 0], [5, 4, 7, 6, 1, 3, 8, 2, 10, 0, 11, 9], [1, 4, 5, 3, 7, 6, 8, 2, 10, 9, 11, 0], [1, 4, 5, 3, 7, 6, 8, 2, 10, 0, 11, 9], [1, 4, 5, 3, 7, 2, 8, 6, 10, 9, 11, 0], [1, 4, 5, 3, 7, 2, 8, 6, 10, 0, 11, 9], [1, 4, 5, 3, 7, 2, 8, 0, 10, 9, 11, 6], [1, 4, 5, 3, 7, 2, 8, 0, 10, 6, 11, 9]]
def witness (i : Fin 14) : List Nat := words.getD i.val []
def obstructionTable : List (List (List Nat)) := [[[], [5, 4, 1, 3, 7, 6, 8, 2, 10, 11, 0, 9], [5, 4, 1, 3, 7, 8, 2, 6, 10, 9, 11, 0], [5, 4, 1, 3, 7, 2, 6, 8, 10, 11, 0, 9], [5, 4, 1, 3, 7, 2, 8, 10, 0, 6, 9, 11], [5, 4, 1, 3, 7, 2, 6, 8, 10, 11, 0, 9], [5, 4, 1, 7, 3, 6, 8, 2, 10, 9, 11, 0], [5, 4, 1, 3, 7, 6, 8, 2, 10, 11, 0, 9], [1, 5, 4, 3, 7, 6, 8, 2, 10, 9, 11, 0], [1, 4, 5, 3, 7, 6, 8, 2, 10, 11, 0, 9], [1, 4, 5, 3, 7, 8, 2, 6, 10, 9, 11, 0], [1, 4, 5, 3, 7, 2, 6, 8, 10, 11, 0, 9], [1, 4, 5, 3, 7, 2, 8, 10, 0, 6, 9, 11], [1, 4, 5, 3, 7, 2, 6, 8, 10, 11, 0, 9]], [[5, 4, 1, 3, 7, 6, 8, 2, 10, 11, 0, 9], [], [5, 4, 1, 3, 7, 2, 6, 8, 10, 11, 0, 9], [5, 4, 1, 3, 7, 8, 2, 6, 10, 0, 11, 9], [5, 4, 1, 3, 7, 2, 8, 0, 10, 11, 6, 9], [5, 4, 1, 3, 7, 2, 8, 10, 0, 6, 11, 9], [5, 4, 1, 3, 7, 6, 8, 2, 10, 11, 0, 9], [5, 4, 1, 7, 3, 6, 8, 2, 10, 0, 11, 9], [1, 4, 5, 3, 7, 6, 8, 2, 10, 11, 0, 9], [1, 5, 4, 3, 7, 6, 8, 2, 10, 0, 11, 9], [1, 4, 5, 3, 7, 2, 6, 8, 10, 11, 0, 9], [1, 4, 5, 3, 7, 8, 2, 6, 10, 0, 11, 9], [1, 4, 5, 3, 7, 2, 8, 0, 10, 11, 6, 9], [1, 4, 5, 3, 7, 2, 8, 10, 0, 6, 11, 9]], [[5, 4, 1, 3, 7, 8, 2, 6, 10, 9, 11, 0], [5, 4, 1, 3, 7, 2, 6, 8, 10, 11, 0, 9], [], [5, 4, 1, 3, 7, 2, 8, 6, 10, 11, 0, 9], [5, 4, 1, 3, 7, 2, 8, 10, 0, 6, 9, 11], [5, 4, 1, 3, 7, 2, 8, 6, 10, 11, 0, 9], [5, 4, 1, 3, 7, 8, 2, 6, 10, 9, 11, 0], [5, 4, 1, 3, 7, 2, 6, 8, 10, 11, 0, 9], [1, 4, 5, 3, 7, 8, 2, 6, 10, 9, 11, 0], [1, 4, 5, 3, 7, 2, 6, 8, 10, 11, 0, 9], [1, 5, 4, 3, 7, 2, 8, 6, 10, 9, 11, 0], [1, 4, 5, 3, 7, 2, 8, 6, 10, 11, 0, 9], [1, 4, 5, 3, 7, 2, 8, 10, 0, 6, 9, 11], [1, 4, 5, 3, 7, 2, 8, 6, 10, 11, 0, 9]], [[5, 4, 1, 3, 7, 2, 6, 8, 10, 11, 0, 9], [5, 4, 1, 3, 7, 8, 2, 6, 10, 0, 11, 9], [5, 4, 1, 3, 7, 2, 8, 6, 10, 11, 0, 9], [], [5, 4, 1, 3, 7, 2, 8, 0, 10, 11, 6, 9], [5, 4, 1, 3, 7, 2, 8, 10, 0, 6, 11, 9], [5, 4, 1, 3, 7, 2, 6, 8, 10, 11, 0, 9], [5, 4, 1, 3, 7, 8, 2, 6, 10, 0, 11, 9], [1, 4, 5, 3, 7, 2, 6, 8, 10, 11, 0, 9], [1, 4, 5, 3, 7, 8, 2, 6, 10, 0, 11, 9], [1, 4, 5, 3, 7, 2, 8, 6, 10, 11, 0, 9], [1, 5, 4, 3, 7, 2, 8, 6, 10, 0, 11, 9], [1, 4, 5, 3, 7, 2, 8, 0, 10, 11, 6, 9], [1, 4, 5, 3, 7, 2, 8, 10, 0, 6, 11, 9]], [[5, 4, 1, 3, 7, 2, 8, 10, 0, 6, 9, 11], [5, 4, 1, 3, 7, 2, 8, 0, 10, 11, 6, 9], [5, 4, 1, 3, 7, 2, 8, 10, 0, 6, 9, 11], [5, 4, 1, 3, 7, 2, 8, 0, 10, 11, 6, 9], [], [5, 4, 1, 3, 7, 2, 8, 0, 10, 11, 6, 9], [5, 4, 1, 3, 7, 2, 8, 10, 0, 6, 9, 11], [5, 4, 1, 3, 7, 2, 8, 0, 10, 11, 6, 9], [1, 4, 5, 3, 7, 2, 8, 10, 0, 6, 9, 11], [1, 4, 5, 3, 7, 2, 8, 0, 10, 11, 6, 9], [1, 4, 5, 3, 7, 2, 8, 10, 0, 6, 9, 11], [1, 4, 5, 3, 7, 2, 8, 0, 10, 11, 6, 9], [1, 5, 4, 3, 7, 2, 8, 0, 10, 9, 11, 6], [1, 4, 5, 3, 7, 2, 8, 0, 10, 11, 6, 9]], [[5, 4, 1, 3, 7, 2, 6, 8, 10, 11, 0, 9], [5, 4, 1, 3, 7, 2, 8, 10, 0, 6, 11, 9], [5, 4, 1, 3, 7, 2, 8, 6, 10, 11, 0, 9], [5, 4, 1, 3, 7, 2, 8, 10, 0, 6, 11, 9], [5, 4, 1, 3, 7, 2, 8, 0, 10, 11, 6, 9], [], [5, 4, 1, 3, 7, 2, 6, 8, 10, 11, 0, 9], [5, 4, 1, 3, 7, 2, 8, 10, 0, 6, 11, 9], [1, 4, 5, 3, 7, 2, 6, 8, 10, 11, 0, 9], [1, 4, 5, 3, 7, 2, 8, 10, 0, 6, 11, 9], [1, 4, 5, 3, 7, 2, 8, 6, 10, 11, 0, 9], [1, 4, 5, 3, 7, 2, 8, 10, 0, 6, 11, 9], [1, 4, 5, 3, 7, 2, 8, 0, 10, 11, 6, 9], [1, 5, 4, 3, 7, 2, 8, 0, 10, 6, 11, 9]], [[5, 4, 1, 7, 3, 6, 8, 2, 10, 9, 11, 0], [5, 4, 1, 3, 7, 6, 8, 2, 10, 11, 0, 9], [5, 4, 1, 3, 7, 8, 2, 6, 10, 9, 11, 0], [5, 4, 1, 3, 7, 2, 6, 8, 10, 11, 0, 9], [5, 4, 1, 3, 7, 2, 8, 10, 0, 6, 9, 11], [5, 4, 1, 3, 7, 2, 6, 8, 10, 11, 0, 9], [], [5, 4, 7, 6, 1, 3, 8, 2, 10, 11, 0, 9], [1, 4, 5, 7, 3, 6, 8, 2, 10, 9, 11, 0], [1, 4, 5, 3, 7, 6, 8, 2, 10, 11, 0, 9], [1, 4, 5, 3, 7, 8, 2, 6, 10, 9, 11, 0], [1, 4, 5, 3, 7, 2, 6, 8, 10, 11, 0, 9], [1, 4, 5, 3, 7, 2, 8, 10, 0, 6, 9, 11], [1, 4, 5, 3, 7, 2, 6, 8, 10, 11, 0, 9]], [[5, 4, 1, 3, 7, 6, 8, 2, 10, 11, 0, 9], [5, 4, 1, 7, 3, 6, 8, 2, 10, 0, 11, 9], [5, 4, 1, 3, 7, 2, 6, 8, 10, 11, 0, 9], [5, 4, 1, 3, 7, 8, 2, 6, 10, 0, 11, 9], [5, 4, 1, 3, 7, 2, 8, 0, 10, 11, 6, 9], [5, 4, 1, 3, 7, 2, 8, 10, 0, 6, 11, 9], [5, 4, 7, 6, 1, 3, 8, 2, 10, 11, 0, 9], [], [1, 4, 5, 3, 7, 6, 8, 2, 10, 11, 0, 9], [1, 4, 5, 7, 3, 6, 8, 2, 10, 0, 11, 9], [1, 4, 5, 3, 7, 2, 6, 8, 10, 11, 0, 9], [1, 4, 5, 3, 7, 8, 2, 6, 10, 0, 11, 9], [1, 4, 5, 3, 7, 2, 8, 0, 10, 11, 6, 9], [1, 4, 5, 3, 7, 2, 8, 10, 0, 6, 11, 9]], [[1, 5, 4, 3, 7, 6, 8, 2, 10, 9, 11, 0], [1, 4, 5, 3, 7, 6, 8, 2, 10, 11, 0, 9], [1, 4, 5, 3, 7, 8, 2, 6, 10, 9, 11, 0], [1, 4, 5, 3, 7, 2, 6, 8, 10, 11, 0, 9], [1, 4, 5, 3, 7, 2, 8, 10, 0, 6, 9, 11], [1, 4, 5, 3, 7, 2, 6, 8, 10, 11, 0, 9], [1, 4, 5, 7, 3, 6, 8, 2, 10, 9, 11, 0], [1, 4, 5, 3, 7, 6, 8, 2, 10, 11, 0, 9], [], [1, 4, 5, 3, 7, 6, 8, 2, 10, 11, 0, 9], [1, 4, 5, 3, 7, 8, 2, 6, 10, 9, 11, 0], [1, 4, 5, 3, 7, 2, 6, 8, 10, 11, 0, 9], [1, 4, 5, 3, 7, 2, 8, 10, 0, 6, 9, 11], [1, 4, 5, 3, 7, 2, 6, 8, 10, 11, 0, 9]], [[1, 4, 5, 3, 7, 6, 8, 2, 10, 11, 0, 9], [1, 5, 4, 3, 7, 6, 8, 2, 10, 0, 11, 9], [1, 4, 5, 3, 7, 2, 6, 8, 10, 11, 0, 9], [1, 4, 5, 3, 7, 8, 2, 6, 10, 0, 11, 9], [1, 4, 5, 3, 7, 2, 8, 0, 10, 11, 6, 9], [1, 4, 5, 3, 7, 2, 8, 10, 0, 6, 11, 9], [1, 4, 5, 3, 7, 6, 8, 2, 10, 11, 0, 9], [1, 4, 5, 7, 3, 6, 8, 2, 10, 0, 11, 9], [1, 4, 5, 3, 7, 6, 8, 2, 10, 11, 0, 9], [], [1, 4, 5, 3, 7, 2, 6, 8, 10, 11, 0, 9], [1, 4, 5, 3, 7, 8, 2, 6, 10, 0, 11, 9], [1, 4, 5, 3, 7, 2, 8, 0, 10, 11, 6, 9], [1, 4, 5, 3, 7, 2, 8, 10, 0, 6, 11, 9]], [[1, 4, 5, 3, 7, 8, 2, 6, 10, 9, 11, 0], [1, 4, 5, 3, 7, 2, 6, 8, 10, 11, 0, 9], [1, 5, 4, 3, 7, 2, 8, 6, 10, 9, 11, 0], [1, 4, 5, 3, 7, 2, 8, 6, 10, 11, 0, 9], [1, 4, 5, 3, 7, 2, 8, 10, 0, 6, 9, 11], [1, 4, 5, 3, 7, 2, 8, 6, 10, 11, 0, 9], [1, 4, 5, 3, 7, 8, 2, 6, 10, 9, 11, 0], [1, 4, 5, 3, 7, 2, 6, 8, 10, 11, 0, 9], [1, 4, 5, 3, 7, 8, 2, 6, 10, 9, 11, 0], [1, 4, 5, 3, 7, 2, 6, 8, 10, 11, 0, 9], [], [1, 4, 5, 3, 7, 2, 8, 6, 10, 11, 0, 9], [1, 4, 5, 3, 7, 2, 8, 10, 0, 6, 9, 11], [1, 4, 5, 3, 7, 2, 8, 6, 10, 11, 0, 9]], [[1, 4, 5, 3, 7, 2, 6, 8, 10, 11, 0, 9], [1, 4, 5, 3, 7, 8, 2, 6, 10, 0, 11, 9], [1, 4, 5, 3, 7, 2, 8, 6, 10, 11, 0, 9], [1, 5, 4, 3, 7, 2, 8, 6, 10, 0, 11, 9], [1, 4, 5, 3, 7, 2, 8, 0, 10, 11, 6, 9], [1, 4, 5, 3, 7, 2, 8, 10, 0, 6, 11, 9], [1, 4, 5, 3, 7, 2, 6, 8, 10, 11, 0, 9], [1, 4, 5, 3, 7, 8, 2, 6, 10, 0, 11, 9], [1, 4, 5, 3, 7, 2, 6, 8, 10, 11, 0, 9], [1, 4, 5, 3, 7, 8, 2, 6, 10, 0, 11, 9], [1, 4, 5, 3, 7, 2, 8, 6, 10, 11, 0, 9], [], [1, 4, 5, 3, 7, 2, 8, 0, 10, 11, 6, 9], [1, 4, 5, 3, 7, 2, 8, 10, 0, 6, 11, 9]], [[1, 4, 5, 3, 7, 2, 8, 10, 0, 6, 9, 11], [1, 4, 5, 3, 7, 2, 8, 0, 10, 11, 6, 9], [1, 4, 5, 3, 7, 2, 8, 10, 0, 6, 9, 11], [1, 4, 5, 3, 7, 2, 8, 0, 10, 11, 6, 9], [1, 5, 4, 3, 7, 2, 8, 0, 10, 9, 11, 6], [1, 4, 5, 3, 7, 2, 8, 0, 10, 11, 6, 9], [1, 4, 5, 3, 7, 2, 8, 10, 0, 6, 9, 11], [1, 4, 5, 3, 7, 2, 8, 0, 10, 11, 6, 9], [1, 4, 5, 3, 7, 2, 8, 10, 0, 6, 9, 11], [1, 4, 5, 3, 7, 2, 8, 0, 10, 11, 6, 9], [1, 4, 5, 3, 7, 2, 8, 10, 0, 6, 9, 11], [1, 4, 5, 3, 7, 2, 8, 0, 10, 11, 6, 9], [], [1, 4, 5, 3, 7, 2, 8, 0, 10, 11, 6, 9]], [[1, 4, 5, 3, 7, 2, 6, 8, 10, 11, 0, 9], [1, 4, 5, 3, 7, 2, 8, 10, 0, 6, 11, 9], [1, 4, 5, 3, 7, 2, 8, 6, 10, 11, 0, 9], [1, 4, 5, 3, 7, 2, 8, 10, 0, 6, 11, 9], [1, 4, 5, 3, 7, 2, 8, 0, 10, 11, 6, 9], [1, 5, 4, 3, 7, 2, 8, 0, 10, 6, 11, 9], [1, 4, 5, 3, 7, 2, 6, 8, 10, 11, 0, 9], [1, 4, 5, 3, 7, 2, 8, 10, 0, 6, 11, 9], [1, 4, 5, 3, 7, 2, 6, 8, 10, 11, 0, 9], [1, 4, 5, 3, 7, 2, 8, 10, 0, 6, 11, 9], [1, 4, 5, 3, 7, 2, 8, 6, 10, 11, 0, 9], [1, 4, 5, 3, 7, 2, 8, 10, 0, 6, 11, 9], [1, 4, 5, 3, 7, 2, 8, 0, 10, 11, 6, 9], []]]
def obstruction (i j : Fin 14) : List Nat := (obstructionTable.getD i.val []).getD j.val []
abbrev S := semantics 12
abbrev Legal := legal events initial final erasures

theorem witnesses_legal : ∀ i : Fin 14, Legal (witness i) := by decide

theorem obstructions_checked : ∀ i j : Fin 14, i ≠ j →
  ErasureCover.Extends S (ErasureCover.Common S (witness i) (witness j)) (obstruction i j) ∧
  ¬ Legal (obstruction i j) := by
  dsimp [ErasureCover.Extends, ErasureCover.Common, S, semantics]
  decide

theorem obstructions_noncapacity_legal : ∀ i j : Fin 14, i ≠ j →
  (match replay false events erasures initial (obstruction i j) with
  | none => false
  | some board => sameBoard board final) = true := by decide

theorem no_sound_relation_covers_pair (P : Fin 12 → Fin 12 → Prop)
    (i j : Fin 14) (hne : i ≠ j) (sound : ErasureCover.Sound S Legal P)
    (hi : ErasureCover.Extends S P (witness i))
    (hj : ErasureCover.Extends S P (witness j)) : False := by
  have hz := obstructions_checked i j hne
  exact ErasureCover.badCommonExtension S Legal P (witness i) (witness j)
    (obstruction i j) sound hi hj hz.1 hz.2

theorem cover_assignment_injective {Cover : Type}
    (relation : Cover → Fin 12 → Fin 12 → Prop)
    (choose : Fin 14 → Cover)
    (sound : ∀ c, ErasureCover.Sound S Legal (relation c))
    (covered : ∀ i, ErasureCover.Extends S (relation (choose i)) (witness i)) :
    ∀ i j, choose i = choose j → i = j := by
  apply ErasureCover.witnessAssignmentInjective S Legal witness relation choose sound covered
  intro i j hne
  exact ⟨obstruction i j, obstructions_checked i j hne⟩

#print axioms witnesses_legal
#print axioms obstructions_checked
#print axioms obstructions_noncapacity_legal
#print axioms no_sound_relation_covers_pair
#print axioms cover_assignment_injective
end M
end LocalCertificate
