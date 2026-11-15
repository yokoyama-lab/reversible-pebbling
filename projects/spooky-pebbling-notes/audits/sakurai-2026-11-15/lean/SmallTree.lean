import Std
namespace SpookyDP
structure Result (α : Type) where
  state : α
  work : Nat
  space : Nat
  deriving DecidableEq

def prepend (e : Result α) (r : Result α) : Result α :=
  ⟨r.state, e.work + r.work, max e.space r.space⟩

def dp (next : α → List (Result α)) : Nat → α → List (Result α)
  | 0, q => [⟨q, 0, 0⟩]
  | d+1, q => (next q).flatMap fun e => (dp next d e.state).map (prepend e)

inductive Runs (next : α → List (Result α)) : Nat → α → Result α → Prop
  | zero (q) : Runs next 0 q ⟨q, 0, 0⟩
  | step {d q e r} : e ∈ next q → Runs next d e.state r →
      Runs next (d+1) q (prepend e r)

theorem mem_dp_iff (next : α → List (Result α)) (d q r) :
    r ∈ dp next d q ↔ Runs next d q r := by
  induction d generalizing q r with
  | zero =>
    constructor
    · intro h
      have hr : r = ⟨q, 0, 0⟩ := by simpa [dp] using h
      subst r
      exact Runs.zero q
    · intro h
      cases h
      simp [dp]
  | succ d ih =>
    constructor
    · intro h
      simp only [dp, List.mem_flatMap, List.mem_map] at h
      obtain ⟨e, he, t, ht, hr⟩ := h
      subst r
      exact Runs.step he ((ih _ _).mp ht)
    · intro h
      cases h with
      | step he ht =>
        simp only [dp, List.mem_flatMap, List.mem_map]
        exact ⟨_, he, _, (ih _ _).mpr ht, rfl⟩

def feasible (next : α → List (Result α)) (d : Nat) (q : α)
    (s w : Nat) : List (Result α) :=
  (dp next d q).filter fun r => decide (r.space ≤ s ∧ r.work ≤ w)

theorem mem_feasible_iff (next : α → List (Result α)) (d q s w r) :
    r ∈ feasible next d q s w ↔
      Runs next d q r ∧ r.space ≤ s ∧ r.work ≤ w := by
  simp [feasible, mem_dp_iff, and_assoc]

#print axioms mem_dp_iff
#print axioms mem_feasible_iff
end SpookyDP

namespace SpookyRound

def words (a : List α) : Nat → List (List α)
  | 0 => [[]]
  | n+1 => a.flatMap fun x => (words a n).map (x :: ·)

theorem mem_words (a : List α) (n : Nat) (xs : List α) :
    xs ∈ words a n ↔ xs.length = n ∧ ∀ x ∈ xs, x ∈ a := by
  induction n generalizing xs with
  | zero => cases xs <;> simp [words]
  | succ n ih =>
    cases xs with
    | nil => simp [words]
    | cons x xs => simp [words, ih, and_assoc, and_left_comm, and_comm]

inductive Move where
  | idle | pebble | unpebble
  deriving DecidableEq, Repr

def moves : List Move := [.idle, .pebble, .unpebble]

theorem mem_moves (m : Move) : m ∈ moves := by cases m <;> simp [moves]

structure Action where
  first : List Move
  ghosts : List Bool
  deriving DecidableEq

def actions (n : Nat) : List Action :=
  (words moves n).flatMap fun ms =>
    (words [false,true] n).map fun gs => ⟨ms,gs⟩

theorem mem_actions (n : Nat) (a : Action) :
    a ∈ actions n ↔ a.first.length = n ∧ a.ghosts.length = n := by
  cases a with
  | mk ms gs =>
    simp only [actions, List.mem_flatMap, List.mem_map, Action.mk.injEq]
    constructor
    · rintro ⟨xs,hxs,ys,hys,hx,hy⟩
      subst xs; subst ys
      exact ⟨(mem_words _ _ _).mp hxs |>.1, (mem_words _ _ _).mp hys |>.1⟩
    · rintro ⟨hm,hg⟩
      refine ⟨ms, (mem_words _ _ _).mpr ⟨hm, ?_⟩, gs, (mem_words _ _ _).mpr ⟨hg, ?_⟩, rfl, rfl⟩
      · intro x _; exact mem_moves x
      · intro x _; cases x <;> simp

structure Config (n : Nat) where
  peb : Fin n → Bool
  ghost : Fin n → Bool

def firstAt (a : Action) (v : Fin n) : Move := a.first[v.val]?.getD .idle
def ghostAt (a : Action) (v : Fin n) : Bool := a.ghosts[v.val]?.getD false

def afterFirst (q : Config n) (a : Action) : Config n :=
  ⟨fun v => match firstAt a v with
      | .idle => q.peb v | .pebble => true | .unpebble => false,
   fun v => match firstAt a v with
      | .pebble => false | _ => q.ghost v⟩

def afterRound (q : Config n) (a : Action) : Config n :=
  let p := afterFirst q a
  ⟨fun v => p.peb v && !(ghostAt a v),
   fun v => p.ghost v || ghostAt a v⟩

-- pred v u means u is an immediate dependency of v.
def Legal (pred : Fin n → Fin n → Bool) (q : Config n) (a : Action) : Prop :=
  (∀ v, ¬ (q.peb v = true ∧ q.ghost v = true)) ∧
  (∀ v, firstAt a v = .pebble → q.peb v = false) ∧
  (∀ v, firstAt a v = .unpebble → q.peb v = true) ∧
  (∀ v, firstAt a v ≠ .idle → ∀ u, pred v u = true → q.peb u = true) ∧
  (∀ v w, v ≠ w → firstAt a v ≠ .idle → firstAt a w ≠ .idle →
      ∀ u, (u = v ∨ pred v u = true) → ¬ (u = w ∨ pred w u = true)) ∧
  (∀ v, ghostAt a v = true → (afterFirst q a).peb v = true)

instance (pred : Fin n → Fin n → Bool) (q : Config n) (a : Action) :
    Decidable (Legal pred q a) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

def legalActions (pred : Fin n → Fin n → Bool) (q : Config n) : List Action :=
  (actions n).filter fun a => decide (Legal pred q a)

theorem mem_legalActions (pred : Fin n → Fin n → Bool) (q : Config n) (a : Action) :
    a ∈ legalActions pred q ↔
      a.first.length = n ∧ a.ghosts.length = n ∧ Legal pred q a := by
  simp [legalActions, mem_actions, and_assoc]

-- First-phase union, deliberately NOT just the two round endpoints.
def roundSpace (q : Config n) (a : Action) : Nat :=
  ((List.finRange n).filter fun v => q.peb v || (afterFirst q a).peb v).length

def roundWork (a : Action) : Nat :=
  (a.first.filter fun m => m != .idle).length


def edge (q : Config n) (a : Action) : SpookyDP.Result (Config n) :=
  ⟨afterRound q a, roundWork a, roundSpace q a⟩

def next (pred : Fin n → Fin n → Bool) (q : Config n) : List (SpookyDP.Result (Config n)) :=
  (legalActions pred q).map (edge q)

def PaperStep (pred : Fin n → Fin n → Bool) (q : Config n)
    (e : SpookyDP.Result (Config n)) : Prop :=
  ∃ a : Action, a.first.length = n ∧ a.ghosts.length = n ∧ Legal pred q a ∧ edge q a = e

theorem mem_next (pred : Fin n → Fin n → Bool) (q : Config n) (e) :
    e ∈ next pred q ↔ PaperStep pred q e := by
  simp only [next, List.mem_map, mem_legalActions, PaperStep]
  constructor
  · rintro ⟨a, ⟨h1,h2,h3⟩, h4⟩; exact ⟨a,h1,h2,h3,h4⟩
  · rintro ⟨a,h1,h2,h3,h4⟩; exact ⟨a,⟨h1,h2,h3⟩,h4⟩

inductive PaperRuns (pred : Fin n → Fin n → Bool) :
    Nat → Config n → SpookyDP.Result (Config n) → Prop
  | zero (q) : PaperRuns pred 0 q ⟨q,0,0⟩
  | step {d q e r} : PaperStep pred q e → PaperRuns pred d e.state r →
      PaperRuns pred (d+1) q (SpookyDP.prepend e r)

theorem runs_iff (pred : Fin n → Fin n → Bool) (d q r) :
    SpookyDP.Runs (next pred) d q r ↔ PaperRuns pred d q r := by
  constructor
  · intro h
    induction h with
    | zero q => exact PaperRuns.zero q
    | step he _ ih => exact PaperRuns.step ((mem_next _ _ _).mp he) ih
  · intro h
    induction h with
    | zero q => exact SpookyDP.Runs.zero q
    | step he _ ih => exact SpookyDP.Runs.step ((mem_next _ _ _).mpr he) ih

theorem dp_iff_paperRuns (pred : Fin n → Fin n → Bool) (d q r) :
    r ∈ SpookyDP.dp (next pred) d q ↔ PaperRuns pred d q r := by
  rw [SpookyDP.mem_dp_iff, runs_iff]

theorem feasible_iff_paperRuns (pred : Fin n → Fin n → Bool) (d q s w r) :
    r ∈ SpookyDP.feasible (next pred) d q s w ↔
      PaperRuns pred d q r ∧ r.space ≤ s ∧ r.work ≤ w := by
  rw [SpookyDP.mem_feasible_iff, runs_iff]

theorem afterRound_disjoint (pred : Fin n → Fin n → Bool) (q : Config n) (a : Action)
    (h : Legal pred q a) : ∀ v, ¬ ((afterRound q a).peb v = true ∧
      (afterRound q a).ghost v = true) := by
  intro v
  have hi := h.1 v
  cases hm : firstAt a v <;> cases hp : q.peb v <;>
    cases hg : q.ghost v <;> cases hb : ghostAt a v <;>
    simp_all [afterRound, afterFirst]

#eval (legalActions (n := 1) (fun _ _ => false) ⟨fun _ => false, fun _ => false⟩).length
#print axioms afterRound_disjoint
#print axioms dp_iff_paperRuns
#print axioms feasible_iff_paperRuns
#print axioms mem_words
#print axioms mem_actions
#print axioms mem_legalActions
end SpookyRound


namespace SmallTree
def pred3 (v u : Fin 3) : Bool := v.val == 0 && (u.val == 1 || u.val == 2)
def empty3 : SpookyRound.Config 3 := ⟨fun _ => false, fun _ => false⟩
def goal3 (q : SpookyRound.Config 3) : Bool :=
  (List.finRange 3).all fun v => q.peb v == (v.val == 0) && !q.ghost v
def outcomes3 (d : Nat) : List (Nat × Nat) :=
  ((SpookyDP.dp (SpookyRound.next pred3) d empty3).filter fun r => goal3 r.state).map fun r => (r.work,r.space)
#eval (List.range 4).map fun d => (d, outcomes3 d)
end SmallTree
