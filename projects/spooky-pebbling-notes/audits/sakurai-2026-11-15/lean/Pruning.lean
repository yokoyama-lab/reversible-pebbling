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


namespace Certificates
def pred7 (v u : Fin 7) : Bool := u.val == 2*v.val+1 || u.val == 2*v.val+2
def empty7 : SpookyRound.Config 7 := ⟨fun _ => false, fun _ => false⟩
def goal7 (q : SpookyRound.Config 7) : Bool :=
  (List.finRange 7).all fun v => q.peb v == (v.val == 0) && !q.ghost v
def check (q : SpookyRound.Config 7) (w s : Nat) : List SpookyRound.Action → Nat → Nat → Bool
 | [], W, S => goal7 q && w == W && s == S
 | a::as, W, S => decide (a.first.length = 7 ∧ a.ghosts.length = 7 ∧ SpookyRound.Legal pred7 q a) &&
     check (SpookyRound.afterRound q a) (w + SpookyRound.roundWork a) (max s (SpookyRound.roundSpace q a)) as W S
def witness0 : List SpookyRound.Action := [⟨[.idle,.idle,.idle,.pebble,.pebble,.pebble,.pebble],[false,false,false,false,false,false,false]⟩,⟨[.idle,.pebble,.pebble,.idle,.idle,.idle,.idle],[false,false,false,false,false,false,false]⟩,⟨[.pebble,.idle,.idle,.idle,.idle,.idle,.idle],[false,false,false,false,false,false,false]⟩,⟨[.idle,.unpebble,.unpebble,.idle,.idle,.idle,.idle],[false,false,false,false,false,false,false]⟩,⟨[.idle,.idle,.idle,.unpebble,.unpebble,.unpebble,.unpebble],[false,false,false,false,false,false,false]⟩]
theorem certificate0 : check empty7 0 0 witness0 13 7 = true ∧ witness0.length = 5 := by decide
#print axioms certificate0
def witness1 : List SpookyRound.Action := [⟨[.idle,.idle,.idle,.pebble,.pebble,.pebble,.pebble],[false,false,false,false,false,false,false]⟩,⟨[.idle,.pebble,.pebble,.idle,.idle,.idle,.idle],[false,false,false,false,false,false,true]⟩,⟨[.pebble,.idle,.idle,.idle,.idle,.idle,.idle],[false,false,false,false,false,false,false]⟩,⟨[.idle,.unpebble,.idle,.idle,.idle,.idle,.idle],[false,false,false,false,false,false,false]⟩,⟨[.idle,.idle,.idle,.idle,.idle,.idle,.pebble],[false,false,false,false,false,false,false]⟩,⟨[.idle,.idle,.unpebble,.idle,.idle,.idle,.idle],[false,false,false,false,false,false,false]⟩,⟨[.idle,.idle,.idle,.unpebble,.unpebble,.unpebble,.unpebble],[false,false,false,false,false,false,false]⟩]
theorem certificate1 : check empty7 0 0 witness1 14 6 = true ∧ witness1.length = 7 := by decide
#print axioms certificate1
def witness2 : List SpookyRound.Action := [⟨[.idle,.idle,.idle,.idle,.idle,.pebble,.pebble],[false,false,false,false,false,false,false]⟩,⟨[.idle,.idle,.pebble,.pebble,.pebble,.idle,.idle],[false,false,false,false,false,true,true]⟩,⟨[.idle,.pebble,.idle,.idle,.idle,.idle,.idle],[false,false,false,false,false,false,false]⟩,⟨[.pebble,.idle,.idle,.idle,.idle,.idle,.idle],[false,false,false,false,false,false,false]⟩,⟨[.idle,.unpebble,.idle,.idle,.idle,.idle,.idle],[false,false,false,false,true,false,false]⟩,⟨[.idle,.idle,.idle,.unpebble,.idle,.pebble,.pebble],[false,false,false,false,false,false,false]⟩,⟨[.idle,.idle,.unpebble,.idle,.pebble,.idle,.idle],[false,false,false,false,false,false,false]⟩,⟨[.idle,.idle,.idle,.idle,.unpebble,.unpebble,.unpebble],[false,false,false,false,false,false,false]⟩]
theorem certificate2 : check empty7 0 0 witness2 16 5 = true ∧ witness2.length = 8 := by decide
#print axioms certificate2
def witness3 : List SpookyRound.Action := [⟨[.idle,.idle,.idle,.idle,.idle,.pebble,.pebble],[false,false,false,false,false,false,false]⟩,⟨[.idle,.idle,.pebble,.pebble,.pebble,.idle,.idle],[false,false,false,false,false,true,true]⟩,⟨[.idle,.pebble,.idle,.idle,.idle,.idle,.idle],[false,false,false,false,false,false,false]⟩,⟨[.pebble,.idle,.idle,.idle,.idle,.idle,.idle],[false,false,false,false,false,false,false]⟩,⟨[.idle,.unpebble,.idle,.idle,.idle,.idle,.idle],[false,false,false,false,false,false,false]⟩,⟨[.idle,.idle,.idle,.unpebble,.idle,.idle,.idle],[false,false,false,false,false,false,false]⟩,⟨[.idle,.idle,.idle,.idle,.idle,.pebble,.pebble],[false,false,false,false,false,false,false]⟩,⟨[.idle,.idle,.unpebble,.idle,.idle,.idle,.idle],[false,false,false,false,false,false,false]⟩,⟨[.idle,.idle,.idle,.idle,.unpebble,.unpebble,.unpebble],[false,false,false,false,false,false,false]⟩]
theorem certificate3 : check empty7 0 0 witness3 15 5 = true ∧ witness3.length = 9 := by decide
#print axioms certificate3
def witness4 : List SpookyRound.Action := [⟨[.idle,.idle,.idle,.idle,.idle,.pebble,.pebble],[false,false,false,false,false,false,false]⟩,⟨[.idle,.idle,.pebble,.idle,.idle,.idle,.idle],[false,false,false,false,false,true,true]⟩,⟨[.idle,.idle,.idle,.pebble,.pebble,.idle,.idle],[false,false,false,false,false,false,false]⟩,⟨[.idle,.pebble,.idle,.idle,.idle,.idle,.idle],[false,false,false,false,true,false,false]⟩,⟨[.pebble,.idle,.idle,.idle,.idle,.idle,.idle],[false,false,true,false,false,false,false]⟩,⟨[.idle,.idle,.idle,.idle,.pebble,.idle,.idle],[false,false,false,false,false,false,false]⟩,⟨[.idle,.unpebble,.idle,.idle,.idle,.idle,.idle],[false,false,false,false,false,false,false]⟩,⟨[.idle,.idle,.idle,.unpebble,.idle,.idle,.idle],[false,false,false,false,false,false,false]⟩,⟨[.idle,.idle,.idle,.idle,.unpebble,.pebble,.pebble],[false,false,false,false,false,false,false]⟩,⟨[.idle,.idle,.pebble,.idle,.idle,.idle,.idle],[false,false,false,false,false,false,false]⟩,⟨[.idle,.idle,.unpebble,.idle,.idle,.idle,.idle],[false,false,false,false,false,false,false]⟩,⟨[.idle,.idle,.idle,.idle,.idle,.unpebble,.unpebble],[false,false,false,false,false,false,false]⟩]
theorem certificate4 : check empty7 0 0 witness4 17 4 = true ∧ witness4.length = 12 := by decide
#print axioms certificate4
end Certificates

namespace Certificates
theorem check_sound (as : List SpookyRound.Action) (q : SpookyRound.Config 7) (w s W S : Nat)
    (h : check q w s as W S = true) :
    ∃ r, SpookyRound.PaperRuns pred7 as.length q r ∧ goal7 r.state = true ∧
      w + r.work = W ∧ max s r.space = S := by
  induction as generalizing q w s with
  | nil =>
    simp only [check, Bool.and_eq_true, beq_iff_eq] at h
    refine ⟨⟨q,0,0⟩, SpookyRound.PaperRuns.zero q, ?_⟩
    simpa [and_assoc] using h
  | cons a as ih =>
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨r, hr, hg, hw, hs⟩ := ih _ _ _ h.2
    refine ⟨SpookyDP.prepend (SpookyRound.edge q a) r, ?_, hg, ?_, ?_⟩
    · apply SpookyRound.PaperRuns.step (e := SpookyRound.edge q a)
      · exact ⟨a,h.1.1,h.1.2.1,h.1.2.2,rfl⟩
      · exact hr
    · simpa [SpookyDP.prepend, SpookyRound.edge, Nat.add_assoc] using hw
    · simpa [SpookyDP.prepend, SpookyRound.edge, Nat.max_assoc] using hs
#print axioms check_sound
end Certificates

namespace SpookyRound
theorem prepend_assoc (a b c : SpookyDP.Result α) :
    SpookyDP.prepend a (SpookyDP.prepend b c) = SpookyDP.prepend (SpookyDP.prepend a b) c := by
  simp [SpookyDP.prepend, Nat.add_assoc, Nat.max_assoc]

theorem append_runs (pred : Fin n → Fin n → Bool) {d q r}
    (h : PaperRuns pred d q r) {k t} (ht : PaperRuns pred k r.state t) :
    PaperRuns pred (d+k) q (SpookyDP.prepend r t) := by
  induction h with
  | zero q => simpa [SpookyDP.prepend] using ht
  | @step d q e r he hr ih =>
    have hh := PaperRuns.step he (ih ht)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, prepend_assoc] using hh

-- A dominated prefix to the SAME configuration is unnecessary for every continuation.
theorem same_state_prune_safe (pred : Fin n → Fin n → Bool)
    {d₁ d₂ k : Nat} {q : Config n} {r₁ r₂ t : SpookyDP.Result (Config n)}
    (h₁ : PaperRuns pred d₁ q r₁) (h₂ : PaperRuns pred d₂ q r₂)
    (same : r₁.state = r₂.state) (hd : d₁ ≤ d₂)
    (hw : r₁.work ≤ r₂.work) (hs : r₁.space ≤ r₂.space)
    (ht : PaperRuns pred k r₂.state t) :
    ∃ r, PaperRuns pred (d₁+k) q r ∧ r.state = t.state ∧
      d₁+k ≤ d₂+k ∧ r.work ≤ (SpookyDP.prepend r₂ t).work ∧
      r.space ≤ (SpookyDP.prepend r₂ t).space := by
  have ht₁ : PaperRuns pred k r₁.state t := by simpa [same] using ht
  refine ⟨SpookyDP.prepend r₁ t, append_runs pred h₁ ht₁, rfl,
    Nat.add_le_add_right hd k, ?_, ?_⟩
  · exact Nat.add_le_add_right hw t.work
  · simp only [SpookyDP.prepend]
    omega
#print axioms append_runs
#print axioms same_state_prune_safe
end SpookyRound

namespace Certificates
theorem feasible0 : ∃ r, SpookyRound.PaperRuns pred7 5 empty7 r ∧ goal7 r.state = true ∧ r.work = 13 ∧ r.space = 7 := by
  have h := check_sound witness0 empty7 0 0 13 7 certificate0.1
  simpa [certificate0.2] using h
#print axioms feasible0
theorem feasible1 : ∃ r, SpookyRound.PaperRuns pred7 7 empty7 r ∧ goal7 r.state = true ∧ r.work = 14 ∧ r.space = 6 := by
  have h := check_sound witness1 empty7 0 0 14 6 certificate1.1
  simpa [certificate1.2] using h
#print axioms feasible1
theorem feasible2 : ∃ r, SpookyRound.PaperRuns pred7 8 empty7 r ∧ goal7 r.state = true ∧ r.work = 16 ∧ r.space = 5 := by
  have h := check_sound witness2 empty7 0 0 16 5 certificate2.1
  simpa [certificate2.2] using h
#print axioms feasible2
theorem feasible3 : ∃ r, SpookyRound.PaperRuns pred7 9 empty7 r ∧ goal7 r.state = true ∧ r.work = 15 ∧ r.space = 5 := by
  have h := check_sound witness3 empty7 0 0 15 5 certificate3.1
  simpa [certificate3.2] using h
#print axioms feasible3
theorem feasible4 : ∃ r, SpookyRound.PaperRuns pred7 12 empty7 r ∧ goal7 r.state = true ∧ r.work = 17 ∧ r.space = 4 := by
  have h := check_sound witness4 empty7 0 0 17 4 certificate4.1
  simpa [certificate4.2] using h
#print axioms feasible4
end Certificates
namespace SmallTree
def pred3 (v u : Fin 3) : Bool := v.val == 0 && (u.val == 1 || u.val == 2)
def empty3 : SpookyRound.Config 3 := ⟨fun _ => false, fun _ => false⟩
def goal3 (q : SpookyRound.Config 3) : Bool :=
  (List.finRange 3).all fun v => q.peb v == (v.val == 0) && !q.ghost v
def outcomes3 (d : Nat) : List (Nat × Nat) :=
  ((SpookyDP.dp (SpookyRound.next pred3) d empty3).filter fun r => goal3 r.state).map fun r => (r.work,r.space)
#eval (List.range 4).map fun d => (d, outcomes3 d)


theorem shallow_no_goal_eval : ∀ d : Fin 3,
    (SpookyDP.dp (SpookyRound.next pred3) d.val empty3).all
      (fun r => !goal3 r.state) = true := by native_decide

theorem no_goal_lt_three {d : Nat} {r : SpookyDP.Result (SpookyRound.Config 3)}
    (hd : d < 3) (h : SpookyRound.PaperRuns pred3 d empty3 r) :
    goal3 r.state = false := by
  have hc := shallow_no_goal_eval ⟨d,hd⟩
  have hm := (SpookyRound.dp_iff_paperRuns pred3 d empty3 r).mpr h
  have hn := List.all_eq_true.mp hc r hm
  simpa using hn
#print axioms no_goal_lt_three
end SmallTree

namespace SmallTree
def a0 : SpookyRound.Action := ⟨[.idle,.pebble,.pebble],[false,false,false]⟩
def a1 : SpookyRound.Action := ⟨[.pebble,.idle,.idle],[false,false,false]⟩
def a2 : SpookyRound.Action := ⟨[.idle,.unpebble,.unpebble],[false,false,false]⟩
def q1 := SpookyRound.afterRound empty3 a0
def q2 := SpookyRound.afterRound q1 a1
def q3 := SpookyRound.afterRound q2 a2
def result3 := SpookyDP.prepend (SpookyRound.edge empty3 a0)
  (SpookyDP.prepend (SpookyRound.edge q1 a1)
    (SpookyDP.prepend (SpookyRound.edge q2 a2) ⟨q3,0,0⟩))
theorem run_three : SpookyRound.PaperRuns pred3 3 empty3 result3 := by
  apply SpookyRound.PaperRuns.step (e := SpookyRound.edge empty3 a0)
  · exact ⟨a0,by decide,by decide,by decide,rfl⟩
  apply SpookyRound.PaperRuns.step (e := SpookyRound.edge q1 a1)
  · exact ⟨a1,by decide,by decide,by decide,rfl⟩
  apply SpookyRound.PaperRuns.step (e := SpookyRound.edge q2 a2)
  · exact ⟨a2,by decide,by decide,by decide,rfl⟩
  exact SpookyRound.PaperRuns.zero q3

theorem result_three : goal3 result3.state = true ∧ result3.work = 5 ∧ result3.space = 3 := by decide

theorem depth_min_three {d : Nat} {r : SpookyDP.Result (SpookyRound.Config 3)}
    (h : SpookyRound.PaperRuns pred3 d empty3 r) (hg : goal3 r.state = true) : 3 ≤ d := by
  by_cases hd : d < 3
  · have hn := no_goal_lt_three hd h
    simp [hg] at hn
  · omega
#print axioms run_three
#print axioms result_three
#print axioms depth_min_three
end SmallTree
