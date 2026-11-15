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

namespace ClosedFrontier
structure Cost where
  depth : Nat
  work : Nat
  space : Nat
  deriving DecidableEq

def Dom (a b : Cost) : Prop := a.depth ≤ b.depth ∧ a.work ≤ b.work ∧ a.space ≤ b.space
instance (a b : Cost) : Decidable (Dom a b) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))
def advance (c : Cost) (e : SpookyDP.Result α) : Cost := ⟨c.depth+1,c.work+e.work,max c.space e.space⟩
def finish (c : Cost) (d : Nat) (r : SpookyDP.Result α) : Cost := ⟨c.depth+d,c.work+r.work,max c.space r.space⟩
def Covers (front : α → List Cost) (q : α) (c : Cost) : Prop := ∃ f ∈ front q, Dom f c

def Closed (front : α → List Cost) (next : α → List (SpookyDP.Result α)) : Prop :=
  ∀ q f, f ∈ front q → ∀ e, e ∈ next q → Covers front e.state (advance f e)

theorem dom_trans {a b c : Cost} (h : Dom a b) (k : Dom b c) : Dom a c := by
  unfold Dom at *; omega

theorem advance_mono {a b : Cost} (h : Dom a b) (e : SpookyDP.Result α) :
    Dom (advance a e) (advance b e) := by
  unfold Dom advance at *; dsimp at *; omega

theorem covered_step (hc : Closed front next) (h : Covers front q c)
    (he : e ∈ next q) : Covers front e.state (advance c e) := by
  obtain ⟨f,hf,hfc⟩ := h
  obtain ⟨g,hg,hgf⟩ := hc q f hf e he
  exact ⟨g,hg,dom_trans hgf (advance_mono hfc e)⟩

theorem covers_all_runs (hc : Closed front next)
    (h : SpookyDP.Runs next d q r) (h0 : Covers front q c) :
    Covers front r.state (finish c d r) := by
  induction h generalizing c with
  | zero q => simpa [finish] using h0
  | @step d q e r he hr ih =>
    have hh := ih (covered_step hc h0 he)
    simpa [finish, advance, SpookyDP.prepend, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.max_assoc] using hh

def checkClosed (vertices : List α) (front : α → List Cost)
    (next : α → List (SpookyDP.Result α)) : Bool :=
  vertices.all fun q => (front q).all fun f => (next q).all fun e =>
    (front e.state).any fun g => decide (Dom g (advance f e))

theorem checkClosed_sound (hall : ∀ q, q ∈ vertices)
    (h : checkClosed vertices front next = true) : Closed front next := by
  intro q f hf e he
  have hq := List.all_eq_true.mp h q (hall q)
  have hfe := List.all_eq_true.mp (List.all_eq_true.mp hq f hf) e he
  obtain ⟨g,hg,hd⟩ := List.any_eq_true.mp hfe
  exact ⟨g,hg,of_decide_eq_true hd⟩

-- A finite CLOSED frontier covering the initial label bounds ALL depths,
-- not just the depths observed by the enumerating program.
theorem goal_lower_bound (hc : Closed front next)
    (h0 : Covers front start ⟨0,0,0⟩)
    (h : SpookyDP.Runs next d start r) (hg : r.state = goal) :
    ∃ f ∈ front goal, f.depth ≤ d ∧ f.work ≤ r.work ∧ f.space ≤ r.space := by
  have hh := covers_all_runs hc h h0
  simpa [Covers,finish,Dom,hg] using hh
#print axioms covers_all_runs
#print axioms checkClosed_sound
#print axioms goal_lower_bound
end ClosedFrontier
