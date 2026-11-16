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
