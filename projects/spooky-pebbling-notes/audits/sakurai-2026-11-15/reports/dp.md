# Finite-round DP: soundness and completeness (preparatory C)
Source model: https://arxiv.org/html/2610.09434v1 section 2.3. A round consists of pairwise active-set-disjoint Pebble/Unpebble actions followed by arbitrary Ghost actions. Preconditions are checked at first-phase entry. Space is cardinality of union of entry pebbles and post-first-phase pebbles. Work counts Pebble+Unpebble; depth counts every round including ghost-only rounds.

This artifact proves an ABSTRACT recurrence for any finite successor list. It does not yet prove that an executable successor list enumerates exactly the paper's legal rounds. That connection remains a required obligation.

Result stores final state, total work, peak round space. dp(0,q) is [(q,0,0)]; dp(d+1,q) flatMaps all first edges with dp(d,target), adding work and taking max space. Runs is the inductive exact-length path semantics.

Verified theorem SpookyDP.mem_dp_iff: result is in dp iff an exact-d-round run has that result. SpookyDP.mem_feasible_iff: filtered result membership iff such a run exists and result space/work satisfy budgets. No Pareto pruning and no asymptotic theorem are proved. Empty depth has peak0; concrete start is empty, so this convention matches intended initial case.

Lean4.35.0 commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, rc0, standard axioms propext and Quot.sound, no sorryAx. Source contains no sorry/admit. One harmless unused simp argument warning.

A1: process preexec failed at macOS resource limit setup; Lean not started. A2: supported Lean -j1 -M1024 with wall30; success 2026-11-15T13:42:56.316953 to 13:42:56.846480 UTC, CPU0.282805s, peak660193280 bytes. Original finite reservation preserved. Compile log and event files enclosed.

Storage: Mac source and logs persisted. Existing SSH <host>-ts failed with DNS resolution error; remote storage not complete. No job stopped or restarted and no credentials/settings changed.

Novelty: standard finite-path enumeration induction, preparatory C, not a new S result. Next: concrete round enumerator equivalence, Pareto pruning soundness/completeness, and certified small-tree boundary computation.

## Exact checked source
```lean
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

```
