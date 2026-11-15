import Std
namespace CutBound
inductive State | empty | pebble | ghost deriving DecidableEq
inductive Event | idle | compute | uncompute | ghost deriving DecidableEq
inductive Step : State → Event → State → Prop
 | idle (s) : Step s .idle s
 | computeEmpty : Step .empty .compute .pebble
 | computeGhost : Step .ghost .compute .pebble
 | uncompute : Step .pebble .uncompute .empty
 | ghost : Step .pebble .ghost .ghost
inductive Trace : State → List Event → State → Prop
 | nil (s) : Trace s [] s
 | cons : Step s e t → Trace t es u → Trace s (e::es) u

def count (target : Event) (es : List Event) : Nat :=
  (es.filter fun e => e == target).length

def debt : State → Nat | .empty => 0 | _ => 1

theorem cleanup_debt (h : Trace s es t) : debt s ≤ count .uncompute es + debt t := by
  induction h with
  | nil s => simp [count]
  | @cons s e t es u hstep htail ih =>
    cases hstep <;> simp_all [count,debt,List.filter_cons] <;> omega

theorem cleanup_required (h : Trace s es .empty) (hs : s ≠ .empty) :
    1 ≤ count .uncompute es := by
  have hh := cleanup_debt h
  cases s <;> simp_all [debt]

theorem missing_requires_recompute (h : Trace s es t)
    (hu : Event.uncompute ∈ es) (hs : s ≠ .pebble) :
    1 ≤ count .compute es := by
  induction h with
  | nil s => simp at hu
  | @cons s e t es u hstep htail ih =>
    cases hstep <;> simp_all [count,List.filter_cons] <;> omega

-- Per-vertex cut accounts. Their graph-wide existence is NOT assumed to be
-- automatically proved by these scalar lemmas; see report's outstanding bridge.
structure Account where
  preCompute : Nat
  postCompute : Nat
  postUncompute : Nat
  cutPebble : Nat
  isRoot : Nat

def Valid (a : Account) : Prop :=
  1 ≤ a.preCompute ∧ 1 ≤ a.postCompute+a.cutPebble ∧ 1 ≤ a.postUncompute+a.isRoot

def work (as : List Account) : Nat :=
  (as.map fun a => a.preCompute+a.postCompute+a.postUncompute).sum
def pebbles (as : List Account) : Nat := (as.map Account.cutPebble).sum
def roots (as : List Account) : Nat := (as.map Account.isRoot).sum

theorem cut_charging (as : List Account) (hv : ∀ a ∈ as, Valid a) :
    3*as.length ≤ work as+pebbles as+roots as := by
  induction as with
  | nil => simp [work,pebbles,roots]
  | cons a as ih =>
    have ha := hv a (by simp)
    have ht := ih (fun b hb => hv b (by simp [hb]))
    simp only [work,pebbles,roots,List.map_cons,List.sum_cons,List.length_cons] at *
    unfold Valid at ha
    omega

theorem space_work_bound (as : List Account) (hv : ∀ a ∈ as, Valid a)
    (hr : roots as = 1) (hp : pebbles as ≤ S) :
    3*as.length ≤ work as+S+1 := by
  have h := cut_charging as hv
  omega
#print axioms cleanup_required
#print axioms missing_requires_recompute
#print axioms space_work_bound
end CutBound
