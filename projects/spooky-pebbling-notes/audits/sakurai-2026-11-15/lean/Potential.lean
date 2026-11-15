import ConcreteRound
namespace SpookyPotential
open SpookyRound SpookyDP
-- A local certificate is only required on steps within the chosen peak budget.
-- This is a reusable telescoping lemma, not a new pebbling lower bound.
def LocalBound (pred : Fin n → Fin n → Bool) (S a b : Nat)
    (phi : Config n → Nat) : Prop :=
  ∀ q e, PaperStep pred q e → e.space ≤ S →
    phi q ≤ a * e.work + b + phi e.state

theorem all_runs_bound (hlocal : LocalBound pred S a b phi)
    (hr : PaperRuns pred d q r) (hs : r.space ≤ S) :
    phi q ≤ a * r.work + b * d + phi r.state := by
  induction hr with
  | zero q => simp
  | @step d q e r he hr ih =>
    have heS : e.space ≤ S := by simpa [prepend] using (Nat.le_trans (Nat.le_max_left e.space r.space) hs)
    have hrS : r.space ≤ S := by simpa [prepend] using (Nat.le_trans (Nat.le_max_right e.space r.space) hs)
    have hstep := hlocal q e he heS
    have htail := ih hrS
    simp only [prepend] at *
    simp only [Nat.mul_add, Nat.mul_succ]
    omega

theorem budget_bound (hlocal : LocalBound pred S a b phi)
    (hr : PaperRuns pred d q r) (hs : r.space ≤ S)
    (hd : d ≤ D) (hw : r.work ≤ W) (hg : phi r.state = 0) :
    phi q ≤ a * W + b * D := by
  have h := all_runs_bound hlocal hr hs
  have hw' := Nat.mul_le_mul_left a hw
  have hd' := Nat.mul_le_mul_left b hd
  omega

-- To certify a graph-specific lower bound it suffices to verify legal actions,
-- without trusting any candidate successor-table generator.
theorem actions_to_local
    (ha : ∀ (q : Config n) (act : Action), act.first.length = n → act.ghosts.length = n →
      Legal pred q act → roundSpace q act ≤ S →
      phi q ≤ a * roundWork act + b + phi (afterRound q act)) :
    LocalBound pred S a b phi := by
  intro q e he hs
  obtain ⟨act,hm,hg,hl,he⟩ := he
  subst e
  exact ha q act hm hg hl hs
#print axioms all_runs_bound
#print axioms budget_bound
#print axioms actions_to_local
end SpookyPotential
