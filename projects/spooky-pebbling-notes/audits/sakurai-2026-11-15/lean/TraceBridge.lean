import ConcreteRound
import CutBound
namespace TraceBridge
open SpookyRound
variable {n : Nat} {pred : Fin n → Fin n → Bool} {q : Config n} {a : Action}

def kind (q : Config n) (v : Fin n) : CutBound.State :=
  if q.peb v then .pebble else if q.ghost v then .ghost else .empty

def firstEvent : Move → CutBound.Event
 | .idle => .idle | .pebble => .compute | .unpebble => .uncompute

def secondEvent (g : Bool) : CutBound.Event := if g then .ghost else .idle

theorem first_scalar (hl : Legal pred q a) (v : Fin n) :
    CutBound.Step (kind q v) (firstEvent (firstAt a v)) (kind (afterFirst q a) v) := by
  have hd := hl.1 v
  have hp := hl.2.1 v
  have hu := hl.2.2.1 v
  cases hm : firstAt a v <;> cases hq : q.peb v <;> cases hg : q.ghost v <;>
    simp_all [kind,firstEvent,afterFirst] <;> constructor

theorem second_scalar (hl : Legal pred q a) (v : Fin n) :
    CutBound.Step (kind (afterFirst q a) v) (secondEvent (ghostAt a v)) (kind (afterRound q a) v) := by
  have hh := hl.2.2.2.2.2 v
  cases hg : ghostAt a v <;> cases hp : (afterFirst q a).peb v <;>
    cases hq : (afterFirst q a).ghost v <;>
    simp_all [kind,secondEvent,afterRound] <;> constructor

theorem scalar_round (hl : Legal pred q a) (v : Fin n) :
    CutBound.Trace (kind q v) [firstEvent (firstAt a v), secondEvent (ghostAt a v)]
      (kind (afterRound q a) v) :=
  CutBound.Trace.cons (first_scalar hl v)
    (CutBound.Trace.cons (second_scalar hl v) (CutBound.Trace.nil _))
inductive ActionRuns (pred : Fin n → Fin n → Bool) :
    Config n → List Action → SpookyDP.Result (Config n) → Prop
 | nil (q : Config n) : ActionRuns pred q [] ⟨q,0,0⟩
 | cons {q : Config n} {a : Action} {as : List Action} {r : SpookyDP.Result (Config n)} : a.first.length = n → a.ghosts.length = n → Legal pred q a →
     ActionRuns pred (afterRound q a) as r →
     ActionRuns pred q (a::as) (SpookyDP.prepend (edge q a) r)

theorem extract_actions (h : PaperRuns pred d q r) :
    ∃ as, as.length = d ∧ ActionRuns pred q as r := by
  induction h with
  | zero q => exact ⟨[],rfl,ActionRuns.nil q⟩
  | @step d q e r he hr ih =>
    obtain ⟨a,hm,hg,hl,he⟩ := he
    subst e
    obtain ⟨as,hd,hh⟩ := ih
    exact ⟨a::as,by simp [hd],ActionRuns.cons hm hg hl hh⟩

def events (v : Fin n) : List Action → List CutBound.Event
 | [] => []
 | a::as => firstEvent (firstAt a v)::secondEvent (ghostAt a v)::events v as

theorem trace_append (h : CutBound.Trace s es t) (g : CutBound.Trace t fs u) :
    CutBound.Trace s (es++fs) u := by
  induction h with
  | nil s => exact g
  | cons hs ht ih => exact CutBound.Trace.cons hs (ih g)

theorem actionruns_scalar (h : ActionRuns pred q as r) (v : Fin n) :
    CutBound.Trace (kind q v) (events v as) (kind r.state v) := by
  induction h with
  | nil q => exact CutBound.Trace.nil _
  | cons hm hg hl ht ih =>
    exact CutBound.Trace.cons (first_scalar hl v) (CutBound.Trace.cons (second_scalar hl v) ih)

theorem paperRuns_scalar (h : PaperRuns pred d q r) :
    ∃ as, as.length = d ∧ ActionRuns pred q as r ∧
      ∀ v, CutBound.Trace (kind q v) (events v as) (kind r.state v) := by
  obtain ⟨as,hd,ha⟩ := extract_actions h
  exact ⟨as,hd,ha,actionruns_scalar ha⟩

@[simp] theorem first_uncompute (m : Move) :
    firstEvent m = .uncompute ↔ m = .unpebble := by cases m <;> simp [firstEvent]
@[simp] theorem second_not_uncompute (g : Bool) :
    secondEvent g ≠ .uncompute := by cases g <;> simp [secondEvent]

theorem uncompute_in_events (v : Fin n) (as : List Action) :
    CutBound.Event.uncompute ∈ events v as ↔ ∃ a ∈ as, firstAt a v = .unpebble := by
  induction as with
  | nil => simp [events]
  | cons a as ih =>
    cases hm : firstAt a v <;> cases hg : ghostAt a v <;> simp [events,ih,hm,hg,firstEvent,secondEvent]

theorem cleanup_action_exists (h : ActionRuns pred q as r) (v : Fin n)
    (hq : kind q v ≠ .empty) (hr : kind r.state v = .empty) :
    ∃ a ∈ as, firstAt a v = .unpebble := by
  have ht := actionruns_scalar h v
  rw [hr] at ht
  have hc := CutBound.cleanup_required ht hq
  unfold CutBound.count at hc
  obtain ⟨e,he⟩ := List.exists_mem_of_length_pos (by omega : 0 < ((events v as).filter fun e => e == .uncompute).length)
  have hh := List.mem_filter.mp he
  have heq : e = .uncompute := by simpa using hh.2
  subst e
  exact (uncompute_in_events v as).mp hh.1
theorem dependency_nonempty_after (hl : Legal pred q a) (v u : Fin n)
    (hne : v ≠ u) (hv : firstAt a v ≠ .idle) (hu : pred v u = true) :
    kind (afterRound q a) u ≠ .empty := by
  have hp := hl.2.2.2.1 v hv u hu
  have hidle : firstAt a u = .idle := by
    by_cases hh : firstAt a u = .idle
    · exact hh
    exfalso
    exact hl.2.2.2.2.1 v u hne hv hh u (Or.inr hu) (Or.inl rfl)
  cases hg : ghostAt a u <;> simp [kind,afterRound,afterFirst,hidle,hp,hg]

theorem child_cleanup_later (hl : Legal pred q a) (v u : Fin n)
    (hne : v ≠ u) (hv : firstAt a v ≠ .idle) (hu : pred v u = true)
    (ht : ActionRuns pred (afterRound q a) as r) (hf : kind r.state u = .empty) :
    ∃ b ∈ as, firstAt b u = .unpebble :=
  cleanup_action_exists ht u (dependency_nonempty_after hl v u hne hv hu) hf

theorem split_actions (xs ys : List Action) (h : ActionRuns pred q (xs++ys) r) :
    ∃ p t, ActionRuns pred q xs p ∧ ActionRuns pred p.state ys t ∧ t.state = r.state := by
  induction xs generalizing q r with
  | nil => exact ⟨⟨q,0,0⟩,r,ActionRuns.nil q,h,rfl⟩
  | cons a xs ih =>
    cases h with
    | cons hm hg hl ht =>
      obtain ⟨p,t,hp,ht,hs⟩ := ih ht
      exact ⟨SpookyDP.prepend (edge q a) p,t,ActionRuns.cons hm hg hl hp,ht,hs⟩

-- Any active parent occurrence forces a STRICTLY LATER child-uncompute.
-- Thus a final child-uncompute occurs after the final active parent event.
theorem cleanup_after_occurrence (xs ys : List Action)
    (h : ActionRuns pred q (xs++a::ys) r) (v u : Fin n)
    (hne : v ≠ u) (hv : firstAt a v ≠ .idle) (hu : pred v u = true)
    (hf : kind r.state u = .empty) :
    ∃ b ∈ ys, firstAt b u = .unpebble := by
  obtain ⟨p,t,hp,ht,hs⟩ := split_actions xs (a::ys) h
  have hfinal : kind t.state u = .empty := by rw [hs]; exact hf
  cases ht with
  | cons hm hg hl ht =>
    apply child_cleanup_later hl v u hne hv hu ht
    simpa only [SpookyDP.prepend] using hfinal
def occupied : CutBound.State → Nat | .pebble => 1 | _ => 0

theorem compute_charge (h : CutBound.Trace s es t) :
    occupied t ≤ CutBound.count .compute es + occupied s := by
  induction h with
  | nil s => simp [CutBound.count]
  | cons hs ht ih => cases hs <;> simp_all [CutBound.count,occupied] <;> omega

theorem compute_in_events (v : Fin n) (as : List Action) :
    CutBound.Event.compute ∈ events v as ↔ ∃ a ∈ as, firstAt a v = .pebble := by
  induction as with
  | nil => simp [events]
  | cons a as ih =>
    cases hm : firstAt a v <;> cases hg : ghostAt a v <;> simp [events,ih,hm,hg,firstEvent,secondEvent]

theorem compute_action_exists (h : ActionRuns pred q as r) (v : Fin n)
    (hq : kind q v ≠ .pebble) (hr : kind r.state v = .pebble) :
    ∃ a ∈ as, firstAt a v = .pebble := by
  have hc := compute_charge (actionruns_scalar h v)
  have hz : occupied (kind q v) = 0 := by cases hh : kind q v <;> simp_all [occupied]
  rw [hr,hz] at hc
  simp only [occupied,Nat.add_zero] at hc
  unfold CutBound.count at hc
  obtain ⟨e,he⟩ := List.exists_mem_of_length_pos (by omega : 0 < ((events v as).filter fun e => e == .compute).length)
  have hh := List.mem_filter.mp he
  have heq : e = .compute := by simpa using hh.2
  subst e
  exact (compute_in_events v as).mp hh.1

theorem compute_before_occurrence (xs ys : List Action)
    (h : ActionRuns pred q (xs++a::ys) r) (v u : Fin n)
    (hv : firstAt a v ≠ .idle) (hu : pred v u = true)
    (hstart : kind q u ≠ .pebble) :
    ∃ b ∈ xs, firstAt b u = .pebble := by
  obtain ⟨p,t,hp,ht,hs⟩ := split_actions xs (a::ys) h
  cases ht with
  | cons hm hg hl ht =>
    apply compute_action_exists hp u hstart
    have hh := hl.2.2.2.1 v hv u hu
    simp [kind,hh]

-- For a nonpebbled initial child and empty final child, EVERY parent active
-- occurrence has a child computation strictly before and uncomputation after.
theorem parent_bracketed (xs ys : List Action)
    (h : ActionRuns pred q (xs++a::ys) r) (v u : Fin n)
    (hne : v ≠ u) (hv : firstAt a v ≠ .idle) (hu : pred v u = true)
    (hstart : kind q u ≠ .pebble) (hfinish : kind r.state u = .empty) :
    (∃ b ∈ xs, firstAt b u = .pebble) ∧ (∃ b ∈ ys, firstAt b u = .unpebble) :=
  ⟨compute_before_occurrence xs ys h v u hv hu hstart,
   cleanup_after_occurrence xs ys h v u hne hv hu hfinish⟩
#print axioms parent_bracketed
#print axioms cleanup_after_occurrence
#print axioms scalar_round
#print axioms paperRuns_scalar
#print axioms cleanup_action_exists
end TraceBridge
