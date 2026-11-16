import FourBarrier
namespace EpochCharge
open CutBound TraceBridge SpookyRound

theorem balance (h : Trace s es t) :
 count .compute es + occupied s = count .ghost es + count .uncompute es + occupied t := by
 induction h with
 | nil s => simp [count]
 | cons hs ht ih => cases hs <;> simp_all [count,occupied] <;> omega

theorem pebble_to_pebble (h : Trace .pebble es .pebble) :
 count .compute es = count .ghost es + count .uncompute es := by
 have hh := balance h
 simp only [occupied] at hh
 omega

theorem closed_epochs (h : Trace s es .empty) (hs : s≠.pebble) :
 count .compute es = count .ghost es + count .uncompute es := by
 have hh := balance h
 cases s <;> simp_all [occupied]

theorem ghost_requires_extra_compute (h : Trace .pebble es .pebble)
 (hg : .ghost ∈ es) : 1≤count .compute es := by
 have hh := pebble_to_pebble h
 have hc := Exceptions.count_positive .ghost es hg
 omega

variable {n : Nat} {pred : Fin n → Fin n → Bool} {q : Config n}
 {r : SpookyDP.Result (Config n)} {a b : Action}

theorem referenced_child_pebbled (hl : Legal pred q a) (v u : Fin n)
 (hv : firstAt a v≠.idle) (hu : pred v u=true) : kind q u=.pebble := by
 have hh := hl.2.2.2.1 v hv u hu
 simp [kind,hh]

-- The segment starts before the first parent reference and ends before the second.
-- Both may occur in a larger run; the actual segment is not replaced by a synthetic trace.
theorem between_references (h : ActionRuns pred q as r)
 (hfirst : Legal pred q a) (hlast : Legal pred r.state b)
 (v w u : Fin n) (hv : firstAt a v≠.idle) (hw : firstAt b w≠.idle)
 (hvu : pred v u=true) (hwu : pred w u=true) :
 count .compute (events u as)=count .ghost (events u as)+count .uncompute (events u as) := by
 have ht := actionruns_scalar h u
 rw [referenced_child_pebbled hfirst v u hv hvu,
     referenced_child_pebbled hlast w u hw hwu] at ht
 exact pebble_to_pebble ht

-- Exact charge sums safely over disjoint consecutive segments, not over overlapping references.
theorem count_append (e : Event) (xs ys : List Event) :
 count e (xs++ys)=count e xs+count e ys := by simp [count,List.filter_append]

theorem charge_segments (segments : List (List Event))
 (h : ∀es ∈ segments, Trace .pebble es .pebble) :
 (segments.map (count .ghost)).sum + (segments.map (count .uncompute)).sum =
 (segments.map (count .compute)).sum := by
 induction segments with
 | nil => simp
 | cons es rest ih =>
   have hh := pebble_to_pebble (h es (by simp))
   have hr := ih (fun xs hx => h xs (by simp [hx]))
   simp only [List.map_cons,List.sum_cons]
   omega
#print axioms balance
#print axioms between_references
#print axioms charge_segments

-- A cut-level arithmetic consequence. The aggregate hypotheses still need their own bridge.
theorem postghost_budget (n preC postC postU ghosts p e : Nat)
 (hpre : n≤preC) (hun : n≤postU+1)
 (hbalance : postC+p=ghosts+postU+1)
 (hwork : preC+postC+postU≤3*n+e) : ghosts≤e+p+1 := by omega

theorem overlap_warning :
 Trace .pebble [.ghost,.compute] .pebble ∧
 2*count .ghost [.ghost,.compute]>count .compute [.ghost,.compute] := by
 constructor
 · exact Trace.cons Step.ghost (Trace.cons Step.computeGhost (Trace.nil _))
 · decide
#print axioms postghost_budget
#print axioms overlap_warning
end EpochCharge
