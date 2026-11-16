import CutSpace
namespace Area
open SpookyRound TraceBridge
variable {n : Nat} {q : Config n} {r : SpookyDP.Result (Config n)}

def volume (q : Config n) : List Action → Nat
 | [] => 0
 | a::as => roundSpace q a + volume (afterRound q a) as

def boundary (q : Config n) : List Action → Nat
 | [] => 0
 | a::as => CutSpace.pebs q + boundary (afterRound q a) as

theorem before_space (q : Config n) (a : Action) : CutSpace.pebs q ≤ roundSpace q a := by
  rw [roundSpace,CutSpace.filter_sum]
  apply Exceptions.sum_le
  intro v hv
  cases hp : q.peb v <;> cases ht : (afterFirst q a).peb v <;> simp [hp,ht]

theorem boundary_le_volume (as : List Action) (q : Config n) : boundary q as ≤ volume q as := by
  induction as generalizing q with
  | nil => simp [boundary,volume]
  | cons a as ih =>
    have hp := before_space q a
    have ht := ih (afterRound q a)
    simp only [boundary,volume]; omega

theorem volume_cap {pred : Fin n → Fin n → Bool} (h : ActionRuns pred q as r) :
    volume q as ≤ as.length*r.space := by
  induction h with
  | nil q => simp [volume]
  | @cons q a as r hm hg hl ht ih =>
    have hb : r.space ≤ max (roundSpace q a) r.space := Nat.le_max_right _ _
    have hm' := Nat.mul_le_mul_left as.length hb
    have ha : roundSpace q a ≤ max (roundSpace q a) r.space := Nat.le_max_left _ _
    simp only [volume,List.length_cons,SpookyDP.prepend,edge,Nat.add_mul,Nat.one_mul]
    omega

theorem paper_area_cap {pred : Fin n → Fin n → Bool}
    (h : PaperRuns pred d q r) (hs : r.space ≤ s) :
    ∃ as, as.length=d ∧ ActionRuns pred q as r ∧
      boundary q as ≤ volume q as ∧ volume q as ≤ d*s := by
  obtain ⟨as,hd,ha⟩ := extract_actions h
  have hh := volume_cap ha
  have hm := Nat.mul_le_mul_left d hs
  rw [hd] at hh
  exact ⟨as,hd,ha,boundary_le_volume as q,Nat.le_trans hh hm⟩

-- No recomputation remains before a required cleanup: the current vertex
-- MUST be pebbled, so a ghost cannot secretly bridge its live interval.
theorem occupied_until_cleanup {pred : Fin n → Fin n → Bool}
    (h : ActionRuns pred q as r) (v : Fin n)
    (hu : ∃ a ∈ as, firstAt a v = .unpebble)
    (hc : ∀ a ∈ as, firstAt a v ≠ .pebble) : q.peb v = true := by
  by_cases hp : q.peb v = true
  · exact hp
  · have hn : kind q v ≠ .pebble := by cases hg : q.ghost v <;> simp [kind,hp,hg]
    have hh := CutBound.missing_requires_recompute (actionruns_scalar h v)
      ((uncompute_in_events v as).mpr hu) hn
    unfold CutBound.count at hh
    obtain ⟨e,he⟩ := List.exists_mem_of_length_pos (by omega : 0 < ((events v as).filter fun e => e == .compute).length)
    have hf := List.mem_filter.mp he
    have heq : e = .compute := by simpa using hf.2
    subst e
    obtain ⟨a,ha,hm⟩ := (compute_in_events v as).mp hf.1
    exact False.elim (hc a ha hm)
def live (v : Fin n) (q : Config n) : List Action → Nat
 | [] => 0
 | a::as => (if q.peb v then 1 else 0) + live v (afterRound q a) as

theorem live_prefix {pred : Fin n → Fin n → Bool} (xs ys : List Action)
    (h : ActionRuns pred q (xs ++ a :: ys) r) (v : Fin n)
    (hu : firstAt a v = .unpebble)
    (hc : ∀ b ∈ xs ++ a :: ys, firstAt b v ≠ .pebble) :
    live v q xs = xs.length := by
  induction xs generalizing q r with
  | nil => rfl
  | cons b xs ih =>
    have hp := occupied_until_cleanup h v ⟨a,by simp,hu⟩ hc
    cases h with
    | cons hm hg hl ht =>
      have hh := ih ht (fun c hm => hc c (by simp_all))
      simp only [live,hp,ite_true,List.length_cons]
      omega

-- Boundary area is exactly the sum of actual per-vertex occupied boundaries.
theorem boundary_by_vertex (as : List Action) (q : Config n) :
    boundary q as = ((List.finRange n).map fun v => live v q as).sum := by
  induction as generalizing q with
  | nil =>
    simp only [boundary,live]
    induction (List.finRange n) with
    | nil => rfl
    | cons x xs ih => simpa using ih
  | cons a as ih =>
    simp only [boundary,live]
    rw [HeapPath.sum_add,← ih]
    rfl
#print axioms live_prefix
#print axioms boundary_by_vertex
#print axioms paper_area_cap
#print axioms occupied_until_cleanup
end Area
