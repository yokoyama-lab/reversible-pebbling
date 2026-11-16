import PhysicalStepCapacity

/- Finite unit, compiled (green 2026-11-15/16). This only separates original capacity checks
   from original successful noncapacity replay; it does not identify Q. -/
set_option maxRecDepth 2048
set_option maxHeartbeats 2000000
namespace LocalCertificate

/-- An increment-WORD predicate: check only post-step upper bounds. -/
def PostUpper (h : Int) : List Int → Prop
  | [] => True
  | d :: ds => h + d ≤ 5 ∧ PostUpper (h + d) ds

/-- Include the empty prefix as a separate requirement. -/
def FullUpper (h : Int) (ds : List Int) : Prop := h ≤ 5 ∧ PostUpper h ds

/-- Nonnegative post-step heights are a separate predicate, not silently
    included in or removed from the capacity upper-bound predicate. -/
def PostNonnegative (h : Int) : List Int → Prop
  | [] => True
  | d :: ds => 0 ≤ h + d ∧ PostNonnegative (h + d) ds

theorem successful_replay_post_nonnegative (events : List Event)
    (erasures board ids after : List Nat)
    (hs : replay false events erasures board ids = some after) :
    PostNonnegative (board.length : Int) (ids.map (eventIdIncrement events)) := by
  induction ids generalizing board with
  | nil => trivial
  | cons i rest ih =>
      obtain ⟨e, mid, he, ht, hr⟩ :=
        successful_replay_cons_decompose false events erasures board after i rest hs
      have hlen := successful_step_length_increment false erasures board mid e ht
      have hw : eventIdIncrement events i = eventIncrement e := by
        simp [eventIdIncrement, he]
      simp only [List.map_cons, PostNonnegative, hw]
      rw [← hlen]
      exact ⟨by omega, ih mid hr⟩

/-- The same actual execution has capacity iff its increment word satisfies
    the post-step upper guard. This does not assume any guard invariance. -/
theorem capacityTrace_iff_postUpper_of_replay_false (events : List Event)
    (erasures board ids after : List Nat)
    (hs : replay false events erasures board ids = some after) :
    CapacityTrace events erasures board ids after ↔
      PostUpper (board.length : Int) (ids.map (eventIdIncrement events)) := by
  induction ids generalizing board with
  | nil =>
      have he : board = after := by simpa [replay] using hs
      subst after
      constructor
      · intro _; trivial
      · intro _; exact CapacityTrace.nil board
  | cons i rest ih =>
      obtain ⟨e, mid, he, ht, hr⟩ :=
        successful_replay_cons_decompose false events erasures board after i rest hs
      have hlen := successful_step_length_increment false erasures board mid e ht
      have hw : eventIdIncrement events i = eventIncrement e := by
        simp [eventIdIncrement, he]
      simp only [List.map_cons, PostUpper, hw]
      rw [← hlen]
      constructor
      · intro hc
        have hsTrue := (replay_true_iff_capacityTrace events erasures board (i :: rest) after).mpr hc
        obtain ⟨e', mid', he', ht', hr'⟩ :=
          successful_replay_cons_decompose true events erasures board after i rest hsTrue
        have ee : e' = e := by simpa [he] using he'.symm
        subst e'
        have hcStep := (step_true_iff_false_and_capacity erasures board mid' e).mp ht'
        have mm : mid' = mid := by simpa [ht] using hcStep.1.symm
        subst mid'
        have hcTail := (replay_true_iff_capacityTrace events erasures mid rest after).mp hr'
        exact ⟨by omega, (ih mid hr).mp hcTail⟩
      · rintro ⟨hb, hg⟩
        exact CapacityTrace.cons he ht (by omega) ((ih mid hr).mpr hg)

/-- Unconditional factorization: original noncapacity success plus word guard. -/
theorem replay_true_iff_false_and_postUpper (events : List Event)
    (erasures board ids after : List Nat) :
    replay true events erasures board ids = some after ↔
      replay false events erasures board ids = some after ∧
      PostUpper (board.length : Int) (ids.map (eventIdIncrement events)) := by
  constructor
  · intro hs
    have hc := (replay_true_iff_capacityTrace events erasures board ids after).mp hs
    have hf := hc.replay_false
    exact ⟨hf, (capacityTrace_iff_postUpper_of_replay_false events erasures board ids after hf).mp hc⟩
  · rintro ⟨hf,hg⟩
    exact (replay_true_iff_capacityTrace events erasures board ids after).mpr
      ((capacityTrace_iff_postUpper_of_replay_false events erasures board ids after hf).mpr hg)

theorem replay_true_iff_false_and_fullUpper (events : List Event)
    (erasures board ids after : List Nat) (hinit : (board.length : Int) ≤ 5) :
    replay true events erasures board ids = some after ↔
      replay false events erasures board ids = some after ∧
      FullUpper (board.length : Int) (ids.map (eventIdIncrement events)) := by
  simpa [FullUpper, hinit] using
    replay_true_iff_false_and_postUpper events erasures board ids after

#print axioms successful_replay_post_nonnegative
#print axioms capacityTrace_iff_postUpper_of_replay_false
#print axioms replay_true_iff_false_and_postUpper
#print axioms replay_true_iff_false_and_fullUpper
end LocalCertificate
