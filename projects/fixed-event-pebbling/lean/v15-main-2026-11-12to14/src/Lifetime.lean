import ChainTrace
namespace ChainLifetime
open LocalCertificate ChainTrace

theorem step_membership_unchanged (erasures board after : List Nat) (e : Event) (v : Nat)
    (hne : e.vertex ≠ v) (hs : step true erasures board e = some after) :
    (v ∈ after ↔ v ∈ board) := by
  cases hp : e.place with
  | false =>
    rw [removal_step_after erasures board after e hp hs]
    exact List.mem_erase_of_ne (Ne.symm hne)
  | true =>
    rw [((placement_step erasures board after e hp).mp hs).2.2.2]
    simp [Ne.symm hne]

theorem run_membership_unchanged (erasures board after : List Nat) (es : List Event) (v : Nat)
    (untouched : ∀ e ∈ es, e.vertex ≠ v)
    (hr : run erasures board es = some after) : (v ∈ after ↔ v ∈ board) := by
  induction es generalizing board with
  | nil => simp [run] at hr; subst after; rfl
  | cons e es ih =>
    cases hs : step true erasures board e with
    | none => simp [run,hs] at hr
    | some mid =>
      have tail : run erasures mid es = some after := by simpa [run,hs] using hr
      have hn : ∀ f ∈ es, f.vertex ≠ v := fun f hf => untouched f (List.mem_cons_of_mem e hf)
      exact (ih mid hn tail).trans
        (step_membership_unchanged erasures board mid e v (untouched e (by simp)) hs)

theorem placement_present (erasures board after : List Nat) (e : Event)
    (hp : e.place = true) (hs : step true erasures board e = some after) : e.vertex ∈ after := by
  rw [((placement_step erasures board after e hp).mp hs).2.2.2]
  simp

theorem removal_absent (erasures board after : List Nat) (e : Event)
    (hn : board.Nodup) (hp : e.place = false) (hs : step true erasures board e = some after) :
    e.vertex ∉ after := by
  rw [removal_step_after erasures board after e hp hs]
  exact hn.not_mem_erase

theorem run_nodup (erasures board after : List Nat) (es : List Event)
    (hn : board.Nodup) (hr : run erasures board es = some after) : after.Nodup := by
  induction es generalizing board with
  | nil => simp [run] at hr; subst after; exact hn
  | cons e es ih =>
    cases hs : step true erasures board e with
    | none => simp [run,hs] at hr
    | some mid =>
      exact ih mid (step_nodup erasures board mid e hn hs) (by simpa [run,hs] using hr)

theorem step_contains (erasures board after : List Nat) (e : Event) (v : Nat)
    (hn : board.Nodup) (hs : step true erasures board e = some after) :
    after.contains v = if e.vertex = v then e.place else board.contains v := by
  by_cases hv : e.vertex = v
  · subst v
    cases hp : e.place with
    | false =>
      have ha := removal_absent erasures board after e hn hp hs
      simp [ha]
    | true =>
      have ha := placement_present erasures board after e hp hs
      simp [ha]
  · rw [if_neg hv]
    apply Bool.eq_iff_iff.mpr
    simpa using step_membership_unchanged erasures board after e v hv hs

/-- Vertex-local projection of a successful physical trace, including its initial flag. -/
def presence (v : Nat) : Bool → List Event → Bool
  | flag, [] => flag
  | flag, e :: es => presence v (if e.vertex = v then e.place else flag) es

theorem run_presence (erasures board after : List Nat) (es : List Event) (v : Nat)
    (hn : board.Nodup) (hr : run erasures board es = some after) :
    after.contains v = presence v (board.contains v) es := by
  induction es generalizing board with
  | nil => simp [run] at hr; subst after; rfl
  | cons e es ih =>
    cases hs : step true erasures board e with
    | none => simp [run,hs] at hr
    | some mid =>
      have h := ih mid (step_nodup erasures board mid e hn hs) (by simpa [run,hs] using hr)
      rw [h, step_contains erasures board mid e v hn hs]
      rfl

theorem placement_survives_untouched_interval (erasures before placed after : List Nat)
    (e : Event) (interval : List Event)
    (hp : e.place = true) (hs : step true erasures before e = some placed)
    (untouched : ∀ f ∈ interval, f.vertex ≠ e.vertex)
    (hr : run erasures placed interval = some after) : e.vertex ∈ after :=
  (run_membership_unchanged erasures placed after interval e.vertex untouched hr).mpr
    (placement_present erasures before placed e hp hs)

#print axioms step_membership_unchanged
#print axioms run_membership_unchanged
#print axioms placement_present
#print axioms removal_absent
#print axioms run_nodup
#print axioms step_contains
#print axioms run_presence
#print axioms placement_survives_untouched_interval


theorem run_preserves_without_removal (erasures board after : List Nat) (es : List Event)
    (v : Nat) (present : v ∈ board)
    (noRemoval : ∀ e ∈ es, e.place = false → e.vertex ≠ v)
    (hr : run erasures board es = some after) : v ∈ after := by
  induction es generalizing board with
  | nil => simp [run] at hr; subst after; exact present
  | cons e es ih =>
    cases hs : step true erasures board e with
    | none => simp [run,hs] at hr
    | some mid =>
      have hm : v ∈ mid := by
        cases hp : e.place with
        | false =>
          exact (step_membership_unchanged erasures board mid e v
            (noRemoval e (by simp) hp) hs).mpr present
        | true =>
          rw [((placement_step erasures board mid e hp).mp hs).2.2.2]
          exact List.mem_cons_of_mem e.vertex present
      exact ih mid hm (fun f hf => noRemoval f (List.mem_cons_of_mem e hf))
        (by simpa [run,hs] using hr)

theorem placement_survives_until_removal (erasures before placed after : List Nat)
    (e : Event) (interval : List Event)
    (hp : e.place = true) (hs : step true erasures before e = some placed)
    (noRemoval : ∀ f ∈ interval, f.place = false → f.vertex ≠ e.vertex)
    (hr : run erasures placed interval = some after) : e.vertex ∈ after :=
  run_preserves_without_removal erasures placed after interval e.vertex
    (placement_present erasures before placed e hp hs) noRemoval hr

theorem disappearance_requires_removal (erasures board after : List Nat) (es : List Event)
    (v : Nat) (present : v ∈ board) (absent : v ∉ after)
    (hr : run erasures board es = some after) :
    ∃ e ∈ es, e.place = false ∧ e.vertex = v := by
  by_cases hex : ∃ e ∈ es, e.place = false ∧ e.vertex = v
  · exact hex
  · have hn : ∀ e ∈ es, e.place = false → e.vertex ≠ v := by
      intro e he hp hv
      exact hex ⟨e,he,hp,hv⟩
    exact False.elim (absent (run_preserves_without_removal erasures board after es v present hn hr))

#print axioms run_preserves_without_removal
#print axioms placement_survives_until_removal
#print axioms disappearance_requires_removal
end ChainLifetime
