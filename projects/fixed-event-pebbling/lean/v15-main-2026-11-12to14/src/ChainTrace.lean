import LocalCertificate
namespace ChainTrace
open LocalCertificate

theorem placement_step (erasures board after : List Nat) (e : Event)
    (hp : e.place = true) :
    step true erasures board e = some after ↔
      e.vertex ∉ board ∧ (e.vertex = 1 ∨ e.vertex - 1 ∈ board) ∧
      (e.vertex :: board).length ≤ 5 ∧ after = e.vertex :: board := by
  simp only [step, hp]
  simp [Bool.and_eq_true, Bool.or_eq_true]
  constructor
  · rintro ⟨⟨ha,hb⟩,hc,hd⟩
    exact ⟨ha,hb,hc,hd.symm⟩
  · rintro ⟨ha,hb,hc,hd⟩
    exact ⟨⟨ha,hb⟩,hc,hd.symm⟩

theorem removal_step_after (erasures board after : List Nat) (e : Event)
    (hp : e.place = false) (h : step true erasures board e = some after) :
    after = board.erase e.vertex := by
  simp [step, hp] at h
  exact h.2.2.symm

theorem step_support (erasures board after : List Nat) (e : Event)
    (h : step true erasures board e = some after) (v : Nat) (hv : v ∈ after) :
    v ∈ board ∨ (e.place = true ∧ e.vertex = v) := by
  cases hp : e.place with
  | false =>
    have he := removal_step_after erasures board after e hp h
    rw [he] at hv
    exact Or.inl (List.mem_of_mem_erase hv)
  | true =>
    have he := (placement_step erasures board after e hp).mp h
    rw [he.2.2.2] at hv
    rcases List.mem_cons.mp hv with hv | hv
    · exact Or.inr ⟨rfl, hv.symm⟩
    · exact Or.inl hv

def run (erasures : List Nat) : List Nat → List Event → Option (List Nat)
  | board, [] => some board
  | board, e :: es => (step true erasures board e).bind (fun after => run erasures after es)

theorem run_support (erasures board after : List Nat) (es : List Event)
    (h : run erasures board es = some after) (v : Nat) (hv : v ∈ after) :
    v ∈ board ∨ ∃ e ∈ es, e.place = true ∧ e.vertex = v := by
  induction es generalizing board with
  | nil =>
    simp [run] at h
    exact Or.inl (h ▸ hv)
  | cons e es ih =>
    cases hs : step true erasures board e with
    | none => simp [run, hs] at h
    | some mid =>
      have hr : run erasures mid es = some after := by simpa [run, hs] using h
      rcases ih mid hr with hm | ⟨f,hf,hp,hfval⟩
      · rcases step_support erasures board mid e hs v hm with hb | he
        · exact Or.inl hb
        · exact Or.inr ⟨e, by simp, he⟩
      · exact Or.inr ⟨f, List.mem_cons_of_mem e hf, hp,hfval⟩

theorem removal_requires_present (erasures board after : List Nat) (e : Event)
    (hp : e.place = false) (h : step true erasures board e = some after) :
    e.vertex ∈ board := by
  simp [step, hp] at h
  exact h.1.1

theorem run_append (erasures board : List Nat) (xs ys : List Event) :
    run erasures board (xs ++ ys) =
    (run erasures board xs).bind (fun mid => run erasures mid ys) := by
  induction xs generalizing board with
  | nil => rfl
  | cons e es ih =>
    cases h : step true erasures board e with
    | none => simp [run,h]
    | some mid => simp [run,h,ih]

theorem earlier_predecessor (erasures final : List Nat) (pre post : List Event) (e : Event)
    (h : run erasures [] (pre ++ e :: post) = some final)
    (hp : e.place = true) (hne : e.vertex ≠ 1) :
    ∃ f ∈ pre, f.place = true ∧ f.vertex = e.vertex - 1 := by
  rw [run_append] at h
  cases hpre : run erasures [] pre with
  | none => simp [hpre] at h
  | some mid =>
    have hrest : run erasures mid (e :: post) = some final := by simpa [hpre] using h
    cases he : step true erasures mid e with
    | none => simp [run, he] at hrest
    | some after =>
      have hd := (placement_step erasures mid after e hp).mp he
      have hm : e.vertex - 1 ∈ mid := hd.2.1.resolve_left hne
      have hx := run_support erasures [] mid pre hpre (e.vertex-1) hm
      simpa using hx

/-- Before the first placement of cutoff t, no event at or above t can occur.
    The arbitrary initial board must already lie strictly below t. -/
theorem before_first_placement
    (erasures board after : List Nat) (es : List Event) (t : Nat)
    (ht : 0 < t) (hb : ∀ v ∈ board, v < t)
    (hn : ∀ e ∈ es, e.place = true → e.vertex ≠ t)
    (hr : run erasures board es = some after) :
    (∀ e ∈ es, e.vertex < t) ∧ (∀ v ∈ after, v < t) := by
  induction es generalizing board with
  | nil =>
    simp [run] at hr
    subst after
    exact ⟨by simp, hb⟩
  | cons e es ih =>
    cases hs : step true erasures board e with
    | none => simp [run,hs] at hr
    | some mid =>
      have hr' : run erasures mid es = some after := by simpa [run,hs] using hr
      have he : e.vertex < t := by
        cases hp : e.place with
        | false => exact hb e.vertex (removal_requires_present erasures board mid e hp hs)
        | true =>
          have hd := (placement_step erasures board mid e hp).mp hs
          have hne := hn e (by simp) hp
          rcases hd.2.1 with h1 | hm
          · omega
          · have hh := hb (e.vertex-1) hm
            omega
      have hm : ∀ v ∈ mid, v < t := by
        intro v hv
        rcases step_support erasures board mid e hs v hv with hv | hv
        · exact hb v hv
        · rw [← hv.2]; exact he
      have hn' : ∀ f ∈ es, f.place = true → f.vertex ≠ t := by
        intro f hf; exact hn f (List.mem_cons_of_mem e hf)
      obtain ⟨hrest, haf⟩ := ih mid hm hn' hr'
      refine ⟨?_, haf⟩
      intro f hf
      rcases List.mem_cons.mp hf with hf | hf
      · subst f; exact he
      · exact hrest f hf

theorem nonerasure_requires_predecessor (erasures board after : List Nat) (e : Event)
    (hne : e.vertex ∉ erasures) (h : step true erasures board e = some after) :
    e.vertex = 1 ∨ e.vertex - 1 ∈ board := by
  cases hp : e.place with
  | true => exact ((placement_step erasures board after e hp).mp h).2.1
  | false =>
    simp [step, hp, hne] at h
    exact h.1.2

/-- If a predecessor is absent and never placed again, none of its
    non-erasing successor's operations can appear in a successful suffix. -/
theorem absent_predecessor_blocks_successor
    (erasures board after : List Nat) (es : List Event) (v : Nat)
    (hv : 0 < v) (hb : v ∉ board) (he : v+1 ∉ erasures)
    (hn : ∀ e ∈ es, e.place = true → e.vertex ≠ v)
    (hr : run erasures board es = some after) :
    (∀ e ∈ es, e.vertex ≠ v+1) ∧ v ∉ after := by
  induction es generalizing board with
  | nil =>
    simp [run] at hr
    subst after
    exact ⟨by simp, hb⟩
  | cons e es ih =>
    cases hs : step true erasures board e with
    | none => simp [run,hs] at hr
    | some mid =>
      have hr' : run erasures mid es = some after := by simpa [run,hs] using hr
      have hchild : e.vertex ≠ v+1 := by
        intro hc
        have he' : e.vertex ∉ erasures := by simpa [hc] using he
        have pred := nonerasure_requires_predecessor erasures board mid e he' hs
        rcases pred with h1 | hmem
        · omega
        · have : v ∈ board := by simpa [hc] using hmem
          exact hb this
      have hm : v ∉ mid := by
        intro hmem
        rcases step_support erasures board mid e hs v hmem with hmem | hnew
        · exact hb hmem
        · exact hn e (by simp) hnew.1 hnew.2
      have hn' : ∀ f ∈ es, f.place = true → f.vertex ≠ v := by
        intro f hf; exact hn f (List.mem_cons_of_mem e hf)
      obtain ⟨hrest,hfinal⟩ := ih mid hm hn' hr'
      refine ⟨?_,hfinal⟩
      intro f hf
      rcases List.mem_cons.mp hf with hf | hf
      · subst f; exact hchild
      · exact hrest f hf

def decodeTrace (events : List Event) : List Nat → Option (List Event)
  | [] => some []
  | i :: rest => do
    let e ← events[i]?
    let tail ← decodeTrace events rest
    pure (e :: tail)

theorem replay_eq_decode_run (events : List Event) (erasures board ids : List Nat) :
    replay true events erasures board ids =
    (decodeTrace events ids).bind (fun es => run erasures board es) := by
  induction ids generalizing board with
  | nil => rfl
  | cons i ids ih =>
    cases he : events[i]? with
    | none => simp [replay, decodeTrace, he]
    | some e =>
      cases hd : decodeTrace events ids with
      | none =>
        cases hs : step true erasures board e with
        | none => simp [replay, decodeTrace, he,hd,hs]
        | some mid => simp [replay, decodeTrace, he,hd, ih]
      | some tail =>
        cases hs : step true erasures board e with
        | none => simp [replay, decodeTrace, he,hd,hs,run]
        | some mid => simp [replay, decodeTrace, he,hd,hs,run,ih]

theorem step_capacity (erasures board after : List Nat) (e : Event)
    (h : step true erasures board e = some after) : after.length ≤ 5 := by
  cases hp : e.place with
  | true =>
    have he := (placement_step erasures board after e hp).mp h
    rw [he.2.2.2]
    exact he.2.2.1
  | false =>
    simp [step,hp] at h
    rw [← h.2.2]
    omega

theorem step_nodup (erasures board after : List Nat) (e : Event)
    (hb : board.Nodup) (h : step true erasures board e = some after) : after.Nodup := by
  cases hp : e.place with
  | true =>
    have he := (placement_step erasures board after e hp).mp h
    rw [he.2.2.2]
    exact List.nodup_cons.mpr ⟨he.1,hb⟩
  | false =>
    rw [removal_step_after erasures board after e hp h]
    exact hb.erase e.vertex

theorem run_invariants (erasures board after : List Nat) (es : List Event)
    (hb : board.Nodup ∧ board.length ≤ 5)
    (h : run erasures board es = some after) : after.Nodup ∧ after.length ≤ 5 := by
  induction es generalizing board with
  | nil =>
    simp [run] at h
    subst after
    exact hb
  | cons e es ih =>
    cases hs : step true erasures board e with
    | none => simp [run,hs] at h
    | some mid =>
      have hr : run erasures mid es = some after := by simpa [run,hs] using h
      exact ih mid ⟨step_nodup erasures board mid e hb.1 hs,
        step_capacity erasures board mid e hs⟩ hr

#print axioms ChainTrace.step_capacity
#print axioms ChainTrace.step_nodup
#print axioms ChainTrace.run_invariants
#print axioms ChainTrace.replay_eq_decode_run
#print axioms ChainTrace.nonerasure_requires_predecessor
#print axioms ChainTrace.absent_predecessor_blocks_successor
#print axioms ChainTrace.earlier_predecessor
#print axioms ChainTrace.before_first_placement
#print axioms ChainTrace.run_append
#print axioms ChainTrace.placement_step
#print axioms ChainTrace.removal_step_after
#print axioms ChainTrace.step_support
#print axioms ChainTrace.run_support
end ChainTrace
