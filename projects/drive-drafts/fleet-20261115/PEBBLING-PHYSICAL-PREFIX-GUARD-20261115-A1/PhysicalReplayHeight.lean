import PhysicalStepHeight

/- SOURCE CANDIDATE, uncompiled. This imports and uses the original
   LocalCertificate.replay and the validated original-step height lemma. -/
set_option maxRecDepth 2048
set_option maxHeartbeats 2000000
namespace LocalCertificate

/-- Total weight on event IDs. The missing-event value is arbitrary here;
    successful replay is separately shown never to take that branch. -/
 def eventIdIncrement (events : List Event) (i : Nat) : Int :=
  match events[i]? with
  | none => 0
  | some e => eventIncrement e

 theorem successful_replay_cons_decompose (capacity : Bool) (events : List Event)
    (erasures board after : List Nat) (i : Nat) (rest : List Nat)
    (hs : replay capacity events erasures board (i :: rest) = some after) :
    ∃ e mid, events[i]? = some e ∧ step capacity erasures board e = some mid ∧
      replay capacity events erasures mid rest = some after := by
  cases he : events[i]? with
  | none => simp [replay, he] at hs
  | some e =>
      cases ht : step capacity erasures board e with
      | none => simp [replay, he, ht] at hs
      | some mid =>
          exact ⟨e, mid, rfl, ht, by simpa [replay, he, ht] using hs⟩

/-- Every executed ID actually resolves to a concrete original event. -/
 theorem successful_replay_ids_exist (capacity : Bool) (events : List Event)
    (erasures board after ids : List Nat)
    (hs : replay capacity events erasures board ids = some after) :
    ∀ i ∈ ids, ∃ e, events[i]? = some e := by
  induction ids generalizing board with
  | nil => simp
  | cons j rest ih =>
      obtain ⟨e, mid, he, ht, hr⟩ :=
        successful_replay_cons_decompose capacity events erasures board after j rest hs
      intro i hi
      rcases List.mem_cons.mp hi with hij | hi
      · subst i
        exact ⟨e, he⟩
      · exact ih (board := mid) hr i hi

/-- Physical height telescopes along arbitrary successful original replay.
    No Perm, unique-event, Nodup, fixed capacity, or final-board assumption. -/
 theorem successful_replay_length_sum (capacity : Bool) (events : List Event)
    (erasures board after ids : List Nat)
    (hs : replay capacity events erasures board ids = some after) :
    (after.length : Int) = (board.length : Int) +
      (ids.map (eventIdIncrement events)).sum := by
  induction ids generalizing board with
  | nil =>
      have he : board = after := by simpa [replay] using hs
      simp [← he]
  | cons i rest ih =>
      obtain ⟨e, mid, he, ht, hr⟩ :=
        successful_replay_cons_decompose capacity events erasures board after i rest hs
      have htail := ih (board := mid) hr
      have hstep := successful_step_length_increment capacity erasures board mid e ht
      have hw : eventIdIncrement events i = eventIncrement e := by
        simp [eventIdIncrement, he]
      simp only [List.map_cons, List.sum_cons, hw]
      omega

 theorem I_successful_replay_height (after ids : List Nat)
    (hs : replay true I.events I.erasures I.initial ids = some after) :
    (after.length : Int) = 4 + (ids.map (eventIdIncrement I.events)).sum := by
  have h := successful_replay_length_sum true I.events I.erasures I.initial after ids hs
  simpa only [I_initial_height] using h

 theorem M_successful_replay_height (after ids : List Nat)
    (hs : replay true M.events M.erasures M.initial ids = some after) :
    (after.length : Int) = 4 + (ids.map (eventIdIncrement M.events)).sum := by
  have h := successful_replay_length_sum true M.events M.erasures M.initial after ids hs
  simpa only [M_initial_height] using h

#print axioms successful_replay_cons_decompose
#print axioms successful_replay_ids_exist
#print axioms successful_replay_length_sum
#print axioms I_successful_replay_height
#print axioms M_successful_replay_height
end LocalCertificate
