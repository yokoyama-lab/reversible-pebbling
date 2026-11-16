import PhysicalReplayHeight

/- Separate optional finite unit: physical set interpretation is preserved,
   rather than treating arbitrary list length as set cardinality. Uncompiled. -/
set_option maxRecDepth 2048
set_option maxHeartbeats 2000000
namespace LocalCertificate

 theorem successful_step_nodup (capacity : Bool) (erasures board after : List Nat)
    (e : Event) (hd : board.Nodup)
    (hs : step capacity erasures board e = some after) : after.Nodup := by
  cases hp : e.place with
  | false =>
      obtain ⟨he, hc⟩ := successful_remove_shape capacity erasures board after e hp hs
      rw [he]
      exact List.Nodup.erase e.vertex hd
  | true =>
      obtain ⟨he, hc⟩ := successful_place_shape capacity erasures board after e hp hs
      have hn : e.vertex ∉ board := by simpa using hc
      rw [he]
      exact List.nodup_cons.mpr ⟨hn, hd⟩

 theorem successful_replay_nodup (capacity : Bool) (events : List Event)
    (erasures board after ids : List Nat) (hd : board.Nodup)
    (hs : replay capacity events erasures board ids = some after) : after.Nodup := by
  induction ids generalizing board with
  | nil =>
      have he : board = after := by simpa [replay] using hs
      simpa [← he] using hd
  | cons i rest ih =>
      obtain ⟨e, mid, he, ht, hr⟩ :=
        successful_replay_cons_decompose capacity events erasures board after i rest hs
      have hmid := successful_step_nodup capacity erasures board mid e hd ht
      exact ih (board := mid) hmid hr

#print axioms successful_step_nodup
#print axioms successful_replay_nodup
end LocalCertificate
