import ChainTrace
namespace RemovalOrder
open LocalCertificate ChainTrace

/-- After the last removal of v, no operation at its non-erasing successor
can occur. Last means that the suffix contains no further placement of v. -/
theorem last_removal_blocks_successor
    (erasures board final : List Nat) (e : Event) (post : List Event)
    (v : Nat) (hv : 0 < v) (hnodup : board.Nodup)
    (hp : e.place = false) (he : e.vertex = v)
    (her : v+1 ∉ erasures)
    (hnever : ∀ f ∈ post, f.place = true → f.vertex ≠ v)
    (hr : run erasures board (e :: post) = some final) :
    (∀ f ∈ post, f.vertex ≠ v+1) ∧ v ∉ final := by
  cases hs : step true erasures board e with
  | none => simp [run, hs] at hr
  | some mid =>
    have hmid := removal_step_after erasures board mid e hp hs
    have habsent : v ∉ mid := by
      rw [hmid, he]
      simp [hnodup.mem_erase_iff]
    have hpost : run erasures mid post = some final := by simpa [run,hs] using hr
    exact absent_predecessor_blocks_successor erasures mid final post v hv habsent her hnever hpost

/-- In an empty-start successful trace, every successor event must be in
    the prefix preceding its predecessor's final removal. This is an
    order conclusion derived from the operational semantics, not assumed. -/
theorem successor_precedes_last_removal
    (erasures final : List Nat) (pre post : List Event) (e f : Event)
    (v : Nat) (hv : 0 < v) (hp : e.place = false) (he : e.vertex = v)
    (her : v+1 ∉ erasures)
    (hnever : ∀ g ∈ post, g.place = true → g.vertex ≠ v)
    (hr : run erasures [] (pre ++ e :: post) = some final)
    (hf : f ∈ pre ++ e :: post) (hfv : f.vertex = v+1) : f ∈ pre := by
  rw [run_append] at hr
  cases hs : run erasures [] pre with
  | none => simp [hs] at hr
  | some mid =>
    have hrest : run erasures mid (e :: post) = some final := by simpa [hs] using hr
    have hinv := run_invariants erasures [] mid pre (by simp) hs
    have hblock := last_removal_blocks_successor erasures mid final e post v hv hinv.1 hp he her hnever hrest
    rcases List.mem_append.mp hf with hpre | htail
    · exact hpre
    · rcases List.mem_cons.mp htail with hsame | hpost
      · subst f; omega
      · exact False.elim (hblock.1 f hpost hfv)

#print axioms last_removal_blocks_successor
#print axioms successor_precedes_last_removal
end RemovalOrder
