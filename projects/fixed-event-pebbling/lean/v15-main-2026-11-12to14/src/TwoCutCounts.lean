import CutPresence
namespace ChainTwoCutCounts
open LocalCertificate ChainTrace ChainTwoLifetimeExact ChainCutPresence

/-- An absent cut between a past placement and future removal divides a
budget of two placements exactly one on each side. -/
theorem absent_cut_splits_two_placements (erasures initial cut final : List Nat)
    (pre post : List Event) (v : Nat)
    (absent : v ∉ cut)
    (past : ∃ e ∈ pre, e.place = true ∧ e.vertex = v)
    (future : ∃ e ∈ post, e.place = false ∧ e.vertex = v)
    (budget : (pre ++ post).countP (isPlacement v) ≤ 2)
    (hp : run erasures initial pre = some cut)
    (hr : run erasures initial (pre ++ post) = some final) :
    pre.countP (isPlacement v) = 1 ∧ post.countP (isPlacement v) = 1 := by
  have hs : run erasures cut post = some final := by
    rw [run_append, hp] at hr
    exact hr
  obtain ⟨e,he,hep,hev⟩ := past
  have lp : 0 < pre.countP (isPlacement v) :=
    List.countP_pos_iff.mpr ⟨e,he,by simp [isPlacement,hep,hev]⟩
  have ls : 0 < post.countP (isPlacement v) := by
    by_cases hz : post.countP (isPlacement v) = 0
    · exact False.elim (absent (future_removal_requires_initial_presence
        erasures cut final post v (zero_placements v post hz) future hs))
    · omega
  rw [List.countP_append] at budget
  omega

#print axioms absent_cut_splits_two_placements
/-- Exactly one placement between absent endpoints implies exactly one removal. -/
theorem closed_single_placement_single_removal (erasures board final : List Nat)
    (es : List Event) (v : Nat) (nd : board.Nodup)
    (ia : v ∉ board) (fa : v ∉ final)
    (count : es.countP (isPlacement v) = 1)
    (hr : run erasures board es = some final) :
    es.countP (ChainUniqueLifetime.isRemoval v) = 1 := by
  obtain ⟨a,p,b,he,hp,za,zb⟩ := ChainTwoProjection.split_first_count (isPlacement v) es 0 count
  have hpp : p.place = true ∧ p.vertex = v := by simpa [isPlacement] using hp
  subst es
  rw [run_append] at hr
  cases ha : run erasures board a with
  | none => simp [ha] at hr
  | some before =>
    simp only [ha, Option.bind_some] at hr
    cases hs : step true erasures before p with
    | none => simp [run,hs] at hr
    | some after =>
      have hb : run erasures after b = some final := by simpa [run,hs] using hr
      have ca := ChainUniqueLifetime.absent_no_placement_no_removal erasures board before a v
        ia (zero_placements v a za) ha
      have nda := ChainLifetime.run_nodup erasures board before a nd ha
      have nds := step_nodup erasures before after p nda hs
      have ub := ChainUniqueLifetime.no_placement_at_most_one_removal erasures after final b v
        nds (zero_placements v b zb) hb
      have present : v ∈ after := hpp.2 ▸ ChainLifetime.placement_present erasures before after p hpp.1 hs
      obtain ⟨e,he,hep,hev⟩ := ChainLifetime.disappearance_requires_removal erasures after final b v present fa hb
      have lb : 0 < b.countP (ChainUniqueLifetime.isRemoval v) :=
        List.countP_pos_iff.mpr ⟨e,he,by simp [ChainUniqueLifetime.isRemoval,hep,hev]⟩
      have cb : b.countP (ChainUniqueLifetime.isRemoval v) = 1 := by omega
      simp [List.countP_append, ChainUniqueLifetime.isRemoval, hpp.1, ca, cb]

#print axioms closed_single_placement_single_removal
end ChainTwoCutCounts
