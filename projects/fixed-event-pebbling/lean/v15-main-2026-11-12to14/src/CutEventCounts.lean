import TwoCutCounts
namespace ChainCutEventCounts
open LocalCertificate ChainTrace ChainLifetime ChainUniqueLifetime ChainTwoLifetimeExact ChainTwoCutCounts

theorem absent_cut_exact_prefix_counts (erasures initial cut final : List Nat)
    (pre post : List Event) (v : Nat) (nd : initial.Nodup)
    (ia : v ∉ initial) (ca : v ∉ cut)
    (past : ∃ e ∈ pre, e.place = true ∧ e.vertex = v)
    (future : ∃ e ∈ post, e.place = false ∧ e.vertex = v)
    (budget : (pre ++ post).countP (isPlacement v) ≤ 2)
    (hp : run erasures initial pre = some cut)
    (hr : run erasures initial (pre ++ post) = some final) :
    pre.countP (isPlacement v) = 1 ∧ pre.countP (isRemoval v) = 1 ∧
      post.countP (isPlacement v) = 1 := by
  obtain ⟨cp,cq⟩ := absent_cut_splits_two_placements erasures initial cut final pre post v
    ca past future budget hp hr
  exact ⟨cp, closed_single_placement_single_removal erasures initial cut pre v nd ia ca cp hp, cq⟩

/-- A single placement still present at the end has never been removed. -/
theorem present_single_placement_no_removal (erasures board final : List Nat)
    (es : List Event) (v : Nat) (nd : board.Nodup)
    (ia : v ∉ board) (present : v ∈ final)
    (count : es.countP (isPlacement v) = 1)
    (hr : run erasures board es = some final) : es.countP (isRemoval v) = 0 := by
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
      have ca := absent_no_placement_no_removal erasures board before a v ia (zero_placements v a za) ha
      have nda := run_nodup erasures board before a nd ha
      have nds := step_nodup erasures before after p nda hs
      have cb : b.countP (isRemoval v) = 0 := by
        by_cases hz : b.countP (isRemoval v) = 0
        · exact hz
        · have pos : 0 < b.countP (isRemoval v) := by omega
          obtain ⟨x,r,y,he,hrm,_,_⟩ := ChainTwoProjection.split_first_count (isRemoval v) b
            (b.countP (isRemoval v)-1) (by omega)
          have rr : r.place = false ∧ r.vertex = v := by simpa [isRemoval] using hrm
          rw [he, run_append] at hb
          cases hx : run erasures after x with
          | none => simp [hx] at hb
          | some bef =>
            simp only [hx,Option.bind_some] at hb
            cases hh : step true erasures bef r with
            | none => simp [run,hh] at hb
            | some aft =>
              have hy : run erasures aft y = some final := by simpa [run,hh] using hb
              have absent : v ∉ aft := rr.2 ▸ removal_absent erasures bef aft r
                (run_nodup erasures after bef x nds hx) rr.1 hh
              have np := zero_placements v b zb
              have support := run_support erasures aft final y hy v present
              rcases support with hm | ⟨e,hem,hep,hev⟩
              · exact False.elim (absent hm)
              · exact False.elim (np e (by rw [he]; simp [hem]) hep hev)
      simp [List.countP_append,isRemoval,hpp.1,ca,cb]

/-- A live cut vertex with global placement budget one has prefix counts P=1,R=0. -/
theorem live_cut_exact_prefix_counts (erasures initial cut : List Nat)
    (pre post : List Event) (v : Nat) (nd : initial.Nodup)
    (ia : v ∉ initial) (present : v ∈ cut)
    (budget : (pre ++ post).countP (isPlacement v) ≤ 1)
    (hp : run erasures initial pre = some cut) :
    pre.countP (isPlacement v) = 1 ∧ pre.countP (isRemoval v) = 0 := by
  obtain ⟨e,he,hep,hev⟩ := (run_support erasures initial cut pre hp v present).resolve_left ia
  have pos : 0 < pre.countP (isPlacement v) :=
    List.countP_pos_iff.mpr ⟨e,he,by simp [isPlacement,hep,hev]⟩
  have cp : pre.countP (isPlacement v) = 1 := by
    rw [List.countP_append] at budget
    omega
  exact ⟨cp,present_single_placement_no_removal erasures initial cut pre v nd ia present cp hp⟩

#print axioms absent_cut_exact_prefix_counts
#print axioms present_single_placement_no_removal
#print axioms live_cut_exact_prefix_counts
end ChainCutEventCounts
