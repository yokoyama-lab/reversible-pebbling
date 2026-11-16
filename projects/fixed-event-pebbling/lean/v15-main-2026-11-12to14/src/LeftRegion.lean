import ActualCheckpoint
import CompletedEvents
namespace LeftRegion
open LocalCertificate ChainTrace ReachPrefix CompletedEvents
abbrev P := ChainTwoLifetimeExact.isPlacement
abbrev R := ChainUniqueLifetime.isRemoval

/-- The entire left region is finished once its one-placement vertices
and the predecessors of its repeated vertices have disappeared. -/
theorem left_region_completed
    (erasures before cut final : List Nat) (pre post : List Event) (t : Event) (s : Nat)
    (htp : t.place = true) (htv : t.vertex = s+6)
    (hp : run erasures [] pre = some before)
    (hs : step true erasures before t = some cut)
    (hr : run erasures [] (pre ++ t :: post) = some final)
    (hboard : ∀ v, v ∈ cut ↔ v ∈ [s,s+2,s+4,s+5,s+6])
    (hleft : ∀ v, 0 < v → v < s →
      (pre ++ t :: post).countP (P v) ≤ 1 ∨
      (1 < v ∧ (pre ++ t :: post).countP (P (v-1)) ≤ 1 ∧ v ∉ erasures)) :
    ∀ v, 0 < v → v < s → ∀ e ∈ post, e.vertex ≠ v := by
  have hc : run erasures [] (pre ++ [t]) = some cut := by
    rw [run_append]; simp [hp,run,hs]
  have hall : run erasures [] ((pre ++ [t]) ++ post) = some final := by
    simpa [List.append_assoc] using hr
  have habsent : ∀ v, v < s → v ∉ cut := by
    intro v hv
    rw [hboard]
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    omega
  intro v hv hvs
  rcases hleft v hv hvs with hsingle | ⟨hgt,hpred,hne⟩
  · have seen := after_placement_all_predecessors_seen erasures before cut pre t v hv (by omega) hp hs
    apply absent_single_vertex_completed erasures [] cut final (pre ++ [t]) post v seen
    · simpa [List.append_assoc] using hsingle
    · exact habsent v hvs
    · exact hc
    · exact hall
  · have seen := after_placement_all_predecessors_seen erasures before cut pre t (v-1) (by omega) (by omega) hp hs
    have hid : v-1+1 = v := by omega
    have hchild := absent_single_predecessor_completes_successor erasures [] cut final
      (pre ++ [t]) post (v-1) (by omega) (by simpa [hid] using hne) seen
      (by simpa [List.append_assoc] using hpred) (habsent (v-1) (by omega)) hc hall
    simpa [hid] using hchild

/-- Finishing a vertex means the prefix has all its P/R occurrences. -/
theorem completed_vertex_prefix_counts (pre post : List Event) (v : Nat)
    (hn : ∀ e ∈ post, e.vertex ≠ v) :
    pre.countP (P v) = (pre ++ post).countP (P v) ∧
    pre.countP (R v) = (pre ++ post).countP (R v) := by
  have zp : post.countP (P v) = 0 := by
    apply List.countP_eq_zero.mpr
    intro e he
    simp [P,ChainTwoLifetimeExact.isPlacement,hn e he]
  have zr : post.countP (R v) = 0 := by
    apply List.countP_eq_zero.mpr
    intro e he
    simp [R,ChainUniqueLifetime.isRemoval,hn e he]
  simp [List.countP_append,zp,zr]
#print axioms left_region_completed
#print axioms completed_vertex_prefix_counts
end LeftRegion
