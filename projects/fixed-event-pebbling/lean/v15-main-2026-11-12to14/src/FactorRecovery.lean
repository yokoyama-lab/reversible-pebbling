import InitialConverse
import MiddleConverse
namespace ChainFactorRecovery
open LocalCertificate

theorem split_three (w : List Nat) (d m : Nat) :
    w = w.take d ++ ((w.drop d).take m ++ w.drop (d+m)) := by
  calc
    w = w.take d ++ w.drop d := (List.take_append_drop d w).symm
    _ = w.take d ++ ((w.drop d).take m ++ w.drop (d+m)) := by
      congr 1
      simpa [List.drop_drop, Nat.add_comm] using (List.take_append_drop m (w.drop d)).symm

theorem recover (w : List Nat) (d m last : Nat) (nd : w.Nodup)
    (hp : w.take d = List.range d) (hs : w.drop (d+m) = [last]) :
    w = List.range d ++ (((w.drop d).take m).map (fun i => i-d)).map (fun i => i+d) ++ [last] := by
  have he := split_three w d m
  rw [hp,hs] at he
  have hn : (List.range d ++ ((w.drop d).take m ++ [last])).Nodup := he ▸ nd
  have dis := (List.nodup_append.mp hn).2.2
  have hm : (((w.drop d).take m).map (fun i => i-d)).map (fun i => i+d) = (w.drop d).take m := by
    rw [List.map_map]
    apply Eq.trans (b := ((w.drop d).take m).map (fun i => i))
    · apply List.map_congr_left
      intro i hi
      have lo : d ≤ i := by
        by_cases hh : i < d
        · exact False.elim (dis i (List.mem_range.mpr hh) i (by simp [hi]) rfl)
        · omega
      simp only [Function.comp_apply]
      omega
    · exact List.map_id' _
  rw [hm]
  simpa [List.append_assoc] using he

theorem initial_recovery (w : List Nat) (perm : isPermutation 17 w)
    (good : ChainInitialSegment.Good w) :
    w = ChainInitialConverse.liftWord (ChainInitialSegment.middle w) := by
  exact recover w 6 10 16 perm.2.1 good.1 good.2.1

theorem middle_recovery (w : List Nat) (perm : isPermutation 16 w)
    (good : ChainMiddleSegment.Good w) :
    w = ChainMiddleConverse.liftWord (ChainMiddleSegment.middle w) := by
  exact recover w 3 12 15 perm.2.1 good.1 good.2.1

theorem initial_legal_iff_factor (w : List Nat) :
    legal ChainInitialSegment.events [] ChainInitialSegment.final [5] w ↔
      ∃ u, I.Legal u ∧ w = ChainInitialConverse.liftWord u := by
  constructor
  · intro h
    have hg := ChainInitialSegment.all_legal_factor w h
    exact ⟨_,hg.2.2,initial_recovery w h.1 hg⟩
  · rintro ⟨u,hu,he⟩
    exact ChainInitialConverse.explicit_factor_converse w u he hu

theorem middle_legal_iff_factor (w : List Nat) :
    legal ChainMiddleSegment.events ChainMiddleSegment.initial ChainMiddleSegment.final [5,11] w ↔
      ∃ u, M.Legal u ∧ w = ChainMiddleConverse.liftWord u := by
  constructor
  · intro h
    have hg := ChainMiddleSegment.all_legal_factor w h
    exact ⟨_,hg.2.2,middle_recovery w h.1 hg⟩
  · rintro ⟨u,hu,he⟩
    exact ChainMiddleConverse.explicit_factor_converse w u he hu

#print axioms recover
#print axioms initial_recovery
#print axioms middle_recovery
#print axioms initial_legal_iff_factor
#print axioms middle_legal_iff_factor
end ChainFactorRecovery
