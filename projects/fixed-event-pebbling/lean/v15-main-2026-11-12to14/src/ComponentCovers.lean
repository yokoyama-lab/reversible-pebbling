import ComponentExclusion
namespace MComponentCover
open LocalCertificate UpperCertificate LocalUpperBridge ErasureCover

def smallCover (i : Fin 2) : Fin 14 := ⟨if i.val=0 then 5 else 10,by split <;> omega⟩
def largeCover (i : Fin 12) : Fin 14 := ⟨if i.val<5 then i.val else if i.val<9 then i.val+1 else i.val+2,by split <;> (try split) <;> omega⟩

theorem extends_satisfies (c : Fin 14) (w) (hw : Extends M.S (relationM c) w) :
 satisfiesPredecessors (UpperCertificate.M.covers.getD c.val []) w=true := by
 have len := length_of_checked 12 _ (M_checked c)
 have valid := ExtensionCompleteness.strict_poset_predecessors_valid
  (UpperCertificate.M.covers.getD c.val []) (by simpa only [len] using M_checked c)
 apply List.all_eq_true.mpr
 intro b hb
 have bl : b<12 := by simpa only [len] using List.mem_range.mp hb
 apply List.all_eq_true.mpr
 intro a ha
 have al : a<12 := by simpa only [len] using valid b (by simpa only [len] using bl) a ha
 simpa only [decide_eq_true_eq,M.S,semantics] using hw.2 ⟨a,al⟩ ⟨b,bl⟩ ha

theorem small_sound_index (c : Fin 14) (hc : c.val=5 ∨ c.val=10) :
 Sound M.S Small (relationM c) := by
 intro w hw
 refine ⟨M_sound c w hw,?_⟩
 have memberSound : Sound M.S (fun w=>w∈MSmallSwap.component) (relationM c) := by
  apply sound_of_enumerated 12 _ (fun w=>w∈MSmallSwap.component) (M_checked c)
  rcases hc with h | h
  · simpa only [h] using poset5_small
  · simpa only [h] using poset10_small
 exact memberSound w hw

theorem large_sound_index (c : Fin 14) (h5 : c.val≠5) (h10 : c.val≠10) :
 Sound M.S Large (relationM c) := by
 intro w hw
 refine ⟨M_sound c w hw,?_⟩
 intro small
 have hn := small_exclusion_check c h5 h10 w small
 have hy := extends_satisfies c w hw
 rw [hn] at hy
 contradiction

theorem small_cover_complete (w) (hw : Small w) :
 ∃i : Fin 2,Extends M.S (relationM (smallCover i)) w := by
 rcases small_covered_check w hw.2 with h | h
 · refine ⟨⟨0,by decide⟩,?_⟩
   apply satisfies_extends 12 _ w (length_of_checked 12 _ (M_checked _)) hw.1.1
   exact h
 · refine ⟨⟨1,by decide⟩,?_⟩
   apply satisfies_extends 12 _ w (length_of_checked 12 _ (M_checked _)) hw.1.1
   exact h

theorem large_cover_complete (w) (hw : Large w) :
 ∃i : Fin 12,Extends M.S (relationM (largeCover i)) w := by
 obtain ⟨c,hc⟩ := M_covers w hw.1
 have h5 : c.val≠5 := by intro eq;exact hw.2 ((small_sound_index c (Or.inl eq) w hc).2)
 have h10 : c.val≠10 := by intro eq;exact hw.2 ((small_sound_index c (Or.inr eq) w hc).2)
 have ex : ∃i : Fin 12,largeCover i=c := by
  by_cases h : c.val<5
  · refine ⟨⟨c.val,by omega⟩,?_⟩;apply Fin.ext;simp [largeCover,h]
  · by_cases h' : c.val<10
    · refine ⟨⟨c.val-1,by omega⟩,?_⟩;apply Fin.ext;dsimp [largeCover];split <;> (try split) <;> omega
    · refine ⟨⟨c.val-2,by omega⟩,?_⟩;apply Fin.ext;dsimp [largeCover];split <;> (try split) <;> omega
 obtain ⟨i,eq⟩ := ex
 exact ⟨i,by simpa only [eq] using hc⟩

theorem small_upper :
 (∀i,Strict (relationM (smallCover i))) ∧
 (∀i,Sound M.S Small (relationM (smallCover i))) ∧
 (∀w,Small w→∃i,Extends M.S (relationM (smallCover i)) w) := by
 refine ⟨fun i=>M_strict _,?_,small_cover_complete⟩
 intro i;apply small_sound_index;dsimp [smallCover];split <;> simp

theorem large_upper :
 (∀i,Strict (relationM (largeCover i))) ∧
 (∀i,Sound M.S Large (relationM (largeCover i))) ∧
 (∀w,Large w→∃i,Extends M.S (relationM (largeCover i)) w) := by
 refine ⟨fun i=>M_strict _,?_,large_cover_complete⟩
 intro i
 apply large_sound_index <;> dsimp [largeCover] <;> split <;> (try split) <;> omega

#print axioms extends_satisfies
#print axioms small_sound_index
#print axioms large_sound_index
#print axioms small_cover_complete
#print axioms large_cover_complete
#print axioms small_upper
#print axioms large_upper
end MComponentCover
