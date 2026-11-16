import LocalCounts
namespace ComponentCompleteness
theorem nodup_subset_full {α : Type} [DecidableEq α] {xs ys : List α}
 (nd : xs.Nodup) (sub : ∀x∈xs,x∈ys) (len : ys.length≤xs.length) : xs.Perm ys := by
 induction xs generalizing ys with
 | nil =>
  have hy : ys=[] := by cases ys <;> simp_all
  simp [hy]
 | cons a xs ih =>
  have am : a∈ys := sub a (by simp)
  have hn := List.nodup_cons.mp nd
  have tail : ∀x∈xs,x∈ys.erase a := by
   intro x hx
   have ne : x≠a := by intro h;subst x;exact hn.1 hx
   exact (List.mem_erase_of_ne ne).mpr (sub x (by simp [hx]))
  have leng : (ys.erase a).length≤xs.length := by
   rw [List.length_erase_of_mem am]
   simp only [List.length_cons] at len
   omega
  exact ((ih hn.2 tail leng).cons a).trans (List.perm_cons_erase am).symm

theorem middle_complete (cert : List (List Nat)) (nd : cert.Nodup)
 (len : cert.length=584) (sound : ∀w∈cert,LocalCertificate.M.Legal w) :
 ∀w,LocalCertificate.M.Legal w ↔ w∈cert := by
 have perm : cert.Perm UpperCertificate.M.physicalWords := by
  apply nodup_subset_full nd
  · intro w hw; exact (ChainWordCounts.middle_iff w).mpr (sound w hw)
  · rw [UpperCertificate.M.physical_word_count,len];omega
 intro w
 exact (ChainWordCounts.middle_iff w).symm.trans perm.mem_iff.symm

theorem initial_complete (cert : List (List Nat)) (nd : cert.Nodup)
 (len : cert.length=200) (sound : ∀w∈cert,LocalCertificate.I.Legal w) :
 ∀w,LocalCertificate.I.Legal w ↔ w∈cert := by
 have perm : cert.Perm UpperCertificate.I.physicalWords := by
  apply nodup_subset_full nd
  · intro w hw; exact (ChainWordCounts.initial_iff w).mpr (sound w hw)
  · rw [UpperCertificate.I.physical_word_count,len];omega
 intro w
 exact (ChainWordCounts.initial_iff w).symm.trans perm.mem_iff.symm
#print axioms middle_complete
#print axioms initial_complete
end ComponentCompleteness
