import LastBad
namespace MaxBad
open LocalCertificate TerminalProjection VisitMeasure CleanHandoffMeasure LastBad
theorem rank_witness {xs : List Nat} (h : 0<rank xs) :
 ∃m∈xs,rank xs=m+1 := by
 induction xs with
 | nil => simp [rank] at h
 | cons a xs ih =>
  by_cases hle : rank xs≤a+1
  · exact ⟨a,by simp,by simp [rank,Nat.max_eq_left hle]⟩
  · have ht : 0<rank xs := by omega
    obtain ⟨m,hm,he⟩ := ih ht
    exact ⟨m,by simp [hm],by rw [rank,Nat.max_eq_right (by omega : a+1≤rank xs)]; exact he⟩

theorem maximal {xs : List Nat} (h : xs≠[]) :
 ∃m∈xs,∀j∈xs,j≤m := by
 have hp : 0<rank xs := by
  cases xs with
  | nil => exact False.elim (h rfl)
  | cons a xs => simp only [rank];have hh:=Nat.le_max_left (a+1) (rank xs);omega
 obtain ⟨m,hm,he⟩ := rank_witness hp
 refine ⟨m,hm,?_⟩
 intro j hj
 have hh := member_rank hj
 omega

theorem maximal_last_run {p n b es z c r}
 (hr : Run p b es z c r) (badExists : bad n b es≠[]) :
 ∃m pre e post a c1 r1 c2 r2,
 es=pre++e::post ∧ Run p b pre [m] c1 r1 ∧ Step p [m] e a ∧
 Run p a post z c2 r2 ∧ m<n ∧ e.vertex≤m ∧
 (∀j∈bad n b es,j≤m) ∧ (∀j∈bad n a post,j<m) ∧
 c=c1+fee [m] e+c2 ∧ r=r1+erasure [m] e+r2 := by
 obtain ⟨m,hm,hmax⟩ := maximal badExists
 obtain ⟨pre,e,post,a,c1,r1,c2,r2,hw,hpre,hs,ht,hn,hv,hno,hc,her⟩ := split_last_run hr hm
 refine ⟨m,pre,e,post,a,c1,r1,c2,r2,hw,hpre,hs,ht,hn,hv,hmax,?_,hc,her⟩
 have hb : evolve b pre=[m] := run_evolve hpre
 have ha : a=update [m] e := (step_update hs).symm
 rw [ha] at hno ⊢
 apply last_suffix_below hb
 · simpa [hw] using hmax
 · exact hno
theorem board_positive {p b es z c r}
 (hr : Run p b es z c r) (hb : ∀v∈b,1≤v) : ∀v∈z,1≤v := by
 induction hr with
 | nil => exact hb
 | @cons b a z es c r e hs ht ih =>
  apply ih
  intro v hv
  have ha := step_update hs
  rw [←ha] at hv
  cases hp : e.place with
  | true =>
    simp [update,hp] at hv
    rcases hv with rfl | hv
    · exact hs.1
    · exact hb v hv
  | false => exact hb v (List.mem_of_mem_erase (by simpa [update,hp] using hv))

theorem singleton_positive {p es m c r} (hr : Run p [] es [m] c r) : 1≤m := by
 exact board_positive hr (by simp) m (by simp)
#print axioms singleton_positive
#print axioms maximal_last_run
end MaxBad
