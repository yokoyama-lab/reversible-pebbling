import CleanHandoffMeasure
namespace LastBad
open LocalCertificate TerminalProjection VisitMeasure CleanHandoffMeasure TerminalExistence
theorem split_last {n m b es} (hm : m∈bad n b es) :
 ∃pre e post, es=pre++e::post ∧ evolve b pre=[m] ∧ m<n ∧ e.vertex≤m ∧
 m∉bad n (update [m] e) post := by
 induction es generalizing b with
 | nil => simp [bad] at hm
 | cons e es ih =>
  by_cases ht : m∈bad n (update b e) es
  · obtain ⟨pre,f,post,he,hb,hn,hf,hno⟩ := ih ht
    exact ⟨e::pre,f,post,by simp [he],by simpa [evolve] using hb,hn,hf,hno⟩
  · cases b with
    | nil => simp [bad,ht] at hm
    | cons a bs =>
      cases bs with
      | cons x xs => simp [bad,ht] at hm
      | nil =>
        by_cases h : a<n ∧ e.vertex≤a
        · simp [bad,h,ht] at hm
          subst m
          exact ⟨[],e,es,rfl,rfl,h.1,h.2,ht⟩
        · simp [bad,h,ht] at hm

theorem split_last_run {p n m b es z c r}
 (hr : Run p b es z c r) (hm : m∈bad n b es) :
 ∃pre e post a c1 r1 c2 r2,
 es=pre++e::post ∧ Run p b pre [m] c1 r1 ∧ Step p [m] e a ∧
 Run p a post z c2 r2 ∧ m<n ∧ e.vertex≤m ∧ m∉bad n a post ∧
 c=c1+fee [m] e+c2 ∧ r=r1+erasure [m] e+r2 := by
 obtain ⟨pre,e,post,he,hb,hn,hv,hno⟩ := split_last hm
 rw [he] at hr
 obtain ⟨q,c1,r1,d,s,hpre,hrest,hc,her⟩ := run_split hr
 have hq : q=[m] := (run_evolve hpre).symm.trans hb
 subst q
 cases hrest with
 | @cons b a z es d t ev hs ht =>
  have ha : a=update [m] e := (step_update hs).symm
  refine ⟨pre,e,post,a,c1,r1,d,t,he,hpre,hs,ht,hn,hv,?_,?_,?_⟩
  · simpa [ha] using hno
  · omega
  · omega

theorem last_suffix_below {n m b pre e post}
 (hb : evolve b pre=[m])
 (bound : ∀j∈bad n b (pre++e::post),j≤m)
 (last : m∉bad n (update [m] e) post) :
 ∀j∈bad n (update [m] e) post,j<m := by
 intro j hj
 have hmem : j∈bad n b (pre++e::post) := by
  rw [bad_append,hb]
  apply List.mem_append_right
  simp only [bad,List.mem_append]
  exact Or.inr hj
 have hle := bound j hmem
 have hne : j≠m := by intro h;subst j;exact last hj
 omega
theorem first_upper {m : Nat} {es : List Event}
 (h : ∃e∈es,m<e.vertex) :
 ∃pre e post,es=pre++e::post ∧ (∀f∈pre,f.vertex≤m) ∧ m<e.vertex := by
 induction es with
 | nil => simp at h
 | cons e es ih =>
  by_cases he : m<e.vertex
  · exact ⟨[],e,es,rfl,by simp,he⟩
  · have ht : ∃f∈es,m<f.vertex := by simpa [he] using h
    obtain ⟨pre,f,post,hw,hpre,hf⟩ := ih ht
    refine ⟨e::pre,f,post,by simp [hw],?_,hf⟩
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · omega
    · exact hpre g hg

theorem evolve_bounded {m b es}
 (hb : ∀v∈b,v≤m) (he : ∀e∈es,e.vertex≤m) :
 ∀v∈evolve b es,v≤m := by
 induction es generalizing b with
 | nil => simpa [evolve] using hb
 | cons e es ih =>
  apply ih
  · intro v hv
    cases hp : e.place with
    | true =>
      simp [update,hp] at hv
      rcases hv with rfl | hv
      · exact he e (by simp)
      · exact hb v hv
    | false => exact hb v (List.mem_of_mem_erase (by simpa [update,hp] using hv))
  · intro f hf; exact he f (by simp [hf])

theorem upper_exists {p m n b es z c r}
 (hr : Run p b es z c r) (hb : ∀v∈b,v≤m) (hn : n∈z) (hm : m<n) :
 ∃e∈es,m<e.vertex := by
 apply Classical.byContradiction
 intro no
 have he : ∀e∈es,e.vertex≤m := by
  intro e he
  have h : ¬m<e.vertex := fun hgt => no ⟨e,he,hgt⟩
  omega
 have hb' := evolve_bounded hb he
 rw [run_evolve hr] at hb'
 have hh := hb' n hn
 omega

#print axioms first_upper
#print axioms upper_exists
#print axioms split_last_run
#print axioms last_suffix_below
end LastBad
