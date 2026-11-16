import LastBad
namespace FirstUpperStructure
open LocalCertificate TerminalProjection TerminalExistence VisitMeasure

theorem step_above_bound {p m b a e}
 (hs : Step p b e a) (hb : ∀v∈b,v≤m) (above : m<e.vertex) :
 e.place=true ∧ e.vertex=m+1 ∧ (m=0 ∨ m∈b) ∧ b.length≤p-1 := by
 cases hp : e.place with
 | false =>
  have he : e.vertex∈b ∧ a=b.erase e.vertex := by simpa [hp] using hs.2.2
  have h := hb e.vertex he.1
  omega
 | true =>
  have he : e.vertex∉b ∧ pred b e.vertex ∧ a=e.vertex::b := by simpa [hp] using hs.2.2
  have hc := hs.2.1
  rw [he.2.2] at hc
  simp only [List.length_cons] at hc
  rcases he.2.1 with h1 | hmem
  · exact ⟨rfl,by omega,Or.inl (by omega),by omega⟩
  · have hv := hb (e.vertex-1) hmem
    have hvEq : e.vertex=m+1 := by omega
    refine ⟨rfl,hvEq,Or.inr ?_,by omega⟩
    simpa [hvEq] using hmem

theorem step_above_positive_bound {p m b a e}
 (hm : 1≤m) (hs : Step p b e a) (hb : ∀v∈b,v≤m) (above : m<e.vertex) :
 e.place=true ∧ e.vertex=m+1 ∧ m∈b ∧ b.length≤p-1 := by
 obtain ⟨hp,hv,hmemb,hcap⟩ := step_above_bound hs hb above
 exact ⟨hp,hv,hmemb.resolve_left (by omega),hcap⟩

theorem low_run_bounded {p m b pre q c r}
 (hr : Run p b pre q c r) (hb : ∀v∈b,v≤m) (low : ∀e∈pre,e.vertex≤m) :
 ∀v∈q,v≤m := by
 have h := LastBad.evolve_bounded hb low
 simpa only [run_evolve hr] using h

theorem first_upper_run {p m b es z c r}
 (hm : 1≤m) (hr : Run p b es z c r) (hb : ∀v∈b,v≤m)
 (upper : ∃e∈es,m<e.vertex) :
 ∃pre post q a cp rp ct rt,
 es=pre++⟨true,m+1⟩::post ∧
 Run p b pre q cp rp ∧ Step p q ⟨true,m+1⟩ a ∧ Run p a post z ct rt ∧
 (∀e∈pre,e.vertex≤m) ∧ (∀v∈q,v≤m) ∧ m∈q ∧ q.length≤p-1 ∧
 c=cp+1+ct ∧ r=rp+rt := by
 obtain ⟨pre,e,post,hw,low,above⟩ := LastBad.first_upper upper
 have hr' : Run p b (pre++e::post) z c r := by simpa only [←hw] using hr
 obtain ⟨q,cp,rp,d,s,hpre,hrest,hc,her⟩ := run_split hr'
 have hq := low_run_bounded hpre hb low
 cases hrest with
 | @cons q a z es ct rt ev hs ht =>
  obtain ⟨hp,hv,hmq,hcap⟩ := step_above_positive_bound hm hs hq above
  have ee : e=⟨true,m+1⟩ := by cases e; simp_all
  subst e
  refine ⟨pre,post,q,a,cp,rp,ct,rt,hw,hpre,hs,ht,low,hq,hmq,hcap,?_,?_⟩
  · simpa [fee,Nat.add_assoc] using hc
  · simpa [erasure] using her

#print axioms step_above_bound
#print axioms step_above_positive_bound
#print axioms low_run_bounded
#print axioms first_upper_run
end FirstUpperStructure
