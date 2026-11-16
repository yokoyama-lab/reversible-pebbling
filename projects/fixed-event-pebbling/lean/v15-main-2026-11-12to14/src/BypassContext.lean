import LowerBypass
namespace BypassContext
open TerminalProjection LocalCertificate
theorem singleton_next {p m e a} (hm : 2≤m) (hs : Step p [m] e a)
 (bound : e.vertex≤m) (noerase : e.vertex=m → erasure [m] e=0) :
 e=⟨true,1⟩ ∧ a=[1,m] := by
 cases hp : e.place with
 | true =>
  have h : e.vertex∉[m] ∧ pred [m] e.vertex ∧ a=e.vertex::[m] := by simpa [hp] using hs.2.2
  have hv : e.vertex=1 := by
   rcases h.2.1 with hv|hv
   · exact hv
   · have hv' : e.vertex-1=m := by simpa using hv
     omega
  constructor
  · cases e;simp_all
  · simpa [hv] using h.2.2
 | false =>
  have h : e.vertex∈[m] ∧ a=[m].erase e.vertex := by simpa [hp] using hs.2.2
  have hv : e.vertex=m := by simpa using h.1
  have hz := noerase hv
  have hn : ¬pred [m] e.vertex := by simp [pred,hv];omega
  simp [erasure,hp,hn] at hz
theorem singleton_previous {p m e b} (hm : m∈b) (nd : b.Nodup)
 (hs : Step p b e [m]) :
 e.place=false ∧ e.vertex≠m ∧ b.Perm [e.vertex,m] := by
 cases hp : e.place with
 | true =>
  have h : e.vertex∉b ∧ pred b e.vertex ∧ [m]=e.vertex::b := by simpa [hp] using hs.2.2
  have hb : b=[] := (List.cons.inj h.2.2).2.symm
  simp [hb] at hm
 | false =>
  have h : e.vertex∈b ∧ [m]=b.erase e.vertex := by simpa [hp] using hs.2.2
  have hn : e.vertex≠m := by
   intro he
   have hmm : m∈b.erase e.vertex := by rw [←h.2];simp
   exact (nd.mem_erase_iff.mp hmm).1 he.symm
  refine ⟨rfl,hn,?_⟩
  have hh := List.perm_cons_erase h.1
  simpa [←h.2] using hh
theorem context_replace {p initial b a final xs old new ys cp rp co ro cn rn cs rs}
 (pre : Run p initial xs b cp rp) (localOld : Run p b old a co ro)
 (localNew : Run p b new a cn rn) (post : Run p a ys final cs rs)
 (hc : cn≤co) (hr : rn≤ro) :
 Run p initial (xs++old++ys) final (cp+co+cs) (rp+ro+rs) ∧
 Run p initial (xs++new++ys) final (cp+cn+cs) (rp+rn+rs) ∧
 cp+cn+cs≤cp+co+cs ∧ rp+rn+rs≤rp+ro+rs := by
 exact ⟨run_append (run_append pre localOld) post,
  run_append (run_append pre localNew) post,by omega,by omega⟩
theorem swap_in_context {p m q initial final xs ys cp rp cs rs}
 (hq : 2≤q) (hqm : q<m) (hp : 3≤p)
 (pre : Run p initial xs [m,q] cp rp) (post : Run p [1,m] ys final cs rs) :
 ∃c r,Run p initial (xs++[⟨true,1⟩,⟨false,q⟩]++ys) final c r ∧
 c≤cp+10+cs ∧ r≤rp+1+rs := by
 obtain ⟨hold,c,r,hnew,hc,hr⟩ := LowerBypass.swap_disposal_add_one m q p hq hqm hp
 have h := context_replace pre hold hnew post hc hr
 exact ⟨cp+c+cs,rp+r+rs,h.2.1,h.2.2.1,h.2.2.2⟩
#print axioms singleton_next
#print axioms singleton_previous
#print axioms swap_in_context
end BypassContext
