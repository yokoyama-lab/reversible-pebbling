import DecodeSwapSplit
import CanonicalSwap
import RawSwapVertex
namespace RawSwapGraph
open LocalCertificate ChainTrace ChainOccurrence ChainLabelledCount

theorem lift_raw_edge {r E u ru rv}
 (hu : labelledLegal r E u) (du : decodeTrace (ChainAssembledTrace.fullTable r) u=some ru)
 (edge : Edge ru rv) (hr : FamilyCut.Trace (r+1) E rv) :
 ∃v,labelledLegal r E v ∧ decodeTrace (ChainAssembledTrace.fullTable r) v=some rv ∧
 (v=u ∨ v∈SwapComponents.neighbors u) := by
 obtain ⟨pre,a,b,post,eu,ev⟩ := edge
 subst ru;subst rv
 obtain ⟨raw,dd,tr⟩ := hu.2.2
 have eq : raw=pre++a::b::post := Option.some.inj (dd.symm.trans du)
 subst raw
 rcases RawSwapVertex.trace_swap_distinct_or_equal tr hr with diff | same
 · obtain ⟨p,i,j,s,eq,dp,di,dj,ds⟩ := decode_swap_split _ _ pre a b post du
   obtain ⟨ib,ie⟩ := List.getElem?_eq_some_iff.mp di
   obtain ⟨jb,je⟩ := List.getElem?_eq_some_iff.mp dj
   subst u
   let v := p++j::i::s
   have hp : (p++j::i::s).Perm (p++i::j::s) := (List.Perm.swap i j s).append_left p
   have perm := (EnumerationCorrectness.isPermutation_iff_perm_range _ _).mpr
    (hp.trans ((EnumerationCorrectness.isPermutation_iff_perm_range _ _).mp hu.1))
   have canon := CanonicalSwap.canonical_swap (ChainAssembledTrace.fullTable r) p s ⟨i,ib⟩ ⟨j,jb⟩
    (by simpa [ie,je] using diff) hu.2.1
   have dec := decode_swapped dp di dj ds
   exact ⟨v,⟨perm,canon,_,dec,hr⟩,dec,Or.inr (SwapGraphBasics.swap_context p i j s)⟩
 · subst b
   exact ⟨u,hu,du,Or.inl rfl⟩

theorem raw_path_to_labelled {r E ru rv}
 (h : Reach (FamilyCut.Trace (r+1) E) ru rv) :
 ∀u,labelledLegal r E u → decodeTrace (ChainAssembledTrace.fullTable r) u=some ru →
 ∃v,SwapComponents.Reach (labelledLegal r E) u v ∧ decodeTrace (ChainAssembledTrace.fullTable r) v=some rv := by
 induction h with
 | refl legal => intro u hu du;exact ⟨u,SwapComponents.Reach.refl hu,du⟩
 | @step ru' rv path edge legal ih =>
  intro u hu du
  obtain ⟨mid,hm,dm⟩ := ih u hu du
  obtain ⟨v,hv,dv,ev⟩ := lift_raw_edge (SwapGraphBasics.reach_legal hm) dm edge legal
  refine ⟨v,?_,dv⟩
  rcases ev with same | adjacent
  · simpa [same] using hm
  · exact SwapComponents.Reach.step hm adjacent hv

theorem reach_iff_decode {r E u v ru rv}
 (hu : labelledLegal r E u) (hv : labelledLegal r E v)
 (du : decodeTrace (ChainAssembledTrace.fullTable r) u=some ru)
 (dv : decodeTrace (ChainAssembledTrace.fullTable r) v=some rv) :
 SwapComponents.Reach (labelledLegal r E) u v ↔ Reach (FamilyCut.Trace (r+1) E) ru rv := by
 refine ⟨fun h=>labelled_path_to_raw h ru rv du dv,?_⟩
 intro h
 obtain ⟨v',hv',dv'⟩ := raw_path_to_labelled h u hu du
 have eq := labelled_decode_injective r E v' v (SwapGraphBasics.reach_legal hv') hv (dv'.trans dv.symm)
 simpa [eq] using hv'
#print axioms lift_raw_edge
#print axioms raw_path_to_labelled
#print axioms reach_iff_decode
end RawSwapGraph
