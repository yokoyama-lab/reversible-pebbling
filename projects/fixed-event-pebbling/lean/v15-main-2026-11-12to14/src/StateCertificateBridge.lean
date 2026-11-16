import FiniteDFATransport
import StateFamilyJoin
namespace StateCertificateBridge
open CompletedSetDFA ChainStateFamilyJoin ChainPrefixSetConcat
theorem setOf_same (n : Nat) (u : List Nat) (bound : ∀i∈u,i<n) : Same (setOf n u) u := by
 intro i
 rw [setOf_bounds]
 exact ⟨fun h=>h.2,fun h=>⟨bound i h,h⟩⟩
theorem certificate_of_full (n : Nat) (L : CompletedSetDFA.Language) (sets : List (List Nat))
 (full : Full n L sets) (nd : sets.Nodup)
 (canonical : ∀c∈sets,∀d∈sets,Same c d → c=d) : FiniteDFATransport.Certificate L sets := by
 refine ⟨nd,?_,?_,canonical⟩
 · intro c hc
   obtain ⟨w,hw,t,ht,he⟩ := full.sound c hc
   refine ⟨w.take t,⟨w.drop t,by simpa using hw⟩,?_⟩
   rw [←he]
   apply setOf_same
   intro i hi
   exact List.mem_range.mp ((full.perms w hw).mem_iff.mp (List.mem_of_mem_take hi))
 · intro u hu
   obtain ⟨s,hs⟩ := hu
   have hp := full.perms (u++s) hs
   have hlen : u.length≤n := by have := hp.length_eq; simp at this;omega
   have hu_take : (u++s).take u.length=u := by simp
   refine ⟨setOf n u,?_,?_⟩
   · simpa [hu_take] using full.complete (u++s) hs u.length hlen
   · intro i
     exact (setOf_same n u (by
       intro j hj
       exact List.mem_range.mp (hp.mem_iff.mp (List.mem_append_left s hj))) i).symm
#print axioms certificate_of_full
end StateCertificateBridge
