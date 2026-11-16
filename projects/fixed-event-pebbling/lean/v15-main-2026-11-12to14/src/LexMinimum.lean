import Std
namespace LexMinimum
theorem least_nat (P : Nat → Prop) (h : ∃n,P n) : ∃n,P n ∧ ∀m,P m → n≤m := by
 classical
 obtain ⟨n,hn⟩ := h
 suffices hh : ∀n,P n → ∃k,P k ∧ ∀m,P m → k≤m from hh n hn
 intro n
 induction n using Nat.strongRecOn with
 | ind n ih =>
   intro hn
   by_cases hs : ∃m,m<n ∧ P m
   · obtain ⟨m,hm,hp⟩ := hs
     exact ih m hm hp
   · refine ⟨n,hn,?_⟩
     intro m hm
     have hnot : ¬m<n := fun hlt => hs ⟨m,hlt,hm⟩
     omega
theorem exists_cost_then_measure {α : Type} (cost measure : α → Nat) (hne : Nonempty α) :
 ∃a:α,(∀b,cost a≤cost b) ∧ (∀b,cost b=cost a → measure a≤measure b) := by
 classical
 obtain ⟨x⟩ := hne
 obtain ⟨n,hn,hmin⟩ := least_nat (fun n=>∃a:α,cost a=n) ⟨cost x,x,rfl⟩
 have hm : ∃t,∃a:α,cost a=n ∧ measure a=t := by
   obtain ⟨a,ha⟩ := hn
   exact ⟨measure a,a,ha,rfl⟩
 obtain ⟨t,⟨a,ha,ht⟩,hmeasure⟩ := least_nat _ hm
 refine ⟨a,?_,?_⟩
 · intro b
   rw [ha]
   exact hmin (cost b) ⟨b,rfl⟩
 · intro b hb
   rw [ht]
   exact hmeasure (measure b) ⟨b,hb.trans ha,rfl⟩
#print axioms least_nat
#print axioms exists_cost_then_measure
end LexMinimum
