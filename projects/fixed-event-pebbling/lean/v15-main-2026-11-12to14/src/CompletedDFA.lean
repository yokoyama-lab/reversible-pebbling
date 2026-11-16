import LabelledResidual
namespace CompletedSetDFA
abbrev Language := List Nat → Prop
def Viable (L : Language) (u : List Nat) : Prop := ∃s,L (u++s)
def Same (u v : List Nat) : Prop := ∀i,i∈u ↔ i∈v
def Respects (L : Language) : Prop := ∀u v,Viable L u → Viable L v → Same u v → ∀s,L (u++s)↔L (v++s)
def Live (L : Language) := {S : Nat → Prop // ∃u,Viable L u ∧ ∀i,S i ↔ i∈u}
abbrev State (L : Language) := Option (Live L)
noncomputable def representative {L : Language} (q : Live L) : List Nat := Classical.choose q.property
theorem representative_viable {L : Language} (q : Live L) : Viable L (representative q) :=
 (Classical.choose_spec q.property).1
theorem representative_set {L : Language} (q : Live L) : ∀i,q.val i ↔ i∈representative q :=
 (Classical.choose_spec q.property).2
noncomputable def make (L : Language) (u : List Nat) : State L := by
 classical
 exact if h : Viable L u then some ⟨(fun i => i∈u),u,h,fun _ => Iff.rfl⟩ else none
noncomputable def step (L : Language) (q : State L) (a : Nat) : State L :=
 match q with | none => none | some q => make L (representative q ++ [a])
def Accept (L : Language) (q : State L) : Prop :=
 match q with | none => False | some q => L (representative q)
noncomputable def run (L : Language) : State L → List Nat → State L
 | q,[] => q
 | q,a::w => run L (step L q a) w
noncomputable def initial (L : Language) : State L := make L []
theorem make_eq {L : Language} {u v : List Nat} (hs : Same u v)
 (hv : Viable L u ↔ Viable L v) : make L u=make L v := by
 classical
 unfold make
 by_cases hu : Viable L u
 · have hv' := hv.mp hu
   simp only [dif_pos hu,dif_pos hv']
   congr 1
   apply Subtype.ext
   funext i
   exact propext (hs i)
 · have hv' : ¬Viable L v := fun h => hu (hv.mpr h)
   simp [hu,hv']
theorem viable_of_append {L : Language} {u v : List Nat} (h : Viable L (u++v)) : Viable L u := by
 obtain ⟨s,hs⟩ := h
 exact ⟨v++s,by simpa [List.append_assoc] using hs⟩
theorem step_make (L : Language) (respect : Respects L) (u : List Nat) (a : Nat) :
 step L (make L u) a=make L (u++[a]) := by
 classical
 by_cases hu : Viable L u
 · let q : Live L := ⟨(fun i => i∈u),u,hu,fun _ => Iff.rfl⟩
   have hmake : make L u=some q := by simp [make,hu,q]
   rw [hmake]
   change make L (representative q++[a])=make L (u++[a])
   have same : Same (representative q) u := fun i => (representative_set q i).symm
   apply make_eq
   · intro i;simpa only [List.mem_append,List.mem_singleton] using or_congr (same i) Iff.rfl
   · constructor
     · rintro ⟨s,hs⟩
       refine ⟨s,?_⟩
       have h := (respect _ _ (representative_viable q) hu same ([a]++s)).mp
         (by simpa [List.append_assoc] using hs)
       simpa [List.append_assoc] using h
     · rintro ⟨s,hs⟩
       refine ⟨s,?_⟩
       have h := (respect _ _ (representative_viable q) hu same ([a]++s)).mpr
         (by simpa [List.append_assoc] using hs)
       simpa [List.append_assoc] using h
 · have hn : ¬Viable L (u++[a]) := fun h => hu (viable_of_append h)
   simp [make,hu,hn,step]
theorem accept_make (L : Language) (respect : Respects L) (u : List Nat) :
 Accept L (make L u) ↔ L u := by
 classical
 by_cases hu : Viable L u
 · let q : Live L := ⟨(fun i => i∈u),u,hu,fun _ => Iff.rfl⟩
   have hmake : make L u=some q := by simp [make,hu,q]
   rw [hmake]
   have same : Same (representative q) u := fun i => (representative_set q i).symm
   simpa [Accept] using respect _ _ (representative_viable q) hu same []
 · have hn : ¬L u := fun h => hu ⟨[],by simpa using h⟩
   simp [make,hu,Accept,hn]
theorem run_make (L : Language) (respect : Respects L) (u w : List Nat) :
 run L (make L u) w=make L (u++w) := by
 induction w generalizing u with
 | nil => simp [run]
 | cons a w ih =>
  rw [run,step_make L respect,ih]
  simp [List.append_assoc]
theorem recognizes (L : Language) (respect : Respects L) (w : List Nat) :
 Accept L (run L (initial L) w) ↔ L w := by
 rw [initial,run_make L respect]
 simpa using accept_make L respect w
theorem rejecting_absorbs (L : Language) (a : Nat) : step L none a=none := rfl
theorem step_live_set (L : Language) (q q' : Live L) (a : Nat)
 (h : step L (some q) a=some q') : ∀i,q'.val i ↔ q.val i ∨ i=a := by
 classical
 change make L (representative q ++ [a])=some q' at h
 unfold make at h
 split at h
 · have he := Option.some.inj h
   subst q'
   intro i
   simpa using or_congr (representative_set q i).symm (Iff.rfl : i=a ↔ i=a)
 · contradiction
#print axioms step_live_set
#print axioms recognizes
end CompletedSetDFA
namespace ChainCompletedDFA
open ChainOccurrence CompletedSetDFA
theorem respects (r : Nat) (E : List Nat) : Respects (labelledLegal r E) := by
 intro u v hu hv hs
 exact ChainLabelledResidual.same_completed_labelled_residual r E u v hs hu hv
theorem recognizes_labelled (r : Nat) (E w : List Nat) :
 Accept (labelledLegal r E) (run (labelledLegal r E) (initial (labelledLegal r E)) w) ↔ labelledLegal r E w :=
 recognizes _ (respects r E) w
theorem live_bounded (r : Nat) (E : List Nat) (q : Live (labelledLegal r E)) :
 ∀i,q.val i → i < (ChainAssembledTrace.fullTable r).length := by
 obtain ⟨u,⟨s,hs⟩,hu⟩ := q.property
 intro i hi
 exact hs.1.2.2 i (List.mem_append_left s ((hu i).mp hi))
noncomputable def liveMask (r : Nat) (E : List Nat) (q : Live (labelledLegal r E)) :
 Fin (ChainAssembledTrace.fullTable r).length → Bool := by
 classical
 exact fun i => decide (q.val i.val)
theorem liveMask_injective (r : Nat) (E : List Nat) (a b : Live (labelledLegal r E))
 (h : liveMask r E a=liveMask r E b) : a=b := by
 classical
 apply Subtype.ext
 funext i
 apply propext
 by_cases hi : i < (ChainAssembledTrace.fullTable r).length
 · have he := congrFun h ⟨i,hi⟩
   simpa [liveMask] using he
 · have ha : ¬a.val i := fun hh => hi (live_bounded r E a i hh)
   have hb : ¬b.val i := fun hh => hi (live_bounded r E b i hh)
   simp [ha,hb]
noncomputable def stateMask (r : Nat) (E : List Nat) : State (labelledLegal r E) →
 Option (Fin (ChainAssembledTrace.fullTable r).length → Bool)
 | none => none
 | some q => some (liveMask r E q)
theorem stateMask_injective (r : Nat) (E : List Nat) (a b : State (labelledLegal r E))
 (h : stateMask r E a=stateMask r E b) : a=b := by
 cases a with
 | none => cases b <;> simp [stateMask] at *
 | some a =>
  cases b with
  | none => simp [stateMask] at h
  | some b => exact congrArg some (liveMask_injective r E a b (Option.some.inj h))
#print axioms stateMask_injective
#print axioms recognizes_labelled
end ChainCompletedDFA
