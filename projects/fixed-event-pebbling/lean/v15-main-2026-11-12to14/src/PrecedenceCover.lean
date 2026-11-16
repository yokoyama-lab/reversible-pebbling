import PhysicalCover
namespace PrecedenceCover
open ErasureCover
universe u v
inductive Closure {α : Type u} (R : α→α→Prop) : α→α→Prop
 | edge {a b} : R a b → Closure R a b
 | trans {a b c} : Closure R a b → Closure R b c → Closure R a c

def combined {α : Type u} (P Q : α→α→Prop) : α→α→Prop := Closure (fun a b=>P a b ∨ Q a b)
def Acyclic {α : Type u} (P : α→α→Prop) := ∀a,¬P a a

theorem combined_strict {α : Type u} {P Q : α→α→Prop}
 (h : Acyclic (combined P Q)) : StrictOrder (combined P Q) :=
 ⟨h,fun _ _ _=>Closure.trans⟩

theorem extends_combined {α : Type u} {T : Type v} (S : Semantics α T)
 (ht : ∀w,S.admissible w→∀a b c,S.before w a b→S.before w b c→S.before w a c)
 (P Q : α→α→Prop) (w : T) :
 Extends S (combined P Q) w ↔ Extends S P w ∧ Extends S Q w := by
 constructor
 · intro h
   exact ⟨⟨h.1,fun a b hab=>h.2 a b (.edge (.inl hab))⟩,
    ⟨h.1,fun a b hab=>h.2 a b (.edge (.inr hab))⟩⟩
 · rintro ⟨hp,hq⟩
   refine ⟨hp.1,?_⟩
   intro a b hab
   induction hab with
   | edge h => exact h.elim (hp.2 _ _) (hq.2 _ _)
   | trans _ _ ih₁ ih₂ => exact ht w hp.1 _ _ _ ih₁ ih₂

theorem extension_acyclic {α : Type u} {T : Type v} (S : Semantics α T)
 (hi : ∀w,S.admissible w→∀a,¬S.before w a a)
 (P : α→α→Prop) (w : T) (hw : Extends S P w) : Acyclic P := by
 intro a ha;exact hi w hw.1 a (hw.2 a a ha)

noncomputable def surviving {α : Type u} (Ps : List (α→α→Prop)) (Q : α→α→Prop) := by
 classical
 exact (Ps.map (fun P=>combined P Q)).filter (fun R=>decide (Acyclic R))
theorem surviving_length {α : Type u} (Ps : List (α→α→Prop)) (Q : α→α→Prop) :
 (surviving Ps Q).length ≤ Ps.length := by
 classical
 simpa [surviving] using (List.length_filter_le (p:=fun R=>decide (Acyclic R)) (l:=Ps.map (fun P=>combined P Q)))
theorem mem_surviving {α : Type u} (Ps : List (α→α→Prop)) (Q R : α→α→Prop) :
 R∈surviving Ps Q ↔ (∃P∈Ps,combined P Q=R) ∧ Acyclic R := by
 classical simp [surviving,List.mem_filter,List.mem_map]

theorem restrict_cover {α : Type u} {T : Type v} (S : Semantics α T)
 (hi : ∀w,S.admissible w→∀a,¬S.before w a a)
 (ht : ∀w,S.admissible w→∀a b c,S.before w a b→S.before w b c→S.before w a c)
 (L : T→Prop) (Ps : List (α→α→Prop)) (Q : α→α→Prop)
 (hs : ∀P∈Ps,Sound S L P)
 (hc : ∀w,L w→∃P∈Ps,Extends S P w) :
 ∃Rs : List (α→α→Prop), Rs.length ≤ Ps.length ∧
 (∀R∈Rs,StrictOrder R ∧ Sound S (fun w=>L w ∧ Extends S Q w) R) ∧
 (∀w,L w ∧ Extends S Q w→∃R∈Rs,Extends S R w) := by
 refine ⟨surviving Ps Q,surviving_length Ps Q,?_,?_⟩
 · intro R hR
   obtain ⟨⟨P,hP,rfl⟩,ha⟩ := (mem_surviving Ps Q R).mp hR
   refine ⟨combined_strict ha,?_⟩
   intro w hw
   have ex := (extends_combined S ht P Q w).mp hw
   exact ⟨hs P hP w ex.1,ex.2⟩
 · intro w hw
   obtain ⟨P,hP,hpw⟩ := hc w hw.1
   have ex := (extends_combined S ht P Q w).mpr ⟨hpw,hw.2⟩
   exact ⟨combined P Q,(mem_surviving Ps Q _).mpr ⟨⟨P,hP,rfl⟩,extension_acyclic S hi _ w ex⟩,ex⟩
#print axioms restrict_cover
end PrecedenceCover
namespace PrecedenceCover
open ErasureCover
universe u v
/-- Uniform finite-index form: cyclic unions are discarded, so the new number m is at most n. -/
theorem restrict_finite_cover {α : Type u} {T : Type v} (S : Semantics α T)
 (hi : ∀w,S.admissible w→∀a,¬S.before w a a)
 (ht : ∀w,S.admissible w→∀a b c,S.before w a b→S.before w b c→S.before w a c)
 (L : T→Prop) (n : Nat) (P : Fin n→α→α→Prop) (Q : α→α→Prop)
 (hs : ∀i,Sound S L (P i))
 (hc : ∀w,L w→∃i,Extends S (P i) w) :
 ∃m, m≤n ∧ ∃R : Fin m→α→α→Prop,
 (∀i,StrictOrder (R i) ∧ Sound S (fun w=>L w ∧ Extends S Q w) (R i)) ∧
 (∀w,L w ∧ Extends S Q w→∃i,Extends S (R i) w) := by
 let Ps := (List.finRange n).map P
 have hsp : ∀p∈Ps,Sound S L p := by
  intro p hp;obtain ⟨i,_,rfl⟩ := List.mem_map.mp hp;exact hs i
 have hcp : ∀w,L w→∃p∈Ps,Extends S p w := by
  intro w hw;obtain ⟨i,hi⟩ := hc w hw
  exact ⟨P i,List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩,hi⟩
 obtain ⟨Rs,hsize,hr,hcover⟩ := restrict_cover S hi ht L Ps Q hsp hcp
 refine ⟨Rs.length,by simpa [Ps] using hsize,fun i=>Rs.get i,?_,?_⟩
 · intro i;exact hr _ (List.get_mem Rs i)
 · intro w hw;obtain ⟨R,hR,he⟩ := hcover w hw
   obtain ⟨i,hiR⟩ := List.mem_iff_get.mp hR
   refine ⟨i,?_⟩; change Extends S (Rs.get i) w; rw [hiR]; exact he

/-- Paper v11's precedence restriction bound, now on its actual occurrence-labelled pebbling language. -/
theorem physical_precedence_upper (r : Nat) (E : List Nat)
 (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (r+1) v)
 (Q : Fin (25+16*r)→Fin (25+16*r)→Prop) :
 ∃m, m≤6*14^r ∧ ∃R : Fin m→Fin (25+16*r)→Fin (25+16*r)→Prop,
 (∀i,StrictOrder (R i) ∧ Sound (LocalCertificate.semantics (25+16*r))
   (fun w=>ChainOccurrence.labelledLegal r E w ∧ Extends (LocalCertificate.semantics (25+16*r)) Q w) (R i)) ∧
 (∀w,ChainOccurrence.labelledLegal r E w ∧ Extends (LocalCertificate.semantics (25+16*r)) Q w→
   ∃i,Extends (LocalCertificate.semantics (25+16*r)) (R i) w) := by
 have hu := ChainPhysicalCover.physical_upper r E he
 apply restrict_finite_cover (LocalCertificate.semantics (25+16*r))
  (fun _ _ _ h=>Nat.lt_irrefl _ h) (fun _ _ _ _ _ hab hbc=>Nat.lt_trans hab hbc)
  (ChainOccurrence.labelledLegal r E) (6*14^r) (ChainPhysicalCover.physicalRelation r) Q hu.2.1 hu.2.2
#print axioms restrict_finite_cover
#print axioms physical_precedence_upper
end PrecedenceCover
