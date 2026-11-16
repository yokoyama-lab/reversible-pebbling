import PhysicalComponentCount
import RawComponentCount
namespace ComponentMultiplicity
/-- Pascal's binomial coefficient, zero outside 0 ≤ a ≤ r. -/
def binomial : Nat → Nat → Nat
 | 0, 0 => 1
 | 0, _+1 => 0
 | _+1, 0 => 1
 | r+1, a+1 => binomial r (a+1) + binomial r a
theorem binomial_zero (r : Nat) : binomial r 0 = 1 := by cases r <;> rfl
/-- false chooses the large (556-word) local component. -/
def signatures : Nat → Nat → List (List Bool)
 | 0, 0 => [[]]
 | 0, _+1 => []
 | r+1, 0 => (signatures r 0).map (true :: ·)
 | r+1, a+1 => (signatures r (a+1)).map (true :: ·) ++
                (signatures r a).map (false :: ·)
theorem length_signatures (r a : Nat) : (signatures r a).length = binomial r a := by
 induction r generalizing a with
 | zero => cases a <;> rfl
 | succ r ih => cases a <;> simp [signatures, binomial, ih, binomial_zero]
theorem mem_signatures (r a : Nat) (bs : List Bool) :
 bs ∈ signatures r a ↔ bs.length = r ∧ bs.count false = a := by
 induction r generalizing a bs with
 | zero => cases a <;> cases bs <;> simp [signatures]
 | succ r ih =>
   cases bs with
   | nil => cases a <;> simp [signatures]
   | cons b bs =>
     cases a with
     | zero => cases b <;> simp [signatures, ih]
     | succ a => cases b <;> simp [signatures, ih]
theorem map_cons_nodup (b : Bool) (xs : List (List Bool)) (h : xs.Nodup) :
 (xs.map (b :: ·)).Nodup := by
 induction xs with
 | nil => simp
 | cons x xs ih =>
   simp only [List.nodup_cons] at h
   simp only [List.map_cons, List.nodup_cons]
   constructor
   · simpa using h.1
   · exact ih h.2
theorem signatures_nodup (r a : Nat) : (signatures r a).Nodup := by
 induction r generalizing a with
 | zero => cases a <;> simp [signatures]
 | succ r ih =>
   cases a with
   | zero => exact map_cons_nodup true _ (ih 0)
   | succ a =>
     apply List.nodup_append.mpr
     refine ⟨map_cons_nodup true _ (ih _), map_cons_nodup false _ (ih _), ?_⟩
     intro x hx y hy
     obtain ⟨u,_,rfl⟩ := List.mem_map.mp hx
     obtain ⟨v,_,rfl⟩ := List.mem_map.mp hy
     simp
#print axioms length_signatures
#print axioms mem_signatures
#print axioms signatures_nodup
end ComponentMultiplicity
namespace ComponentMultiplicity
 def asPattern (r : Nat) (bs : List Bool) : Fin r → Bool := fun j => bs[j.val]?.getD false
 theorem asPattern_ofFn {r} (b : Fin r → Bool) : asPattern r (List.ofFn b) = b := by
  funext j
  simp [asPattern, j.isLt]
 theorem ofFn_asPattern {r} (bs : List Bool) (h : bs.length = r) :
  List.ofFn (asPattern r bs) = bs := by
  apply List.ext_getElem (by simp [h])
  intro i h₁ h₂
  simp [asPattern, h₂]
 theorem asPattern_inj {r} {bs cs : List Bool} (hb : bs.length=r) (hc : cs.length=r)
  (eq : asPattern r bs = asPattern r cs) : bs=cs := by
  have e := congrArg List.ofFn eq
  simpa [ofFn_asPattern bs hb, ofFn_asPattern cs hc] using e
 def reps (r a : Nat) : List (List Nat) :=
  (signatures r a).map (fun bs => ComponentPatterns.representative (asPattern r bs))
 theorem length_reps (r a : Nat) : (reps r a).length = binomial r a := by
  simp [reps, length_signatures]
 theorem reps_legal {r a E}
  (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (r+1) v)
  (w : List Nat) (hw : w ∈ reps r a) : ChainOccurrence.labelledLegal r E w := by
  obtain ⟨bs,_,rfl⟩ := List.mem_map.mp hw
  exact ComponentPatterns.representative_legal he _
 theorem reps_reach_iff {r a E}
  (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (r+1) v)
  (u v : List Nat) (hu : u∈reps r a) (hv : v∈reps r a) :
  SwapComponents.Reach (ChainOccurrence.labelledLegal r E) u v ↔ u=v := by
  obtain ⟨bs,_,rfl⟩ := List.mem_map.mp hu
  obtain ⟨cs,_,rfl⟩ := List.mem_map.mp hv
  constructor
  · intro h
    exact congrArg ComponentPatterns.representative ((ComponentPatterns.representatives_reach_iff he _ _).mp h)
  · intro h; rw [h]
    exact .refl (ComponentPatterns.representative_legal he _)
 theorem reps_nodup {r a} {E : List Nat}
  (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (r+1) v) : (reps r a).Nodup := by
  have inj : ∀bs∈signatures r a, ∀cs∈signatures r a,
   ComponentPatterns.representative (asPattern r bs) = ComponentPatterns.representative (asPattern r cs) → bs=cs := by
   intro bs hb cs hc eq
   apply asPattern_inj ((mem_signatures r a bs).mp hb).1 ((mem_signatures r a cs).mp hc).1
   apply (ComponentPatterns.representatives_reach_iff he _ _).mp
   rw [eq]
   exact .refl (ComponentPatterns.representative_legal he _)
  have nd := signatures_nodup r a
  unfold reps
  generalize signatures r a = xs at *
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.nodup_cons] at nd
    simp only [List.map_cons, List.nodup_cons]
    constructor
    · intro hm
      obtain ⟨y,hy,eq⟩ := List.mem_map.mp hm
      exact nd.1 ((inj x (by simp) y (by simp [hy]) eq.symm) ▸ hy)
    · apply ih
      · intro bs hb cs hc; exact inj bs (by simp [hb]) cs (by simp [hc])
      · exact nd.2
#print axioms asPattern_ofFn
#print axioms ofFn_asPattern
#print axioms reps_nodup
end ComponentMultiplicity
namespace ComponentMultiplicity
/-- A component has type a when its unique Boolean signature has a large factors. -/
def HasType (r a : Nat) (E : List Nat) (w : List Nat) : Prop :=
 ∃b : Fin r → Bool, (List.ofFn b).count false = a ∧
 SwapComponents.Reach (ChainOccurrence.labelledLegal r E) (ComponentPatterns.representative b) w

theorem reps_complete {r a E}
 (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (r+1) v)
 (w : List Nat) : HasType r a E w ↔
 ∃u∈reps r a, SwapComponents.Reach (ChainOccurrence.labelledLegal r E) u w := by
 constructor
 · rintro ⟨b,hb,hw⟩
   refine ⟨ComponentPatterns.representative b,?_,hw⟩
   apply List.mem_map.mpr
   refine ⟨List.ofFn b,(mem_signatures _ _ _).mpr ⟨List.length_ofFn,hb⟩,?_⟩
   rw [asPattern_ofFn]
 · rintro ⟨u,hu,hw⟩
   obtain ⟨bs,hbs,rfl⟩ := List.mem_map.mp hu
   have hs := (mem_signatures r a bs).mp hbs
   refine ⟨asPattern r bs,?_,hw⟩
   rw [ofFn_asPattern bs hs.1]
   exact hs.2

theorem exact_multiplicity (r a : Nat) (E : List Nat)
 (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (r+1) v) :
 ∃us : List (List Nat), us.Nodup ∧ us.length = binomial r a ∧
 (∀u∈us,ChainOccurrence.labelledLegal r E u) ∧
 (∀u∈us,∀v∈us,SwapComponents.Reach (ChainOccurrence.labelledLegal r E) u v ↔ u=v) ∧
 (∀w,HasType r a E w ↔ ∃u∈us,SwapComponents.Reach (ChainOccurrence.labelledLegal r E) u w) := by
 exact ⟨reps r a,reps_nodup he,length_reps r a,reps_legal he,
   fun u hu v hv=>reps_reach_iff he u v hu hv,reps_complete he⟩

/-- Membership has one well-defined type: it cannot be reclassified by another signature. -/
theorem type_unique {r a b E}
 (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (r+1) v)
 (w : List Nat) (ha : HasType r a E w) (hb : HasType r b E w) : a=b := by
 obtain ⟨s,hs,hsa⟩ := ha
 obtain ⟨t,ht,htb⟩ := hb
 have eq := (ComponentPatterns.representatives_reach_iff he s t).mp
  (SwapGraphBasics.reach_trans hsa (SwapGraphBasics.reach_symm htb))
 subst t
 omega
#print axioms exact_multiplicity
#print axioms type_unique
end ComponentMultiplicity
namespace ComponentMultiplicity
open ChainWholeBijection ChainLabelledCount
noncomputable def rawOf (r : Nat) (E : List Nat) (w : List Nat) : List LocalCertificate.Event := by
 classical
 exact if h : ChainOccurrence.labelledLegal r E w then (toRaw ⟨w,h⟩).val else []
theorem rawOf_eq {r E w} (h : ChainOccurrence.labelledLegal r E w) :
 rawOf r E w = (toRaw ⟨w,h⟩).val := by classical simp [rawOf,h]
theorem rawOf_legal {r E w} (h : ChainOccurrence.labelledLegal r E w) :
 FamilyCut.Trace (r+1) E (rawOf r E w) := by rw [rawOf_eq h]; exact (toRaw ⟨w,h⟩).property
theorem rawOf_reach {r E u v} (hu : ChainOccurrence.labelledLegal r E u)
 (hv : ChainOccurrence.labelledLegal r E v) :
 SwapComponents.Reach (ChainOccurrence.labelledLegal r E) u v ↔
 RawSwapGraph.Reach (FamilyCut.Trace (r+1) E) (rawOf r E u) (rawOf r E v) := by
 rw [rawOf_eq hu,rawOf_eq hv]
 exact RawSwapGraph.reach_iff_decode hu hv (toRaw_spec ⟨u,hu⟩) (toRaw_spec ⟨v,hv⟩)

def RawHasType (r a : Nat) (E : List Nat) (w : List LocalCertificate.Event) : Prop :=
 ∃b : Fin r → Bool, (List.ofFn b).count false = a ∧
 RawSwapGraph.Reach (FamilyCut.Trace (r+1) E) (rawOf r E (ComponentPatterns.representative b)) w
noncomputable def rawReps (r a : Nat) (E : List Nat) := (reps r a).map (rawOf r E)
theorem rawReps_length (r a E) : (rawReps r a E).length = binomial r a := by
 simp [rawReps,length_reps]
theorem rawReps_complete {r a E}
 (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (r+1) v)
 (w : List LocalCertificate.Event) : RawHasType r a E w ↔
 ∃u∈rawReps r a E,RawSwapGraph.Reach (FamilyCut.Trace (r+1) E) u w := by
 constructor
 · rintro ⟨b,hb,hw⟩
   refine ⟨rawOf r E (ComponentPatterns.representative b),?_,hw⟩
   apply List.mem_map.mpr
   refine ⟨ComponentPatterns.representative b,?_,rfl⟩
   apply List.mem_map.mpr
   refine ⟨List.ofFn b,(mem_signatures _ _ _).mpr ⟨List.length_ofFn,hb⟩,?_⟩
   rw [asPattern_ofFn]
 · rintro ⟨u,hu,hw⟩
   obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hu
   obtain ⟨bs,hbs,rfl⟩ := List.mem_map.mp hv
   have hs := (mem_signatures r a bs).mp hbs
   refine ⟨asPattern r bs,?_,hw⟩
   rw [ofFn_asPattern bs hs.1];exact hs.2

theorem rawReps_nodup {r a} {E : List Nat}
 (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (r+1) v) : (rawReps r a E).Nodup := by
 have inj : ∀u∈reps r a,∀v∈reps r a,rawOf r E u=rawOf r E v→u=v := by
  intro u hu v hv eq
  apply (reps_reach_iff he u v hu hv).mp
  apply (rawOf_reach (reps_legal he u hu) (reps_legal he v hv)).mpr
  rw [eq];exact .refl (rawOf_legal (reps_legal he v hv))
 have nd := reps_nodup (r:=r) (a:=a) he
 unfold rawReps
 generalize reps r a = xs at *
 induction xs with
 | nil => simp
 | cons x xs ih =>
  simp only [List.nodup_cons] at nd
  simp only [List.map_cons,List.nodup_cons]
  constructor
  · intro hm
    obtain ⟨y,hy,eq⟩ := List.mem_map.mp hm
    exact nd.1 ((inj x (by simp) y (by simp [hy]) eq.symm) ▸ hy)
  · apply ih
    · intro u hu v hv; exact inj u (by simp [hu]) v (by simp [hv])
    · exact nd.2

theorem rawReps_reach_iff {r a E}
 (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (r+1) v)
 (u v : List LocalCertificate.Event) (hu : u∈rawReps r a E) (hv : v∈rawReps r a E) :
 RawSwapGraph.Reach (FamilyCut.Trace (r+1) E) u v ↔ u=v := by
 obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hu
 obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hv
 constructor
 · intro h
   have eq := (reps_reach_iff he x y hx hy).mp ((rawOf_reach (reps_legal he x hx) (reps_legal he y hy)).mpr h)
   rw [eq]
 · intro eq;rw [eq];exact .refl (rawOf_legal (reps_legal he y hy))

theorem raw_exact_multiplicity (r a : Nat) (E : List Nat)
 (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (r+1) v) :
 ∃us : List (List LocalCertificate.Event), us.Nodup ∧ us.length = binomial r a ∧
 (∀u∈us,FamilyCut.Trace (r+1) E u) ∧
 (∀u∈us,∀v∈us,RawSwapGraph.Reach (FamilyCut.Trace (r+1) E) u v ↔ u=v) ∧
 (∀w,RawHasType r a E w ↔ ∃u∈us,RawSwapGraph.Reach (FamilyCut.Trace (r+1) E) u w) := by
 refine ⟨rawReps r a E,rawReps_nodup he,rawReps_length r a E,?_,
   fun u hu v hv=>rawReps_reach_iff he u v hu hv,rawReps_complete he⟩
 intro u hu
 obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hu
 exact rawOf_legal (reps_legal he w hw)
#print axioms raw_exact_multiplicity
end ComponentMultiplicity
namespace ComponentMultiplicity
theorem every_legal_has_type {r E}
 (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (r+1) v)
 (w : List Nat) (hw : ChainOccurrence.labelledLegal r E w) :
 ∃a, a≤r ∧ HasType r a E w ∧ ∀b,HasType r b E w→b=a := by
 obtain ⟨b,hb,_⟩ := ComponentPatterns.every_word_has_pattern he w hw
 let a := (List.ofFn b).count false
 have ha : HasType r a E w := ⟨b,rfl,hb⟩
 refine ⟨a,?_,ha,fun c hc=>type_unique he w hc ha⟩
 simpa [a] using (List.count_le_length (a:=false) (l:=List.ofFn b))
open ChainWholeBijection ChainLabelledCount
theorem raw_type_unique {r a b E}
 (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (r+1) v)
 (w : List LocalCertificate.Event) (ha : RawHasType r a E w) (hb : RawHasType r b E w) : a=b := by
 obtain ⟨s,hs,hsa⟩ := ha
 obtain ⟨t,ht,htb⟩ := hb
 have hw := RawComponentCode.raw_legal hsa
 let lab := toLabelled E he ⟨w,hw⟩
 have conv (z : Fin r → Bool) :
  SwapComponents.Reach (ChainOccurrence.labelledLegal r E) (ComponentPatterns.representative z) lab.val ↔
  RawSwapGraph.Reach (FamilyCut.Trace (r+1) E) (rawOf r E (ComponentPatterns.representative z)) w := by
  rw [rawOf_eq (ComponentPatterns.representative_legal he z)]
  exact RawSwapGraph.reach_iff_decode (ComponentPatterns.representative_legal he z) lab.property
   (toRaw_spec ⟨ComponentPatterns.representative z,ComponentPatterns.representative_legal he z⟩)
   (toLabelled_spec E he ⟨w,hw⟩)
 have eq := (ComponentPatterns.representatives_reach_iff he s t).mp
  (SwapGraphBasics.reach_trans ((conv s).mpr hsa) (SwapGraphBasics.reach_symm ((conv t).mpr htb)))
 subst t;omega
#print axioms every_legal_has_type
#print axioms raw_type_unique
end ComponentMultiplicity
