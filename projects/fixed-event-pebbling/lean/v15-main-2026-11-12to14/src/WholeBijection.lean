import ForwardFactor
import AssembledTrace
import TupleInjectivity
namespace ChainWholeBijection
open LocalCertificate ChainTrace FamilyCut ChainFamilyArithmetic ChainGlobalReassembly

structure LocalTuple (r : Nat) where
  initial : {u : List Nat // I.Legal u}
  middles : Fin r → {u : List Nat // M.Legal u}
  tail : {u : List Nat // u=ChainTailSegment.wordA ∨ u=ChainTailSegment.wordB}

def middleWords {r : Nat} (x : LocalTuple r) (j : Nat) : List Nat :=
  if h : j<r then (x.middles ⟨j,h⟩).val else []

@[simp] theorem middleWords_at {r : Nat} (x : LocalTuple r) (j : Nat) (h : j<r) :
    middleWords x j = (x.middles ⟨j,h⟩).val := by simp [middleWords,h]

def Physical (r : Nat) (E : List Nat) := {w : List Event // Trace (r+1) E w}

def Represents {r : Nat} (x : LocalTuple r) (word : List Event) : Prop :=
  ∃ initial middles tail,
    decodeTrace ChainInitialSegment.events (ChainInitialConverse.liftWord x.initial.val) = some initial ∧
    (∀ j, j<r → decodeTrace (MiddleDifference.events (5+6*j))
      (ChainMiddleConverse.liftWord (middleWords x j)) = some (middles j)) ∧
    decodeTrace (ReplayBridge.shiftEvents (6*r) ChainTailSegment.events) x.tail.val = some tail ∧
    word = initial ++ assemble middles r ++ tail

theorem tuple_exists {r : Nat} {E : List Nat} (w : Physical r E) :
    ∃ x : LocalTuple r, Represents x w.val := by
  obtain ⟨iu,tw,mu,a,t,ms,hi,hm,ht,da,dm,dt,he⟩ :=
    GlobalSplit.forward_factorization r E w.val w.property
  let x : LocalTuple r := ⟨⟨iu,hi⟩,fun j => ⟨mu j.val,hm j.val j.isLt⟩,⟨tw,ht⟩⟩
  refine ⟨x,a,ms,t,da,?_,dt,he⟩
  intro j hj
  simpa [middleWords,hj,x] using dm j hj

theorem physical_exists {r : Nat} (E : List Nat)
    (hE : ∀ v, v∈E ↔ IsErasure (r+1) v) (x : LocalTuple r) :
    ∃ w : Physical r E, Represents x w.val := by
  obtain ⟨a,ms,t,da,dm,dt,model⟩ := ChainAssembledTrace.arbitrary_local_tuple_trace r E
    x.initial.val x.tail.val (middleWords x) hE x.initial.property
    (fun j hj => by simpa [middleWords,hj] using (x.middles ⟨j,hj⟩).property) x.tail.property
  exact ⟨⟨a ++ assemble ms r ++ t,model⟩,a,ms,t,da,dm,dt,rfl⟩

theorem tuple_unique {r : Nat} (x y : LocalTuple r) (w : List Event)
    (hx : Represents x w) (hy : Represents y w) : x=y := by
  obtain ⟨a,xs,z,da,dx,dz,ex⟩ := hx
  obtain ⟨b,ys,t,db,dy,dt,ey⟩ := hy
  have h := ChainTupleInjectivity.local_tuple_unique r x.initial.val y.initial.val x.tail.val y.tail.val
    (middleWords x) (middleWords y) a b z t xs ys x.initial.property y.initial.property
    (fun j hj => by simpa [middleWords,hj] using (x.middles ⟨j,hj⟩).property)
    (fun j hj => by simpa [middleWords,hj] using (y.middles ⟨j,hj⟩).property)
    da db dx dy dz dt (ex.symm.trans ey)
  have hi : x.initial=y.initial := Subtype.ext h.1
  have ht : x.tail=y.tail := Subtype.ext h.2.2
  have hm : x.middles=y.middles := by
    funext j
    apply Subtype.ext
    simpa [middleWords,j.isLt] using h.2.1 j.val j.isLt
  cases x
  cases y
  simp_all

theorem assemble_congr (xs ys : Nat → List Event) (r : Nat)
    (h : ∀ j, j<r → xs j=ys j) : assemble xs r=assemble ys r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [assemble, ih (fun j hj => h j (by omega)),h r (by omega)]

theorem word_unique {r : Nat} (x : LocalTuple r) (u v : List Event)
    (hu : Represents x u) (hv : Represents x v) : u=v := by
  obtain ⟨a,xs,z,da,dx,dz,ex⟩ := hu
  obtain ⟨b,ys,t,db,dy,dt,ey⟩ := hv
  have ab : a=b := Option.some.inj (da.symm.trans db)
  have zt : z=t := Option.some.inj (dz.symm.trans dt)
  have ms := assemble_congr xs ys r (fun j hj => Option.some.inj ((dx j hj).symm.trans (dy j hj)))
  rw [ab,zt,ms] at ex
  exact ex.trans ey.symm

noncomputable def toPhysical {r : Nat} (E : List Nat)
    (hE : ∀ v, v∈E ↔ IsErasure (r+1) v) (x : LocalTuple r) : Physical r E :=
  Classical.choose (physical_exists E hE x)
noncomputable def toLocal {r : Nat} {E : List Nat} (w : Physical r E) : LocalTuple r :=
  Classical.choose (tuple_exists w)

theorem toPhysical_spec {r : Nat} (E : List Nat)
    (hE : ∀ v, v∈E ↔ IsErasure (r+1) v) (x : LocalTuple r) :
    Represents x (toPhysical E hE x).val := Classical.choose_spec (physical_exists E hE x)
theorem toLocal_spec {r : Nat} {E : List Nat} (w : Physical r E) :
    Represents (toLocal w) w.val := Classical.choose_spec (tuple_exists w)

theorem local_roundtrip {r : Nat} (E : List Nat)
    (hE : ∀ v, v∈E ↔ IsErasure (r+1) v) (x : LocalTuple r) :
    toLocal (toPhysical E hE x)=x :=
  tuple_unique _ _ _ (toLocal_spec _) (toPhysical_spec E hE x)

theorem physical_roundtrip {r : Nat} (E : List Nat)
    (hE : ∀ v, v∈E ↔ IsErasure (r+1) v) (w : Physical r E) :
    toPhysical E hE (toLocal w)=w := by
  apply Subtype.ext
  exact word_unique _ _ _ (toPhysical_spec E hE (toLocal w)) (toLocal_spec w)

#print axioms tuple_exists
#print axioms physical_exists
#print axioms tuple_unique
#print axioms word_unique
#print axioms local_roundtrip
#print axioms physical_roundtrip
end ChainWholeBijection
