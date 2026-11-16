import EndpointLocalRun
import FactorUnique
import DecodedPerm
import GlobalReassembly
namespace ChainTupleInjectivity
open LocalCertificate ChainTrace ChainGlobalReassembly

theorem decode_injective (table : List Event) (nd : table.Nodup)
    (u v : List Nat) (es : List Event)
    (hu : decodeTrace table u = some es) (hv : decodeTrace table v = some es) : u=v := by
  induction u generalizing v es with
  | nil =>
    cases v with
    | nil => rfl
    | cons j vs =>
      simp only [decodeTrace,Option.some.injEq] at hu
      subst es
      cases hj : table[j]? <;> simp [decodeTrace,hj] at hv
      cases ht : decodeTrace table vs <;> simp [ht] at hv
  | cons i us ih =>
    cases hi : table[i]? with
    | none => simp [decodeTrace,hi] at hu
    | some e =>
      cases ht : decodeTrace table us with
      | none => simp [decodeTrace,hi,ht] at hu
      | some rest =>
        have he : es=e::rest := by simpa [decodeTrace,hi,ht] using hu.symm
        subst es
        cases v with
        | nil => simp [decodeTrace] at hv
        | cons j vs =>
          cases hj : table[j]? with
          | none => simp [decodeTrace,hj] at hv
          | some f =>
            cases hs : decodeTrace table vs with
            | none => simp [decodeTrace,hj,hs] at hv
            | some tail =>
              have eqs : f=e ∧ tail=rest := by simpa [decodeTrace,hj,hs] using hv
              have ilt : i < table.length := by
                by_cases hh : i < table.length
                · exact hh
                · have hn : table[i]? = none := List.getElem?_eq_none (by omega)
                  rw [hn] at hi
                  contradiction
              have ij : i=j := (List.getElem?_inj ilt nd).mp (hi.trans (by simpa [eqs.1] using hj.symm))
              have uv := ih vs rest ht (by simpa [eqs.2] using hs)
              simp [ij,uv]

theorem assemble_length (words : Nat → List Event) (r size : Nat)
    (h : ∀ j, j<r → (words j).length=size) : (assemble words r).length = r*size := by
  induction r with
  | zero => simp [assemble]
  | succ r ih =>
    simp only [assemble,List.length_append,ih (fun j hj => h j (by omega)),h r (by omega)]
    simp [Nat.add_mul]

theorem assemble_injective (xs ys : Nat → List Event) (r size : Nat)
    (hx : ∀ j, j<r → (xs j).length=size) (hy : ∀ j, j<r → (ys j).length=size)
    (he : assemble xs r = assemble ys r) : ∀ j, j<r → xs j=ys j := by
  induction r with
  | zero => omega
  | succ r ih =>
    have split := List.append_inj' he ((hx r (by omega)).trans (hy r (by omega)).symm)
    intro j hj
    by_cases h : j<r
    · exact ih (fun j hj => hx j (by omega)) (fun j hj => hy j (by omega)) split.1 j h
    · have : j=r := by omega
      simpa [this] using split.2

theorem physical_factors_unique (a b z t : List Event) (xs ys : Nat → List Event) (r : Nat)
    (ha : a.length=17) (hb : b.length=17)
    (hx : ∀ j, j<r → (xs j).length=16) (hy : ∀ j, j<r → (ys j).length=16)
    (he : a ++ assemble xs r ++ z = b ++ assemble ys r ++ t) :
    a=b ∧ (∀ j, j<r → xs j=ys j) ∧ z=t := by
  have hs := List.append_inj (by simpa [List.append_assoc] using he) (ha.trans hb.symm)
  have hl := (assemble_length xs r 16 hx).trans (assemble_length ys r 16 hy).symm
  have hm := List.append_inj hs.2 hl
  exact ⟨hs.1,assemble_injective xs ys r 16 hx hy hm.1,hm.2⟩

#print axioms decode_injective
#print axioms assemble_length
#print axioms assemble_injective
#print axioms physical_factors_unique
theorem local_tuple_unique (r : Nat) (iu iv tu tv : List Nat) (mu mv : Nat → List Nat)
    (a b z t : List Event) (xs ys : Nat → List Event)
    (hi : I.Legal iu) (hj : I.Legal iv)
    (hm : ∀ j, j<r → M.Legal (mu j)) (hn : ∀ j, j<r → M.Legal (mv j))
    (da : decodeTrace ChainInitialSegment.events (ChainInitialConverse.liftWord iu) = some a)
    (db : decodeTrace ChainInitialSegment.events (ChainInitialConverse.liftWord iv) = some b)
    (dx : ∀ j, j<r → decodeTrace (MiddleDifference.events (5+6*j))
      (ChainMiddleConverse.liftWord (mu j)) = some (xs j))
    (dy : ∀ j, j<r → decodeTrace (MiddleDifference.events (5+6*j))
      (ChainMiddleConverse.liftWord (mv j)) = some (ys j))
    (dz : decodeTrace (ReplayBridge.shiftEvents (6*r) ChainTailSegment.events) tu = some z)
    (dt : decodeTrace (ReplayBridge.shiftEvents (6*r) ChainTailSegment.events) tv = some t)
    (he : a ++ assemble xs r ++ z = b ++ assemble ys r ++ t) :
    iu=iv ∧ (∀ j, j<r → mu j=mv j) ∧ tu=tv := by
  have la : a.length=17 := by
    rw [ChainDecodedPerm.decode_map _ _ _ da, List.length_map]
    have h : iu.length=10 := hi.1.1
    simp [ChainInitialConverse.liftWord,h]
  have lb : b.length=17 := by
    rw [ChainDecodedPerm.decode_map _ _ _ db, List.length_map]
    have h : iv.length=10 := hj.1.1
    simp [ChainInitialConverse.liftWord,h]
  have lx : ∀ j, j<r → (xs j).length=16 := by
    intro j hj
    rw [ChainDecodedPerm.decode_map _ _ _ (dx j hj), List.length_map]
    have h : (mu j).length=12 := (hm j hj).1.1
    simp [ChainMiddleConverse.liftWord,h]
  have ly : ∀ j, j<r → (ys j).length=16 := by
    intro j hj
    rw [ChainDecodedPerm.decode_map _ _ _ (dy j hj), List.length_map]
    have h : (mv j).length=12 := (hn j hj).1.1
    simp [ChainMiddleConverse.liftWord,h]
  obtain ⟨ab,xy,zt⟩ := physical_factors_unique a b z t xs ys r la lb lx ly he
  have ndi : ChainInitialSegment.events.Nodup := by decide
  have ndm : ∀ j, (MiddleDifference.events (5+6*j)).Nodup := by
    intro j
    simp [MiddleDifference.events,List.nodup_cons]
  have ndt : (ReplayBridge.shiftEvents (6*r) ChainTailSegment.events).Nodup := by
    simp [ReplayBridge.shiftEvents,ReplayBridge.shiftEvent,ChainTailSegment.events,List.nodup_cons]
  refine ⟨ChainFactorUnique.initial_lift_injective iu iv
    (decode_injective _ ndi _ _ a da (by simpa [ab] using db)), ?_, ?_⟩
  · intro j hj
    exact ChainFactorUnique.middle_lift_injective (mu j) (mv j)
      (decode_injective _ (ndm j) _ _ (xs j) (dx j hj) (by simpa [xy j hj] using dy j hj))
  · exact decode_injective _ ndt _ _ z dz (by simpa [zt] using dt)

#print axioms local_tuple_unique
end ChainTupleInjectivity
