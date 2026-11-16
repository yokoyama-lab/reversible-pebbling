import SignatureCardinality
namespace SignatureCover
open ErasureCover SlotConcat ChainRecursiveBlockedCover

def finiteRelation (bs) (c : Fin (6*count bs)) := relation bs (fullDecode bs c)
theorem finite_upper (bs : List Bool) :
 (∀c,StrictOrder (finiteRelation bs c) ∧ Sound (semantics (allSlots bs.length)) (Legal bs) (finiteRelation bs c)) ∧
 (∀w,Legal bs w→∃c,Extends (semantics (allSlots bs.length)) (finiteRelation bs c) w) := by
 refine ⟨fun c=>(upper bs).1 _,?_⟩
 intro w hw
 obtain ⟨c,hc⟩ := (upper bs).2 w hw
 exact ⟨fullEncode bs c,by simpa [finiteRelation,full_decode_encode] using hc⟩

theorem lower (bs : List Bool) (N : Nat) (R : Fin N → Slots bs.length → Slots bs.length → Prop)
 (sound : ∀c,Sound (semantics (allSlots bs.length)) (Legal bs) (R c))
 (cover : ∀w,Legal bs w→∃c,Extends (semantics (allSlots bs.length)) (R c) w) : 6*count bs ≤ N := by
 classical
 let choose := fun i => Classical.choose (cover (witness bs i) (witness_legal bs i))
 have covered := fun i => Classical.choose_spec (cover (witness bs i) (witness_legal bs i))
 have inj := witnessAssignmentInjective (semantics (allSlots bs.length)) (Legal bs)
   (witness bs) R choose sound covered (witness_obstruction bs)
 apply ErasureCardinality.fin_injection_bound (fun i => choose (fullDecode bs i))
 intro i j h
 have hd := inj _ _ h
 have he := congrArg (fullEncode bs) hd
 simpa only [full_encode_decode] using he

theorem count_formula (bs : List Bool) : count bs=12^(bs.count false)*2^(bs.count true) := by
 induction bs with
 | nil => simp [count]
 | cons b bs ih => cases b <;> simp [count,ComponentSlotCover.size,ih,List.count_cons,Nat.pow_succ,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc]

#print axioms finite_upper
#print axioms lower
#print axioms count_formula
end SignatureCover
