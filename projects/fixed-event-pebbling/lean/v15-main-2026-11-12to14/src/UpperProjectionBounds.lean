import TerminalProjection
namespace UpperProjectionBounds
open TerminalProjection LocalCertificate
def high (m : Nat) (b : List Nat) := b.filter (fun v => decide (m<v))
def low (m : Nat) (b : List Nat) := b.filter (fun v => decide (v≤m))
theorem partition_length (m : Nat) (b : List Nat) : (low m b).length+(high m b).length=b.length := by
 induction b with
 | nil => rfl
 | cons x xs ih =>
   by_cases h : x≤m
   · simp [low,high,h,show ¬m<x by omega] at *;omega
   · simp [low,high,h,show m<x by omega] at *;omega
theorem high_capacity {m p b} (hb : b.length≤p) (occupied : ∃x∈b,x≤m) :
 (high m b).length≤p-1 := by
 obtain ⟨x,hx,hxm⟩ := occupied
 have hm : x∈low m b := by simp [low,hx,hxm]
 have hp : 0<(low m b).length := List.length_pos_of_mem hm
 have h := partition_length m b
 omega
def upperPred (m : Nat) (b : List Nat) (v : Nat) := v=m+1 ∨ v-1∈high m b
instance (m b v) : Decidable (upperPred m b v) := inferInstanceAs (Decidable (_ ∨ _))
theorem predecessor_retained {m b v} (hv : m<v) (hp : pred b v) : upperPred m b v := by
 by_cases he : v=m+1
 · exact Or.inl he
 · have h : m<v-1 := by omega
   rcases hp with hp | hp
   · omega
   · exact Or.inr (by simp [high,hp,h])
theorem predecessor_interior {m b v} (hv : m+1<v) : upperPred m b v ↔ pred b v := by
 have hne : v≠m+1 := by omega
 have h1 : v≠1 := by omega
 have h : m<v-1 := by omega
 simp [upperPred,pred,high,hne,h1,h]
def projectedFee (m : Nat) (b : List Nat) (e : Event) : Nat :=
 if e.place then 1 else if upperPred m b e.vertex then 1 else 9
def projectedErasure (m : Nat) (b : List Nat) (e : Event) : Nat :=
 if e.place then 0 else if upperPred m b e.vertex then 0 else 1
theorem projected_fee_le {m b e} (hv : m<e.vertex) : projectedFee m b e≤fee b e := by
 cases hp : e.place with
 | true => simp [projectedFee,fee,hp]
 | false =>
   by_cases h : pred b e.vertex
   · simp [projectedFee,fee,hp,h,predecessor_retained hv h]
   · simp only [projectedFee,fee,hp,Bool.false_eq_true,↓reduceIte,h]
     split <;> omega
theorem projected_erasure_le {m b e} (hv : m<e.vertex) : projectedErasure m b e≤erasure b e := by
 cases hp : e.place with
 | true => simp [projectedErasure,erasure,hp]
 | false =>
   by_cases h : pred b e.vertex
   · simp [projectedErasure,erasure,hp,h,predecessor_retained hv h]
   · simp only [projectedErasure,erasure,hp,Bool.false_eq_true,↓reduceIte,h]
     split <;> omega
#print axioms high_capacity
#print axioms predecessor_retained
#print axioms predecessor_interior
#print axioms projected_fee_le
#print axioms projected_erasure_le
end UpperProjectionBounds
