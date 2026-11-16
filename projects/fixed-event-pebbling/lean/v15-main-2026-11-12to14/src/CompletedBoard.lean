import BoardTransport
import EnumerationCorrectness
namespace ChainCompletedBoard
open LocalCertificate ChainTrace
def placementAt (v : Nat) (e : Event) : Bool := e.place && e.vertex==v
def removalAt (v : Nat) (e : Event) : Bool := !e.place && e.vertex==v
theorem step_balance (E board after : List Nat) (e : Event) (v : Nat)
 (hs : step true E board e=some after) :
 after.count v + (if removalAt v e then 1 else 0) = board.count v + (if placementAt v e then 1 else 0) := by
 cases hp : e.place with
 | true =>
  have ha := (placement_step E board after e hp).mp hs
  rw [ha.2.2.2]
  by_cases hv : e.vertex=v
  · simp [placementAt,removalAt,hp,hv]
  · simp [placementAt,removalAt,hp,hv,List.count_cons_of_ne hv]
 | false =>
  have ha := removal_step_after E board after e hp hs
  rw [ha]
  by_cases hv : e.vertex=v
  · have hm := removal_requires_present E board after e hp hs
    have hc : 0<board.count v := List.count_pos_iff.mpr (by simpa [hv] using hm)
    simp [placementAt,removalAt,hp,hv]
    omega
  · simp [placementAt,removalAt,hp,hv,List.count_erase_of_ne (Ne.symm hv)]
theorem run_balance (E board after : List Nat) (es : List Event) (v : Nat)
 (hr : run E board es=some after) :
 after.count v + es.countP (removalAt v) = board.count v + es.countP (placementAt v) := by
 induction es generalizing board with
 | nil => simp [run] at hr; subst after; simp
 | cons e es ih =>
  cases hs : step true E board e with
  | none => simp [run,hs] at hr
  | some mid =>
   have ht : run E mid es=some after := by simpa [run,hs] using hr
   have hb := step_balance E board mid e v hs
   have hi := ih mid ht
   simp only [List.countP_cons]
   omega
theorem perm_runs_same_counts (E board a b : List Nat) (xs ys : List Event)
 (hp : xs.Perm ys) (hx : run E board xs=some a) (hy : run E board ys=some b) :
 ∀v,a.count v=b.count v := by
 intro v
 have h1 := run_balance E board a xs v hx
 have h2 := run_balance E board b ys v hy
 have h3 := hp.countP_eq (removalAt v)
 have h4 := hp.countP_eq (placementAt v)
 omega
theorem perm_runs_same_board (E board a b : List Nat) (xs ys : List Event)
 (hp : xs.Perm ys) (hx : run E board xs=some a) (hy : run E board ys=some b) : a.Perm b := by
 apply List.perm_iff_count.mpr
 exact perm_runs_same_counts E board a b xs ys hp hx hy
theorem decode_as_map (table : List Event) (ids : List Nat) (raw : List Event)
 (hd : decodeTrace table ids=some raw) : raw=ids.map (fun i => table.getD i ⟨false,0⟩) := by
 induction ids generalizing raw with
 | nil => simpa [decodeTrace] using hd.symm
 | cons i ids ih =>
  cases he : table[i]? with
  | none => simp [decodeTrace,he] at hd
  | some e =>
   cases ht : decodeTrace table ids with
   | none => simp [decodeTrace,he,ht] at hd
   | some rest =>
    have hr : raw=e::rest := by simpa [decodeTrace,he,ht] using hd.symm
    rw [hr,ih rest ht]
    simp [List.getD,he]
theorem same_completed_board (table : List Event) (E initial a b p q : List Nat)
 (x y : List Event) (np : p.Nodup) (nq : q.Nodup)
 (same : ∀i,i∈p ↔ i∈q) (dx : decodeTrace table p=some x) (dy : decodeTrace table q=some y)
 (hx : run E initial x=some a) (hy : run E initial y=some b) : a.Perm b := by
 have hp := BoardTransport.nodup_membership_perm p q np nq same
 have hr : x.Perm y := by
  rw [decode_as_map table p x dx,decode_as_map table q y dy]
  exact hp.map _
 exact perm_runs_same_board E initial a b x y hr hx hy
def Completes (E board final : List Nat) (suffix : List Event) : Prop :=
 ∃after,run E board suffix=some after ∧ after.Perm final
theorem board_perm_residual (E a b final : List Nat) (hp : a.Perm b) (suffix : List Event) :
 Completes E a final suffix ↔ Completes E b final suffix := by
 constructor
 · rintro ⟨after,hr,hf⟩
   obtain ⟨after',hr',ha⟩ := BoardTransport.run_perm_transport E a b after suffix hp hr
   exact ⟨after',hr',ha.symm.trans hf⟩
 · rintro ⟨after,hr,hf⟩
   obtain ⟨after',hr',ha⟩ := BoardTransport.run_perm_transport E b a after suffix hp.symm hr
   exact ⟨after',hr',ha.symm.trans hf⟩
theorem same_completed_physical_residual (table : List Event) (E initial a b p q final : List Nat)
 (x y : List Event) (np : p.Nodup) (nq : q.Nodup)
 (same : ∀i,i∈p ↔ i∈q) (dx : decodeTrace table p=some x) (dy : decodeTrace table q=some y)
 (hx : run E initial x=some a) (hy : run E initial y=some b) (suffix : List Event) :
 Completes E a final suffix ↔ Completes E b final suffix :=
 board_perm_residual E a b final (same_completed_board table E initial a b p q x y np nq same dx dy hx hy) suffix
#print axioms same_completed_board
#print axioms board_perm_residual
#print axioms same_completed_physical_residual
#print axioms step_balance
#print axioms run_balance
#print axioms perm_runs_same_board
end ChainCompletedBoard
