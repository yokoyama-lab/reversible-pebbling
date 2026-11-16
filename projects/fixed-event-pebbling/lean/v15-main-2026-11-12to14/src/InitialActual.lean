import PrefixFormula
import InitialSegment
import BoardTransport
import EventEncoding
import ShiftedMiddle
namespace FamilyCut
open LocalCertificate ChainTrace ChainEventEncoding ChainFamilyArithmetic

theorem initial_table_nodup : ChainInitialSegment.events.Nodup := by decide

theorem initial_table_counts (v : Nat) (hv : 0 < v) :
    ChainInitialSegment.events.countP (P v) = prefixPCount 5 v ∧
    ChainInitialSegment.events.countP (R v) = prefixRCount 5 v := by
  by_cases hi : v ≤ 11
  · have hc : v=1 ∨ v=2 ∨ v=3 ∨ v=4 ∨ v=5 ∨ v=6 ∨ v=7 ∨ v=8 ∨ v=9 ∨ v=10 ∨ v=11 := by omega
    rcases hc with h|h|h|h|h|h|h|h|h|h|h <;> subst v <;> decide
  · have he : ∀ e ∈ ChainInitialSegment.events, e.vertex ≠ v := by
      have hb : ∀ e ∈ ChainInitialSegment.events, e.vertex ≤ 11 := by decide
      intro e hm; have := hb e hm; omega
    have pc : ChainInitialSegment.events.countP (P v) = 0 := by
      apply List.countP_eq_zero.mpr
      intro e hm; simp [P,RemovalOrder.isPlacement,he e hm]
    have rc : ChainInitialSegment.events.countP (R v) = 0 := by
      apply List.countP_eq_zero.mpr
      intro e hm; simp [R,ChainUniqueLifetime.isRemoval,he e hm]
    simp [pc,rc,prefixPCount,prefixRCount,show ¬v<5 by omega,hi,
      show v≠6 by omega,show v≠8 by omega]

theorem initial_prefix_perm (k : Nat) (erasures : List Nat)
    (pre post : List Event) (t : Event) (hk : 0 < k)
    (htp : t.place = true) (htv : t.vertex = 11)
    (model : Trace k erasures (pre ++ t :: post)) :
    (pre ++ [t]).Perm ChainInitialSegment.events := by
  have sig := all_block_cut_signature k 0 5 erasures pre post t hk rfl htp htv model
  have valid (v : Nat) (hv : 0 < v) (hn : v ≤ 5+6*k) :
      (pre ++ [t]).countP (P v) = ChainInitialSegment.events.countP (P v) ∧
      (pre ++ [t]).countP (R v) = ChainInitialSegment.events.countP (R v) := by
    have a := block_prefix_closed_counts k 0 5 erasures pre post t hk rfl htp htv model v hv hn
    have b := initial_table_counts v hv
    change (pre ++ [t]).countP (P v) = prefixPCount 5 v ∧
      (pre ++ [t]).countP (R v) = prefixRCount 5 v at a
    exact ⟨a.1.trans b.1.symm,a.2.trans b.2.symm⟩
  have prebound : ∀ e ∈ pre ++ [t], 0 < e.vertex ∧ e.vertex ≤ 5+6*k := by
    intro e he
    apply model.bounded e
    rcases List.mem_append.mp he with hp | ht
    · exact List.mem_append_left _ hp
    · have : e=t := by simpa using ht
      subst e
      simp
  have tablebound : ∀ e ∈ ChainInitialSegment.events, 0 < e.vertex ∧ e.vertex ≤ 5+6*k := by
    have h : ∀ e ∈ ChainInitialSegment.events, 0 < e.vertex ∧ e.vertex ≤ 11 := by decide
    intro e he; have := h e he; constructor <;> omega
  have zero (es : List Event) (hb : ∀ e ∈ es, 0 < e.vertex ∧ e.vertex ≤ 5+6*k)
      (v : Nat) (hv : ¬(0<v ∧ v≤5+6*k)) :
      es.countP (P v)=0 ∧ es.countP (R v)=0 := by
    have ne : ∀ e ∈ es, e.vertex ≠ v := by intro e he hh; have := hb e he; omega
    constructor
    · apply List.countP_eq_zero.mpr
      intro e he; simp [P,RemovalOrder.isPlacement,ne e he]
    · apply List.countP_eq_zero.mpr
      intro e he; simp [R,ChainUniqueLifetime.isRemoval,ne e he]
  apply SegmentDifference.perm_of_event_counts
  · intro v
    by_cases h : 0<v ∧ v≤5+6*k
    · exact (valid v h.1 h.2).1
    · rw [(zero _ prebound v h).1,(zero _ tablebound v h).1]
  · intro v
    by_cases h : 0<v ∧ v≤5+6*k
    · exact (valid v h.1 h.2).2
    · rw [(zero _ prebound v h).2,(zero _ tablebound v h).2]

theorem initial_erasure_agreement (k : Nat) (erasures : List Nat) (hk : 0<k)
    (hm : ∀ v, v∈erasures ↔ IsErasure k v) :
    ∀ e ∈ ChainInitialSegment.events, e.place=false → (e.vertex∈erasures ↔ e.vertex∈[5]) := by
  have hb : ∀ e ∈ ChainInitialSegment.events, e.place=false →
      0<e.vertex ∧ e.vertex<11 := by decide
  intro e he hp
  have bounds := hb e he hp
  rw [hm]
  simp only [List.mem_cons,List.not_mem_nil,or_false]
  constructor
  · rintro ⟨i,hi,hh⟩
    omega
  · intro h
    exact ⟨0,hk,by omega⟩

theorem initial_actual_legal (k : Nat) (erasures : List Nat)
    (pre post : List Event) (t : Event) (hk : 0 < k)
    (htp : t.place = true) (htv : t.vertex = 11)
    (model : Trace k erasures (pre ++ t :: post)) :
    legal ChainInitialSegment.events [] ChainInitialSegment.final [5]
      (encode ChainInitialSegment.events (pre ++ [t])) := by
  obtain ⟨⟨before,cut,hb,hc,hm⟩,_⟩ :=
    all_block_cut_signature k 0 5 erasures pre post t hk rfl htp htv model
  have runp : run erasures [] (pre ++ [t]) = some cut := by
    simp [run_append,hb,run,hc]
  have nd := ChainLifetime.run_nodup erasures [] cut (pre ++ [t]) (by simp) runp
  have perm : cut.Perm ChainInitialSegment.final :=
    BoardTransport.nodup_membership_perm _ _ nd (by decide) hm
  have hsame : sameBoard cut ChainInitialSegment.final = true := by
    unfold sameBoard
    simp only [perm.length_eq,beq_self_eq_true,Bool.true_and]
    apply List.all_eq_true.mpr
    intro v hv
    exact List.contains_iff_mem.mpr (perm.mem_iff.mp hv)
  have hl : legal ChainInitialSegment.events [] ChainInitialSegment.final erasures
      (encode ChainInitialSegment.events (pre ++ [t])) :=
    (legal_encode_iff_run _ _ _ _ _ initial_table_nodup
      (initial_prefix_perm k erasures pre post t hk htp htv model)).mpr ⟨cut,runp,hsame⟩
  exact (ShiftedMiddle.legal_erasure_congr _ _ _ erasures [5] _
    (initial_erasure_agreement k erasures hk model.erasure_sites)).mp hl

theorem initial_actual_good (k : Nat) (erasures : List Nat)
    (pre post : List Event) (t : Event) (hk : 0 < k)
    (htp : t.place = true) (htv : t.vertex = 11)
    (model : Trace k erasures (pre ++ t :: post)) :
    ChainInitialSegment.Good (encode ChainInitialSegment.events (pre ++ [t])) :=
  ChainInitialSegment.all_legal_factor _
    (initial_actual_legal k erasures pre post t hk htp htv model)

theorem initial_actual_exists (k : Nat) (erasures : List Nat) (word : List Event)
    (hk : 0 < k) (model : Trace k erasures word) :
    ∃ pre t post, word = pre ++ t :: post ∧ t.place=true ∧ t.vertex=11 ∧
      ChainInitialSegment.Good (encode ChainInitialSegment.events (pre ++ [t])) := by
  obtain ⟨pre,t,post,hw,hp,hv⟩ := block_placement_exists k 0 erasures word hk model
  refine ⟨pre,t,post,hw,hp,hv,?_⟩
  apply initial_actual_good k erasures pre post t hk hp hv
  simpa only [← hw] using model

#print axioms initial_table_nodup
#print axioms initial_table_counts
#print axioms initial_prefix_perm
#print axioms initial_erasure_agreement
#print axioms initial_actual_legal
#print axioms initial_actual_good
#print axioms initial_actual_exists
end FamilyCut
