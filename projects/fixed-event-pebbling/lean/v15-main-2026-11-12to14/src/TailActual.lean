import PrefixFormula
import SegmentDifference
import MiddleDifference
import TailSegment
import ShiftedMiddle
import BoardTransport
namespace TailActual
open LocalCertificate ChainTrace ChainFamilyArithmetic FamilyCut ReplayBridge

def events (s : Nat) : List Event :=
 [⟨false,s+5⟩,⟨true,s+3⟩,⟨false,s+4⟩,⟨false,s⟩,
  ⟨true,s+1⟩,⟨false,s+1⟩,⟨false,s+2⟩,⟨false,s+3⟩]

theorem count_difference (j v : Nat) (hv : 0 < v) (hb : v ≤ 5+6*j+6) :
 placementCount v = MiddleDifference.prefixP (5+6*j) v + (events (5+6*j)).countP (P v) ∧
 (if v < 5+6*j+6 then placementCount v else 0) =
 MiddleDifference.prefixR (5+6*j) v + (events (5+6*j)).countP (R v) := by
 let s := 5+6*j
 change placementCount v = MiddleDifference.prefixP s v + (events s).countP (P v) ∧
   (if v<s+6 then placementCount v else 0) = MiddleDifference.prefixR s v + (events s).countP (R v)
 by_cases hl : v < s
 · have hn : ∀ d, d ≤ 6 → s+d ≠ v := by intro d hd; omega
   simp [MiddleDifference.prefixP,MiddleDifference.prefixR,hl,
     show v<s+6 by omega,events,P,R,RemovalOrder.isPlacement,
     ChainUniqueLifetime.isRemoval,hn,show s≠v by omega]
 · have cases : v=s ∨ v=s+1 ∨ v=s+2 ∨ v=s+3 ∨ v=s+4 ∨ v=s+5 ∨ v=s+6 := by omega
   rcases cases with h|h|h|h|h|h|h <;> subst v <;>
     simp [MiddleDifference.prefixP,MiddleDifference.prefixR,events,P,R,
       RemovalOrder.isPlacement,ChainUniqueLifetime.isRemoval,s,placementCount,Nat.add_mod] <;>
       (repeat (first | omega | split))

theorem tail_perm (j : Nat) (erasures : List Nat) (pre post : List Event) (t : Event)
 (htp : t.place = true) (htv : t.vertex = 5+6*j+6)
 (model : Trace (j+1) erasures (pre ++ t :: post)) :
 post.Perm (events (5+6*j)) := by
 let n := 5+6*j+6
 have neqn : n = 5+6*(j+1) := by omega
 have wholeR (v : Nat) (hv : 0 < v) (hb : v ≤ n) :
   (pre ++ t :: post).countP (R v) = if v < n then placementCount v else 0 := by
   by_cases h : v < n
   · rw [if_pos h]; exact family_total_removals (j+1) erasures _ model v hv (by omega)
   · have he : v=n := by omega
     subst v
     rw [if_neg (by omega)]
     have pc : (pre ++ t :: post).countP (P n) = 1 := by
       rw [model.counts n (by omega) (by omega)]
       exact (block_placement_counts j).2.2.2.2.2.2
     exact ChainCutEventCounts.present_single_placement_no_removal erasures [] [5+6*(j+1)] _ n
       (by simp) (by simp) (by simp [neqn]) pc model.legal
 have counts (v : Nat) (hv : 0 < v) (hb : v ≤ n) :
   post.countP (P v) = (events (5+6*j)).countP (P v) ∧
   post.countP (R v) = (events (5+6*j)).countP (R v) := by
   have a := block_prefix_closed_counts (j+1) j (5+6*j) erasures pre post t
     (by omega) rfl htp htv model v hv (by omega)
   have d := count_difference j v hv hb
   change placementCount v = MiddleDifference.prefixP (5+6*j) v + (events (5+6*j)).countP (P v) ∧
     (if v<n then placementCount v else 0) = MiddleDifference.prefixR (5+6*j) v + (events (5+6*j)).countP (R v) at d
   have p := model.counts v hv (by omega)
   have r := wholeR v hv hb
   change (pre ++ [t]).countP (P v) = MiddleDifference.prefixP (5+6*j) v ∧
     (pre ++ [t]).countP (R v) = MiddleDifference.prefixR (5+6*j) v at a
   have ew : pre ++ t :: post = (pre ++ [t]) ++ post := by simp
   rw [ew,List.countP_append] at p r
   constructor <;> omega
 have pb : ∀ e ∈ post, 0 < e.vertex ∧ e.vertex ≤ n := by
   intro e he
   have h := model.bounded e (by simp [he])
   omega
 have eb : ∀ e ∈ events (5+6*j), 0 < e.vertex ∧ e.vertex ≤ n := by
   intro e he
   simp only [events,List.mem_cons,List.not_mem_nil,or_false] at he
   rcases he with h|h|h|h|h|h|h|h <;> subst e <;> dsimp <;> constructor <;> omega
 have zero (xs : List Event) (b : ∀ e ∈ xs, 0 < e.vertex ∧ e.vertex ≤ n)
   (v : Nat) (hi : ¬(0<v ∧ v≤n)) : xs.countP (P v)=0 ∧ xs.countP (R v)=0 := by
   have ne : ∀ e ∈ xs, e.vertex ≠ v := by intro e he hh; have := b e he; omega
   constructor
   · apply List.countP_eq_zero.mpr; intro e he; simp [P,RemovalOrder.isPlacement,ne e he]
   · apply List.countP_eq_zero.mpr; intro e he; simp [R,ChainUniqueLifetime.isRemoval,ne e he]
 apply SegmentDifference.perm_of_event_counts
 · intro v
   by_cases h : 0<v ∧ v≤n
   · exact (counts v h.1 h.2).1
   · rw [(zero post pb v h).1,(zero _ eb v h).1]
 · intro v
   by_cases h : 0<v ∧ v≤n
   · exact (counts v h.1 h.2).2
   · rw [(zero post pb v h).2,(zero _ eb v h).2]
#print axioms count_difference
#print axioms tail_perm

theorem table_shift (j : Nat) : events (5+6*j) = shiftEvents (6*j) ChainTailSegment.events := by
 simp [events,shiftEvents,shiftEvent,ChainTailSegment.events,
   Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] <;> omega

theorem tail_legal (j : Nat) (erasures : List Nat) (pre post : List Event) (t : Event)
 (htp : t.place = true) (htv : t.vertex = 5+6*j+6)
 (model : Trace (j+1) erasures (pre ++ t :: post)) :
 legal (events (5+6*j)) (shiftBoard (6*j) ChainTailSegment.initial)
   (shiftBoard (6*j) ChainTailSegment.final) erasures
   (ChainEventEncoding.encode (events (5+6*j)) post) := by
 obtain ⟨⟨b,c,hb,hc,memc⟩,_⟩ := all_block_cut_signature (j+1) j (5+6*j) erasures pre post t
   (by omega) rfl htp htv model
 have run1 : run erasures [] (pre ++ [t]) = some c := by simp [run_append,hb,run,hc]
 have hr := model.legal
 have ew : pre ++ t :: post = (pre ++ [t]) ++ post := by simp
 rw [ew,run_append,run1] at hr
 have cn := ChainLifetime.run_nodup erasures [] c (pre ++ [t]) (by simp) run1
 have cp : c.Perm (shiftBoard (6*j) ChainTailSegment.initial) := by
   have eqb : shiftBoard (6*j) ChainTailSegment.initial = [5+6*j,5+6*j+2,5+6*j+4,5+6*j+5,5+6*j+6] := by
     simp [shiftBoard,ChainTailSegment.initial,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] <;> omega
   rw [eqb]
   apply BoardTransport.nodup_membership_perm c _ cn
   · simp [List.nodup_cons]
   · exact memc
 obtain ⟨after,ha,hp⟩ := BoardTransport.run_perm_transport erasures c
   (shiftBoard (6*j) ChainTailSegment.initial) [5+6*(j+1)] post cp hr
 have ef : shiftBoard (6*j) ChainTailSegment.final = [5+6*(j+1)] := by
   simp [shiftBoard,ChainTailSegment.final]; omega
 have nd : (events (5+6*j)).Nodup := by simp [events,List.nodup_cons]
 apply (ChainEventEncoding.legal_encode_iff_run _ post _ _ erasures nd
   (tail_perm j erasures pre post t htp htv model)).mpr
 refine ⟨after,ha,?_⟩
 rw [ef]
 have ap := hp.symm
 unfold sameBoard
 simp only [ap.length_eq,beq_self_eq_true,Bool.true_and]
 apply List.all_eq_true.mpr
 intro v hv
 exact List.contains_iff_mem.mpr (ap.mem_iff.mp hv)

theorem tail_two (j : Nat) (erasures : List Nat) (pre post : List Event) (t : Event)
 (htp : t.place = true) (htv : t.vertex = 5+6*j+6)
 (model : Trace (j+1) erasures (pre ++ t :: post)) :
 let w := ChainEventEncoding.encode (events (5+6*j)) post
 w = ChainTailSegment.wordA ∨ w = ChainTailSegment.wordB := by
 let w := ChainEventEncoding.encode (events (5+6*j)) post
 have hl := tail_legal j erasures pre post t htp htv model
 have he : ∀ e ∈ events (5+6*j), e.place = false →
   (e.vertex ∈ erasures ↔ e.vertex ∈ shiftBoard (6*j) [5]) := by
   have red (v : Nat) (lo : 5+6*j ≤ v) (hi : v < 5+6*j+6) :
     v ∈ erasures ↔ v ∈ shiftBoard (6*j) [5] := by
     rw [model.erasure_sites]
     simp only [shiftBoard,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false]
     constructor
     · rintro ⟨i,hi,he⟩; omega
     · intro hv; exact ⟨j,by omega,by omega⟩
   intro e hm hh
   simp only [events,List.mem_cons,List.not_mem_nil,or_false] at hm
   rcases hm with h|h|h|h|h|h|h|h <;> subst e <;> simp only at hh ⊢
   all_goals try contradiction
   all_goals apply red <;> omega
 have norm := (ShiftedMiddle.legal_erasure_congr _ _ _ erasures (shiftBoard (6*j) [5]) w he).mp hl
 rw [table_shift j] at norm
 have base := (legal_shift_iff (6*j) ChainTailSegment.events ChainTailSegment.initial
   ChainTailSegment.final [5] w (by decide)).mp norm
 exact (ChainTailSegment.legal_iff_two w).mp base
#print axioms table_shift
#print axioms tail_legal
#print axioms tail_two
theorem tail_exists (j : Nat) (erasures : List Nat) (word : List Event)
 (model : Trace (j+1) erasures word) :
 ∃ pre t post, word = pre ++ t :: post ∧ t.place = true ∧ t.vertex = 5+6*j+6 ∧
   (ChainEventEncoding.encode (events (5+6*j)) post = ChainTailSegment.wordA ∨
    ChainEventEncoding.encode (events (5+6*j)) post = ChainTailSegment.wordB) := by
 obtain ⟨pre,t,post,hw,hp,hv⟩ := block_placement_exists (j+1) j erasures word (by omega) model
 have m : Trace (j+1) erasures (pre ++ t :: post) := by rw [← hw]; exact model
 exact ⟨pre,t,post,hw,hp,hv,tail_two j erasures pre post t hp hv m⟩
#print axioms tail_exists
end TailActual
