import RootCleanup
namespace SkeletonUnfill
open SpookyRound BatchUpper FillUpper FringeEmbed RetainRoot

def upper (L U n : Nat) : Config n :=
 ⟨fun v=>decide (v.val=0 ∨ (L≤v.val ∧ v.val<U)),fun v=>decide (U≤v.val)⟩
def remove (L n : Nat) : Action := SpookyReverse.reverse (batch (mask L : Fin n→Bool) (fun _=>false))
@[simp] theorem first_remove (L : Nat) (v : Fin n) :
 firstAt (remove L n) v=if mask L v then .unpebble else .idle := by
 simp [remove,SpookyReverse.first_reverse]; cases mask L v <;> rfl
@[simp] theorem ghost_remove (L : Nat) (v : Fin n) : ghostAt (remove L n) v=false := by simp [remove]

theorem legal (L U n : Nat) (hL : 0<L) (hU : 4*L+3≤U) : Legal HeapPath.pred (upper L U n) (remove L n) := by
 have range : ∀v : Fin n,mask L v=true → L≤v.val∧v.val<2*L+1 := by simp [mask]
 refine ⟨?_,?_,?_,?_,?_,?_⟩
 · intro v; simp only [upper,decide_eq_true_eq]; omega
 · intro v hv; simp only [first_remove] at hv; split at hv <;> contradiction
 · intro v hv
   have hh : mask L v=true := by cases hm : mask L v <;> simp_all
   have hx := range v hh
   simp only [upper,decide_eq_true_eq]; omega
 · intro v hv u hu
   have hh : mask L v=true := by cases hm : mask L v <;> simp_all
   have hx := range v hh
   simp [HeapPath.pred] at hu
   simp only [upper,decide_eq_true_eq]; omega
 · intro v w hne hv hw u hu
   have hv' : mask L v=true := by cases hm : mask L v <;> simp_all
   have hw' : mask L w=true := by cases hm : mask L w <;> simp_all
   exact heap_layer_independent L (mask L) range v w hne hv' hw' u hu
 · intro v hv; simp at hv

theorem removed (L U n : Nat) (hL : 0<L) (hU : 2*L+1≤U) :
 afterRound (upper L U n) (remove L n)=upper (2*L+1) U n := by
 apply SpookyReverse.config_ext <;> intro v <;>
   simp only [afterRound,afterFirst,first_remove,ghost_remove,Bool.false_eq_true,ite_false]
 · by_cases hm : mask L v=true
   · have hx : L≤v.val∧v.val<2*L+1 := by simpa [mask] using hm
     simp [hm,upper,show v.val≠0 by omega,show ¬2*L+1≤v.val by omega]
   · have hx : ¬(L≤v.val∧v.val<2*L+1) := by simpa only [mask,decide_eq_true_eq] using hm
     simp only [hm,ite_false,upper]
     have he : (v.val=0∨(L≤v.val∧v.val<U))↔(v.val=0∨(2*L+1≤v.val∧v.val<U)) := by omega
     simp only [Bool.false_eq_true,ite_false,Bool.not_false,Bool.and_true,he]
 · cases hm : mask L v <;> simp [hm,upper]

theorem work_bound (L n : Nat) : roundWork (remove L n)≤L+1 := by
 have hh := Skeleton.card_interval (mask L : Fin n→Bool) L (2*L+1) (by simp [mask])
 simp only [remove,SpookyReverse.reverse_work,work_batch]
 omega

theorem space_bound (L U n : Nat) (hU : 0<U) : roundSpace (upper L U n) (remove L n)≤U := by
 have hh := Skeleton.card_cap (fun v : Fin n=>(upper L U n).peb v || (afterFirst (upper L U n) (remove L n)).peb v) U (by
   intro v hv
   cases hm : mask L v <;> simp [afterFirst,hm,upper] at hv <;> omega)
 exact hh

theorem step (L U n : Nat) (hL : 0<L) (hU : 4*L+3≤U) :
 ∃t,PaperRuns HeapPath.pred 1 (upper L U n) t ∧ t.state=upper (2*L+1) U n ∧ t.work≤L+1 ∧ t.space≤U := by
 have hl := legal L U n hL hU
 have hs : PaperStep HeapPath.pred (upper L U n) (edge (upper L U n) (remove L n)) :=
   ⟨_,by simp [remove,SpookyReverse.reverse,batch],by simp [remove,SpookyReverse.reverse,batch],hl,rfl⟩
 have hh := PaperRuns.step hs (PaperRuns.zero (afterRound (upper L U n) (remove L n)))
 refine ⟨_,hh,removed L U n hL (by omega),?_,?_⟩
 · simpa [SpookyDP.prepend,edge] using work_bound L n
 · simpa [SpookyDP.prepend,edge] using space_bound L U n (by omega)
#print axioms step


theorem sweep (t H U n : Nat) (hH : 0<H) (hU : 2^(H+t+1)-1≤U) :
 ∃r,PaperRuns HeapPath.pred t (upper (2^H-1) U n) r ∧ r.state=upper (2^(H+t)-1) U n ∧
 r.work≤2^(H+t)-2^H ∧ r.space≤U := by
 induction t generalizing H with
 | zero => exact ⟨⟨upper (2^H-1) U n,0,0⟩,PaperRuns.zero _,by simp,by simp,by simp⟩
 | succ t ih =>
   have hp : 1<2^H := by
     have hh := Nat.pow_le_pow_right (n:=2) (by decide) hH
     simp at hh; omega
   have pl := Nat.pow_le_pow_right (n:=2) (by decide) (show H+2≤H+(t+1)+1 by omega)
   have hl : 4*(2^H-1)+3≤U := by
     simp only [Nat.pow_succ] at pl; omega
   obtain ⟨r,hr,hrs,hrw,hrsp⟩ := step (2^H-1) U n (by omega) hl
   have he : 2*(2^H-1)+1=2^(H+1)-1 := by rw [Nat.pow_succ]; omega
   rw [he] at hrs
   have hu : 2^((H+1)+t+1)-1≤U := by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hU
   obtain ⟨s,hs,hss,hsw,hssp⟩ := ih (H+1) (by omega) hu
   rw [←hrs] at hs
   refine ⟨⟨s.state,r.work+s.work,max r.space s.space⟩,?_,?_,?_,Nat.max_le.mpr ⟨hrsp,hssp⟩⟩
   · have run := runs_append hr hs
     simpa [Nat.add_comm] using run
   · simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hss
   · change r.work+s.work≤_
     have pe := Nat.pow_le_pow_right (n:=2) (by decide) (show H+1≤H+1+t by omega)
     have eq : H+1+t=H+(t+1) := by omega
     rw [eq] at pe hsw
     rw [Nat.pow_succ] at pe hsw
     omega

theorem unfill_skeleton (D n : Nat) (hD : 0<D) :
 ∃t,PaperRuns HeapPath.pred (D-1) (Skeleton.capState (2^(D+1)-1) n) t ∧
 t.state=RootCleanup.held D n ∧ t.work≤2^D-2 ∧ t.space≤2^(D+1)-1 := by
 have hsum : 1+(D-1)=D := by omega
 obtain ⟨t,ht,hs,hw,hsp⟩ := sweep (D-1) 1 (2^(D+1)-1) n (by decide) (by simp [hsum])
 have start : upper (2^1-1) (2^(D+1)-1) n=Skeleton.capState (2^(D+1)-1) n := by
   have hp : 0<2^D := Nat.pow_pos (by decide)
   apply SpookyReverse.config_ext
   · intro v
     have eq : (v.val=0∨(2^1-1≤v.val∧v.val<2^(D+1)-1))↔v.val<2^(D+1)-1 := by
       rw [Nat.pow_succ]; simp; omega
     simp only [upper,Skeleton.capState,eq]
   · intro v; rfl
 rw [start] at ht
 rw [hsum] at hs hw
 exact ⟨t,ht,hs,hw,hsp⟩

#print axioms unfill_skeleton


theorem complete (D h B K : Nat) (hD : 0<D) (hk : 0<K) (hsize : B*K=2^D) :
 ∃t,PaperRuns HeapPath.pred (B*((1+h)+1)+D+(D-1)+B*(2*h+1)) (empty (2^(D+(1+h))-1)) t ∧
 t.state=rootOnly (2^(D+(1+h))-1) ∧ t.work≤3*(2^(D+(1+h))-1) ∧
 t.space≤K*(2^(1+h)-1)+(2^(D+1)-1) := by
 obtain ⟨r,hr,hrs,hrw,hrsp,hrp⟩ := FullPartition.initial_with_boundary D (1+h) B K (by omega) hk hsize
 obtain ⟨s,hs,hss,hsw,hssp⟩ := Skeleton.skeleton D (2^(D+(1+h))-1)
 rw [←hrs] at hs
 obtain ⟨u,hu,hus,huw,husp⟩ := unfill_skeleton D (2^(D+(1+h))-1) hD
 rw [←hss] at hu
 obtain ⟨v,hv,hvs,hvw,hvsp⟩ := RootCleanup.held_to_clean D h B K hD hk hsize
 rw [←hus] at hv
 have run := runs_append (runs_append (runs_append hr hs) hu) hv
 refine ⟨_,run,hvs,?_,?_⟩
 · change r.work+s.work+u.work+v.work≤3*(2^(D+(1+h))-1)
   have pm : 0<2^(1+h)-1 := by
     have hp : 0<2^h := Nat.pow_pos (by decide)
     rw [Nat.pow_add]; simp; omega
   have pR : 0<2^D := Nat.pow_pos (by decide)
   have e1 : B*(K*(2^(1+h)-1))=2^D*(2^(1+h)-1) := by rw [←Nat.mul_assoc,hsize]
   have e2 : B*(K*(2*(2^(1+h)-1)-1))+2^D=2*(2^D*(2^(1+h)-1)) := by
     rw [←Nat.mul_assoc,hsize]
     calc
      _=2^D*((2*(2^(1+h)-1)-1)+1) := by rw [Nat.mul_add,Nat.mul_one]
      _=2^D*(2*(2^(1+h)-1)) := by congr 1; omega
      _=2*(2^D*(2^(1+h)-1)) := by simp [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
   have e3 : 2^D*(2^(1+h)-1)+2^D=2^(D+(1+h)) := by
     calc
      _=2^D*((2^(1+h)-1)+1) := by rw [Nat.mul_add,Nat.mul_one]
      _=2^D*2^(1+h) := by congr 1; omega
      _=2^(D+(1+h)) := (Nat.pow_add _ _ _).symm
   rw [hrw,e1,hvw]
   omega
 · change max (max (max r.space s.space) u.space) v.space≤_
   have pR : 0<2^D := Nat.pow_pos (by decide)
   have init : r.space≤K*(2^(1+h)-1)+(2^(D+1)-1) := by
     rw [Nat.pow_succ]; omega
   exact Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨init,by omega⟩,by omega⟩,hvsp⟩
#print axioms complete


theorem twice_le_pow (f : Nat) (hf : 0<f) : 2*f≤2^f := by
 induction f with
 | zero => omega
 | succ f ih =>
   by_cases hz : f=0
   · subst f; decide
   · have hh := ih (by omega)
     rw [Nat.pow_succ]; omega

theorem height_upper (H : Nat) (hH : 2≤H) :
 ∃d t,PaperRuns HeapPath.pred d (empty (2^H-1)) t ∧
 t.state=rootOnly (2^H-1) ∧ t.work≤3*(2^H-1) ∧
 d≤3*H*Nat.log2 H+2*H ∧ H*t.space≤6*2^H := by
 let f := Nat.log2 H
 have hf : 0<f := by
   have hh := (Nat.le_log2 (n:=H) (by omega)).mpr (show 2^1≤H by simpa using hH)
   omega
 have pf : 2^f≤H := Nat.log2_self_le (by omega)
 have ff : 2*f≤H := Nat.le_trans (twice_le_pow f hf) pf
 have height : (H-f)+(1+(f-1))=H := by omega
 have hsize : 2^f*2^(H-2*f)=2^(H-f) := by
   rw [←Nat.pow_add]; congr 1; omega
 have hi := complete (H-f) (f-1) (2^f) (2^(H-2*f)) (by omega) (Nat.pow_pos (by decide)) hsize
 rw [height] at hi
 obtain ⟨t,ht,hs,hw,hsp⟩ := hi
 refine ⟨_,t,ht,hs,hw,?_,?_⟩
 · have he : 2^f*((1+(f-1))+1)+(H-f)+(H-f-1)+2^f*(2*(f-1)+1)≤3*H*f+2*H := by
     have h1 : ((1+(f-1))+1)+(2*(f-1)+1)=3*f := by omega
     have hm := Nat.mul_le_mul_right (3*f) pf
     have eq : 2^f*((1+(f-1))+1)+2^f*(2*(f-1)+1)=3*2^f*f := by
       rw [←Nat.mul_add,h1]; simp [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
     have hnorm : H*(3*f)=3*H*f := by simp [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
     have hnorm2 : 2^f*(3*f)=3*2^f*f := by simp [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
     rw [hnorm,hnorm2] at hm
     omega
   exact he
 · have ef : 1+(f-1)=f := by omega
   rw [ef] at hsp
   have km : 2^(H-2*f)*(2^f-1)≤2^(H-f) := by
     have hh := Nat.mul_le_mul_left (2^(H-2*f)) (Nat.sub_le (2^f : Nat) 1)
     rw [Nat.mul_comm (2^(H-2*f)) (2^f),hsize] at hh
     exact hh
   have ps : t.space≤3*2^(H-f) := by rw [Nat.pow_succ] at hsp; omega
   have hb : H≤2*2^f := by
     have hh := Nat.lt_log2_self (n:=H)
     change H<2^(f+1) at hh
     rw [Nat.pow_succ] at hh; omega
   have eq : 2^f*2^(H-f)=2^H := by rw [←Nat.pow_add]; congr 1; omega
   calc
    H*t.space≤H*(3*2^(H-f)) := Nat.mul_le_mul_left H ps
    _≤(2*2^f)*(3*2^(H-f)) := Nat.mul_le_mul_right _ hb
    _=6*(2^f*2^(H-f)) := by
      calc
       _=(2*3)*(2^f*2^(H-f)) := by ac_rfl
       _=_ := rfl
    _=6*2^H := by rw [eq]
#print axioms height_upper
end SkeletonUnfill
