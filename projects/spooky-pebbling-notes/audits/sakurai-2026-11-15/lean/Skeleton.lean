import FullPartition
namespace Skeleton
open SpookyRound BatchUpper FillUpper

def Band (q : Config n) (L U : Nat) := consistent q ∧ ∀v,q.peb v=decide (L≤v.val ∧ v.val<U)

theorem layer (q : Config n) (L U : Nat) (h : Band q (2*L+1) U) (hu : 4*L+3≤U) :
 Ready HeapPath.pred q (mask L) (fun _=>false) ∧ Band (evolve q (mask L) (fun _=>false)) L U := by
 have range : ∀v : Fin n,mask L v=true → L≤v.val ∧ v.val<2*L+1 := by simp [mask]
 have ready : Ready HeapPath.pred q (mask L) (fun _=>false) := by
   refine ⟨h.1,?_,?_,heap_layer_independent L (mask L) range,?_⟩
   · intro v hv; rw [h.2]; have hh := range v hv; simp; omega
   · intro v hv u hu'
     have hh := range v hv
     simp [HeapPath.pred] at hu'
     rw [h.2]; simp; omega
   · simp
 refine ⟨ready,evolve_consistent q _ h.1,?_⟩
 intro v
 simp only [evolve,Bool.and_true,Bool.not_false,h.2,mask]
 by_cases ha : L≤v.val <;> by_cases hb : 2*L+1≤v.val <;> by_cases hc : v.val<U <;> simp_all <;> omega

theorem fill (H U : Nat) (q : Config n) (h : Band q (2^H-1) U)
 (hu : 2^(H+1)-1≤U) :
 Admissible HeapPath.pred q (layers n H) ∧ Band (execute q (layers n H)).state 0 U := by
 induction H generalizing q with
 | zero => simpa [layers,execute,Admissible] using h
 | succ H ih =>
   have hp : 0<2^H := Nat.pow_pos (by decide)
   have he : 2^(H+1)-1=2*(2^H-1)+1 := by rw [Nat.pow_succ]; omega
   have hh : 4*(2^H-1)+3≤U := by simp only [Nat.pow_succ] at hu; omega
   rw [he] at h
   have hl := layer q (2^H-1) U h hh
   have small : 2^(H+1)-1≤U := by rw [he]; omega
   have hr := ih _ hl.2 small
   exact ⟨⟨hl.1,hr.1⟩,hr.2⟩


theorem card_cap (C : Fin n → Bool) (U : Nat) (hc : ∀v,C v=true → v.val<U) : card C≤U := by
 have hn : (((List.finRange n).filter C).map Fin.val).Nodup := by
   apply List.pairwise_map.mpr
   have hh := (List.nodup_finRange n).filter C
   apply hh.imp
   intro a b hab he
   exact hab (Fin.ext he)
 have hs : (((List.finRange n).filter C).map Fin.val) ⊆ List.range U := by
   intro a ha
   obtain ⟨v,hv,rfl⟩ := List.mem_map.mp ha
   exact List.mem_range.mpr (hc v (List.mem_filter.mp hv).2)
 have hh := hn.length_le_of_subset hs
 simpa [card] using hh

theorem work (H U : Nat) (q : Config n) (h : Band q (2^H-1) U) (hu : 2^(H+1)-1≤U) :
 (execute q (layers n H)).work+CutSpace.pebs q=CutSpace.pebs (execute q (layers n H)).state := by
 induction H generalizing q with
 | zero => simp [layers,execute]
 | succ H ih =>
   have hp : 0<2^H := Nat.pow_pos (by decide)
   have he : 2^(H+1)-1=2*(2^H-1)+1 := by rw [Nat.pow_succ]; omega
   have hh : 4*(2^H-1)+3≤U := by simp only [Nat.pow_succ] at hu; omega
   rw [he] at h
   have hl := layer q (2^H-1) U h hh
   have hr := ih _ hl.2 (by rw [he]; omega)
   have hp := pebs_evolve q (mask (2^H-1)) hl.1.fresh
   simp only [layers,execute,SpookyDP.prepend]
   omega

theorem space (H U : Nat) (q : Config n) (h : Band q (2^H-1) U) (hu : 2^(H+1)-1≤U) :
 (execute q (layers n H)).space≤U := by
 induction H generalizing q with
 | zero => simp [layers,execute]
 | succ H ih =>
   have hp : 0<2^H := Nat.pow_pos (by decide)
   have he : 2^(H+1)-1=2*(2^H-1)+1 := by rw [Nat.pow_succ]; omega
   have hh : 4*(2^H-1)+3≤U := by simp only [Nat.pow_succ] at hu; omega
   rw [he] at h
   have hl := layer q (2^H-1) U h hh
   have hr := ih _ hl.2 (by rw [he]; omega)
   apply Nat.max_le.mpr
   refine ⟨card_cap _ U ?_,hr⟩
   intro v hv
   simp [h.2,mask] at hv
   omega


theorem card_interval (C : Fin n → Bool) (L U : Nat)
 (hc : ∀v,C v=true → L≤v.val ∧ v.val<U) : card C≤U-L := by
 have hn : (((List.finRange n).filter C).map (fun v=>v.val-L)).Nodup := by
   apply List.pairwise_map.mpr
   have hh := (List.nodup_finRange n).filter C
   apply hh.imp_of_mem
   intro a b ha hb hab he
   have h1 := hc a (List.mem_filter.mp ha).2
   have h2 := hc b (List.mem_filter.mp hb).2
   apply hab; apply Fin.ext; omega
 have hs : (((List.finRange n).filter C).map (fun v=>v.val-L)) ⊆ List.range (U-L) := by
   intro a ha
   obtain ⟨v,hv,rfl⟩ := List.mem_map.mp ha
   have hh := hc v (List.mem_filter.mp hv).2
   apply List.mem_range.mpr; omega
 have hh := hn.length_le_of_subset hs
 simpa [card] using hh

theorem work_bound (H : Nat) (q : Config n) : (execute q (layers n H)).work≤2^H-1 := by
 induction H generalizing q with
 | zero => simp [layers,execute]
 | succ H ih =>
   have hc := card_interval (mask (2^H-1) : Fin n → Bool) (2^H-1) (2*(2^H-1)+1) (by simp [mask])
   have hi := ih (evolve q (mask (2^H-1)) (fun _=>false))
   have hp : 0<2^H := Nat.pow_pos (by decide)
   simp only [layers,execute,SpookyDP.prepend,Nat.pow_succ]
   omega

theorem ghost_fill (H U : Nat) (q : Config n) (hg : ∀v,q.ghost v=decide (U≤v.val))
 (hu : 2^H-1≤U) : ∀v,(execute q (layers n H)).state.ghost v=decide (U≤v.val) := by
 induction H generalizing q with
 | zero => exact hg
 | succ H ih =>
   have hp : 0<2^H := Nat.pow_pos (by decide)
   have hh : 2^H-1≤U := by rw [Nat.pow_succ] at hu; omega
   apply ih _ ?_ hh
   intro v
   simp only [evolve,hg,Bool.or_false]
   by_cases hv : U≤v.val
   · have hm : ¬(2^H-1≤v.val ∧ v.val<2*(2^H-1)+1) := by
       rw [Nat.pow_succ] at hu; omega
     simp only [mask,hm,decide_false,Bool.not_false,Bool.and_true]
   · simp [hv]

def capState (U n : Nat) : Config n := ⟨fun v=>decide (v.val<U),fun v=>decide (U≤v.val)⟩

theorem boundary_band (D n : Nat) : Band (FullPartition.boundary D n) (2^D-1) (2^(D+1)-1) := by
 constructor
 · intro v; simp [FullPartition.boundary]; omega
 · intro v; rfl

theorem skeleton (D n : Nat) :
 ∃t,PaperRuns HeapPath.pred D (FullPartition.boundary D n) t ∧
 t.state=capState (2^(D+1)-1) n ∧ t.work≤2^D-1 ∧ t.space≤2^(D+1)-1 := by
 let q := FullPartition.boundary D n
 have hf := fill D (2^(D+1)-1) q (boundary_band D n) (by omega)
 refine ⟨execute q (layers n D),?_,?_,work_bound D q,space D _ q (boundary_band D n) (by omega)⟩
 · simpa [layer_length] using execute_runs hf.1
 · have hp : 0<2^D := Nat.pow_pos (by decide)
   have hg := ghost_fill D (2^(D+1)-1) q (fun _=>rfl) (by rw [Nat.pow_succ]; omega)
   apply SpookyReverse.config_ext
   · intro v; simpa [capState] using hf.2.2 v
   · intro v; exact hg v

#print axioms skeleton
#print axioms work
#print axioms card_interval


theorem collapse (U n : Nat) (hu : 0<U) :
 ∃t,PaperRuns HeapPath.pred 1 (capState U n) t ∧ t.state=InitialGhost.rootGhost n ∧ t.work=0 ∧ t.space≤U := by
 let C : Fin n→Bool := fun _=>false
 let G : Fin n→Bool := fun v=>decide (v.val≠0 ∧ v.val<U)
 have hr : Ready HeapPath.pred (capState U n) C G := by
   refine ⟨?_,?_,?_,?_,?_⟩
   · intro v; simp [capState]
   · simp [C]
   · simp [C]
   · simp [C]
   · intro v hv; left; simp [G] at hv; simpa [capState] using hv.2
 have hs := batch_step hr
 have es : evolve (capState U n) C G=InitialGhost.rootGhost n := by
   apply SpookyReverse.config_ext <;> intro v <;>
     by_cases hz : v.val=0 <;> by_cases hv : v.val<U <;>
       simp_all [evolve,capState,C,G,InitialGhost.rootGhost] <;> omega
 have wc : card C=0 := by simp [card,C]
 have sp : card (fun v=>(capState U n).peb v||C v)≤U :=
   card_cap _ U (by intro v hv; simpa [capState,C] using hv)
 rw [es,wc] at hs
 have hh := PaperRuns.step hs (PaperRuns.zero (InitialGhost.rootGhost n))
 refine ⟨_,hh,rfl,?_,?_⟩
 · simp [SpookyDP.prepend]
 · simpa [SpookyDP.prepend] using sp

theorem skeleton_to_root (D n : Nat) :
 ∃t,PaperRuns HeapPath.pred (D+1) (FullPartition.boundary D n) t ∧
 t.state=InitialGhost.rootGhost n ∧ t.work≤2^D-1 ∧ t.space≤2^(D+1)-1 := by
 obtain ⟨r,hr,hrs,hrw,hrsp⟩ := skeleton D n
 have hp : 0<2^D := Nat.pow_pos (by decide)
 obtain ⟨t,ht,hts,htw,htsp⟩ := collapse (2^(D+1)-1) n (by rw [Nat.pow_succ]; omega)
 rw [←hrs] at ht
 refine ⟨_,runs_append hr ht,hts,?_,Nat.max_le.mpr ⟨hrsp,htsp⟩⟩
 simpa [htw] using hrw

theorem initial_root (D h B K : Nat) (hh : 0<h) (hk : 0<K) (hsize : B*K=2^D) :
 ∃t,PaperRuns HeapPath.pred (B*(h+1)+(D+1)) (empty (2^(D+h)-1)) t ∧
 t.state=InitialGhost.rootGhost (2^(D+h)-1) ∧ t.work≤2^(D+h)-1 ∧
 t.space≤max (K*(2^h-1)+2^D) (2^(D+1)-1) := by
 obtain ⟨r,hr,hrs,hrw,hrsp,hrp⟩ := FullPartition.initial_with_boundary D h B K hh hk hsize
 obtain ⟨t,ht,hts,htw,htsp⟩ := skeleton_to_root D (2^(D+h)-1)
 rw [←hrs] at ht
 refine ⟨_,runs_append hr ht,hts,?_,Nat.max_le.mpr ⟨Nat.le_trans hrsp (Nat.le_max_left _ _),Nat.le_trans htsp (Nat.le_max_right _ _)⟩⟩
 have p : 0<2^h := Nat.pow_pos (by decide)
 have pD : 0<2^D := Nat.pow_pos (by decide)
 have eq : B*(K*(2^h-1))=2^D*(2^h-1) := by rw [←Nat.mul_assoc,hsize]
 have ar : 2^D*(2^h-1)+2^D=2^D*2^h := by
   calc
    _=2^D*((2^h-1)+1) := by rw [Nat.mul_add,Nat.mul_one]
    _=2^D*2^h := by congr 1; omega
 change r.work+t.work≤_
 rw [hrw,eq]
 have hpw := Nat.pow_add 2 D h
 omega
#print axioms initial_root
#print axioms skeleton_to_root
end Skeleton
