import SyncTrace
namespace FamilySync
open SpookyRound

def total (f : Fin k → Nat) := ((List.finRange k).map f).sum

theorem total_add (f g : Fin k → Nat) : total (fun i=>f i+g i)=total f+total g := by
 exact HeapPath.sum_add _ _ _
theorem total_mono (f g : Fin k → Nat) (h : ∀i,f i≤g i) : total f≤total g := by
 exact Exceptions.sum_le _ _ _ (fun i _=>h i)
@[simp] theorem total_zero : total (fun _ : Fin k=>0)=0 := by
 unfold total
 generalize List.finRange k = xs
 induction xs with
 | nil => rfl
 | cons a xs ih => simp [ih]

def ConsistentFamily (q : Fin k → Config m) := ∀i,FillUpper.consistent (q i)

/-- Explicit unproved-at-this-interface obligations: simultaneous physical step,
    exact work sum, peak sum plus ONE exterior occupancy, and product state. -/
structure RoundProduct (k m N : Nat) (p : Fin m→Fin m→Bool) (P : Fin N→Fin N→Bool) where
 pack : (Fin k→Config m)→Config N
 exterior : Nat
 step : ∀(q : Fin k→Config m)(e : Fin k→SpookyDP.Result (Config m)),
   ConsistentFamily q → (∀i,PaperStep p (q i) (e i)) →
   ∃E,PaperStep P (pack q) E ∧ E.state=pack (fun i=>(e i).state) ∧
     E.work=total (fun i=>(e i).work) ∧ E.space≤total (fun i=>(e i).space)+exterior

theorem step_consistent (he : PaperStep p q e) : FillUpper.consistent e.state := by
 obtain ⟨a,_,_,hl,rfl⟩ := he
 exact afterRound_disjoint _ _ _ hl

theorem uncons (hr : PaperRuns p (d+1) q r) :
 ∃e t,PaperStep p q e ∧ PaperRuns p d e.state t ∧ r=SpookyDP.prepend e t := by
 cases hr with | step he ht => exact ⟨_,_,he,ht,rfl⟩

theorem zero_result (h : PaperRuns p 0 q r) : r=⟨q,0,0⟩ := by
 cases h
 rfl

/-- Arbitrary K, including K=0. Common depth; no hidden sequential execution. -/
theorem sync (R : RoundProduct k m N p P) (q : Fin k→Config m)
 (r : Fin k→SpookyDP.Result (Config m))
 (hc : ConsistentFamily q) (hr : ∀i,PaperRuns p d (q i) (r i)) :
 ∃t,PaperRuns P d (R.pack q) t ∧ t.state=R.pack (fun i=>(r i).state) ∧
 t.work=total (fun i=>(r i).work) ∧ t.space≤total (fun i=>(r i).space)+R.exterior := by
 classical
 induction d generalizing q r with
 | zero =>
   have hz : ∀i,r i=⟨q i,0,0⟩ := fun i=>zero_result (hr i)
   refine ⟨_,PaperRuns.zero _,?_,?_,?_⟩ <;> simp [hz]
 | succ d ih =>
   have hu := fun i=>uncons (hr i)
   let e := fun i=>Classical.choose (hu i)
   let t := fun i=>Classical.choose (Classical.choose_spec (hu i))
   have hh : ∀i,PaperStep p (q i) (e i) ∧ PaperRuns p d (e i).state (t i) ∧
     r i=SpookyDP.prepend (e i) (t i) := fun i=>Classical.choose_spec (Classical.choose_spec (hu i))
   obtain ⟨E,hE,hEs,hEw,hEp⟩ := R.step q e hc (fun i=>(hh i).1)
   obtain ⟨T,hT,hTs,hTw,hTp⟩ := ih (fun i=>(e i).state) t
     (fun i=>step_consistent (hh i).1) (fun i=>(hh i).2.1)
   have hT' : PaperRuns P d E.state T := by rw [hEs]; exact hT
   refine ⟨_,PaperRuns.step hE hT',?_,?_,?_⟩
   · simpa only [SpookyDP.prepend,funext (fun i=>congrArg (fun x=>x.state) (hh i).2.2)] using hTs
   · change E.work+T.work=total (fun i=>(r i).work)
     rw [hEw,hTw,←total_add]
     congr 1; funext i; rw [(hh i).2.2]; rfl
   · change max E.space T.space≤total (fun i=>(r i).space)+R.exterior
     apply Nat.max_le.mpr
     constructor
     · apply Nat.le_trans hEp
       apply Nat.add_le_add_right
       apply total_mono
       intro i; rw [(hh i).2.2]; exact Nat.le_max_left _ _
     · apply Nat.le_trans hTp
       apply Nat.add_le_add_right
       apply total_mono
       intro i; rw [(hh i).2.2]; exact Nat.le_max_right _ _
theorem total_const (c : Nat) : total (fun _ : Fin k=>c)=k*c := by
 unfold total
 have h : ∀xs : List (Fin k),(xs.map (fun _=>c)).sum=xs.length*c := by
   intro xs
   induction xs with
   | nil => simp
   | cons a xs ih => simp [ih,Nat.succ_mul,Nat.add_comm]
 simpa using h (List.finRange k)

/-- Uniform local costs. This is conditional on RoundProduct, NOT yet a
    concrete arbitrary-fringe constructor. Exterior is charged once. -/
theorem sync_uniform (R : RoundProduct k m N p P) (q : Fin k→Config m)
 (r : Fin k→SpookyDP.Result (Config m)) (hc : ConsistentFamily q)
 (hr : ∀i,PaperRuns p d (q i) (r i))
 (hw : ∀i,(r i).work=w) (hs : ∀i,(r i).space≤s) :
 ∃t,PaperRuns P d (R.pack q) t ∧ t.state=R.pack (fun i=>(r i).state) ∧
 t.work=k*w ∧ t.space≤k*s+R.exterior := by
 obtain ⟨t,ht,hst,hwt,hsp⟩ := sync R q r hc hr
 refine ⟨t,ht,hst,?_,?_⟩
 · rw [hwt]; simpa only [hw] using total_const (k:=k) w
 · have hh := total_mono (fun i=>(r i).space) (fun _=>s) hs
   rw [total_const] at hh
   omega

theorem family_cleanup (R : RoundProduct k (2^h-1) N HeapPath.pred P)
 (q : Fin k→Config (2^h-1)) (hc : ConsistentFamily q)
 (hp : ∀i v,(q i).peb v=false) :
 ∃t,PaperRuns P (2*h) (R.pack q) t ∧
 t.state=R.pack (fun _=>FillUpper.empty (2^h-1)) ∧
 t.work=k*(2*(2^h-1)) ∧ t.space≤k*(2^h-1)+R.exterior := by
 classical
 have hx := fun i=>FillUpper.full_storage_cleanup h (q i) (hc i) (hp i)
 let r := fun i=>Classical.choose (hx i)
 have hh := fun i=>Classical.choose_spec (hx i)
 obtain ⟨t,ht,hst,hw,hs⟩ := sync_uniform R q r hc
   (fun i=>(hh i).1) (fun i=>(hh i).2.2.1) (fun i=>(hh i).2.2.2)
 refine ⟨t,ht,?_,hw,hs⟩
 rw [hst]
 congr 1
 funext i
 exact (hh i).2.1
#print axioms family_cleanup
#print axioms sync_uniform
#print axioms sync
end FamilySync
