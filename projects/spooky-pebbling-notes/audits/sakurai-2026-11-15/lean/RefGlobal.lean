import RefSum
namespace RefGlobal
open SpookyRound TraceBridge CutBound RefPartition RefSum

def cbit : Move → Nat
 | .pebble => 1
 | _ => 0

def actualComputes (as : List Action) : Nat :=
 (as.map fun a => (a.first.filter fun m => m == .pebble).length).sum

theorem scalar_computes (v : Fin n) (as : List Action) :
 count .compute (events v as)=(as.map fun a => cbit (firstAt a v)).sum := by
 induction as with
 | nil => rfl
 | cons a as ih =>
   cases hm : firstAt a v <;> cases hg : ghostAt a v <;>
    simp_all [events,firstEvent,secondEvent,count,cbit] <;> omega

theorem filter_computes (ms : List Move) :
 (ms.filter fun m => m == .pebble).length=(ms.map cbit).sum := by
 induction ms with
 | nil => rfl
 | cons m ms ih => cases m <;> simp_all [cbit] <;> omega

theorem compute_slots {pred : Fin n → Fin n → Bool} (h : ActionRuns pred q as r) :
 ((List.finRange n).map fun v => count .compute (events v as)).sum=actualComputes as := by
 have hall : ∀a ∈ as,a.first.length=n := by
   induction h with
   | nil q => simp
   | cons hm hg hl ht ih =>
     intro a ha
     simp only [List.mem_cons] at ha
     rcases ha with ha|ha
     · subst a; exact hm
     · exact ih a ha
 have he : as.map (fun a => (a.first.filter fun m => m == .pebble).length)=
  as.map (fun a => ((List.finRange n).map fun v => cbit (firstAt a v)).sum) := by
   apply List.map_congr_left
   intro a ha
   rw [filter_computes,←WorkBridge.indexed_moves a (hall a ha),List.map_map]
   rfl
 unfold actualComputes
 rw [he,HeapPath.exchange]
 apply congrArg List.sum
 apply List.map_congr_left
 intro v hv
 exact scalar_computes v as

def charged (pred : Fin n → Fin n → Bool) (as : List Action) (u : Fin n) : Nat :=
 total (fun gap => count .ghost (events u gap)) (interior (parts (references pred u) as).2)+
 total (fun gap => count .uncompute (events u gap)) (interior (parts (references pred u) as).2)

theorem sum_mono (xs : List α) (f g : α → Nat) (h : ∀v∈xs,f v≤g v) :
 (xs.map f).sum≤(xs.map g).sum := by
 induction xs with
 | nil => simp
 | cons v xs ih =>
   have hh := h v (by simp)
   have hr := ih (fun u hu => h u (by simp [hu]))
   simp only [List.map_cons,List.sum_cons]
   omega

theorem all_vertices {pred : Fin n → Fin n → Bool} (h : ActionRuns pred q as r) :
 ((List.finRange n).map (charged pred as)).sum≤actualComputes as := by
 rw [←compute_slots h]
 apply sum_mono
 intro v hv
 exact no_duplicate_charge h v

#print axioms compute_slots
#print axioms all_vertices

theorem total_charge_le_work {pred : Fin n → Fin n → Bool} (h : ActionRuns pred q as r) :
 ((List.finRange n).map (charged pred as)).sum≤r.work := by
 have hc := all_vertices h
 have hm : actualComputes as≤r.work := by
   rw [←compute_slots h,WorkBridge.work_by_vertices h]
   apply sum_mono
   intros
   omega
 exact Nat.le_trans hc hm

theorem paper_charge {pred : Fin n → Fin n → Bool} (h : PaperRuns pred d q r) :
 ∃as,as.length=d ∧ ActionRuns pred q as r ∧
  ((List.finRange n).map (charged pred as)).sum≤actualComputes as ∧
  ((List.finRange n).map (charged pred as)).sum≤r.work := by
 obtain ⟨as,hd,ha⟩ := extract_actions h
 exact ⟨as,hd,ha,all_vertices ha,total_charge_le_work ha⟩

#print axioms total_charge_le_work
#print axioms paper_charge
end RefGlobal
