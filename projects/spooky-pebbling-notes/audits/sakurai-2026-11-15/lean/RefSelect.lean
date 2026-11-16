import RefArea
namespace RefSelect
open SpookyRound TraceBridge CutBound RefPartition RefSum

def comp (u : Fin n) (gap : List Action) := count .compute (events u gap)
def good (u : Fin n) (xs : List (List Action)) := xs.filter fun gap => comp u gap==0
def bad (u : Fin n) (xs : List (List Action)) := xs.filter fun gap => comp u gap != 0

theorem split_lengths (u : Fin n) (xs : List (List Action)) :
 (good u xs).length+(bad u xs).length=xs.length := by
 induction xs with
 | nil => rfl
 | cons gap xs ih =>
   by_cases hh : comp u gap=0 <;> simp_all [good,bad] <;> omega

theorem bad_le_computes (u : Fin n) (xs : List (List Action)) :
 (bad u xs).length≤total (comp u) xs := by
 induction xs with
 | nil => simp [bad,total]
 | cons gap xs ih =>
   by_cases hh : comp u gap=0 <;> simp_all [bad,total] <;> omega

theorem no_compute_of_zero (u : Fin n) (as : List Action) (hc : comp u as=0) :
 ∀a∈as,firstAt a u≠.pebble := by
 intro a ha hm
 have he : Event.compute ∈ events u as := (compute_in_events u as).mpr ⟨a,ha,hm⟩
 have hm' : Event.compute ∈ (events u as).filter (fun e => e==.compute) := by simp [he]
 have hp := List.length_pos_of_mem hm'
 unfold comp count at hc
 omega

theorem kept_gap_live {pred : Fin n → Fin n → Bool}
 (h : ActionRuns pred q (gap++b::ys) r) (u : Fin n)
 (hb : references pred u b=true) (hc : comp u gap=0) :
 Area.live u q gap=gap.length ∧ gap.length≤Area.volume q gap :=
 ⟨RefArea.reference_suffix_live h u hb (no_compute_of_zero u gap hc),
 by
   rw [←RefArea.reference_suffix_live h u hb (no_compute_of_zero u gap hc)]
   exact RefArea.live_le_volume q gap u⟩

theorem removed_count {pred : Fin n → Fin n → Bool} (h : ActionRuns pred q as r) (u : Fin n) :
 (bad u (interior (parts (references pred u) as).2)).length≤comp u as := by
 have hb := bad_le_computes u (interior (parts (references pred u) as).2)
 have hi := total_interior_le (comp u) (parts (references pred u) as).2
 have hf := events_count_flatten u .compute (parts (references pred u) as).2
 have he := reconstruct (references pred u) as
 have hh : comp u as=comp u (parts (references pred u) as).1+
   comp u (parts (references pred u) as).2.flatten := by
   unfold comp
   calc
    _ = count .compute (events u ((parts (references pred u) as).1++(parts (references pred u) as).2.flatten)) := congrArg (fun xs => count .compute (events u xs)) he.symm
    _ = _ := by rw [RefSum.events_append,EpochCharge.count_append]
 unfold comp at *
 omega

#print axioms kept_gap_live
#print axioms removed_count
#print axioms split_lengths

theorem many_kept {pred : Fin n → Fin n → Bool} (h : ActionRuns pred q as r) (u : Fin n) :
 (interior (parts (references pred u) as).2).length≤
 (good u (interior (parts (references pred u) as).2)).length+comp u as := by
 have hs := split_lengths u (interior (parts (references pred u) as).2)
 have hb := removed_count h u
 omega

theorem kept_has_no_loss {pred : Fin n → Fin n → Bool}
 (h : ActionRuns pred q as r) (u : Fin n) (left right : List (List Action))
 (gap next : List Action)
 (hp : (parts (references pred u) as).2=left++gap::next::right)
 (hc : comp u gap=0) :
 count .ghost (events u gap)=0 ∧ count .uncompute (events u gap)=0 := by
 have hh := extracted_gap h u left right gap next hp
 unfold comp at hc
 omega

#print kept_gap_live
#print axioms many_kept
#print axioms kept_has_no_loss
end RefSelect
