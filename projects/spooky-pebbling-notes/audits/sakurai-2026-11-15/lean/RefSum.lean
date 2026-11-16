import RefPartition
namespace RefSum
open SpookyRound TraceBridge CutBound RefPartition

def interior : List (List α) → List (List α)
 | [] => []
 | [_] => []
 | a::b::xs => a::interior (b::xs)

def total (f : List α → Nat) (xs : List (List α)) : Nat := (xs.map f).sum

theorem total_interior_le (f : List α → Nat) (xs : List (List α)) :
 total f (interior xs) ≤ total f xs := by
 induction xs with
 | nil => simp [interior,total]
 | cons a xs ih =>
   cases xs with
   | nil => simp [interior,total]
   | cons b xs => simp only [interior,total,List.map_cons,List.sum_cons] at *; omega

theorem aggregate_suffix {n : Nat} {pred : Fin n → Fin n → Bool} {q : Config n}
 {r : SpookyDP.Result (Config n)} {as : List Action}
 (h : ActionRuns pred q as r) (u : Fin n) (xs : List (List Action)) :
 ∀left,(parts (references pred u) as).2=left++xs →
 total (fun gap => count .compute (events u gap)) (interior xs)=
 total (fun gap => count .ghost (events u gap)) (interior xs)+
 total (fun gap => count .uncompute (events u gap)) (interior xs) := by
 induction xs with
 | nil => intros; simp [interior,total]
 | cons a xs ih =>
   intro left hp
   cases xs with
   | nil => simp [interior,total]
   | cons b xs =>
     have ha := extracted_gap h u left xs a b hp
     have hi := ih (left++[a]) (by simpa only [List.append_assoc,List.singleton_append] using hp)
     simp only [interior,total,List.map_cons,List.sum_cons] at *
     omega

theorem aggregate {n : Nat} {pred : Fin n → Fin n → Bool} {q : Config n}
 {r : SpookyDP.Result (Config n)} {as : List Action}
 (h : ActionRuns pred q as r) (u : Fin n) :
 total (fun gap => count .compute (events u gap)) (interior (parts (references pred u) as).2)=
 total (fun gap => count .ghost (events u gap)) (interior (parts (references pred u) as).2)+
 total (fun gap => count .uncompute (events u gap)) (interior (parts (references pred u) as).2) :=
 aggregate_suffix h u _ [] (by simp)

theorem events_append (u : Fin n) (xs ys : List Action) :
 events u (xs++ys)=events u xs++events u ys := by
 induction xs with
 | nil => rfl
 | cons a xs ih => simp [events,ih]

theorem events_count_flatten (u : Fin n) (e : Event) (xs : List (List Action)) :
 total (fun gap => count e (events u gap)) xs = count e (events u xs.flatten) := by
 induction xs with
 | nil => simp [total,events,count]
 | cons a xs ih =>
   simp only [total,List.map_cons,List.sum_cons,List.flatten_cons] at *
   rw [events_append,EpochCharge.count_append,ih]

theorem no_duplicate_charge {n : Nat} {pred : Fin n → Fin n → Bool} {q : Config n}
 {r : SpookyDP.Result (Config n)} {as : List Action}
 (h : ActionRuns pred q as r) (u : Fin n) :
 total (fun gap => count .ghost (events u gap)) (interior (parts (references pred u) as).2)+
 total (fun gap => count .uncompute (events u gap)) (interior (parts (references pred u) as).2)
 ≤ count .compute (events u as) := by
 rw [←aggregate h u]
 have hi := total_interior_le (fun gap => count .compute (events u gap)) (parts (references pred u) as).2
 have hf := events_count_flatten u .compute (parts (references pred u) as).2
 have he := reconstruct (references pred u) as
 have hc : count .compute (events u as)=
  count .compute (events u (parts (references pred u) as).1)+
  count .compute (events u (parts (references pred u) as).2.flatten) := by
   calc
    _ = count .compute (events u ((parts (references pred u) as).1++(parts (references pred u) as).2.flatten)) := congrArg (fun xs => count .compute (events u xs)) he.symm
    _ = _ := by rw [events_append,EpochCharge.count_append]
 omega

#print axioms no_duplicate_charge
#print axioms aggregate
#print axioms total_interior_le
#print axioms events_count_flatten
end RefSum
