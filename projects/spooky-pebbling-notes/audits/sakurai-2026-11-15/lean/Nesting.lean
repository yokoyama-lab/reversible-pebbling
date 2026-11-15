import GoodInterval
namespace Nesting
open SpookyRound TraceBridge
variable {n : Nat} {q : Config n} {r : SpookyDP.Result (Config n)}
def time (as : List Action) (v : Fin n) (m : Move) : Nat :=
  as.findIdx (fun a => firstAt a v == m)

theorem time_unique (xs ys : List Action) (a : Action) (v : Fin n)
    (m : Move) (e : CutBound.Event)
    (he : (m = .pebble ∧ e = .compute) ∨ (m = .unpebble ∧ e = .uncompute))
    (ha : firstAt a v = m) (hc : CutBound.count e (events v (xs++a::ys)) = 1) :
    time (xs++a::ys) v m = xs.length := by
  have hz := (GoodInterval.unique_round_counts xs ys a v m e he ha hc).1
  have hno : ∀ b ∈ xs, (firstAt b v == m) = false := by
    intro b hb
    cases hh : firstAt b v == m with
    | false => rfl
    | true =>
      have hm : firstAt b v = m := by simpa using hh
      have hex : e ∈ events v xs := by
        rcases he with ⟨hm',he'⟩ | ⟨hm',he'⟩
        · rw [he']; exact (compute_in_events v xs).mpr ⟨b,hb,hm.trans hm'⟩
        · rw [he']; exact (uncompute_in_events v xs).mpr ⟨b,hb,hm.trans hm'⟩
      have hp := Exceptions.count_positive e (events v xs) hex
      omega
  unfold time
  rw [List.findIdx_append,List.findIdx_eq_length_of_false hno]
  simp [List.findIdx_cons,ha]

theorem active_bracket_times {pred : Fin n → Fin n → Bool}
    (xs ys : List Action) (h : ActionRuns pred q (xs++a::ys) r)
    (v u : Fin n) (hne : v ≠ u) (hv : firstAt a v ≠ .idle) (hedge : pred v u = true)
    (hs : kind q u ≠ .pebble) (hf : kind r.state u = .empty)
    (hc : CutBound.count .compute (events u (xs++a::ys)) = 1)
    (hu : CutBound.count .uncompute (events u (xs++a::ys)) = 1) :
    time (xs++a::ys) u .pebble < xs.length ∧
      xs.length < time (xs++a::ys) u .unpebble := by
  obtain ⟨⟨b,hb,hcM⟩,⟨c,hc',huM⟩⟩ := parent_bracketed xs ys h v u hne hv hedge hs hf
  obtain ⟨bs,bt,hxs⟩ := Descendants.split_mem hb
  obtain ⟨cs,ct,hys⟩ := Descendants.split_mem hc'
  constructor
  · have heq : xs++a::ys = bs++b::(bt++a::ys) := by rw [hxs]; simp
    rw [heq] at hc ⊢
    rw [time_unique bs _ b u .pebble .compute (Or.inl ⟨rfl,rfl⟩) hcM hc]
    rw [hxs]; simp
  · have heq : xs++a::ys = (xs++a::cs)++c::ct := by rw [hys]; simp
    rw [heq] at hu ⊢
    rw [time_unique _ ct c u .unpebble .uncompute (Or.inr ⟨rfl,rfl⟩) huM hu]
    simp
theorem good_edge_nesting {pred : Fin n → Fin n → Bool}
    (h : ActionRuns pred q as r) (v u : Fin n)
    (hne : v ≠ u) (he : pred v u = true)
    (hsv : kind q v ≠ .pebble) (hsu : kind q u ≠ .pebble)
    (hfu : kind r.state u = .empty)
    (hcv : CutBound.count .compute (events v as) = 1)
    (huv : CutBound.count .uncompute (events v as) = 1)
    (hcu : CutBound.count .compute (events u as) = 1)
    (huu : CutBound.count .uncompute (events u as) = 1) :
    time as u .pebble < time as v .pebble ∧
      time as v .pebble < time as v .unpebble ∧
      time as v .unpebble < time as u .unpebble := by
  obtain ⟨xs,c,mid,b,tail,heq,hc,hb,hno⟩ := GoodInterval.good_decomposition h v hsv hcv huv
  subst as
  have htC := time_unique xs (mid++b::tail) c v .pebble .compute (Or.inl ⟨rfl,rfl⟩) hc hcv
  have hsplit : xs++c::(mid++b::tail) = (xs++c::mid)++b::tail := by simp
  have hvU : CutBound.count .uncompute (events v ((xs++c::mid)++b::tail)) = 1 := by rw [← hsplit]; exact huv
  have htU := time_unique (xs++c::mid) tail b v .unpebble .uncompute (Or.inr ⟨rfl,rfl⟩) hb hvU
  rw [← hsplit] at htU
  have hl := (active_bracket_times xs (mid++b::tail) h v u hne (by simp [hc]) he hsu hfu hcu huu).1
  have hh : ActionRuns pred q ((xs++c::mid)++b::tail) r := by rw [← hsplit]; exact h
  have hcu' : CutBound.count .compute (events u ((xs++c::mid)++b::tail)) = 1 := by rw [← hsplit]; exact hcu
  have huu' : CutBound.count .uncompute (events u ((xs++c::mid)++b::tail)) = 1 := by rw [← hsplit]; exact huu
  have hr := (active_bracket_times (xs++c::mid) tail hh v u hne (by simp [hb]) he hsu hfu hcu' huu').2
  rw [← hsplit] at hr
  rw [htC,htU]
  exact ⟨hl,by simp,hr⟩
theorem live_prefix_le (xs ys : List Action) (q : Config n) (v : Fin n) :
    Area.live v q xs ≤ Area.live v q (xs++ys) := by
  induction xs generalizing q with
  | nil => simp [Area.live]
  | cons a xs ih =>
    have hh := ih (afterRound q a)
    simp only [List.cons_append,Area.live]
    omega

theorem live_split {pred : Fin n → Fin n → Bool}
    (h : ActionRuns pred q xs p) (ys : List Action) (v : Fin n) :
    Area.live v q (xs++ys) = Area.live v q xs + Area.live v p.state ys := by
  induction h with
  | nil q => simp [Area.live]
  | cons hm hg hl ht ih => simp only [List.cons_append,Area.live,SpookyDP.prepend]; rw [ih]; omega

theorem good_span_bound {pred : Fin n → Fin n → Bool}
    (h : ActionRuns pred q as r) (v : Fin n)
    (hs : kind q v ≠ .pebble)
    (hc : CutBound.count .compute (events v as) = 1)
    (hu : CutBound.count .uncompute (events v as) = 1) :
    time as v .unpebble - time as v .pebble ≤ Area.live v q as := by
  obtain ⟨xs,c,mid,b,tail,he,hcM,huM,hno⟩ := GoodInterval.good_decomposition h v hs hc hu
  subst as
  have hsplit : xs++c::(mid++b::tail) = (xs++c::mid)++b::tail := by simp
  have tc := time_unique xs _ c v .pebble .compute (Or.inl ⟨rfl,rfl⟩) hcM hc
  have hu' : CutBound.count .uncompute (events v ((xs++c::mid)++b::tail)) = 1 := by rw [← hsplit]; exact hu
  have tu := time_unique _ tail b v .unpebble .uncompute (Or.inr ⟨rfl,rfl⟩) huM hu'
  rw [← hsplit] at tu
  obtain ⟨p,t,hp,ht,hfinal⟩ := split_actions xs (c::(mid++b::tail)) h
  have hl := live_split hp (c::(mid++b::tail)) v
  cases ht with
  | cons hm hg hlegal htail =>
    have he := GoodInterval.live_through_cleanup mid tail htail v huM hno
    have hb := live_prefix_le (mid++[b]) tail (afterRound p.state c) v
    simp only [List.append_assoc,List.singleton_append] at hb
    rw [he] at hb
    rw [tc,tu,hl]
    simp only [List.length_append,List.length_cons,Area.live]
    omega
theorem good_span_sum {pred : Fin n → Fin n → Bool}
    (h : ActionRuns pred q as r) (good : Fin n → Bool)
    (hg : ∀ v, good v = true → kind q v ≠ .pebble ∧
      CutBound.count .compute (events v as) = 1 ∧ CutBound.count .uncompute (events v as) = 1)
    (hs : r.space ≤ s) :
    ((List.finRange n).map fun v => if good v then time as v .unpebble - time as v .pebble else 0).sum ≤ as.length*s := by
  have hh : ((List.finRange n).map fun v => if good v then time as v .unpebble - time as v .pebble else 0).sum ≤
      ((List.finRange n).map fun v => Area.live v q as).sum := by
    apply Exceptions.sum_le
    intro v hv
    cases hp : good v with
    | false => simp
    | true =>
      simp only [ite_true]
      have hc := hg v hp
      exact good_span_bound h v hc.1 hc.2.1 hc.2.2
  rw [← Area.boundary_by_vertex] at hh
  exact Nat.le_trans hh (Nat.le_trans (Area.boundary_le_volume as q)
    (Nat.le_trans (Area.volume_cap h) (Nat.mul_le_mul_left as.length hs)))
#print axioms good_span_sum
#print axioms good_span_bound
#print axioms good_edge_nesting
#print axioms active_bracket_times
end Nesting
