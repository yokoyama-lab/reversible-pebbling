import Coverage
namespace DepthArea
open Forest

def shallow (ell : Nat) (t : Tree) : Nat := ((depths 0 t).filter fun d => decide (d<ell)).length

theorem level_exact (t : Tree) (k d : Nat) :
    level k d t = ((depths d t).filter fun j => decide (j=k)).length := by
  induction t generalizing d with
  | nil => rfl
  | node keep l r il ir =>
    cases keep <;> simp [level,depths,List.filter_append,il,ir] <;> split <;> simp_all <;> omega

theorem count_succ (ds : List Nat) (ell : Nat) :
    (ds.filter fun d => decide (d<ell+1)).length =
      (ds.filter fun d => decide (d<ell)).length + (ds.filter fun d => decide (d=ell)).length := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    by_cases hlt : d<ell
    · have hn : d<ell+1 := by omega
      have he : ¬d=ell := by omega
      simp [hlt,hn,he,ih]; omega
    · by_cases he : d=ell
      · subst d; simp [ih]; omega
      · have hn : ¬d<ell+1 := by omega
        simp [hlt,he,hn,ih]

theorem shallow_bound (t : Tree) (ell : Nat) :
    shallow ell t ≤ components false t*(2^ell-1) := by
  induction ell with
  | zero => simp [shallow]
  | succ ell ih =>
    have hl := level_bound t ell
    have he : shallow (ell+1) t = shallow ell t + level ell 0 t := by
      simp only [shallow,level_exact,count_succ]
    rw [he]
    have hp : 0<2^ell := Nat.pow_pos (by decide)
    have hc : (2^ell-1)+2^ell=2^(ell+1)-1 := by rw [Nat.pow_succ]; omega
    calc
      shallow ell t+level ell 0 t ≤ components false t*(2^ell-1)+components false t*2^ell := Nat.add_le_add ih hl
      _ = components false t*((2^ell-1)+2^ell) := (Nat.mul_add _ _ _).symm
      _ = components false t*(2^(ell+1)-1) := by rw [hc]
def pairs (keep : Nat → Bool) : Nat → Nat → Nat → List (Nat × Nat)
 | 0,_,_ => []
 | h+1,i,d => if keep i then (i,d)::(pairs keep h (2*i+1) (d+1) ++ pairs keep h (2*i+2) (d+1))
                 else pairs keep h (2*i+1) 0 ++ pairs keep h (2*i+2) 0

theorem pair_depths (keep : Nat → Bool) (h i d : Nat) :
    (pairs keep h i d).map Prod.snd = depths d (HeapForest.embed keep h i) := by
  induction h generalizing i d with
  | zero => rfl
  | succ h ih => cases hk : keep i <;> simp [pairs,HeapForest.embed,depths,hk,ih]

theorem depth_span (keep : Nat → Bool) (C U : Nat → Nat)
    (valid : ∀ i, keep i=true → C i < U i)
    (nested : ∀ i j, j=2*i+1 ∨ j=2*i+2 → keep i=true → keep j=true → C j<C i ∧ U i<U j)
    (h i d : Nat) (incoming : keep i=true → 2*d+1 ≤ U i-C i) :
    ∀ vd ∈ pairs keep h i d, 2*vd.2+1 ≤ U vd.1-C vd.1 := by
  induction h generalizing i d with
  | zero => simp [pairs]
  | succ h ih =>
    cases hk : keep i with
    | false =>
      intro vd hm
      simp only [pairs,hk,Bool.false_eq_true,ite_false,List.mem_append] at hm
      rcases hm with hm|hm
      · apply ih (2*i+1) 0 (fun hj => by have hh := valid (2*i+1) hj; omega) vd hm
      · apply ih (2*i+2) 0 (fun hj => by have hh := valid (2*i+2) hj; omega) vd hm
    | true =>
      have hi := incoming hk
      have hv := valid i hk
      have left : keep (2*i+1)=true → 2*(d+1)+1 ≤ U (2*i+1)-C (2*i+1) := by
        intro hj
        have hh := nested i (2*i+1) (Or.inl rfl) hk hj
        omega
      have right : keep (2*i+2)=true → 2*(d+1)+1 ≤ U (2*i+2)-C (2*i+2) := by
        intro hj
        have hh := nested i (2*i+2) (Or.inr rfl) hk hj
        omega
      intro vd hm
      simp only [pairs,hk,ite_true,List.mem_cons,List.mem_append] at hm
      rcases hm with hm | hm | hm
      · subst vd; exact hi
      · exact ih (2*i+1) (d+1) left vd hm
      · exact ih (2*i+2) (d+1) right vd hm
open SpookyRound TraceBridge

theorem good_order {pred : Fin n → Fin n → Bool}
    (h : ActionRuns pred q as r) (v : Fin n)
    (hs : kind q v ≠ .pebble) (hc : CutBound.count .compute (events v as)=1)
    (hu : CutBound.count .uncompute (events v as)=1) :
    Nesting.time as v .pebble < Nesting.time as v .unpebble := by
  obtain ⟨xs,c,mid,u,tail,he,hcM,huM,hn⟩ := GoodInterval.good_decomposition h v hs hc hu
  subst as
  have hsplit : xs++c::(mid++u::tail) = (xs++c::mid)++u::tail := by simp
  have tc := Nesting.time_unique xs _ c v .pebble .compute (Or.inl ⟨rfl,rfl⟩) hcM hc
  have hu' : CutBound.count .uncompute (events v ((xs++c::mid)++u::tail))=1 := by rw [← hsplit]; exact hu
  have tu := Nesting.time_unique _ tail u v .unpebble .uncompute (Or.inr ⟨rfl,rfl⟩) huM hu'
  rw [← hsplit] at tu
  rw [tc,tu]
  simp

def clockLift (as : List Action) (m : Move) (n i : Nat) : Nat :=
  if hi : i<n then Nesting.time as ⟨i,hi⟩ m else 0

theorem actual_depth_span {n : Nat} {q : Config n} {r : SpookyDP.Result (Config n)}
    (h : ActionRuns HeapPath.pred q as r)
    (hf : ∀ v : Fin n, 0<v.val → kind r.state v=.empty)
    (H : Nat) : ∀ vd ∈ pairs (HeapForest.lift (HeapForest.goodAt as q)) H 0 0,
      2*vd.2+1 ≤ clockLift as .unpebble n vd.1-clockLift as .pebble n vd.1 := by
  let keep := HeapForest.lift (HeapForest.goodAt as q)
  let C := clockLift as .pebble n
  let U := clockLift as .unpebble n
  have valid : ∀ i, keep i=true → C i<U i := by
    intro i hk
    by_cases hi : i<n
    · have hg : HeapForest.goodAt as q ⟨i,hi⟩=true := by simpa [keep,HeapForest.lift,hi] using hk
      have hs := HeapForest.good_semantics as q ⟨i,hi⟩ hg
      simpa [C,U,clockLift,hi] using good_order h ⟨i,hi⟩ hs.1 hs.2.1 hs.2.2
    · simp [keep,HeapForest.lift,hi] at hk
  have nested : ∀ i j, j=2*i+1 ∨ j=2*i+2 → keep i=true → keep j=true → C j<C i ∧ U i<U j := by
    intro i j hedge hki hkj
    by_cases hi : i<n
    · by_cases hj : j<n
      · have hgi : HeapForest.goodAt as q ⟨i,hi⟩=true := by simpa [keep,HeapForest.lift,hi] using hki
        have hgj : HeapForest.goodAt as q ⟨j,hj⟩=true := by simpa [keep,HeapForest.lift,hj] using hkj
        have si := HeapForest.good_semantics as q ⟨i,hi⟩ hgi
        have sj := HeapForest.good_semantics as q ⟨j,hj⟩ hgj
        have hn : (⟨i,hi⟩ : Fin n) ≠ ⟨j,hj⟩ := by intro he; have hh := congrArg Fin.val he; simp at hh; omega
        have he : HeapPath.pred (⟨i,hi⟩ : Fin n) ⟨j,hj⟩=true := by simp [HeapPath.pred]; omega
        have hh := Nesting.good_edge_nesting h ⟨i,hi⟩ ⟨j,hj⟩ hn he si.1 sj.1
          (hf ⟨j,hj⟩ (by simp; omega)) si.2.1 si.2.2 sj.2.1 sj.2.2
        simpa [C,U,clockLift,hi,hj] using And.intro hh.1 hh.2.2
      · simp [keep,HeapForest.lift,hj] at hkj
    · simp [keep,HeapForest.lift,hi] at hki
  exact depth_span keep C U valid nested H 0 0 (fun hk => by have hh := valid 0 hk; omega)
#print axioms actual_depth_span
#print axioms depth_span
#print axioms shallow_bound
end DepthArea
