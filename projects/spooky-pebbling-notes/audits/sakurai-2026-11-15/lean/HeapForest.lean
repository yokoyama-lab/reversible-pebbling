import Forest
namespace HeapForest
open SpookyRound TraceBridge

def labels : Nat → Nat → List Nat
 | 0,_ => []
 | h+1,i => i :: (labels h (2*i+1) ++ labels h (2*i+2))
def embed (keep : Nat → Bool) : Nat → Nat → Forest.Tree
 | 0,_ => .nil
 | h+1,i => .node (keep i) (embed keep h (2*i+1)) (embed keep h (2*i+2))
def lift (keep : Fin n → Bool) (i : Nat) : Bool := if h : i<n then keep ⟨i,h⟩ else false

theorem bad_labels (keep : Nat → Bool) (h i : Nat) :
    Forest.bad (embed keep h i) = ((labels h i).map fun j => if keep j then 0 else 1).sum := by
  induction h generalizing i with
  | zero => rfl
  | succ h ih => simp [embed,labels,Forest.bad,ih,List.sum_append,Nat.add_assoc]

theorem perm_sum {xs ys : List Nat} (h : xs.Perm ys) : xs.sum = ys.sum := by
  induction h with
  | nil => rfl
  | cons a h ih => simp [ih]
  | swap a b xs => simp [Nat.add_comm,Nat.add_left_comm]
  | trans h1 h2 i1 i2 => exact i1.trans i2

theorem bad_fin (keep : Fin n → Bool) (h : Nat)
    (cover : (labels h 0).Perm ((List.finRange n).map Fin.val)) :
    Forest.bad (embed (lift keep) h 0) = ((List.finRange n).map fun v => if keep v then 0 else 1).sum := by
  rw [bad_labels]
  have hp := cover.map (fun j => if lift keep j then 0 else 1)
  rw [perm_sum hp,List.map_map]
  simp [lift,Function.comp_def]

def goodAt (post : List Action) (c : Config n) (v : Fin n) : Bool :=
  !c.peb v && decide (CutBound.count .compute (events v post)=1 ∧ CutBound.count .uncompute (events v post)=1)

theorem bad_removed (pre post : List Action) (c : Config n) (root : Fin n)
    (hr : c.peb root = true) :
    ((List.finRange n).map fun v => if goodAt post c v then 0 else 1).sum =
      Exceptions.removed (Exceptions.accounts pre post c root) := by
  unfold Exceptions.removed CutBound.pebbles Exceptions.accounts
  simp only [List.map_map]
  rw [← HeapPath.sum_add]
  congr 1
  apply List.map_congr_left
  intro v hv
  simp only [Function.comp_apply,Exceptions.exceptional,goodAt]
  by_cases he : v=root
  · subst v; simp [hr]
  · by_cases hp : c.peb v = true
    · simp [hp,he]
    · simp [hp,he]
      split <;> simp_all

theorem component_account_bound (pre post : List Action) (c : Config n) (root : Fin n)
    (hr : c.peb root = true) (h : Nat)
    (cover : (labels h 0).Perm ((List.finRange n).map Fin.val)) :
    Forest.components false (embed (lift (goodAt post c)) h 0) ≤
      2*Exceptions.removed (Exceptions.accounts pre post c root)+1 := by
  have hh := Forest.forest_bound (embed (lift (goodAt post c)) h 0)
  rw [bad_fin _ h cover,bad_removed pre post c root hr] at hh
  exact hh

theorem good_semantics (post : List Action) (c : Config n) (v : Fin n)
    (hg : goodAt post c v = true) :
    kind c v ≠ .pebble ∧ CutBound.count .compute (events v post)=1 ∧
      CutBound.count .uncompute (events v post)=1 := by
  have hh : c.peb v = false ∧ (CutBound.count .compute (events v post)=1 ∧
      CutBound.count .uncompute (events v post)=1) := by simpa [goodAt] using hg
  refine ⟨?_,hh.2⟩
  cases hp : c.ghost v <;> simp [kind,hh.1,hp]

theorem actual_good_area {pred : Fin n → Fin n → Bool}
    (h : ActionRuns pred c post t) (hs : t.space ≤ s) :
    ((List.finRange n).map fun v => if goodAt post c v then
      Nesting.time post v .unpebble - Nesting.time post v .pebble else 0).sum ≤ post.length*s :=
  Nesting.good_span_sum h (goodAt post c) (good_semantics post c) hs

theorem component_budget (pre post : List Action) (c : Config n) (root : Fin n)
    (hr : c.peb root=true) (h : Nat)
    (cover : (labels h 0).Perm ((List.finRange n).map Fin.val))
    (hb : Exceptions.removed (Exceptions.accounts pre post c root) ≤ e+2*s+1) :
    Forest.components false (embed (lift (goodAt post c)) h 0) ≤ 2*e+4*s+3 := by
  have hh := component_account_bound pre post c root hr h cover
  omega

-- Finite coverage certificates, not a proof for all heights.
theorem cover7 : (labels 3 0).Perm ((List.finRange 7).map Fin.val) := by decide
theorem cover15 : (labels 4 0).Perm ((List.finRange 15).map Fin.val) := by decide
theorem cover31 : (labels 5 0).Perm ((List.finRange 31).map Fin.val) := by decide
#print axioms actual_good_area
#print axioms component_budget
#print axioms component_account_bound
#print axioms cover31
end HeapForest
