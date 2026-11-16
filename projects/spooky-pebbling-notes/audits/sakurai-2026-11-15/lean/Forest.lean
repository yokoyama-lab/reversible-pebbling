import Nesting
namespace Forest
-- Keep=true vertices survive deletion; empty branches are permitted.
inductive Tree where
 | nil
 | node (keep : Bool) (left right : Tree)

def size : Tree → Nat | .nil => 0 | .node _ l r => 1+size l+size r
def bad : Tree → Nat | .nil => 0 | .node k l r => (if k then 0 else 1)+bad l+bad r
def good : Tree → Nat | .nil => 0 | .node k l r => (if k then 1 else 0)+good l+good r
-- An induced component starts exactly at a kept vertex whose parent is absent.
def components (parentKept : Bool) : Tree → Nat
 | .nil => 0
 | .node k l r => (if k && !parentKept then 1 else 0)+components k l+components k r

theorem partition (t : Tree) : good t + bad t = size t := by
  induction t with
  | nil => rfl
  | node k l r il ir => cases k <;> simp_all [good,bad,size] <;> omega

theorem component_bound (t : Tree) (p : Bool) :
    components p t ≤ 2*bad t + (if p then 0 else 1) := by
  induction t generalizing p with
  | nil => simp [components,bad]
  | node k l r il ir =>
    have hl := il k
    have hr := ir k
    cases k <;> cases p <;> simp_all [components,bad] <;> omega

theorem forest_bound (t : Tree) : components false t ≤ 2*bad t+1 := component_bound t false

-- Direct root enumeration provides a check that component count is not an
-- unrelated numerical recurrence: every listed root is an actual kept node.
def rootFlags (p : Bool) : Tree → List Bool
 | .nil => []
 | .node k l r => (k && !p)::(rootFlags k l ++ rootFlags k r)

theorem roots_exact (t : Tree) (p : Bool) :
    components p t = ((rootFlags p t).filter id).length := by
  induction t generalizing p with
  | nil => rfl
  | node k l r il ir =>
    have hl := il k
    have hr := ir k
    cases k <;> cases p <;> simp_all [components,rootFlags,List.filter_append] <;> omega

-- Component-depth: consecutive kept ancestors only, reset after a deletion.
def depths (d : Nat) : Tree → List Nat
 | .nil => []
 | .node k l r => if k then d::(depths (d+1) l ++ depths (d+1) r)
                 else depths 0 l ++ depths 0 r

theorem depths_count (t : Tree) (d : Nat) : (depths d t).length = good t := by
  induction t generalizing d with
  | nil => rfl
  | node k l r il ir => cases k <;> simp [depths,good,il,ir,Nat.add_assoc] <;> omega
def level (target d : Nat) : Tree → Nat
 | .nil => 0
 | .node k l r => if k then (if d=target then 1 else 0)+level target (d+1) l+level target (d+1) r
                 else level target 0 l+level target 0 r

theorem next_level (t : Tree) (k d : Nat) :
    level (k+1) d t ≤ 2*level k d t + (if d=k+1 then 1 else 0) := by
  induction t generalizing d with
  | nil => simp [level]
  | node keep l r il ir =>
    cases keep with
    | false =>
      have hl := il 0
      have hr := ir 0
      simp only [level,Bool.false_eq_true,ite_false] at *
      simp at hl hr
      split <;> omega
    | true =>
      have hl := il (d+1)
      have hr := ir (d+1)
      simp only [level,ite_true] at *
      by_cases hd : d=k
      · subst d; simp at hl hr ⊢; omega
      · simp [hd] at hl hr ⊢
        split <;> omega
theorem zero_level (t : Tree) (d : Nat) :
    level 0 d t = components (decide (0<d)) t := by
  induction t generalizing d with
  | nil => rfl
  | node k l r il ir =>
    cases k <;> cases d <;> simp [level,components,il,ir]

theorem level_bound (t : Tree) (k : Nat) :
    level k 0 t ≤ components false t * 2^k := by
  induction k with
  | zero => simp [zero_level]
  | succ k ih =>
    have hn := next_level t k 0
    simp at hn
    have hm := Nat.mul_le_mul_left 2 ih
    simpa [Nat.pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using (Nat.le_trans hn hm)
#print axioms level_bound
#print axioms next_level
#print axioms forest_bound
#print axioms roots_exact
#print axioms depths_count
end Forest
