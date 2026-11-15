import Descendants
namespace HeapPath
open SpookyRound TraceBridge Descendants

def pred (v u : Fin n) : Bool := decide (0 < u.val ∧ v.val = (u.val-1)/2)

theorem heap_paths (hn : 0 < n) (final : Config n)
    (hf : ∀ u : Fin n, 0 < u.val → kind final u = .empty)
    (u : Fin n) : Path pred final ⟨0,hn⟩ u := by
  have general : ∀ k, ∀ u : Fin n, u.val = k → Path pred final ⟨0,hn⟩ u := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro u hk
      by_cases hz : k = 0
      · have hu : u = ⟨0,hn⟩ := by apply Fin.ext; change u.val = 0; omega
        rw [hu]; exact Path.refl _
      · have hpos : 0 < u.val := by omega
        let p : Fin n := ⟨(u.val-1)/2, by omega⟩
        have hlt : p.val < k := by dsimp [p]; omega
        have hp := ih p.val hlt p rfl
        apply Path.step hp
        · intro heq; have hh := congrArg Fin.val heq; dsimp [p] at hh; omega
        · simp [pred,p,hpos]
        · exact hf u hpos
  exact general u.val u rfl

theorem sum_add (xs : List α) (f g : α → Nat) :
    (xs.map fun x => f x + g x).sum = (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons,List.sum_cons]; rw [ih]; omega

theorem exchange (xs : List α) (ys : List β) (f : α → β → Nat) :
    (xs.map fun x => (ys.map (f x)).sum).sum =
      (ys.map fun y => (xs.map fun x => f x y).sum).sum := by
  induction xs with
  | nil =>
    simp only [List.map_nil,List.sum_nil]
    induction ys with
    | nil => rfl
    | cons y ys ih => simpa using ih
  | cons x xs ih =>
    simp only [List.map_cons,List.sum_cons]
    rw [sum_add,ih]

theorem heap_cleanup (hn : 0 < n) (h : ActionRuns pred q as r)
    (hf : ∀ u : Fin n, 0 < u.val → kind r.state u = .empty)
    (hb : ∀ u : Fin n, pred ⟨0,hn⟩ u = true →
      ∃ a ∈ as, firstAt a u = .unpebble)
    (u : Fin n) (hu : 0 < u.val) : ∃ a ∈ as, firstAt a u = .unpebble := by
  have general : ∀ k, ∀ u : Fin n, u.val = k → 0 < k →
      ∃ a ∈ as, firstAt a u = .unpebble := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro u hk hpos
      let p : Fin n := ⟨(u.val-1)/2,by omega⟩
      have hlt : p.val < k := by dsimp [p]; omega
      have he : pred p u = true := by simp [pred,p]; omega
      by_cases hz : p.val = 0
      · have hp : p = ⟨0,hn⟩ := by apply Fin.ext; exact hz
        rw [hp] at he
        exact hb u he
      · obtain ⟨a,ha,hh⟩ := ih p.val hlt p rfl (by omega)
        apply cleanup_propagates h p u
        · intro heq; have hv := congrArg Fin.val heq; omega
        · exact he
        · exact hf u (by omega)
        · exact ⟨a,ha,by simp [hh]⟩
  exact general u.val u rfl hu
#print axioms heap_cleanup
#print axioms heap_paths
#print axioms exchange
end HeapPath
