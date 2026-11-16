import HeapForest
namespace Coverage
open HeapForest

def leaves : Nat → Nat → List Nat
 | 0,i => [i]
 | h+1,i => leaves h (2*i+1) ++ leaves h (2*i+2)

theorem grow (h i : Nat) : (labels (h+1) i).Perm (labels h i ++ leaves h i) := by
  induction h generalizing i with
  | zero => simp [labels,leaves]
  | succ h ih =>
    simp only [labels,leaves]
    have hp := (ih (2*i+1)).append (ih (2*i+2))
    apply (hp.cons i).trans
    have hm := List.perm_append_comm_assoc (leaves h (2*i+1)) (labels h (2*i+2)) (leaves h (2*i+2))
    have hh := hm.append_left (labels h (2*i+1))
    simpa only [List.append_assoc,List.cons_append] using hh.cons i

theorem leaves_range (h i : Nat) :
    leaves h i = List.range' (2^h*i+(2^h-1)) (2^h) := by
  induction h generalizing i with
  | zero => simp [leaves,List.range']
  | succ h ih =>
    rw [leaves,ih,ih]
    have hp : 0 < 2^h := Nat.pow_pos (by decide)
    have hleft : 2^h*(2*i+1)+(2^h-1) = 2^(h+1)*i+(2^(h+1)-1) := by
      simp only [Nat.pow_succ,Nat.mul_add,Nat.mul_one]
      simp only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
      omega
    have hright : 2^h*(2*i+2)+(2^h-1) = (2^(h+1)*i+(2^(h+1)-1))+2^h := by
      simp only [Nat.pow_succ,Nat.mul_add,Nat.mul_one]
      simp only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
      omega
    rw [hleft,hright,List.range'_append_1]
    congr 1
    simp [Nat.pow_succ,Nat.mul_two]

theorem cover_range (h : Nat) : (labels h 0).Perm (List.range (2^h-1)) := by
  induction h with
  | zero => simp [labels]
  | succ h ih =>
    have hh := (grow h 0).trans (ih.append (List.Perm.refl (leaves h 0)))
    rw [leaves_range] at hh
    simp only [Nat.mul_zero,Nat.zero_add] at hh
    rw [List.range_eq_range'] at hh ⊢
    have hh' : List.range' 0 (2^h-1) ++ List.range' (2^h-1) (2^h) =
        List.range' 0 ((2^h-1)+2^h) := by simpa using (List.range'_append_1 (s:=0) (m:=2^h-1) (n:=2^h))
    rw [hh'] at hh
    have hp : 0 < 2^h := Nat.pow_pos (by decide)
    have he : (2^h-1)+2^h = 2^(h+1)-1 := by rw [Nat.pow_succ]; omega
    rw [he] at hh
    exact hh

theorem fin_values (n : Nat) : (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem <;> simp

theorem all_height_coverage (h : Nat) :
    (labels h 0).Perm ((List.finRange (2^h-1)).map Fin.val) := by
  rw [fin_values]
  exact cover_range h
theorem all_height_components (H : Nat) (pre post : List SpookyRound.Action)
    (c : SpookyRound.Config (2^H-1)) (root : Fin (2^H-1))
    (hr : c.peb root = true) :
    Forest.components false (embed (lift (goodAt post c)) H 0) ≤
      2*Exceptions.removed (Exceptions.accounts pre post c root)+1 :=
  component_account_bound pre post c root hr H (all_height_coverage H)

theorem paper_forest_components (H : Nat) (hn : 0 < 2^H-1)
    {q : SpookyRound.Config (2^H-1)} {r : SpookyDP.Result (SpookyRound.Config (2^H-1))}
    (h : SpookyRound.PaperRuns HeapPath.pred d q r)
    (hs : ∀ u, TraceBridge.kind q u ≠ .pebble)
    (hr : TraceBridge.kind r.state ⟨0,hn⟩ = .pebble)
    (hf : ∀ u : Fin (2^H-1), 0 < u.val → TraceBridge.kind r.state u = .empty)
    (hw : r.work ≤ 3*(2^H-1)+e) (hspace : r.space ≤ s) :
    ∃ pre a post c, (pre ++ a :: post).length = d ∧
      TraceBridge.ActionRuns HeapPath.pred q (pre ++ a :: post) r ∧
      c.peb ⟨0,hn⟩ = true ∧ CutSpace.pebs c ≤ s ∧
      Exceptions.removed (Exceptions.accounts (pre++[a]) post c ⟨0,hn⟩) ≤ e+2*s+1 ∧
      Forest.components false (embed (lift (goodAt post c)) H 0) ≤ 2*e+4*s+3 := by
  obtain ⟨pre,a,post,c,hd,ha,hc,hp,hb⟩ := CutSpace.paper_exception_bound hn h hs hr hf hw hspace
  exact ⟨pre,a,post,c,hd,ha,hc,hp,hb,
    component_budget (pre++[a]) post c ⟨0,hn⟩ hc H (all_height_coverage H) hb⟩
#print axioms paper_forest_components
#print axioms all_height_coverage
end Coverage
