import GlobalSplit
namespace GlobalSplit
open LocalCertificate FamilyCut

def below : Nat → Event → Bool
  | 0, _ => false
  | n+1,e => below n e || FamilyCut.P (11+6*n) e

theorem below_iff (n : Nat) (e : Event) :
    below n e=true ↔ ∃ j, j<n ∧ e.place=true ∧ e.vertex=11+6*j := by
  induction n with
  | zero => simp [below]
  | succ n ih =>
    simp only [below,Bool.or_eq_true,ih,P,RemovalOrder.isPlacement,Bool.and_eq_true,beq_iff_eq]
    constructor
    · rintro (⟨j,hj,hp,hv⟩ | ⟨hp,hv⟩)
      · exact ⟨j,by omega,hp,hv⟩
      · exact ⟨n,by omega,hp,hv⟩
    · rintro ⟨j,hj,hp,hv⟩
      by_cases he : j=n
      · subst j; exact Or.inr ⟨hp,hv⟩
      · exact Or.inl ⟨j,by omega,hp,hv⟩

theorem count_or_disjoint (p q : Event → Bool) (xs : List Event)
    (hd : ∀ e∈xs, ¬(p e=true ∧ q e=true)) :
    xs.countP (fun e => p e || q e) = xs.countP p + xs.countP q := by
  induction xs with
  | nil => simp
  | cons e es ih =>
    have h := hd e (by simp)
    have ht := ih (fun x hx => hd x (by simp [hx]))
    cases hp : p e <;> cases hq : q e <;>
      simp_all [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem below_count (word : List Event) (n : Nat)
    (hc : ∀ j, j<n → word.countP (FamilyCut.P (11+6*j))=1) :
    word.countP (below n)=n := by
  induction n with
  | zero => simp [below]
  | succ n ih =>
    have old := ih (fun j hj => hc j (by omega))
    have fresh := hc n (by omega)
    have hd : ∀ e∈word, ¬(below n e=true ∧ FamilyCut.P (11+6*n) e=true) := by
      intro e he hh
      obtain ⟨j,hj,hp,hv⟩ := (below_iff n e).mp hh.1
      have hn : e.vertex=11+6*n := by
        have h := hh.2
        simpa [P,RemovalOrder.isPlacement] using (show e.place=true ∧ e.vertex=11+6*n from by
          simpa [P,RemovalOrder.isPlacement] using h) |>.2
      omega
    change word.countP (fun e => below n e || FamilyCut.P (11+6*n) e)=n+1
    rw [count_or_disjoint _ _ _ hd,old,fresh]

theorem trace_blocks_length (k : Nat) (erasures : List Nat) (word : List Event)
    (model : Trace k erasures word) :
    (splitMarkers marker word).1.length=k := by
  have eqc : word.countP marker = word.countP (below k) := by
    apply List.countP_congr
    intro e he
    exact (marker_trace_iff k erasures word model e he).trans (below_iff k e).symm
  rw [← split_marker_count,eqc]
  exact below_count word k (fun j hj => each_cut_count k j erasures word model hj)

#print axioms below_iff
#print axioms count_or_disjoint
#print axioms below_count
#print axioms trace_blocks_length
end GlobalSplit
