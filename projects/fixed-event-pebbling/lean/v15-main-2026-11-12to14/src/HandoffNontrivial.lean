import LastBad
import FirstUpperStructure
import MaxBad
namespace HandoffNontrivial
open LocalCertificate TerminalProjection TerminalExistence VisitMeasure LastBad CleanHandoffMeasure
/-- Price 9 makes every actual operation strictly positive. -/
theorem fee_positive (b : List Nat) (e : Event) : 1≤fee b e := by
 simp only [fee]; split <;> simp_all; split <;> omega

theorem nonempty_cost_positive {p b es z c r}
 (h : Run p b es z c r) (ne : es≠[]) : 0<c := by
 cases h with
 | nil => exact False.elim (ne rfl)
 | @cons b a z es c r e hs ht => have hp := fee_positive b e; omega

/-- Any nonempty exact return can be removed, strictly improving price-9 cost. -/
theorem delete_return {p initial pre loop post b z c1 r1 c2 r2 c3 r3}
 (hp : Run p initial pre b c1 r1) (hl : Run p b loop b c2 r2)
 (ht : Run p b post z c3 r3) (ne : loop≠[]) :
 Run p initial (pre++post) z (c1+c3) (r1+r3) ∧
 c1+c3<c1+c2+c3 := by
 have hc := nonempty_cost_positive hl ne
 exact ⟨run_append hp ht,by omega⟩

def CostMinimal (p : Nat) (initial z : List Nat) (c : Nat) : Prop :=
 ∀es d s, Run p initial es z d s → c≤d

/-- The pre-upper board cannot be singleton again: the intervening word
 contains the original bad move, hence is nonempty. Lastness is not needed. -/
theorem optimal_no_return {p initial pre middle post m P z c c1 r1 c2 r2 c3 r3}
 (minimal : CostMinimal p initial z c)
 (hp : Run p initial pre [m] c1 r1)
 (hm : Run p [m] middle P c2 r2)
 (ht : Run p P post z c3 r3)
 (cost : c=c1+c2+c3) (nonempty : middle≠[]) : P≠[m] := by
 intro eq
 subst P
 obtain ⟨run,lt⟩ := delete_return hp hm ht nonempty
 have lower := minimal _ _ _ run
 omega

/-- A complete extraction suitable for the existing last-bad decomposition.
The first upper move is included in the unchanged suffix. -/
theorem pre_upper_not_singleton {p initial pre m e a rest z c c1 r1 c2 r2}
 (minimal : CostMinimal p initial z c)
 (hp : Run p initial pre [m] c1 r1)
 (hs : Step p [m] e a) (ht : Run p a rest z c2 r2)
 (cost : c=c1+fee [m] e+c2) (lower : e.vertex≤m)
 (upper : ∃f∈e::rest,m<f.vertex) :
 ∃middle f suffix P d s t u,
 e::rest=middle++f::suffix ∧ middle≠[] ∧
 (∀g∈middle,g.vertex≤m) ∧ m<f.vertex ∧
 Run p [m] middle P d s ∧ Run p P (f::suffix) z t u ∧
 P≠[m] ∧ c=c1+d+t := by
 obtain ⟨middle,f,suffix,word,bound,hf⟩ := first_upper upper
 have ne : middle≠[] := by
  intro he
  simp only [he,List.nil_append,List.cons.injEq] at word
  have hv : e.vertex=f.vertex := congrArg Event.vertex word.1
  omega
 have full := Run.cons hs ht
 rw [word] at full
 obtain ⟨P,d,s,t,u,hmid,hsuf,hc,hr⟩ := run_split full
 have total : c=c1+d+t := by omega
 exact ⟨middle,f,suffix,P,d,s,t,u,word,ne,bound,hf,hmid,hsuf,
   optimal_no_return minimal hp hmid hsuf total ne,total⟩
theorem nontrivial_perm {P : List Nat} {m : Nat} (h : P≠[m]) : ¬P.Perm [m] := by
 intro hp; exact h hp.eq_singleton

/-- Discharges m=0 and m=1 once the actual target board bounds are supplied. -/
theorem target_forces_two {P : List Nat} {m : Nat}
 (nd : P.Nodup) (member : m∈P)
 (bounds : ∀v∈P,1≤v ∧ v≤m) (ne : P≠[m]) : 2≤m := by
 apply Classical.byContradiction
 intro small
 have mm : m≤1 := by omega
 cases P with
 | nil => simp at member
 | cons a tail =>
  have ha := bounds a (by simp)
  have am : a=m := by omega
  cases tail with
  | nil => exact ne (by simp [am])
  | cons b tail =>
   have hb := bounds b (by simp)
   have ab : a=b := by omega
   have hn := (List.nodup_cons.mp nd).1
   exact hn (by simp [ab])
theorem actual_target_conditions {p pre m e a rest z c c1 r1 c2 r2}
 (minimal : CostMinimal p [] z c)
 (hp : Run p [] pre [m] c1 r1)
 (hs : Step p [m] e a) (ht : Run p a rest z c2 r2)
 (cost : c=c1+fee [m] e+c2) (lower : e.vertex≤m)
 (upper : ∃f∈e::rest,m<f.vertex) :
 ∃middle f suffix P d s t u,
 e::rest=middle++f::suffix ∧
 Run p [m] middle P d s ∧ Run p P (f::suffix) z t u ∧
 (∀g∈middle,g.vertex≤m) ∧ (∀v∈P,1≤v ∧ v≤m) ∧
 m∈P ∧ P.length≤p-1 ∧ ¬P.Perm [m] ∧ 2≤m ∧ c=c1+d+t := by
 obtain ⟨middle,f,suffix,P,d,s,t,u,word,ne,low,above,mid,tail,nontriv,total⟩ :=
  pre_upper_not_singleton minimal hp hs ht cost lower upper
 have positive := MaxBad.singleton_positive hp
 have pb := FirstUpperStructure.low_run_bounded mid (by simp) low
 have pos := MaxBad.board_positive (run_append hp mid) (by simp)
 have nd := run_nodup (by simp : ([] : List Nat).Nodup) (run_append hp mid)
 have all : ∀v∈P,1≤v ∧ v≤m := by intro v hv; exact ⟨pos v hv,pb v hv⟩
 have data : m∈P ∧ P.length≤p-1 := by
  cases tail with
  | cons hstep hrest =>
   obtain ⟨_,_,hm,hcap⟩ := FirstUpperStructure.step_above_positive_bound positive hstep pb above
   exact ⟨hm,hcap⟩
 exact ⟨middle,f,suffix,P,d,s,t,u,word,mid,tail,low,all,data.1,data.2,
  nontrivial_perm nontriv,target_forces_two nd data.1 all nontriv,total⟩
#print axioms actual_target_conditions
#print axioms target_forces_two
#print axioms delete_return
#print axioms optimal_no_return
#print axioms pre_upper_not_singleton
end HandoffNontrivial
