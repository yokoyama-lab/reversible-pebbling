import RunCost
namespace PhysicalLinearBound
open LocalCertificate TerminalProjection

def placements : List Event → Nat
 | [] => 0
 | e::es => (if e.place then 1 else 0)+placements es

theorem reach_bound {p b es z c r} (h : Run p b es z c r) {B : Nat}
 (bound : ∀v∈b,v≤B) : ∀v∈z,v≤B+placements es := by
 induction h generalizing B with
 | nil => simpa [placements] using bound
 | @cons b a z es c r e hs ht ih =>
  cases hp : e.place with
  | true =>
   have he : e.vertex∉b ∧ pred b e.vertex ∧ a=e.vertex::b := by simpa [hp] using hs.2.2
   have ev : e.vertex≤B+1 := by
    rcases he.2.1 with h1 | hm
    · omega
    · have hh := bound (e.vertex-1) hm;omega
   have ba : ∀v∈a,v≤B+1 := by
    intro v hv
    rw [he.2.2] at hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact ev
    · have hh := bound v hv;omega
   have out := ih ba
   simpa [placements,hp,Nat.add_assoc] using out
  | false =>
   have he : e.vertex∈b ∧ a=b.erase e.vertex := by simpa [hp] using hs.2.2
   have ba : ∀v∈a,v≤B := by
    intro v hv;rw [he.2] at hv;exact bound v (List.mem_of_mem_erase hv)
   simpa [placements,hp] using ih ba

theorem event_balance {p b es z c r} (h : Run p b es z c r) :
 z.length+es.length=b.length+2*placements es := by
 induction h with
 | nil => simp [placements]
 | @cons b a z es c r e hs ht ih =>
  cases hp : e.place with
  | true =>
   have he : e.vertex∉b ∧ pred b e.vertex ∧ a=e.vertex::b := by simpa [hp] using hs.2.2
   rw [he.2.2] at ih
   simp only [List.length_cons,placements,hp,ite_true]
   simp only [List.length_cons] at ih
   omega
  | false =>
   have he : e.vertex∈b ∧ a=b.erase e.vertex := by simpa [hp] using hs.2.2
   have bl := List.length_pos_of_mem he.1
   have al : a.length=b.length-1 := by rw [he.2];exact List.length_erase_of_mem he.1
   simp only [List.length_cons,placements,hp,Bool.false_eq_true,ite_false]
   omega

theorem winning_event_lower {p n es c r} (h : Run p [] es [n] c r) :
 2*n≤es.length+1 := by
 have reach := reach_bound h (B:=0) (by simp) n (by simp)
 have bal := event_balance h
 simp only [List.length_cons,List.length_nil] at bal
 simp only [Nat.zero_add] at reach
 omega

theorem winning_cost_lower {p n es c r} (h : Run p [] es [n] c r) :
 2*n≤c+1 := by
 have bound := winning_event_lower h
 have cost := PhysicalRunCost.run_cost_identity h
 omega

#print axioms reach_bound
#print axioms event_balance
#print axioms winning_event_lower
#print axioms winning_cost_lower
end PhysicalLinearBound
