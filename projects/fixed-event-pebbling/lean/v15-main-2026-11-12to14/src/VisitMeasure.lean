import TerminalProjection
namespace VisitMeasure
open TerminalProjection LocalCertificate
def update (b : List Nat) (e : Event) := if e.place then e.vertex::b else b.erase e.vertex
def evolve (b : List Nat) : List Event → List Nat
 | [] => b
 | e::es => evolve (update b e) es
def frames (b : List Nat) : List Event → List (List Nat)
 | [] => []
 | e::es => update b e :: frames (update b e) es
theorem step_update {p b a e} (h : Step p b e a) : update b e=a := by
 cases hp : e.place with
 | true => have he : e.vertex∉b ∧ pred b e.vertex ∧ a=e.vertex::b := by simpa [hp] using h.2.2
           simpa [update,hp] using he.2.2.symm
 | false => have he : e.vertex∈b ∧ a=b.erase e.vertex := by simpa [hp] using h.2.2
            simpa [update,hp] using he.2.symm
theorem run_evolve {p b es z c r} (h : Run p b es z c r) : evolve b es=z := by
 induction h with
 | nil => rfl
 | cons hs hr ih => simpa only [evolve,step_update hs] using ih
theorem evolve_append (b) (xs ys : List Event) : evolve b (xs++ys)=evolve (evolve b xs) ys := by
 induction xs generalizing b with
 | nil => rfl
 | cons e es ih => simp only [List.cons_append,evolve,ih]
theorem frames_append (b) (xs ys : List Event) : frames b (xs++ys)=frames b xs ++ frames (evolve b xs) ys := by
 induction xs generalizing b with
 | nil => rfl
 | cons e es ih => simp only [List.cons_append,frames,evolve,ih]
theorem swap_visit_drop (m q : Nat) (hq : 2≤q) (hqm : q<m) :
 (frames [m,q] [⟨false,q⟩,⟨true,1⟩]).count [m] =
 (frames [m,q] [⟨true,1⟩,⟨false,q⟩]).count [m] + 1 := by
 have hmq : m≠q := by omega
 have hq1 : 1≠q := by omega
 simp [frames,update,hmq,hq1]
theorem swap_context_visit_drop {p pre c r} (m q : Nat)
 (hp : Run p [] pre [m,q] c r) (post : List Event) (hq : 2≤q) (hqm : q<m) :
 (frames [] (pre++[⟨false,q⟩,⟨true,1⟩]++post)).count [m] =
 (frames [] (pre++[⟨true,1⟩,⟨false,q⟩]++post)).count [m]+1 := by
 have he := run_evolve hp
 have hmq : m≠q := by omega
 have hq1 : 1≠q := by omega
 have hlocal := swap_visit_drop m q hq hqm
 simp only [frames_append,evolve_append,he,List.count_append]
 have eo : evolve [m,q] [⟨false,q⟩,⟨true,1⟩]=[1,m] := by simp [evolve,update,hmq]
 have en : evolve [m,q] [⟨true,1⟩,⟨false,q⟩]=[1,m] := by simp [evolve,update,hmq,hq1]
 rw [eo,en]
 omega
#print axioms run_evolve
#print axioms frames_append
#print axioms swap_visit_drop
#print axioms swap_context_visit_drop
end VisitMeasure
