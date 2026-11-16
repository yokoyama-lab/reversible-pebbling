import CleanHandoffMeasure
namespace PermMeasure
open LocalCertificate TerminalProjection VisitMeasure CleanHandoffMeasure

theorem update_perm {b b' : List Nat} (h : b.Perm b') (e : Event) :
 (update b e).Perm (update b' e) := by
 cases hp : e.place
 · simpa [update,hp] using h.erase e.vertex
 · simpa [update,hp] using h.cons e.vertex

theorem singleton_iff {b b' : List Nat} (h : b.Perm b') (j : Nat) :
 b=[j] ↔ b'=[j] := by
 constructor
 · intro hb; subst b; simpa using h.symm
 · intro hb; subst b'; simpa using h

theorem singleton_visits_perm {b b' : List Nat} (h : b.Perm b') (es : List Event) (j : Nat) :
 (frames b es).count [j] = (frames b' es).count [j] := by
 induction es generalizing b b' with
 | nil => rfl
 | cons e es ih =>
  have hu := update_perm h e
  have he := singleton_iff hu j
  simp only [frames,List.count_cons]
  rw [ih hu]
  simp only [beq_iff_eq]
  simp only [he]

theorem bad_perm {b b' : List Nat} (h : b.Perm b') (n : Nat) (es : List Event) :
 bad n b es = bad n b' es := by
 induction es generalizing b b' with
 | nil => rfl
 | cons e es ih =>
  simp only [bad]
  rw [ih (update_perm h e)]
  have hl := h.length_eq
  cases b with
  | nil =>
   have hb : b'=[] := by simpa using h.symm
   subst b'
   rfl
  | cons j bs =>
   cases bs with
   | nil => have hb : b'=[j] := (singleton_iff h j).mp rfl; subst b'; rfl
   | cons k ks =>
    cases b' with
    | nil => simp at hl
    | cons j' bs' =>
     cases bs' with
     | nil => simp at hl
     | cons k' ks' => rfl

theorem rank_perm {b b' : List Nat} (h : b.Perm b') (n : Nat) (es : List Event) :
 rank (bad n b es) = rank (bad n b' es) := by rw [bad_perm h]

/-- Replacement may end at any permutation of the old cut board. All suffix
 fees, erasure counts, singleton visits and bad-vertex lists transport. -/
theorem replacement_decreases_perm {p n m pre replacement post P Q z c r d s ct rt}
 (old : Run p [] pre P c r) (new : Run p [] replacement Q d s)
 (cut : P.Perm Q) (tail : Run p P post z ct rt) (cost : d≤c)
 (witness : m∈bad n [] (pre++post))
 (lower : ∀j∈bad n [] replacement,j<m)
 (suffix : ∀j∈bad n P post,j<m) :
 ∃z', Run p [] (replacement++post) z' (d+ct) (s+rt) ∧ z.Perm z' ∧
 d+ct≤c+ct ∧ rank (bad n [] (replacement++post)) < rank (bad n [] (pre++post)) := by
 obtain ⟨z',ht,hz⟩ := SingletonVisit.run_perm tail cut
 have hb : ∀j∈bad n [] (replacement++post),j<m := by
  rw [bad_append,run_evolve new,←bad_perm cut]
  intro j hj
  rcases List.mem_append.mp hj with h | h
  · exact lower j h
  · exact suffix j h
 have hl := rank_le _ m hb
 have hr := member_rank witness
 exact ⟨z',run_append new ht,hz,by omega,by omega⟩

#print axioms update_perm
#print axioms singleton_iff
#print axioms singleton_visits_perm
#print axioms bad_perm
#print axioms rank_perm
#print axioms replacement_decreases_perm
end PermMeasure
