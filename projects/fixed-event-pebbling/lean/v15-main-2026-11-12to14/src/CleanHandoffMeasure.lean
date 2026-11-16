import BypassOptimal
namespace CleanHandoffMeasure
open LocalCertificate TerminalProjection VisitMeasure
/-- Bad vertices, not move indices. The initial board is inspected before each move. -/
def bad (n : Nat) (b : List Nat) : List Event → List Nat
 | [] => []
 | e::es => (match b with
   | [j] => if j<n ∧ e.vertex≤j then [j] else []
   | _ => []) ++ bad n (update b e) es

theorem bad_append (n b) (xs ys : List Event) :
 bad n b (xs++ys)=bad n b xs ++ bad n (evolve b xs) ys := by
 induction xs generalizing b with
 | nil => simp [bad,evolve]
 | cons e xs ih => simp only [List.cons_append,bad,ih,evolve,List.append_assoc]

def rank : List Nat → Nat
 | [] => 0
 | j::js => max (j+1) (rank js)

theorem rank_le (xs : List Nat) (m : Nat) (h : ∀j∈xs,j<m) : rank xs≤m := by
 induction xs with
 | nil => simp [rank]
 | cons j js ih =>
  have hj := h j (by simp)
  have ht := ih (by intro i hi; exact h i (by simp [hi]))
  simp only [rank,Nat.max_le]; omega

theorem member_rank {j : Nat} {xs : List Nat} (h : j∈xs) : j+1≤rank xs := by
 induction xs with
 | nil => simp at h
 | cons a xs ih =>
  simp only [List.mem_cons] at h
  rcases h with rfl | h
  · exact Nat.le_max_left _ _
  · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

/-- The semantic prefix replacement interface. Its hypotheses explicitly include
 the missing last-bad extraction and lower-prefix structural properties. -/
theorem replacement_decreases {p n m pre replacement post P z c r d s ct rt}
 (old : Run p [] pre P c r) (new : Run p [] replacement P d s)
 (tail : Run p P post z ct rt) (cost : d≤c)
 (witness : m∈bad n [] (pre++post))
 (lower : ∀j∈bad n [] replacement,j<m)
 (suffix : ∀j∈bad n P post,j<m) :
 Run p [] (replacement++post) z (d+ct) (s+rt) ∧
 d+ct≤c+ct ∧ rank (bad n [] (replacement++post)) < rank (bad n [] (pre++post)) := by
 have hb : ∀j∈bad n [] (replacement++post),j<m := by
  rw [bad_append,run_evolve new]
  intro j hj
  rcases List.mem_append.mp hj with h | h
  · exact lower j h
  · exact suffix j h
 have hl := rank_le _ m hb
 have hr := member_rank witness
 exact ⟨run_append new tail,by omega,by omega⟩

/-- No singleton m at any before-move board and no board vertex above m
 suffice for all bad indices to be strictly below m. -/
theorem lower_bad {n m b es}
 (bounds : ∀j∈b,j≤m) (events : ∀e∈es,e.vertex≤m)
 (initial : b≠[m]) (avoid : [m]∉frames b es) :
 ∀j∈bad n b es,j<m := by
 induction es generalizing b with
 | nil => simp [bad]
 | cons e es ih =>
  have eb := events e (by simp)
  have tailBound : ∀j∈update b e,j≤m := by
   intro j hj
   cases he : e.place with
   | true => simp [update,he] at hj; rcases hj with rfl | hj; exact eb; exact bounds j hj
   | false => exact bounds j (List.mem_of_mem_erase (by simpa [update,he] using hj))
  have hn : update b e≠[m] := by intro h; apply avoid; simp [frames,h]
  have ha : [m]∉frames (update b e) es := by intro h; apply avoid; simp [frames,h]
  have ht := ih tailBound (by intro f hf; exact events f (by simp [hf])) hn ha
  intro j hj
  simp only [bad,List.mem_append] at hj
  rcases hj with hj | hj
  · cases b with
    | nil => simp at hj
    | cons a bs =>
     cases bs with
     | nil =>
      by_cases h : a<n ∧ e.vertex≤a
      · simp [h] at hj; subst j
        have hab := bounds a (by simp)
        have ham : a≠m := by intro hh; apply initial; simp [hh]
        omega
      · simp [h] at hj
     | cons x xs => simp at hj
  · exact ht j hj
theorem bypass_bad_bound {n m es}
 (events : ∀e∈es,e.vertex≤m)
 (avoids : (frames [] es).count [m]=0) :
 ∀j∈bad n [] es,j<m := by
 apply lower_bad (by simp) events (by simp)
 exact List.count_eq_zero.mp avoids

#print axioms bypass_bad_bound
#print axioms replacement_decreases
#print axioms lower_bad
end CleanHandoffMeasure
