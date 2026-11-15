import Complete
namespace Certificates
def pred7 (v u : Fin 7) : Bool := u.val == 2*v.val+1 || u.val == 2*v.val+2
def empty7 : SpookyRound.Config 7 := ⟨fun _ => false, fun _ => false⟩
def goal7 (q : SpookyRound.Config 7) : Bool :=
  (List.finRange 7).all fun v => q.peb v == (v.val == 0) && !q.ghost v
def check (q : SpookyRound.Config 7) (w s : Nat) : List SpookyRound.Action → Nat → Nat → Bool
 | [], W, S => goal7 q && w == W && s == S
 | a::as, W, S => decide (a.first.length = 7 ∧ a.ghosts.length = 7 ∧ SpookyRound.Legal pred7 q a) &&
     check (SpookyRound.afterRound q a) (w + SpookyRound.roundWork a) (max s (SpookyRound.roundSpace q a)) as W S
def witness0 : List SpookyRound.Action := [⟨[.idle,.idle,.idle,.pebble,.pebble,.pebble,.pebble],[false,false,false,false,false,false,false]⟩,⟨[.idle,.pebble,.pebble,.idle,.idle,.idle,.idle],[false,false,false,false,false,false,false]⟩,⟨[.pebble,.idle,.idle,.idle,.idle,.idle,.idle],[false,false,false,false,false,false,false]⟩,⟨[.idle,.unpebble,.unpebble,.idle,.idle,.idle,.idle],[false,false,false,false,false,false,false]⟩,⟨[.idle,.idle,.idle,.unpebble,.unpebble,.unpebble,.unpebble],[false,false,false,false,false,false,false]⟩]
theorem certificate0 : check empty7 0 0 witness0 13 7 = true ∧ witness0.length = 5 := by decide
#print axioms certificate0
def witness1 : List SpookyRound.Action := [⟨[.idle,.idle,.idle,.pebble,.pebble,.pebble,.pebble],[false,false,false,false,false,false,false]⟩,⟨[.idle,.pebble,.pebble,.idle,.idle,.idle,.idle],[false,false,false,false,false,false,true]⟩,⟨[.pebble,.idle,.idle,.idle,.idle,.idle,.idle],[false,false,false,false,false,false,false]⟩,⟨[.idle,.unpebble,.idle,.idle,.idle,.idle,.idle],[false,false,false,false,false,false,false]⟩,⟨[.idle,.idle,.idle,.idle,.idle,.idle,.pebble],[false,false,false,false,false,false,false]⟩,⟨[.idle,.idle,.unpebble,.idle,.idle,.idle,.idle],[false,false,false,false,false,false,false]⟩,⟨[.idle,.idle,.idle,.unpebble,.unpebble,.unpebble,.unpebble],[false,false,false,false,false,false,false]⟩]
theorem certificate1 : check empty7 0 0 witness1 14 6 = true ∧ witness1.length = 7 := by decide
#print axioms certificate1
def witness2 : List SpookyRound.Action := [⟨[.idle,.idle,.idle,.idle,.idle,.pebble,.pebble],[false,false,false,false,false,false,false]⟩,⟨[.idle,.idle,.pebble,.pebble,.pebble,.idle,.idle],[false,false,false,false,false,true,true]⟩,⟨[.idle,.pebble,.idle,.idle,.idle,.idle,.idle],[false,false,false,false,false,false,false]⟩,⟨[.pebble,.idle,.idle,.idle,.idle,.idle,.idle],[false,false,false,false,false,false,false]⟩,⟨[.idle,.unpebble,.idle,.idle,.idle,.idle,.idle],[false,false,false,false,true,false,false]⟩,⟨[.idle,.idle,.idle,.unpebble,.idle,.pebble,.pebble],[false,false,false,false,false,false,false]⟩,⟨[.idle,.idle,.unpebble,.idle,.pebble,.idle,.idle],[false,false,false,false,false,false,false]⟩,⟨[.idle,.idle,.idle,.idle,.unpebble,.unpebble,.unpebble],[false,false,false,false,false,false,false]⟩]
theorem certificate2 : check empty7 0 0 witness2 16 5 = true ∧ witness2.length = 8 := by decide
#print axioms certificate2
def witness3 : List SpookyRound.Action := [⟨[.idle,.idle,.idle,.idle,.idle,.pebble,.pebble],[false,false,false,false,false,false,false]⟩,⟨[.idle,.idle,.pebble,.pebble,.pebble,.idle,.idle],[false,false,false,false,false,true,true]⟩,⟨[.idle,.pebble,.idle,.idle,.idle,.idle,.idle],[false,false,false,false,false,false,false]⟩,⟨[.pebble,.idle,.idle,.idle,.idle,.idle,.idle],[false,false,false,false,false,false,false]⟩,⟨[.idle,.unpebble,.idle,.idle,.idle,.idle,.idle],[false,false,false,false,false,false,false]⟩,⟨[.idle,.idle,.idle,.unpebble,.idle,.idle,.idle],[false,false,false,false,false,false,false]⟩,⟨[.idle,.idle,.idle,.idle,.idle,.pebble,.pebble],[false,false,false,false,false,false,false]⟩,⟨[.idle,.idle,.unpebble,.idle,.idle,.idle,.idle],[false,false,false,false,false,false,false]⟩,⟨[.idle,.idle,.idle,.idle,.unpebble,.unpebble,.unpebble],[false,false,false,false,false,false,false]⟩]
theorem certificate3 : check empty7 0 0 witness3 15 5 = true ∧ witness3.length = 9 := by decide
#print axioms certificate3
def witness4 : List SpookyRound.Action := [⟨[.idle,.idle,.idle,.idle,.idle,.pebble,.pebble],[false,false,false,false,false,false,false]⟩,⟨[.idle,.idle,.pebble,.idle,.idle,.idle,.idle],[false,false,false,false,false,true,true]⟩,⟨[.idle,.idle,.idle,.pebble,.pebble,.idle,.idle],[false,false,false,false,false,false,false]⟩,⟨[.idle,.pebble,.idle,.idle,.idle,.idle,.idle],[false,false,false,false,true,false,false]⟩,⟨[.pebble,.idle,.idle,.idle,.idle,.idle,.idle],[false,false,true,false,false,false,false]⟩,⟨[.idle,.idle,.idle,.idle,.pebble,.idle,.idle],[false,false,false,false,false,false,false]⟩,⟨[.idle,.unpebble,.idle,.idle,.idle,.idle,.idle],[false,false,false,false,false,false,false]⟩,⟨[.idle,.idle,.idle,.unpebble,.idle,.idle,.idle],[false,false,false,false,false,false,false]⟩,⟨[.idle,.idle,.idle,.idle,.unpebble,.pebble,.pebble],[false,false,false,false,false,false,false]⟩,⟨[.idle,.idle,.pebble,.idle,.idle,.idle,.idle],[false,false,false,false,false,false,false]⟩,⟨[.idle,.idle,.unpebble,.idle,.idle,.idle,.idle],[false,false,false,false,false,false,false]⟩,⟨[.idle,.idle,.idle,.idle,.idle,.unpebble,.unpebble],[false,false,false,false,false,false,false]⟩]
theorem certificate4 : check empty7 0 0 witness4 17 4 = true ∧ witness4.length = 12 := by decide
#print axioms certificate4
end Certificates

namespace Certificates
theorem check_sound (as : List SpookyRound.Action) (q : SpookyRound.Config 7) (w s W S : Nat)
    (h : check q w s as W S = true) :
    ∃ r, SpookyRound.PaperRuns pred7 as.length q r ∧ goal7 r.state = true ∧
      w + r.work = W ∧ max s r.space = S := by
  induction as generalizing q w s with
  | nil =>
    simp only [check, Bool.and_eq_true, beq_iff_eq] at h
    refine ⟨⟨q,0,0⟩, SpookyRound.PaperRuns.zero q, ?_⟩
    simpa [and_assoc] using h
  | cons a as ih =>
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨r, hr, hg, hw, hs⟩ := ih _ _ _ h.2
    refine ⟨SpookyDP.prepend (SpookyRound.edge q a) r, ?_, hg, ?_, ?_⟩
    · apply SpookyRound.PaperRuns.step (e := SpookyRound.edge q a)
      · exact ⟨a,h.1.1,h.1.2.1,h.1.2.2,rfl⟩
      · exact hr
    · simpa [SpookyDP.prepend, SpookyRound.edge, Nat.add_assoc] using hw
    · simpa [SpookyDP.prepend, SpookyRound.edge, Nat.max_assoc] using hs
#print axioms check_sound
end Certificates

namespace Certificates
theorem feasible0 : ∃ r, SpookyRound.PaperRuns pred7 5 empty7 r ∧ goal7 r.state = true ∧ r.work = 13 ∧ r.space = 7 := by
  have h := check_sound witness0 empty7 0 0 13 7 certificate0.1
  simpa [certificate0.2] using h
#print axioms feasible0
theorem feasible1 : ∃ r, SpookyRound.PaperRuns pred7 7 empty7 r ∧ goal7 r.state = true ∧ r.work = 14 ∧ r.space = 6 := by
  have h := check_sound witness1 empty7 0 0 14 6 certificate1.1
  simpa [certificate1.2] using h
#print axioms feasible1
theorem feasible2 : ∃ r, SpookyRound.PaperRuns pred7 8 empty7 r ∧ goal7 r.state = true ∧ r.work = 16 ∧ r.space = 5 := by
  have h := check_sound witness2 empty7 0 0 16 5 certificate2.1
  simpa [certificate2.2] using h
#print axioms feasible2
theorem feasible3 : ∃ r, SpookyRound.PaperRuns pred7 9 empty7 r ∧ goal7 r.state = true ∧ r.work = 15 ∧ r.space = 5 := by
  have h := check_sound witness3 empty7 0 0 15 5 certificate3.1
  simpa [certificate3.2] using h
#print axioms feasible3
theorem feasible4 : ∃ r, SpookyRound.PaperRuns pred7 12 empty7 r ∧ goal7 r.state = true ∧ r.work = 17 ∧ r.space = 4 := by
  have h := check_sound witness4 empty7 0 0 17 4 certificate4.1
  simpa [certificate4.2] using h
#print axioms feasible4
end Certificates
namespace ExactFrontier
def points : List ClosedFrontier.Cost := [⟨5,13,7⟩,⟨7,14,6⟩,⟨8,16,5⟩,⟨9,15,5⟩,⟨12,17,4⟩]
def Achievable (D W S : Nat) : Prop :=
  ∃ d, d ≤ D ∧ ∃ r, SpookyRound.PaperRuns EdgeBridge.pred d EdgeBridge.empty r ∧
    EdgeBridge.goalCfg r.state = true ∧ r.work ≤ W ∧ r.space ≤ S

theorem exact_frontier (D W S : Nat) : Achievable D W S ↔
    ∃ f ∈ points, f.depth ≤ D ∧ f.work ≤ W ∧ f.space ≤ S := by
  constructor
  · rintro ⟨d,hd,r,hr,hg,hw,hs⟩
    obtain ⟨f,hf,fd,fw,fs⟩ := EdgeBridge.physical_lower_complete hr hg
    exact ⟨f,hf,Nat.le_trans fd hd,Nat.le_trans fw hw,Nat.le_trans fs hs⟩
  · rintro ⟨f,hf,hd,hw,hs⟩
    simp only [points,List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl
    · obtain ⟨r,hr,hg,heW,heS⟩ := Certificates.feasible0
      refine ⟨5,hd,r,hr,hg,?_,?_⟩
      · simpa [heW] using hw
      · simpa [heS] using hs
    · obtain ⟨r,hr,hg,heW,heS⟩ := Certificates.feasible1
      refine ⟨7,hd,r,hr,hg,?_,?_⟩
      · simpa [heW] using hw
      · simpa [heS] using hs
    · obtain ⟨r,hr,hg,heW,heS⟩ := Certificates.feasible2
      refine ⟨8,hd,r,hr,hg,?_,?_⟩
      · simpa [heW] using hw
      · simpa [heS] using hs
    · obtain ⟨r,hr,hg,heW,heS⟩ := Certificates.feasible3
      refine ⟨9,hd,r,hr,hg,?_,?_⟩
      · simpa [heW] using hw
      · simpa [heS] using hs
    · obtain ⟨r,hr,hg,heW,heS⟩ := Certificates.feasible4
      refine ⟨12,hd,r,hr,hg,?_,?_⟩
      · simpa [heW] using hw
      · simpa [heS] using hs
#print axioms exact_frontier
end ExactFrontier
