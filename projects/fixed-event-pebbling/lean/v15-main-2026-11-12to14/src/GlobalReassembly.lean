import BoardTransport
namespace ChainGlobalReassembly
open LocalCertificate ChainTrace BoardTransport

/-- A physical interval reaching its specified checkpoint up to board order. -/
def Segment (erasures source target : List Nat) (events : List Event) : Prop :=
  ∃ actual, run erasures source events = some actual ∧ target.Perm actual

theorem segment_trans (erasures a b c : List Nat) (xs ys : List Event)
    (hx : Segment erasures a b xs) (hy : Segment erasures b c ys) :
    Segment erasures a c (xs ++ ys) := by
  obtain ⟨mid,hx,hm⟩ := hx
  obtain ⟨last,hy,hl⟩ := hy
  obtain ⟨actual,hr,hp⟩ := concatenate_through_perm erasures a mid b last xs ys hx hm hy
  exact ⟨actual,hr,hl.trans hp⟩

def assemble (words : Nat → List Event) : Nat → List Event
  | 0 => []
  | n+1 => assemble words n ++ words n

/-- Any finite sequence of independently checked interval runs composes,
without requiring their concrete list orders at boundaries to coincide. -/
theorem assemble_segments (erasures : List Nat) (boards : Nat → List Nat)
    (words : Nat → List Event) (n : Nat)
    (each : ∀ i, i < n → Segment erasures (boards i) (boards (i+1)) (words i)) :
    Segment erasures (boards 0) (boards n) (assemble words n) := by
  induction n with
  | zero => exact ⟨boards 0,rfl,List.Perm.refl _⟩
  | succ n ih =>
    exact segment_trans erasures (boards 0) (boards n) (boards (n+1))
      (assemble words n) (words n)
      (ih (fun i hi => each i (by omega))) (each n (by omega))

def checkpoint (j : Nat) : List Nat := [5+6*j,7+6*j,9+6*j,10+6*j,11+6*j]

theorem checkpoint_shift_six (j : Nat) :
    checkpoint (j+1) = (checkpoint j).map (fun v => v+6) := by
  simp [checkpoint, Nat.mul_add, Nat.add_assoc]

theorem canonical_middle_chain (erasures : List Nat) (words : Nat → List Event) (r : Nat)
    (each : ∀ j, j < r → Segment erasures (checkpoint j) (checkpoint (j+1)) (words j)) :
    Segment erasures (checkpoint 0) (checkpoint r) (assemble words r) :=
  assemble_segments erasures checkpoint words r each

/-- Reassemble an initial factor, r translated middle intervals, and a tail.
All supplied interval proofs must use the same global erasure set. -/
theorem reassemble_initial_middle_tail (erasures : List Nat)
    (initial tail : List Event) (middles : Nat → List Event) (r : Nat)
    (hi : Segment erasures [] (checkpoint 0) initial)
    (hm : ∀ j, j < r → Segment erasures (checkpoint j) (checkpoint (j+1)) (middles j))
    (ht : Segment erasures (checkpoint r) [11+6*r] tail) :
    run erasures [] (initial ++ assemble middles r ++ tail) = some [11+6*r] := by
  have h := segment_trans erasures [] (checkpoint r) [11+6*r]
    (initial ++ assemble middles r) tail
    (segment_trans erasures [] (checkpoint 0) (checkpoint r) initial (assemble middles r)
      hi (canonical_middle_chain erasures middles r hm)) ht
  obtain ⟨actual,hr,hperm⟩ := h
  have he : actual = [11+6*r] := by simpa using hperm.symm
  simpa [he] using hr

#print axioms segment_trans
#print axioms assemble_segments
#print axioms checkpoint_shift_six
#print axioms canonical_middle_chain
#print axioms reassemble_initial_middle_tail
end ChainGlobalReassembly
