import AssembledTrace
namespace ChainOccurrence
open LocalCertificate ChainTrace FamilyCut ChainAssembledTrace ChainGlobalReassembly

/-- All slot permutations are admissible, regardless of physical legality. -/
def semantics (r : Nat) := LocalCertificate.semantics (fullTable r).length

/-- Table chronology orders every event at a fixed vertex, including P/R alternation. -/
def canonical (table : List Event) (w : List Nat) : Prop :=
  ∀ (i j : Fin table.length), i.val<j.val →
    (table[i.val]).vertex=(table[j.val]).vertex → w.idxOf i.val < w.idxOf j.val

def labelledLegal (r : Nat) (E w : List Nat) : Prop :=
  isPermutation (fullTable r).length w ∧ canonical (fullTable r) w ∧
    ∃ raw, decodeTrace (fullTable r) w=some raw ∧ Trace (r+1) E raw

theorem admissible_not_restricted (r : Nat) (w : List Nat) :
    (semantics r).admissible w ↔ isPermutation (fullTable r).length w := Iff.rfl

theorem table_length (r : Nat) : (fullTable r).length=25+16*r := by
  have mids (n : Nat) : (assemble midTable n).length=16*n := by
    induction n with
    | zero => rfl
    | succ n ih =>
      simp [assemble,List.length_append,ih,midTable,MiddleDifference.events]
      omega
  simp [fullTable,preTable,List.length_append,mids,TailActual.events,
    ChainInitialSegment.events,I.events]
  omega

/-- Real duplicate slots exist already in the first family member. -/
theorem actual_duplicate_P6 :
    (fullTable 0)[9]?=some ⟨true,6⟩ ∧ (fullTable 0)[21]?=some ⟨true,6⟩ := by decide

/-- Identical raw decoding does not recover occurrence order. -/
theorem duplicate_decode_counterexample :
    let table : List Event := [⟨true,6⟩,⟨true,6⟩]
    isPermutation 2 [1,0] ∧
    decodeTrace table [0,1]=decodeTrace table [1,0] ∧
    canonical table [0,1] ∧ ¬canonical table [1,0] := by unfold canonical; decide

#print axioms admissible_not_restricted
#print axioms table_length
#print axioms actual_duplicate_P6
#print axioms duplicate_decode_counterexample
end ChainOccurrence
