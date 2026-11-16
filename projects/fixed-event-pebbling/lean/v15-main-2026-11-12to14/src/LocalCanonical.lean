import OccurrenceOrder
import InitialConverse
import MiddleConverse
namespace ChainLocalCanonical
open LocalCertificate ChainOccurrence
set_option maxRecDepth 100000
set_option maxHeartbeats 0
 def check (edges : List (Nat × Nat)) (w : List Nat) : Bool :=
 edges.all (fun p => decide (w.idxOf p.1 < w.idxOf p.2))
 def iEdges : List (Nat × Nat) := [(0,6),(1,7),(2,8),(3,5),(9,10),(12,13)]
 def mEdges : List (Nat × Nat) := [(1,7),(4,5),(8,9),(11,12)]
 def tEdges : List (Nat × Nat) := [(1,7),(4,5)]
 theorem edges_canonical (table : List Event) (edges : List (Nat × Nat)) (w : List Nat)
   (complete : ∀ i j : Fin table.length, i.val<j.val →
     (table[i.val]).vertex=(table[j.val]).vertex → (i.val,j.val)∈edges)
   (hc : check edges w=true) : canonical table w := by
   intro i j hij he
   have hh := List.all_eq_true.mp hc (i.val,j.val) (complete i j hij he)
   exact of_decide_eq_true hh
 theorem iComplete : ∀ i j : Fin ChainInitialSegment.events.length, i.val<j.val →
   (ChainInitialSegment.events[i.val]).vertex=(ChainInitialSegment.events[j.val]).vertex →
   (i.val,j.val)∈iEdges := by decide
 theorem mComplete : ∀ i j : Fin ChainMiddleSegment.events.length, i.val<j.val →
   (ChainMiddleSegment.events[i.val]).vertex=(ChainMiddleSegment.events[j.val]).vertex →
   (i.val,j.val)∈mEdges := by decide
 theorem tComplete : ∀ i j : Fin ChainTailSegment.events.length, i.val<j.val →
   (ChainTailSegment.events[i.val]).vertex=(ChainTailSegment.events[j.val]).vertex →
   (i.val,j.val)∈tEdges := by decide
 theorem initial_checked : UpperCertificate.I.physicalWords.all (fun u =>
   check iEdges (ChainInitialConverse.liftWord u))=true := by decide
 theorem middle_checked : UpperCertificate.M.physicalWords.all (fun u =>
   check mEdges (ChainMiddleConverse.liftWord u))=true := by decide
 theorem initial_canonical (u : List Nat) (hu : I.Legal u) :
   canonical ChainInitialSegment.events (ChainInitialConverse.liftWord u) := by
   have hm := (EnumerationCorrectness.upper_physical_enumeration_legal I.events I.initial I.final I.erasures u).mpr hu
   exact edges_canonical _ _ _ iComplete (List.all_eq_true.mp initial_checked u hm)
 theorem middle_canonical (u : List Nat) (hu : M.Legal u) :
   canonical ChainMiddleSegment.events (ChainMiddleConverse.liftWord u) := by
   have hm := (EnumerationCorrectness.upper_physical_enumeration_legal M.events M.initial M.final M.erasures u).mpr hu
   exact edges_canonical _ _ _ mComplete (List.all_eq_true.mp middle_checked u hm)
 theorem tail_canonical (w : List Nat) (hw : w=ChainTailSegment.wordA ∨ w=ChainTailSegment.wordB) :
   canonical ChainTailSegment.events w := by
   apply edges_canonical _ _ _ tComplete
   rcases hw with h|h <;> subst w <;> decide
#print axioms edges_canonical
#print axioms iComplete
#print axioms mComplete
#print axioms tComplete
#print axioms initial_checked
#print axioms middle_checked
#print axioms initial_canonical
#print axioms middle_canonical
#print axioms tail_canonical
end ChainLocalCanonical
