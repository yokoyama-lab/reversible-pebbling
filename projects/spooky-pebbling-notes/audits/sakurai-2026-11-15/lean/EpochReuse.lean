import ChargeFailure
namespace EpochReuse
open SpookyRound TraceBridge CutBound RefPartition

def empty7 : Config 7 := ⟨fun _ => false,fun _ => false⟩
def leafC : Action := ⟨[.idle,.idle,.idle,.pebble,.pebble,.pebble,.pebble],List.replicate 7 false⟩
def firstParent : Action := ⟨[.idle,.pebble,.idle,.idle,.idle,.idle,.idle],[false,true,false,false,false,false,false]⟩
def secondParents : Action := ⟨[.idle,.pebble,.pebble,.idle,.idle,.idle,.idle],List.replicate 7 false⟩
def rootC : Action := ⟨[.pebble,.idle,.idle,.idle,.idle,.idle,.idle],List.replicate 7 false⟩
def parentU : Action := ⟨[.idle,.unpebble,.unpebble,.idle,.idle,.idle,.idle],List.replicate 7 false⟩
def leafU : Action := ⟨[.idle,.idle,.idle,.unpebble,.unpebble,.unpebble,.unpebble],List.replicate 7 false⟩
def trace := [leafC,firstParent,secondParents,rootC,parentU,leafU]
def result := RefArea.eval empty7 trace

theorem actual : ActionRuns HeapPath.pred empty7 trace result := by
 apply ActionRuns.cons (by decide) (by decide) (by decide)
 apply ActionRuns.cons (by decide) (by decide) (by decide)
 apply ActionRuns.cons (by decide) (by decide) (by decide)
 apply ActionRuns.cons (by decide) (by decide) (by decide)
 apply ActionRuns.cons (by decide) (by decide) (by decide)
 apply ActionRuns.cons (by decide) (by decide) (by decide)
 exact ActionRuns.nil _

theorem properties : result.work=14 ∧ result.space=7 ∧
 (∀v : Fin 7,result.state.peb v=(v.val==0)) ∧
 (∀v : Fin 7,result.state.ghost v=false) ∧
 count .compute (events (3 : Fin 7) trace)=1 ∧
 count .ghost (events (3 : Fin 7) trace)=0 ∧
 count .compute (events (1 : Fin 7) trace)=2 ∧
 count .ghost (events (1 : Fin 7) trace)=1 ∧
 (trace.filter (references HeapPath.pred (3 : Fin 7))).length=3 := by decide

-- The two parent computes both use the same uninterrupted child epoch.
theorem child_held : Area.live (3 : Fin 7) (afterRound empty7 leafC)
 [firstParent,secondParents,rootC,parentU]=4 := by decide
#print axioms actual
#print axioms properties
#print axioms child_held

-- Abstract ordered epoch-label lemma; actual epoch extraction is not encoded here.
theorem ordered_overlap {a b c d x y : Nat}
 (hab : a≤b) (hbc : b≤c) (hcd : c≤d)
 (hx : (x=a ∨ x=b) ∧ (x=c ∨ x=d))
 (hy : (y=a ∨ y=b) ∧ (y=c ∨ y=d)) : x=y := by omega
#print axioms ordered_overlap
end EpochReuse
