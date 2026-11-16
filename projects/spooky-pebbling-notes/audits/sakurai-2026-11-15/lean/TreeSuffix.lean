import LastLive
namespace TreeSuffix
open SpookyRound TraceBridge CutBound RefPartition

def empty3 : Config 3 := ⟨fun _ => false,fun _ => false⟩
def leaves : Action := ⟨[.idle,.pebble,.pebble],[false,false,false]⟩
def root : Action := ⟨[.pebble,.idle,.idle],[false,false,false]⟩
def clean : Action := ⟨[.idle,.unpebble,.unpebble],[false,false,false]⟩
def result := RefArea.eval empty3 [leaves,root,clean]

theorem clean_tree_run : ActionRuns HeapPath.pred empty3 [leaves,root,clean] result := by
 apply ActionRuns.cons (by decide) (by decide) (by decide)
 apply ActionRuns.cons (by decide) (by decide) (by decide)
 apply ActionRuns.cons (by decide) (by decide) (by decide)
 exact ActionRuns.nil _

theorem clean_tree_properties :
 result.work=5 ∧ result.space=3 ∧
 (∀v : Fin 3,result.state.peb v=(v.val==0)) ∧
 (∀v : Fin 3,result.state.ghost v=false) ∧
 references HeapPath.pred (1 : Fin 3) root=true ∧
 firstAt leaves (1 : Fin 3)=.pebble ∧
 Area.live (1 : Fin 3) (afterRound empty3 leaves) ([] : List Action)=0 := by decide

-- General all-or-nothing selection at separated reference endpoints.
-- Count controls the exception, not its duration.
theorem reference_dichotomy {n : Nat} {pred : Fin n → Fin n → Bool}
 {q : Config n} {gap ys : List Action} {b : Action} {r : SpookyDP.Result (Config n)}
 (h : ActionRuns pred q (gap++b::ys) r) (u : Fin n)
 (hb : references pred u b=true) :
 1≤RefSelect.comp u gap ∨
 (RefSelect.comp u gap=0 ∧ Area.live u q gap=gap.length ∧ gap.length≤Area.volume q gap) := by
 by_cases hc : RefSelect.comp u gap=0
 · exact Or.inr ⟨hc,RefSelect.kept_gap_live h u hb hc⟩
 · exact Or.inl (by omega)

-- If a reference pair has prescribed separation L and no re-compute,
-- it yields L occupied boundary cells for the SAME child (not per parent).
theorem separated_reference_area {n : Nat} {pred : Fin n → Fin n → Bool}
 {q : Config n} {gap ys : List Action} {b : Action} {r : SpookyDP.Result (Config n)}
 (h : ActionRuns pred q (gap++b::ys) r) (u : Fin n)
 (hb : references pred u b=true) (hc : RefSelect.comp u gap=0)
 (hsep : L≤gap.length) : L≤Area.live u q gap ∧ L≤Area.volume q gap := by
 have hh := RefSelect.kept_gap_live h u hb hc
 omega
#print axioms clean_tree_run
#print axioms clean_tree_properties
#print axioms reference_dichotomy
#print axioms separated_reference_area
end TreeSuffix
