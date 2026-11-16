import LabelledTuple
import ComponentMixedRadix
namespace ComponentTuple
open ChainWholeBijection ComponentWordCodes ComponentPatterns SwapComponents SwapGraphBasics
abbrev Selected (bs : List Bool) := (j : Fin bs.length) → {w : List Nat // Reach LocalCertificate.M.Legal (root (bs.get j)) w}
def fromFactors : (bs : List Bool) → Factors bs → Selected bs
 | [],_ => fun j=>Fin.elim0 j
 | b::bs,x => Fin.cases x.1 (fromFactors bs x.2)
def toFactors : (bs : List Bool) → Selected bs → Factors bs
 | [],_ => ()
 | b::bs,f => (f 0,toFactors bs (fun j=>f j.succ))
theorem from_to (bs : List Bool) (f : Selected bs) : fromFactors bs (toFactors bs f)=f := by
 induction bs with
 | nil => funext j;exact Fin.elim0 j
 | cons b bs ih => funext j;refine Fin.cases ?_ (fun j=>?_) j
                   · rfl
                   · exact congrFun (ih (fun j=>f j.succ)) j
theorem to_from (bs : List Bool) (x : Factors bs) : toFactors bs (fromFactors bs x)=x := by
 induction bs with
 | nil => cases x;rfl
 | cons b bs ih => rcases x with ⟨a,x⟩;simp only [toFactors,fromFactors,Fin.cases_zero,Fin.cases_succ,ih]

def chosen (bs : List Bool) (x : LocalTuple bs.length) : Prop :=
 ∀j,Reach LocalCertificate.M.Legal (root (bs.get j)) (x.middles j).val
abbrev SelectedTuple (bs : List Bool) := {x : LocalTuple bs.length // chosen bs x}
def fromTuple (bs : List Bool) (x : ComponentMixedRadix.ComponentTuples bs) : SelectedTuple bs :=
 let f := fromFactors bs x.1.2
 ⟨⟨x.1.1,fun j=>⟨(f j).val,reach_legal (f j).property⟩,x.2⟩,fun j=>(f j).property⟩
def toTuple (bs : List Bool) (x : SelectedTuple bs) : ComponentMixedRadix.ComponentTuples bs :=
 ((x.val.initial,toFactors bs (fun j=>⟨(x.val.middles j).val,x.property j⟩)),x.val.tail)
theorem tuple_from_to (bs) (x : SelectedTuple bs) : fromTuple bs (toTuple bs x)=x := by
 apply Subtype.ext
 simp only [fromTuple,toTuple,from_to]
theorem tuple_to_from (bs) (x : ComponentMixedRadix.ComponentTuples bs) : toTuple bs (fromTuple bs x)=x := by
 change ((x.1.1,toFactors bs (fromFactors bs x.1.2)),x.2)=x
 rw [to_from]
#print axioms tuple_from_to
#print axioms tuple_to_from
end ComponentTuple
