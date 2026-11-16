import Std
namespace ChainListIndex
noncomputable def index {α : Type} (xs : List α) (x : {x // x∈xs}) : Fin xs.length :=
 ⟨Classical.choose (List.mem_iff_getElem.mp x.property), (Classical.choose_spec (List.mem_iff_getElem.mp x.property)).1⟩
def value {α : Type} (xs : List α) (i : Fin xs.length) : {x // x∈xs} := ⟨xs[i.val], List.getElem_mem i.isLt⟩
theorem value_index {α : Type} (xs : List α) (x : {x // x∈xs}) : value xs (index xs x)=x := by
 apply Subtype.ext
 exact (Classical.choose_spec (List.mem_iff_getElem.mp x.property)).2
theorem index_value {α : Type} (xs : List α) (hn : xs.Nodup) (i : Fin xs.length) : index xs (value xs i)=i := by
 apply Fin.ext
 apply (List.getElem_inj hn).mp
 exact congrArg Subtype.val (value_index xs (value xs i))
#print axioms value_index
#print axioms index_value
end ChainListIndex
