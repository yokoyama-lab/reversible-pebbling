import LastBad
namespace CleanMeaning
open LocalCertificate VisitMeasure CleanHandoffMeasure
/-- Every move after a singleton below n moves strictly above that singleton. -/
def Clean (n : Nat) (b : List Nat) (es : List Event) : Prop :=
 ∀pre e post j,es=pre++e::post → evolve b pre=[j] → j<n → j<e.vertex

theorem bad_nil_iff_clean {n b es} : bad n b es=[] ↔ Clean n b es := by
 constructor
 · intro empty pre e post j hw hb hj
   by_cases he : e.vertex≤j
   · have hm : j∈bad n b es := by
      rw [hw,bad_append,hb]
      apply List.mem_append_right
      simp [bad,hj,he]
     rw [empty] at hm
     simp at hm
   · omega
 · intro clean
   cases he : bad n b es with
   | nil => rfl
   | cons m ms =>
    have hm : m∈bad n b es := by rw [he];simp
    obtain ⟨pre,e,post,hw,hb,hn,hv,hno⟩ := LastBad.split_last hm
    have hh := clean pre e post m hw hb hn
    omega
#print axioms bad_nil_iff_clean
end CleanMeaning
