import LastLive
namespace ChargeFailure
open CutBound Exceptions

def rootAccount : Account := ⟨1,0,0,1,1⟩
def brokenAccount : Account := ⟨1,2,1,0,0⟩
def model (k : Nat) : List Account := rootAccount::List.replicate k brokenAccount

theorem valid_model (k : Nat) : ∀a∈model k,Valid a := by
 intro a ha
 simp only [model,List.mem_cons,List.mem_replicate] at ha
 rcases ha with rfl|⟨_,rfl⟩ <;> unfold Valid <;> decide

theorem totals (k : Nat) :
 (model k).length=k+1 ∧ work (model k)=4*k+1 ∧
 pebbles (model k)=1 ∧ roots (model k)=1 ∧ removed (model k)=k+1 := by
 induction k with
 | zero => decide
 | succ k ih =>
   simp only [model,List.replicate_succ,List.length_cons,work,pebbles,roots,removed,List.map_cons,List.sum_cons] at *
   simp only [rootAccount,brokenAccount,exceptional] at *
   simp at *
   omega

-- All first-scale account assumptions allow no retained good vertices at C=4.
theorem no_good_mass (k : Nat) :
 (∀a∈model k,Valid a) ∧ work (model k)≤4*(model k).length ∧
 pebbles (model k)≤1 ∧ roots (model k)≤1 ∧
 removed (model k)=(model k).length := by
 have ht := totals k
 refine ⟨valid_model k,?_,?_,?_,?_⟩ <;> omega
#print axioms valid_model
#print axioms totals
#print axioms no_good_mass
end ChargeFailure
