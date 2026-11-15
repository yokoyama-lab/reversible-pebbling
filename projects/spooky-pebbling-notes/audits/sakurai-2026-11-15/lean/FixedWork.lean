import Std
namespace FixedWork
-- Integer accounting avoids silently truncating subtraction. Real calls must
-- separately establish valid forest counts and their cost equalities.
def tailCost (M old : Int) : List Int → Int
 | [] => 2*(M-old)
 | a::as => M+a-2*old+tailCost M a as

theorem tail_balance (M old : Int) (as : List Int) :
    tailCost M old as + 2*old + as.sum = ((as.length : Int)+2)*M := by
  induction as generalizing old with
  | nil => simp [tailCost]; omega
  | cons a as ih =>
    have h := ih a
    simp only [tailCost,List.sum_cons,List.length_cons,Int.natCast_add,Int.natCast_one]
    simp only [Int.add_mul] at *
    omega

def totalCost (M first : Int) (as : List Int) := M+first-3+tailCost M first as

theorem exact_work (M first : Int) (as : List Int) :
    totalCost M first as + 3 + first + as.sum = ((as.length : Int)+3)*M := by
  have h := tail_balance M first as
  unfold totalCost
  simp only [Int.add_mul] at *
  omega

theorem sum_ge_length (as : List Int) (h : ∀ a ∈ as, 1 ≤ a) :
    (as.length : Int) ≤ as.sum := by
  induction as with
  | nil => simp
  | cons a as ih =>
    have ha := h a (by simp)
    have hs := ih (fun b hb => h b (by simp [hb]))
    simp only [List.sum_cons,List.length_cons,Int.natCast_add,Int.natCast_one]
    omega

theorem fixed_work_coefficient (M first : Int) (as : List Int)
    (hf : 1 ≤ first) (ha : ∀ a ∈ as, 1 ≤ a) :
    totalCost M first as ≤ ((as.length : Int)+3)*(M-1)-1 := by
  have h := exact_work M first as
  have hs := sum_ge_length as ha
  simp only [Int.mul_sub,Int.mul_one]
  omega
#print axioms tail_balance
#print axioms exact_work
#print axioms fixed_work_coefficient
end FixedWork
