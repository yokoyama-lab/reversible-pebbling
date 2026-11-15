import Std
namespace CleanFringe
-- Counts under the mathematical two-level schedule decomposition.
def work (k m : Nat) := 2*k*(2*m-1)+(2*k-3)
def vertices (k m : Nat) := k*m+k-1

theorem work_exact (k m : Nat) (hk : 2 ≤ k) (hm : 1 ≤ m) :
    work k m + 3 = 4*k*m := by
  unfold work
  rw [Nat.mul_sub_left_distrib]
  simp only [Nat.mul_one]
  have h : k ≤ k*m := by simpa using Nat.mul_le_mul_left k hm
  have heq : 2*k*(2*m) = 4*k*m := by
    calc
      2*k*(2*m) = (2*2)*(k*m) := by ac_rfl
      _ = 4*k*m := by simp [Nat.mul_assoc]
  rw [heq]
  have hbig : 2*k ≤ 4*k*m := by
    calc
      2*k ≤ 2*(k*m) := Nat.mul_le_mul_left 2 h
      _ ≤ 4*(k*m) := Nat.mul_le_mul_right (k*m) (by decide)
      _ = 4*k*m := by simp [Nat.mul_assoc]
  omega

theorem work_linear (k m : Nat) (hk : 2 ≤ k) (hm : 1 ≤ m) :
    work k m < 4 * vertices k m := by
  have h := work_exact k m hk hm
  have hkm : k ≤ k*m := by simpa using Nat.mul_le_mul_left k hm
  unfold vertices
  rw [Nat.mul_sub_left_distrib, Nat.mul_add]
  simp only [Nat.mul_one, Nat.mul_assoc] at *
  omega

def peak (k m b : Nat) := max (2*k-1) (k+1+b*(m-1))
theorem peak_fits (htop : 2*k-1 ≤ s) (hfringe : k+1+b*(m-1) ≤ s) :
    peak k m b ≤ s := Nat.max_le.mpr ⟨htop,hfringe⟩
#print axioms work_exact
#print axioms work_linear
#print axioms peak_fits
end CleanFringe
