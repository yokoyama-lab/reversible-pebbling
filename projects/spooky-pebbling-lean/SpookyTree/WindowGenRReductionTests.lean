/-
# `WindowGenRReduction.lean` の検査: 公理と，主張の仮定が満たせること

* 公理は `propext`，`Classical.choice`，`Quot.sound` だけ．
* `lp_relaxed_le_envU` は具体の点（列 λ 1 本，`γ = 3/2`，`X = 2`，ゆるみ 1）に適用できる．
* `step` は空でない区域（根 `[]`，`E = {[]}`，`K_Z = {[false, false, false]}`）に適用できる．
* `top_bound` は `m = 2`（段 1 だけ）の区域の族に適用できる．
-/
import SpookyTree.WindowGenRReduction

namespace SpookyTree
namespace GenRReduction

open Finset GenRSigma GenRDual GenRLemmaT

/-- 緩めた右辺での弱双対の具体例: 列 λ を重み 1 で 1 本，[行 Z] `1 ≤ (3/2)·2 + 1`，[行 N] `1 ≤ 1 + 1`． -/
example :
    (1 : ℝ) ≤ 2 * envU (3 / 2) 1 (fun j : ℕ => U (3 / 2) 1 0 j) (1 / 2) +
      (2 * (3 / 2) ^ 1 + 2 ^ (1 - 1)) * (1 + 1 + ∑ j ∈ Icc 1 0, (fun _ => (0 : ℝ)) j) := by
  have h := lp_relaxed_le_envU (Good_U (γ := 3 / 2) (by norm_num) 1 0)
    (fun j => U_le_pow (by norm_num) 1 0 j) ({()} : Finset Unit) (fun _ => 1) (fun _ => ColType.lam)
    0 1 (by norm_num) (γ := 3 / 2) (X := 2) (N := 1) (sZ := 1) (sN := 1) (fun _ => 0)
    (by norm_num) (by norm_num) (by norm_num) (fun _ _ => le_refl _)
    (by simp) (by simp [ColType.Valid])
    (by simp [ColType.col]) (by simp [ColType.col]) (by simp)
  simpa [ColType.col] using h

/-- `inZ` の仮定は満たせる（深い点 1 つ）． -/
theorem inZ_ex : ∀ x ∈ ({[false, false, false]} : Finset Node), inZ {[]} [] x := by
  intro x hx
  rw [Finset.mem_singleton] at hx
  subst hx
  refine ⟨List.nil_prefix, by simp, fun e he _ _ hne => ?_⟩
  rw [Finset.mem_singleton] at he
  exact hne he

theorem jIdx_ex : jIdx 2 {[false, false, false]} {[]} [false, false, false] = 0 := by
  simp [jIdx]

/-- `step` は空でない区域に適用できる（深さ 3 の点，`β = 2`，`X = 1`，`t = 5`，`τ = 5`）． -/
example (γ' : ℝ) (h1 : 1 ≤ γ') (h2 : γ' ≤ 2) :=
  step (X := 1) le_rfl h1 h2 1 1 1 (by omega) 2 4 [] {[false, false, false]} {[]} inZ_ex
    (by simp; linarith) (fun x => (1 : ℝ) ^ (1 + 1) * U γ' 1 1 ((5 : ℕ) / (1 : ℕ)))
    (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 5) (fun _ => 5) 5
    (∑ x ∈ ({[false, false, false]} : Finset Node), (1 : ℝ) ^ (1 + 1) * U γ' 1 1 ((5 : ℕ) / (1 : ℕ)))
    0
    (by intro x _; simp)
    (by intro x hx; rw [Finset.mem_singleton] at hx; subst hx; rw [jIdx_ex])
    (by simp)
    le_rfl (by simp)

/-- `m = 2` の族（段 1 の区域 1 つ，根 `[]`，基底の点は空）． -/
noncomputable def F2 : ZoneFamily where
  X := 1
  γ := 1
  r := 1
  hgt := 2
  β := fun _ => 1
  E := fun _ => {[]}
  Ys := fun L => if L = 1 then {[]} else ∅
  KZ := fun _ _ => ∅
  Val := fun _ _ => 0
  Uc := fun _ _ => 0
  t := fun _ _ => 0
  τ := fun _ _ => 0
  J1 := fun _ => 0
  ι := Unit
  sB := fun _ => ∅
  xB := fun _ _ => 0
  tB := fun _ _ => NoneCol.dirty

theorem F2_hyp : F2.Hyp where
  hX := le_rfl
  h1 := le_rfl
  h2 := by norm_num [F2]
  hYE := by
    intro L y hy
    simp only [F2] at hy ⊢
    split_ifs at hy <;> simp_all
  hKZ := by intro L y _ x hx; simp [F2] at hx
  hchild := by intro L y hy; simp [F2] at hy
  hbud := by intro L y hy; simp [F2] at hy
  hVal := by intro L y hy; simp [F2] at hy
  hU := by intro L y hy; simp [F2] at hy
  hM := by intro L y hy; simp [F2] at hy
  hb := by intro L y hy; simp [F2] at hy
  hbase := by
    intro y _
    refine ⟨by simp [F2], fun i hi => absurd hi (Finset.notMem_empty i), by simp [F2], ?_, by simp [F2]⟩
    simp only [F2, sum_empty]
    exact Nat.cast_nonneg _

theorem F2_Mz : (F2.Mz 1 [] : ℝ) ≤ 2 ^ F2.r * F2.X := by
  have h : F2.Mz 1 [] ≤ 2 := by
    classical
    unfold ZoneFamily.Mz fullM
    refine (Finset.card_filter_le _ _).trans ?_
    simp [F2, card_words]
  have : (F2.Mz 1 [] : ℝ) ≤ 2 := by exact_mod_cast h
  simpa [F2] using this

/-- `top_bound` は `m = 2` の族に適用できる． -/
example := ZoneFamily.top_bound F2_hyp (by intro y _; simp [F2]) (by intro L; simp [F2]) 0 []
  (by simp [F2]) F2_Mz

#print axioms weak_duality_relaxed
#print axioms chordZ_le
#print axioms treePrice_le
#print axioms lp_relaxed_le_envU
#print axioms lp_relaxed_le_envU'
#print axioms envU_scale
#print axioms step
#print axioms base_step
#print axioms ZoneFamily.C_all
#print axioms ZoneFamily.slack_sum_le
#print axioms ZoneFamily.slackLevel_le
#print axioms ZoneFamily.junk_sum_le
#print axioms ZoneFamily.junkLevel_le
#print axioms ZoneFamily.top_bound

end GenRReduction
end SpookyTree
