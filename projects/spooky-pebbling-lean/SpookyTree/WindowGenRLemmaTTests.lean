/-
# `WindowGenRLemmaT.lean` の検査: 公理と，主張の仮定が満たせること

* 公理は `propext`，`Classical.choice`，`Quot.sound` だけ．
* (T1) は具体の深さで使える．部分和の選択は具体の個数で使える（`K = 1`，`f = 2`，大きさ 2 の子 1 個）．
* `zone_feasible` の仮定 `∀ x ∈ KZ, inZ E y x` は満たせる（根 `[]`，`E = ∅`，`KZ = {[false]}`）．
-/
import SpookyTree.WindowGenRLemmaT

namespace SpookyTree
namespace GenRLemmaT

open Finset GenRDual

/-- (T1) の具体例（切断点なし，深さ 2 のブロック，根）． -/
example : (openBelow 2 (fun _ => False) []).card +
    ∑ c ∈ kids 2 (fun _ => False) [], 2 ^ (2 - c.length) = 2 ^ (2 - ([] : Node).length) :=
  T1 2 _ (by simp)

/-- 部分和の選択の具体例: `K = 1`，`f = 2`，大きさ 2 の子 1 個（`4 ∣ 2 + 2`），`ρ = 2`． -/
example : ∃ c' : ℕ → ℕ, (∀ j, c' j ≤ (fun j => if j = 1 then 1 else 0) j) ∧
    ∑ j ∈ Icc 1 1, c' j * 2 ^ j = (2 ^ (1 + 1) - 2 % 2 ^ (1 + 1)) % 2 ^ (1 + 1) ∧
    2 ^ (1 + 1) ∣ 2 + ∑ j ∈ Icc 1 1, c' j * 2 ^ j :=
  select_large 1 2 _ (by decide)

/-- `inZ` の仮定は満たせる． -/
example : ∀ x ∈ ({[false]} : Finset Node), inZ ∅ [] x := by
  intro x hx
  rw [Finset.mem_singleton] at hx
  subst hx
  exact ⟨List.nil_prefix, by simp, fun e he => by simp at he⟩

/-- `zone_feasible` は具体の区域に適用できる． -/
example (vv : ℕ → ℝ) :=
  zone_feasible 1 3 4 [] {[false]} ∅ (by
    intro x hx
    rw [Finset.mem_singleton] at hx
    subst hx
    exact ⟨List.nil_prefix, by simp, fun e he => by simp at he⟩) vv

#print axioms T1
#print axioms T1_zone
#print axioms T2
#print axioms T3a
#print axioms T3b
#print axioms T4_holes
#print axioms T4_blocks
#print axioms T4_d0
#print axioms T4_NM
#print axioms cnt_sum_le
#print axioms select_large
#print axioms large_dvd
#print axioms colOf_valid
#print axioms rowZ_le
#print axioms rowN_le
#print axioms rowT_le
#print axioms obj_eq
#print axioms zone_feasible

end GenRLemmaT
end SpookyTree
