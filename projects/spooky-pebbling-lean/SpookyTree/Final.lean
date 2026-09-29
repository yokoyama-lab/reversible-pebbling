/-
# 最終形: 最小ペブル数 `h + 1` での時間下界 `Ω(n log n / log log n)`

`L = 2⌊log₂ h⌋ + 3`、`j = ⌊(h − 1)/L⌋` と取ると `time_lower_bound` の仮定が満たされ、
  `T + 1 ≥ 2(2^h − 1) + (j − 2) · 2^h`、`j ≈ h / (2 log₂ h)`。
`n = 2^h − 1`、`log n ≈ h`、`log log n ≈ log h` なので、これは `T = Ω(n log n / log log n)`。
あわせて、定義が空虚でないことの確認として、`h = 2` の正しい手順（5 手）を示す。
-/
import SpookyTree.Arith

namespace SpookyTree

theorem time_lower_bound_log {h T : ℕ} {ms : ℕ → Move} (hV : Valid h (h + 1) T ms) (hh : 2 ≤ h) :
    2 * ((2 : ℝ) ^ h - 1) + ((((h - 1) / (2 * Nat.log 2 h + 3) : ℕ) : ℝ) - 2) * 2 ^ h ≤ T + 1 := by
  set Lg := Nat.log 2 h
  set j := (h - 1) / (2 * Lg + 3)
  apply time_lower_bound hV hh (2 * Lg + 1) j
  · -- j * L ≤ h − 1 < h
    have := Nat.div_mul_le_self (h - 1) (2 * Lg + 3)
    have e : 2 * Lg + 1 + 2 = 2 * Lg + 3 := by omega
    rw [e]
    show (h - 1) / (2 * Lg + 3) * (2 * Lg + 3) < h
    omega
  · -- 2 j (h−2) ≤ 2 h² < 2^(2 Lg + 3)
    have hj : j ≤ h := le_trans (Nat.div_le_self _ _) (Nat.sub_le _ _)
    have hlt : h < 2 ^ (Lg + 1) := Nat.lt_pow_succ_log_self (by norm_num) h
    have hsq : h * h < 2 ^ (2 * Lg + 2) := by
      calc h * h < 2 ^ (Lg + 1) * 2 ^ (Lg + 1) := Nat.mul_lt_mul'' hlt hlt
        _ = 2 ^ (2 * Lg + 2) := by rw [← pow_add]; ring_nf
    calc 2 * j * (h - 2) ≤ 2 * h * h := by
          have := Nat.mul_le_mul hj (Nat.sub_le h 2); nlinarith
      _ ≤ 2 * 2 ^ (2 * Lg + 2) := by nlinarith [hsq]
      _ = 2 ^ (2 * Lg + 1 + 2) := by rw [pow_succ]; ring_nf

/-! ## 空虚でないことの確認: `h = 2`（3 頂点）の 5 手の正しい手順 -/

/-- 葉 2 つを置き、根を置き、葉 2 つを外す。 -/
def ex2 : ℕ → Move
  | 0 => ⟨.pebble, [false]⟩
  | 1 => ⟨.pebble, [true]⟩
  | 2 => ⟨.pebble, []⟩
  | 3 => ⟨.unpebble, [false]⟩
  | 4 => ⟨.unpebble, [true]⟩
  | _ => ⟨.ghost, []⟩

theorem nodes_two : nodes 2 = {[], [false], [true]} := by decide

theorem ex2_valid : Valid 2 3 5 ex2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t ht
    interval_cases t <;> simp [Legal, Ready, st, step, ex2, result, Function.update]
  · intro t ht
    interval_cases t <;> simp [pcount, nodes_two, st, step, ex2, result, Function.update] <;> decide
  · simp [st, step, ex2, result, Function.update]
  · intro l hl hne
    match l, hl, hne with
    | [false], _, _ => simp [st, step, ex2, result, Function.update]
    | [true], _, _ => simp [st, step, ex2, result, Function.update]
    | [], _, hne => exact absurd rfl hne
    | _ :: _ :: _, hl, _ => simp at hl

end SpookyTree
