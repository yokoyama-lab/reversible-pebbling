/-
  **ピークつきレベル束の証明書（ビットマップ＋`decide +kernel`）で $M^*(T_4,6) \ge 47$**（第60夜 周2/3・生成物）。（分割: Defs）

  `autoresearch/tools/night60r2_levelcert_gen_bit.py 4 6` の出力。**手で編集しないこと。**
  表（q=6・大きさ s の最短距離）: s=1→15, s=2→12, s=3→11, s=4→10, s=5→9, s=6→8。束の状態数 127・深さ 14。
  表（q=5・大きさ s の最短距離）: s=1→17, s=2→12, s=3→11, s=4→10, s=5→9。束の状態数 120・深さ 16。
-/
import LevelCertBit

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace SplitLemma

open Finset HullLemma Bit

namespace H4Bit

/-- heap 番号の `T_4`: 内部頂点 `1..15` の子は `2v, 2v+1`。 -/
def pred : ℕ → Finset ℕ := fun v =>
  if 1 ≤ v ∧ v ≤ 15 then {2 * v, 2 * v + 1} else ∅

def F : Finset ℕ := {16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31}

theorem pred_irrefl : ∀ v : ℕ, v ∉ pred v := by
  intro v
  unfold pred
  split_ifs with hv
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    omega
  · simp

def TfP : ℕ → ℕ := fun s =>
  if s = 1 then 14
  else if s = 2 then 11
  else if s = 3 then 10
  else if s = 4 then 9
  else if s = 5 then 8
  else if s = 6 then 7
  else if s = 7 then 14
  else 0

def TfQ : ℕ → ℕ := fun s =>
  if s = 1 then 16
  else if s = 2 then 11
  else if s = 3 then 10
  else if s = 4 then 9
  else if s = 5 then 8
  else if s = 6 then 16
  else if s = 7 then 16
  else 0

def SA : Finset ℕ := {2, 4, 5, 8, 9, 10, 11}

def msA : List ℕ := [2, 4, 5, 8, 9, 10, 11]

def idxA : ℕ → ℕ := fun v =>
  if v = 2 then 0
  else if v = 4 then 1
  else if v = 5 then 2
  else if v = 8 then 3
  else if v = 9 then 4
  else if v = 10 then 5
  else if v = 11 then 6
  else 0

def kidsA : ℕ → List ℕ := fun v =>
  if v = 2 then [4, 5]
  else if v = 4 then [8, 9]
  else if v = 5 then [10, 11]
  else if v = 8 then []
  else if v = 9 then []
  else if v = 10 then []
  else if v = 11 then []
  else []

def SB : Finset ℕ := {3, 6, 7, 12, 13, 14, 15}

def msB : List ℕ := [3, 6, 7, 12, 13, 14, 15]

def idxB : ℕ → ℕ := fun v =>
  if v = 3 then 0
  else if v = 6 then 1
  else if v = 7 then 2
  else if v = 12 then 3
  else if v = 13 then 4
  else if v = 14 then 5
  else if v = 15 then 6
  else 0

def kidsB : ℕ → List ℕ := fun v =>
  if v = 3 then [6, 7]
  else if v = 6 then [12, 13]
  else if v = 7 then [14, 15]
  else if v = 12 then []
  else if v = 13 then []
  else if v = 14 then []
  else if v = 15 then []
  else []

#print axioms pred_irrefl

end H4Bit

end SplitLemma
