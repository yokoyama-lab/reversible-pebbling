/-
  **ピークつきレベル束の証明書（ビットマップ＋`decide +kernel`）で $M^*(T_5,7) \ge 121$**（第60夜 周2/3・生成物）。（分割: Defs）

  `autoresearch/tools/night60r2_levelcert_gen_bit.py 5 7` の出力。**手で編集しないこと。**
  表（q=7・大きさ s の最短距離）: s=1→45, s=2→32, s=3→27, s=4→26, s=5→25, s=6→24, s=7→23。束の状態数 16384・深さ 44。
  表（q=6・大きさ s の最短距離）: s=1→53, s=2→36, s=3→31, s=4→28, s=5→25, s=6→24。束の状態数 9938・深さ 52。
-/
import LevelCertBit

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace SplitLemma

open Finset HullLemma Bit

namespace H5Bit

/-- heap 番号の `T_5`: 内部頂点 `1..31` の子は `2v, 2v+1`。 -/
def pred : ℕ → Finset ℕ := fun v =>
  if 1 ≤ v ∧ v ≤ 31 then {2 * v, 2 * v + 1} else ∅

def F : Finset ℕ := {32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63}

theorem pred_irrefl : ∀ v : ℕ, v ∉ pred v := by
  intro v
  unfold pred
  split_ifs with hv
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    omega
  · simp

def TfP : ℕ → ℕ := fun s =>
  if s = 1 then 44
  else if s = 2 then 31
  else if s = 3 then 26
  else if s = 4 then 25
  else if s = 5 then 24
  else if s = 6 then 23
  else if s = 7 then 22
  else if s = 8 then 44
  else if s = 9 then 44
  else if s = 10 then 44
  else if s = 11 then 44
  else if s = 12 then 44
  else if s = 13 then 44
  else if s = 14 then 44
  else if s = 15 then 44
  else 0

def TfQ : ℕ → ℕ := fun s =>
  if s = 1 then 52
  else if s = 2 then 35
  else if s = 3 then 30
  else if s = 4 then 27
  else if s = 5 then 24
  else if s = 6 then 23
  else if s = 7 then 52
  else if s = 8 then 52
  else if s = 9 then 52
  else if s = 10 then 52
  else if s = 11 then 52
  else if s = 12 then 52
  else if s = 13 then 52
  else if s = 14 then 52
  else if s = 15 then 52
  else 0

def SA : Finset ℕ := {2, 4, 5, 8, 9, 10, 11, 16, 17, 18, 19, 20, 21, 22, 23}

def msA : List ℕ := [2, 4, 5, 8, 9, 10, 11, 16, 17, 18, 19, 20, 21, 22, 23]

def idxA : ℕ → ℕ := fun v =>
  if v = 2 then 0
  else if v = 4 then 1
  else if v = 5 then 2
  else if v = 8 then 3
  else if v = 9 then 4
  else if v = 10 then 5
  else if v = 11 then 6
  else if v = 16 then 7
  else if v = 17 then 8
  else if v = 18 then 9
  else if v = 19 then 10
  else if v = 20 then 11
  else if v = 21 then 12
  else if v = 22 then 13
  else if v = 23 then 14
  else 0

def kidsA : ℕ → List ℕ := fun v =>
  if v = 2 then [4, 5]
  else if v = 4 then [8, 9]
  else if v = 5 then [10, 11]
  else if v = 8 then [16, 17]
  else if v = 9 then [18, 19]
  else if v = 10 then [20, 21]
  else if v = 11 then [22, 23]
  else if v = 16 then []
  else if v = 17 then []
  else if v = 18 then []
  else if v = 19 then []
  else if v = 20 then []
  else if v = 21 then []
  else if v = 22 then []
  else if v = 23 then []
  else []

def SB : Finset ℕ := {3, 6, 7, 12, 13, 14, 15, 24, 25, 26, 27, 28, 29, 30, 31}

def msB : List ℕ := [3, 6, 7, 12, 13, 14, 15, 24, 25, 26, 27, 28, 29, 30, 31]

def idxB : ℕ → ℕ := fun v =>
  if v = 3 then 0
  else if v = 6 then 1
  else if v = 7 then 2
  else if v = 12 then 3
  else if v = 13 then 4
  else if v = 14 then 5
  else if v = 15 then 6
  else if v = 24 then 7
  else if v = 25 then 8
  else if v = 26 then 9
  else if v = 27 then 10
  else if v = 28 then 11
  else if v = 29 then 12
  else if v = 30 then 13
  else if v = 31 then 14
  else 0

def kidsB : ℕ → List ℕ := fun v =>
  if v = 3 then [6, 7]
  else if v = 6 then [12, 13]
  else if v = 7 then [14, 15]
  else if v = 12 then [24, 25]
  else if v = 13 then [26, 27]
  else if v = 14 then [28, 29]
  else if v = 15 then [30, 31]
  else if v = 24 then []
  else if v = 25 then []
  else if v = 26 then []
  else if v = 27 then []
  else if v = 28 then []
  else if v = 29 then []
  else if v = 30 then []
  else if v = 31 then []
  else []

#print axioms pred_irrefl

end H5Bit

end SplitLemma
