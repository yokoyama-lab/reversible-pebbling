/-
  **ピークつきレベル束の証明書（ビットマップ＋`decide +kernel`）で $M^*(T_4,6) \ge 47$**（第60夜 周2/3・生成物）。

  `autoresearch/tools/night60r2_levelcert_gen_bit.py 4 6` の出力（変異 `BM1_drop_state`）。**手で編集しないこと。**
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

def LAP : ℕ → ℕ := fun i =>
  if i = 0 then 1
  else if i = 1 then 4295033088
  else if i = 2 then 79229376162450717666868985856
  else if i = 3 then 5213847228223717421758603113529344
  else if i = 4 then 1412629265313071876408594056691844096
  else if i = 5 then 26584559915722590421803742671772057620
  else if i = 6 then 85091442052258930015120888548486549504
  else if i = 7 then 333605409880553365368205180410003456
  else if i = 8 then 667215256615881013467640291546628096
  else if i = 9 then 41710785408778125264003108574347264
  else if i = 10 then 53169120465270483318905428077019430976
  else if i = 11 then 2825258530626143900391140737421944960
  else if i = 12 then 10427694456447434843517206227058728
  else if i = 13 then 158458752324901435333737971712
  else if i = 14 then 36893488156009169408
  else 0

theorem LbAP_cl_0 : checkAll msA idxA kidsA 6 128 (LAP 0) (LAP (0 - 1) ||| LAP 0 ||| LAP (0 + 1)) = true := by
  decide +kernel

theorem LbAP_cl_1 : checkAll msA idxA kidsA 6 128 (LAP 1) (LAP (1 - 1) ||| LAP 1 ||| LAP (1 + 1)) = true := by
  decide +kernel

theorem LbAP_cl_2 : checkAll msA idxA kidsA 6 128 (LAP 2) (LAP (2 - 1) ||| LAP 2 ||| LAP (2 + 1)) = true := by
  decide +kernel

theorem LbAP_cl_3 : checkAll msA idxA kidsA 6 128 (LAP 3) (LAP (3 - 1) ||| LAP 3 ||| LAP (3 + 1)) = true := by
  decide +kernel

theorem LbAP_cl_4 : checkAll msA idxA kidsA 6 128 (LAP 4) (LAP (4 - 1) ||| LAP 4 ||| LAP (4 + 1)) = true := by
  decide +kernel

theorem LbAP_cl_5 : checkAll msA idxA kidsA 6 128 (LAP 5) (LAP (5 - 1) ||| LAP 5 ||| LAP (5 + 1)) = true := by
  decide +kernel

theorem LbAP_cl_6 : checkAll msA idxA kidsA 6 128 (LAP 6) (LAP (6 - 1) ||| LAP 6 ||| LAP (6 + 1)) = true := by
  decide +kernel

theorem LbAP_cl_7 : checkAll msA idxA kidsA 6 128 (LAP 7) (LAP (7 - 1) ||| LAP 7 ||| LAP (7 + 1)) = true := by
  decide +kernel

theorem LbAP_cl_8 : checkAll msA idxA kidsA 6 128 (LAP 8) (LAP (8 - 1) ||| LAP 8 ||| LAP (8 + 1)) = true := by
  decide +kernel

theorem LbAP_cl_9 : checkAll msA idxA kidsA 6 128 (LAP 9) (LAP (9 - 1) ||| LAP 9 ||| LAP (9 + 1)) = true := by
  decide +kernel

theorem LbAP_cl_10 : checkAll msA idxA kidsA 6 128 (LAP 10) (LAP (10 - 1) ||| LAP 10 ||| LAP (10 + 1)) = true := by
  decide +kernel

theorem LbAP_cl_11 : checkAll msA idxA kidsA 6 128 (LAP 11) (LAP (11 - 1) ||| LAP 11 ||| LAP (11 + 1)) = true := by
  decide +kernel

theorem LbAP_cl_12 : checkAll msA idxA kidsA 6 128 (LAP 12) (LAP (12 - 1) ||| LAP 12 ||| LAP (12 + 1)) = true := by
  decide +kernel

theorem LbAP_cl_13 : checkAll msA idxA kidsA 6 128 (LAP 13) (LAP (13 - 1) ||| LAP 13 ||| LAP (13 + 1)) = true := by
  decide +kernel

theorem LbAP_closed : ∀ i, i < 14 → checkAll msA idxA kidsA 6 128 (LAP i) (LAP (i - 1) ||| LAP i ||| LAP (i + 1)) = true := by
  intro i hi
  interval_cases i
  · exact LbAP_cl_0
  · exact LbAP_cl_1
  · exact LbAP_cl_2
  · exact LbAP_cl_3
  · exact LbAP_cl_4
  · exact LbAP_cl_5
  · exact LbAP_cl_6
  · exact LbAP_cl_7
  · exact LbAP_cl_8
  · exact LbAP_cl_9
  · exact LbAP_cl_10
  · exact LbAP_cl_11
  · exact LbAP_cl_12
  · exact LbAP_cl_13

theorem LbAP_mi_0 : missAll msA idxA TfP 2 128 0 (LAP 0) = true := by decide +kernel
theorem LbAP_mi_1 : missAll msA idxA TfP 2 128 1 (LAP 1) = true := by decide +kernel
theorem LbAP_mi_2 : missAll msA idxA TfP 2 128 2 (LAP 2) = true := by decide +kernel
theorem LbAP_mi_3 : missAll msA idxA TfP 2 128 3 (LAP 3) = true := by decide +kernel
theorem LbAP_mi_4 : missAll msA idxA TfP 2 128 4 (LAP 4) = true := by decide +kernel
theorem LbAP_mi_5 : missAll msA idxA TfP 2 128 5 (LAP 5) = true := by decide +kernel
theorem LbAP_mi_6 : missAll msA idxA TfP 2 128 6 (LAP 6) = true := by decide +kernel
theorem LbAP_mi_7 : missAll msA idxA TfP 2 128 7 (LAP 7) = true := by decide +kernel
theorem LbAP_mi_8 : missAll msA idxA TfP 2 128 8 (LAP 8) = true := by decide +kernel
theorem LbAP_mi_9 : missAll msA idxA TfP 2 128 9 (LAP 9) = true := by decide +kernel
theorem LbAP_mi_10 : missAll msA idxA TfP 2 128 10 (LAP 10) = true := by decide +kernel
theorem LbAP_mi_11 : missAll msA idxA TfP 2 128 11 (LAP 11) = true := by decide +kernel
theorem LbAP_mi_12 : missAll msA idxA TfP 2 128 12 (LAP 12) = true := by decide +kernel
theorem LbAP_mi_13 : missAll msA idxA TfP 2 128 13 (LAP 13) = true := by decide +kernel
theorem LbAP_mi_14 : missAll msA idxA TfP 2 128 14 (LAP 14) = true := by decide +kernel

theorem LbAP_miss : ∀ j, j ≤ 14 → missAll msA idxA TfP 2 128 j (LAP j) = true := by
  intro j hj
  interval_cases j
  · exact LbAP_mi_0
  · exact LbAP_mi_1
  · exact LbAP_mi_2
  · exact LbAP_mi_3
  · exact LbAP_mi_4
  · exact LbAP_mi_5
  · exact LbAP_mi_6
  · exact LbAP_mi_7
  · exact LbAP_mi_8
  · exact LbAP_mi_9
  · exact LbAP_mi_10
  · exact LbAP_mi_11
  · exact LbAP_mi_12
  · exact LbAP_mi_13
  · exact LbAP_mi_14

theorem hDmAP : ∀ (Y : Finset ℕ), Y ⊆ SA → 2 ∈ Y →
    TfP Y.card + 1 ≤ Dcert pred F 17 6 SA ∅ Y :=
  Dm_le_Dcert_of_bits_peak (pred := pred) (F := F) (A := SA) (ms := msA) (idx := idxA)
    (kids := kidsA) (a := 2) (B := 17) (M := 14) (Nn := 7) (N := 128) (q0 := 6)
    (L := LAP) (Tf := TfP)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
    LbAP_closed LbAP_miss (by decide)
    (by intro s h1 hN; interval_cases s <;> decide)
    (by intro s h1 hN; interval_cases s <;> decide)

def LAQ : ℕ → ℕ := fun i =>
  if i = 0 then 1
  else if i = 1 then 18446744078004584704
  else if i = 2 then 79229376162450717666868985856
  else if i = 3 then 5213847228223717421758603113529344
  else if i = 4 then 1412629265313071876408594056691844096
  else if i = 5 then 26584559915722590421803742671772057620
  else if i = 6 then 20850322024314149277236690544496640
  else if i = 7 then 333605409880553365368205180410003456
  else if i = 8 then 5070680074396845930679615094784
  else if i = 9 then 10141360149974283482351523610624
  else if i = 10 then 633825302475297942733475315776
  else if i = 11 then 41700644048628298554473381088993408
  else if i = 12 then 48545927455202932330332200
  else if i = 13 then 166802539056312007009573992822999040
  else if i = 14 then 10427694456447434843517206227058688
  else if i = 15 then 2658456150028584070709049454298660864
  else if i = 16 then 36893488156009169408
  else 0

theorem LbAQ_cl_0 : checkAll msA idxA kidsA 5 128 (LAQ 0) (LAQ (0 - 1) ||| LAQ 0 ||| LAQ (0 + 1)) = true := by
  decide +kernel

theorem LbAQ_cl_1 : checkAll msA idxA kidsA 5 128 (LAQ 1) (LAQ (1 - 1) ||| LAQ 1 ||| LAQ (1 + 1)) = true := by
  decide +kernel

theorem LbAQ_cl_2 : checkAll msA idxA kidsA 5 128 (LAQ 2) (LAQ (2 - 1) ||| LAQ 2 ||| LAQ (2 + 1)) = true := by
  decide +kernel

theorem LbAQ_cl_3 : checkAll msA idxA kidsA 5 128 (LAQ 3) (LAQ (3 - 1) ||| LAQ 3 ||| LAQ (3 + 1)) = true := by
  decide +kernel

theorem LbAQ_cl_4 : checkAll msA idxA kidsA 5 128 (LAQ 4) (LAQ (4 - 1) ||| LAQ 4 ||| LAQ (4 + 1)) = true := by
  decide +kernel

theorem LbAQ_cl_5 : checkAll msA idxA kidsA 5 128 (LAQ 5) (LAQ (5 - 1) ||| LAQ 5 ||| LAQ (5 + 1)) = true := by
  decide +kernel

theorem LbAQ_cl_6 : checkAll msA idxA kidsA 5 128 (LAQ 6) (LAQ (6 - 1) ||| LAQ 6 ||| LAQ (6 + 1)) = true := by
  decide +kernel

theorem LbAQ_cl_7 : checkAll msA idxA kidsA 5 128 (LAQ 7) (LAQ (7 - 1) ||| LAQ 7 ||| LAQ (7 + 1)) = true := by
  decide +kernel

theorem LbAQ_cl_8 : checkAll msA idxA kidsA 5 128 (LAQ 8) (LAQ (8 - 1) ||| LAQ 8 ||| LAQ (8 + 1)) = true := by
  decide +kernel

theorem LbAQ_cl_9 : checkAll msA idxA kidsA 5 128 (LAQ 9) (LAQ (9 - 1) ||| LAQ 9 ||| LAQ (9 + 1)) = true := by
  decide +kernel

theorem LbAQ_cl_10 : checkAll msA idxA kidsA 5 128 (LAQ 10) (LAQ (10 - 1) ||| LAQ 10 ||| LAQ (10 + 1)) = true := by
  decide +kernel

theorem LbAQ_cl_11 : checkAll msA idxA kidsA 5 128 (LAQ 11) (LAQ (11 - 1) ||| LAQ 11 ||| LAQ (11 + 1)) = true := by
  decide +kernel

theorem LbAQ_cl_12 : checkAll msA idxA kidsA 5 128 (LAQ 12) (LAQ (12 - 1) ||| LAQ 12 ||| LAQ (12 + 1)) = true := by
  decide +kernel

theorem LbAQ_cl_13 : checkAll msA idxA kidsA 5 128 (LAQ 13) (LAQ (13 - 1) ||| LAQ 13 ||| LAQ (13 + 1)) = true := by
  decide +kernel

theorem LbAQ_cl_14 : checkAll msA idxA kidsA 5 128 (LAQ 14) (LAQ (14 - 1) ||| LAQ 14 ||| LAQ (14 + 1)) = true := by
  decide +kernel

theorem LbAQ_cl_15 : checkAll msA idxA kidsA 5 128 (LAQ 15) (LAQ (15 - 1) ||| LAQ 15 ||| LAQ (15 + 1)) = true := by
  decide +kernel

theorem LbAQ_closed : ∀ i, i < 16 → checkAll msA idxA kidsA 5 128 (LAQ i) (LAQ (i - 1) ||| LAQ i ||| LAQ (i + 1)) = true := by
  intro i hi
  interval_cases i
  · exact LbAQ_cl_0
  · exact LbAQ_cl_1
  · exact LbAQ_cl_2
  · exact LbAQ_cl_3
  · exact LbAQ_cl_4
  · exact LbAQ_cl_5
  · exact LbAQ_cl_6
  · exact LbAQ_cl_7
  · exact LbAQ_cl_8
  · exact LbAQ_cl_9
  · exact LbAQ_cl_10
  · exact LbAQ_cl_11
  · exact LbAQ_cl_12
  · exact LbAQ_cl_13
  · exact LbAQ_cl_14
  · exact LbAQ_cl_15

theorem LbAQ_mi_0 : missAll msA idxA TfQ 2 128 0 (LAQ 0) = true := by decide +kernel
theorem LbAQ_mi_1 : missAll msA idxA TfQ 2 128 1 (LAQ 1) = true := by decide +kernel
theorem LbAQ_mi_2 : missAll msA idxA TfQ 2 128 2 (LAQ 2) = true := by decide +kernel
theorem LbAQ_mi_3 : missAll msA idxA TfQ 2 128 3 (LAQ 3) = true := by decide +kernel
theorem LbAQ_mi_4 : missAll msA idxA TfQ 2 128 4 (LAQ 4) = true := by decide +kernel
theorem LbAQ_mi_5 : missAll msA idxA TfQ 2 128 5 (LAQ 5) = true := by decide +kernel
theorem LbAQ_mi_6 : missAll msA idxA TfQ 2 128 6 (LAQ 6) = true := by decide +kernel
theorem LbAQ_mi_7 : missAll msA idxA TfQ 2 128 7 (LAQ 7) = true := by decide +kernel
theorem LbAQ_mi_8 : missAll msA idxA TfQ 2 128 8 (LAQ 8) = true := by decide +kernel
theorem LbAQ_mi_9 : missAll msA idxA TfQ 2 128 9 (LAQ 9) = true := by decide +kernel
theorem LbAQ_mi_10 : missAll msA idxA TfQ 2 128 10 (LAQ 10) = true := by decide +kernel
theorem LbAQ_mi_11 : missAll msA idxA TfQ 2 128 11 (LAQ 11) = true := by decide +kernel
theorem LbAQ_mi_12 : missAll msA idxA TfQ 2 128 12 (LAQ 12) = true := by decide +kernel
theorem LbAQ_mi_13 : missAll msA idxA TfQ 2 128 13 (LAQ 13) = true := by decide +kernel
theorem LbAQ_mi_14 : missAll msA idxA TfQ 2 128 14 (LAQ 14) = true := by decide +kernel
theorem LbAQ_mi_15 : missAll msA idxA TfQ 2 128 15 (LAQ 15) = true := by decide +kernel
theorem LbAQ_mi_16 : missAll msA idxA TfQ 2 128 16 (LAQ 16) = true := by decide +kernel

theorem LbAQ_miss : ∀ j, j ≤ 16 → missAll msA idxA TfQ 2 128 j (LAQ j) = true := by
  intro j hj
  interval_cases j
  · exact LbAQ_mi_0
  · exact LbAQ_mi_1
  · exact LbAQ_mi_2
  · exact LbAQ_mi_3
  · exact LbAQ_mi_4
  · exact LbAQ_mi_5
  · exact LbAQ_mi_6
  · exact LbAQ_mi_7
  · exact LbAQ_mi_8
  · exact LbAQ_mi_9
  · exact LbAQ_mi_10
  · exact LbAQ_mi_11
  · exact LbAQ_mi_12
  · exact LbAQ_mi_13
  · exact LbAQ_mi_14
  · exact LbAQ_mi_15
  · exact LbAQ_mi_16

theorem hDmAQ : ∀ (Y : Finset ℕ), Y ⊆ SA → 2 ∈ Y →
    TfQ Y.card + 1 ≤ Dcert pred F 17 5 SA ∅ Y :=
  Dm_le_Dcert_of_bits_peak (pred := pred) (F := F) (A := SA) (ms := msA) (idx := idxA)
    (kids := kidsA) (a := 2) (B := 17) (M := 16) (Nn := 7) (N := 128) (q0 := 5)
    (L := LAQ) (Tf := TfQ)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
    LbAQ_closed LbAQ_miss (by decide)
    (by intro s h1 hN; interval_cases s <;> decide)
    (by intro s h1 hN; interval_cases s <;> decide)

def LBP : ℕ → ℕ := fun i =>
  if i = 0 then 1
  else if i = 1 then 18446744078004584704
  else if i = 2 then 79229376162450717666868985856
  else if i = 3 then 5213847228223717421758603113529344
  else if i = 4 then 1412629265313071876408594056691844096
  else if i = 5 then 26584559915722590421803742671772057620
  else if i = 6 then 85091442052258930015120888548486549504
  else if i = 7 then 333605409880553365368205180410003456
  else if i = 8 then 667215256615881013467640291546628096
  else if i = 9 then 41710785408778125264003108574347264
  else if i = 10 then 53169120465270483318905428077019430976
  else if i = 11 then 2825258530626143900391140737421944960
  else if i = 12 then 10427694456447434843517206227058728
  else if i = 13 then 158458752324901435333737971712
  else if i = 14 then 36893488156009169408
  else 0

theorem LbBP_cl_0 : checkAll msB idxB kidsB 6 128 (LBP 0) (LBP (0 - 1) ||| LBP 0 ||| LBP (0 + 1)) = true := by
  decide +kernel

theorem LbBP_cl_1 : checkAll msB idxB kidsB 6 128 (LBP 1) (LBP (1 - 1) ||| LBP 1 ||| LBP (1 + 1)) = true := by
  decide +kernel

theorem LbBP_cl_2 : checkAll msB idxB kidsB 6 128 (LBP 2) (LBP (2 - 1) ||| LBP 2 ||| LBP (2 + 1)) = true := by
  decide +kernel

theorem LbBP_cl_3 : checkAll msB idxB kidsB 6 128 (LBP 3) (LBP (3 - 1) ||| LBP 3 ||| LBP (3 + 1)) = true := by
  decide +kernel

theorem LbBP_cl_4 : checkAll msB idxB kidsB 6 128 (LBP 4) (LBP (4 - 1) ||| LBP 4 ||| LBP (4 + 1)) = true := by
  decide +kernel

theorem LbBP_cl_5 : checkAll msB idxB kidsB 6 128 (LBP 5) (LBP (5 - 1) ||| LBP 5 ||| LBP (5 + 1)) = true := by
  decide +kernel

theorem LbBP_cl_6 : checkAll msB idxB kidsB 6 128 (LBP 6) (LBP (6 - 1) ||| LBP 6 ||| LBP (6 + 1)) = true := by
  decide +kernel

theorem LbBP_cl_7 : checkAll msB idxB kidsB 6 128 (LBP 7) (LBP (7 - 1) ||| LBP 7 ||| LBP (7 + 1)) = true := by
  decide +kernel

theorem LbBP_cl_8 : checkAll msB idxB kidsB 6 128 (LBP 8) (LBP (8 - 1) ||| LBP 8 ||| LBP (8 + 1)) = true := by
  decide +kernel

theorem LbBP_cl_9 : checkAll msB idxB kidsB 6 128 (LBP 9) (LBP (9 - 1) ||| LBP 9 ||| LBP (9 + 1)) = true := by
  decide +kernel

theorem LbBP_cl_10 : checkAll msB idxB kidsB 6 128 (LBP 10) (LBP (10 - 1) ||| LBP 10 ||| LBP (10 + 1)) = true := by
  decide +kernel

theorem LbBP_cl_11 : checkAll msB idxB kidsB 6 128 (LBP 11) (LBP (11 - 1) ||| LBP 11 ||| LBP (11 + 1)) = true := by
  decide +kernel

theorem LbBP_cl_12 : checkAll msB idxB kidsB 6 128 (LBP 12) (LBP (12 - 1) ||| LBP 12 ||| LBP (12 + 1)) = true := by
  decide +kernel

theorem LbBP_cl_13 : checkAll msB idxB kidsB 6 128 (LBP 13) (LBP (13 - 1) ||| LBP 13 ||| LBP (13 + 1)) = true := by
  decide +kernel

theorem LbBP_closed : ∀ i, i < 14 → checkAll msB idxB kidsB 6 128 (LBP i) (LBP (i - 1) ||| LBP i ||| LBP (i + 1)) = true := by
  intro i hi
  interval_cases i
  · exact LbBP_cl_0
  · exact LbBP_cl_1
  · exact LbBP_cl_2
  · exact LbBP_cl_3
  · exact LbBP_cl_4
  · exact LbBP_cl_5
  · exact LbBP_cl_6
  · exact LbBP_cl_7
  · exact LbBP_cl_8
  · exact LbBP_cl_9
  · exact LbBP_cl_10
  · exact LbBP_cl_11
  · exact LbBP_cl_12
  · exact LbBP_cl_13

theorem LbBP_mi_0 : missAll msB idxB TfP 3 128 0 (LBP 0) = true := by decide +kernel
theorem LbBP_mi_1 : missAll msB idxB TfP 3 128 1 (LBP 1) = true := by decide +kernel
theorem LbBP_mi_2 : missAll msB idxB TfP 3 128 2 (LBP 2) = true := by decide +kernel
theorem LbBP_mi_3 : missAll msB idxB TfP 3 128 3 (LBP 3) = true := by decide +kernel
theorem LbBP_mi_4 : missAll msB idxB TfP 3 128 4 (LBP 4) = true := by decide +kernel
theorem LbBP_mi_5 : missAll msB idxB TfP 3 128 5 (LBP 5) = true := by decide +kernel
theorem LbBP_mi_6 : missAll msB idxB TfP 3 128 6 (LBP 6) = true := by decide +kernel
theorem LbBP_mi_7 : missAll msB idxB TfP 3 128 7 (LBP 7) = true := by decide +kernel
theorem LbBP_mi_8 : missAll msB idxB TfP 3 128 8 (LBP 8) = true := by decide +kernel
theorem LbBP_mi_9 : missAll msB idxB TfP 3 128 9 (LBP 9) = true := by decide +kernel
theorem LbBP_mi_10 : missAll msB idxB TfP 3 128 10 (LBP 10) = true := by decide +kernel
theorem LbBP_mi_11 : missAll msB idxB TfP 3 128 11 (LBP 11) = true := by decide +kernel
theorem LbBP_mi_12 : missAll msB idxB TfP 3 128 12 (LBP 12) = true := by decide +kernel
theorem LbBP_mi_13 : missAll msB idxB TfP 3 128 13 (LBP 13) = true := by decide +kernel
theorem LbBP_mi_14 : missAll msB idxB TfP 3 128 14 (LBP 14) = true := by decide +kernel

theorem LbBP_miss : ∀ j, j ≤ 14 → missAll msB idxB TfP 3 128 j (LBP j) = true := by
  intro j hj
  interval_cases j
  · exact LbBP_mi_0
  · exact LbBP_mi_1
  · exact LbBP_mi_2
  · exact LbBP_mi_3
  · exact LbBP_mi_4
  · exact LbBP_mi_5
  · exact LbBP_mi_6
  · exact LbBP_mi_7
  · exact LbBP_mi_8
  · exact LbBP_mi_9
  · exact LbBP_mi_10
  · exact LbBP_mi_11
  · exact LbBP_mi_12
  · exact LbBP_mi_13
  · exact LbBP_mi_14

theorem hDmBP : ∀ (Y : Finset ℕ), Y ⊆ SB → 3 ∈ Y →
    TfP Y.card + 1 ≤ Dcert pred F 17 6 SB ∅ Y :=
  Dm_le_Dcert_of_bits_peak (pred := pred) (F := F) (A := SB) (ms := msB) (idx := idxB)
    (kids := kidsB) (a := 3) (B := 17) (M := 14) (Nn := 7) (N := 128) (q0 := 6)
    (L := LBP) (Tf := TfP)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
    LbBP_closed LbBP_miss (by decide)
    (by intro s h1 hN; interval_cases s <;> decide)
    (by intro s h1 hN; interval_cases s <;> decide)

def LBQ : ℕ → ℕ := fun i =>
  if i = 0 then 1
  else if i = 1 then 18446744078004584704
  else if i = 2 then 79229376162450717666868985856
  else if i = 3 then 5213847228223717421758603113529344
  else if i = 4 then 1412629265313071876408594056691844096
  else if i = 5 then 26584559915722590421803742671772057620
  else if i = 6 then 20850322024314149277236690544496640
  else if i = 7 then 333605409880553365368205180410003456
  else if i = 8 then 5070680074396845930679615094784
  else if i = 9 then 10141360149974283482351523610624
  else if i = 10 then 633825302475297942733475315776
  else if i = 11 then 41700644048628298554473381088993408
  else if i = 12 then 48545927455202932330332200
  else if i = 13 then 166802539056312007009573992822999040
  else if i = 14 then 10427694456447434843517206227058688
  else if i = 15 then 2658456150028584070709049454298660864
  else if i = 16 then 36893488156009169408
  else 0

theorem LbBQ_cl_0 : checkAll msB idxB kidsB 5 128 (LBQ 0) (LBQ (0 - 1) ||| LBQ 0 ||| LBQ (0 + 1)) = true := by
  decide +kernel

theorem LbBQ_cl_1 : checkAll msB idxB kidsB 5 128 (LBQ 1) (LBQ (1 - 1) ||| LBQ 1 ||| LBQ (1 + 1)) = true := by
  decide +kernel

theorem LbBQ_cl_2 : checkAll msB idxB kidsB 5 128 (LBQ 2) (LBQ (2 - 1) ||| LBQ 2 ||| LBQ (2 + 1)) = true := by
  decide +kernel

theorem LbBQ_cl_3 : checkAll msB idxB kidsB 5 128 (LBQ 3) (LBQ (3 - 1) ||| LBQ 3 ||| LBQ (3 + 1)) = true := by
  decide +kernel

theorem LbBQ_cl_4 : checkAll msB idxB kidsB 5 128 (LBQ 4) (LBQ (4 - 1) ||| LBQ 4 ||| LBQ (4 + 1)) = true := by
  decide +kernel

theorem LbBQ_cl_5 : checkAll msB idxB kidsB 5 128 (LBQ 5) (LBQ (5 - 1) ||| LBQ 5 ||| LBQ (5 + 1)) = true := by
  decide +kernel

theorem LbBQ_cl_6 : checkAll msB idxB kidsB 5 128 (LBQ 6) (LBQ (6 - 1) ||| LBQ 6 ||| LBQ (6 + 1)) = true := by
  decide +kernel

theorem LbBQ_cl_7 : checkAll msB idxB kidsB 5 128 (LBQ 7) (LBQ (7 - 1) ||| LBQ 7 ||| LBQ (7 + 1)) = true := by
  decide +kernel

theorem LbBQ_cl_8 : checkAll msB idxB kidsB 5 128 (LBQ 8) (LBQ (8 - 1) ||| LBQ 8 ||| LBQ (8 + 1)) = true := by
  decide +kernel

theorem LbBQ_cl_9 : checkAll msB idxB kidsB 5 128 (LBQ 9) (LBQ (9 - 1) ||| LBQ 9 ||| LBQ (9 + 1)) = true := by
  decide +kernel

theorem LbBQ_cl_10 : checkAll msB idxB kidsB 5 128 (LBQ 10) (LBQ (10 - 1) ||| LBQ 10 ||| LBQ (10 + 1)) = true := by
  decide +kernel

theorem LbBQ_cl_11 : checkAll msB idxB kidsB 5 128 (LBQ 11) (LBQ (11 - 1) ||| LBQ 11 ||| LBQ (11 + 1)) = true := by
  decide +kernel

theorem LbBQ_cl_12 : checkAll msB idxB kidsB 5 128 (LBQ 12) (LBQ (12 - 1) ||| LBQ 12 ||| LBQ (12 + 1)) = true := by
  decide +kernel

theorem LbBQ_cl_13 : checkAll msB idxB kidsB 5 128 (LBQ 13) (LBQ (13 - 1) ||| LBQ 13 ||| LBQ (13 + 1)) = true := by
  decide +kernel

theorem LbBQ_cl_14 : checkAll msB idxB kidsB 5 128 (LBQ 14) (LBQ (14 - 1) ||| LBQ 14 ||| LBQ (14 + 1)) = true := by
  decide +kernel

theorem LbBQ_cl_15 : checkAll msB idxB kidsB 5 128 (LBQ 15) (LBQ (15 - 1) ||| LBQ 15 ||| LBQ (15 + 1)) = true := by
  decide +kernel

theorem LbBQ_closed : ∀ i, i < 16 → checkAll msB idxB kidsB 5 128 (LBQ i) (LBQ (i - 1) ||| LBQ i ||| LBQ (i + 1)) = true := by
  intro i hi
  interval_cases i
  · exact LbBQ_cl_0
  · exact LbBQ_cl_1
  · exact LbBQ_cl_2
  · exact LbBQ_cl_3
  · exact LbBQ_cl_4
  · exact LbBQ_cl_5
  · exact LbBQ_cl_6
  · exact LbBQ_cl_7
  · exact LbBQ_cl_8
  · exact LbBQ_cl_9
  · exact LbBQ_cl_10
  · exact LbBQ_cl_11
  · exact LbBQ_cl_12
  · exact LbBQ_cl_13
  · exact LbBQ_cl_14
  · exact LbBQ_cl_15

theorem LbBQ_mi_0 : missAll msB idxB TfQ 3 128 0 (LBQ 0) = true := by decide +kernel
theorem LbBQ_mi_1 : missAll msB idxB TfQ 3 128 1 (LBQ 1) = true := by decide +kernel
theorem LbBQ_mi_2 : missAll msB idxB TfQ 3 128 2 (LBQ 2) = true := by decide +kernel
theorem LbBQ_mi_3 : missAll msB idxB TfQ 3 128 3 (LBQ 3) = true := by decide +kernel
theorem LbBQ_mi_4 : missAll msB idxB TfQ 3 128 4 (LBQ 4) = true := by decide +kernel
theorem LbBQ_mi_5 : missAll msB idxB TfQ 3 128 5 (LBQ 5) = true := by decide +kernel
theorem LbBQ_mi_6 : missAll msB idxB TfQ 3 128 6 (LBQ 6) = true := by decide +kernel
theorem LbBQ_mi_7 : missAll msB idxB TfQ 3 128 7 (LBQ 7) = true := by decide +kernel
theorem LbBQ_mi_8 : missAll msB idxB TfQ 3 128 8 (LBQ 8) = true := by decide +kernel
theorem LbBQ_mi_9 : missAll msB idxB TfQ 3 128 9 (LBQ 9) = true := by decide +kernel
theorem LbBQ_mi_10 : missAll msB idxB TfQ 3 128 10 (LBQ 10) = true := by decide +kernel
theorem LbBQ_mi_11 : missAll msB idxB TfQ 3 128 11 (LBQ 11) = true := by decide +kernel
theorem LbBQ_mi_12 : missAll msB idxB TfQ 3 128 12 (LBQ 12) = true := by decide +kernel
theorem LbBQ_mi_13 : missAll msB idxB TfQ 3 128 13 (LBQ 13) = true := by decide +kernel
theorem LbBQ_mi_14 : missAll msB idxB TfQ 3 128 14 (LBQ 14) = true := by decide +kernel
theorem LbBQ_mi_15 : missAll msB idxB TfQ 3 128 15 (LBQ 15) = true := by decide +kernel
theorem LbBQ_mi_16 : missAll msB idxB TfQ 3 128 16 (LBQ 16) = true := by decide +kernel

theorem LbBQ_miss : ∀ j, j ≤ 16 → missAll msB idxB TfQ 3 128 j (LBQ j) = true := by
  intro j hj
  interval_cases j
  · exact LbBQ_mi_0
  · exact LbBQ_mi_1
  · exact LbBQ_mi_2
  · exact LbBQ_mi_3
  · exact LbBQ_mi_4
  · exact LbBQ_mi_5
  · exact LbBQ_mi_6
  · exact LbBQ_mi_7
  · exact LbBQ_mi_8
  · exact LbBQ_mi_9
  · exact LbBQ_mi_10
  · exact LbBQ_mi_11
  · exact LbBQ_mi_12
  · exact LbBQ_mi_13
  · exact LbBQ_mi_14
  · exact LbBQ_mi_15
  · exact LbBQ_mi_16

theorem hDmBQ : ∀ (Y : Finset ℕ), Y ⊆ SB → 3 ∈ Y →
    TfQ Y.card + 1 ≤ Dcert pred F 17 5 SB ∅ Y :=
  Dm_le_Dcert_of_bits_peak (pred := pred) (F := F) (A := SB) (ms := msB) (idx := idxB)
    (kids := kidsB) (a := 3) (B := 17) (M := 16) (Nn := 7) (N := 128) (q0 := 5)
    (L := LBQ) (Tf := TfQ)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
    LbBQ_closed LbBQ_miss (by decide)
    (by intro s h1 hN; interval_cases s <;> decide)
    (by intro s h1 hN; interval_cases s <;> decide)

theorem hDmA : ∀ (q : ℕ) (Y : Finset ℕ), Y ⊆ SA → 2 ∈ Y →
    DmTwo 6 TfP TfQ q Y.card ≤ Dcert pred F 17 q SA ∅ Y :=
  DmTwo_sound (p := 6) hDmAP hDmAQ

theorem hDmB : ∀ (q : ℕ) (Y : Finset ℕ), Y ⊆ SB → 3 ∈ Y →
    DmTwo 6 TfP TfQ q Y.card ≤ Dcert pred F 17 q SB ∅ Y :=
  DmTwo_sound (p := 6) hDmBP hDmBQ

theorem hpair : ∀ sA sB : ℕ, 1 ≤ sA → 1 ≤ sB → sA + sB + 1 ≤ 6 →
    47 ≤ (DmTwo 6 TfP TfQ 6 sA + DmTwo 6 TfP TfQ (6 - 1) sA)
      + 2 * DmTwo 6 TfP TfQ (6 - 1) sB + 1 := by
  intro sA sB hA hB hsum
  have hA' : sA ≤ 4 := by omega
  have hB' : sB ≤ 4 := by omega
  interval_cases sA <;> interval_cases sB <;> first | omega | decide

theorem split_num_cert (l : List ℕ)
    (hL : Legal pred F l ∅) (hP : Peak 6 l ∅) (hfin : run l ∅ = {1}) :
    47 ≤ l.length :=
  split_lemma_strong_num (pred := pred) (F := F) (ρ := 1) (p := 6)
    (A := SA) (B := SB) (D := Dcert pred F 17)
    pred_irrefl (Dcert_valid pred F 17)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (DmTwo 6 TfP TfQ) 47 hDmA hDmB hpair
    l hL hP hfin

#print axioms pred_irrefl
#print axioms LbAP_closed
#print axioms LbAP_miss
#print axioms hDmAP
#print axioms LbAQ_closed
#print axioms LbAQ_miss
#print axioms hDmAQ
#print axioms LbBP_closed
#print axioms LbBP_miss
#print axioms hDmBP
#print axioms LbBQ_closed
#print axioms LbBQ_miss
#print axioms hDmBQ
#print axioms hDmA
#print axioms hDmB
#print axioms hpair
#print axioms split_num_cert

end H4Bit

end SplitLemma
