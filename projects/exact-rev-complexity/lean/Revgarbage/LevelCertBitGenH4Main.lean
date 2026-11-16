/-
  **ピークつきレベル束の証明書（ビットマップ＋`decide +kernel`）で $M^*(T_4,6) \ge 47$**（第60夜 周2/3・生成物）。（分割: Main）

  `autoresearch/tools/night60r2_levelcert_gen_bit.py 4 6` の出力。**手で編集しないこと。**
  表（q=6・大きさ s の最短距離）: s=1→15, s=2→12, s=3→11, s=4→10, s=5→9, s=6→8。束の状態数 127・深さ 14。
  表（q=5・大きさ s の最短距離）: s=1→17, s=2→12, s=3→11, s=4→10, s=5→9。束の状態数 120・深さ 16。
-/
import LevelCertBitGenH4AP
import LevelCertBitGenH4AQ
import LevelCertBitGenH4BP
import LevelCertBitGenH4BQ

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace SplitLemma

open Finset HullLemma Bit

namespace H4Bit
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

#print axioms hDmA
#print axioms hDmB
#print axioms hpair
#print axioms split_num_cert

end H4Bit

end SplitLemma
