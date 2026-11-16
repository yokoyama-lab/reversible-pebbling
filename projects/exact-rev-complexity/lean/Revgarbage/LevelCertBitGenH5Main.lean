/-
  **ピークつきレベル束の証明書（ビットマップ＋`decide +kernel`）で $M^*(T_5,7) \ge 121$**（第60夜 周2/3・生成物）。（分割: Main）

  `autoresearch/tools/night60r2_levelcert_gen_bit.py 5 7` の出力。**手で編集しないこと。**
  表（q=7・大きさ s の最短距離）: s=1→45, s=2→32, s=3→27, s=4→26, s=5→25, s=6→24, s=7→23。束の状態数 16384・深さ 44。
  表（q=6・大きさ s の最短距離）: s=1→53, s=2→36, s=3→31, s=4→28, s=5→25, s=6→24。束の状態数 9938・深さ 52。
-/
import LevelCertBitGenH5AP
import LevelCertBitGenH5AQ
import LevelCertBitGenH5BP
import LevelCertBitGenH5BQ

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace SplitLemma

open Finset HullLemma Bit

namespace H5Bit
theorem hDmA : ∀ (q : ℕ) (Y : Finset ℕ), Y ⊆ SA → 2 ∈ Y →
    DmTwo 7 TfP TfQ q Y.card ≤ Dcert pred F 53 q SA ∅ Y :=
  DmTwo_sound (p := 7) hDmAP hDmAQ

theorem hDmB : ∀ (q : ℕ) (Y : Finset ℕ), Y ⊆ SB → 3 ∈ Y →
    DmTwo 7 TfP TfQ q Y.card ≤ Dcert pred F 53 q SB ∅ Y :=
  DmTwo_sound (p := 7) hDmBP hDmBQ

theorem hpair : ∀ sA sB : ℕ, 1 ≤ sA → 1 ≤ sB → sA + sB + 1 ≤ 7 →
    121 ≤ (DmTwo 7 TfP TfQ 7 sA + DmTwo 7 TfP TfQ (7 - 1) sA)
      + 2 * DmTwo 7 TfP TfQ (7 - 1) sB + 1 := by
  intro sA sB hA hB hsum
  have hA' : sA ≤ 5 := by omega
  have hB' : sB ≤ 5 := by omega
  interval_cases sA <;> interval_cases sB <;> first | omega | decide

theorem split_num_cert (l : List ℕ)
    (hL : Legal pred F l ∅) (hP : Peak 7 l ∅) (hfin : run l ∅ = {1}) :
    121 ≤ l.length :=
  split_lemma_strong_num (pred := pred) (F := F) (ρ := 1) (p := 7)
    (A := SA) (B := SB) (D := Dcert pred F 53)
    pred_irrefl (Dcert_valid pred F 53)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (DmTwo 7 TfP TfQ) 121 hDmA hDmB hpair
    l hL hP hfin

#print axioms hDmA
#print axioms hDmB
#print axioms hpair
#print axioms split_num_cert

end H5Bit

end SplitLemma
