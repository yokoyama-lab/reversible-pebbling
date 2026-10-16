/-
  **証書の鍵による Lean の正準形 = 名指しの貪欲の像**（第 82 夜 周 4・2026-10-12）。

  ## どの穴を埋めるか

  第 81 夜 周 5 で ① は「(c) 橋」の 1 点に縮んだ。橋そのもの
  （`keyCert h D = 2 * codeAt h 1 D`）は `KeyBridge.lean` が示す。本ファイルは
  **橋を仮定 `hbr` として受け取り**、周 4（最小性）・周 5（到達可能性）と合成して

      ★ `canonCbtCert h C = C.image (swapAct (bG h C))`      （C ⊆ cbtV h）

  を示す。左辺は `length_ge_of_quot_levels_cbt_cert` が使う正準形（証書の鍵 `keyCert` の
  `autB h` 軌道での最小元、`pickMinK` が選ぶもの）、右辺は「各節点で左の子のコードが
  右より小さければ入れ替える」貪欲（証書 §1.2 の再帰的 `canon` と同じ規則）である。
  すなわち **Lean の下界定理が使う正準形は、証書の再帰的 canon と同じ集合を返す**。

  ## ここで示すこと / 示さないこと

  - ★ 示す: 上の等式（`hrel`・`hbr` を仮定して $h$ 一般）。`hbr` は `KeyBridge.lean` の
    `keyCert_eq_two_codeAt` で外れ（`canonCbtCert_eq_greedy`: 仮定は `hrel` だけ）、
    $h=7$ では `relabCert_inj_7` で `hrel` も外れる（`canonCbtCert_eq_greedy_7`: 仮定 0 本）。`bG h C ∈ autB h`（貪欲のビットは
    `autB h` の元）も $h$ 一般に示す。
  - ✗ 示さない: Python の証書検査器の `canon` が `bG` の規則を実装していること
    （プログラムの層。`night81r4_codecheck.py`・`night81r5_reachcheck.py` が $h\le4$ の全配置で照合）。

  ⚠ **新しい数値は 1 つも足していない。** $M^*(T_7,10)=1001$ の層は 2 のままである。
-/
import GreedyReach
import KeyBridge
import KeyCertH7

set_option autoImplicit false

namespace SplitLemma

open Finset HullLemma TreeAut HullLemmaCBT

/-- 深さは $2^h$ 以上の頂点で $h$ 以上。 -/
theorem le_depB_of_two_pow_le : ∀ (h u : ℕ), 2 ^ h ≤ u → h ≤ depB u := by
  intro h
  induction h with
  | zero => intro u _; exact Nat.zero_le _
  | succ h ih =>
    intro u hu
    have h2 : 2 ≤ u := by
      have : 2 ≤ 2 ^ (h + 1) := by
        rw [pow_succ]; have := Nat.one_le_two_pow (n := h); omega
      omega
    have hsplit : u = 2 * (u / 2) + u % 2 := (Nat.div_add_mod u 2).symm
    have hd : depB u = depB (u / 2) + 1 := by
      rw [hsplit, depB_eq (u / 2) (u % 2) (by omega) (Nat.mod_lt _ (by norm_num))]
      have : (2 * (u / 2) + u % 2) / 2 = u / 2 := by omega
      rw [this]
    have hhalf : 2 ^ h ≤ u / 2 := by
      rw [pow_succ] at hu
      omega
    rw [hd]
    have := ih (u / 2) hhalf
    omega

/-- ★ 貪欲のビットは $2^h$ 以上で `false`。したがって `autB h = bitFns (2^h)` の元。 -/
theorem bG_eq_false (h : ℕ) (C : Finset ℕ) (u : ℕ) (hu : 2 ^ h ≤ u) : bG h C u = false := by
  have hd := le_depB_of_two_pow_le h u hu
  have h0 : h - depB u - 1 = 0 := by omega
  simp only [bG, h0, canonCode, lt_irrefl, decide_false]

theorem bG_mem_autB (h : ℕ) (C : Finset ℕ) : bG h C ∈ autB h :=
  bitFns_mem (2 ^ h) (bG h C) (bG_eq_false h C)

/-- 自己同型の像は頂点集合に留まる。 -/
theorem image_swapAct_subset (b : ℕ → Bool) (h : ℕ) {C : Finset ℕ} (hC : C ⊆ cbtV h) :
    C.image (swapAct b) ⊆ cbtV h := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
  exact (swapAct_mem_cbtV b h y).mpr (hC hy)

/-- ★★ **橋を仮定すれば、Lean の正準形は名指しの貪欲の像そのもの**。 -/
theorem canonCbtCert_eq_greedy_of_bridge (h : ℕ) (C : Finset ℕ)
    (hrel : Function.Injective (relabCert h))
    (hbr : ∀ D : Finset ℕ, D ⊆ cbtV h → keyCert h D = 2 * codeAt h 1 D)
    (hC : C ⊆ cbtV h) :
    canonCbtCert h C = C.image (swapAct (bG h C)) := by
  have hkey := keyCert_injective hrel
  obtain ⟨g, hg, hcan⟩ := canonOfK_mem_orbit (keyCert h) (autB_group h) C
  obtain ⟨b, _, rfl⟩ := mem_swapGroup.mp hg
  have hcan' : canonCbtCert h C = C.image (swapAct b) := hcan
  apply hkey
  have hDmem : C.image (swapAct (bG h C)) ∈ C :: orbList (swapGroup (autB h)) C :=
    List.mem_cons_of_mem _ (mem_orbList.mpr
      ⟨swapAct (bG h C), mem_swapGroup.mpr ⟨bG h C, bG_mem_autB h C, rfl⟩, rfl⟩)
  have hle : keyCert h (canonCbtCert h C) ≤ keyCert h (C.image (swapAct (bG h C))) :=
    pickMinK_le (keyCert h) (orbList (swapGroup (autB h)) C) C _ hDmem
  have hD : keyCert h (C.image (swapAct (bG h C))) = 2 * canonCode h 1 C := by
    rw [hbr _ (image_swapAct_subset _ h hC), reach_root]
  have hge : 2 * canonCode h 1 C ≤ keyCert h (canonCbtCert h C) := by
    rw [hcan', hbr _ (image_swapAct_subset _ h hC)]
    exact Nat.mul_le_mul_left 2 (canonCode_le_root C b h)
  omega

/-- ★★ **橋（`KeyBridge.lean`）を差し込んだ形**: 仮定は `relabCert h` の単射性だけ。 -/
theorem canonCbtCert_eq_greedy (h : ℕ) (C : Finset ℕ)
    (hrel : Function.Injective (relabCert h)) (hC : C ⊆ cbtV h) :
    canonCbtCert h C = C.image (swapAct (bG h C)) :=
  canonCbtCert_eq_greedy_of_bridge h C hrel
    (fun D hD => keyCert_eq_two_codeAt h D hrel hD) hC

/-- ★★ **$T_7$ の実例**: 仮定 0 本（単射性は `KeyCertH7.lean` の `relabCert_inj_7`）。 -/
theorem canonCbtCert_eq_greedy_7 (C : Finset ℕ) (hC : C ⊆ cbtV 7) :
    canonCbtCert 7 C = C.image (swapAct (bG 7 C)) :=
  canonCbtCert_eq_greedy 7 C relabCert_inj_7 hC

#print axioms le_depB_of_two_pow_le
#print axioms bG_mem_autB
#print axioms canonCbtCert_eq_greedy_of_bridge
#print axioms canonCbtCert_eq_greedy
#print axioms canonCbtCert_eq_greedy_7

end SplitLemma
