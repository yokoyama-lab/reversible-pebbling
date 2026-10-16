/-
  **ビットマップ検査器からレベル束の閉包性・全数性へ**（第60夜 周2/3 2026-09-14）。

  `LevelCertDmPeak.Dm_le_Dcert_of_levels_peak` は束 `Lv` の閉包性 `hcl` と全数性 `hmiss` を
  要求する。生成器（`night60_levelcert_gen_peak.py`）はこれを Finset の `decide` で出していたが、
  所属判定が線形走査なので $h=5$ では入らない（第60夜 周1/3 §8: 約 68 時間の見込み）。

  ここでは段を**ビットマップ `Nat`**（部分木の頂点 `v` を位置 `idx v` に置き、配置 `c` が
  段にあれば `L i` の第 `c` ビットが立つ）で持ち、Bool の検査器 `checkAll` / `missAll` を
  `decide +kernel` に掛ける前提で、**検査器が `true` を返すことから `hcl` / `hmiss` を導く**。

  橋は 4 つ（第60夜 周1/3 §9 の予告どおり）:
  * 配置の所属 ↔ `testBit`（`LvB` の定義そのもの）
  * 子の所属 ↔ `testBit`（`kids` の各頂点のビット。`hkids` で `pred` と結ぶ）
  * `toggleAt` ↔ `^^^ (1 <<< idx m)`（`toggle_decode`）
  * `card` ↔ `filter` の長さ（`card_decode`）

  ⚠ 検査器は**寛容側にだけずれてよい**（合法でない手を余分に調べても健全）。
  `kids m` が `pred m` の free でない子を全部含まなくても健全なのはそのため。
-/
import LevelCertDmPeak

set_option autoImplicit false

namespace SplitLemma

open Finset HullLemma

namespace Bit

/-! ## 1. 復号と 2 つの橋 -/

/-- ビット表現 `c` の復号: 頂点列 `ms` のうち位置 `idx v` のビットが立つもの。 -/
def decode (ms : List ℕ) (idx : ℕ → ℕ) (c : ℕ) : Finset ℕ :=
  (ms.filter (fun v => c.testBit (idx v))).toFinset

theorem mem_decode {ms : List ℕ} {idx : ℕ → ℕ} {c v : ℕ} :
    v ∈ decode ms idx c ↔ v ∈ ms ∧ c.testBit (idx v) = true := by
  simp [decode, List.mem_filter]

theorem card_decode {ms : List ℕ} (hnd : ms.Nodup) (idx : ℕ → ℕ) (c : ℕ) :
    (decode ms idx c).card = (ms.filter (fun v => c.testBit (idx v))).length := by
  unfold decode
  exact List.toFinset_card_of_nodup (hnd.filter _)

theorem decode_zero (ms : List ℕ) (idx : ℕ → ℕ) : decode ms idx 0 = ∅ := by
  ext v
  simp [mem_decode]

theorem testBit_flip {ms : List ℕ} {idx : ℕ → ℕ}
    (hinj : ∀ u ∈ ms, ∀ v ∈ ms, idx u = idx v → u = v) {m : ℕ} (hm : m ∈ ms) (c : ℕ)
    {v : ℕ} (hv : v ∈ ms) :
    (c ^^^ (1 <<< idx m)).testBit (idx v) =
      if v = m then !c.testBit (idx m) else c.testBit (idx v) := by
  rw [Nat.testBit_xor, Nat.one_shiftLeft, Nat.testBit_two_pow]
  by_cases e : v = m
  · subst e; simp
  · have hne : idx m ≠ idx v := fun e' => e (hinj v hv m hm e'.symm)
    simp [e, hne]

/-- **`toggleAt` ↔ `^^^`。** -/
theorem toggle_decode {ms : List ℕ} {idx : ℕ → ℕ}
    (hinj : ∀ u ∈ ms, ∀ v ∈ ms, idx u = idx v → u = v) {m : ℕ} (hm : m ∈ ms) (c : ℕ) :
    toggleAt (decode ms idx c) m = decode ms idx (c ^^^ (1 <<< idx m)) := by
  ext v
  unfold toggleAt
  by_cases hv : v ∈ ms
  · have hf := testBit_flip hinj hm c hv
    by_cases e : v = m
    · subst e
      split_ifs with h
      · rw [mem_decode] at h
        simp [mem_decode, hf, h.2]
      · rw [mem_decode] at h
        simp only [Finset.mem_insert, true_or, true_iff, mem_decode, hf, if_true]
        refine ⟨hv, ?_⟩
        simpa [hv] using h
    · split_ifs with h
      · simp [Finset.mem_erase, mem_decode, hf, e, hv]
      · simp [Finset.mem_insert, mem_decode, hf, e, hv]
  · have hne : v ≠ m := fun e => hv (e ▸ hm)
    split_ifs with h
    · simp [Finset.mem_erase, mem_decode, hv]
    · simp [Finset.mem_insert, mem_decode, hv, hne]

/-! ## 2. 検査器 -/

/-- 段 `Li` の配置 `c` について、`kids` のビットが立つ手 `m` の後続 `d` は
ピーク `q` を超えるか、近傍段 `Lnb` にある。 -/
def stepOk (ms : List ℕ) (idx : ℕ → ℕ) (kids : ℕ → List ℕ) (q N Li Lnb c : ℕ) : Bool :=
  !(Li.testBit c) || ms.all (fun m =>
    !((kids m).all (fun u => c.testBit (idx u))) ||
      decide (q < (ms.filter (fun v => (c ^^^ (1 <<< idx m)).testBit (idx v))).length) ||
      (decide (c ^^^ (1 <<< idx m) < N) && Lnb.testBit (c ^^^ (1 <<< idx m))))

def checkAll (ms : List ℕ) (idx : ℕ → ℕ) (kids : ℕ → List ℕ) (q N Li Lnb : ℕ) : Bool :=
  (List.range N).all (stepOk ms idx kids q N Li Lnb)

/-- 段 `Lj` の配置で頂点 `a` を含むものは、`Tf (大きさ) < j`。 -/
def missOk (ms : List ℕ) (idx : ℕ → ℕ) (Tf : ℕ → ℕ) (a j Lj c : ℕ) : Bool :=
  !(Lj.testBit c) || !(c.testBit (idx a)) ||
    decide (Tf (ms.filter (fun v => c.testBit (idx v))).length < j)

def missAll (ms : List ℕ) (idx : ℕ → ℕ) (Tf : ℕ → ℕ) (a N j Lj : ℕ) : Bool :=
  (List.range N).all (missOk ms idx Tf a j Lj)

/-- ビットマップの束。 -/
def LvB (ms : List ℕ) (idx : ℕ → ℕ) (N : ℕ) (L : ℕ → ℕ) (i : ℕ) (C : Finset ℕ) : Prop :=
  ∃ c, c < N ∧ (L i).testBit c = true ∧ decode ms idx c = C

theorem LvB_zero {ms : List ℕ} {idx : ℕ → ℕ} {N : ℕ} {L : ℕ → ℕ}
    (hN : 0 < N) (h0 : (L 0).testBit 0 = true) : LvB ms idx N L 0 ∅ :=
  ⟨0, hN, h0, decode_zero ms idx⟩

/-! ## 3. 検査器 → 閉包性・全数性 -/

theorem closed_of_check {pred : ℕ → Finset ℕ} {F A : Finset ℕ} {ms : List ℕ} {idx : ℕ → ℕ}
    {kids : ℕ → List ℕ} {q N M : ℕ} {L : ℕ → ℕ}
    (hnd : ms.Nodup) (hinj : ∀ u ∈ ms, ∀ v ∈ ms, idx u = idx v → u = v)
    (hA : ∀ m ∈ A, m ∈ ms) (hkids : ∀ m ∈ ms, ∀ u ∈ kids m, u ∈ pred m ∧ u ∉ F)
    (hchk : ∀ i, i < M →
      checkAll ms idx kids q N (L i) (L (i - 1) ||| L i ||| L (i + 1)) = true) :
    ∀ i, i < M → ∀ C : Finset ℕ, LvB ms idx N L i C → ∀ m ∈ A, m ∉ F →
      (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) → (toggleAt C m).card ≤ q →
      ∃ j, j ≤ i + 1 ∧ LvB ms idx N L j (toggleAt C m) := by
  intro i hi C hC m hmA _ hpred hq
  obtain ⟨c, hcN, hLc, hCeq⟩ := hC
  subst hCeq
  have hm := hA m hmA
  have hall := hchk i hi
  unfold checkAll at hall
  rw [List.all_eq_true] at hall
  have hs := hall c (List.mem_range.mpr hcN)
  unfold stepOk at hs
  rw [hLc] at hs
  simp only [Bool.not_true, Bool.false_or, List.all_eq_true] at hs
  have hsm := hs m hm
  have hk : ((kids m).all (fun u => c.testBit (idx u))) = true := by
    rw [List.all_eq_true]
    intro u hu
    obtain ⟨hup, huF⟩ := hkids m hm u hu
    rcases hpred u hup with h | h
    · exact (mem_decode.mp h).2
    · exact absurd h huF
  rw [hk] at hsm
  rw [toggle_decode hinj hm] at hq ⊢
  rw [card_decode hnd] at hq
  have hq' : decide (q < (ms.filter (fun v => (c ^^^ (1 <<< idx m)).testBit (idx v))).length)
      = false := by
    simp only [decide_eq_false_iff_not, not_lt]
    exact hq
  rw [hq'] at hsm
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq,
    Nat.testBit_or, Bool.or_eq_true] at hsm
  obtain ⟨hdN, hb⟩ := hsm
  rcases hb with (hb | hb) | hb
  · exact ⟨i - 1, by omega, _, hdN, hb, rfl⟩
  · exact ⟨i, by omega, _, hdN, hb, rfl⟩
  · exact ⟨i + 1, le_refl _, _, hdN, hb, rfl⟩

theorem lt_of_missCheck {ms : List ℕ} {idx : ℕ → ℕ} {Tf : ℕ → ℕ} {a N M : ℕ} {L : ℕ → ℕ}
    (hnd : ms.Nodup)
    (hchk : ∀ j, j ≤ M → missAll ms idx Tf a N j (L j) = true) :
    ∀ j, j ≤ M → ∀ C : Finset ℕ, LvB ms idx N L j C → a ∈ C → Tf C.card < j := by
  intro j hj C hC ha
  obtain ⟨c, hcN, hLc, hCeq⟩ := hC
  subst hCeq
  have hall := hchk j hj
  unfold missAll at hall
  rw [List.all_eq_true] at hall
  have hs := hall c (List.mem_range.mpr hcN)
  unfold missOk at hs
  rw [hLc, (mem_decode.mp ha).2] at hs
  simp only [Bool.not_true, Bool.false_or, decide_eq_true_eq] at hs
  rw [card_decode hnd]
  exact hs

theorem miss_of_check {ms : List ℕ} {idx : ℕ → ℕ} {Tf : ℕ → ℕ} {a N M Nn : ℕ} {L : ℕ → ℕ}
    (hnd : ms.Nodup)
    (hchk : ∀ j, j ≤ M → missAll ms idx Tf a N j (L j) = true)
    (hT : ∀ s, 1 ≤ s → s ≤ Nn → Tf s ≤ M) :
    ∀ s, 1 ≤ s → s ≤ Nn → ∀ j, j ≤ Tf s → ∀ C : Finset ℕ,
      LvB ms idx N L j C → a ∈ C → C.card ≠ s := by
  intro s h1 hs j hj C hC ha hcs
  have key := lt_of_missCheck hnd hchk j (le_trans hj (hT s h1 hs)) C hC ha
  rw [hcs] at key
  omega

/-! ## 4. まとめ: 検査器 → 表の健全性（ピーク `q0`） -/

theorem Dm_le_Dcert_of_bits_peak {pred : ℕ → Finset ℕ} {F A : Finset ℕ} {ms : List ℕ}
    {idx : ℕ → ℕ} {kids : ℕ → List ℕ} {a B M Nn N q0 : ℕ} {L : ℕ → ℕ} {Tf : ℕ → ℕ}
    (hnd : ms.Nodup) (hinj : ∀ u ∈ ms, ∀ v ∈ ms, idx u = idx v → u = v)
    (hA : ∀ m ∈ A, m ∈ ms) (hkids : ∀ m ∈ ms, ∀ u ∈ kids m, u ∈ pred m ∧ u ∉ F)
    (hN0 : 0 < N) (h0 : (L 0).testBit 0 = true)
    (hcl : ∀ i, i < M →
      checkAll ms idx kids q0 N (L i) (L (i - 1) ||| L i ||| L (i + 1)) = true)
    (hmi : ∀ j, j ≤ M → missAll ms idx Tf a N j (L j) = true)
    (hAN : A.card ≤ Nn)
    (hT : ∀ s, 1 ≤ s → s ≤ Nn → Tf s ≤ M)
    (hB : ∀ s, 1 ≤ s → s ≤ Nn → Tf s + 1 ≤ B) :
    ∀ (Y : Finset ℕ), Y ⊆ A → a ∈ Y → Tf Y.card + 1 ≤ Dcert pred F B q0 A ∅ Y :=
  Dm_le_Dcert_of_levels_peak (Lv := LvB ms idx N L) (LvB_zero hN0 h0)
    (closed_of_check hnd hinj hA hkids hcl) hAN hT (miss_of_check hnd hmi hT) hB

#print axioms toggle_decode
#print axioms card_decode
#print axioms closed_of_check
#print axioms miss_of_check
#print axioms Dm_le_Dcert_of_bits_peak

end Bit

end SplitLemma
