/-
  **$T_3$ の Aut 商レベル集合証書 → $M^*(T_3,5)\ge 17$**（第79夜 周4・2026-10-10）。

  `autoresearch/tools/night79r4_gen_t3_quot.py` の出力。**手で編集しないこと。**

  `LevelCertGrp.lean` の一般機構を、$T_2$ とは別の木で使ってみる回である。
  木ごとに用意したのは **`G` の表 8 本と、有限検査 4 つ（群・`S`・`F`・先行点）だけ**で、
  `canon` は 1 行も書いていない（`canonOf GT3` がそれ）。

  - 内部頂点 `1..7`（heap 番号）・葉 `8..15` は free・ピーク `p = p_min(T_3) = 5`。
  - Aut(T_3) は位数 8（根での左右交換と、各内部頂点での子の交換）。
    原グラフの錐は 120 状態、商は **38 状態**（レベル 0..17）。
  - 得られる下界 17 は既知値 $M^*(T_3,5)=17$ に**ちょうど一致**（証人つき。下の `quot_h3_witness`）。

  ⚠ 新しい数値は足していない。$h=7$ の証書を Lean に通したのではない。
-/
import LevelCertGrp

set_option autoImplicit false
set_option maxRecDepth 8000
-- ⚠ 17 手の証人の `Legal` / `Peak` は `simp only` で展開すると入れ子の `if` が深くなり、
-- `Decidable` の合成が既定の `synthInstance.maxSize = 128` で落ちる（証明の不備ではない）。
set_option synthInstance.maxSize 4000

namespace SplitLemma

open Finset HullLemma

/-! ## 1. 表で与える置換（一般の道具） -/

/-- 表 `t` で与える置換。`t` の長さ以上の点は動かさない。 -/
def tperm (t : List ℕ) : ℕ → ℕ := fun v => if v < t.length then t.getD v v else v

theorem tperm_big {t : List ℕ} {v : ℕ} (h : ¬ v < t.length) : tperm t v = v := by
  unfold tperm
  rw [if_neg h]

/-- **表のリストが `n` 未満の点の上で群をなせば `IsPermGroup`。**
仮定はすべて `∀ x < n` の有界形なので `decide` で片づく。 -/
theorem isPermGroup_of_table (tabs : List (List ℕ)) (n : ℕ)
    (hlen : ∀ t ∈ tabs, t.length = n)
    (hid : ∃ e ∈ tabs, ∀ x < n, tperm e x = x)
    (hcomp : ∀ t₁ ∈ tabs, ∀ t₂ ∈ tabs, ∃ t₃ ∈ tabs, ∀ x < n,
      tperm t₃ x = tperm t₂ (tperm t₁ x))
    (hinv : ∀ t ∈ tabs, ∃ t' ∈ tabs, ∀ x < n, tperm t' (tperm t x) = x) :
    IsPermGroup (tabs.map tperm) := by
  have hbig : ∀ t ∈ tabs, ∀ x : ℕ, ¬ x < n → tperm t x = x := by
    intro t ht x hx
    exact tperm_big (by rw [hlen t ht]; exact hx)
  constructor
  · obtain ⟨e, he, hex⟩ := hid
    refine ⟨tperm e, List.mem_map.mpr ⟨e, he, rfl⟩, ?_⟩
    intro x
    by_cases hx : x < n
    · exact hex x hx
    · exact hbig e he x hx
  · intro g hg h hh
    obtain ⟨t₁, ht₁, rfl⟩ := List.mem_map.mp hg
    obtain ⟨t₂, ht₂, rfl⟩ := List.mem_map.mp hh
    obtain ⟨t₃, ht₃, ht⟩ := hcomp t₁ ht₁ t₂ ht₂
    refine ⟨tperm t₃, List.mem_map.mpr ⟨t₃, ht₃, rfl⟩, ?_⟩
    intro x
    by_cases hx : x < n
    · exact ht x hx
    · rw [hbig t₃ ht₃ x hx, hbig t₁ ht₁ x hx, hbig t₂ ht₂ x hx]
  · intro g hg
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hg
    obtain ⟨t', ht', hti⟩ := hinv t ht
    refine ⟨tperm t', List.mem_map.mpr ⟨t', ht', rfl⟩, ?_⟩
    intro x
    by_cases hx : x < n
    · exact hti x hx
    · rw [hbig t ht x hx, hbig t' ht' x hx]

namespace T3

/-! ## 2. $T_3$（heap 番号）と Aut(T_3) の表 -/

def predT3 : ℕ → Finset ℕ := fun v => if 1 ≤ v ∧ v ≤ 7 then {2 * v, 2 * v + 1} else ∅

def FT3 : Finset ℕ := {8, 9, 10, 11, 12, 13, 14, 15}

def ST3 : Finset ℕ := {1, 2, 3, 4, 5, 6, 7}

/-- Aut(T_3) の 8 元（内部頂点 0..7 への像の表。葉は動かさない）。 -/
def tabT3 : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5, 6, 7],
   [0, 1, 2, 3, 4, 5, 7, 6],
   [0, 1, 2, 3, 5, 4, 6, 7],
   [0, 1, 2, 3, 5, 4, 7, 6],
   [0, 1, 3, 2, 6, 7, 4, 5],
   [0, 1, 3, 2, 6, 7, 5, 4],
   [0, 1, 3, 2, 7, 6, 4, 5],
   [0, 1, 3, 2, 7, 6, 5, 4]]

def GT3 : List (ℕ → ℕ) := tabT3.map tperm

/-! ## 3. 木ごとの有限検査（4 つ）。どれも `decide` -/

theorem tabT3_len : ∀ t ∈ tabT3, t.length = 8 := by decide
theorem tabT3_id : ∃ e ∈ tabT3, ∀ x < 8, tperm e x = x := by decide
theorem tabT3_comp : ∀ t₁ ∈ tabT3, ∀ t₂ ∈ tabT3, ∃ t₃ ∈ tabT3, ∀ x < 8,
    tperm t₃ x = tperm t₂ (tperm t₁ x) := by decide
theorem tabT3_inv : ∀ t ∈ tabT3, ∃ t' ∈ tabT3, ∀ x < 8, tperm t' (tperm t x) = x := by decide

theorem GT3_group : IsPermGroup GT3 :=
  isPermGroup_of_table tabT3 8 tabT3_len tabT3_id tabT3_comp tabT3_inv

theorem tabT3_S : ∀ t ∈ tabT3, ∀ m ∈ ST3, tperm t m ∈ ST3 := by decide
theorem tabT3_small_notF : ∀ t ∈ tabT3, ∀ x < 8, tperm t x ∉ FT3 := by decide
theorem tabT3_pred : ∀ t ∈ tabT3, ∀ v < 8, ∀ c ∈ predT3 (tperm t v),
    (∃ c₀ ∈ predT3 v, c = tperm t c₀) ∨ c ∈ FT3 := by decide

theorem GT3_S : ∀ g ∈ GT3, ∀ m ∈ ST3, g m ∈ ST3 := by
  intro g hg
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hg
  exact tabT3_S t ht

theorem GT3_F : ∀ g ∈ GT3, ∀ x : ℕ, g x ∈ FT3 ↔ x ∈ FT3 := by
  intro g hg x
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hg
  by_cases hx : x < 8
  · have h1 : tperm t x ∉ FT3 := tabT3_small_notF t ht x hx
    have h2 : x ∉ FT3 := by
      simp only [FT3, Finset.mem_insert, Finset.mem_singleton]
      omega
    exact ⟨fun hh => absurd hh h1, fun hh => absurd hh h2⟩
  · rw [tperm_big (by rw [tabT3_len t ht]; exact hx)]

theorem GT3_pred : ∀ g ∈ GT3, ∀ v : ℕ, ∀ c ∈ predT3 (g v),
    (∃ c₀ ∈ predT3 v, c = g c₀) ∨ c ∈ FT3 := by
  intro g hg v
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hg
  by_cases hv : v < 8
  · exact tabT3_pred t ht v hv
  · rw [tperm_big (by rw [tabT3_len t ht]; exact hv)]
    intro c hc
    exfalso
    have : predT3 v = ∅ := by
      unfold predT3
      rw [if_neg (by omega)]
    rw [this] at hc
    simp at hc

/-- ★ $T_3$ の `hstep`。**`canon` 固有の補題は 1 つも無い。** -/
theorem hstepT3 : ∀ C : Finset ℕ, ∀ m ∈ ST3, m ∉ FT3 →
    (∀ c ∈ predT3 m, c ∈ C ∨ c ∈ FT3) → (toggleAt C m).card ≤ 5 →
    ∃ m' : ℕ, m' ∈ ST3 ∧ m' ∉ FT3 ∧
      (∀ c ∈ predT3 m', c ∈ canonOf GT3 C ∨ c ∈ FT3) ∧
      (toggleAt (canonOf GT3 C) m').card ≤ 5 ∧
      canonOf GT3 (toggleAt C m) = canonOf GT3 (toggleAt (canonOf GT3 C) m') :=
  hstep_of_group GT3_group GT3_S GT3_F GT3_pred

/-! ## 4. 商 BFS のレベル集合（生成物） -/

def Lv3 : ℕ → Finset (Finset ℕ) := fun i =>
  if i = 0 then ({∅} : Finset (Finset ℕ))
  else  if i = 1 then ({{4}} : Finset (Finset ℕ))
  else  if i = 2 then ({{4, 5}, {4, 6}} : Finset (Finset ℕ))
  else  if i = 3 then ({{2, 4, 5}, {4, 5, 6}} : Finset (Finset ℕ))
  else  if i = 4 then ({{2, 4}, {2, 4, 5, 6}, {4, 5, 6, 7}} : Finset (Finset ℕ))
  else  if i = 5 then ({{2}, {2, 4, 5, 6, 7}, {2, 4, 6}} : Finset (Finset ℕ))
  else  if i = 6 then ({{3, 4}, {3, 4, 5, 6}} : Finset (Finset ℕ))
  else  if i = 7 then ({{2, 3, 4, 5, 6}, {3, 4, 5}} : Finset (Finset ℕ))
  else  if i = 8 then ({{2, 3, 4, 5}, {2, 3, 4, 6}} : Finset (Finset ℕ))
  else  if i = 9 then ({{1, 2, 3, 4, 5}, {1, 2, 3, 4, 6}, {2, 3, 4}} : Finset (Finset ℕ))
  else  if i = 10 then ({{1, 2, 3, 4}, {1, 3, 4, 5}, {2, 3}} : Finset (Finset ℕ))
  else  if i = 11 then ({{1, 2, 3}, {1, 3, 4}, {1, 3, 4, 5, 6}} : Finset (Finset ℕ))
  else  if i = 12 then ({{1, 2}, {1, 2, 4, 6}} : Finset (Finset ℕ))
  else  if i = 13 then ({{1, 2, 4}, {1, 2, 4, 5, 6}} : Finset (Finset ℕ))
  else  if i = 14 then ({{1, 2, 4, 5}, {1, 4, 5, 6}} : Finset (Finset ℕ))
  else  if i = 15 then ({{1, 4, 5}, {1, 4, 5, 6, 7}, {1, 4, 6}} : Finset (Finset ℕ))
  else  if i = 16 then ({{1, 4}} : Finset (Finset ℕ))
  else ∅

abbrev Lq3 (i : ℕ) (C : Finset ℕ) : Prop := C ∈ Lv3 i

theorem Lq3_zero : Lq3 0 (canonOf GT3 ∅) := by decide

theorem Lq3_cl_0 : ∀ s ∈ Lv3 0, ∀ m ∈ ST3, m ∉ FT3 →
    (∀ c ∈ predT3 m, c ∈ s ∨ c ∈ FT3) → (toggleAt s m).card ≤ 5 →
      canonOf GT3 (toggleAt s m) ∈ Lv3 0 ∨
      canonOf GT3 (toggleAt s m) ∈ Lv3 1 := by decide

theorem Lq3_cl_1 : ∀ s ∈ Lv3 1, ∀ m ∈ ST3, m ∉ FT3 →
    (∀ c ∈ predT3 m, c ∈ s ∨ c ∈ FT3) → (toggleAt s m).card ≤ 5 →
      canonOf GT3 (toggleAt s m) ∈ Lv3 0 ∨
      canonOf GT3 (toggleAt s m) ∈ Lv3 1 ∨
      canonOf GT3 (toggleAt s m) ∈ Lv3 2 := by decide

theorem Lq3_cl_2 : ∀ s ∈ Lv3 2, ∀ m ∈ ST3, m ∉ FT3 →
    (∀ c ∈ predT3 m, c ∈ s ∨ c ∈ FT3) → (toggleAt s m).card ≤ 5 →
      canonOf GT3 (toggleAt s m) ∈ Lv3 1 ∨
      canonOf GT3 (toggleAt s m) ∈ Lv3 2 ∨
      canonOf GT3 (toggleAt s m) ∈ Lv3 3 := by decide

theorem Lq3_cl_3 : ∀ s ∈ Lv3 3, ∀ m ∈ ST3, m ∉ FT3 →
    (∀ c ∈ predT3 m, c ∈ s ∨ c ∈ FT3) → (toggleAt s m).card ≤ 5 →
      canonOf GT3 (toggleAt s m) ∈ Lv3 2 ∨
      canonOf GT3 (toggleAt s m) ∈ Lv3 3 ∨
      canonOf GT3 (toggleAt s m) ∈ Lv3 4 := by decide

theorem Lq3_cl_4 : ∀ s ∈ Lv3 4, ∀ m ∈ ST3, m ∉ FT3 →
    (∀ c ∈ predT3 m, c ∈ s ∨ c ∈ FT3) → (toggleAt s m).card ≤ 5 →
      canonOf GT3 (toggleAt s m) ∈ Lv3 3 ∨
      canonOf GT3 (toggleAt s m) ∈ Lv3 4 ∨
      canonOf GT3 (toggleAt s m) ∈ Lv3 5 := by decide

theorem Lq3_cl_5 : ∀ s ∈ Lv3 5, ∀ m ∈ ST3, m ∉ FT3 →
    (∀ c ∈ predT3 m, c ∈ s ∨ c ∈ FT3) → (toggleAt s m).card ≤ 5 →
      canonOf GT3 (toggleAt s m) ∈ Lv3 4 ∨
      canonOf GT3 (toggleAt s m) ∈ Lv3 5 ∨
      canonOf GT3 (toggleAt s m) ∈ Lv3 6 := by decide

theorem Lq3_cl_6 : ∀ s ∈ Lv3 6, ∀ m ∈ ST3, m ∉ FT3 →
    (∀ c ∈ predT3 m, c ∈ s ∨ c ∈ FT3) → (toggleAt s m).card ≤ 5 →
      canonOf GT3 (toggleAt s m) ∈ Lv3 5 ∨
      canonOf GT3 (toggleAt s m) ∈ Lv3 6 ∨
      canonOf GT3 (toggleAt s m) ∈ Lv3 7 := by decide

theorem Lq3_cl_7 : ∀ s ∈ Lv3 7, ∀ m ∈ ST3, m ∉ FT3 →
    (∀ c ∈ predT3 m, c ∈ s ∨ c ∈ FT3) → (toggleAt s m).card ≤ 5 →
      canonOf GT3 (toggleAt s m) ∈ Lv3 6 ∨
      canonOf GT3 (toggleAt s m) ∈ Lv3 7 ∨
      canonOf GT3 (toggleAt s m) ∈ Lv3 8 := by decide

theorem Lq3_cl_8 : ∀ s ∈ Lv3 8, ∀ m ∈ ST3, m ∉ FT3 →
    (∀ c ∈ predT3 m, c ∈ s ∨ c ∈ FT3) → (toggleAt s m).card ≤ 5 →
      canonOf GT3 (toggleAt s m) ∈ Lv3 7 ∨
      canonOf GT3 (toggleAt s m) ∈ Lv3 8 ∨
      canonOf GT3 (toggleAt s m) ∈ Lv3 9 := by decide

theorem Lq3_cl_9 : ∀ s ∈ Lv3 9, ∀ m ∈ ST3, m ∉ FT3 →
    (∀ c ∈ predT3 m, c ∈ s ∨ c ∈ FT3) → (toggleAt s m).card ≤ 5 →
      canonOf GT3 (toggleAt s m) ∈ Lv3 8 ∨
      canonOf GT3 (toggleAt s m) ∈ Lv3 9 ∨
      canonOf GT3 (toggleAt s m) ∈ Lv3 10 := by decide

theorem Lq3_cl_10 : ∀ s ∈ Lv3 10, ∀ m ∈ ST3, m ∉ FT3 →
    (∀ c ∈ predT3 m, c ∈ s ∨ c ∈ FT3) → (toggleAt s m).card ≤ 5 →
      canonOf GT3 (toggleAt s m) ∈ Lv3 9 ∨
      canonOf GT3 (toggleAt s m) ∈ Lv3 10 ∨
      canonOf GT3 (toggleAt s m) ∈ Lv3 11 := by decide

theorem Lq3_cl_11 : ∀ s ∈ Lv3 11, ∀ m ∈ ST3, m ∉ FT3 →
    (∀ c ∈ predT3 m, c ∈ s ∨ c ∈ FT3) → (toggleAt s m).card ≤ 5 →
      canonOf GT3 (toggleAt s m) ∈ Lv3 10 ∨
      canonOf GT3 (toggleAt s m) ∈ Lv3 11 ∨
      canonOf GT3 (toggleAt s m) ∈ Lv3 12 := by decide

theorem Lq3_cl_12 : ∀ s ∈ Lv3 12, ∀ m ∈ ST3, m ∉ FT3 →
    (∀ c ∈ predT3 m, c ∈ s ∨ c ∈ FT3) → (toggleAt s m).card ≤ 5 →
      canonOf GT3 (toggleAt s m) ∈ Lv3 11 ∨
      canonOf GT3 (toggleAt s m) ∈ Lv3 12 ∨
      canonOf GT3 (toggleAt s m) ∈ Lv3 13 := by decide

theorem Lq3_cl_13 : ∀ s ∈ Lv3 13, ∀ m ∈ ST3, m ∉ FT3 →
    (∀ c ∈ predT3 m, c ∈ s ∨ c ∈ FT3) → (toggleAt s m).card ≤ 5 →
      canonOf GT3 (toggleAt s m) ∈ Lv3 12 ∨
      canonOf GT3 (toggleAt s m) ∈ Lv3 13 ∨
      canonOf GT3 (toggleAt s m) ∈ Lv3 14 := by decide

theorem Lq3_cl_14 : ∀ s ∈ Lv3 14, ∀ m ∈ ST3, m ∉ FT3 →
    (∀ c ∈ predT3 m, c ∈ s ∨ c ∈ FT3) → (toggleAt s m).card ≤ 5 →
      canonOf GT3 (toggleAt s m) ∈ Lv3 13 ∨
      canonOf GT3 (toggleAt s m) ∈ Lv3 14 ∨
      canonOf GT3 (toggleAt s m) ∈ Lv3 15 := by decide

theorem Lq3_cl_15 : ∀ s ∈ Lv3 15, ∀ m ∈ ST3, m ∉ FT3 →
    (∀ c ∈ predT3 m, c ∈ s ∨ c ∈ FT3) → (toggleAt s m).card ≤ 5 →
      canonOf GT3 (toggleAt s m) ∈ Lv3 14 ∨
      canonOf GT3 (toggleAt s m) ∈ Lv3 15 ∨
      canonOf GT3 (toggleAt s m) ∈ Lv3 16 := by decide

theorem Lq3_closed : ∀ i, i < 16 → ∀ s : Finset ℕ, Lq3 i s → ∀ m ∈ ST3, m ∉ FT3 →
    (∀ c ∈ predT3 m, c ∈ s ∨ c ∈ FT3) → (toggleAt s m).card ≤ 5 →
    ∃ j, j ≤ i + 1 ∧ Lq3 j (canonOf GT3 (toggleAt s m)) := by
  intro i hi s hs m hm hmF hpred hcard
  interval_cases i
  · rcases Lq3_cl_0 s hs m hm hmF hpred hcard with h0 | h1
    · exact ⟨0, by omega, h0⟩
    · exact ⟨1, by omega, h1⟩
  · rcases Lq3_cl_1 s hs m hm hmF hpred hcard with h0 | h1 | h2
    · exact ⟨0, by omega, h0⟩
    · exact ⟨1, by omega, h1⟩
    · exact ⟨2, by omega, h2⟩
  · rcases Lq3_cl_2 s hs m hm hmF hpred hcard with h0 | h1 | h2
    · exact ⟨1, by omega, h0⟩
    · exact ⟨2, by omega, h1⟩
    · exact ⟨3, by omega, h2⟩
  · rcases Lq3_cl_3 s hs m hm hmF hpred hcard with h0 | h1 | h2
    · exact ⟨2, by omega, h0⟩
    · exact ⟨3, by omega, h1⟩
    · exact ⟨4, by omega, h2⟩
  · rcases Lq3_cl_4 s hs m hm hmF hpred hcard with h0 | h1 | h2
    · exact ⟨3, by omega, h0⟩
    · exact ⟨4, by omega, h1⟩
    · exact ⟨5, by omega, h2⟩
  · rcases Lq3_cl_5 s hs m hm hmF hpred hcard with h0 | h1 | h2
    · exact ⟨4, by omega, h0⟩
    · exact ⟨5, by omega, h1⟩
    · exact ⟨6, by omega, h2⟩
  · rcases Lq3_cl_6 s hs m hm hmF hpred hcard with h0 | h1 | h2
    · exact ⟨5, by omega, h0⟩
    · exact ⟨6, by omega, h1⟩
    · exact ⟨7, by omega, h2⟩
  · rcases Lq3_cl_7 s hs m hm hmF hpred hcard with h0 | h1 | h2
    · exact ⟨6, by omega, h0⟩
    · exact ⟨7, by omega, h1⟩
    · exact ⟨8, by omega, h2⟩
  · rcases Lq3_cl_8 s hs m hm hmF hpred hcard with h0 | h1 | h2
    · exact ⟨7, by omega, h0⟩
    · exact ⟨8, by omega, h1⟩
    · exact ⟨9, by omega, h2⟩
  · rcases Lq3_cl_9 s hs m hm hmF hpred hcard with h0 | h1 | h2
    · exact ⟨8, by omega, h0⟩
    · exact ⟨9, by omega, h1⟩
    · exact ⟨10, by omega, h2⟩
  · rcases Lq3_cl_10 s hs m hm hmF hpred hcard with h0 | h1 | h2
    · exact ⟨9, by omega, h0⟩
    · exact ⟨10, by omega, h1⟩
    · exact ⟨11, by omega, h2⟩
  · rcases Lq3_cl_11 s hs m hm hmF hpred hcard with h0 | h1 | h2
    · exact ⟨10, by omega, h0⟩
    · exact ⟨11, by omega, h1⟩
    · exact ⟨12, by omega, h2⟩
  · rcases Lq3_cl_12 s hs m hm hmF hpred hcard with h0 | h1 | h2
    · exact ⟨11, by omega, h0⟩
    · exact ⟨12, by omega, h1⟩
    · exact ⟨13, by omega, h2⟩
  · rcases Lq3_cl_13 s hs m hm hmF hpred hcard with h0 | h1 | h2
    · exact ⟨12, by omega, h0⟩
    · exact ⟨13, by omega, h1⟩
    · exact ⟨14, by omega, h2⟩
  · rcases Lq3_cl_14 s hs m hm hmF hpred hcard with h0 | h1 | h2
    · exact ⟨13, by omega, h0⟩
    · exact ⟨14, by omega, h1⟩
    · exact ⟨15, by omega, h2⟩
  · rcases Lq3_cl_15 s hs m hm hmF hpred hcard with h0 | h1 | h2
    · exact ⟨14, by omega, h0⟩
    · exact ⟨15, by omega, h1⟩
    · exact ⟨16, by omega, h2⟩

theorem Lq3_no_root : ∀ j, j ≤ 16 → ¬ Lq3 j (canonOf GT3 ({1} : Finset ℕ)) := by
  intro j hj
  interval_cases j <;> decide

/-- ★ **一般機構だけで $M^*(T_3,5)\ge 17$。** -/
theorem quot_h3_bound (l : List ℕ) (hS : ∀ m ∈ l, m ∈ ST3)
    (hL : Legal predT3 FT3 l ∅) (hP : Peak 5 l ∅) (hrun : run l ∅ = ({1} : Finset ℕ)) :
    17 ≤ l.length :=
  length_ge_of_quot_levels (pred := predT3) (F := FT3) (S := ST3)
    (q := 5) (T := 17) (canon := canonOf GT3) (Lq := Lq3) (Y := ({1} : Finset ℕ))
    Lq3_zero
    (fun _ _ C _ m hmS hmF hpred hcard => hstepT3 C m hmS hmF hpred hcard)
    Lq3_closed Lq3_no_root l hS hL hP hrun


/-! ## 5. 空虚でないことの確認（BFS が出した 17 手。既知値 $M^*(T_3)=17$ と一致） -/

def schedT3 : List ℕ := [4, 5, 2, 4, 5, 6, 7, 3, 1, 3, 4, 6, 5, 2, 4, 5, 7]

theorem schedT3_legal : Legal predT3 FT3 schedT3 ∅ := by
  simp only [schedT3, Legal, predT3, FT3, toggleAt]
  decide

theorem schedT3_peak : Peak 5 schedT3 ∅ := by
  simp only [schedT3, Peak, toggleAt]
  decide

theorem schedT3_clean : run schedT3 ∅ = ({1} : Finset ℕ) := by
  simp only [schedT3, run, toggleAt]
  decide

/-- 仮定は矛盾していない。得られるのは `17 ≤ 17`（証書は下界を 1 も捨てていない）。 -/
theorem quot_h3_witness : 17 ≤ schedT3.length :=
  quot_h3_bound schedT3 (fun m hm => by fin_cases hm <;> decide)
    schedT3_legal schedT3_peak schedT3_clean

#print axioms GT3_group
#print axioms hstepT3
#print axioms Lq3_closed
#print axioms quot_h3_bound
#print axioms quot_h3_witness

end T3

end SplitLemma
