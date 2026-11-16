/-
# 定理 U: 前進と片づけの組み立て（紙の補題 2〜4 と 4 節の系）

紙 `UNIVERSAL_UB_2026-11.md` の 3〜5 節。区域 `Z`（頂 `z`）について 2 種の手順の仕様を置く。

* `FFok t b Z z`（**全前進**）: `Z` の頂点がどれもペブルでなく、`Z` が閉じている（穴はペブル）なら、
  `Z` の各頂点を高々 1 回置き、`Z` の中のペブルを常に `b` 以下に保ち、頂 `z` だけペブル・ほかの
  `Z` の頂点はペブルでない状態で終える手順がある。
* `CLok t b j Z z`（**片づけ**、紙の `CL_j`）: `Z` が片づけ待ち（`z` はペブル、ほかはペブルでない、
  穴はペブル）なら、置く手 `≤ j(|Z|−1)`、`Z` の中のペブルを常に `b` 以下に保ち、`Z` を全部空にする
  手順がある。

**紙との違い（構成）.** 紙の前進 `FWD(Q,S)` は `Q∖{r}` 全体を「大きい子から回る後行順」で 1 頂点ずつ
置き、前線を `L = (d−1)⌊log₂n⌋ + d + 1` で抑える（補題 2）。ここでは前進も群ごとに再帰させる:
`FWD(Q,S)` = 群の頂 `a` を深い順（`rk` の小さい順）に、群 `g a` を一段下の `FFok` で前進する。
各頂点を置く回数は紙と同じく前進で 1 回。ペブルの上限は段ごとに
`B_1 = 1 + d(S_1 − 1)`、`B_{j+1} = ⌊d(S_{j+1} − 1)/S_j⌋ + d + B_j`（`Bd`）で、紙の
`𝒫_j ≤ a_j + d + max(L, 𝒫_{j−1})` から `max(L, ·)` の `L` を除いた形になる（`L` の項が要らない）。
したがって全体の上限は紙の `P*` 以下（`RootedUniversalUpper.lean` の `PU_le_Pstar`）。

* `fwd_loop`・`cl_loop`: 群を `rk` の小さい順／大きい順に処理する帰納法（紙の「dep の大きい順」
  「dep の小さい順」に当たる。穴になる頂は群の頂より真に下にあることだけを使う）。
* `FF_step`・`CL_step`: 一段上げる。`FF_base`・`CL_base`: 段 1。
* `lev_all`: 段 `j` の仕様（大きさ `≤ 1 + d(S_j − 1)` の区域で、ペブル `Bd d S j`、置く手 `≤ j(|Z|−1)`）。
* `global_run`: 全体 `C_K`（全部空 → 根だけペブル）。手数は `2Π − 1 ≤ 2Kn − 1`。
-/
import SpookyPebblingExtra.RootedUniversalUpperGroup

namespace Spooky
namespace RootedTree
namespace UUB

open Finset Classical

variable {t : RootedTree}

theorem exec_app (l₁ l₂ : List Move) (c : Config) :
    exec c (l₁ ++ l₂) = exec (exec c l₁) l₂ := by
  induction l₁ generalizing c with
  | nil => rfl
  | cons a as ih => simpa [exec] using ih (step c a)

/-- 全前進の仕様。 -/
def FFok (t : RootedTree) (b : ℕ) (Z : Finset ℕ) (z : ℕ) : Prop :=
  ∀ c : Config, (∀ v ∈ Z, c v ≠ Cell.pebble) → Closed t c Z →
    ∃ ms, LOk t Z b c ms ∧ np ms ≤ Z.card ∧ exec c ms z = Cell.pebble ∧
      (∀ v ∈ Z, v ≠ z → exec c ms v ≠ Cell.pebble)

/-- 片づけの仕様（紙の `CL_j`）。 -/
def CLok (t : RootedTree) (b j : ℕ) (Z : Finset ℕ) (z : ℕ) : Prop :=
  ∀ c : Config, c z = Cell.pebble → (∀ v ∈ Z, v ≠ z → c v ≠ Cell.pebble) → Closed t c Z →
    ∃ ms, LOk t Z b c ms ∧ np ms ≤ j * (Z.card - 1) ∧ (∀ v ∈ Z, exec c ms v = Cell.empty)

theorem FFok.mono {b b' : ℕ} {Z : Finset ℕ} {z : ℕ} (h : FFok t b Z z) (hb : b ≤ b') :
    FFok t b' Z z := by
  intro c h1 h2
  obtain ⟨ms, a1, a2, a3, a4⟩ := h c h1 h2
  exact ⟨ms, LOk_mono hb a1, a2, a3, a4⟩

theorem CLok.mono {b b' j : ℕ} {Z : Finset ℕ} {z : ℕ} (h : CLok t b j Z z) (hb : b ≤ b') :
    CLok t b' j Z z := by
  intro c h0 h1 h2
  obtain ⟨ms, a1, a2, a3⟩ := h c h0 h1 h2
  exact ⟨ms, LOk_mono hb a1, a2, a3⟩

/-- 1 手の局所の手順。 -/
theorem LOk_single {Q : Finset ℕ} {k : ℕ} {c : Config} {m : Move} (h0 : pc Q c ≤ k) (hm : m.v ∈ Q)
    (hl : t.legal c m = true) (h1 : pc Q (step c m) ≤ k) : LOk t Q k c [m] :=
  ⟨h0, hm, hl, h1⟩

/-! ## 段 1 -/

theorem FF_base (ht : t.isTree = true) {Z : Finset ℕ} {z : ℕ} (hZ : Zone t Z z) : FFok t Z.card Z z := by
  intro c hnp hcl
  obtain ⟨ms1, h1, h2, h3⟩ := placeAll ht Z c hZ.lt hnp hcl
  obtain ⟨ms2, g1, g2, g3⟩ := ghostAll (t := t) (Z.erase z) (exec c ms1)
    (fun v hv => hZ.lt v (mem_of_mem_erase hv)) (fun v hv => h3 v (mem_of_mem_erase hv))
  refine ⟨ms1 ++ ms2, (LOk_append ms1).mpr ⟨h1, LOk_widen (erase_subset _ _) g1⟩, ?_, ?_, ?_⟩
  · rw [np_append, h2, g2]; exact le_of_eq (Nat.add_zero _)
  · rw [exec_app, LOk_out g1 z (by simp)]; exact h3 z hZ.mem
  · intro v hv hvz
    rw [exec_app, g3 v (mem_erase.mpr ⟨hvz, hv⟩)]
    decide

theorem CL_base (ht : t.isTree = true) {Z : Finset ℕ} {z : ℕ} (hZ : Zone t Z z) :
    CLok t Z.card 1 Z z := by
  intro c hz hnp hcl
  have hzn := hZ.lt z hZ.mem
  obtain ⟨ms1, h1, h2, h3⟩ := placeAll ht (Z.erase z) c (fun v hv => hZ.lt v (mem_of_mem_erase hv))
    (fun v hv => hnp v (mem_of_mem_erase hv) (ne_of_mem_erase hv))
    (by
      intro v hv u hu hp
      rcases hcl v (mem_of_mem_erase hv) u hu hp with h | h
      · by_cases huz : u = z
        · right; rw [huz]; exact hz
        · left; exact mem_erase.mpr ⟨huz, h⟩
      · right; exact h)
  set c1 := exec c ms1 with hc1
  have hout1 : ∀ v, v ∉ Z.erase z → c1 v = c v := LOk_out h1
  set m : Move := ⟨Op.unpebble, z⟩ with hm
  have hready : t.ready c1 z = true := by
    apply ready_of_children
    intro u hu hp
    by_cases huZ : u ∈ Z
    · exact h3 u (mem_erase.mpr ⟨par_ne ht hu hp, huZ⟩)
    · rcases hcl z hZ.mem u hu hp with h | h
      · exact absurd h huZ
      · rw [hout1 u (fun h' => huZ (mem_of_mem_erase h'))]; exact h
  have hc1z : c1 z = Cell.pebble := by rw [hout1 z (by simp)]; exact hz
  have hleg : t.legal c1 m = true := by
    simp [RootedTree.legal, hm, hzn, hc1z, hready]
  set c2 := step c1 m with hc2
  have hc2e : c2 = Function.update c1 z Cell.empty := rfl
  obtain ⟨ms3, k1, k2, k3⟩ := unpebbleAll ht (Z.erase z) c2
    (fun v hv => hZ.lt v (mem_of_mem_erase hv))
    (by
      intro v hv
      rw [hc2e, Function.update_of_ne (ne_of_mem_erase hv)]; exact h3 v hv)
    (by
      intro v hv u hu hp
      by_cases huZ : u ∈ Z
      · left
        refine mem_erase.mpr ⟨?_, huZ⟩
        rintro rfl
        exact hZ.top_not_child ht (mem_of_mem_erase hv) hp
      · rcases hcl v (mem_of_mem_erase hv) u hu hp with h | h
        · exact absurd h huZ
        · right
          have huz : u ≠ z := fun e => huZ (e ▸ hZ.mem)
          rw [hc2e, Function.update_of_ne huz, hout1 u (fun h' => huZ (mem_of_mem_erase h'))]
          exact h)
  refine ⟨ms1 ++ (m :: ms3), (LOk_append ms1).mpr ⟨LOk_widen (erase_subset _ _) h1,
    ⟨pc_le_card _ _, hZ.mem, hleg, LOk_widen (erase_subset _ _) k1⟩⟩, ?_, ?_⟩
  · rw [np_append, np_cons_nonplace (by simp [IsPlace, hm]), h2, k2, card_erase_of_mem hZ.mem]
    omega
  · intro v hv
    rw [exec_app]
    show exec c2 ms3 v = _
    by_cases hvz : v = z
    · rw [hvz, LOk_out k1 z (by simp), hc2e, Function.update_self]
    · exact k3 v (mem_erase.mpr ⟨hvz, hv⟩)

/-! ## 群ごとの処理 -/

section Loops

variable {d S b j : ℕ} {Z : Finset ℕ} {z : ℕ} {T : Finset ℕ} {g : ℕ → Finset ℕ}

theorem grp_mem_self (hG : Grp t d S Z z T g) {a : ℕ} (ha : a ∈ T) : a ∈ g a := (hG.zone a ha).mem

theorem grp_sub_Z (hG : Grp t d S Z z T g) {a v : ℕ} (ha : a ∈ T) (hv : v ∈ g a) : v ∈ Z :=
  mem_of_mem_erase (hG.gsub a ha hv)

/-- 群の穴になる頂は群の頂より真に下（`rk` が小さい）。 -/
theorem grp_hole_rk (ht : t.isTree = true) (hG : Grp t d S Z z T g) {a v u : ℕ} (ha : a ∈ T)
    (hv : v ∈ g a) (hun : u < t.n) (hpu : t.par u = some v) (hua : u ∉ g a) : rk t u < rk t a := by
  have hau : t.Anc a u := Anc.trans ((hG.zone a ha).anc v hv) (anc_of_par hpu)
  have hne : a ≠ u := fun e => hua (e ▸ grp_mem_self hG ha)
  exact rk_lt ht hun hau hne

/-- 群の外では変わらない。 -/
theorem grp_out_eq {c c' : Config} {a : ℕ} (hout : ∀ v, v ∉ g a → c' v = c v)
    (hG : Grp t d S Z z T g) (ha : a ∈ T) {a' : ℕ} (ha' : a' ∈ T) (hne : a' ≠ a) {v : ℕ}
    (hv : v ∈ g a') : c' v = c v :=
  hout v (Finset.disjoint_left.mp (hG.disj a' ha' a ha hne) hv)

/-- **前進の繰り返し**: 残りの頂 `U` の群を `rk` の小さい順に全前進する。 -/
theorem fwd_loop (ht : t.isTree = true) (hZ : Zone t Z z) (hG : Grp t d S Z z T g) (hb : 1 ≤ b)
    (hFF : ∀ a ∈ T, FFok t b (g a) a) (U : Finset ℕ) : U ⊆ T → ∀ c : Config,
      (∀ a ∈ T, a ∉ U → c a = Cell.pebble ∧ ∀ v ∈ g a, v ≠ a → c v ≠ Cell.pebble) →
      (∀ a ∈ U, ∀ v ∈ g a, c v ≠ Cell.pebble) → Closed t c Z →
      ∃ ms, LOk t (Z.erase z) (T.card + b - 1) c ms ∧ np ms ≤ ∑ a ∈ U, (g a).card ∧
        (∀ a ∈ T, exec c ms a = Cell.pebble ∧ ∀ v ∈ g a, v ≠ a → exec c ms v ≠ Cell.pebble) := by
  induction U using Finset.strongInduction with
  | H U ih =>
  intro hUT c hI1 hI2 hcl
  -- ペブルは処理済みの頂だけ
  have htops : ∀ v ∈ Z.erase z, c v = Cell.pebble → v ∈ T ∧ v ∉ U := by
    intro v hv hp
    obtain ⟨a', ha', hva'⟩ := hG.cover v hv
    by_cases haU : a' ∈ U
    · exact absurd hp (hI2 a' haU v hva')
    · by_cases hva : v = a'
      · subst hva; exact ⟨ha', haU⟩
      · exact absurd hp ((hI1 a' ha' haU).2 v hva' hva)
  rcases U.eq_empty_or_nonempty with hU | hne
  · subst hU
    refine ⟨[], ?_, by simp, fun a ha => hI1 a ha (Finset.notMem_empty a)⟩
    show pc (Z.erase z) c ≤ T.card + b - 1
    have := pc_le_of (B := T) (fun v hv hp => (htops v hv hp).1)
    omega
  obtain ⟨a, haU, hmin⟩ := U.exists_min_image (rk t) hne
  have haT := hUT haU
  -- 群 `g a` は閉じている
  have hclA : Closed t c (g a) := by
    intro v hv u hu hp
    rcases hG.hole a haT v hv u hu hp with h | h | h
    · exact Or.inl h
    · by_cases hua : u ∈ g a
      · exact Or.inl hua
      · right
        have hlt := grp_hole_rk ht hG haT hv hu hp hua
        have huU : u ∉ U := fun huU => absurd (hmin u huU) (not_le.mpr hlt)
        exact (hI1 u h huU).1
    · rcases hcl v (grp_sub_Z hG haT hv) u hu hp with h' | h'
      · exact absurd h' h
      · exact Or.inr h'
  obtain ⟨ms1, f1, f2, f3, f4⟩ := hFF a haT c (hI2 a haU) hclA
  set c1 := exec c ms1 with hc1
  have hout1 : ∀ v, v ∉ g a → c1 v = c v := LOk_out f1
  have hgsub : g a ⊆ Z.erase z := hG.gsub a haT
  -- 持ち上げ
  have hlift : LOk t (Z.erase z) (T.card + b - 1) c ms1 := by
    have hrest : pc (Z.erase z \ g a) c ≤ T.card - 1 := by
      have := pc_le_of (Q := Z.erase z \ g a) (B := T.erase a) (c := c) (by
        intro v hv hp
        obtain ⟨hv1, hv2⟩ := mem_sdiff.mp hv
        refine mem_erase.mpr ⟨fun e => hv2 (by rw [e]; exact grp_mem_self hG haT), (htops v hv1 hp).1⟩)
      rw [card_erase_of_mem haT] at this; exact this
    have := LOk_lift hgsub f1 hrest
    have hT1 : 1 ≤ T.card := card_pos.mpr ⟨a, haT⟩
    exact LOk_mono (by omega) this
  obtain ⟨ms2, e1, e2, e3⟩ := ih (U.erase a) (erase_ssubset haU) ((erase_subset _ _).trans hUT) c1
    (by
      intro a' ha' haU'
      by_cases haa : a' = a
      · subst haa
        exact ⟨f3, fun v hv hva => f4 v hv hva⟩
      · have haU2 : a' ∉ U := fun h => haU' (mem_erase.mpr ⟨haa, h⟩)
        obtain ⟨p1, p2⟩ := hI1 a' ha' haU2
        refine ⟨?_, fun v hv hva => ?_⟩
        · rw [grp_out_eq hout1 hG haT ha' haa (grp_mem_self hG ha')]; exact p1
        · rw [grp_out_eq hout1 hG haT ha' haa hv]; exact p2 v hv hva)
    (by
      intro a' ha' v hv
      obtain ⟨haa, haU2⟩ := mem_erase.mp ha'
      rw [grp_out_eq hout1 hG haT (hUT haU2) haa hv]
      exact hI2 a' haU2 v hv)
    (hcl.of_out (fun v hv => hout1 v (fun h => hv (grp_sub_Z hG haT h))))
  refine ⟨ms1 ++ ms2, (LOk_append ms1).mpr ⟨hlift, e1⟩, ?_, ?_⟩
  · rw [np_append, ← Finset.add_sum_erase U _ haU]
    exact Nat.add_le_add f2 e2
  · intro a' ha'
    rw [exec_app]
    exact e3 a' ha'

/-- **片づけの繰り返し**: 残りの頂 `U` の群を `rk` の大きい順に片づける。 -/
theorem cl_loop (ht : t.isTree = true) (hZ : Zone t Z z) (hG : Grp t d S Z z T g) (hb : 1 ≤ b)
    (hCL : ∀ a ∈ T, CLok t b j (g a) a) (U : Finset ℕ) : U ⊆ T →
      (∀ a ∈ U, ∀ a' ∈ T, rk t a' < rk t a → a' ∈ U) → ∀ c : Config,
      (∀ a ∈ T, a ∉ U → ∀ v ∈ g a, c v = Cell.empty) →
      (∀ a ∈ U, c a = Cell.pebble ∧ ∀ v ∈ g a, v ≠ a → c v ≠ Cell.pebble) → Closed t c Z →
      ∃ ms, LOk t (Z.erase z) (T.card + b - 1) c ms ∧ np ms ≤ j * ∑ a ∈ U, (g a).card ∧
        (∀ v ∈ Z.erase z, exec c ms v = Cell.empty) := by
  induction U using Finset.strongInduction with
  | H U ih =>
  intro hUT hdown c hI1 hI2 hcl
  have htops : ∀ v ∈ Z.erase z, c v = Cell.pebble → v ∈ U := by
    intro v hv hp
    obtain ⟨a', ha', hva'⟩ := hG.cover v hv
    by_cases haU : a' ∈ U
    · by_cases hva : v = a'
      · subst hva; exact haU
      · exact absurd hp ((hI2 a' haU).2 v hva' hva)
    · rw [hI1 a' ha' haU v hva'] at hp; exact absurd hp (by decide)
  rcases U.eq_empty_or_nonempty with hU | hne
  · subst hU
    refine ⟨[], ?_, by simp, ?_⟩
    · show pc (Z.erase z) c ≤ T.card + b - 1
      have := pc_le_of (B := ∅) (fun v hv hp => htops v hv hp)
      simp at this; omega
    · intro v hv
      obtain ⟨a', ha', hva'⟩ := hG.cover v hv
      exact hI1 a' ha' (Finset.notMem_empty a') v hva'
  obtain ⟨a, haU, hmax⟩ := U.exists_max_image (rk t) hne
  have haT := hUT haU
  have hclA : Closed t c (g a) := by
    intro v hv u hu hp
    rcases hG.hole a haT v hv u hu hp with h | h | h
    · exact Or.inl h
    · by_cases hua : u ∈ g a
      · exact Or.inl hua
      · right
        have hlt := grp_hole_rk ht hG haT hv hu hp hua
        exact (hI2 u (hdown a haU u h hlt)).1
    · rcases hcl v (grp_sub_Z hG haT hv) u hu hp with h' | h'
      · exact absurd h' h
      · exact Or.inr h'
  obtain ⟨ms1, f1, f2, f3⟩ := hCL a haT c (hI2 a haU).1 (hI2 a haU).2 hclA
  set c1 := exec c ms1 with hc1
  have hout1 : ∀ v, v ∉ g a → c1 v = c v := LOk_out f1
  have hgsub : g a ⊆ Z.erase z := hG.gsub a haT
  have hlift : LOk t (Z.erase z) (T.card + b - 1) c ms1 := by
    have hrest : pc (Z.erase z \ g a) c ≤ T.card - 1 := by
      have := pc_le_of (Q := Z.erase z \ g a) (B := T.erase a) (c := c) (by
        intro v hv hp
        obtain ⟨hv1, hv2⟩ := mem_sdiff.mp hv
        exact mem_erase.mpr ⟨fun e => hv2 (by rw [e]; exact grp_mem_self hG haT), hUT (htops v hv1 hp)⟩)
      rw [card_erase_of_mem haT] at this; exact this
    have := LOk_lift hgsub f1 hrest
    have hT1 : 1 ≤ T.card := card_pos.mpr ⟨a, haT⟩
    exact LOk_mono (by omega) this
  obtain ⟨ms2, e1, e2, e3⟩ := ih (U.erase a) (erase_ssubset haU) ((erase_subset _ _).trans hUT)
    (by
      intro a1 ha1 a' ha' hlt
      obtain ⟨ha1a, ha1U⟩ := mem_erase.mp ha1
      refine mem_erase.mpr ⟨?_, hdown a1 ha1U a' ha' hlt⟩
      rintro rfl
      exact absurd (hmax a1 ha1U) (not_le.mpr hlt))
    c1
    (by
      intro a' ha' haU' v hv
      by_cases haa : a' = a
      · subst haa; exact f3 v hv
      · have haU2 : a' ∉ U := fun h => haU' (mem_erase.mpr ⟨haa, h⟩)
        rw [grp_out_eq hout1 hG haT ha' haa hv]
        exact hI1 a' ha' haU2 v hv)
    (by
      intro a' ha'
      obtain ⟨haa, haU2⟩ := mem_erase.mp ha'
      obtain ⟨p1, p2⟩ := hI2 a' haU2
      refine ⟨?_, fun v hv hva => ?_⟩
      · rw [grp_out_eq hout1 hG haT (hUT haU2) haa (grp_mem_self hG (hUT haU2))]; exact p1
      · rw [grp_out_eq hout1 hG haT (hUT haU2) haa hv]; exact p2 v hv hva)
    (hcl.of_out (fun v hv => hout1 v (fun h => hv (grp_sub_Z hG haT h))))
  refine ⟨ms1 ++ ms2, (LOk_append ms1).mpr ⟨hlift, e1⟩, ?_, ?_⟩
  · rw [np_append, ← Finset.add_sum_erase U _ haU, Nat.mul_add]
    have : j * ((g a).card - 1) ≤ j * (g a).card := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    omega
  · intro v hv
    rw [exec_app]
    exact e3 v hv

end Loops

/-! ## 一段上げる -/

section Step

variable {d S b j : ℕ} {Z : Finset ℕ} {z : ℕ} {T : Finset ℕ} {g : ℕ → Finset ℕ}

/-- 群分けした後の盤面で、`Z` の中のペブルは頂と（ペブルなら）`z` だけ。 -/
theorem pc_after_fwd (hG : Grp t d S Z z T g) {c : Config}
    (hc : ∀ a ∈ T, ∀ v ∈ g a, v ≠ a → c v ≠ Cell.pebble) : pc Z c ≤ T.card + 1 := by
  have := pc_le_of (Q := Z) (B := insert z T) (c := c) (by
    intro v hv hp
    by_cases hvz : v = z
    · rw [hvz]; exact mem_insert_self _ _
    · obtain ⟨a', ha', hva'⟩ := hG.cover v (mem_erase.mpr ⟨hvz, hv⟩)
      by_cases hva : v = a'
      · rw [hva]; exact mem_insert_of_mem ha'
      · exact absurd hp (hc a' ha' v hva' hva))
  exact le_trans this (card_insert_le _ _)

theorem FF_step (ht : t.isTree = true) (hZ : Zone t Z z) (hG : Grp t d S Z z T g) (hb : 1 ≤ b)
    (hFF : ∀ a ∈ T, FFok t b (g a) a) : FFok t (T.card + b) Z z := by
  intro c hnp hcl
  have hzn := hZ.lt z hZ.mem
  obtain ⟨ms1, h1, h2, h3⟩ := fwd_loop ht hZ hG hb hFF T subset_rfl c
    (fun a _ haT => absurd ‹a ∈ T› haT)
    (fun a ha v hv => hnp v (grp_sub_Z hG ha hv)) hcl
  set c1 := exec c ms1 with hc1
  have hout1 : ∀ v, v ∉ Z.erase z → c1 v = c v := LOk_out h1
  have hc1z : c1 z ≠ Cell.pebble := by rw [hout1 z (by simp)]; exact hnp z hZ.mem
  -- 前進を Z へ持ち上げる（z はペブルでない）
  have hL1 : LOk t Z (T.card + b) c ms1 := by
    have := LOk_lift (erase_subset z Z) h1 (m := 0) (by
      have := pc_le_of (Q := Z \ Z.erase z) (B := ∅) (c := c) (by
        intro v hv hp
        have : v = z := by
          by_contra hvz
          exact (mem_sdiff.mp hv).2 (mem_erase.mpr ⟨hvz, (mem_sdiff.mp hv).1⟩)
        exact absurd (this ▸ hp) (hnp z hZ.mem))
      simpa using this)
    exact LOk_mono (by omega) this
  -- 頂 z を置く
  have hcl1 : Closed t c1 Z := hcl.of_out (fun v hv => hout1 v (fun h => hv (mem_of_mem_erase h)))
  have hready : t.ready c1 z = true := by
    apply ready_of_children
    intro u hu hp
    by_cases huZ : u ∈ Z
    · exact (h3 u (hG.topch u hu hp huZ)).1
    · rcases hcl1 z hZ.mem u hu hp with h | h
      · exact absurd h huZ
      · exact h
  set m := placeMove c1 z with hm
  set c2 := step c1 m with hc2
  have hc2e : c2 = Function.update c1 z Cell.pebble := step_placeMove c1 z
  have hTz : ∀ a ∈ T, a ≠ z := fun a ha => ne_of_mem_erase (hG.sub ha)
  have hc2T : ∀ a ∈ T, c2 a = Cell.pebble := by
    intro a ha; rw [hc2e, Function.update_of_ne (hTz a ha)]; exact (h3 a ha).1
  have hc2g : ∀ a ∈ T, ∀ v ∈ g a, v ≠ a → c2 v ≠ Cell.pebble := by
    intro a ha v hv hva
    have hvz : v ≠ z := ne_of_mem_erase (hG.gsub a ha hv)
    rw [hc2e, Function.update_of_ne hvz]; exact (h3 a ha).2 v hv hva
  have hL2 : LOk t Z (T.card + b) c1 [m] := LOk_single
    (by have := pc_after_fwd hG (fun a ha => (h3 a ha).2); omega)
    (by rw [hm, placeMove_v]; exact hZ.mem)
    (legal_placeMove hzn hc1z hready)
    (by show pc Z c2 ≤ T.card + b; have := pc_after_fwd hG hc2g; omega)
  -- 頂の集合 T をゴーストにする
  obtain ⟨ms3, g1, g2, g3⟩ := ghostAll (t := t) T c2
    (fun v hv => hZ.lt v (mem_of_mem_erase (hG.sub hv))) hc2T
  have hTZ : T ⊆ Z := fun a ha => mem_of_mem_erase (hG.sub ha)
  have hL3 : LOk t Z (T.card + b) c2 ms3 := by
    have := LOk_lift hTZ g1 (m := 1) (by
      have := pc_le_of (Q := Z \ T) (B := {z}) (c := c2) (by
        intro v hv hp
        by_contra hvz
        rw [mem_singleton] at hvz
        obtain ⟨hvZ, hvT⟩ := mem_sdiff.mp hv
        obtain ⟨a', ha', hva'⟩ := hG.cover v (mem_erase.mpr ⟨hvz, hvZ⟩)
        have hva : v ≠ a' := fun e => hvT (e ▸ ha')
        exact hc2g a' ha' v hva' hva hp)
      simpa using this)
    exact LOk_mono (by omega) this
  refine ⟨ms1 ++ (m :: ms3), (LOk_append ms1).mpr ⟨hL1, ⟨hL2.1, hL2.2.1, hL2.2.2.1, hL3⟩⟩, ?_, ?_, ?_⟩
  · rw [np_append, np_cons_place (by rw [hm]; exact placeMove_place c1 z), g2]
    have := hG.sum_card_le hZ.mem (subset_refl T)
    have := hZ.card_pos
    omega
  · rw [exec_app]
    show exec c2 ms3 z = _
    rw [LOk_out g1 z (fun h => hTz z h rfl), hc2e, Function.update_self]
  · intro v hv hvz
    rw [exec_app]
    show exec c2 ms3 v ≠ _
    by_cases hvT : v ∈ T
    · rw [g3 v hvT]; decide
    · rw [LOk_out g1 v hvT]
      obtain ⟨a', ha', hva'⟩ := hG.cover v (mem_erase.mpr ⟨hvz, hv⟩)
      exact hc2g a' ha' v hva' (fun e => hvT (e ▸ ha'))

theorem CL_step (ht : t.isTree = true) (hZ : Zone t Z z) (hG : Grp t d S Z z T g) (hb : 1 ≤ b)
    (hFF : ∀ a ∈ T, FFok t b (g a) a) (hCL : ∀ a ∈ T, CLok t b j (g a) a) :
    CLok t (T.card + b) (j + 1) Z z := by
  intro c hz hnp hcl
  have hzn := hZ.lt z hZ.mem
  obtain ⟨ms1, h1, h2, h3⟩ := fwd_loop ht hZ hG hb hFF T subset_rfl c
    (fun a _ haT => absurd ‹a ∈ T› haT)
    (fun a ha v hv => hnp v (grp_sub_Z hG ha hv) (ne_of_mem_erase (hG.gsub a ha hv))) hcl
  set c1 := exec c ms1 with hc1
  have hout1 : ∀ v, v ∉ Z.erase z → c1 v = c v := LOk_out h1
  have hc1z : c1 z = Cell.pebble := by rw [hout1 z (by simp)]; exact hz
  have hL1 : LOk t Z (T.card + b) c ms1 := by
    have := LOk_lift (erase_subset z Z) h1 (m := 1) (by
      have := pc_le_of (Q := Z \ Z.erase z) (B := {z}) (c := c) (by
        intro v hv _
        by_contra hvz
        rw [mem_singleton] at hvz
        exact (mem_sdiff.mp hv).2 (mem_erase.mpr ⟨hvz, (mem_sdiff.mp hv).1⟩))
      simpa using this)
    exact LOk_mono (by omega) this
  have hcl1 : Closed t c1 Z := hcl.of_out (fun v hv => hout1 v (fun h => hv (mem_of_mem_erase h)))
  have hready : t.ready c1 z = true := by
    apply ready_of_children
    intro u hu hp
    by_cases huZ : u ∈ Z
    · exact (h3 u (hG.topch u hu hp huZ)).1
    · rcases hcl1 z hZ.mem u hu hp with h | h
      · exact absurd h huZ
      · exact h
  set m : Move := ⟨Op.unpebble, z⟩ with hm
  have hleg : t.legal c1 m = true := by simp [RootedTree.legal, hm, hzn, hc1z, hready]
  set c2 := step c1 m with hc2
  have hc2e : c2 = Function.update c1 z Cell.empty := rfl
  have hTz : ∀ a ∈ T, a ≠ z := fun a ha => ne_of_mem_erase (hG.sub ha)
  have hc2g : ∀ a ∈ T, ∀ v ∈ g a, v ≠ a → c2 v ≠ Cell.pebble := by
    intro a ha v hv hva
    have hvz : v ≠ z := ne_of_mem_erase (hG.gsub a ha hv)
    rw [hc2e, Function.update_of_ne hvz]; exact (h3 a ha).2 v hv hva
  have hL2 : LOk t Z (T.card + b) c1 [m] := LOk_single
    (by have := pc_after_fwd hG (fun a ha => (h3 a ha).2); omega) hZ.mem hleg
    (by show pc Z c2 ≤ T.card + b; have := pc_after_fwd hG hc2g; omega)
  have hcl2 : Closed t c2 Z := hcl.of_out (fun v hv => by
    have hvz : v ≠ z := fun e => hv (e ▸ hZ.mem)
    rw [hc2e, Function.update_of_ne hvz]
    exact hout1 v (fun h => hv (mem_of_mem_erase h)))
  obtain ⟨ms3, k1, k2, k3⟩ := cl_loop ht hZ hG hb hCL T subset_rfl (fun _ _ a' ha' _ => ha') c2
    (fun a _ haT => absurd ‹a ∈ T› haT)
    (by
      intro a ha
      refine ⟨?_, hc2g a ha⟩
      rw [hc2e, Function.update_of_ne (hTz a ha)]; exact (h3 a ha).1)
    hcl2
  have hL3 : LOk t Z (T.card + b) c2 ms3 := by
    have := LOk_lift (erase_subset z Z) k1 (m := 0) (by
      have := pc_le_of (Q := Z \ Z.erase z) (B := ∅) (c := c2) (by
        intro v hv hp
        have : v = z := by
          by_contra hvz
          exact (mem_sdiff.mp hv).2 (mem_erase.mpr ⟨hvz, (mem_sdiff.mp hv).1⟩)
        rw [this, hc2e, Function.update_self] at hp
        exact absurd hp (by decide))
      simpa using this)
    exact LOk_mono (by omega) this
  refine ⟨ms1 ++ (m :: ms3), (LOk_append ms1).mpr ⟨hL1, ⟨hL2.1, hL2.2.1, hL2.2.2.1, hL3⟩⟩, ?_, ?_⟩
  · rw [np_append, np_cons_nonplace (by simp [IsPlace, hm])]
    have hs := hG.sum_card_le hZ.mem (subset_refl T)
    have : j * ∑ a ∈ T, (g a).card ≤ j * (Z.card - 1) := Nat.mul_le_mul_left _ hs
    rw [Nat.add_one_mul]
    omega
  · intro v hv
    rw [exec_app]
    show exec c2 ms3 v = _
    by_cases hvz : v = z
    · rw [hvz, LOk_out k1 z (by simp), hc2e, Function.update_self]
    · exact k3 v (mem_erase.mpr ⟨hvz, hv⟩)

end Step

/-! ## 段の仕様 -/

/-- 閾値 `S` の群の大きさの上限 `1 + d(S − 1)`（紙の `M_j`）。 -/
def Mg (d S : ℕ) : ℕ := 1 + d * (S - 1)

/-- 段の仕様: 大きさ `≤ M` のどの区域でも、全前進と（段 `j` の）片づけがペブル `b` 以下でできる。 -/
def Lev (t : RootedTree) (M b j : ℕ) : Prop :=
  ∀ Y y, Zone t Y y → Y.card ≤ M → FFok t b Y y ∧ CLok t b j Y y

theorem lev_one (ht : t.isTree = true) (M : ℕ) : Lev t M M 1 := fun _ _ hY hM =>
  ⟨(FF_base ht hY).mono hM, (CL_base ht hY).mono hM⟩

theorem lev_succ (ht : t.isTree = true) {d S M b j : ℕ} (hd : ∀ v, v < t.n → (chs t v).card ≤ d)
    (hS : 1 ≤ S) (hM : Mg d S ≤ M) (hb : 1 ≤ b) (hL : Lev t M b j) (M' : ℕ) :
    Lev t M' ((M' - 1) / S + d + b) (j + 1) := by
  intro Y y hY hYM
  obtain ⟨T, g, hG⟩ := grp_exists ht hd hS Y y hY
  have hsub : ∀ a ∈ T, FFok t b (g a) a ∧ CLok t b j (g a) a := fun a ha =>
    hL (g a) a (hG.zone a ha) (le_trans (hG.size a ha) hM)
  have hT : T.card + b ≤ (M' - 1) / S + d + b := by
    have h1 := hG.count
    have h2 : (Y.card - 1) / S ≤ (M' - 1) / S := Nat.div_le_div_right (by omega)
    exact Nat.add_le_add_right (le_trans h1 (Nat.add_le_add_right h2 d)) b
  exact ⟨(FF_step ht hY hG hb (fun a ha => (hsub a ha).1)).mono hT,
    (CL_step ht hY hG hb (fun a ha => (hsub a ha).1) (fun a ha => (hsub a ha).2)).mono hT⟩

/-- 段ごとのペブルの上限（`S j` は段 `j` の閾値）。`Bd d S 1 = 1 + d(S_1 − 1)`、
`Bd d S (j+1) = ⌊d(S_{j+1} − 1)/S_j⌋ + d + Bd d S j`。 -/
def Bd (d : ℕ) (S : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => Mg d (S 1)
  | j + 2 => (Mg d (S (j + 2)) - 1) / S (j + 1) + d + Bd d S (j + 1)

theorem Bd_pos (d : ℕ) (S : ℕ → ℕ) : ∀ j, 1 ≤ j → 1 ≤ Bd d S j
  | 0, h => absurd h (by decide)
  | 1, _ => by simp [Bd, Mg]
  | j + 2, _ => by
      have := Bd_pos d S (j + 1) (by omega)
      show 1 ≤ (Mg d (S (j + 2)) - 1) / S (j + 1) + d + Bd d S (j + 1)
      exact le_trans this (Nat.le_add_left _ _)

/-- **段 `j` の仕様**（`1 ≤ S_i`、`1 ≤ i < j`）。 -/
theorem lev_all (ht : t.isTree = true) {d : ℕ} (hd : ∀ v, v < t.n → (chs t v).card ≤ d)
    (S : ℕ → ℕ) : ∀ j, 1 ≤ j → (∀ i, 1 ≤ i → i < j → 1 ≤ S i) →
      Lev t (Mg d (S j)) (Bd d S j) j
  | 0, h, _ => absurd h (by decide)
  | 1, _, _ => lev_one ht _
  | j + 2, _, hS => by
      have hL := lev_all ht hd S (j + 1) (by omega) (fun i hi1 hi2 => hS i hi1 (by omega))
      exact lev_succ ht hd (hS (j + 1) (by omega) (by omega)) le_rfl (Bd_pos d S (j + 1) (by omega))
        hL (Mg d (S (j + 2)))

/-! ## 全体 `C_K` -/

theorem zone_all (ht : t.isTree = true) : Zone t (range t.n) t.root := by
  refine ⟨mem_range.mpr (isTree_spec ht).1, fun v hv => mem_range.mp hv,
    fun v hv => anc_of_root ht (mem_range.mp hv), ?_⟩
  intro v hv hvr
  have hvn := mem_range.mp hv
  cases hp : t.par v with
  | none => exact absurd (parOk_none ((isTree_spec ht).2 v hvn).1 hp) hvr
  | some p => exact ⟨p, mem_range.mpr (parOk_some ((isTree_spec ht).2 v hvn).1 hp).1, rfl⟩

/-- **全体の構成**: 段 `j` の仕様（区域の大きさ `≤ M`）と閾値 `S`（`1 + d(S−1) ≤ M`）から、
全部空 → 根だけペブル の手順で、ペブル `≤ ⌊(n−1)/S⌋ + d + b`、置く手 `≤ (j+1)n`。 -/
theorem global_run (ht : t.isTree = true) {d S M b j : ℕ} (hd : ∀ v, v < t.n → (chs t v).card ≤ d)
    (hS : 1 ≤ S) (hM : Mg d S ≤ M) (hb : 1 ≤ b) (hL : Lev t M b j) :
    ∃ ms, LOk t (range t.n) ((t.n - 1) / S + d + b) allEmpty ms ∧ np ms ≤ (j + 1) * t.n ∧
      AgreeOn t.n (exec allEmpty ms) t.rootPebble := by
  set Z := range t.n with hZdef
  set z := t.root
  have hZ : Zone t Z z := zone_all ht
  have hzn := hZ.lt z hZ.mem
  obtain ⟨T, g, hG⟩ := grp_exists ht hd hS Z z hZ
  have hsub : ∀ a ∈ T, FFok t b (g a) a ∧ CLok t b j (g a) a := fun a ha =>
    hL (g a) a (hG.zone a ha) (le_trans (hG.size a ha) hM)
  have hclE : ∀ c : Config, Closed t c Z := fun c v _ u hu _ => Or.inl (mem_range.mpr hu)
  have hTb : T.card + b ≤ (t.n - 1) / S + d + b := by
    have := hG.count; rw [card_range] at this; exact Nat.add_le_add_right this b
  obtain ⟨ms1, h1, h2, h3⟩ := fwd_loop ht hZ hG hb (fun a ha => (hsub a ha).1) T subset_rfl allEmpty
    (fun a _ haT => absurd ‹a ∈ T› haT) (fun _ _ _ _ => by simp [allEmpty]) (hclE _)
  set c1 := exec allEmpty ms1 with hc1
  have hout1 : ∀ v, v ∉ Z.erase z → c1 v = allEmpty v := LOk_out h1
  have hc1z : c1 z ≠ Cell.pebble := by rw [hout1 z (by simp)]; simp [allEmpty]
  have hL1 : LOk t Z (T.card + b) allEmpty ms1 := by
    have := LOk_lift (erase_subset z Z) h1 (m := 0) (by
      have := pc_le_of (Q := Z \ Z.erase z) (B := ∅) (c := allEmpty) (by
        intro v _ hp; simp [allEmpty] at hp)
      simpa using this)
    exact LOk_mono (by omega) this
  have hready : t.ready c1 z = true := by
    apply ready_of_children
    intro u hu hp
    exact (h3 u (hG.topch u hu hp (mem_range.mpr hu))).1
  set m := placeMove c1 z with hm
  set c2 := step c1 m with hc2
  have hc2e : c2 = Function.update c1 z Cell.pebble := step_placeMove c1 z
  have hTz : ∀ a ∈ T, a ≠ z := fun a ha => ne_of_mem_erase (hG.sub ha)
  have hc2g : ∀ a ∈ T, ∀ v ∈ g a, v ≠ a → c2 v ≠ Cell.pebble := by
    intro a ha v hv hva
    have hvz : v ≠ z := ne_of_mem_erase (hG.gsub a ha hv)
    rw [hc2e, Function.update_of_ne hvz]; exact (h3 a ha).2 v hv hva
  have hL2 : LOk t Z (T.card + b) c1 [m] := LOk_single
    (by have := pc_after_fwd hG (fun a ha => (h3 a ha).2); omega)
    (by rw [hm, placeMove_v]; exact hZ.mem) (legal_placeMove hzn hc1z hready)
    (by show pc Z c2 ≤ T.card + b; have := pc_after_fwd hG hc2g; omega)
  obtain ⟨ms3, k1, k2, k3⟩ := cl_loop ht hZ hG hb (fun a ha => (hsub a ha).2) T subset_rfl
    (fun _ _ a' ha' _ => ha') c2 (fun a _ haT => absurd ‹a ∈ T› haT)
    (by
      intro a ha
      refine ⟨?_, hc2g a ha⟩
      rw [hc2e, Function.update_of_ne (hTz a ha)]; exact (h3 a ha).1)
    (hclE _)
  have hL3 : LOk t Z (T.card + b) c2 ms3 := by
    have := LOk_lift (erase_subset z Z) k1 (m := 1) (by
      have := pc_le_of (Q := Z \ Z.erase z) (B := {z}) (c := c2) (by
        intro v hv _
        by_contra hvz
        rw [mem_singleton] at hvz
        exact (mem_sdiff.mp hv).2 (mem_erase.mpr ⟨hvz, (mem_sdiff.mp hv).1⟩))
      simpa using this)
    exact LOk_mono (by omega) this
  refine ⟨ms1 ++ (m :: ms3), LOk_mono hTb ((LOk_append ms1).mpr
    ⟨hL1, ⟨hL2.1, hL2.2.1, hL2.2.2.1, hL3⟩⟩), ?_, ?_⟩
  · rw [np_append, np_cons_place (by rw [hm]; exact placeMove_place c1 z)]
    have hs := hG.sum_card_le hZ.mem (subset_refl T)
    rw [card_range] at hs
    have : j * ∑ a ∈ T, (g a).card ≤ j * (t.n - 1) := Nat.mul_le_mul_left _ hs
    have hjn : j * (t.n - 1) ≤ j * t.n := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    rw [Nat.add_one_mul]
    omega
  · intro v hv
    rw [exec_app]
    show exec c2 ms3 v = _
    unfold RootedTree.rootPebble
    by_cases hvz : v = z
    · rw [hvz, LOk_out k1 z (by simp), hc2e, Function.update_self, Function.update_self]
    · rw [k3 v (mem_erase.mpr ⟨hvz, mem_range.mpr hv⟩), Function.update_of_ne hvz]
      rfl

end UUB
end RootedTree
end Spooky
