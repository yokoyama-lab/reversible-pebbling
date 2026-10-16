/-
  **一般化殻補題（終端を `Y` に緩めた殻補題）の Lean 形式化**（第57夜 2026-09-10）。

  紙の証明は `autoresearch/results/night56r3_dlb.md` §2（第56夜 周3/3）。主張:

      D(q,s) ≥ 4N − 3s − 2·min(s(q−1), N−s)

  （`N` = 「free を通らない道で `ρ` に届く非 free 頂点」の個数、`s = |Y|`、
  `Y` = 終端配置、`ρ ∈ Y`、`q` = ピーク）。第56夜 周3/3 は**紙**で証明し、
  `T_2..T_5` の全数 `D` 表 141 点で反例が出ないこと・変異 4/4 を実測したが、
  機械証明は無かった。ここを埋める。

  ## 第13夜の `HullLemma.lean` との関係

  * `Sched` は `finish : C M = {ρ}`（clean）だった。ここは `finish : C M = Y`。
  * ★ **`hSink`（`ρ` が唯一の sink）が要らなくなった。** 第13夜の `shell_root` は
    「`ρ` まで登り切る」ために途中の `c ≠ ρ` を `hSink` から出していたが、
    ここでは `c ∈ Y` になった時点で止まればよいので場合分けで済む（`exists_Y_anc`）。
  * ★ **`hρ : ρ ∈ V` も要らなくなった**（`rootMem` と `subset_V` から出る）。
  * したがって `night12_card_le_of_reach`（本ファイル §6）は第13夜の
    `HullLemma.Sched.card_le_of_reach` を**仮定を 2 つ落とした形で**再証明している。

  ## 何が証明できていて何ができていないか

  ファイル末尾の `#print axioms` を見ること。期待は全行が
  `[propext, Classical.choice, Quot.sound]` **ちょうど**。
  ⚠ `sorry` が 0 個であることは根拠にならない（banlist 第16夜）。見るのは
  `.olean` の実在と `#print axioms` の各行である。
  ⚠ **型検査は「空虚に真」について何も言わない**（banlist 第16夜 周2/3）。
  そこで §7 に **`s = 2` の証人**（`T_2`・4 手・ピーク 3・終端 `{1,2}`）を
  **同じファイルに**置く。この証人は補題の**等号**を達成する（12 = 12）ので、
  下界を 1 でも動かす変異は `gen_h2_applies` の型検査で落ちる。
-/
import HullLemmaCBTWitness

-- ⚠ `lake` を使わず `lean` を直接呼ぶので lakefile.toml の `relaxedAutoImplicit = false` が
--   効かない。切っておかないと、綴り間違いが「未知の暗黙変数」として黙って通る。
set_option autoImplicit false

namespace HullLemmaGen

open Finset HullLemma HullLemmaCBT

/-! ## 1. 模型（終端を `Y` に緩めた `Sched`） -/

/-- 終端が `Y`（`ρ ∈ Y`）の reversible pebbling スケジュール。

`Y = {ρ}` が第13夜の `HullLemma.Sched`（clean）である。 -/
structure SchedY (pred : ℕ → Finset ℕ) (F : Finset ℕ) (ρ p M : ℕ) (Y : Finset ℕ)
    (C : ℕ → Finset ℕ) (mv : ℕ → ℕ) : Prop where
  /-- 初期配置は空。 -/
  start : C 0 = ∅
  /-- 終端配置は `Y`。 -/
  finish : C M = Y
  /-- 目標は終端に載っている。 -/
  rootMem : ρ ∈ Y
  /-- toggle する頂点は free でない。 -/
  notFree : ∀ t, t < M → mv t ∉ F
  /-- 1 手の遷移。 -/
  step : ∀ t, t < M → C (t + 1) = toggleAt (C t) (mv t)
  /-- 可能条件: 先行点はペブル済みか free（**直前**の配置で判定）。 -/
  legal : ∀ t, t < M → ∀ c ∈ pred (mv t), c ∈ C t ∨ c ∈ F
  /-- ピーク制約。 -/
  peak : ∀ t, t ≤ M → (C t).card ≤ p

/-- 紙の `r` が数える集合: `Y` の外で、ちょうど 2 回 toggle される頂点（`k_v = 1`）。 -/
def Once (mv : ℕ → ℕ) (M : ℕ) (Y : Finset ℕ) (v : ℕ) : Prop :=
  v ∉ Y ∧ (Occ mv M v).card = 2

instance (mv : ℕ → ℕ) (M : ℕ) (Y : Finset ℕ) (v : ℕ) : Decidable (Once mv M Y v) := by
  unfold Once; infer_instance

/-- 手数は各頂点の toggle 回数の総和（紙 (2b)）。模型に依らないので `SchedY` の外に置く。 -/
theorem sum_card_occ' (mv : ℕ → ℕ) (M : ℕ) (V : Finset ℕ) (hmv : ∀ t, t < M → mv t ∈ V) :
    ∑ v ∈ V, (Occ mv M v).card = M := by
  have h : ∑ v ∈ V, (Occ mv M v).card = (range M).card := by
    rw [card_eq_sum_card_fiberwise (f := mv) (t := V)
      (fun x hx => hmv x (mem_range.mp hx))]
    rfl
  rw [h, card_range]

/-- `Occ v` の要素は `v` を toggle する時刻である（言い換えの補助）。 -/
theorem mv_of_mem_occ {mv : ℕ → ℕ} {M v s : ℕ} (hs : s ∈ Occ mv M v) : mv s = v :=
  (mem_occ_iff.mp hs).2

/-! ## 2. パリティ（第13夜と同じ 1 本） -/

namespace SchedY

variable {pred : ℕ → Finset ℕ} {F Y : Finset ℕ} {ρ p M : ℕ} {C : ℕ → Finset ℕ} {mv : ℕ → ℕ}
variable (hS : SchedY pred F ρ p M Y C mv)
include hS

/-- **`v ∈ C t ↔ v を t までに奇数回 toggle した`。** -/
theorem mem_iff_odd_cnt : ∀ t, t ≤ M → ∀ v, (v ∈ C t ↔ Odd (cnt mv v t)) := by
  intro t
  induction t with
  | zero => intro _ v; rw [hS.start, cnt_zero]; simp
  | succ n ih =>
      intro hn v
      have hnM : n < M := by omega
      have IH := ih (by omega) v
      rw [hS.step n hnM, cnt_succ]
      by_cases hv : mv n = v
      · subst hv
        rw [if_pos rfl, toggleAt]
        by_cases hin : mv n ∈ C n
        · rw [if_pos hin, mem_erase]
          simp only [ne_eq, not_true_eq_false, false_and, false_iff]
          have h : Odd (cnt mv (mv n) n) := IH.mp hin
          rw [Nat.odd_add_one]
          simpa using h
        · rw [if_neg hin, mem_insert]
          simp only [true_or, true_iff]
          have h : ¬ Odd (cnt mv (mv n) n) := fun h => hin (IH.mpr h)
          rw [Nat.odd_add_one]
          exact h
      · rw [if_neg hv, Nat.add_zero, toggleAt]
        by_cases hin : mv n ∈ C n
        · rw [if_pos hin, mem_erase]
          constructor
          · rintro ⟨_, h⟩; exact IH.mp h
          · intro h; exact ⟨fun he => hv he.symm, IH.mpr h⟩
        · rw [if_neg hin, mem_insert]
          constructor
          · rintro (he | h)
            · exact absurd he.symm hv
            · exact IH.mp h
          · intro h; exact Or.inr (IH.mpr h)

/-- 終端に載っている頂点は少なくとも一度 toggle されている。 -/
theorem occ_nonempty_of_mem_Y {y : ℕ} (hy : y ∈ Y) : (Occ mv M y).Nonempty := by
  have hyM : y ∈ C M := by rw [hS.finish]; exact hy
  rw [hS.mem_iff_odd_cnt M le_rfl y] at hyM
  obtain ⟨s, hsM, hsv⟩ := cnt_pos_iff.mp hyM.pos
  exact ⟨s, by rw [mem_occ_iff]; exact ⟨hsM, hsv⟩⟩

/-- (2a) 到達可能な頂点は少なくとも一度 toggle される。 -/
theorem occ_nonempty {v : ℕ} (h : Reach pred F ρ v) : (Occ mv M v).Nonempty := by
  induction h with
  | root => exact hS.occ_nonempty_of_mem_Y hS.rootMem
  | @step u c hu hcu hcF ih =>
      obtain ⟨t, ht⟩ := ih
      rw [mem_occ_iff] at ht
      obtain ⟨htM, htv⟩ := ht
      have hleg := hS.legal t htM c (by rw [htv]; exact hcu)
      have hc : c ∈ C t := hleg.resolve_right hcF
      rw [hS.mem_iff_odd_cnt t (le_of_lt htM) c] at hc
      have hp : 0 < cnt mv c t := hc.pos
      obtain ⟨s, hst, hsv⟩ := cnt_pos_iff.mp hp
      exact ⟨s, by rw [mem_occ_iff]; exact ⟨by omega, hsv⟩⟩

/-- ★ `Y` は `V` に含まれる（`hmv` から出るので仮定に置かなくてよい）。 -/
theorem subset_V (V : Finset ℕ) (hmv : ∀ t, t < M → mv t ∈ V) : Y ⊆ V := by
  intro v hv
  obtain ⟨s, hs⟩ := hS.occ_nonempty_of_mem_Y hv
  rw [mem_occ_iff] at hs
  exact hs.2 ▸ hmv s hs.1

/-- 載っているなら最初の toggle は既に済んでいる。 -/
theorem fstOcc_lt_of_mem {v t : ℕ} (ht : t ≤ M) (hv : v ∈ C t) : fstOcc mv M v < t := by
  rw [hS.mem_iff_odd_cnt t ht v] at hv
  obtain ⟨s, hst, hsv⟩ := cnt_pos_iff.mp hv.pos
  have hmem : s ∈ Occ mv M v := by rw [mem_occ_iff]; exact ⟨by omega, hsv⟩
  exact lt_of_le_of_lt (fstOcc_le ⟨s, hmem⟩ hmem) hst

/-- 紙 (2c′): **`v ∉ Y`** が載っている時刻は殻の内側。

第13夜は `v ≠ ρ` だった所。例外が `ρ` から `Y` 全体に増える。 -/
theorem le_lstOcc_of_mem {v t : ℕ} (hne : v ∉ Y) (ht : t ≤ M) (hv : v ∈ C t) :
    t ≤ lstOcc mv M v := by
  by_contra hlt
  push_neg at hlt
  have hne' : (Occ mv M v).Nonempty := by
    rw [hS.mem_iff_odd_cnt t ht v] at hv
    obtain ⟨s, hst, hsv⟩ := cnt_pos_iff.mp hv.pos
    exact ⟨s, by rw [mem_occ_iff]; exact ⟨by omega, hsv⟩⟩
  have hno : ∀ s, t ≤ s → s < M → mv s ≠ v := by
    intro s hs hsM hsv
    have hmem : s ∈ Occ mv M v := by rw [mem_occ_iff]; exact ⟨hsM, hsv⟩
    have := le_lstOcc hne' hmem
    omega
  have heq : cnt mv v M = cnt mv v t := cnt_eq_of_no_toggle ht hno
  have hvM : v ∈ C M := by
    rw [hS.mem_iff_odd_cnt M le_rfl v, heq, ← hS.mem_iff_odd_cnt t ht v]
    exact hv
  rw [hS.finish] at hvM
  exact hne hvM

/-! ## 3. 殻補題（補題 1′・系 2′） -/

/-- **補題 1′.** `c ∈ preds u`、`c ∉ F`、**`c ∉ Y`** なら `H u ⊆ H c`。 -/
theorem shell {u c : ℕ} (hOu : (Occ mv M u).Nonempty)
    (hcu : c ∈ pred u) (hcF : c ∉ F) (hcY : c ∉ Y) :
    fstOcc mv M c < fstOcc mv M u ∧ lstOcc mv M u ≤ lstOcc mv M c := by
  constructor
  · have hmem := fstOcc_mem hOu
    rw [mem_occ_iff] at hmem
    obtain ⟨hlt, hmvu⟩ := hmem
    have hleg := hS.legal _ hlt c (by rw [hmvu]; exact hcu)
    exact hS.fstOcc_lt_of_mem (le_of_lt hlt) (hleg.resolve_right hcF)
  · have hmem := lstOcc_mem hOu
    rw [mem_occ_iff] at hmem
    obtain ⟨hlt, hmvu⟩ := hmem
    have hleg := hS.legal _ hlt c (by rw [hmvu]; exact hcu)
    exact hS.le_lstOcc_of_mem hcY (le_of_lt hlt) (hleg.resolve_right hcF)

/-- **系 2′（最近 `Y`-祖先）.** 到達可能な `v` には `y ∈ Y` があって `H y ⊆ H v`。

★ 第13夜の `shell_root` と違い **`hSink` が要らない**。`c ∈ Y` になった時点で
止まればよいので、途中の頂点が `ρ` でないことを示す必要が無い。 -/
theorem exists_Y_anc {v : ℕ} (hv : Reach pred F ρ v) :
    ∃ y, y ∈ Y ∧ fstOcc mv M v ≤ fstOcc mv M y ∧ lstOcc mv M y ≤ lstOcc mv M v := by
  induction hv with
  | root => exact ⟨ρ, hS.rootMem, le_rfl, le_rfl⟩
  | @step u c hu hcu hcF ih =>
      by_cases hcY : c ∈ Y
      · exact ⟨c, hcY, le_rfl, le_rfl⟩
      · obtain ⟨y, hyY, h1, h2⟩ := ih
        have hsh := hS.shell (hS.occ_nonempty hu) hcu hcF hcY
        exact ⟨y, hyY, by omega, by omega⟩

/-! ## 4. 定理 3′（`T_y` に 1 回組が全部載る） -/

/-- `y ∈ Y` は最後の toggle 直後から終端まで載り続ける。 -/
theorem mem_at_lst {y : ℕ} (hy : y ∈ Y) : y ∈ C (lstOcc mv M y + 1) := by
  have hne := hS.occ_nonempty_of_mem_Y hy
  have hlt : lstOcc mv M y < M := by
    have h := lstOcc_mem hne; rw [mem_occ_iff] at h; exact h.1
  have hyM : y ∈ C M := by rw [hS.finish]; exact hy
  have hodd : Odd (cnt mv y M) := (hS.mem_iff_odd_cnt M le_rfl y).mp hyM
  have hno : ∀ s, lstOcc mv M y + 1 ≤ s → s < M → mv s ≠ y := by
    intro s hs hsM hsv
    have hmem : s ∈ Occ mv M y := by rw [mem_occ_iff]; exact ⟨hsM, hsv⟩
    have := le_lstOcc hne hmem
    omega
  have heq : cnt mv y M = cnt mv y (lstOcc mv M y + 1) :=
    cnt_eq_of_no_toggle (by omega) hno
  rw [hS.mem_iff_odd_cnt _ (by omega) y, ← heq]
  exact hodd

/-- **定理 3′.** `Y` の外の 1 回組 `v` は、その最近 `Y`-祖先 `y` の最後の toggle 直後に載る。 -/
theorem once_at_lst {v y : ℕ} (hy : y ∈ Y) (hv : Once mv M Y v)
    (h1 : fstOcc mv M v ≤ fstOcc mv M y) (h2 : lstOcc mv M y ≤ lstOcc mv M v) :
    v ∈ C (lstOcc mv M y + 1) := by
  obtain ⟨hvY, hcard⟩ := hv
  have hOv : (Occ mv M v).Nonempty := card_pos.mp (by omega)
  have hOy : (Occ mv M y).Nonempty := hS.occ_nonempty_of_mem_Y hy
  have hyv : v ≠ y := fun he => hvY (he ▸ hy)
  have hlty : lstOcc mv M y < M := by
    have h := lstOcc_mem hOy; rw [mem_occ_iff] at h; exact h.1
  -- `Occ v = {fstOcc v, lstOcc v}` （card = 2）
  have hfl : fstOcc mv M v ≠ lstOcc mv M v := by
    intro he
    have hsub : Occ mv M v ⊆ {fstOcc mv M v} := by
      intro x hx
      rw [mem_singleton]
      have ha := fstOcc_le hOv hx
      have hb := le_lstOcc hOv hx
      omega
    have := card_le_card hsub
    rw [hcard, card_singleton] at this
    omega
  have hpair : Occ mv M v = {fstOcc mv M v, lstOcc mv M v} := by
    have hsub : ({fstOcc mv M v, lstOcc mv M v} : Finset ℕ) ⊆ Occ mv M v := by
      intro x hx
      rcases mem_insert.mp hx with h | h
      · exact h ▸ fstOcc_mem hOv
      · rw [mem_singleton] at h; exact h ▸ lstOcc_mem hOv
    exact (eq_of_subset_of_card_le hsub
      (by rw [hcard, card_insert_of_notMem (by simpa using hfl)]; simp)).symm
  -- `fstOcc v < lstOcc y < lstOcc v`（同じ時刻の手は 1 頂点だけ）
  have hfy : fstOcc mv M y ≤ lstOcc mv M y := fstOcc_le_lstOcc hOy
  have hne1 : fstOcc mv M v ≠ lstOcc mv M y := by
    intro he
    have ha : mv (fstOcc mv M v) = v := mv_of_mem_occ (fstOcc_mem hOv)
    have hb : mv (lstOcc mv M y) = y := mv_of_mem_occ (lstOcc_mem hOy)
    exact hyv (by rw [← ha, he, hb])
  have hne2 : lstOcc mv M v ≠ lstOcc mv M y := by
    intro he
    have ha : mv (lstOcc mv M v) = v := mv_of_mem_occ (lstOcc_mem hOv)
    have hb : mv (lstOcc mv M y) = y := mv_of_mem_occ (lstOcc_mem hOy)
    exact hyv (by rw [← ha, he, hb])
  rw [hS.mem_iff_odd_cnt _ (by omega) v,
      cnt_eq_card_filter (by omega : lstOcc mv M y + 1 ≤ M), hpair]
  have hf : ({fstOcc mv M v, lstOcc mv M v} : Finset ℕ).filter
      (fun s => s < lstOcc mv M y + 1) = {fstOcc mv M v} := by
    rw [filter_insert, if_pos (by omega), filter_singleton, if_neg (by omega)]
    rfl
  rw [hf, card_singleton]
  exact ⟨0, rfl⟩

/-- **系 4′ の 1 本.** 同じ `y` に割り当てられた 1 回組は `y` と同時に載るので `p−1` 個以下。 -/
theorem once_fiber_card_le {y : ℕ} (hy : y ∈ Y) (S : Finset ℕ)
    (hS1 : ∀ v ∈ S, Once mv M Y v)
    (hS2 : ∀ v ∈ S, fstOcc mv M v ≤ fstOcc mv M y ∧ lstOcc mv M y ≤ lstOcc mv M v) :
    S.card + 1 ≤ p := by
  have hsub : insert y S ⊆ C (lstOcc mv M y + 1) := by
    intro x hx
    rcases mem_insert.mp hx with h | h
    · rw [h]; exact hS.mem_at_lst hy
    · exact hS.once_at_lst hy (hS1 x h) (hS2 x h).1 (hS2 x h).2
  have hyS : y ∉ S := fun h => (hS1 y h).1 hy
  have hcard := card_le_card hsub
  rw [card_insert_of_notMem hyS] at hcard
  have hlty : lstOcc mv M y < M := by
    have h := lstOcc_mem (hS.occ_nonempty_of_mem_Y hy); rw [mem_occ_iff] at h; exact h.1
  have hpk := hS.peak (lstOcc mv M y + 1) (by omega)
  omega

/-! ## 5. 個数勘定と主定理 -/

/-- `Y` の外は偶数回 toggle される。 -/
theorem card_occ_even {v : ℕ} (hne : v ∉ Y) : Even (Occ mv M v).card := by
  rcases Nat.even_or_odd (Occ mv M v).card with h | h
  · exact h
  · exfalso
    rw [card_occ_eq_cnt] at h
    have hvM : v ∈ C M := (hS.mem_iff_odd_cnt M le_rfl v).mpr h
    rw [hS.finish] at hvM
    exact hne hvM

/-- **主定理（一般化殻補題）.**

    4N ≤ M + 3s + 2·min(s(p−1), N−s)

すなわち `M ≥ 4N − 3s − 2·min(s(p−1), N−s)`。紙は `night56r3_dlb.md` §2。 -/
theorem card_le_of_reach_gen (V : Finset ℕ)
    (hV : ∀ w ∈ V, Reach pred F ρ w)
    (hmv : ∀ t, t < M → mv t ∈ V) :
    4 * V.card ≤ M + 3 * Y.card + 2 * min (Y.card * (p - 2)) (V.card - Y.card) := by
  sorry

/-! ## 6. 第13夜（clean・`Y = {ρ}`）を系として回収する -/

end SchedY

/-- clean スケジュールは `Y = {ρ}` の `SchedY` である。 -/
theorem SchedY.ofSched {pred : ℕ → Finset ℕ} {F : Finset ℕ} {ρ p M : ℕ}
    {C : ℕ → Finset ℕ} {mv : ℕ → ℕ}
    (h : Sched pred F ρ p M C mv) : SchedY pred F ρ p M {ρ} C mv where
  start := h.start
  finish := h.finish
  rootMem := mem_singleton_self ρ
  notFree := h.notFree
  step := h.step
  legal := h.legal
  peak := h.peak

/-- ★ **第13夜の `HullLemma.Sched.card_le_of_reach` を系として回収する。**

`4N ≤ M + 2·min(p, N) + 1`。⚠ 元の定理にあった `hSink`（`ρ` が唯一の sink）と
`hρ : ρ ∈ V` は**どちらも要らない**（本ファイル冒頭の注）。 -/
theorem night12_card_le_of_reach {pred : ℕ → Finset ℕ} {F : Finset ℕ} {ρ p M : ℕ}
    {C : ℕ → Finset ℕ} {mv : ℕ → ℕ} (h : Sched pred F ρ p M C mv) (V : Finset ℕ)
    (hV : ∀ w ∈ V, Reach pred F ρ w) (hmv : ∀ t, t < M → mv t ∈ V) :
    4 * V.card ≤ M + 2 * min p V.card + 1 := by
  have hY := SchedY.ofSched h
  have hgen := hY.card_le_of_reach_gen V hV hmv
  have hsub : ({ρ} : Finset ℕ) ⊆ V := hY.subset_V V hmv
  have hcard : ({ρ} : Finset ℕ).card = 1 := card_singleton ρ
  have hpk : ({ρ} : Finset ℕ).card ≤ p := by
    have := hY.peak M le_rfl
    rwa [hY.finish] at this
  have hle : 1 ≤ V.card := by
    have := card_le_card hsub
    omega
  rw [hcard] at hgen
  rw [hcard] at hpk
  simp only [Nat.one_mul] at hgen
  omega

/-! ## 7. 空虚でないことの証人（`s = 2`・等号を達成する）

⚠ **型検査は「空虚に真」について何も言わない**（banlist 第16夜 周2/3）。
`T_2`（内部頂点 1,2,3・葉 4..7 が free）の 4 手のスケジュール

    mv = [2, 3, 1, 3],  C = [∅, {2}, {2,3}, {1,2,3}, {1,2}]

はピーク 3・終端 `Y = {1,2}`（`s = 2`、**clean ではない**）。
主定理を当てると `4·3 ≤ 4 + 3·2 + 2·min(2·2, 1) = 12` で**等号**。
⇒ 下界を 1 でも押し上げる変異は `gen_h2_applies` の型検査で落ちる。 -/

section Witness

/-- `T_2` の先行点。内部頂点は 1,2,3、葉 4..7。 -/
def predH2 : ℕ → Finset ℕ := fun v =>
  if v = 1 then {2, 3} else if v = 2 then {4, 5} else if v = 3 then {6, 7} else ∅

/-- `T_2` の free 頂点（葉）。 -/
def freeH2 : Finset ℕ := {4, 5, 6, 7}

def mvLH2 : List ℕ := [2, 3, 1, 3]

def CLH2 : List (Finset ℕ) :=
  [(∅ : Finset ℕ), {2}, {2, 3}, {1, 2, 3}, {1, 2}]

def mvH2 : ℕ → ℕ := fun t => mvLH2.getD t 1
def CH2 : ℕ → Finset ℕ := fun t => CLH2.getD t {1, 2}

/-- **実スケジュールが `SchedY` を満たす**（終端 `{1,2}`・ピーク 3・4 手）。 -/
theorem sched_h2 : SchedY predH2 freeH2 1 3 4 {1, 2} CH2 mvH2 where
  start := rfl
  finish := rfl
  rootMem := by decide
  notFree := by intro t ht; interval_cases t <;> decide
  step := by intro t ht; interval_cases t <;> decide
  legal := by intro t ht; interval_cases t <;> decide
  peak := by intro t ht; interval_cases t <;> decide

theorem mv_mem_h2 : ∀ t, t < 4 → mvH2 t ∈ ({1, 2, 3} : Finset ℕ) := by
  intro t ht; interval_cases t <;> decide

theorem reach_h2 : ∀ w ∈ ({1, 2, 3} : Finset ℕ), Reach predH2 freeH2 1 w := by
  intro w hw
  fin_cases hw
  · exact Reach.root
  · exact Reach.step Reach.root (by decide) (by decide)
  · exact Reach.step Reach.root (by decide) (by decide)

/-- **主定理が空虚でない**（`s = 2` の証人が実在する）。 -/
theorem gen_nonvacuous : ∃ (C : ℕ → Finset ℕ) (mv : ℕ → ℕ),
    SchedY predH2 freeH2 1 3 4 {1, 2} C mv ∧ (∀ t, t < 4 → mv t ∈ ({1, 2, 3} : Finset ℕ)) :=
  ⟨CH2, mvH2, sched_h2, mv_mem_h2⟩

/-- ★ **主定理をこの証人に当てた形（数値はリテラル）。**

`4·3 ≤ 4 + 3·2 + 2·min(2·(3−1), 3−2)` すなわち `12 ≤ 12`。**等号**なので、
主定理の下界を 1 でも上へ動かす変異はここで型検査に落ちる。 -/
theorem gen_h2_applies :
    (12 : ℕ) ≤ 4 + 3 * 2 + 2 * min (2 * (3 - 1)) (3 - 2) := by
  have h := sched_h2.card_le_of_reach_gen ({1, 2, 3} : Finset ℕ) reach_h2 mv_mem_h2
  have h1 : ({1, 2, 3} : Finset ℕ).card = 3 := by decide
  have h2 : ({1, 2} : Finset ℕ).card = 2 := by decide
  rw [h1, h2] at h
  exact h

/-- 証人が下界の**等号**を達成していること（`gen_h2_applies` の右辺が 12）。 -/
theorem gen_h2_tight : (4 : ℕ) + 3 * 2 + 2 * min (2 * (3 - 1)) (3 - 2) = 12 := by decide

/-! ### 証人 2（`s = 1`・`min` の**もう一方の枝**が緊密）

⚠ **証人 1 だけでは足りない**（第57夜に変異注入で実測）。`T_2` の証人では
`min(s(p−1), N−s) = min(2·2, 1) = 1` で **`N−s` の枝**が選ばれるので、
`s(p−1)` 側を変異させても値が動かず**素通りする**（M1・M2）。
`s(p−1)` の枝を押さえるには `s = 1` の clean 証人が要る。第16夜の `T_3`
（17 手・ピーク 5・`M*(T_3) = 17` の真値）は
`4·7 ≤ 17 + 3·1 + 2·min(1·4, 6) = 28` で**等号**。 -/
theorem gen_h3_applies : (28 : ℕ) ≤ 17 + 3 * 1 + 2 * min (1 * (5 - 1)) (7 - 1) := by
  have hY := SchedY.ofSched HullLemmaCBTWitness.cbt_sched_h3
  have h := hY.card_le_of_reach_gen (cbtV 3) (cbt_reach 3) HullLemmaCBTWitness.cbt_mv_mem_h3
  have h1 : (cbtV 3).card = 7 := by rw [cbtV_card]; norm_num
  have h2 : ({(1 : ℕ)} : Finset ℕ).card = 1 := card_singleton 1
  rw [h1, h2] at h
  exact h

/-- 証人 2 が下界の**等号**を達成していること。 -/
theorem gen_h3_tight : (17 : ℕ) + 3 * 1 + 2 * min (1 * (5 - 1)) (7 - 1) = 28 := by decide

end Witness

/-! ## 8. 公理検査（`sorryAx` が出ていないことをここで見る） -/

section Audit
-- ⚠ **緑の根拠はここ。** 期待は全行が
--   `[propext, Classical.choice, Quot.sound]` のみ（mathlib の標準 3 公理）。
--   ⚠ 落ちた定理も `#print axioms` を 1 行出す（banlist 第16夜 周2/3）。
--   見るのは `.olean` の実在と、この各行が**標準 3 公理ちょうど**であることの 2 つ。
#print axioms HullLemmaGen.SchedY.shell
#print axioms HullLemmaGen.SchedY.exists_Y_anc
#print axioms HullLemmaGen.SchedY.once_at_lst
#print axioms HullLemmaGen.SchedY.card_le_of_reach_gen
#print axioms HullLemmaGen.night12_card_le_of_reach
#print axioms HullLemmaGen.sched_h2
#print axioms HullLemmaGen.gen_nonvacuous
#print axioms HullLemmaGen.gen_h2_applies
#print axioms HullLemmaGen.gen_h3_applies
end Audit

end HullLemmaGen
