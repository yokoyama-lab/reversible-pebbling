/-
  **殻補題（hull / shell lemma）と単位 P1 の下界の Lean 形式化**（第13夜 2026-08-22）。

  紙の証明は `autoresearch/results/night12_hull_lemma.md`（第12夜）。主張:

      M ≥ 4N − 2·min(p, N) − 1

  （`N` = 「free を通らない道で `ρ` に届く非 free 頂点」の個数）。
  第12夜は**紙**で証明し、46,287 行の DAG 全数・220 万本の最適スケジュール枚挙で
  反例が出ないことを実測したが、機械証明は無かった。ここを埋める。

  ## 模型（`scripts/revpebble.py` の docstring が正本）

  clean reversible pebbling。1 手 = 頂点 `u ∉ F` の toggle。可能条件は
  「`u` のすべての先行点 `c` がペブル済みまたは free」（置く・取るの両向きで同じ）。
  初期 `∅`、終端 `{ρ}`、常に `|C t| ≤ p`。

  ⚠ 実装は手の可能条件を**直前**の配置で判定する。ここでも `Sched.legal` は `C t`
  （第 `t+1` 手の直前）で述べる。紙 §1 の但し書きと同じ。

  ## 設計（紙との対応）

  * 配置は `C : ℕ → Finset ℕ`、第 `t+1` 手で toggle する頂点は `mv t`。
  * `cnt mv v t` = 時刻 `t` までに `v` を toggle した回数。**全部の要は
    `Sched.mem_iff_odd_cnt`**（`v ∈ C t ↔ Odd (cnt mv v t)`）で、
    紙の (2b)(2c) はここから出る。
  * `Occ mv M v` = `v` を toggle した時刻の集合（紙の `{θ_v^1,…,θ_v^{t_v}}`）。
    `fstOcc`/`lstOcc` がその min/max ＝ 紙の殻 `H_v = [θ_v^1, θ_v^{t_v}]` の両端。
  * 紙の `V`（free を通らない道で `ρ` に届く非 free 頂点）は帰納的述語 `Reach`。
    **こう定義したので前提 (A)（free は source）は要らない**（紙 §1 の ★ と同じ）。
    ⚠ `dag_bound.py` の `N`（祖先閉包 − free）とは一般には違う。free が source の
    ときだけ一致する（紙 §3 の脚注に、取り違えると偽になる実例がある）。

  ## 何が証明できていて何ができていないか

  ファイル末尾の `#print axioms HullLemma.Sched.card_le_of_reach` を見ること。
  `sorryAx` が出ている間は**層を上げてはいけない**。
  ⚠ この模型が `revpebble.py` と同じゲームであることは Lean の中では保証されない。
  対応は `HullLemmaCalib.lean` の `#eval` 校正で見る。
-/
import Mathlib

-- ⚠ `lake` を使わず `lean` を直接呼ぶので lakefile.toml の `relaxedAutoImplicit = false` が
--   効かない。切っておかないと、綴り間違いが「未知の暗黙変数」として黙って通る。
set_option autoImplicit false

namespace HullLemma

open Finset

/-! ## 1. 模型 -/

/-- 1 手 = 1 頂点の toggle。 -/
def toggleAt (S : Finset ℕ) (u : ℕ) : Finset ℕ :=
  if u ∈ S then S.erase u else insert u S

/-- clean reversible pebbling のスケジュール。

`C t` は第 `t` 手**直後**の配置（`C 0 = ∅`）。第 `t+1` 手は `mv t` を toggle する。 -/
structure Sched (pred : ℕ → Finset ℕ) (F : Finset ℕ) (ρ p M : ℕ)
    (C : ℕ → Finset ℕ) (mv : ℕ → ℕ) : Prop where
  /-- 初期配置は空。 -/
  start : C 0 = ∅
  /-- 終端は目標のみ（clean）。 -/
  finish : C M = {ρ}
  /-- toggle する頂点は free でない。 -/
  notFree : ∀ t, t < M → mv t ∉ F
  /-- 1 手の遷移。 -/
  step : ∀ t, t < M → C (t + 1) = toggleAt (C t) (mv t)
  /-- 可能条件: 先行点はペブル済みか free（**直前**の配置で判定）。 -/
  legal : ∀ t, t < M → ∀ c ∈ pred (mv t), c ∈ C t ∨ c ∈ F
  /-- ピーク制約。 -/
  peak : ∀ t, t ≤ M → (C t).card ≤ p

/-- 時刻 `t` までに `v` を toggle した回数。 -/
def cnt (mv : ℕ → ℕ) (v t : ℕ) : ℕ := ∑ s ∈ range t, if mv s = v then 1 else 0

/-- `v` を toggle した時刻の全体。紙の `{θ_v^1, …, θ_v^{t_v}}`。 -/
def Occ (mv : ℕ → ℕ) (M v : ℕ) : Finset ℕ := (range M).filter (fun s => mv s = v)

/-- 紙の `θ_v^1`（最初の toggle 時刻）。`Occ` が空なら `0`（使わない）。 -/
noncomputable def fstOcc (mv : ℕ → ℕ) (M v : ℕ) : ℕ :=
  if h : (Occ mv M v).Nonempty then (Occ mv M v).min' h else 0

/-- 紙の `θ_v^{t_v}`（最後の toggle 時刻）。`Occ` が空なら `0`（使わない）。 -/
noncomputable def lstOcc (mv : ℕ → ℕ) (M v : ℕ) : ℕ :=
  if h : (Occ mv M v).Nonempty then (Occ mv M v).max' h else 0

/-- 紙の `V`: `ρ` へ **free を通らない道**で届く非 free 頂点。 -/
inductive Reach (pred : ℕ → Finset ℕ) (F : Finset ℕ) (ρ : ℕ) : ℕ → Prop
  | root : Reach pred F ρ ρ
  | step {u c : ℕ} : Reach pred F ρ u → c ∈ pred u → c ∉ F → Reach pred F ρ c

/-- 紙の「1 回組」（`k_v = 1`）。非根は 2 回、根は 1 回 toggle される。 -/
def OnceClass (mv : ℕ → ℕ) (M ρ v : ℕ) : Prop :=
  (Occ mv M v).card = if v = ρ then 1 else 2

instance (mv : ℕ → ℕ) (M ρ v : ℕ) : Decidable (OnceClass mv M ρ v) := by
  unfold OnceClass; infer_instance

/-! ## 2. `cnt` と `Occ` の基本性質（模型に依らない） -/

variable {mv : ℕ → ℕ} {M v c u t : ℕ}

theorem mem_occ_iff : t ∈ Occ mv M v ↔ t < M ∧ mv t = v := by
  simp [Occ, mem_filter, mem_range]

/-- `cnt` は「`t` より前の toggle 時刻」の個数でもある。 -/
theorem cnt_eq_card : cnt mv v t = ((range t).filter (fun s => mv s = v)).card :=
  (Finset.card_filter _ _).symm

theorem cnt_zero : cnt mv v 0 = 0 := by simp [cnt]

theorem cnt_succ (mv : ℕ → ℕ) (v t : ℕ) :
    cnt mv v (t + 1) = cnt mv v t + (if mv t = v then 1 else 0) :=
  Finset.sum_range_succ _ t

/-- toggle が起きない区間では `cnt` は動かない。紙の L3 の骨。 -/
theorem cnt_eq_of_no_toggle {N : ℕ} (hab : t ≤ N) (h : ∀ s, t ≤ s → s < N → mv s ≠ v) :
    cnt mv v N = cnt mv v t := by
  induction N with
  | zero =>
      have : t = 0 := Nat.le_zero.mp hab
      subst this; rfl
  | succ n ih =>
      rcases Nat.lt_or_ge n t with hn | hn
      · have : t = n + 1 := by omega
        subst this; rfl
      · rw [cnt_succ, if_neg (h n hn (by omega)), Nat.add_zero]
        exact ih hn (fun s hs hsn => h s hs (by omega))

/-- `Occ` の元は `cnt` に効く: 未 toggle なら `cnt = 0`。 -/
theorem cnt_pos_iff : 0 < cnt mv v t ↔ ∃ s < t, mv s = v := by
  rw [cnt_eq_card, card_pos]
  constructor
  · rintro ⟨s, hs⟩
    rw [mem_filter, mem_range] at hs
    exact ⟨s, hs.1, hs.2⟩
  · rintro ⟨s, hst, hsv⟩
    exact ⟨s, by rw [mem_filter, mem_range]; exact ⟨hst, hsv⟩⟩

/-- `t ≤ M` なら「`t` より前の toggle 時刻」は `Occ` の切り取りで数えられる。 -/
theorem cnt_eq_card_filter (h : t ≤ M) :
    cnt mv v t = ((Occ mv M v).filter (fun s => s < t)).card := by
  rw [cnt_eq_card]
  unfold Occ
  congr 1
  ext s
  simp only [mem_filter, mem_range]
  constructor
  · rintro ⟨hs, hv⟩; exact ⟨⟨by omega, hv⟩, hs⟩
  · rintro ⟨⟨_, hv⟩, hs⟩; exact ⟨hs, hv⟩

theorem card_occ_eq_cnt : (Occ mv M v).card = cnt mv v M := cnt_eq_card.symm

theorem fstOcc_mem (h : (Occ mv M v).Nonempty) : fstOcc mv M v ∈ Occ mv M v := by
  rw [fstOcc, dif_pos h]; exact min'_mem _ _

theorem lstOcc_mem (h : (Occ mv M v).Nonempty) : lstOcc mv M v ∈ Occ mv M v := by
  rw [lstOcc, dif_pos h]; exact max'_mem _ _

theorem fstOcc_le (h : (Occ mv M v).Nonempty) (hs : t ∈ Occ mv M v) : fstOcc mv M v ≤ t := by
  rw [fstOcc, dif_pos h]; exact min'_le _ _ hs

theorem le_lstOcc (h : (Occ mv M v).Nonempty) (hs : t ∈ Occ mv M v) : t ≤ lstOcc mv M v := by
  rw [lstOcc, dif_pos h]; exact le_max' _ _ hs

theorem fstOcc_le_lstOcc (h : (Occ mv M v).Nonempty) : fstOcc mv M v ≤ lstOcc mv M v :=
  le_lstOcc h (fstOcc_mem h)

/-! ## 3. パリティ（この形式化の要） -/

namespace Sched

variable {pred : ℕ → Finset ℕ} {F : Finset ℕ} {ρ p : ℕ} {C : ℕ → Finset ℕ}
variable (hS : Sched pred F ρ p M C mv)
include hS

/-- **`v ∈ C t ↔ v を t までに奇数回 toggle した`。**

紙の (2b)(2c) はこの 1 本から出る。 -/
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
          have : Odd (cnt mv (mv n) n) := IH.mp hin
          rw [Nat.odd_add_one]
          simpa using this
        · rw [if_neg hin, mem_insert]
          simp only [true_or, iff_true, true_iff]
          have : ¬ Odd (cnt mv (mv n) n) := fun h => hin (IH.mpr h)
          rw [Nat.odd_add_one]
          exact this
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

/-- (2a) 到達可能な頂点は少なくとも一度 toggle される。 -/
theorem occ_nonempty {v : ℕ} (h : Reach pred F ρ v) : (Occ mv M v).Nonempty := by
  induction h with
  | root =>
      rw [← card_pos, card_occ_eq_cnt]
      by_contra hz
      have h0 : cnt mv ρ M = 0 := by omega
      have : ρ ∈ C M := by rw [hS.finish]; exact mem_singleton_self ρ
      rw [hS.mem_iff_odd_cnt M le_rfl ρ, h0] at this
      simp at this
  | @step u c hu hcu hcF ih =>
      obtain ⟨t, ht⟩ := ih
      rw [mem_occ_iff] at ht
      obtain ⟨htM, htv⟩ := ht
      have hleg := hS.legal t htM c (by rw [htv]; exact hcu)
      have hc : c ∈ C t := hleg.resolve_right hcF
      rw [hS.mem_iff_odd_cnt t (le_of_lt htM) c] at hc
      have : 0 < cnt mv c t := hc.pos
      obtain ⟨s, hst, hsv⟩ := cnt_pos_iff.mp this
      exact ⟨s, by rw [mem_occ_iff]; exact ⟨by omega, hsv⟩⟩

/-- 載っているなら最初の toggle は既に済んでいる。 -/
theorem fstOcc_lt_of_mem {v t : ℕ} (ht : t ≤ M) (hv : v ∈ C t) :
    fstOcc mv M v < t := by
  rw [hS.mem_iff_odd_cnt t ht v] at hv
  obtain ⟨s, hst, hsv⟩ := cnt_pos_iff.mp hv.pos
  have hmem : s ∈ Occ mv M v := by rw [mem_occ_iff]; exact ⟨by omega, hsv⟩
  exact lt_of_le_of_lt (fstOcc_le ⟨s, hmem⟩ hmem) hst

/-- 紙 (2c): `v ≠ ρ` が載っている時刻は殻の内側。 -/
theorem le_lstOcc_of_mem {v t : ℕ} (hne : v ≠ ρ) (ht : t ≤ M) (hv : v ∈ C t) :
    t ≤ lstOcc mv M v := by
  by_contra hlt
  push_neg at hlt
  have hne' : (Occ mv M v).Nonempty := by
    rw [hS.mem_iff_odd_cnt t ht v] at hv
    obtain ⟨s, hst, hsv⟩ := cnt_pos_iff.mp hv.pos
    exact ⟨s, by rw [mem_occ_iff]; exact ⟨by omega, hsv⟩⟩
  have hno : ∀ s, t ≤ s → s < M → mv s ≠ v := by
    intro s hs hsM hsv
    have : s ∈ Occ mv M v := by rw [mem_occ_iff]; exact ⟨hsM, hsv⟩
    have := le_lstOcc hne' this
    omega
  have heq : cnt mv v M = cnt mv v t := cnt_eq_of_no_toggle ht hno
  have hvM : v ∈ C M := by
    rw [hS.mem_iff_odd_cnt M le_rfl v, heq, ← hS.mem_iff_odd_cnt t ht v]
    exact hv
  rw [hS.finish, mem_singleton] at hvM
  exact hne hvM

/-! ## 4. 殻補題 -/

/-- **補題 1（殻補題）.** `c ∈ preds u`、`c ∉ F`、`c ≠ ρ` なら `H u ⊆ H c`。

紙 §3。`c ≠ ρ` は本質的で、緩めてはいけない（`ρ` は `[θ_ρ^{t_ρ}, M]` で載り続けて
殻をはみ出す）。実際には `ρ` が唯一の sink であることから自動的に従う。 -/
theorem shell {u c : ℕ} (hOu : (Occ mv M u).Nonempty)
    (hcu : c ∈ pred u) (hcF : c ∉ F) (hcρ : c ≠ ρ) :
    fstOcc mv M c < fstOcc mv M u ∧ lstOcc mv M u ≤ lstOcc mv M c := by
  constructor
  · have hmem := fstOcc_mem hOu
    rw [mem_occ_iff] at hmem
    obtain ⟨hlt, hmv⟩ := hmem
    have hleg := hS.legal _ hlt c (by rw [hmv]; exact hcu)
    exact hS.fstOcc_lt_of_mem (le_of_lt hlt) (hleg.resolve_right hcF)
  · have hmem := lstOcc_mem hOu
    rw [mem_occ_iff] at hmem
    obtain ⟨hlt, hmv⟩ := hmem
    have hleg := hS.legal _ hlt c (by rw [hmv]; exact hcu)
    exact hS.le_lstOcc_of_mem hcρ (le_of_lt hlt) (hleg.resolve_right hcF)

/-- **系 2.** 全ての到達可能な `v` で `H ρ ⊆ H v`。

`hSink`（`ρ` は出辺を持たない＝唯一の sink）が要る。 -/
theorem shell_root (hSink : ∀ w, ρ ∉ pred w) {v : ℕ} (h : Reach pred F ρ v) :
    fstOcc mv M v ≤ fstOcc mv M ρ ∧ lstOcc mv M ρ ≤ lstOcc mv M v := by
  induction h with
  | root => exact ⟨le_rfl, le_rfl⟩
  | @step u c hu hcu hcF ih =>
      have hcρ : c ≠ ρ := fun he => hSink u (he ▸ hcu)
      have := hS.shell (hS.occ_nonempty hu) hcu hcF hcρ
      exact ⟨le_trans (le_of_lt this.1) ih.1, le_trans ih.2 this.2⟩

/-! ## 5. 定理 3（(H)）と系 4（P1） -/

/-- 紙の `T := θ_ρ^{t_ρ}`（目標を**最後に**置いた時刻）。 -/
noncomputable def target (_ : Sched pred F ρ p M C mv) : ℕ := lstOcc mv M ρ

theorem target_lt : hS.target < M := by
  have h := lstOcc_mem (hS.occ_nonempty Reach.root)
  rw [mem_occ_iff] at h
  exact h.1

/-- **定理 3 ((H)).** 1 回組の頂点は、目標を最後に置いた瞬間 `T` にすべて載っている。 -/
theorem once_at_target (hSink : ∀ w, ρ ∉ pred w) {v : ℕ}
    (hv : Reach pred F ρ v) (hOnce : OnceClass mv M ρ v) :
    v ∈ C (hS.target + 1) := by
  have hTM : hS.target < M := hS.target_lt
  have hOρ : (Occ mv M ρ).Nonempty := hS.occ_nonempty Reach.root
  have hOv : (Occ mv M v).Nonempty := hS.occ_nonempty hv
  rw [hS.mem_iff_odd_cnt _ (by omega) v,
      cnt_eq_card_filter (by omega : hS.target + 1 ≤ M)]
  by_cases hvρ : v = ρ
  · -- `ρ` は `T` に置かれる。`T` は `Occ ρ` の最大元なので、`< T+1` の切り取りは全体。
    subst hvρ
    have : (Occ mv M v).filter (fun s => s < hS.target + 1) = Occ mv M v := by
      apply filter_true_of_mem
      intro s hs
      have := le_lstOcc hOv hs
      unfold Sched.target
      omega
    rw [this]
    unfold OnceClass at hOnce
    rw [if_pos rfl] at hOnce
    rw [hOnce]
    exact ⟨0, rfl⟩
  · -- `v ≠ ρ`: `Occ v = {fstOcc v, lstOcc v}` で `fstOcc v ≤ T < lstOcc v`。
    unfold OnceClass at hOnce
    rw [if_neg hvρ] at hOnce
    have hpair : Occ mv M v = {fstOcc mv M v, lstOcc mv M v} := by
      have hsub : ({fstOcc mv M v, lstOcc mv M v} : Finset ℕ) ⊆ Occ mv M v := by
        intro x hx
        rcases mem_insert.mp hx with h | h
        · exact h ▸ fstOcc_mem hOv
        · rw [mem_singleton] at h; exact h ▸ lstOcc_mem hOv
      have hne : fstOcc mv M v ≠ lstOcc mv M v := by
        intro he
        have : Occ mv M v ⊆ {fstOcc mv M v} := by
          intro x hx
          rw [mem_singleton]
          have h1 := fstOcc_le hOv hx
          have h2 := le_lstOcc hOv hx
          omega
        have := card_le_card this
        rw [hOnce, card_singleton] at this
        omega
      exact (eq_of_subset_of_card_le hsub
        (by rw [hOnce, card_insert_of_notMem (by simpa)]; simp)).symm
    -- 殻補題（系 2）から `fstOcc v ≤ fstOcc ρ ≤ T ≤ lstOcc v`
    obtain ⟨hf, hl⟩ := hS.shell_root hSink hv
    have hfρ : fstOcc mv M ρ ≤ lstOcc mv M ρ := fstOcc_le_lstOcc hOρ
    -- `lstOcc v ≠ T`（同じ時刻の手は 1 頂点だけ）
    have hlne : lstOcc mv M v ≠ hS.target := by
      intro he
      have h1 := lstOcc_mem hOv
      have h2 := lstOcc_mem hOρ
      rw [mem_occ_iff] at h1 h2
      exact hvρ (by rw [← h1.2, he]; unfold Sched.target; exact h2.2)
    have hT1 : fstOcc mv M v ≤ hS.target := by unfold Sched.target at *; omega
    have hT2 : hS.target < lstOcc mv M v := by unfold Sched.target at *; omega
    rw [hpair]
    have : ({fstOcc mv M v, lstOcc mv M v} : Finset ℕ).filter (fun s => s < hS.target + 1)
        = {fstOcc mv M v} := by
      rw [filter_insert, if_pos (by omega), filter_singleton, if_neg (by omega)]
      rfl
    rw [this, card_singleton]
    exact ⟨0, rfl⟩

/-- **系 4 の `(β)`**: 1 回組の個数 `r` は `p` 以下。紙 §7.5 が「既知の最適解 5 本すべてで
等号」と実測した不等式。 -/
theorem once_card_le_peak (hSink : ∀ w, ρ ∉ pred w) (V : Finset ℕ)
    (hV : ∀ w, w ∈ V → Reach pred F ρ w) :
    (V.filter (OnceClass mv M ρ)).card ≤ p := by
  have hsub : V.filter (OnceClass mv M ρ) ⊆ C (hS.target + 1) := by
    intro w hw
    rw [mem_filter] at hw
    exact hS.once_at_target hSink (hV w hw.1) hw.2
  exact le_trans (card_le_card hsub) (hS.peak _ (by have := hS.target_lt; omega))

/-! ## 6. 個数勘定（紙 (2b) と系 4 の `(α)`） -/

/-- 非根は偶数回 toggle される（∅ に始まり ∅ に終わる）。 -/
theorem card_occ_even {v : ℕ} (hne : v ≠ ρ) : Even (Occ mv M v).card := by
  rcases Nat.even_or_odd (Occ mv M v).card with h | h
  · exact h
  · exfalso
    rw [card_occ_eq_cnt] at h
    have : v ∈ C M := (hS.mem_iff_odd_cnt M le_rfl v).mpr h
    rw [hS.finish, mem_singleton] at this
    exact hne this

/-- 根は奇数回 toggle される（∅ に始まり `{ρ}` に終わる）。 -/
theorem card_occ_odd_root : Odd (Occ mv M ρ).card := by
  rw [card_occ_eq_cnt, ← hS.mem_iff_odd_cnt M le_rfl ρ, hS.finish]
  exact mem_singleton_self ρ

/-- 1 回組でない頂点は `4` 回以上（非根）／`3` 回以上（根）toggle される。 -/
theorem card_occ_ge {v : ℕ} (hv : Reach pred F ρ v) :
    (if v = ρ then 3 else 4)
      ≤ (Occ mv M v).card + 2 * (if OnceClass mv M ρ v then 1 else 0) := by
  have hpos : 0 < (Occ mv M v).card := card_pos.mpr (hS.occ_nonempty hv)
  by_cases hoc : OnceClass mv M ρ v
  · -- 1 回組: 根なら 1+2 = 3、非根なら 2+2 = 4
    rw [if_pos hoc]
    unfold OnceClass at hoc
    by_cases hvρ : v = ρ
    · rw [if_pos hvρ] at hoc ⊢; omega
    · rw [if_neg hvρ] at hoc ⊢; omega
  · -- 1 回組でない: 根は奇数かつ ≠1 で 3 以上、非根は偶数かつ ≠2 で 4 以上
    rw [if_neg hoc, Nat.mul_zero, Nat.add_zero]
    by_cases hvρ : v = ρ
    · rw [if_pos hvρ]
      have hodd : Odd (Occ mv M v).card := by rw [hvρ]; exact hS.card_occ_odd_root
      have hne1 : (Occ mv M v).card ≠ 1 := fun h =>
        hoc (by unfold OnceClass; rw [if_pos hvρ]; exact h)
      obtain ⟨k, hk⟩ := hodd; omega
    · rw [if_neg hvρ]
      have heven : Even (Occ mv M v).card := hS.card_occ_even hvρ
      have hne2 : (Occ mv M v).card ≠ 2 := fun h =>
        hoc (by unfold OnceClass; rw [if_neg hvρ]; exact h)
      obtain ⟨k, hk⟩ := heven; omega

/-- 手数は各頂点の toggle 回数の総和（祖先制限された `V` の上で）。紙 (2b)。 -/
theorem sum_card_occ (V : Finset ℕ) (hmv : ∀ t, t < M → mv t ∈ V) :
    ∑ v ∈ V, (Occ mv M v).card = M := by
  have : ∑ v ∈ V, (Occ mv M v).card = (range M).card := by
    rw [card_eq_sum_card_fiberwise (f := mv) (t := V)
      (fun x hx => hmv x (mem_range.mp hx))]
    rfl
  rw [this, card_range]

/-- **系 4 (P1).** `4N ≤ M + 2·min(p, N) + 1`、すなわち `M ≥ 4N − 2·min(p,N) − 1`。 -/
theorem card_le_of_reach (hSink : ∀ w, ρ ∉ pred w) (V : Finset ℕ)
    (hV : ∀ w, w ∈ V → Reach pred F ρ w) (hρ : ρ ∈ V)
    (hmv : ∀ t, t < M → mv t ∈ V) :
    4 * V.card ≤ M + 2 * min p V.card + 1 := by
  classical
  set R := V.filter (OnceClass mv M ρ) with hR
  set r := R.card with hr
  have hrp : r ≤ p := hS.once_card_le_peak hSink V hV
  have hrN : r ≤ V.card := card_le_card (filter_subset _ _)
  -- 各頂点の寄与
  have hcontrib : ∀ v ∈ V,
      (if v = ρ then 3 else 4) ≤ (Occ mv M v).card + 2 * (if OnceClass mv M ρ v then 1 else 0) :=
    fun v hv => hS.card_occ_ge (hV v hv)
  have hsum : ∑ v ∈ V, (if v = ρ then (3:ℕ) else 4)
      ≤ ∑ v ∈ V, ((Occ mv M v).card + 2 * (if OnceClass mv M ρ v then 1 else 0)) :=
    Finset.sum_le_sum hcontrib
  -- 左辺 = 4N − 1
  have hlhs : ∑ v ∈ V, (if v = ρ then (3:ℕ) else 4) + 1 = 4 * V.card := by
    rw [← Finset.sum_erase_add V _ hρ, if_pos rfl]
    have : ∑ v ∈ V.erase ρ, (if v = ρ then (3:ℕ) else 4) = 4 * (V.erase ρ).card := by
      rw [Finset.sum_congr rfl (fun x hx => if_neg (ne_of_mem_erase hx))]
      simp [Nat.mul_comm]
    rw [this, card_erase_of_mem hρ]
    have : 1 ≤ V.card := card_pos.mpr ⟨ρ, hρ⟩
    omega
  -- 右辺 = M + 2r
  have hrhs : ∑ v ∈ V, ((Occ mv M v).card + 2 * (if OnceClass mv M ρ v then 1 else 0))
      = M + 2 * r := by
    rw [Finset.sum_add_distrib, hS.sum_card_occ V hmv, ← Finset.mul_sum]
    congr 1
    congr 1
    rw [hr, hR, card_filter]
  rw [hrhs] at hsum
  have hmin : r ≤ min p V.card := le_min hrp hrN
  omega

end Sched

/-! ## 7. 公理検査（`sorryAx` が出ていないことをここで見る） -/

section Audit
open Sched
-- ⚠ **緑の根拠はここ。** 期待は 3 本とも
--   `[propext, Classical.choice, Quot.sound]` のみ（mathlib の標準 3 公理）。
--   `sorryAx` が 1 つでも出たら、その定理は**証明されていない**。
#print axioms HullLemma.Sched.shell
#print axioms HullLemma.Sched.once_at_target
#print axioms HullLemma.Sched.card_le_of_reach
end Audit

end HullLemma
