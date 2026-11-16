/-
  **等号構造補題（§7.1 item 5）の Lean 形式化**（第29夜・2026-08-24）。

  紙は `autoresearch/results/night24_oneshot_verdict.md` §7.1。one-shot 符号化
  （v1/v2/v3）の無条件性はこの補題**だけ**に依っており、Lean にあったのは
  **不等式の側（item 4）＝ `HullLemma.Sched.card_le_of_reach`** だけだった。

  第28夜（`tools/night27r3_excess_support.py --strict`）の実測:
  $\tau_{\text{真}}(6)=13$ を支える 5 点のうち $p=11,12$ の 2 点は
  **この補題だけに乗っている**（しかも $L$ との差が +2 しかなく、いちばん脆い）。
  ⇒ **紙のうち Lean に入れる価値がいちばん高いのがここ**、というのが第28夜の結論。

  ## 何を証明するか（紙の item 5 そのもの）

  `M = 4N − 2p − 1`（＝ `L`。等号ケース）なら:

  1. **根はちょうど 1 回** toggle される（`k_ρ = 1`）。
  2. **1 回組はちょうど `p` 個**で、しかもその全体は
     **根を最後に置いた直後の配置 `C (T+1)` そのもの**（＝ピークをちょうど使い切る）。
  3. **1 回組でない非根はちょうど 4 回** toggle される（`m_v = 2`）。
  4. その個数は **ちょうど `N − p`**。

  紙が「$t^*$ に生きている非根が $p-1$ 個」と書いているのは、上の 2 で
  **根自身が 1 枠を占める**（`root_at_target`）ことによる。**紙で暗黙だった
  この一段が、Lean では独立の補題として要った**（`root_at_target`）。

  ## 副産物（item 4 の括弧）

  `card_le_of_root_not_once`: 根が 1 回でないなら `4N + 1 ≤ M + 2p`
  （＝ `M ≥ L + 2`）。`HullLemma` の `card_le_of_reach` は `M ≥ L` までしか言わない。

  ## ⚠ ここで閉じていないもの

  * 「CNF の UNSAT ⟹ $M^*$ の下界」は**符号化の完全性**が別に要る（第26夜）。
    この補題は**その一段目**であって、one-shot の無条件化そのものではない。
  * この模型が `revpebble.py` と同じゲームであることは Lean の中では保証されない
    （`HullLemmaCBTWitness` の証人と `HullEqWitness.lean` の照合で見る）。
  * **空虚でないことは型検査では分からない**（第16夜 周2/3 の M4）。証人は
    `HullEqWitness.lean`（$T_3$・$p=5$・17 手＝**等号ケースの実物**）。
-/
import HullLemmaCBT

set_option autoImplicit false
set_option maxRecDepth 4000

-- ⚠ 一般の補題は **`HullLemma.Sched` 名前空間に置く**。ここに置かないと
--   `hS.root_at_target` のドット記法が引けない（型は `HullLemma.Sched` なので、
--   Lean は `HullLemma.Sched.root_at_target` を探しにいく）。
namespace HullLemma

namespace Sched

open Finset

variable {pred : ℕ → Finset ℕ} {F : Finset ℕ} {ρ p M : ℕ} {C : ℕ → Finset ℕ} {mv : ℕ → ℕ}

/-! ## 1. 根は `T+1` に載っている（紙で暗黙だった一段） -/

/-- **根は最後の toggle の直後に載っている。**

紙 §7.1 の「$t^*$ に生きている非根は $\le p-1$ 個」は、この 1 本
（＝根自身がピークの 1 枠を食う）から出る。 -/
theorem root_at_target (hS : Sched pred F ρ p M C mv) : ρ ∈ C (hS.target + 1) := by
  have hTM : hS.target < M := hS.target_lt
  have hOρ : (Occ mv M ρ).Nonempty := hS.occ_nonempty Reach.root
  -- `target` は `Occ ρ` の最大元なので、それ以後に `ρ` の toggle は無い。
  have hno : ∀ s, hS.target + 1 ≤ s → s < M → mv s ≠ ρ := by
    intro s hs hsM hsv
    have hmem : s ∈ Occ mv M ρ := by rw [mem_occ_iff]; exact ⟨hsM, hsv⟩
    have := le_lstOcc hOρ hmem
    unfold Sched.target at hs
    omega
  have heq : cnt mv ρ M = cnt mv ρ (hS.target + 1) :=
    cnt_eq_of_no_toggle (by omega) hno
  have hodd : Odd (cnt mv ρ M) := by
    have h := hS.card_occ_odd_root
    rwa [card_occ_eq_cnt] at h
  rw [hS.mem_iff_odd_cnt _ (by omega) ρ, ← heq]
  exact hodd

/-- 1 回組の全体は `T+1` の配置に含まれる（根を明示的に足しても崩れない）。 -/
theorem insert_root_once_subset (hS : Sched pred F ρ p M C mv) (hSink : ∀ w, ρ ∉ pred w)
    (V : Finset ℕ) (hV : ∀ w, w ∈ V → Reach pred F ρ w) :
    insert ρ (V.filter (OnceClass mv M ρ)) ⊆ C (hS.target + 1) := by
  intro w hw
  rcases mem_insert.mp hw with he | hw'
  · exact he ▸ hS.root_at_target
  · rw [mem_filter] at hw'
    exact hS.once_at_target hSink (hV w hw'.1) hw'.2

/-- **根が 1 回組でないなら、1 回組は `p−1` 個以下。**

`HullLemma.Sched.once_card_le_peak`（`≤ p`）の強化。根が枠を 1 つ食うので。 -/
theorem once_card_lt_peak (hS : Sched pred F ρ p M C mv) (hSink : ∀ w, ρ ∉ pred w)
    (V : Finset ℕ) (hV : ∀ w, w ∈ V → Reach pred F ρ w)
    (hnot : ¬ OnceClass mv M ρ ρ) :
    (V.filter (OnceClass mv M ρ)).card + 1 ≤ p := by
  classical
  have hρR : ρ ∉ V.filter (OnceClass mv M ρ) := by
    intro h; exact hnot (mem_filter.mp h).2
  have hsub := hS.insert_root_once_subset hSink V hV
  have hcard := card_le_card hsub
  rw [card_insert_of_notMem hρR] at hcard
  exact le_trans hcard (hS.peak _ (by have := hS.target_lt; omega))

/-! ## 2. 個数勘定の 2 本（`card_le_of_reach` の中の `have` を外に出したもの） -/

/-- 左辺 `∑ (3 or 4) + 1 = 4N`。 -/
theorem sum_weight (V : Finset ℕ) (hρ : ρ ∈ V) :
    (∑ v ∈ V, (if v = ρ then (3:ℕ) else 4)) + 1 = 4 * V.card := by
  rw [← Finset.sum_erase_add V _ hρ, if_pos rfl]
  have hsum : ∑ v ∈ V.erase ρ, (if v = ρ then (3:ℕ) else 4) = 4 * (V.erase ρ).card := by
    rw [Finset.sum_congr rfl (fun x hx => if_neg (ne_of_mem_erase hx))]
    simp [Nat.mul_comm]
  rw [hsum, card_erase_of_mem hρ]
  have : 1 ≤ V.card := card_pos.mpr ⟨ρ, hρ⟩
  omega

/-- 右辺 `∑ (|Occ v| + 2·[1 回組]) = M + 2r`。 -/
theorem sum_occ (hS : Sched pred F ρ p M C mv) (V : Finset ℕ)
    (hmv : ∀ t, t < M → mv t ∈ V) :
    (∑ v ∈ V, ((Occ mv M v).card + 2 * (if OnceClass mv M ρ v then 1 else 0)))
      = M + 2 * (V.filter (OnceClass mv M ρ)).card := by
  classical
  rw [Finset.sum_add_distrib, hS.sum_card_occ V hmv, ← Finset.mul_sum]
  congr 1
  congr 1
  rw [card_filter]

/-- **鍵の不等式**: `4N ≤ M + 2r + 1`（`r` = 1 回組の個数）。

`card_le_of_reach` は最後に `r ≤ min p N` を掛けて `p` にするが、
等号解析では `r` のまま持っておく必要がある。 -/
theorem key_le (hS : Sched pred F ρ p M C mv) (V : Finset ℕ)
    (hV : ∀ w, w ∈ V → Reach pred F ρ w) (hρ : ρ ∈ V)
    (hmv : ∀ t, t < M → mv t ∈ V) :
    4 * V.card ≤ M + 2 * (V.filter (OnceClass mv M ρ)).card + 1 := by
  classical
  have hcontrib : ∀ v ∈ V,
      (if v = ρ then (3:ℕ) else 4)
        ≤ (Occ mv M v).card + 2 * (if OnceClass mv M ρ v then 1 else 0) :=
    fun v hv => hS.card_occ_ge (hV v hv)
  have hle := Finset.sum_le_sum hcontrib
  have hF := sum_weight (ρ := ρ) V hρ
  have hG := hS.sum_occ V hmv
  omega

/-- **系（item 4 の括弧）**: 根が 1 回組でないなら `4N + 1 ≤ M + 2p`（＝ `M ≥ L + 2`）。 -/
theorem card_le_of_root_not_once (hS : Sched pred F ρ p M C mv) (hSink : ∀ w, ρ ∉ pred w)
    (V : Finset ℕ) (hV : ∀ w, w ∈ V → Reach pred F ρ w) (hρ : ρ ∈ V)
    (hmv : ∀ t, t < M → mv t ∈ V) (hnot : ¬ OnceClass mv M ρ ρ) :
    4 * V.card + 1 ≤ M + 2 * p := by
  have hkey := hS.key_le V hV hρ hmv
  have hlt := hS.once_card_lt_peak hSink V hV hnot
  omega

/-! ## 3. 等号構造補題（§7.1 item 5） -/

/-- **等号構造補題.** `M + 2p + 1 = 4N`（＝ `M = L`）なら:

1. 根はちょうど 1 回 toggle される、
2. 1 回組の全体は `C (T+1)` そのもの（ピークをちょうど使い切る）、
3. その個数はちょうど `p`、
4. 1 回組でない非根はちょうど 4 回 toggle される、
5. その個数はちょうど `N − p`。 -/
theorem eq_structure (hS : Sched pred F ρ p M C mv) (hSink : ∀ w, ρ ∉ pred w)
    (V : Finset ℕ) (hV : ∀ w, w ∈ V → Reach pred F ρ w) (hρ : ρ ∈ V)
    (hmv : ∀ t, t < M → mv t ∈ V)
    (hM : M + 2 * p + 1 = 4 * V.card) :
    (Occ mv M ρ).card = 1
      ∧ V.filter (OnceClass mv M ρ) = C (hS.target + 1)
      ∧ (V.filter (OnceClass mv M ρ)).card = p
      ∧ (∀ v ∈ V, v ≠ ρ → ¬ OnceClass mv M ρ v → (Occ mv M v).card = 4)
      ∧ (V.filter (fun v => ¬ OnceClass mv M ρ v)).card + p = V.card := by
  classical
  -- (0) `p ≥ 1`（終端が `{ρ}` なのでピークは 1 以上）
  have hp1 : 1 ≤ p := by
    have h := hS.peak M le_rfl
    rw [hS.finish] at h
    simpa using h
  -- (1) 根は 1 回組（そうでなければ `M ≥ L + 2` で仮定に反する）
  have hρonce : OnceClass mv M ρ ρ := by
    by_contra hno
    have := hS.card_le_of_root_not_once hSink V hV hρ hmv hno
    omega
  have hroot : (Occ mv M ρ).card = 1 := by
    have h := hρonce
    unfold OnceClass at h
    rwa [if_pos rfl] at h
  -- (2) `r = p`
  have hrp : (V.filter (OnceClass mv M ρ)).card ≤ p := hS.once_card_le_peak hSink V hV
  have hkey := hS.key_le V hV hρ hmv
  have hr : (V.filter (OnceClass mv M ρ)).card = p := by omega
  -- (3) 和が等号 ⇒ 各頂点で等号
  have hcontrib : ∀ v ∈ V,
      (if v = ρ then (3:ℕ) else 4)
        ≤ (Occ mv M v).card + 2 * (if OnceClass mv M ρ v then 1 else 0) :=
    fun v hv => hS.card_occ_ge (hV v hv)
  have hF := sum_weight (ρ := ρ) V hρ
  have hG := hS.sum_occ V hmv
  have hsumeq : (∑ v ∈ V, (if v = ρ then (3:ℕ) else 4))
      = ∑ v ∈ V, ((Occ mv M v).card + 2 * (if OnceClass mv M ρ v then 1 else 0)) := by
    omega
  have hpt := (Finset.sum_eq_sum_iff_of_le hcontrib).mp hsumeq
  -- (4) 1 回組でない非根は 4 回ちょうど
  have hfour : ∀ v ∈ V, v ≠ ρ → ¬ OnceClass mv M ρ v → (Occ mv M v).card = 4 := by
    intro v hv hne hnot
    have h := hpt v hv
    rw [if_neg hne, if_neg hnot] at h
    omega
  -- (5) 1 回組の全体 = `C (T+1)`
  have hsub : V.filter (OnceClass mv M ρ) ⊆ C (hS.target + 1) := by
    intro w hw
    rw [mem_filter] at hw
    exact hS.once_at_target hSink (hV w hw.1) hw.2
  have hCcard : (C (hS.target + 1)).card ≤ p :=
    hS.peak _ (by have := hS.target_lt; omega)
  have hset : V.filter (OnceClass mv M ρ) = C (hS.target + 1) :=
    eq_of_subset_of_card_le hsub (by omega)
  -- (6) 1 回組でないものの個数
  have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
    (s := V) (p := OnceClass mv M ρ)
  exact ⟨hroot, hset, hr, hfour, by omega⟩

end Sched

end HullLemma

/-! ## 4. 完全二分木への具体化 -/

namespace HullEq

open Finset HullLemma HullLemmaCBT

variable {p M : ℕ} {C : ℕ → Finset ℕ} {mv : ℕ → ℕ}

/-- **`T_h` の等号構造補題.** `M + 2p + 1 = 4(2^h − 1)` なら §7.1 item 5 が成り立つ。

`hmv`（手はすべて内部頂点）は `cbt_bound` と同じ理由で仮定に残す
（`HullLemmaCBT.lean` 冒頭の ⚠）。 -/
theorem cbt_eq_structure {h : ℕ} (hh : 1 ≤ h)
    (hS : Sched (cbtPred h) (cbtFree h) 1 p M C mv)
    (hmv : ∀ t, t < M → mv t ∈ cbtV h)
    (hM : M + 2 * p + 1 = 4 * (2 ^ h - 1)) :
    (Occ mv M 1).card = 1
      ∧ (cbtV h).filter (OnceClass mv M 1) = C (hS.target + 1)
      ∧ ((cbtV h).filter (OnceClass mv M 1)).card = p
      ∧ (∀ v ∈ cbtV h, v ≠ 1 → ¬ OnceClass mv M 1 v → (Occ mv M v).card = 4)
      ∧ ((cbtV h).filter (fun v => ¬ OnceClass mv M 1 v)).card + p = 2 ^ h - 1 := by
  have hN := cbtV_card h
  have hres := hS.eq_structure (cbt_sink h) (cbtV h) (cbt_reach h) (cbt_root_mem h hh) hmv
    (by rw [hN]; exact hM)
  rw [hN] at hres
  exact hres

/-- **`h = 6`, `p = 13` の等号ケース**（manifest 行11 の `M = 225 = L(63,13)`）。

225 手の `T_6` のスケジュールは、**根を 1 回しか置かず**、
**根の最終配置の瞬間にちょうど 13 個（＝ピーク一杯）が載っており**、
**残り 50 個は 4 回ずつ** toggle される。 -/
theorem cbt_h6_p13_structure
    (hS : Sched (cbtPred 6) (cbtFree 6) 1 12 227 C mv)
    (hmv : ∀ t, t < 227 → mv t ∈ cbtV 6) :
    (Occ mv 227 1).card = 1
      ∧ ((cbtV 6).filter (OnceClass mv 227 1)).card = 12
      ∧ ((cbtV 6).filter (fun v => ¬ OnceClass mv 227 1 v)).card = 51 := by
  have hres := cbt_eq_structure (h := 6) (p := 12) (M := 227) (by norm_num) hS hmv (by norm_num)
  obtain ⟨h1, _, h3, _, h5⟩ := hres
  refine ⟨h1, h3, ?_⟩
  simp only [show (2:ℕ) ^ 6 - 1 = 63 from by norm_num] at h5
  omega

/-- **`h = 6`, `p = 11` で根が 1 回でないなら `M ≥ 231`**（`L(63,11) = 229`）。

one-shot v2/v3 が $p=11$ で潰しているのは「根 1 回・$p-1$ 個が 1 回置き・
残りが 2 回置き」という**等号構造を持つ解**だけである。それ以外の解が
`L` を 2 以上超えることは、この系が**機械証明で**与える。 -/
theorem cbt_h6_p11_root_not_once
    (hS : Sched (cbtPred 6) (cbtFree 6) 1 11 M C mv)
    (hmv : ∀ t, t < M → mv t ∈ cbtV 6)
    (hnot : ¬ OnceClass mv M 1 1) : 231 ≤ M := by
  have h := hS.card_le_of_root_not_once (cbt_sink 6) (cbtV 6) (cbt_reach 6)
    (cbt_root_mem 6 (by norm_num)) hmv hnot
  rw [cbtV_card 6] at h
  simp only [show (2:ℕ) ^ 6 - 1 = 63 from by norm_num] at h
  omega

/-! ## 5. 公理検査（`sorryAx` が出ていないことをここで見る）  GATE-OK: 言及のみ。このファイルに未証明の穴は 1 つも無く、末尾 7 行の `#print axioms` が標準 3 公理ちょうどであることが根拠（`logs/night29_hulleq.status`） -/

section Audit
-- ⚠ **緑の根拠はここ。** 期待は全部 `[propext, Classical.choice, Quot.sound]` のみ。
#print axioms HullLemma.Sched.root_at_target
#print axioms HullLemma.Sched.once_card_lt_peak
#print axioms HullLemma.Sched.card_le_of_root_not_once
#print axioms HullLemma.Sched.eq_structure
#print axioms HullEq.cbt_eq_structure
#print axioms HullEq.cbt_h6_p13_structure
#print axioms HullEq.cbt_h6_p11_root_not_once
end Audit

end HullEq
