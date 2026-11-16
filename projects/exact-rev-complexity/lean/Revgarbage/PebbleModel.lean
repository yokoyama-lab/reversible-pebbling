/-
# 消去ペブリングのモデルと、定理 B2 の上界方向

`data/conj_g_proof_attempt.md` §1・§7.2 の機械証明。
`Revgarbage.PebbleDP`（解体順序 DP と補題 A♮・B♮）の上に、

  * ペブリングの遷移系 `Reach`
  * 走行から解体順序を取り出す `reach_cost`（= $W \le u_{\min}$）
  * 系: `reach(p,e) ≤ (e+2)2^{p-2}`（`reach_singleton_le`）

を置く。**構成側（定理 B1、`reach ≥ …`）は含まない**ので、
等号（定理 B2）の機械証明にはなっていない。
-/
import Revgarbage.PebbleDP

namespace PebbleDP

open Finset PebbleArith

/-! ### ペブリングのモデル -/

/-- 配置 `S`（位置の有限集合。位置 0 は常時可用な源で `S` に入れない）が
ピーク `p`・消去 `u` 回で `∅` から到達可能。 -/
inductive Reach (p : ℕ) : Finset ℕ → ℕ → Prop
  | empty : Reach p ∅ 0
  | put {S u v} : Reach p S u → 0 < v → v ∉ S → (v = 1 ∨ v - 1 ∈ S) → S.card < p →
      Reach p (insert v S) u
  | take {S u v} : Reach p S u → v ∈ S → (v = 1 ∨ v - 1 ∈ S) → Reach p (S.erase v) u
  | erase {S u v} : Reach p S u → v ∈ S → ¬(v = 1 ∨ v - 1 ∈ S) → Reach p (S.erase v) (u + 1)

lemma Reach.pos {p S u} (h : Reach p S u) : ∀ w ∈ S, 0 < w := by
  induction h with
  | empty => intro w hw; cases hw
  | put _ hv _ _ _ ih =>
    intro w hw
    rcases Finset.mem_insert.1 hw with rfl | hw
    · exact hv
    · exact ih w hw
  | take _ _ _ ih => intro w hw; exact ih w (Finset.mem_of_mem_erase hw)
  | erase _ _ _ ih => intro w hw; exact ih w (Finset.mem_of_mem_erase hw)

lemma Reach.card_le {p S u} (h : Reach p S u) : S.card ≤ p := by
  induction h with
  | empty => simp
  | put _ _ hv _ hc _ => rw [Finset.card_insert_of_notMem hv]; omega
  | take _ hv _ ih => exact le_trans (Finset.card_erase_le) ih
  | erase _ hv _ ih => exact le_trans (Finset.card_erase_le) ih

/-! ### リストによる表現 -/

/-- `D` は `S` の（重複無しの）並べ方。 -/
def Repr (D : List ℕ) (S : Finset ℕ) : Prop := D.Nodup ∧ ∀ w, w ∈ D ↔ w ∈ S

lemma Repr.length {D S} (h : Repr D S) : D.length = S.card := by
  obtain ⟨hnd, hmem⟩ := h
  have : D.toFinset = S := by
    ext w; simpa using hmem w
  rw [← this, List.toFinset_card_of_nodup hnd]

lemma Repr.cons {D S v} (h : Repr D S) (hv : v ∉ S) : Repr (v :: D) (insert v S) := by
  obtain ⟨hnd, hmem⟩ := h
  refine ⟨?_, ?_⟩
  · refine List.nodup_cons.2 ⟨fun hc => hv ((hmem v).1 hc), hnd⟩
  · intro w
    simp only [List.mem_cons, Finset.mem_insert, hmem]

lemma Repr.erase {D S v} (h : Repr D S) : Repr (D.erase v) (S.erase v) := by
  obtain ⟨hnd, hmem⟩ := h
  refine ⟨hnd.erase v, ?_⟩
  intro w
  rw [List.Nodup.mem_erase_iff hnd, Finset.mem_erase, hmem]

lemma Repr.perm {D E S} (h : Repr D S) (hp : E.Perm D) : Repr E S :=
  ⟨hp.symm.nodup h.1, fun w => (hp.mem_iff).trans (h.2 w)⟩

/-! ### 主定理（下界側）: 走行から解体順序を取り出す -/

theorem reach_cost (p : ℕ) {S : Finset ℕ} {u : ℕ} (h : Reach p S u) :
    ∃ D : List ℕ, Repr D S ∧ cost p D ≤ (u : ℕ∞) := by
  induction h with
  | empty => exact ⟨[], ⟨List.nodup_nil, by simp⟩, by simp⟩
  | @put S u v hS hv hvS hsup hcard ih =>
    obtain ⟨D, hR, hc⟩ := ih
    have hlen : D.length = S.card := hR.length
    have hposD : ∀ w ∈ D, 0 < w := fun w hw => hS.pos w ((hR.2 w).1 hw)
    have h3 : pred D v < v := pred_lt hv
    have hgap : v - pred D v = 1 := by
      rcases hsup with h1 | hmem
      · have h0 : pred D v = 0 := by
          rcases pred_zero_or D v with h0 | ⟨hm, hlt⟩
          · exact h0
          · have := hposD _ hm; omega
        omega
      · have hm1 : v - 1 ∈ D := (hR.2 _).2 hmem
        have h2 : v - 1 ≤ pred D v := pred_le hm1 (by
          have := hS.pos _ hmem; omega)
        omega
    refine ⟨v :: D, hR.cons hvS, ?_⟩
    rw [cost_cons, hgap, cst_gap_one (by omega)]
    simpa using hc
  | @take S u v hS hvS hsup ih =>
    obtain ⟨D, hR, hc⟩ := ih
    have hvD : v ∈ D := (hR.2 v).2 hvS
    have hposD : ∀ w ∈ D, 0 < w := fun w hw => hS.pos w ((hR.2 w).1 hw)
    have hv0 : 0 < v := hS.pos v hvS
    have h3 : pred (D.erase v) v < v := pred_lt hv0
    have hgap : v - pred (D.erase v) v = 1 := by
      rcases hsup with h1 | hmem
      · have h0 : pred (D.erase v) v = 0 := by
          rcases pred_zero_or (D.erase v) v with h0 | ⟨hm, hlt⟩
          · exact h0
          · have := hposD _ (List.mem_of_mem_erase hm); omega
        omega
      · have hne : v - 1 ≠ v := by have := hS.pos _ hmem; omega
        have hm1 : v - 1 ∈ D.erase v :=
          (List.mem_erase_of_ne hne).2 ((hR.2 _).2 hmem)
        have h2 : v - 1 ≤ pred (D.erase v) v := pred_le hm1 (by omega)
        omega
    refine ⟨D.erase v, hR.erase, ?_⟩
    have hlen : D.length ≤ p := by rw [hR.length]; exact hS.card_le
    exact le_trans (cost_erase_le_of_supported p D hR.1 hposD v hvD hlen hgap) hc
  | @erase S u v hS hvS _ ih =>
    obtain ⟨D, hR, hc⟩ := ih
    have hvD : v ∈ D := (hR.2 v).2 hvS
    have hposD : ∀ w ∈ D, 0 < w := fun w hw => hS.pos w ((hR.2 w).1 hw)
    obtain ⟨E, hEperm, hEc⟩ := Bnat p D hR.1 hposD v hvD
    refine ⟨E, (hR.erase (v := v)).perm hEperm, ?_⟩
    calc cost p E ≤ cost p D + 1 := hEc
      _ ≤ (u : ℕ∞) + 1 := add_le_add hc le_rfl
      _ = ((u + 1 : ℕ) : ℕ∞) := by push_cast; ring


lemma Repr.singleton {D : List ℕ} {n : ℕ} (h : Repr D {n}) : D = [n] := by
  have hlen : D.length = 1 := by rw [h.length]; simp
  obtain ⟨a, rfl⟩ := List.length_eq_one_iff.1 hlen
  have ha : a = n := by simpa using (h.2 a).1 (by simp)
  rw [ha]

@[simp] lemma pred_nil (y : ℕ) : pred [] y = 0 := rfl

lemma cost_singleton (p n : ℕ) : cost p [n] = cst n p := by
  rw [cost_cons]
  simp

/-- **定理 B2 の上界方向（層1）**: ピーク `p`・消去 `u` 回で単独ペブル `{n}` に
到達できるなら `n ≤ (u+2)·2^{p-2}`。すなわち `reach(p,e) ≤ (e+2)2^{p-2}`。 -/
theorem reach_singleton_le {p n u : ℕ} (hp : 2 ≤ p) (h : Reach p {n} u) :
    n ≤ (u + 2) * 2 ^ (p - 2) := by
  obtain ⟨D, hR, hc⟩ := reach_cost p h
  rw [hR.singleton, cost_singleton] at hc
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 2 := ⟨p - 2, by omega⟩
  rw [cst_succ_succ] at hc
  have hle : psi n (2 ^ m) ≤ u := by exact_mod_cast hc
  have h2 : n ⌈/⌉ 2 ^ m ≤ u + 2 := by
    simp only [psi] at hle
    omega
  have h4 := (ceilDiv_le_iff_le_mul (a := 2 ^ m) (b := n) (c := u + 2) (by positivity)).1 h2
  have h3 : m + 2 - 2 = m := by omega
  rw [h3, Nat.mul_comm]
  exact h4

/-! ### 非空性の検査（モデルが空でないこと・上界がタイトであること） -/

/-- 非空性の検査（**上界定理が空虚に真でないことの確認**）:
$p=3$・消去 0 で $\{4\}$ に到達できる（Bennett の 9 手:
put1 put2 take1 put3 put4 take3 put1 take2 take1）。
`reach_singleton_le` の境界 $(0+2)\cdot2^{3-2}=4$ がタイトであることも示す。 -/
theorem reach_four : Reach 3 {4} 0 := by
  have e1 : Reach 3 (insert 1 (∅ : Finset ℕ)) 0 :=
    Reach.put Reach.empty (by norm_num) (by decide) (by decide) (by decide)
  rw [show insert 1 (∅ : Finset ℕ) = {1} from by decide] at e1
  have e2 : Reach 3 (insert 2 ({1} : Finset ℕ)) 0 :=
    Reach.put e1 (by norm_num) (by decide) (by decide) (by decide)
  rw [show insert 2 ({1} : Finset ℕ) = {1, 2} from by decide] at e2
  have e3 : Reach 3 (({1, 2} : Finset ℕ).erase 1) 0 :=
    Reach.take e2 (by decide) (by decide)
  rw [show (({1, 2} : Finset ℕ).erase 1) = {2} from by decide] at e3
  have e4 : Reach 3 (insert 3 ({2} : Finset ℕ)) 0 :=
    Reach.put e3 (by norm_num) (by decide) (by decide) (by decide)
  rw [show insert 3 ({2} : Finset ℕ) = {2, 3} from by decide] at e4
  have e5 : Reach 3 (insert 4 ({2, 3} : Finset ℕ)) 0 :=
    Reach.put e4 (by norm_num) (by decide) (by decide) (by decide)
  rw [show insert 4 ({2, 3} : Finset ℕ) = {2, 3, 4} from by decide] at e5
  have e6 : Reach 3 (({2, 3, 4} : Finset ℕ).erase 3) 0 :=
    Reach.take e5 (by decide) (by decide)
  rw [show (({2, 3, 4} : Finset ℕ).erase 3) = {2, 4} from by decide] at e6
  have e7 : Reach 3 (insert 1 ({2, 4} : Finset ℕ)) 0 :=
    Reach.put e6 (by norm_num) (by decide) (by decide) (by decide)
  rw [show insert 1 ({2, 4} : Finset ℕ) = {1, 2, 4} from by decide] at e7
  have e8 : Reach 3 (({1, 2, 4} : Finset ℕ).erase 2) 0 :=
    Reach.take e7 (by decide) (by decide)
  rw [show (({1, 2, 4} : Finset ℕ).erase 2) = {1, 4} from by decide] at e8
  have e9 : Reach 3 (({1, 4} : Finset ℕ).erase 1) 0 :=
    Reach.take e8 (by decide) (by decide)
  rw [show (({1, 4} : Finset ℕ).erase 1) = {4} from by decide] at e9
  exact e9

/-- 上の到達は上界にちょうど乗っている。 -/
example : (4 : ℕ) ≤ (0 + 2) * 2 ^ (3 - 2) := reach_singleton_le (by norm_num) reach_four

/-- 一方 `{5}` は $p=3$・消去 0 では到達不能（上界定理の帰結）。 -/
theorem not_reach_five : ¬ Reach 3 {5} 0 := by
  intro h
  have := reach_singleton_le (p := 3) (n := 5) (u := 0) (by norm_num) h
  norm_num at this


/-- 消去手も使えることの確認: $p=3$・消去 1 回で $\{6\}$ に到達
（$\{4\}$ から put5 put6 take5 erase4）。境界 $(1+2)\cdot2=6$ にちょうど乗る。 -/
theorem reach_six : Reach 3 {6} 1 := by
  have e1 : Reach 3 (insert 5 ({4} : Finset ℕ)) 0 :=
    Reach.put reach_four (by norm_num) (by decide) (by decide) (by decide)
  rw [show insert 5 ({4} : Finset ℕ) = {4, 5} from by decide] at e1
  have e2 : Reach 3 (insert 6 ({4, 5} : Finset ℕ)) 0 :=
    Reach.put e1 (by norm_num) (by decide) (by decide) (by decide)
  rw [show insert 6 ({4, 5} : Finset ℕ) = {4, 5, 6} from by decide] at e2
  have e3 : Reach 3 (({4, 5, 6} : Finset ℕ).erase 5) 0 :=
    Reach.take e2 (by decide) (by decide)
  rw [show (({4, 5, 6} : Finset ℕ).erase 5) = {4, 6} from by decide] at e3
  have e4 : Reach 3 (({4, 6} : Finset ℕ).erase 4) (0 + 1) :=
    Reach.erase e3 (by decide) (by decide)
  rw [show (({4, 6} : Finset ℕ).erase 4) = {6} from by decide] at e4
  simpa using e4

example : (6 : ℕ) ≤ (1 + 2) * 2 ^ (3 - 2) := reach_singleton_le (by norm_num) reach_six

/-- $\{7\}$ は $p=3$・消去 1 回では到達不能。 -/
theorem not_reach_seven : ¬ Reach 3 {7} 1 := by
  intro h
  have := reach_singleton_le (p := 3) (n := 7) (u := 1) (by norm_num) h
  norm_num at this

end PebbleDP
