/-
# P5 補題 A: 木の再帰 `F` は同じ頂点数の鎖の Knill 再帰 `Fc` より小さくならない

原稿 `2026-WiNF/P5-tree-exponent.tex` §6 (3)「頂点数の帰納法で F(G,S) ≥ F(P_{|G|},S)」と
`p5/lb/PROOF.md` §1 補題 A を機械証明する。鎖の再帰は Knill（arXiv:2609.15062 の式 (1)）:
  Fc(n, 0) = ∞,  Fc(1, S) = 1 (S ≥ 1),  Fc(n, S) = min_{1≤m<n} [Fc(m,S) + Fc(m,S−1) + Fc(n−m,S−1)]  (n ≥ 2)
（`Fc 0 S` は空の min で `⊤`。原稿・PROOF.md の F_c(0,S)=0 とは違うが、補題 A では使わない。）

  * `F_ge_Fc`: 任意の部分問題 `(W, x)` と `S` で `Fc |W| S ≤ F W x S`（子の数は任意。`SubProb` も要らない）
  * `F_univ_ge_Fc`: 木全体で `Fc |V| S ≤ F(T, S)`
  * `cbt_F_ge_Fc`: 完全二分木 `T_h` で `Fc (2^h − 1) S ≤ F(T_h, S)`

証明に使うのは「分割の 2 つの部分の頂点数の和が |W|」と、`F` と `Fc` の再帰の形が同じこと
（第 1 項が S、残り 2 項が S−1、第 1・2 項が同じ部分）だけである。
ここで得るのは再帰 `F` の下界であって、最短手数 `M` の下界ではない（`M ≤ F` の向きしか無い）。
-/
import Revgarbage.P5TreeF
import Revgarbage.P5TreeCBT

namespace P5Tree

open Finset

/-- 鎖の Knill 再帰（`n` 頂点の鎖を `S` 個以下で）。 -/
def Fc : ℕ → ℕ → ℕ∞
  | _, 0 => ⊤
  | n, S + 1 =>
    if n = 1 then 1
    else (Ico 1 n).attach.inf (fun m => Fc m.1 (S + 1) + Fc m.1 S + Fc (n - m.1) S)
termination_by n S => (S, n)
decreasing_by
  all_goals
    have hm := mem_Ico.1 m.2
    first
    | exact Prod.Lex.right _ hm.2
    | exact Prod.Lex.left _ _ (Nat.lt_succ_self S)

lemma Fc_zero (n : ℕ) : Fc n 0 = ⊤ := by rw [Fc.eq_1]

lemma Fc_one (S : ℕ) : Fc 1 (S + 1) = 1 := by rw [Fc.eq_2, if_pos rfl]

/-- 分割 `m` による上界（Knill 再帰の 1 項）。 -/
lemma Fc_le_split {n m : ℕ} (hm1 : 1 ≤ m) (hmn : m < n) (S : ℕ) :
    Fc n (S + 1) ≤ Fc m (S + 1) + Fc m S + Fc (n - m) S := by
  rw [Fc.eq_2, if_neg (by omega)]
  exact Finset.inf_le (s := (Ico 1 n).attach)
    (f := fun m : {m // m ∈ Ico 1 n} => Fc m.1 (S + 1) + Fc m.1 S + Fc (n - m.1) S)
    (mem_attach _ ⟨m, mem_Ico.2 ⟨hm1, hmn⟩⟩)

namespace RootedTree

variable {V : Type*} [Fintype V] [DecidableEq V] (T : RootedTree V)

/-- **補題 A**: 木の再帰は、頂点数の等しい鎖の Knill 再帰より小さくならない。 -/
theorem F_ge_Fc : ∀ (W : Finset V) (x : V) (S : ℕ), Fc W.card S ≤ T.F W x S := by
  intro W
  induction W using Finset.strongInduction with
  | H W ih =>
  intro x S
  cases S with
  | zero => rw [F_zero]; exact le_top
  | succ S =>
    rw [F_succ]
    by_cases hx : x ∈ W
    · rw [dif_pos hx]
      by_cases hW : W = {x}
      · rw [if_pos hW, hW, card_singleton, Fc_one]
      · rw [if_neg hW]
        apply Finset.le_inf
        intro u _
        have hu := T.mem_splitters.1 u.2
        have huA : u.1 ∈ W ∩ T.desc u.1 := mem_inter.2 ⟨hu.1, T.self_mem_desc u.1⟩
        have hxB : x ∈ W \ T.desc u.1 := mem_sdiff.2 ⟨hx, hu.2.2⟩
        have h1 : W ∩ T.desc u.1 ⊂ W :=
          Finset.ssubset_iff_of_subset inter_subset_left |>.2 ⟨x, hx, fun h => hu.2.2 (mem_inter.1 h).2⟩
        have h2 : W \ T.desc u.1 ⊂ W :=
          Finset.ssubset_iff_of_subset sdiff_subset |>.2
            ⟨u.1, hu.1, fun h => (mem_sdiff.1 h).2 (T.self_mem_desc u.1)⟩
        have hcard := Finset.card_inter_add_card_sdiff W (T.desc u.1)
        have hA : 1 ≤ (W ∩ T.desc u.1).card := card_pos.2 ⟨_, huA⟩
        have hB : 1 ≤ (W \ T.desc u.1).card := card_pos.2 ⟨_, hxB⟩
        have hsplit := Fc_le_split (n := W.card) (m := (W ∩ T.desc u.1).card) hA (by omega) S
        have hBeq : W.card - (W ∩ T.desc u.1).card = (W \ T.desc u.1).card := by omega
        rw [hBeq] at hsplit
        refine le_trans hsplit ?_
        exact add_le_add (add_le_add (ih _ h1 u.1 (S + 1)) (ih _ h1 u.1 S)) (ih _ h2 x S)
    · rw [dif_neg hx]; exact le_top

/-- 木全体: `Fc |V| S ≤ F(T, S)`。 -/
theorem F_univ_ge_Fc (S : ℕ) : Fc (Fintype.card V) S ≤ T.F univ T.root S := by
  simpa [card_univ] using T.F_ge_Fc univ T.root S

end RootedTree

/-- 完全二分木 `T_h`（頂点数 `2^h − 1`）: `Fc (2^h − 1) S ≤ F(T_h, S)`。 -/
theorem cbt_F_ge_Fc (h : ℕ) (hh : 0 < h) (S : ℕ) :
    Fc (2 ^ h - 1) S ≤ (cbt h hh).F univ (cbt h hh).root S := by
  simpa [Fintype.card_fin] using (cbt h hh).F_univ_ge_Fc S

end P5Tree
