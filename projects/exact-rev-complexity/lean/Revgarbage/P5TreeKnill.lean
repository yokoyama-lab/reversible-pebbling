/-
# P5 系 LI の最後の一歩: 道の最短手数は Knill の再帰 `Fc` より小さくならない

`P5TreeCaterpillar.lean` は毛虫型の木の手順を、根から全頂点を 1 回ずつ通る道の手順に直した
（M(T,S) ≥ M(道,S)）。ここでは残っていた M(道,S) ≥ F_c(|V|,S)（Knill 1995 Thm 2.1 の `≥` の向き）を、
`reversible-pebbling-lean`（`RevPebbling`）の鎖のゲームの証明につないで示す。

  * `Fc_succ_le`: `Fc n (S+1) ≤ Fc n S`（ペブルが増えても再帰の値は増えない）
  * `Fc_le_of_reachIn`: 鎖のゲーム（`RevPebbling.GameReach.ReachIn`．盤は `List Bool`，マス `i` の手は
    `i = 0` かマス `i-1` にペブルがあるとき合法，空から最後のマスだけにペブルがある盤へ，ペブル数の最大 ≤ S）で
    `t` 手以下なら `Fc n S ≤ t`．`RevPebbling.HpkResolved.gameF_recursion_ge_final`（最適な手順を Knill の 3 つに切る）
    と，切った部分も手順であること（`RowExact.reachIn_lower_suffix`，`reachIn_upper`）を `(S, n)` の帰納法で使う
  * `path_reachIn`: P5 の模型で道（`L` に沿って前の頂点の子がちょうど次の頂点）の手順は，同じペブル数・同じ手数以下の
    鎖のゲームの手順に写る（頂点 `L[i]` をマス `|L|-1-i` に）
  * `path_Fc_le`，`RootedTree.caterpillar_Fc_le`: 道と毛虫型の木で `Fc |V| k ≤ n`，すなわち M(T,k) ≥ F_c(|T|,k)

ペブル数の意味は両方の模型で同じ（配置の大きさの最大）で，番号のずれは無い．
このファイルは `reversible-pebbling-lean`（非公開，0d3feab で検査．Mathlib は同じ fabf563a7c95）の `RevPebbling` を
import する．`revgarbage` の lakefile はその依存を持たないので `Revgarbage.lean` には登録していない（`lake build` は
このファイルに触れない）．検査は両リポのモジュールを同じ `LEAN_PATH` に並べて `lean` を直接走らせる（`p5/cc/LEAN_LI.md`）。
-/
import Revgarbage.P5TreeChain
import Revgarbage.P5TreeCaterpillar
import RevPebbling.RowExact

namespace P5Tree

open Finset
open RevPebbling.PebblingFoundations RevPebbling.GameReach RevPebbling.GameCost
open RevPebbling.CutFull RevPebbling.CutTime RevPebbling.HpkResolved RevPebbling.UpperPeak
open RevPebbling.RowExact RevPebbling.ReachLimit RevPebbling.GameDecomposition
open RevPebbling.CutOptimal

/-! ### Knill の再帰の単調性 -/

/-- ペブルを 1 個増やしても再帰の値は増えない。 -/
theorem Fc_succ_le : ∀ S n, Fc n (S + 1) ≤ Fc n S := by
  intro S
  induction S with
  | zero => intro n; rw [Fc_zero]; exact le_top
  | succ S ih =>
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ihn =>
    rw [Fc.eq_2 n (S + 1), Fc.eq_2 n S]
    split_ifs with h
    · exact le_rfl
    · apply Finset.le_inf
      intro m _
      refine le_trans (Finset.inf_le (mem_attach _ m)) ?_
      have hm := mem_Ico.1 m.2
      exact add_le_add (add_le_add (ihn m.1 hm.2) (ih m.1)) (ih (n - m.1))

/-! ### 鎖のゲームの手順は `Fc` 以上（Knill の `≥`） -/

lemma ReachIn.mono_peak {n p q t : ℕ} (h : ReachIn n p t) (hpq : p ≤ q) : ReachIn n q t := by
  obtain ⟨s, hlen, hr, hleg, hex, hpk⟩ := h
  exact ⟨s, hlen, hr, hleg, hex, le_trans hpk hpq⟩

/-- 1 個のペブルでは 1 マスの鎖も終えられない（終わりの盤にペブルが 1 個ある）。 -/
lemma not_reachIn_zero {n t : ℕ} (hn : 1 ≤ n) : ¬ ReachIn n 0 t := by
  rintro ⟨s, _, _, _, hex, hpk⟩
  have h1 := ones_prefix_le_maxOnes s (emptyBoard n) s.length
  rw [List.take_length, hex] at h1
  have hon : nth (doneBoard n) (n - 1) = true := by
    rw [RevPebbling.CutUpper.nth_doneBoard n (n - 1) hn]; simp
  have hmem : true ∈ doneBoard n := by
    have hlt : n - 1 < (doneBoard n).length := by simp; omega
    have : (doneBoard n)[n - 1] = true := by
      simpa [nth, List.getElem?_eq_getElem hlt] using hon
    exact this ▸ List.getElem_mem hlt
  have hpos : 0 < ones (doneBoard n) := List.count_pos_iff.2 hmem
  omega

/-- **Knill の `≥`**: 鎖のゲームで `n ≥ 1` マスを `S` 個以下・`t` 手以下で終えられるなら `Fc n S ≤ t`。 -/
theorem Fc_le_of_reachIn : ∀ S n t, 1 ≤ n → ReachIn n S t → Fc n S ≤ (t : ℕ∞) := by
  intro S
  induction S with
  | zero => intro n t hn h; exact absurd h (not_reachIn_zero hn)
  | succ S ihS =>
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ihn =>
    intro t hn h
    have hgt : gameF n (S + 1) ≤ t := gameF_le h
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · obtain rfl : n = 1 := by omega
      rw [Fc_one]
      have h1 := gameF_one (S + 1) (by omega)
      exact_mod_cast (show 1 ≤ t by omega)
    obtain ⟨p, hlen, hr, hleg, hex, hpk⟩ := reachIn_gameF ⟨t, h⟩
    by_cases hsmall : maxOnes (emptyBoard n) p ≤ S
    · have hr2 : ReachIn n S p.length := ⟨p, le_rfl, hr, hleg, hex, hsmall⟩
      calc Fc n (S + 1) ≤ Fc n S := Fc_succ_le S n
        _ ≤ (p.length : ℕ∞) := ihS n _ hn hr2
        _ ≤ (t : ℕ∞) := by exact_mod_cast le_trans hlen hgt
    · have hpeak : maxOnes (emptyBoard n) p = S + 1 := by omega
      rcases Nat.eq_zero_or_pos S with hS0 | hS
      · subst hS0
        have := le_two_pow_of_reachIn hn h
        simp at this; omega
      have hrec := gameF_recursion_ge_final (S := S) (n := n) (s := p) hS h2 hr hleg hex hpeak hlen
      have hxlt : cutFull n S p + 1 < n := cutFull_lt hS h2
      obtain ⟨a, hafull, ha⟩ := cutFull_attained (exists_full_time hpeak)
      have hpkl := hpk_at_full_cut (x := cutFull n S p) (a := a)
        (by omega) hS hr hleg hex (Nat.le_of_eq hpeak) hlen hafull ha
      have hlow : ∃ t, ReachIn (cutFull n S p + 1) S t :=
        reachIn_lower_suffix hxlt hleg hex ha hpkl
      have hup : ∃ t, ReachIn (n - (cutFull n S p + 1)) S t :=
        reachIn_upper hxlt hr hleg hex (upper_peak_le (Nat.le_of_eq hpeak) hfull_cutFull)
      have hlow' : ∃ t, ReachIn (cutFull n S p + 1) (S + 1) t := by
        obtain ⟨t', ht'⟩ := hlow; exact ⟨t', ReachIn.mono_peak ht' (by omega)⟩
      have e1 := ihn (cutFull n S p + 1) hxlt _ (by omega) (reachIn_gameF hlow')
      have e2 := ihS (cutFull n S p + 1) _ (by omega) (reachIn_gameF hlow)
      have e3 := ihS (n - (cutFull n S p + 1)) _ (by omega) (reachIn_gameF hup)
      have hsplit := Fc_le_split (n := n) (m := cutFull n S p + 1) (by omega) hxlt S
      calc Fc n (S + 1)
          ≤ Fc (cutFull n S p + 1) (S + 1) + Fc (cutFull n S p + 1) S
              + Fc (n - (cutFull n S p + 1)) S := hsplit
        _ ≤ (gameF (cutFull n S p + 1) (S + 1) : ℕ∞) + (gameF (cutFull n S p + 1) S : ℕ∞)
              + (gameF (n - (cutFull n S p + 1)) S : ℕ∞) := add_le_add (add_le_add e1 e2) e3
        _ ≤ (t : ℕ∞) := by exact_mod_cast le_trans hrec hgt

/-! ### P5 の道の手順を鎖のゲームの手順に写す -/

section PathToChain

variable {V : Type*} [DecidableEq V]

/-- 配置 `P` の盤: マス `j` は頂点 `L.reverse[j]`（`L` の後ろから数えて `j` 番目）。 -/
def board (L : List V) (P : Finset V) : Board := L.reverse.map (fun v => decide (v ∈ P))

@[simp] lemma board_length (L : List V) (P : Finset V) : (board L P).length = L.length := by
  simp [board]

lemma board_empty (L : List V) : board L ∅ = emptyBoard L.length := by
  simp [board, emptyBoard, List.map_const']

lemma getElem_board (L : List V) (P : Finset V) (j : ℕ) (hj : j < (board L P).length) :
    (board L P)[j] = decide (L.reverse[j]'(by simpa using hj) ∈ P) := by
  simp [board]

lemma nth_board (L : List V) (P : Finset V) (j : ℕ) (hj : j < L.length) :
    nth (board L P) j = decide (L.reverse[j]'(by simpa using hj) ∈ P) := by
  have hj' : j < (board L P).length := by simpa using hj
  rw [nth, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj', Option.getD_some, getElem_board]

lemma ones_board (L : List V) (hnd : L.Nodup) (P : Finset V) : ones (board L P) ≤ P.card := by
  have hc : ones (board L P) = (L.reverse.filter (fun v => decide (v ∈ P))).length := by
    simp [ones, board, List.count_eq_countP, List.countP_eq_length_filter, List.filter_map,
      Function.comp_def]
  rw [hc]
  have hnd' : (L.reverse.filter (fun v => decide (v ∈ P))).Nodup :=
    (List.nodup_reverse.2 hnd).filter _
  rw [← List.toFinset_card_of_nodup hnd']
  apply Finset.card_le_card
  intro v hv
  simp at hv
  exact hv.2

lemma nth_toggle_self' (c : Board) {i : ℕ} (hi : i < c.length) : nth (toggle c i) i = !nth c i := by
  simp [nth, toggle, List.getElem?_set_self hi, List.getElem?_eq_getElem hi]

/-- 1 手で配置が頂点 `L.reverse[i]` だけ変われば，盤はマス `i` の反転。 -/
lemma board_toggle (L : List V) (hnd : L.Nodup) (P Q : Finset V) (i : ℕ) (hi : i < L.length)
    (hQ : ∀ w, w ∈ Q ↔ (if w = L.reverse[i]'(by simpa using hi) then w ∉ P else w ∈ P)) :
    board L Q = toggle (board L P) i := by
  have hnd' : L.reverse.Nodup := List.nodup_reverse.2 hnd
  have hi' : i < L.reverse.length := by simpa using hi
  apply board_ext (by simp [toggle])
  intro j
  by_cases hj : j < L.length
  · by_cases hij : i = j
    · subst hij
      rw [nth_board L Q i hi, nth_toggle_self' _ (by simpa using hi),
        nth_board L P i hi]
      obtain ⟨w, hw⟩ : ∃ w, L.reverse[i]'hi' = w := ⟨_, rfl⟩
      rw [hw]
      have := hQ w
      rw [if_pos hw.symm] at this
      by_cases hm : w ∈ P <;> simp [hm, this]
    · have hj' : j < L.reverse.length := by simpa using hj
      have hne : L.reverse[j]'hj' ≠ L.reverse[i]'hi' := fun h =>
        hij ((hnd'.getElem_inj_iff).1 h).symm
      have hlen : j < (toggle (board L P) i).length := by simp [toggle]; exact hj
      rw [nth_board L Q j hj, nth, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen,
        Option.getD_some]
      simp only [toggle, List.getElem_set, if_neg hij]
      rw [getElem_board]
      have := hQ (L.reverse[j]'hj')
      simp only [if_neg hne] at this
      simpa using this
  · have h1 : (board L Q).length ≤ j := by simp; omega
    have h2 : (toggle (board L P) i).length ≤ j := by simp [toggle]; omega
    rw [nth, nth, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none h1, List.getElem?_eq_none h2]

/-- 終わりの配置 `{r}`（`r` は `L` の先頭）の盤は鎖のゲームの終わりの盤。 -/
lemma board_done (L : List V) (hnd : L.Nodup) {r : V} (hh : L.head? = some r) :
    board L {r} = doneBoard L.length := by
  have hpos : 1 ≤ L.length := by
    cases L with
    | nil => simp at hh
    | cons a t => simp
  have hnd' : L.reverse.Nodup := List.nodup_reverse.2 hnd
  have hlast : L.reverse[L.length - 1]'(by simp; omega) = r := by
    rw [List.getElem_reverse]
    cases L with
    | nil => simp at hh
    | cons a t => simp at hh ⊢; exact hh
  apply board_ext (by simp)
  intro j
  rw [RevPebbling.CutUpper.nth_doneBoard _ j hpos]
  by_cases hj : j < L.length
  · rw [nth_board L {r} j hj]
    simp only [mem_singleton]
    congr 1
    apply propext
    constructor
    · intro h
      rw [← hlast] at h
      exact (hnd'.getElem_inj_iff).1 h
    · intro h; subst h; exact hlast
  · have h1 : (board L {r}).length ≤ j := by simp; omega
    rw [nth, List.getD_eq_getElem?_getD, List.getElem?_eq_none h1]
    simp; omega

variable {pred : V → Finset V}

/-- 道の 1 手は鎖のゲームの合法な 1 手。 -/
lemma step_to_chain {L : List V} (hnd : L.Nodup) (hall : ∀ v, v ∈ L)
    (hc : L.IsChain (fun a b => pred a = {b})) {P Q : Finset V} (h : Step pred ∅ P Q) :
    ∃ i, i < L.length ∧ okMove (board L P) i = true ∧ board L Q = toggle (board L P) i := by
  obtain ⟨v, hp, hmove⟩ := h
  have hvr : v ∈ L.reverse := List.mem_reverse.2 (hall v)
  set i := L.reverse.idxOf v with hidef
  have hi' : i < L.reverse.length := List.idxOf_lt_length_of_mem hvr
  have hi : i < L.length := by simpa using hi'
  have hv : L.reverse[i] = v := List.getElem_idxOf hi'
  refine ⟨i, hi, ?_, ?_⟩
  · unfold okMove
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · simp [h0]
    · -- 子 `L.reverse[i-1]` は配置にある
      have hci : L.length - 1 - i + 1 < L.length := by omega
      have hchain := (List.isChain_iff_getElem.1 hc) (L.length - 1 - i) hci
      have hv' : L[L.length - 1 - i] = v := by
        rw [List.getElem_reverse] at hv; exact hv
      have hw : L[L.length - 1 - i + 1] = L.reverse[i - 1]'(by omega) := by
        rw [List.getElem_reverse]; congr 1; omega
      rw [hv', hw] at hchain
      have hmem : L.reverse[i - 1]'(by omega) ∈ P := by
        have := hp (by rw [hchain]; exact mem_singleton_self _)
        simp only [union_empty, mem_erase] at this
        exact this.2
      have hmem' : L[L.length - 1 - (i - 1)]'(by omega) ∈ P := by
        rw [List.getElem_reverse] at hmem; exact hmem
      rw [nth_board L P (i - 1) (by omega)]
      simp [hmem']
  · apply board_toggle L hnd P Q i hi
    intro w
    rcases hmove with ⟨hvP, rfl⟩ | ⟨hvP, rfl⟩
    · by_cases hw : w = L.reverse[i]
      · simp [hw, hv, hvP]
      · rw [if_neg hw, mem_insert]; rw [hv] at hw; simp [hw]
    · by_cases hw : w = L.reverse[i]
      · simp [hw, hv, hvP]
      · rw [if_neg hw, mem_erase]; rw [hv] at hw; simp [hw]

/-- 道の手順の列は鎖のゲームの手順に写る（手数は列の長さ − 1，盤のペブル数は配置の大きさ以下）。 -/
lemma chain_moves {L : List V} (hnd : L.Nodup) (hall : ∀ v, v ∈ L)
    (hc : L.IsChain (fun a b => pred a = {b})) (k : ℕ) :
    ∀ (Ls : List (Finset V)) (P₀ : Finset V), (P₀ :: Ls).IsChain (Step pred ∅) →
      (∀ Q ∈ P₀ :: Ls, Q.card ≤ k) →
      ∃ s : List ℕ, s.length = Ls.length ∧ (∀ i ∈ s, i < L.length) ∧
        legalB (board L P₀) s = true ∧
        execB (board L P₀) s = board L ((P₀ :: Ls).getLast (List.cons_ne_nil _ _)) ∧
        maxOnes (board L P₀) s ≤ k := by
  intro Ls
  induction Ls with
  | nil =>
    intro P₀ _ hk
    refine ⟨[], rfl, by simp, rfl, rfl, ?_⟩
    simp only [maxOnes]
    exact le_trans (ones_board L hnd P₀) (hk P₀ (by simp))
  | cons Q rest ih =>
    intro P₀ hch hk
    rw [List.isChain_cons_cons] at hch
    obtain ⟨i, hi, hok, htog⟩ := step_to_chain hnd hall hc hch.1
    obtain ⟨s, hlen, hr, hleg, hex, hpk⟩ :=
      ih Q hch.2 (fun R hR => hk R (List.mem_cons_of_mem _ hR))
    refine ⟨i :: s, by simp [hlen], ?_, ?_, ?_, ?_⟩
    · intro j hj
      rcases List.mem_cons.1 hj with rfl | hj
      · exact hi
      · exact hr j hj
    · simp only [legalB, hok, Bool.true_and, ← htog]; exact hleg
    · show execB (toggle (board L P₀) i) s = _
      rw [← htog, hex]
      simp
    · simp only [maxOnes, ← htog]
      exact max_le (le_trans (ones_board L hnd P₀) (hk P₀ (by simp))) hpk

/-- **道の手順は鎖のゲームの手順**: `L` に沿った道（前の頂点の子がちょうど次の頂点）で，
空から `{r}`（`r` は先頭）へ `k` 個以下・`n` 手以下なら，`|L|` マスの鎖のゲームも `k` 個以下・`n` 手以下。 -/
theorem path_reachIn {L : List V} (hnd : L.Nodup) (hall : ∀ v, v ∈ L)
    (hc : L.IsChain (fun a b => pred a = {b})) {r : V} (hh : L.head? = some r) {k n : ℕ}
    (h : Pebbling pred ∅ ∅ {r} k n) : ReachIn L.length k n := by
  obtain ⟨Ls, hhead, hlast, hch, hk, hlen⟩ := h
  cases Ls with
  | nil => simp at hhead
  | cons P₀ rest =>
    simp only [List.head?_cons, Option.some.injEq] at hhead
    subst hhead
    obtain ⟨s, hslen, hr, hleg, hex, hpk⟩ := chain_moves hnd hall hc k rest ∅ hch hk
    have hl : (∅ :: rest).getLast (List.cons_ne_nil _ _) = {r} := by
      rw [List.getLast?_eq_some_getLast (List.cons_ne_nil _ _)] at hlast
      exact Option.some.inj hlast
    rw [hl, board_done L hnd hh] at hex
    rw [board_empty] at hleg hex hpk
    refine ⟨s, ?_, hr, hleg, hex, hpk⟩
    simp at hlen; omega

end PathToChain

/-! ### まとめ: 道と毛虫型の木で M ≥ F_c -/

section Main

variable {V : Type*} [Fintype V] [DecidableEq V] {pred : V → Finset V}

/-- **道で M(P_n,k) ≥ F_c(n,k)**: 全頂点を 1 回ずつ通る `L` に沿った道の手順は `Fc |V| k` 手以上。 -/
theorem path_Fc_le {L : List V} (hnd : L.Nodup) (hall : ∀ v, v ∈ L)
    (hc : L.IsChain (fun a b => pred a = {b})) {r : V} (hh : L.head? = some r) {k n : ℕ}
    (h : Pebbling pred ∅ ∅ {r} k n) : Fc (Fintype.card V) k ≤ (n : ℕ∞) := by
  have hcard : L.length = Fintype.card V := by
    rw [← List.toFinset_card_of_nodup hnd]
    congr 1
    ext v; simp [hall v]
  have hpos : 1 ≤ L.length := by
    cases L with
    | nil => simp at hh
    | cons a t => simp
  rw [← hcard]
  exact Fc_le_of_reachIn k L.length n hpos (path_reachIn hnd hall hc hh h)

namespace RootedTree

variable (T : RootedTree V)

/-- **系 LI（Knill の定理までつないだ形）**: 各頂点の葉でない子が高々 1 個の根付き木 `T` で，
`k` 個以下・`n` 手以下のペブリングがあれば `Fc |T| k ≤ n`。すなわち M(T,k) ≥ F_c(|T|,k)（予想 CC が成り立つ）。 -/
theorem caterpillar_Fc_le (hcat : ∀ u x y, x ∈ T.children u → y ∈ T.children u →
    T.children x ≠ ∅ → T.children y ≠ ∅ → x = y) {k n : ℕ}
    (h : Pebbling T.children ∅ ∅ {T.root} k n) : Fc (Fintype.card V) k ≤ (n : ℕ∞) := by
  obtain ⟨pred', L, hh, hnd, hall, hc, _, htr⟩ := T.caterpillar_path_list hcat
  exact path_Fc_le hnd hall hc hh (htr k n h)

end RootedTree

end Main

end P5Tree
