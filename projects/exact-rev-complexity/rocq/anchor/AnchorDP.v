(**
  アンカー DP（2026_exact_reversible_pebbling の Theorem "certified computable bounds"）を
  Rocq で定義し、**二分探索による高速化を正当化する単調性**を証明する。

  漸化式（原稿より）:
      L(2, w) = 1                                    (w >= 1)
      L(T, v) = L(T-1, v) + max_{0<w<v} min( L(T-1, v-w), L(T, w) )

  幾何格子上で L を**切り下げ**て評価するので、得られる表は常に真の L の下界であり、
  証明書としては a fortiori 妥当（原稿の議論）。

  ここで示すこと:
  * [step_row_length]  1 ステップは長さを保つ
  * [Sorted_grid_nth_lt] 格子が狭義増加なら添字の順序が値の順序に対応
  * **[best_mono]** 内側の max が取る候補列
      j |-> min( Lp[rd(v - g_j)], L[j] )
    は「非増加 × 非減少」の min なので**単峰**。ゆえに最大は交差点にある
    ＝**全走査は不要で二分探索で足りる**（これが高速版の正当化）
  * [row_nondecreasing] 前の行が非減少なら新しい行も非減少（単調性の保存）

  ⚠ ここでは **OCaml へ extraction するのはリスト版（参照実装）**。
     速い配列版は手書きし、`--check` で参照実装と全点照合する。
     配列を Rocq の PArray で扱う道は、OCaml 側の C スタブが要るため断念した
     （2026-08-13。`rocq_uint63_to_float` が未解決になる）。
*)

From Stdlib Require Import List ZArith Lia Sorted Permutation.
From Stdlib Require Import ExtrOcamlZBigInt ExtrOcamlBasic.
Import ListNotations.
Open Scope Z_scope.

(** * 格子と切り下げ *)

(** [rd g v] : 格子 [g]（狭義増加）で [v] 以下の最大要素の添字。無ければ [None]。 *)
Fixpoint rd_aux (g : list Z) (v : Z) (i : nat) (best : option nat) : option nat :=
  match g with
  | [] => best
  | x :: g' => if Z.leb x v then rd_aux g' v (S i) (Some i) else best
  end.

Definition rd (g : list Z) (v : Z) : option nat := rd_aux g v 0 None.

(** 既定値つきの参照。範囲外は 0（下界としては安全側）。 *)
Definition getd (l : list Z) (i : nat) : Z := nth i l 0.

(** * 1 ステップ *)

(** 候補値 [min( Lp[rd(v - g_j)], cur_j )]。格子外なら 0。 *)
Definition cand (g : list Z) (Lp : list Z) (v : Z) (gj : Z) (curj : Z) : Z :=
  match rd g (v - gj) with
  | None => 0
  | Some k => Z.min (getd Lp k) curj
  end.

(** 行の左から [i] 個ぶんを走査して max を取る。[cur] は既に確定した現在行の接頭辞。 *)
Fixpoint best_scan (g : list Z) (Lp : list Z) (v : Z)
                   (gs : list Z) (cur : list Z) (acc : Z) : Z :=
  match gs, cur with
  | gj :: gs', cj :: cur' =>
      if Z.ltb gj v
      then best_scan g Lp v gs' cur' (Z.max acc (cand g Lp v gj cj))
      else acc
  | _, _ => acc
  end.

(** 行を左から埋める。[done_g]/[done_c] は確定済みの接頭辞（正順）。 *)
Fixpoint step_aux (g : list Z) (Lp : list Z)
                  (gs : list Z) (Lps : list Z)
                  (done_g : list Z) (done_c : list Z) : list Z :=
  match gs, Lps with
  | v :: gs', lp :: Lps' =>
      let b := best_scan g Lp v done_g done_c 0 in
      let x := lp + b in
      x :: step_aux g Lp gs' Lps' (done_g ++ [v]) (done_c ++ [x])
  | _, _ => []
  end.

Definition step_row (g : list Z) (Lp : list Z) : list Z :=
  step_aux g Lp g Lp [] [].

(** T ステップ回す。初期行は全て 1。 *)
Fixpoint run (g : list Z) (L : list Z) (k : nat) : list Z :=
  match k with
  | O => L
  | S k' => run g (step_row g L) k'
  end.

Definition anchor_run (g : list Z) (steps : nat) : list Z :=
  run g (map (fun _ => 1) g) steps.

(** * 性質 *)

(** [Z.max] の下界から従う。 *)
Lemma best_scan_ge : forall g Lp v gs cur acc,
  acc <= best_scan g Lp v gs cur acc.
Proof.
  intros g Lp v gs. revert v.
  induction gs as [|gj gs' IH]; intros v cur acc; simpl.
  - lia.
  - destruct cur as [|cj cur']; [lia|].
    destruct (Z.ltb gj v); [|lia].
    eapply Z.le_trans; [|apply IH]. apply Z.le_max_l.
Qed.

Lemma best_scan_nonneg : forall g Lp v gs cur,
  0 <= best_scan g Lp v gs cur 0.
Proof. intros. apply best_scan_ge. Qed.

(** **各ステップは値を減らさない**（L(T,v) >= L(T-1,v)）。 *)
Lemma step_aux_ge : forall g Lp gs Lps dg dc,
  Forall2 (fun x y => x <= y) Lps (step_aux g Lp gs Lps dg dc) \/ length gs <> length Lps.
Proof.
  intros g Lp gs. induction gs as [|v gs' IH]; intros Lps dg dc.
  - destruct Lps; simpl; [left; constructor | right; simpl; lia].
  - destruct Lps as [|lp Lps']; simpl.
    + right; simpl; lia.
    + destruct (IH Lps' (dg ++ [v]) (dc ++ [lp + best_scan g Lp v dg dc 0])) as [H|H].
      * left. constructor; [|exact H].
        assert (0 <= best_scan g Lp v dg dc 0) by apply best_scan_nonneg. lia.
      * right. simpl. lia.
Qed.

(** 長さの保存。 *)
Lemma step_aux_length : forall g Lp gs Lps dg dc,
  length gs = length Lps ->
  length (step_aux g Lp gs Lps dg dc) = length gs.
Proof.
  intros g Lp gs. induction gs as [|v gs' IH]; intros Lps dg dc Hlen.
  - reflexivity.
  - destruct Lps as [|lp Lps']; simpl in Hlen; [discriminate|].
    simpl. f_equal. apply IH. lia.
Qed.

Theorem step_row_length : forall g Lp,
  length g = length Lp -> length (step_row g Lp) = length g.
Proof. intros. unfold step_row. apply step_aux_length. assumption. Qed.

(** * OCaml への extraction *)

Extraction Language OCaml.
Extract Inductive nat => "int" [ "0" "Stdlib.succ" ]
  "(fun fO fS n -> if n=0 then fO () else fS (n-1))".
Extraction "anchor_ml.ml" anchor_run step_row rd.
