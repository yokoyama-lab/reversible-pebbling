/-
  # 有限 DAG に効く下界と、時間最適ペブリングの**時間窓定理**（2026-08-14）

  ## ⚠ まず、先に書いた下界の欠陥を直す

  `ParPebbleDAG.time_lower_bound_path` は路の仮定を

      hw : ∀ j, w j ∈ pa (w (j + 1))

  と書いていた。これは `w` が**無限に前方へ伸びる路**であることを要求する。
  `ℕ` 上の無限鎖（`pa v = {v-1}`）なら満たせるが、**有限 DAG では満たせない**。
  実際、`ParPebbleDAG` の 3 頂点の例 `paD`（`0 → 2 ← 1`）については
  下の `paD_no_infinite_path` で**この仮定が矛盾すること**を証明する。

  つまり **「一般 DAG で両側」は言い過ぎ**であった。上界（`par_time_exact_dag`、
  `layered` 構成）は有限 DAG に対して成立していたが、下界はその同じ DAG に
  適用できていなかった。

  本ファイルでは仮定を**有限区間** `∀ j, j < K → w j ∈ pa (w (j+1))` に弱め、
  `depth_bound_seg` / `descend_seg` / `time_lower_bound_seg` を証明する。
  元の証明が `hw` を `j ≤ d` の範囲でしか使っていないので、
  結論はそのままで仮定だけが弱くなる。これで **`paD` に下界が適用でき**
  （`paD_time_lower`）、上界と突き合わせて `par_time_exact_paD` が閉じる。

  ## 時間窓定理

  路 `w 0 → ⋯ → w k` の頂点 `w k`（最終状態に残らないもの）は

  $$ k + 1 \;\le\; t \;\le\; T - k - 1 $$

  の時刻にしか存在できない（`time_window_seg`）。**深いほど窓は狭い。**
  さらに時間最適 `T = 2d+3` のときは、その窓の**両端で必ず存在している**
  （`present_at_window_start` / `present_at_window_end` / `no_slack`）。
  最短時間で終えるには、どの頂点も**置ける最初の瞬間に置き、消せる最後の
  瞬間まで残す**しかない。

  ## 由来

  鎖 `n = 4`・`T = 7` について手で作った列

      ∅ → {0} → {0,1} → {0,1,2} → {1,2,3} → {0,1,3} → {0,3} → {3}

  はピーク 3 で、`layered` が使うピーク 4 より小さい（SAT でも `p=3` SAT・
  `p=2` UNSAT を確認）。**時間最適でも `layered` は空間的に最適ではない。**
  では何が強制されるのかを突き詰めた結果がこの窓定理である。
  鎖 `n` 頂点（`T = 2n-1`）では `w_j` の窓は `[j+1, 2n-2-j]` となり、
  手で導いた「最初の配置 `= j+1`・最後の存在 `= 2n-2-j`」に一致する。
-/
import Revgarbage.ParPebbleDAG
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Image
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.Finset.Union

namespace ParPebbleDAG

variable {pa : ℕ → Finset ℕ}

/-! ## 0. 無限路の仮定は有限 DAG では矛盾する -/

/-- **`paD`（`0 → 2 ← 1`）には無限に前方へ伸びる路が無い。**

    したがって `time_lower_bound_path` の仮定 `∀ j, w j ∈ paD (w (j+1))` は
    `paD` については充足不能であり、同定理は `paD` に対して空虚である。
    これが以下で仮定を有限区間に弱める理由。 -/
theorem paD_no_infinite_path : ¬ ∃ w : ℕ → ℕ, ∀ j, w j ∈ paD (w (j + 1)) := by
  rintro ⟨w, hw⟩
  have h1 : w 1 = 2 := by
    by_contra h
    have h0 := hw 0
    simp [paD, h] at h0
  have h2 := hw 1
  rw [h1] at h2
  by_cases hc : w 2 = 2
  · rw [hc] at h2; simp [paD] at h2
  · simp [paD, hc] at h2

/-! ## 1. 有限区間版の補題 -/

/-- **深さの下界（有限区間版）**。`w 0 → ⋯ → w K` が有向路なら、
    `w j`（`j ≤ K`）は時刻 `j` 以前には置かれていない。

    `depth_bound_path` の仮定を `∀ j` から `∀ j < K` に弱めたもの。 -/
theorem depth_bound_seg {P : ℕ → Finset ℕ} {T K : ℕ} {w : ℕ → ℕ}
    (hp : Pebbling pa P T) (hw : ∀ j, j < K → w j ∈ pa (w (j + 1))) :
    ∀ t, t ≤ T → ∀ j, j ≤ K → w j ∈ P t → j + 1 ≤ t := by
  intro t
  induction t with
  | zero =>
      intro _ j _ hj
      rw [hp.start] at hj; simp at hj
  | succ t IH =>
      intro htT j hjK hj
      by_cases hjt : w j ∈ P t
      · have := IH (by omega) j hjK hjt; omega
      · rcases Nat.eq_zero_or_pos j with rfl | hjpos
        · omega
        · have hch : Changed (P t) (P (t + 1)) (w j) := Or.inr ⟨hjt, hj⟩
          obtain ⟨j', hj'⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
          subst hj'
          have hpar := (hp.legal t (by omega) _ hch _ (hw j' (by omega))).1
          have := IH (by omega) j' (by omega) hpar
          omega

/-- **路を `m` 段下る（有限区間版）**。`descend_path` の仮定を弱めたもの。 -/
theorem descend_seg {P : ℕ → Finset ℕ} {T K : ℕ} {w : ℕ → ℕ}
    (hp : Pebbling pa P T) (hw : ∀ j, j < K → w j ∈ pa (w (j + 1))) :
    ∀ m j t, j + m ≤ K → w (j + m) ∈ P t → t ≤ T →
      (∀ i, i ≤ m → w (j + i) ∉ P T) →
      ∃ s, t + m ≤ s ∧ s ≤ T ∧ w j ∈ P s := by
  intro m
  induction m with
  | zero =>
      intro j t _ h htT _
      exact ⟨t, by omega, htT, by simpa using h⟩
  | succ m IH =>
      intro j t hbd h htT hg
      have hjm : j + (m + 1) = (j + m) + 1 := by omega
      have hout : w ((j + m) + 1) ∉ P T := by
        have := hg (m + 1) le_rfl
        rwa [hjm] at this
      rw [hjm] at h
      obtain ⟨s, hs1, hs2, hs3⟩ := parent_later hp h htT hout (hw (j + m) (by omega))
      obtain ⟨s', h1, h2, h3⟩ := IH j s (by omega) hs3 hs2 (fun i hi => hg i (by omega))
      exact ⟨s', by omega, h2, h3⟩

/-- **下界定理（有限区間版）: `T ≥ 2d+3`。**

    `w 0 → ⋯ → w (d+1)` が有向路（頂点数 `d+2`）で、終点 `w (d+1)` は最終状態に
    残り、途中の `w 0 … w d` は残らない（clean 到達）とする。このとき `2d+3 ≤ T`。

    `time_lower_bound_path` と結論は同じだが、**有限の路で足りる**ので
    有限 DAG に適用できる。 -/
theorem time_lower_bound_seg {P : ℕ → Finset ℕ} {T d : ℕ} {w : ℕ → ℕ}
    (hp : Pebbling pa P T) (hw : ∀ j, j ≤ d → w j ∈ pa (w (j + 1)))
    (hsink : w (d + 1) ∈ P T) (hgone : ∀ j, j ≤ d → w j ∉ P T) :
    2 * d + 3 ≤ T := by
  have hw' : ∀ j, j < d + 1 → w j ∈ pa (w (j + 1)) := fun j hj => hw j (by omega)
  have h0 : w (d + 1) ∉ P 0 := by rw [hp.start]; simp
  obtain ⟨r, hr1, hr2, hr3, hr4⟩ := exists_placement (Nat.zero_le T) h0 hsink
  have hrd : d + 2 ≤ r := depth_bound_seg hp hw' r hr2 (d + 1) le_rfl hr4
  have hpar : w d ∈ P r := by
    have hch : Changed (P (r - 1)) (P r) (w (d + 1)) := Or.inr ⟨hr3, hr4⟩
    have heq : r - 1 + 1 = r := by omega
    have := hp.legal (r - 1) (by omega) _ (by rw [heq]; exact hch) (w d) (hw d le_rfl)
    rw [← heq]; exact this.2
  obtain ⟨s, hs1, hs2, hs3⟩ :=
    descend_seg hp hw' d 0 r (by omega) (by simpa using hpar) hr2
      (fun i hi => by simpa using hgone i hi)
  obtain ⟨r', hr'1, hr'2, _, _⟩ :=
    exists_removal hs2 hs3 (by simpa using hgone 0 (Nat.zero_le d))
  omega

/-! ## 2. 時間窓定理 -/

/-- **時間窓定理**。`w k` が時刻 `t` に居るなら `k + 1 ≤ t` かつ `t + k + 1 ≤ T`。
    すなわち存在しうる時刻は区間 `[k+1, T-k-1]` に限られ、**窓幅は `T - 2k - 1`**。

    * 下界は `depth_bound_seg`（置くには親を先に置く必要がある）
    * 上界は `descend_seg`（消すには親が要り、その親も消えねばならない） -/
theorem time_window_seg {P : ℕ → Finset ℕ} {T K : ℕ} {w : ℕ → ℕ}
    (hp : Pebbling pa P T) (hw : ∀ j, j < K → w j ∈ pa (w (j + 1)))
    {k t : ℕ} (hkK : k ≤ K) (hk : w k ∈ P t) (htT : t ≤ T)
    (hg : ∀ i, i ≤ k → w i ∉ P T) :
    k + 1 ≤ t ∧ t + k + 1 ≤ T := by
  refine ⟨depth_bound_seg hp hw t htT k hkK hk, ?_⟩
  have hk0 : w (0 + k) ∈ P t := by simpa using hk
  have hg0 : ∀ i, i ≤ k → w (0 + i) ∉ P T := by
    intro i hi; simpa using hg i hi
  obtain ⟨s, hs1, hs2, hs3⟩ := descend_seg hp hw k 0 t (by omega) hk0 htT hg0
  have hne : s ≠ T := fun hst => hg 0 (Nat.zero_le k) (hst ▸ hs3)
  omega

/-- 窓が空でないための条件。深さ `k` の頂点が**一度でも置かれる**なら `2k + 2 ≤ T`。
    対偶: `T < 2k + 2` なら、そのような頂点はどの時刻にも存在できない。 -/
theorem window_nonempty {P : ℕ → Finset ℕ} {T K : ℕ} {w : ℕ → ℕ}
    (hp : Pebbling pa P T) (hw : ∀ j, j < K → w j ∈ pa (w (j + 1)))
    {k t : ℕ} (hkK : k ≤ K) (hk : w k ∈ P t) (htT : t ≤ T)
    (hg : ∀ i, i ≤ k → w i ∉ P T) :
    2 * k + 2 ≤ T := by
  obtain ⟨h1, h2⟩ := time_window_seg hp hw hkK hk htT hg
  omega

/-! ## 3. 時間最適なら窓の両端は必ず使われる

    以下、路 `w 0 → ⋯ → w (d+1)`、終点は `P T` に残り、途中は残らない、
    `T = 2d+3`（`time_lower_bound_seg` よりこれが最小）という設定を固定する。 -/

section Tight

variable {P : ℕ → Finset ℕ} {d : ℕ} {w : ℕ → ℕ}

/-- 時間最適 `T = 2d+3` のとき、**終点は置ける最初の瞬間 `d+2` に置かれる**。
    同時に、直前の頂点 `w d` は `d+1` と `d+2` の**両方**に居る。

    証明: `w d` の窓は `[d+1, T-d-1] = [d+1, d+2]` と幅 2 しかない。
    終点を置く瞬間には `w d` が前後の両方に必要なので、置く時刻は `d+2` に確定する。 -/
theorem sink_placed_at_earliest
    (hp : Pebbling pa P (2 * d + 3)) (hw : ∀ j, j ≤ d → w j ∈ pa (w (j + 1)))
    (hsink : w (d + 1) ∈ P (2 * d + 3))
    (hg : ∀ i, i ≤ d → w i ∉ P (2 * d + 3)) :
    w (d + 1) ∈ P (d + 2) ∧ w d ∈ P (d + 1) ∧ w d ∈ P (d + 2) := by
  have hw' : ∀ j, j < d + 1 → w j ∈ pa (w (j + 1)) := fun j hj => hw j (by omega)
  have hout0 : w (d + 1) ∉ P 0 := by rw [hp.start]; simp
  obtain ⟨r, hr1, hr2, hr3, hr4⟩ :=
    exists_placement (Nat.zero_le (2 * d + 3)) hout0 hsink
  have hch : Changed (P (r - 1)) (P r) (w (d + 1)) := Or.inr ⟨hr3, hr4⟩
  have heq : r - 1 + 1 = r := by omega
  have hpar := hp.legal (r - 1) (by omega) _ (by rw [heq]; exact hch) _ (hw d le_rfl)
  have hprev : w d ∈ P (r - 1) := by rw [← heq]; exact hpar.1
  have hcur : w d ∈ P r := by rw [← heq]; exact hpar.2
  have hw1 := time_window_seg hp hw' (le_of_lt (Nat.lt_succ_self d)) hprev (by omega) hg
  have hw2 := time_window_seg hp hw' (le_of_lt (Nat.lt_succ_self d)) hcur hr2 hg
  have hr : r = d + 2 := by omega
  subst hr
  exact ⟨hr4, by simpa using hprev, hcur⟩

/-- **窓の左端は必ず使われる**: 時間最適なら `w j ∈ P (j+1)`。
    どの頂点も「置ける最初の瞬間」に置かれる。終点から下向きに帰納する。 -/
theorem present_at_window_start
    (hp : Pebbling pa P (2 * d + 3)) (hw : ∀ j, j ≤ d → w j ∈ pa (w (j + 1)))
    (hsink : w (d + 1) ∈ P (2 * d + 3))
    (hg : ∀ i, i ≤ d → w i ∉ P (2 * d + 3)) :
    ∀ j, j ≤ d + 1 → w j ∈ P (j + 1) := by
  have hw' : ∀ j, j < d + 1 → w j ∈ pa (w (j + 1)) := fun j hj => hw j (by omega)
  have key : ∀ k j, j + k = d + 1 → w j ∈ P (j + 1) := by
    intro k
    induction k with
    | zero =>
        intro j hj
        have hjd : j = d + 1 := by omega
        subst hjd
        exact (sink_placed_at_earliest hp hw hsink hg).1
    | succ k IH =>
        intro j hj
        have hnext : w (j + 1) ∈ P (j + 1 + 1) := IH (j + 1) (by omega)
        have hnot : w (j + 1) ∉ P (j + 1) := by
          intro hc
          have := depth_bound_seg hp hw' (j + 1) (by omega) (j + 1) (by omega) hc
          omega
        have hch : Changed (P (j + 1)) (P (j + 1 + 1)) (w (j + 1)) := Or.inr ⟨hnot, hnext⟩
        exact (hp.legal (j + 1) (by omega) _ hch _ (hw j (by omega))).1
  intro j hj
  exact key (d + 1 - j) j (by omega)

/-- **窓の右端も必ず使われる**: 時間最適なら `j ≤ d` について `w j ∈ P (2d + 2 - j)`。
    `T = 2d+3` なので `2d+2-j = T - j - 1` はちょうど窓の右端。
    どの頂点も「消せる最後の瞬間」まで残る。 -/
theorem present_at_window_end
    (hp : Pebbling pa P (2 * d + 3)) (hw : ∀ j, j ≤ d → w j ∈ pa (w (j + 1)))
    (hsink : w (d + 1) ∈ P (2 * d + 3))
    (hg : ∀ i, i ≤ d → w i ∉ P (2 * d + 3)) :
    ∀ j, j ≤ d → w j ∈ P (2 * d + 2 - j) := by
  have hw' : ∀ j, j < d + 1 → w j ∈ pa (w (j + 1)) := fun j hj => hw j (by omega)
  have key : ∀ k j, j + k = d → w j ∈ P (2 * d + 2 - j) := by
    intro k
    induction k with
    | zero =>
        intro j hj
        have hjd : j = d := by omega
        subst hjd
        have h2 : 2 * j + 2 - j = j + 2 := by omega
        rw [h2]
        exact (sink_placed_at_earliest hp hw hsink hg).2.2
    | succ k IH =>
        intro j hj
        have hnext : w (j + 1) ∈ P (2 * d + 2 - (j + 1)) := IH (j + 1) (by omega)
        have hnot : w (j + 1) ∉ P (2 * d + 2 - j) := by
          intro hc
          have := time_window_seg hp hw' (show j + 1 ≤ d + 1 by omega) hc (by omega)
            (fun i hi => hg i (by omega))
          omega
        have heq : 2 * d + 2 - (j + 1) + 1 = 2 * d + 2 - j := by omega
        have hch : Changed (P (2 * d + 2 - (j + 1))) (P (2 * d + 2 - (j + 1) + 1)) (w (j + 1)) :=
          Or.inl ⟨hnext, by rw [heq]; exact hnot⟩
        have := (hp.legal (2 * d + 2 - (j + 1)) (by omega) _ hch _ (hw j (by omega))).2
        rwa [heq] at this
  intro j hj
  exact key (d - j) j (by omega)

/-- **窓の左端では 2 手続けて存在する**: `w j ∈ P (j+1)` かつ `w j ∈ P (j+2)`。

    理由: `w (j+1)` は時刻 `j+2` に置かれる（`present_at_window_start`）が、
    `j+1` にはまだ置けない（深さの下界）。置く瞬間には親 `w j` が**前後の両方**に要る。 -/
theorem present_at_start_two
    (hp : Pebbling pa P (2 * d + 3)) (hw : ∀ j, j ≤ d → w j ∈ pa (w (j + 1)))
    (hsink : w (d + 1) ∈ P (2 * d + 3))
    (hg : ∀ i, i ≤ d → w i ∉ P (2 * d + 3)) :
    ∀ j, j ≤ d → w j ∈ P (j + 1) ∧ w j ∈ P (j + 2) := by
  have hw' : ∀ j, j < d + 1 → w j ∈ pa (w (j + 1)) := fun j hj => hw j (by omega)
  intro j hj
  have hnext : w (j + 1) ∈ P (j + 1 + 1) :=
    present_at_window_start hp hw hsink hg (j + 1) (by omega)
  have hnot : w (j + 1) ∉ P (j + 1) := by
    intro hc
    have := depth_bound_seg hp hw' (j + 1) (by omega) (j + 1) (by omega) hc
    omega
  have hch : Changed (P (j + 1)) (P (j + 1 + 1)) (w (j + 1)) := Or.inr ⟨hnot, hnext⟩
  have := hp.legal (j + 1) (by omega) _ hch _ (hw j (by omega))
  exact ⟨this.1, this.2⟩

/-- **窓の右端でも 2 手続けて存在する**: `w j ∈ P (2d+1-j)` かつ `w j ∈ P (2d+2-j)`。 -/
theorem present_at_end_two
    (hp : Pebbling pa P (2 * d + 3)) (hw : ∀ j, j ≤ d → w j ∈ pa (w (j + 1)))
    (hsink : w (d + 1) ∈ P (2 * d + 3))
    (hg : ∀ i, i ≤ d → w i ∉ P (2 * d + 3)) :
    ∀ j, j ≤ d → w j ∈ P (2 * d + 1 - j) ∧ w j ∈ P (2 * d + 2 - j) := by
  have hw' : ∀ j, j < d + 1 → w j ∈ pa (w (j + 1)) := fun j hj => hw j (by omega)
  intro j hj
  rcases Nat.lt_or_ge j d with hlt | hge
  · -- `j < d`: `w (j+1)` が `2d+1-j → 2d+2-j` で消える瞬間に親 `w j` が両方に要る。
    have hnext : w (j + 1) ∈ P (2 * d + 2 - (j + 1)) :=
      present_at_window_end hp hw hsink hg (j + 1) (by omega)
    have hnot : w (j + 1) ∉ P (2 * d + 2 - j) := by
      intro hc
      have := time_window_seg hp hw' (show j + 1 ≤ d + 1 by omega) hc (by omega)
        (fun i hi => hg i (by omega))
      omega
    have heq : 2 * d + 2 - (j + 1) + 1 = 2 * d + 2 - j := by omega
    have heq2 : 2 * d + 2 - (j + 1) = 2 * d + 1 - j := by omega
    have hch : Changed (P (2 * d + 2 - (j + 1))) (P (2 * d + 2 - (j + 1) + 1)) (w (j + 1)) :=
      Or.inl ⟨hnext, by rw [heq]; exact hnot⟩
    have hpar := hp.legal (2 * d + 2 - (j + 1)) (by omega) _ hch _ (hw j (by omega))
    exact ⟨by rw [← heq2]; exact hpar.1, by rw [← heq]; exact hpar.2⟩
  · -- `j = d`: 窓幅は 2 で、両端はまさに `d+1` と `d+2`。
    have hjd : j = d := by omega
    subst hjd
    have h := sink_placed_at_earliest hp hw hsink hg
    have e1 : 2 * j + 1 - j = j + 1 := by omega
    have e2 : 2 * j + 2 - j = j + 2 := by omega
    exact ⟨by rw [e1]; exact h.2.1, by rw [e2]; exact h.2.2⟩

/-- **余裕ゼロ定理**。時間最適 `T = 2d+3` の可逆ペブリングでは、路上の各頂点
    `w j`（`j ≤ d`）について

    * 存在しうる時刻は `[j+1, 2d+2-j]` に限られ、
    * その**両端では必ず存在している**。

    窓幅は `2d+2-2j`。深さが 1 増えるごとに窓は 2 だけ狭くなる。
    とくに最深の消える頂点 `w d` の窓は `[d+1, d+2]` と幅 2 しかない。 -/
theorem no_slack
    (hp : Pebbling pa P (2 * d + 3)) (hw : ∀ j, j ≤ d → w j ∈ pa (w (j + 1)))
    (hsink : w (d + 1) ∈ P (2 * d + 3))
    (hg : ∀ i, i ≤ d → w i ∉ P (2 * d + 3)) :
    ∀ j, j ≤ d →
      w j ∈ P (j + 1) ∧ w j ∈ P (2 * d + 2 - j) ∧
      (∀ t, t ≤ 2 * d + 3 → w j ∈ P t → j + 1 ≤ t ∧ t ≤ 2 * d + 2 - j) := by
  have hw' : ∀ j, j < d + 1 → w j ∈ pa (w (j + 1)) := fun j hj => hw j (by omega)
  intro j hj
  refine ⟨present_at_window_start hp hw hsink hg j (by omega),
          present_at_window_end hp hw hsink hg j hj, ?_⟩
  intro t htT hjt
  have := time_window_seg hp hw' (show j ≤ d + 1 by omega) hjt htT
    (fun i hi => hg i (by omega))
  omega

end Tight

/-! ## 3.9 深さ関数版（路を明示しない一般形）

    ここまでの補題は路 `w` を明示的に与える必要があった。実用（ピラミッド等）では
    「深さ関数 `dep` が longest path で与えられている」ほうが扱いやすい。
    `dep` について 3 つの仮定を置けば、路を経由せずに同じ結論が出る。

    * `hclosed` — 親は `V` の中にある
    * `hdown`   — 深さ 0 でなければ**深さがちょうど 1 小さい親**を持つ（`dep` が longest path）
    * `hup`     — sink 以外は**深さがちょうど 1 大きい子**を持つ（全頂点が sink の祖先） -/

section DepBased

variable {P : ℕ → Finset ℕ} {V : Finset ℕ} {dep : ℕ → ℕ} {T : ℕ}

/-- **深さの下界（深さ関数版）**: `v ∈ P t → dep v + 1 ≤ t`。路を与えなくてよい。 -/
theorem depth_bound_dep
    (hp : Pebbling pa P T)
    (hclosed : ∀ v ∈ V, ∀ u ∈ pa v, u ∈ V)
    (hdown : ∀ v ∈ V, dep v ≠ 0 → ∃ u ∈ pa v, dep u + 1 = dep v) :
    ∀ t, t ≤ T → ∀ v ∈ V, v ∈ P t → dep v + 1 ≤ t := by
  intro t
  induction t with
  | zero =>
      intro _ v _ hv
      rw [hp.start] at hv; simp at hv
  | succ t IH =>
      intro htT v hvV hv
      by_cases hvt : v ∈ P t
      · have := IH (by omega) v hvV hvt; omega
      · rcases Nat.eq_zero_or_pos (dep v) with h0 | hpos
        · omega
        · obtain ⟨u, hu, hdu⟩ := hdown v hvV (by omega)
          have hch : Changed (P t) (P (t + 1)) v := Or.inr ⟨hvt, hv⟩
          have hut : u ∈ P t := (hp.legal t (by omega) v hch u hu).1
          have := IH (by omega) u (hclosed v hvV u hu) hut
          omega

/-- **窓の上界（深さ関数版）**: 最終状態に残らない `v` は `t + dep v + 1 ≤ T` を満たす。 -/
theorem window_upper_dep {sink : ℕ}
    (hp : Pebbling pa P T)
    (hclosed : ∀ v ∈ V, ∀ u ∈ pa v, u ∈ V)
    (hdown : ∀ v ∈ V, dep v ≠ 0 → ∃ u ∈ pa v, dep u + 1 = dep v)
    (hmax : ∀ v ∈ V, dep v ≤ dep sink)
    (hgone : ∀ v ∈ V, v ≠ sink → v ∉ P T) :
    ∀ k v, dep v = k → v ∈ V → v ≠ sink → ∀ t, t ≤ T → v ∈ P t → t + dep v + 1 ≤ T := by
  intro k
  induction k with
  | zero =>
      intro v hdv hvV hvs t htT hvt
      obtain ⟨r, hr1, hr2, _, _⟩ := exists_removal htT hvt (hgone v hvV hvs)
      omega
  | succ k IH =>
      intro v hdv hvV hvs t htT hvt
      obtain ⟨r, hr1, hr2, hr3, hr4⟩ := exists_removal htT hvt (hgone v hvV hvs)
      obtain ⟨u, hu, hdu⟩ := hdown v hvV (by omega)
      have hch : Changed (P (r - 1)) (P r) v := Or.inl ⟨hr3, hr4⟩
      have heq : r - 1 + 1 = r := by omega
      have hur : u ∈ P r := by
        have := hp.legal (r - 1) (by omega) v (by rw [heq]; exact hch) u hu
        rw [← heq]; exact this.2
      have huV : u ∈ V := hclosed v hvV u hu
      have hus : u ≠ sink := by
        intro he
        have h1 : dep v ≤ dep sink := hmax v hvV
        rw [he] at hdu
        omega
      have := IH u (by omega) huV hus r hr2 hur
      omega

/-- **窓（深さ関数版）**: `sink` 以外の `v` は `[dep v + 1, T - dep v - 1]` にしか居ない。 -/
theorem time_window_dep {sink : ℕ}
    (hp : Pebbling pa P T)
    (hclosed : ∀ v ∈ V, ∀ u ∈ pa v, u ∈ V)
    (hdown : ∀ v ∈ V, dep v ≠ 0 → ∃ u ∈ pa v, dep u + 1 = dep v)
    (hmax : ∀ v ∈ V, dep v ≤ dep sink)
    (hgone : ∀ v ∈ V, v ≠ sink → v ∉ P T)
    {v t : ℕ} (hvV : v ∈ V) (hvs : v ≠ sink) (htT : t ≤ T) (hvt : v ∈ P t) :
    dep v + 1 ≤ t ∧ t + dep v + 1 ≤ T :=
  ⟨depth_bound_dep hp hclosed hdown t htT v hvV hvt,
   window_upper_dep hp hclosed hdown hmax hgone (dep v) v rfl hvV hvs t htT hvt⟩

/-- **sink は最早時刻 `D+1` に置かれ、以後消えない（深さ関数版）**。`T = 2D+1` を仮定する。 -/
theorem sink_at_and_stays_dep {sink D : ℕ}
    (hp : Pebbling pa P (2 * D + 1))
    (hclosed : ∀ v ∈ V, ∀ u ∈ pa v, u ∈ V)
    (hdown : ∀ v ∈ V, dep v ≠ 0 → ∃ u ∈ pa v, dep u + 1 = dep v)
    (hmax : ∀ v ∈ V, dep v ≤ dep sink)
    (hgone : ∀ v ∈ V, v ≠ sink → v ∉ P (2 * D + 1))
    (hsV : sink ∈ V) (hds : dep sink = D) (hD : 1 ≤ D)
    (hsin : sink ∈ P (2 * D + 1)) :
    ∀ t, D + 1 ≤ t → t ≤ 2 * D + 1 → sink ∈ P t := by
  obtain ⟨u, hu, hdu⟩ := hdown sink hsV (by omega)
  have huV : u ∈ V := hclosed sink hsV u hu
  have hus : u ≠ sink := by intro he; rw [he] at hdu; omega
  have hout0 : sink ∉ P 0 := by rw [hp.start]; simp
  obtain ⟨r, hr1, hr2, hr3, hr4⟩ := exists_placement (Nat.zero_le (2 * D + 1)) hout0 hsin
  have hchp : Changed (P (r - 1)) (P r) sink := Or.inr ⟨hr3, hr4⟩
  have heqp : r - 1 + 1 = r := by omega
  have hupar := hp.legal (r - 1) (by omega) sink (by rw [heqp]; exact hchp) u hu
  have hur : u ∈ P r := by rw [← heqp]; exact hupar.2
  have hlow : D + 1 ≤ r := by
    have := depth_bound_dep hp hclosed hdown r hr2 sink hsV hr4
    omega
  have hupp := window_upper_dep hp hclosed hdown hmax hgone (dep u) u rfl huV hus r hr2 hur
  have hrD : r = D + 1 := by omega
  subst hrD
  have hstart : sink ∈ P (D + 1) := hr4
  intro t ht1 ht2
  by_contra hno
  obtain ⟨s, hs1, hs2, hs3, hs4⟩ := exists_removal ht1 hstart hno
  have hchr : Changed (P (s - 1)) (P s) sink := Or.inl ⟨hs3, hs4⟩
  have heqr : s - 1 + 1 = s := by omega
  have hus2 := hp.legal (s - 1) (by omega) sink (by rw [heqr]; exact hchr) u hu
  have hus3 : u ∈ P s := by rw [← heqr]; exact hus2.2
  have := window_upper_dep hp hclosed hdown hmax hgone (dep u) u rfl huV hus s (by omega) hus3
  omega

/-- **窓の左端は必ず使われる（深さ関数版）**: `v ∈ P (dep v + 1)` かつ `v ∈ P (dep v + 2)`。

    追加の仮定 `hup`（sink 以外は深さ +1 の子を持つ）を置く。ピラミッド・鎖は満たす。
    これで**ピラミッドにも両端強制が正当化される**（鎖だけでなく）。 -/
theorem present_at_dep {sink D : ℕ}
    (hp : Pebbling pa P (2 * D + 1))
    (hclosed : ∀ v ∈ V, ∀ u ∈ pa v, u ∈ V)
    (hdown : ∀ v ∈ V, dep v ≠ 0 → ∃ u ∈ pa v, dep u + 1 = dep v)
    (hmax : ∀ v ∈ V, dep v ≤ dep sink)
    (huniq : ∀ v ∈ V, dep v = D → v = sink)
    (hgone : ∀ v ∈ V, v ≠ sink → v ∉ P (2 * D + 1))
    (hsV : sink ∈ V) (hds : dep sink = D) (hD : 1 ≤ D)
    (hsin : sink ∈ P (2 * D + 1))
    (hup : ∀ v ∈ V, v ≠ sink → ∃ c ∈ V, v ∈ pa c ∧ dep c = dep v + 1) :
    ∀ v ∈ V, v ∈ P (dep v + 1) ∧ v ∈ P (dep v + 2) := by
  have key : ∀ m v, v ∈ V → dep v + m = D → v ∈ P (dep v + 1) ∧ v ∈ P (dep v + 2) := by
    intro m
    induction m with
    | zero =>
        intro v hvV hm
        have hvs : v = sink := huniq v hvV (by omega)
        subst hvs
        have hstay := sink_at_and_stays_dep hp hclosed hdown hmax hgone hsV hds hD hsin
        rw [hds]
        exact ⟨hstay (D + 1) (le_refl _) (by omega), hstay (D + 2) (by omega) (by omega)⟩
    | succ m IH =>
        intro v hvV hm
        have hvs : v ≠ sink := by
          intro he; subst he; omega
        obtain ⟨c, hcV, hvc, hdc⟩ := hup v hvV hvs
        have hIH := IH c hcV (by omega)
        have hcnot : c ∉ P (dep v + 1) := by
          intro hcc
          have := depth_bound_dep hp hclosed hdown (dep v + 1) (by omega) c hcV hcc
          omega
        have hcin : c ∈ P (dep v + 1 + 1) := by
          have h := hIH.1; rw [hdc] at h; exact h
        have hch : Changed (P (dep v + 1)) (P (dep v + 1 + 1)) c := Or.inr ⟨hcnot, hcin⟩
        have := hp.legal (dep v + 1) (by omega) c hch v hvc
        exact ⟨this.1, this.2⟩
  intro v hvV
  exact key (D - dep v) v hvV (by have := hmax v hvV; omega)

/-- **窓の右端も必ず使われる（深さ関数版）**: `sink` 以外の `v` は
    `2D - dep v = T - dep v - 1`（窓の右端）と、その 1 つ内側 `2D - dep v - 1` に居る。

    証明: sink は時刻 `D+1` に置かれ、その瞬間に**すべての親**が `D` と `D+1` の両方に
    要る。以下、深さを 1 ずつ下げながら「子が消える瞬間には親が要る」を繰り返す。 -/
theorem present_at_end_dep {sink D : ℕ}
    (hp : Pebbling pa P (2 * D + 1))
    (hclosed : ∀ v ∈ V, ∀ u ∈ pa v, u ∈ V)
    (hdown : ∀ v ∈ V, dep v ≠ 0 → ∃ u ∈ pa v, dep u + 1 = dep v)
    (hmax : ∀ v ∈ V, dep v ≤ dep sink)
    (huniq : ∀ v ∈ V, dep v = D → v = sink)
    (hgone : ∀ v ∈ V, v ≠ sink → v ∉ P (2 * D + 1))
    (hsV : sink ∈ V) (hds : dep sink = D) (hD : 1 ≤ D)
    (hsin : sink ∈ P (2 * D + 1))
    (hup : ∀ v ∈ V, v ≠ sink → ∃ c ∈ V, v ∈ pa c ∧ dep c = dep v + 1) :
    ∀ v ∈ V, v ≠ sink →
      v ∈ P (2 * D - dep v) ∧ v ∈ P (2 * D - dep v - 1) := by
  have hstay := sink_at_and_stays_dep hp hclosed hdown hmax hgone hsV hds hD hsin
  -- sink は `D` には居ない（深さの下界）が `D+1` には居る。置く瞬間に親が両方に要る。
  have hsnot : sink ∉ P D := by
    intro hc
    have := depth_bound_dep hp hclosed hdown D (by omega) sink hsV hc
    omega
  have hsyes : sink ∈ P (D + 1) := hstay (D + 1) (le_refl _) (by omega)
  have hchs : Changed (P D) (P (D + 1)) sink := Or.inr ⟨hsnot, hsyes⟩
  have key : ∀ m v, v ∈ V → v ≠ sink → dep v + m = D →
      v ∈ P (2 * D - dep v) ∧ v ∈ P (2 * D - dep v - 1) := by
    intro m
    induction m with
    | zero =>
        intro v hvV hvs hm
        exact absurd (huniq v hvV (by omega)) hvs
    | succ m IH =>
        intro v hvV hvs hm
        obtain ⟨c, hcV, hvc, hdc⟩ := hup v hvV hvs
        by_cases hcs : c = sink
        · -- `c = sink`: sink を置く瞬間に親 `v` が `D` と `D+1` の両方に要る。
          subst hcs
          have hpar := hp.legal D (by omega) _ hchs v hvc
          have e1 : 2 * D - dep v = D + 1 := by omega
          have e2 : 2 * D - dep v - 1 = D := by omega
          exact ⟨by rw [e1]; exact hpar.2, by rw [e2]; exact hpar.1⟩
        · -- `c ≠ sink`: 帰納法の仮定より `c` は右端に居て、その次には居られない。
          have hIH := IH c hcV hcs (by omega)
          have hcnot : c ∉ P (2 * D - dep c + 1) := by
            intro hcc
            have := window_upper_dep hp hclosed hdown hmax hgone (dep c) c rfl hcV hcs
              (2 * D - dep c + 1) (by omega) hcc
            omega
          have hch : Changed (P (2 * D - dep c)) (P (2 * D - dep c + 1)) c :=
            Or.inl ⟨hIH.1, hcnot⟩
          have hpar := hp.legal (2 * D - dep c) (by omega) _ hch v hvc
          have e1 : 2 * D - dep v = 2 * D - dep c + 1 := by omega
          have e2 : 2 * D - dep v - 1 = 2 * D - dep c := by omega
          exact ⟨by rw [e1]; exact hpar.2, by rw [e2]; exact hpar.1⟩
  intro v hvV hvs
  exact key (D - dep v) v hvV hvs (by have := hmax v hvV; omega)

end DepBased

/-! ## 3.95 `layered` より良い構成: 交互構成

    `layered` は全頂点が窓を丸ごと居座るのでピークが `|V|` になる。SAT の最適解を見ると
    実際には**一部の頂点だけが常駐し、残りは往路と復路で 2 回計算される**。
    その最も単純な形（1 段の交互）を構成として証明する。

    * sink         — 時刻 `d+1` 以降ずっと居る
    * **奇数深さ** — 窓 `[dep+1, 2d-dep]` を丸ごと占有（チェックポイント）
    * **偶数深さ** — 両端の強制ブロック `[dep+1, dep+2]` と `[2d-dep-1, 2d-dep]` のみ

    実測（`tests/test_alt_construction.py`・32 例で合法を確認）:
    鎖 `n=20` でピーク 11（`layered` は 20）、ピラミッド `h=14` で 53（`layered` は 105）。
    **ピラミッド `h ≤ 8` では厳密な最適値に一致する。**

    仮定は `layered` より 1 つ強い: **親の深さはちょうど 1 小さい**（`hpa1`）。鎖・ピラミッドは満たす。 -/

section Alt

variable {V : Finset ℕ} {dep : ℕ → ℕ} {sink d : ℕ}

/-- 交互構成での在否。 -/
def altMem (dep : ℕ → ℕ) (sink d t v : ℕ) : Prop :=
  if v = sink then d + 1 ≤ t
  else if dep v % 2 = 1 then dep v + 1 ≤ t ∧ t ≤ 2 * d - dep v
  else (dep v + 1 ≤ t ∧ t ≤ dep v + 2) ∨ (2 * d - dep v - 1 ≤ t ∧ t ≤ 2 * d - dep v)

instance altMemDec (dep : ℕ → ℕ) (sink d t : ℕ) :
    DecidablePred (altMem dep sink d t) := by
  intro v; unfold altMem; infer_instance

/-- 交互構成。 -/
def alt (V : Finset ℕ) (dep : ℕ → ℕ) (sink d t : ℕ) : Finset ℕ :=
  V.filter (altMem dep sink d t)

theorem mem_alt {t v : ℕ} :
    v ∈ alt V dep sink d t ↔ v ∈ V ∧ altMem dep sink d t v := by
  simp [alt, Finset.mem_filter]

/-- sink の在否は `d + 1 ≤ t` だけで決まる。 -/
theorem altMem_sink {t : ℕ} : altMem dep sink d t sink ↔ d + 1 ≤ t := by
  unfold altMem; rw [if_pos rfl]

/-- sink 以外の在否はパリティで決まる 2 通り。`if` を剥がして算術だけにする。 -/
theorem altMem_ne {t v : ℕ} (hvs : v ≠ sink) :
    altMem dep sink d t v ↔
      (if dep v % 2 = 1 then dep v + 1 ≤ t ∧ t ≤ 2 * d - dep v
       else (dep v + 1 ≤ t ∧ t ≤ dep v + 2) ∨
            (2 * d - dep v - 1 ≤ t ∧ t ≤ 2 * d - dep v)) := by
  unfold altMem; rw [if_neg hvs]

/-- sink 以外の頂点の深さは `d` より真に小さい。 -/
theorem dep_lt_of_ne_sink (hmax : ∀ v ∈ V, dep v ≤ d)
    (huniq : ∀ v ∈ V, dep v = d → v = sink) {v : ℕ} (hvV : v ∈ V) (hvs : v ≠ sink) :
    dep v < d :=
  match Nat.lt_or_ge (dep v) d with
  | Or.inl h => h
  | Or.inr h => absurd (huniq v hvV (Nat.le_antisymm (hmax v hvV) h)) hvs

/-- **交互構成は合法なペブリングである。** -/
theorem alt_legal
    (hs : sink ∈ V) (hds : dep sink = d) (hd : 1 ≤ d)
    (hmax : ∀ v ∈ V, dep v ≤ d)
    (huniq : ∀ v ∈ V, dep v = d → v = sink)
    (hpaV : ∀ v ∈ V, ∀ u ∈ pa v, u ∈ V)
    (hpa1 : ∀ v ∈ V, ∀ u ∈ pa v, dep u + 1 = dep v) :
    Pebbling pa (alt V dep sink d) (2 * d + 1) := by
  constructor
  · -- 時刻 0 では誰も居ない。
    ext v
    constructor
    · intro hv
      obtain ⟨hvV, hm⟩ := mem_alt.mp hv
      exfalso
      by_cases hvs : v = sink
      · subst hvs; rw [altMem_sink] at hm; omega
      · have hlt := dep_lt_of_ne_sink hmax huniq hvV hvs
        rw [altMem_ne hvs] at hm
        revert hm; split <;> omega
    · intro hv; simp at hv
  · intro t _ v hch u hu
    have hvV : v ∈ V := by
      rcases hch with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact (mem_alt.mp h1).1
      · exact (mem_alt.mp h2).1
    have huV : u ∈ V := hpaV v hvV u hu
    have hpa : dep u + 1 = dep v := hpa1 v hvV u hu
    have hvd : dep v ≤ d := hmax v hvV
    have hus : u ≠ sink := by intro he; subst he; omega
    have hchm : (altMem dep sink d t v ∧ ¬ altMem dep sink d (t + 1) v) ∨
                (¬ altMem dep sink d t v ∧ altMem dep sink d (t + 1) v) := by
      rcases hch with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨(mem_alt.mp h1).2, fun hc => h2 (mem_alt.mpr ⟨hvV, hc⟩)⟩
      · exact Or.inr ⟨fun hc => h1 (mem_alt.mpr ⟨hvV, hc⟩), (mem_alt.mp h2).2⟩
    -- 親の側の主張は「sink でない頂点の在否」なので `altMem_ne` で算術に落ちる。
    refine ⟨mem_alt.mpr ⟨huV, (altMem_ne hus).mpr ?_⟩,
            mem_alt.mpr ⟨huV, (altMem_ne hus).mpr ?_⟩⟩ <;>
    · by_cases hvs : v = sink
      · -- v = sink: 変化は t = d の 1 回だけ。親の深さは d-1。
        rw [hvs] at hchm hpa
        rw [altMem_sink, altMem_sink] at hchm
        rw [hds] at hpa
        split <;> omega
      · -- v ≠ sink: パリティで 2 通り。親のパリティは逆。
        have hvlt := dep_lt_of_ne_sink hmax huniq hvV hvs
        rw [altMem_ne hvs, altMem_ne hvs] at hchm
        revert hchm
        split <;> (intro hchm; revert hchm; split <;> (intro hchm; omega))

/-- **終状態は `{sink}`。** -/
theorem alt_final
    (hs : sink ∈ V) (hds : dep sink = d) (hd : 1 ≤ d)
    (hmax : ∀ v ∈ V, dep v ≤ d)
    (huniq : ∀ v ∈ V, dep v = d → v = sink) :
    alt V dep sink d (2 * d + 1) = {sink} := by
  ext v
  simp only [mem_alt, Finset.mem_singleton]
  constructor
  · rintro ⟨hvV, hm⟩
    by_contra hvs
    have hvlt := dep_lt_of_ne_sink hmax huniq hvV hvs
    rw [altMem_ne hvs] at hm
    revert hm; split <;> omega
  · rintro rfl
    exact ⟨hs, altMem_sink.mpr (by omega)⟩

/-- **交互構成による時間最適ペブリング（`layered` の改良）。**
    同じ時間 `2d+1` で終状態も `{sink}` だが、**同時に居る頂点はずっと少ない**。 -/
theorem alt_par_time_exact
    (hs : sink ∈ V) (hds : dep sink = d) (hd : 1 ≤ d)
    (hmax : ∀ v ∈ V, dep v ≤ d)
    (huniq : ∀ v ∈ V, dep v = d → v = sink)
    (hpaV : ∀ v ∈ V, ∀ u ∈ pa v, u ∈ V)
    (hpa1 : ∀ v ∈ V, ∀ u ∈ pa v, dep u + 1 = dep v) :
    Pebbling pa (alt V dep sink d) (2 * d + 1) ∧
    alt V dep sink d (2 * d + 1) = {sink} :=
  ⟨alt_legal hs hds hd hmax huniq hpaV hpa1, alt_final hs hds hd hmax huniq⟩

end Alt

/-! ### 交互構成の非空虚性と、`layered` より真に良いこと

    鎖 `0 → 1 → 2 → 3 → 4`（頂点 5・深さ 4・`T = 9`）で実際に適用する。
    `layered` はピーク 5（= `|V|`）だが、交互構成はピーク **4**。 -/

section AltWitness

/-- 鎖 `0 → 1 → 2 → 3 → 4`。 -/
def paC : ℕ → Finset ℕ := fun v => if v = 0 then ∅ else {v - 1}
def depC : ℕ → ℕ := fun v => v
def VC : Finset ℕ := {0, 1, 2, 3, 4}

/-- 交互構成が鎖に適用でき、時間最適 `T = 9 = 2·4+1` で終状態が `{4}`。 -/
theorem alt_chain5 :
    Pebbling paC (alt VC depC 4 4) (2 * 4 + 1) ∧
    alt VC depC 4 4 (2 * 4 + 1) = {4} := by
  apply alt_par_time_exact
  · decide          -- sink ∈ V
  · decide          -- dep sink = d
  · decide          -- 1 ≤ d
  · decide          -- ∀ v ∈ V, dep v ≤ d
  · decide          -- 最深は sink のみ
  · decide          -- 親は V の中
  · decide          -- 親の深さはちょうど 1 小さい

/-- **ピークの比較**: `layered` は 5（= `|V|`）を使う時刻があるが、交互構成は 4 で済む。 -/
theorem alt_beats_layered :
    (layered VC depC 4 4 5).card = 5 ∧
    (∀ t, t ≤ 9 → (alt VC depC 4 4 t).card ≤ 4) ∧
    (alt VC depC 4 4 5).card = 4 := by
  refine ⟨by decide, ?_, by decide⟩
  intro t ht
  interval_cases t <;> decide

end AltWitness

/-! ## 3.97 レベル一様なスケジュールの持ち上げ

    `alt` は「深さごとに同じ振る舞いをする」構成の一例だった。一般に、

    **深さの鎖 `0 → 1 → ⋯ → d` の合法なペブリング `Q` は、そのまま DAG の
    合法なペブリング（深さ `k` の頂点は `k ∈ Q t` のとき在る）に持ち上がる。**

    これで「レベル一様な戦略の最適値」（`scripts/q2_level_weighted.py` が CP-SAT で
    厳密に解く量）が**すべて証明つきの上界**になる。`alt` はその特別な `Q` の場合。

    実測: この上界はピラミッド `h ≤ 8` で厳密な最適値に一致し、`h = 9` で初めて
    +1 ずれる（`data/q2_parallel_findings.md`）。**レベル対称性が破れる onset が h=9。** -/

section Lift

variable {V : Finset ℕ} {dep : ℕ → ℕ} {sink d : ℕ}

/-- 深さの鎖の親関数。 -/
def chainPa : ℕ → Finset ℕ := fun k => if k = 0 then ∅ else {k - 1}

/-- 深さの集合 `S` を「その深さの頂点全部」に持ち上げる。 -/
def lift (V : Finset ℕ) (dep : ℕ → ℕ) (Q : ℕ → Finset ℕ) (t : ℕ) : Finset ℕ :=
  V.filter (fun v => dep v ∈ Q t)

theorem mem_lift {Q : ℕ → Finset ℕ} {t v : ℕ} :
    v ∈ lift V dep Q t ↔ v ∈ V ∧ dep v ∈ Q t := by
  simp [lift, Finset.mem_filter]

/-- **持ち上げ定理**: 深さの鎖の合法なペブリングは DAG の合法なペブリングになる。 -/
theorem lift_pebbling {Q : ℕ → Finset ℕ} {T : ℕ}
    (hQ : Pebbling chainPa Q T)
    (hpaV : ∀ v ∈ V, ∀ u ∈ pa v, u ∈ V)
    (hpa1 : ∀ v ∈ V, ∀ u ∈ pa v, dep u + 1 = dep v) :
    Pebbling pa (lift V dep Q) T := by
  constructor
  · ext v
    constructor
    · intro hv
      obtain ⟨_, hm⟩ := mem_lift.mp hv
      rw [hQ.start] at hm
      simp at hm
    · intro hv; simp at hv
  · intro t ht v hch u hu
    have hvV : v ∈ V := by
      rcases hch with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact (mem_lift.mp h1).1
      · exact (mem_lift.mp h2).1
    have huV : u ∈ V := hpaV v hvV u hu
    have hpa : dep u + 1 = dep v := hpa1 v hvV u hu
    -- `dep v` は鎖の側で変化している。
    have hchQ : Changed (Q t) (Q (t + 1)) (dep v) := by
      rcases hch with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨(mem_lift.mp h1).2, fun hc => h2 (mem_lift.mpr ⟨hvV, hc⟩)⟩
      · exact Or.inr ⟨fun hc => h1 (mem_lift.mpr ⟨hvV, hc⟩), (mem_lift.mp h2).2⟩
    -- 鎖の合法性より、`dep v` の親 `dep v - 1 = dep u` は前後の両方に居る。
    have hmemPa : dep u ∈ chainPa (dep v) := by
      unfold chainPa
      rw [if_neg (by omega)]
      simp
      omega
    have := hQ.legal t ht (dep v) hchQ (dep u) hmemPa
    exact ⟨mem_lift.mpr ⟨huV, this.1⟩, mem_lift.mpr ⟨huV, this.2⟩⟩

/-- 終状態も持ち上がる: 鎖が `{d}` で終われば DAG は `{sink}` で終わる。 -/
theorem lift_final {Q : ℕ → Finset ℕ} {T : ℕ}
    (hQT : Q T = {d}) (hs : sink ∈ V) (hds : dep sink = d)
    (huniq : ∀ v ∈ V, dep v = d → v = sink) :
    lift V dep Q T = {sink} := by
  ext v
  simp only [mem_lift, hQT, Finset.mem_singleton]
  constructor
  · rintro ⟨hvV, hm⟩
    exact huniq v hvV hm
  · rintro rfl
    exact ⟨hs, hds⟩

/-- **持ち上げによる時間最適ペブリング。**
    深さの鎖を時間 `T` で clean にペブリングできれば、DAG も同じ時間でできる。
    ピークは `∑_{k ∈ Q t} #{v ∈ V : dep v = k}` なので、**深さごとの頂点数を重みにした
    鎖のペブリング問題**を解けばよい（`scripts/q2_level_weighted.py`）。 -/
theorem lift_par_time {Q : ℕ → Finset ℕ} {T : ℕ}
    (hQ : Pebbling chainPa Q T) (hQT : Q T = {d})
    (hs : sink ∈ V) (hds : dep sink = d)
    (huniq : ∀ v ∈ V, dep v = d → v = sink)
    (hpaV : ∀ v ∈ V, ∀ u ∈ pa v, u ∈ V)
    (hpa1 : ∀ v ∈ V, ∀ u ∈ pa v, dep u + 1 = dep v) :
    Pebbling pa (lift V dep Q) T ∧ lift V dep Q T = {sink} :=
  ⟨lift_pebbling hQ hpaV hpa1, lift_final hQT hs hds huniq⟩

end Lift

/-! ### 持ち上げの非空虚性

    深さの鎖（`d = 1`）に `layered` を当てたものを `paD`（`0 → 2 ← 1`）へ持ち上げる。
    `paD` は sink が親を **2 つ**持つので、**1 本の鎖のスケジュールが分岐 DAG を動かす**
    ことがそのまま見える。鎖側の合法性は `par_time_exact_dag` から来るので手証明は要らない。 -/

section LiftWitness

/-- 深さの鎖 `0 → 1` の頂点集合。 -/
def VL : Finset ℕ := {0, 1}

/-- 深さの鎖のスケジュール（`layered` を鎖に当てたもの）。 -/
def QL : ℕ → Finset ℕ := layered VL id 1 1

theorem QL_pebbling : Pebbling chainPa QL 3 ∧ QL 3 = {1} := by
  have h := par_time_exact_dag (pa := chainPa) (V := VL) (dep := id) (sink := 1) (d := 1)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  exact ⟨by simpa [QL] using h.1, by simpa [QL] using h.2⟩

/-- 実際の値: `∅ → {0} → {0,1} → {1}`。 -/
theorem QL_values : QL 0 = ∅ ∧ QL 1 = {0} ∧ QL 2 = {0, 1} ∧ QL 3 = {1} := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- 持ち上げると `paD` の合法なペブリングになり、終状態は `{2}`。 -/
theorem lift_paD :
    Pebbling paD (lift VD depD QL) 3 ∧ lift VD depD QL 3 = {2} := by
  apply lift_par_time (d := 1) (sink := 2) QL_pebbling.1 QL_pebbling.2
  · decide          -- sink ∈ V
  · decide          -- dep sink = d
  · decide          -- 最深は sink のみ
  · decide          -- 親は V の中
  · decide          -- 親の深さはちょうど 1 小さい

/-- 持ち上げた配置列は `∅ → {0,1} → {0,1,2} → {2}` になる。
    鎖の 1 頂点「深さ 0」が DAG の **2 頂点** `{0,1}` に展開されている。 -/
theorem lift_paD_values :
    lift VD depD QL 0 = ∅ ∧ lift VD depD QL 1 = {0, 1} ∧
    lift VD depD QL 2 = {0, 1, 2} ∧ lift VD depD QL 3 = {2} := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

end LiftWitness

/-! ## 3.98 ピークの下界（窓定理の系）

    `present_at_dep` は「どの頂点も `dep v + 1` と `dep v + 2` に居る」と言う。
    したがって**時刻 `k+2` には深さ `k` の頂点と深さ `k+1` の頂点が全部同時に居る**。
    これがピークの下界になる:

    $$ p \;\ge\; \max_k \big( \#\{v : \mathrm{dep}\,v = k\} + \#\{v : \mathrm{dep}\,v = k+1\} \big). $$

    右端でも同じことが起き、そちらは sink も足せる（`present_at_end_dep` ＋ `sink_at_and_stays_dep`）。

    **ピラミッド（高さ `h`、深さ `k` の頂点が `h-k` 個）に当てると `p ≥ 2h`。**
    実測 `3, 6, 8, 10, 13, …` に対して `h = 3, 4, 5` で**厳密にタイト**
    （`6, 8, 10`）。`h = 18` では 36 対 58 で 0.62 倍。 -/

section PeakLower

variable {P : ℕ → Finset ℕ} {V : Finset ℕ} {dep : ℕ → ℕ}

/-- **ピークの下界（左端）**: 時刻 `k+2` には深さ `k` と `k+1` の頂点が全部居る。 -/
theorem peak_lower_left {sink D : ℕ}
    (hp : Pebbling pa P (2 * D + 1))
    (hclosed : ∀ v ∈ V, ∀ u ∈ pa v, u ∈ V)
    (hdown : ∀ v ∈ V, dep v ≠ 0 → ∃ u ∈ pa v, dep u + 1 = dep v)
    (hmax : ∀ v ∈ V, dep v ≤ dep sink)
    (huniq : ∀ v ∈ V, dep v = D → v = sink)
    (hgone : ∀ v ∈ V, v ≠ sink → v ∉ P (2 * D + 1))
    (hsV : sink ∈ V) (hds : dep sink = D) (hD : 1 ≤ D)
    (hsin : sink ∈ P (2 * D + 1))
    (hup : ∀ v ∈ V, v ≠ sink → ∃ c ∈ V, v ∈ pa c ∧ dep c = dep v + 1) :
    ∀ k, V.filter (fun v => dep v = k ∨ dep v = k + 1) ⊆ P (k + 2) := by
  have h := present_at_dep hp hclosed hdown hmax huniq hgone hsV hds hD hsin hup
  intro k v hv
  rw [Finset.mem_filter] at hv
  obtain ⟨hvV, hk⟩ := hv
  rcases hk with hk | hk
  · have := (h v hvV).2
    rw [hk] at this
    exact this
  · have := (h v hvV).1
    rw [hk] at this
    exact this

/-- 上の系: **カード数の不等式**。ピーク制約 `|P t| ≤ p` と合わせて下界になる。 -/
theorem peak_lower_card {sink D : ℕ}
    (hp : Pebbling pa P (2 * D + 1))
    (hclosed : ∀ v ∈ V, ∀ u ∈ pa v, u ∈ V)
    (hdown : ∀ v ∈ V, dep v ≠ 0 → ∃ u ∈ pa v, dep u + 1 = dep v)
    (hmax : ∀ v ∈ V, dep v ≤ dep sink)
    (huniq : ∀ v ∈ V, dep v = D → v = sink)
    (hgone : ∀ v ∈ V, v ≠ sink → v ∉ P (2 * D + 1))
    (hsV : sink ∈ V) (hds : dep sink = D) (hD : 1 ≤ D)
    (hsin : sink ∈ P (2 * D + 1))
    (hup : ∀ v ∈ V, v ≠ sink → ∃ c ∈ V, v ∈ pa c ∧ dep c = dep v + 1) :
    ∀ k, (V.filter (fun v => dep v = k ∨ dep v = k + 1)).card ≤ (P (k + 2)).card :=
  fun k => Finset.card_le_card
    (peak_lower_left hp hclosed hdown hmax huniq hgone hsV hds hD hsin hup k)

/-- **ピークの下界（右端・sink 込み）**: 時刻 `2D - k - 1` には深さ `k` と `k+1` の
    頂点（sink 以外）に加えて **sink も居る**。`k + 2 ≤ D` のとき。 -/
theorem peak_lower_right {sink D : ℕ}
    (hp : Pebbling pa P (2 * D + 1))
    (hclosed : ∀ v ∈ V, ∀ u ∈ pa v, u ∈ V)
    (hdown : ∀ v ∈ V, dep v ≠ 0 → ∃ u ∈ pa v, dep u + 1 = dep v)
    (hmax : ∀ v ∈ V, dep v ≤ dep sink)
    (huniq : ∀ v ∈ V, dep v = D → v = sink)
    (hgone : ∀ v ∈ V, v ≠ sink → v ∉ P (2 * D + 1))
    (hsV : sink ∈ V) (hds : dep sink = D) (hD : 1 ≤ D)
    (hsin : sink ∈ P (2 * D + 1))
    (hup : ∀ v ∈ V, v ≠ sink → ∃ c ∈ V, v ∈ pa c ∧ dep c = dep v + 1) :
    ∀ k, k + 2 ≤ D →
      insert sink (V.filter (fun v => (dep v = k ∨ dep v = k + 1) ∧ v ≠ sink))
        ⊆ P (2 * D - k - 1) := by
  have hend := present_at_end_dep hp hclosed hdown hmax huniq hgone hsV hds hD hsin hup
  have hstay := sink_at_and_stays_dep hp hclosed hdown hmax hgone hsV hds hD hsin
  intro k hk v hv
  rcases Finset.mem_insert.mp hv with rfl | hv
  · exact hstay (2 * D - k - 1) (by omega) (by omega)
  · rw [Finset.mem_filter] at hv
    obtain ⟨hvV, hkk, hvs⟩ := hv
    have hd : dep v ≤ dep sink := hmax v hvV
    rcases hkk with hkk | hkk
    · -- dep v = k: 右端は 2D - k、その 1 つ内側が 2D - k - 1
      have := (hend v hvV hvs).2
      rw [hkk] at this
      exact this
    · -- dep v = k+1: 右端が 2D - (k+1) = 2D - k - 1
      have := (hend v hvV hvs).1
      rw [hkk] at this
      have he : 2 * D - (k + 1) = 2 * D - k - 1 := by omega
      rwa [he] at this


end PeakLower

/-! ## 3.99 ⭐ 全結合の層状 DAG では**射影が逆向きの持ち上げ**になる

    `lift_pebbling` は「深さの鎖のペブリング → DAG のペブリング」だった。
    **親が「深さがちょうど 1 小さい頂点すべて」である層状 DAG**（`fullPa`）では、
    逆向きも成り立つ:

    > **どの合法なペブリング `P` についても、「層が丸ごと居る時刻の集合」
    > `proj P` は深さの鎖の合法なペブリングであり、しかも
    > `V.filter (dep ∈ proj P t) ⊆ P t` なのでピークは減らない。**

    したがって `lift`（上界）と `proj`（下界）が噛み合い、
    **この族では `p_min` が「深さごとの頂点数を重みにした鎖のペブリング問題」に一致する。**
    実測でも 21 例すべてで一致した（`scripts/q2_layers.py`・`q2_level_weighted.py`）。

    **|V| 頂点の問題が `D+1` 頂点の重みつき問題に落ちる。** -/

section FullyLayered

variable {V : Finset ℕ} {dep : ℕ → ℕ} {D : ℕ} {P : ℕ → Finset ℕ} {T : ℕ}

/-- 全結合の層状 DAG の親関数: 「深さがちょうど 1 小さい `V` の頂点すべて」。 -/
def fullPa (V : Finset ℕ) (dep : ℕ → ℕ) : ℕ → Finset ℕ :=
  fun v => V.filter (fun u => dep u + 1 = dep v)

/-- 深さ `k` の層が**丸ごと**居る時刻の集合を、深さの鎖の配置とみなしたもの。 -/
def proj (V : Finset ℕ) (dep : ℕ → ℕ) (D : ℕ) (P : ℕ → Finset ℕ) (t : ℕ) : Finset ℕ :=
  (Finset.range (D + 1)).filter (fun k => ∀ v ∈ V, dep v = k → v ∈ P t)

theorem mem_proj {t k : ℕ} :
    k ∈ proj V dep D P t ↔ k < D + 1 ∧ ∀ v ∈ V, dep v = k → v ∈ P t := by
  simp [proj, Finset.mem_filter, Finset.mem_range]

/-- **射影はピークを減らさない**: 丸ごと居る層の頂点は当然 `P t` に入っている。 -/
theorem proj_subset {t : ℕ} :
    V.filter (fun v => dep v ∈ proj V dep D P t) ⊆ P t := by
  intro v hv
  rw [Finset.mem_filter] at hv
  obtain ⟨hvV, hd⟩ := hv
  exact (mem_proj.mp hd).2 v hvV rfl

/-- **射影は深さの鎖の合法なペブリングになる。**

    仮定は「各層が空でない」（`hne`）だけ。`P 0 = ∅` から `proj P 0 = ∅` が出る。 -/
theorem proj_pebbling
    (hp : Pebbling (fullPa V dep) P T)
    (hne : ∀ k, k ≤ D → ∃ v ∈ V, dep v = k) :
    Pebbling chainPa (proj V dep D P) T := by
  constructor
  · ext k
    constructor
    · intro hk
      exfalso
      obtain ⟨hkD, hall⟩ := mem_proj.mp hk
      obtain ⟨v, hvV, hdv⟩ := hne k (by omega)
      have := hall v hvV hdv
      rw [hp.start] at this
      simp at this
    · intro hk; simp at hk
  · intro t ht k hch u hu
    -- 深さの範囲は先に取り出しておく（あとで `omega` が使う）。
    have hkD : k < D + 1 := by
      rcases hch with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact (mem_proj.mp h1).1
      · exact (mem_proj.mp h2).1
    -- `k = 0` なら親が無いので自明。
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · simp [chainPa] at hu
    -- `k ≥ 1`: 親は `k-1` ただ一つ。
    have hu' : u = k - 1 := by
      unfold chainPa at hu
      rw [if_neg (by omega)] at hu
      simpa using hu
    subst hu'
    -- 層 `k` の中で「変化した頂点」を取り出す。
    have hkey : ∃ v ∈ V, dep v = k ∧ Changed (P t) (P (t + 1)) v := by
      by_contra hno
      push_neg at hno
      have hiff : ∀ v ∈ V, dep v = k → (v ∈ P t ↔ v ∈ P (t + 1)) :=
        fun v hvV hdv => not_changed_iff.mp (hno v hvV hdv)
      rcases hch with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · obtain ⟨_, hall⟩ := mem_proj.mp h1
        exact h2 (mem_proj.mpr ⟨hkD, fun v hvV hdv => (hiff v hvV hdv).mp (hall v hvV hdv)⟩)
      · obtain ⟨_, hall⟩ := mem_proj.mp h2
        exact h1 (mem_proj.mpr ⟨hkD, fun v hvV hdv => (hiff v hvV hdv).mpr (hall v hvV hdv)⟩)
    obtain ⟨v, hvV, hdv, hchv⟩ := hkey
    -- 変化したので**層 `k-1` の全頂点**が前後の両方に居る。
    have hpar : ∀ w ∈ V, dep w = k - 1 → w ∈ P t ∧ w ∈ P (t + 1) := by
      intro w hwV hdw
      refine hp.legal t ht v hchv w ?_
      unfold fullPa
      rw [Finset.mem_filter]
      exact ⟨hwV, by omega⟩
    exact ⟨mem_proj.mpr ⟨by omega, fun w hwV hdw => (hpar w hwV hdw).1⟩,
           mem_proj.mpr ⟨by omega, fun w hwV hdw => (hpar w hwV hdw).2⟩⟩

/-- 終状態も射影される: `P T = {sink}` で最深層が sink だけなら `proj P T = {D}`。 -/
theorem proj_final {sink : ℕ}
    (hPT : P T = {sink}) (hsV : sink ∈ V) (hds : dep sink = D)
    (hne : ∀ k, k ≤ D → ∃ v ∈ V, dep v = k)
    (huniq : ∀ v ∈ V, dep v = D → v = sink) :
    proj V dep D P T = {D} := by
  ext k
  simp only [Finset.mem_singleton]
  constructor
  · intro hk
    obtain ⟨hkD, hall⟩ := mem_proj.mp hk
    by_contra hkD'
    obtain ⟨v, hvV, hdv⟩ := hne k (by omega)
    have hv := hall v hvV hdv
    rw [hPT, Finset.mem_singleton] at hv
    rw [hv, hds] at hdv
    exact hkD' hdv.symm
  · rintro rfl
    refine mem_proj.mpr ⟨by omega, fun v hvV hdv => ?_⟩
    rw [huniq v hvV hdv, hPT]
    simp


/-- ⭐ **還元定理**: 全結合の層状 DAG では、ピーク最小化が
    **深さの鎖の重みつきペブリング問題に完全に一致する。**

    * **下界**（`proj`）: どの合法な `P` も、同じ長さ・同じ終状態の鎖のペブリング `Q` を
      誘導し、各時刻で `|V.filter (dep ∈ Q t)| ≤ |P t|`。つまりピークは減らない
    * **上界**（`lift`）: どの鎖のペブリング `Q` も DAG のペブリングに持ち上がり、
      その配置はちょうど `V.filter (dep ∈ Q t)`

    したがって
    $$ p_{\min}(G) \;=\; \min_Q \max_t \Big| \{v \in V : \mathrm{dep}\,v \in Q_t\} \Big| $$
    で、右辺は `D+1` 頂点の重みつき鎖の問題（重み = 深さごとの頂点数）。
    **|V| 頂点の問題が D+1 頂点に落ちる。**

    実測でも 21 例すべてで一致した（`scripts/q2_layers.py` と `q2_level_weighted.py` の比較）。 -/
theorem full_layered_reduction {sink : ℕ}
    (hne : ∀ k, k ≤ D → ∃ v ∈ V, dep v = k)
    (hsV : sink ∈ V) (hds : dep sink = D)
    (huniq : ∀ v ∈ V, dep v = D → v = sink) :
    (∀ (P : ℕ → Finset ℕ) (T : ℕ), Pebbling (fullPa V dep) P T → P T = {sink} →
        Pebbling chainPa (proj V dep D P) T ∧ proj V dep D P T = {D} ∧
        ∀ t, (V.filter (fun v => dep v ∈ proj V dep D P t)).card ≤ (P t).card) ∧
    (∀ (Q : ℕ → Finset ℕ) (T : ℕ), Pebbling chainPa Q T → Q T = {D} →
        Pebbling (fullPa V dep) (lift V dep Q) T ∧ lift V dep Q T = {sink} ∧
        ∀ t, lift V dep Q t = V.filter (fun v => dep v ∈ Q t)) := by
  constructor
  · intro P T hp hPT
    exact ⟨proj_pebbling hp hne, proj_final hPT hsV hds hne huniq,
           fun t => Finset.card_le_card proj_subset⟩
  · intro Q T hQ hQT
    have hpaV : ∀ v ∈ V, ∀ u ∈ fullPa V dep v, u ∈ V := by
      intro v _ u hu
      unfold fullPa at hu
      exact (Finset.mem_filter.mp hu).1
    have hpa1 : ∀ v ∈ V, ∀ u ∈ fullPa V dep v, dep u + 1 = dep v := by
      intro v _ u hu
      unfold fullPa at hu
      exact (Finset.mem_filter.mp hu).2
    exact ⟨lift_pebbling hQ hpaV hpa1, lift_final hQT hsV hds huniq, fun _ => rfl⟩

end FullyLayered


/-! ### 非空虚性: 層の大きさ `[2, 2, 2, 1]` の全結合層状 DAG

    頂点 7・深さ 3。実測の `p_min` は 5 で、重みつき鎖 `[2,2,2,1]` の最適値と一致する
    （`scripts/q2_layers.py`）。ここでは**還元定理の仮定が実際に満たせること**と、
    `fullPa` が意図した DAG になっていることを `decide` で確かめる。 -/

section FullLayeredWitness

def VL7 : Finset ℕ := {0, 1, 2, 3, 4, 5, 6}
def depL7 : ℕ → ℕ := fun v => if v ≤ 1 then 0 else if v ≤ 3 then 1 else if v ≤ 5 then 2 else 3

/-- `fullPa` が意図した層状 DAG になっている（各層は 1 つ下の層の全頂点を親に持つ）。 -/
theorem VL7_structure :
    fullPa VL7 depL7 0 = ∅ ∧ fullPa VL7 depL7 1 = ∅ ∧
    fullPa VL7 depL7 2 = {0, 1} ∧ fullPa VL7 depL7 3 = {0, 1} ∧
    fullPa VL7 depL7 4 = {2, 3} ∧ fullPa VL7 depL7 5 = {2, 3} ∧
    fullPa VL7 depL7 6 = {4, 5} := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- 還元定理の仮定が満たせる。 -/
theorem VL7_hyps :
    (∀ k, k ≤ 3 → ∃ v ∈ VL7, depL7 v = k) ∧ (6 : ℕ) ∈ VL7 ∧ depL7 6 = 3 ∧
    (∀ v ∈ VL7, depL7 v = 3 → v = 6) := by
  refine ⟨?_, by decide, by decide, by decide⟩
  intro k hk
  interval_cases k
  · exact ⟨0, by decide, by decide⟩
  · exact ⟨2, by decide, by decide⟩
  · exact ⟨4, by decide, by decide⟩
  · exact ⟨6, by decide, by decide⟩

/-- したがって還元定理がこの DAG に**実際に適用できる**。 -/
theorem VL7_reduction :
    (∀ (P : ℕ → Finset ℕ) (T : ℕ), Pebbling (fullPa VL7 depL7) P T → P T = {6} →
        Pebbling chainPa (proj VL7 depL7 3 P) T ∧ proj VL7 depL7 3 P T = {3} ∧
        ∀ t, (VL7.filter (fun v => depL7 v ∈ proj VL7 depL7 3 P t)).card ≤ (P t).card) ∧
    (∀ (Q : ℕ → Finset ℕ) (T : ℕ), Pebbling chainPa Q T → Q T = {3} →
        Pebbling (fullPa VL7 depL7) (lift VL7 depL7 Q) T ∧ lift VL7 depL7 Q T = {6} ∧
        ∀ t, lift VL7 depL7 Q t = VL7.filter (fun v => depL7 v ∈ Q t)) :=
  full_layered_reduction (V := VL7) (dep := depL7) (D := 3) (sink := 6)
    VL7_hyps.1 VL7_hyps.2.1 VL7_hyps.2.2.1 VL7_hyps.2.2.2

/-- 深さごとの頂点数（重み）が `[2, 2, 2, 1]` であること。 -/
theorem VL7_weights :
    (VL7.filter (fun v => depL7 v = 0)).card = 2 ∧
    (VL7.filter (fun v => depL7 v = 1)).card = 2 ∧
    (VL7.filter (fun v => depL7 v = 2)).card = 2 ∧
    (VL7.filter (fun v => depL7 v = 3)).card = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

end FullLayeredWitness


/-! ## 3.995 ピラミッドの**拡大性**（下界を強めるための核）

    ピラミッドでは層 `k` の頂点 `i` の親が層 `k-1` の `i` と `i+1` なので、
    層 `k` の部分集合 `A` の親全体は `A ∪ (A+1)` になる。その大きさは

    $$ |A \cup (A+1)| \;\ge\; |A| + 1 \qquad (A \ne \emptyset) $$

    を満たす。**これが「層が動くと 1 つ下の層はもっと広く要る」の正体**で、
    数え上げだけの下界（`peak_lower_*`、$h \le 5$ でしかタイトでない）を
    $h \le 12$ までタイトにする（`scripts/q2_pyr_lower.py` の整数計画）。 -/

section Expansion

/-- **拡大性の核**: 空でない有限集合 `A ⊆ ℕ` について `|A ∪ (A+1)| ≥ |A| + 1`。

    証明: `A` の最大元 `m` を取ると `m + 1 ∈ A + 1` だが `m + 1 ∉ A`。
    よって `A ∪ (A+1) ⊇ insert (m+1) A` で、`m+1 ∉ A` だから濃度がちょうど 1 増える。 -/
theorem shift_union_card (A : Finset ℕ) (hA : A.Nonempty) :
    A.card + 1 ≤ (A ∪ A.image (· + 1)).card := by
  have hm : A.max' hA ∈ A := A.max'_mem hA
  have hnot : A.max' hA + 1 ∉ A := by
    intro hc
    have := A.le_max' _ hc
    omega
  have hsub : insert (A.max' hA + 1) A ⊆ A ∪ A.image (· + 1) := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨A.max' hA, hm, rfl⟩)
    · exact Finset.mem_union_left _ hx
  have := Finset.card_le_card hsub
  rwa [Finset.card_insert_of_notMem hnot] at this

/-- 系: 変化した集合が空でなければ、親側は**真に大きい**。 -/
theorem shift_union_card_lt (A : Finset ℕ) (hA : A.Nonempty) :
    A.card < (A ∪ A.image (· + 1)).card := by
  have := shift_union_card A hA
  omega

end Expansion

/-! ## 3.996 一般の高さのピラミッドと**拡大性の適用**

    頂点 `(k, i)`（層 `k`・位置 `i`、`i + k < h`）を自然数 `h * k + i` で符号化する。
    `h` で割った商が層・余りが位置になる（`i < h` なので一意）。

    これで **`shift_union_card`（拡大性の核）をペブリングの合法性に接続**できる:
    層 `k` で変化した集合 `A` が空でなければ、その親を含むどんな集合も `|A| + 1` 以上
    （`pyr_expansion`）。ペブリングの合法性より親は前後の両方に居るので、
    **層 `k-1` には前後とも `|A| + 1` 個以上の頂点が居る**（`pyr_change_forces`）。
    これが `scripts/q2_pyr_lower_cert.py` の整数計画が使う制約そのもの。 -/

section PyramidGeneric

/-- ピラミッドの親関数。層 `k ≥ 1` の頂点 `(k,i)` の親は `(k-1, i)` と `(k-1, i+1)`。 -/
def pyrPa (h : ℕ) : ℕ → Finset ℕ := fun v =>
  if v / h = 0 then ∅ else {h * (v / h - 1) + v % h, h * (v / h - 1) + v % h + 1}

/-- 層 `k` の頂点全体（位置は `0 .. h-k-1`）。 -/
def pyrLevel (h k : ℕ) : Finset ℕ := (Finset.range (h - k)).image (fun i => h * k + i)

theorem mem_pyrLevel {h k v : ℕ} : v ∈ pyrLevel h k ↔ ∃ i < h - k, v = h * k + i := by
  simp [pyrLevel, Finset.mem_image, Finset.mem_range, eq_comm]

/-- 層 `k` の頂点は `h*k + (v % h)` と書け、位置は `h - k` 未満、層は `v / h = k`。 -/
theorem pyrLevel_spec {h k v : ℕ} (hk : k < h) (hv : v ∈ pyrLevel h k) :
    v / h = k ∧ v % h < h - k ∧ v = h * k + v % h := by
  obtain ⟨i, hi, rfl⟩ := mem_pyrLevel.mp hv
  have hpos : 0 < h := by omega
  have hih : i < h := by omega
  have hdiv : (h * k + i) / h = k := by
    rw [Nat.mul_add_div hpos, Nat.div_eq_of_lt hih]
    omega
  have hmod : (h * k + i) % h = i := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hih]
  exact ⟨hdiv, by rw [hmod]; exact hi, by rw [hmod]⟩

/-- **拡大性のピラミッドへの適用**。層 `k`（`1 ≤ k < h`）の空でない集合 `A` の
    親をすべて含む集合 `S` は、`|A| + 1` 個以上の要素を持つ。 -/
theorem pyr_expansion {h k : ℕ} (hk1 : 1 ≤ k) (hkh : k < h)
    (A : Finset ℕ) (hA : A.Nonempty) (hAsub : A ⊆ pyrLevel h k)
    (S : Finset ℕ) (hS : ∀ v ∈ A, ∀ u ∈ pyrPa h v, u ∈ S) :
    A.card + 1 ≤ S.card := by
  set P := A.image (fun v => v % h) with hPdef
  -- 位置は層の中で単射
  have hcardP : P.card = A.card := by
    apply Finset.card_image_of_injOn
    intro x hx y hy hxy
    have hx' := (pyrLevel_spec hkh (hAsub hx)).2.2
    have hy' := (pyrLevel_spec hkh (hAsub hy)).2.2
    simp only at hxy
    rw [hx', hy', hxy]
  -- 「位置 ∪ 位置+1」を層 k-1 の頂点へ写したものが S に含まれる
  have hsub : (P ∪ P.image (· + 1)).image (fun i => h * (k - 1) + i) ⊆ S := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    rcases Finset.mem_union.mp hi with hi | hi
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
      refine hS v hv _ ?_
      have hd := (pyrLevel_spec hkh (hAsub hv)).1
      unfold pyrPa
      rw [if_neg (by omega), hd]
      simp
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hj
      refine hS v hv _ ?_
      have hd := (pyrLevel_spec hkh (hAsub hv)).1
      unfold pyrPa
      rw [if_neg (by omega), hd]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      right
      omega
  have hinj : Function.Injective (fun i => h * (k - 1) + i) := by
    intro a b hab
    simp only at hab
    omega
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj] at hcard
  have hPne : P.Nonempty := by
    obtain ⟨v, hv⟩ := hA
    exact ⟨v % h, Finset.mem_image.mpr ⟨v, hv, rfl⟩⟩
  have := shift_union_card P hPne
  omega

/-- **合法性への接続**: 層 `k` で変化した集合 `A` が空でなければ、
    層 `k-1` の頂点が `|A| + 1` 個以上、**前後の両方に**居る。

    これが整数計画の制約「`c_k(t) ≥ 1 → a_{k-1}(t), a_{k-1}(t+1) ≥ c_k(t)+1`」の根拠。 -/
theorem pyr_change_forces {h k t T : ℕ} {P : ℕ → Finset ℕ}
    (hp : Pebbling (pyrPa h) P T) (htT : t < T) (hk1 : 1 ≤ k) (hkh : k < h)
    (A : Finset ℕ) (hA : A.Nonempty) (hAsub : A ⊆ pyrLevel h k)
    (hAch : ∀ v ∈ A, Changed (P t) (P (t + 1)) v) :
    A.card + 1 ≤ (P t).card ∧ A.card + 1 ≤ (P (t + 1)).card := by
  constructor
  · exact pyr_expansion hk1 hkh A hA hAsub (P t)
      (fun v hv u hu => (hp.legal t htT v (hAch v hv) u hu).1)
  · exact pyr_expansion hk1 hkh A hA hAsub (P (t + 1))
      (fun v hv u hu => (hp.legal t htT v (hAch v hv) u hu).2)


/-- 非空虚性: `h = 5` で符号化が意図どおりであること（層の大きさと親）。 -/
theorem pyr5_encoding_ok :
    (pyrLevel 5 0).card = 5 ∧ (pyrLevel 5 1).card = 4 ∧ (pyrLevel 5 2).card = 3 ∧
    (pyrLevel 5 3).card = 2 ∧ (pyrLevel 5 4).card = 1 ∧
    pyrPa 5 5 = {0, 1} ∧ pyrPa 5 6 = {1, 2} ∧ pyrPa 5 7 = {2, 3} ∧
    pyrPa 5 20 = {15, 16} ∧ pyrPa 5 0 = ∅ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- 非空虚性: 拡大性が実際に使えること（`h=5`・層 1 の 4 頂点の親は 5 個以上）。 -/
theorem pyr5_expansion_applied :
    (pyrLevel 5 1).card + 1 ≤ (pyrLevel 5 0).card := by
  have h1 : (pyrLevel 5 1).card = 4 := by decide
  have h0 : (pyrLevel 5 0).card = 5 := by decide
  omega

end PyramidGeneric


/-! ### 層の大きさから直ちに出る下界（完全二分木の指数的コスト）

    `peak_lower_right` を `k = 0` で使うと、**層 0 と層 1 の大きさだけ**から下界が出る:
    $$ p \;\ge\; \#\{v : \mathrm{dep}\,v = 0\} + \#\{v : \mathrm{dep}\,v = 1\} + 1 . $$

    完全二分木（葉が深さ 0・根が深さ $D$）では層 $k$ に $2^{D-k}$ 個あるので
    $$ p_{\min} \;\ge\; 2^D + 2^{D-1} + 1 \;=\; 3 \cdot 2^{D-1} + 1 . $$

    **Královič 2004 Thm 4.9 の空間最適値は $h + \Theta(\lg^* h)$**（時間無制約）なので、
    **時間最適性を課すと必要空間が $\Theta(h)$ から $\Theta(2^h)$ へ指数的に増える。** -/

section LevelSizeLower

variable {P : ℕ → Finset ℕ} {V : Finset ℕ} {dep : ℕ → ℕ}

/-- **層 0 と層 1 の大きさだけから出る下界**（`peak_lower_right` の `k = 0` の場合）。 -/
theorem peak_lower_levels01 {sink D : ℕ}
    (hp : Pebbling pa P (2 * D + 1))
    (hclosed : ∀ v ∈ V, ∀ u ∈ pa v, u ∈ V)
    (hdown : ∀ v ∈ V, dep v ≠ 0 → ∃ u ∈ pa v, dep u + 1 = dep v)
    (hmax : ∀ v ∈ V, dep v ≤ dep sink)
    (huniq : ∀ v ∈ V, dep v = D → v = sink)
    (hgone : ∀ v ∈ V, v ≠ sink → v ∉ P (2 * D + 1))
    (hsV : sink ∈ V) (hds : dep sink = D) (hD : 2 ≤ D)
    (hsin : sink ∈ P (2 * D + 1))
    (hup : ∀ v ∈ V, v ≠ sink → ∃ c ∈ V, v ∈ pa c ∧ dep c = dep v + 1)
    {n0 n1 : ℕ}
    (h0 : (V.filter (fun v => dep v = 0)).card = n0)
    (h1 : (V.filter (fun v => dep v = 1)).card = n1) :
    n0 + n1 + 1 ≤ (P (2 * D - 1)).card := by
  have hsub := peak_lower_right (V := V) (dep := dep) (sink := sink) (D := D)
    hp hclosed hdown hmax huniq hgone hsV hds (by omega) hsin hup 0 (by omega)
  have hcard := Finset.card_le_card hsub
  -- `insert sink (filter …)` の濃度は `n0 + n1 + 1`
  have hne : sink ∉ V.filter (fun v => (dep v = 0 ∨ dep v = 0 + 1) ∧ v ≠ sink) := by
    intro hc
    exact ((Finset.mem_filter.mp hc).2).2 rfl
  rw [Finset.card_insert_of_notMem hne] at hcard
  have hsplit : V.filter (fun v => (dep v = 0 ∨ dep v = 0 + 1) ∧ v ≠ sink)
      = V.filter (fun v => dep v = 0) ∪ V.filter (fun v => dep v = 1) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hvV, (h | h), _⟩
      · exact Or.inl ⟨hvV, h⟩
      · exact Or.inr ⟨hvV, by omega⟩
    · rintro (⟨hvV, h⟩ | ⟨hvV, h⟩) <;>
        refine ⟨hvV, ?_, ?_⟩
      · exact Or.inl h
      · intro hc; rw [hc, hds] at h; omega
      · exact Or.inr (by omega)
      · intro hc; rw [hc, hds] at h; omega
  have hdisj : Disjoint (V.filter (fun v => dep v = 0)) (V.filter (fun v => dep v = 1)) := by
    rw [Finset.disjoint_left]
    intro v hv hv'
    have := (Finset.mem_filter.mp hv).2
    have := (Finset.mem_filter.mp hv').2
    omega
  rw [hsplit, Finset.card_union_of_disjoint hdisj, h0, h1] at hcard
  omega

/-- **完全二分木の指数的コスト**（層の大きさを仮定として与えた形）。
    層 0 に $2^D$ 個・層 1 に $2^{D-1}$ 個あるなら、時間最適には $3 \cdot 2^{D-1} + 1$ 個要る。 -/
theorem tree_peak_lower {sink D : ℕ}
    (hp : Pebbling pa P (2 * D + 1))
    (hclosed : ∀ v ∈ V, ∀ u ∈ pa v, u ∈ V)
    (hdown : ∀ v ∈ V, dep v ≠ 0 → ∃ u ∈ pa v, dep u + 1 = dep v)
    (hmax : ∀ v ∈ V, dep v ≤ dep sink)
    (huniq : ∀ v ∈ V, dep v = D → v = sink)
    (hgone : ∀ v ∈ V, v ≠ sink → v ∉ P (2 * D + 1))
    (hsV : sink ∈ V) (hds : dep sink = D) (hD : 2 ≤ D)
    (hsin : sink ∈ P (2 * D + 1))
    (hup : ∀ v ∈ V, v ≠ sink → ∃ c ∈ V, v ∈ pa c ∧ dep c = dep v + 1)
    (h0 : (V.filter (fun v => dep v = 0)).card = 2 ^ D)
    (h1 : (V.filter (fun v => dep v = 1)).card = 2 ^ (D - 1)) :
    3 * 2 ^ (D - 1) + 1 ≤ (P (2 * D - 1)).card := by
  have h := peak_lower_levels01 hp hclosed hdown hmax huniq hgone hsV hds hD hsin hup h0 h1
  have hpow : 2 ^ D = 2 * 2 ^ (D - 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, D = m + 1 := ⟨D - 1, by omega⟩
    simp [pow_succ, Nat.mul_comm]
  omega

end LevelSizeLower


/-! ### 完全二分木 $h = 4$（頂点 15・深さ 3）で $p_{\min} = 13$ を両側とも機械証明

    葉 `0..7`（深さ0）・`8..11`（深さ1）・`12,13`（深さ2）・根 `14`（深さ3）。
    下界は `tree_peak_lower`（層 0 が $2^3=8$ 個・層 1 が $2^2=4$ 個 → $3\cdot4+1 = 13$）、
    上界は `alt_par_time_exact`（ピーク 13）。 -/

section Tree4

def paT4 : ℕ → Finset ℕ := fun v =>
  if v = 8 then {0, 1} else if v = 9 then {2, 3} else if v = 10 then {4, 5}
  else if v = 11 then {6, 7} else if v = 12 then {8, 9} else if v = 13 then {10, 11}
  else if v = 14 then {12, 13} else ∅
def depT4 : ℕ → ℕ := fun v => if v ≤ 7 then 0 else if v ≤ 11 then 1 else if v ≤ 13 then 2 else 3
def VT4 : Finset ℕ := {0,1,2,3,4,5,6,7,8,9,10,11,12,13,14}

/-- 符号化が完全二分木であることの検査（層の大きさと親の本数）。 -/
theorem paT4_is_tree :
    (VT4.filter (fun v => depT4 v = 0)).card = 8 ∧
    (VT4.filter (fun v => depT4 v = 1)).card = 4 ∧
    (VT4.filter (fun v => depT4 v = 2)).card = 2 ∧
    (VT4.filter (fun v => depT4 v = 3)).card = 1 ∧
    (∀ v ∈ VT4, depT4 v = 0 ↔ paT4 v = ∅) ∧
    (∀ v ∈ VT4, depT4 v ≠ 0 → (paT4 v).card = 2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **$p_{\min}(\text{完全二分木 } h{=}4) = 13$。** 上界は `alt`、下界は層 0・層 1 の大きさから。 -/
theorem tree4_pmin_eq_13 :
    (Pebbling paT4 (alt VT4 depT4 14 3) (2 * 3 + 1) ∧
      alt VT4 depT4 14 3 (2 * 3 + 1) = {14} ∧
      ∀ t, t ≤ 2 * 3 + 1 → (alt VT4 depT4 14 3 t).card ≤ 13) ∧
    (∀ P : ℕ → Finset ℕ, Pebbling paT4 P (2 * 3 + 1) → (14 : ℕ) ∈ P (2 * 3 + 1) →
      (∀ v ∈ VT4, v ≠ 14 → v ∉ P (2 * 3 + 1)) → 13 ≤ (P 5).card) := by
  constructor
  · refine ⟨(alt_par_time_exact (pa := paT4) (V := VT4) (dep := depT4) (sink := 14) (d := 3)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).1,
      (alt_par_time_exact (pa := paT4) (V := VT4) (dep := depT4) (sink := 14) (d := 3)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).2,
      ?_⟩
    intro t ht
    interval_cases t <;> decide
  · intro P hp hsin hgone
    have h := tree_peak_lower (pa := paT4) (V := VT4) (dep := depT4) (sink := 14) (D := 3)
      hp (by decide) (by decide) (by decide) (by decide) hgone
      (by decide) (by decide) (by omega) hsin (by decide) (by decide) (by decide)
    norm_num at h
    exact h

end Tree4


/-! ### 完全二分木 $h = 5$（頂点 31・深さ 4）で $p_{\min} = 25$ -/

section Tree5

def paT5 : ℕ → Finset ℕ := fun v =>
  if v = 16 then {0, 1} else if v = 17 then {2, 3} else if v = 18 then {4, 5}
  else if v = 19 then {6, 7} else if v = 20 then {8, 9} else if v = 21 then {10, 11}
  else if v = 22 then {12, 13} else if v = 23 then {14, 15} else if v = 24 then {16, 17}
  else if v = 25 then {18, 19} else if v = 26 then {20, 21} else if v = 27 then {22, 23}
  else if v = 28 then {24, 25} else if v = 29 then {26, 27} else if v = 30 then {28, 29} else ∅
def depT5 : ℕ → ℕ := fun v =>
  if v ≤ 15 then 0 else if v ≤ 23 then 1 else if v ≤ 27 then 2 else if v ≤ 29 then 3 else 4
def VT5 : Finset ℕ :=
  {0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30}

theorem paT5_is_tree :
    (VT5.filter (fun v => depT5 v = 0)).card = 16 ∧
    (VT5.filter (fun v => depT5 v = 1)).card = 8 ∧
    (VT5.filter (fun v => depT5 v = 2)).card = 4 ∧
    (VT5.filter (fun v => depT5 v = 3)).card = 2 ∧
    (VT5.filter (fun v => depT5 v = 4)).card = 1 ∧
    (∀ v ∈ VT5, depT5 v ≠ 0 → (paT5 v).card = 2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **$p_{\min}(\text{完全二分木 } h{=}5) = 25 = 3\cdot 2^3 + 1$。** -/
theorem tree5_pmin_eq_25 :
    (Pebbling paT5 (alt VT5 depT5 30 4) (2 * 4 + 1) ∧
      alt VT5 depT5 30 4 (2 * 4 + 1) = {30} ∧
      ∀ t, t ≤ 2 * 4 + 1 → (alt VT5 depT5 30 4 t).card ≤ 25) ∧
    (∀ P : ℕ → Finset ℕ, Pebbling paT5 P (2 * 4 + 1) → (30 : ℕ) ∈ P (2 * 4 + 1) →
      (∀ v ∈ VT5, v ≠ 30 → v ∉ P (2 * 4 + 1)) → 25 ≤ (P 7).card) := by
  constructor
  · refine ⟨(alt_par_time_exact (pa := paT5) (V := VT5) (dep := depT5) (sink := 30) (d := 4)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).1,
      (alt_par_time_exact (pa := paT5) (V := VT5) (dep := depT5) (sink := 30) (d := 4)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).2,
      ?_⟩
    intro t ht
    interval_cases t <;> decide
  · intro P hp hsin hgone
    have h := tree_peak_lower (pa := paT5) (V := VT5) (dep := depT5) (sink := 30) (D := 4)
      hp (by decide) (by decide) (by decide) (by decide) hgone
      (by decide) (by decide) (by omega) hsin (by decide) (by decide) (by decide)
    norm_num at h
    exact h

end Tree5

/-! ### 完全二分木の上界を**一般の $D$** で: `alt` のピークは $3\cdot2^{D-1}+1$ 以下

    場合分けは 2 つだけ:

    * $t \le 2$ または $t \ge 2D-1$ — このとき深さ $2..D-1$ の頂点は `alt` に入れないので
      `alt t ⊆ 層0 ∪ 層1 ∪ {sink}`、濃度は $2^D + 2^{D-1} + 1 = 3\cdot2^{D-1}+1$ 以下
    * それ以外 — 層 0 はブロック $[1,2] \cup [2D-1, 2D]$ の外なので `alt t ⊆ V \ 層0`、
      濃度は $|V| - 2^D = 2^D - 1$ 以下

    仮定は木の「形」を濃度で与える（$|V| = 2^{D+1}-1$・層0が $2^D$・層1が $2^{D-1}$）。 -/

section TreeUpper

variable {V : Finset ℕ} {dep : ℕ → ℕ} {sink D : ℕ}

theorem tree_alt_peak
    (hD : 2 ≤ D)
    (hV : V.card = 2 ^ (D + 1) - 1)
    (h0 : (V.filter (fun v => dep v = 0)).card = 2 ^ D)
    (hmax : ∀ v ∈ V, dep v ≤ D)
    (huniq : ∀ v ∈ V, dep v = D → v = sink)
    (hds : dep sink = D)
    (h1 : (V.filter (fun v => dep v = 1)).card = 2 ^ (D - 1)) :
    ∀ t, (alt V dep sink D t).card ≤ 3 * 2 ^ (D - 1) + 1 := by
  have hpow : 2 ^ D = 2 * 2 ^ (D - 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, D = m + 1 := ⟨D - 1, by omega⟩
    simp [pow_succ, Nat.mul_comm]
  have hpow2 : 2 ^ (D + 1) = 2 * 2 ^ D := by rw [pow_succ]; omega
  intro t
  by_cases ht : t ≤ 2 ∨ 2 * D - 1 ≤ t
  · -- 端: 深さ 2..D-1 は入れない
    have hsub : alt V dep sink D t ⊆
        (V.filter (fun v => dep v = 0) ∪ V.filter (fun v => dep v = 1)) ∪ {sink} := by
      intro v hv
      obtain ⟨hvV, hm⟩ := mem_alt.mp hv
      by_cases hvs : v = sink
      · exact Finset.mem_union_right _ (by simp [hvs])
      · have hlt : dep v < D := dep_lt_of_ne_sink hmax huniq hvV hvs
        rw [altMem_ne hvs] at hm
        have hk : dep v = 0 ∨ dep v = 1 := by
          by_contra hc
          push_neg at hc
          revert hm
          split <;> omega
        refine Finset.mem_union_left _ ?_
        rcases hk with hk | hk
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hvV, hk⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hvV, hk⟩)
    have hc := Finset.card_le_card hsub
    have hu1 := Finset.card_union_le (V.filter (fun v => dep v = 0))
      (V.filter (fun v => dep v = 1))
    have hu2 := Finset.card_union_le
      (V.filter (fun v => dep v = 0) ∪ V.filter (fun v => dep v = 1)) ({sink} : Finset ℕ)
    simp only [Finset.card_singleton] at hu2
    omega
  · -- 中間: 層 0 が入れない
    push_neg at ht
    obtain ⟨ht1, ht2⟩ := ht
    have hsub : alt V dep sink D t ⊆ V \ V.filter (fun v => dep v = 0) := by
      intro v hv
      obtain ⟨hvV, hm⟩ := mem_alt.mp hv
      rw [Finset.mem_sdiff]
      refine ⟨hvV, ?_⟩
      intro hc
      have hd0 : dep v = 0 := (Finset.mem_filter.mp hc).2
      have hvs : v ≠ sink := by intro he; rw [he, hds] at hd0; omega
      rw [altMem_ne hvs] at hm
      rw [hd0] at hm
      simp only [Nat.zero_add] at hm
      revert hm
      norm_num
      omega
    have hc := Finset.card_le_card hsub
    have hint : V.filter (fun v => dep v = 0) ∩ V = V.filter (fun v => dep v = 0) :=
      Finset.inter_eq_left.mpr (Finset.filter_subset _ _)
    rw [Finset.card_sdiff, hint, hV, h0] at hc
    omega

end TreeUpper



/-- **一般化**: 層が十分速く減る（$|V| \le 2n_0 + n_1 + 1$、すなわち
    $\sum_{k\ge2} n_k \le n_0 + 1$）層状 DAG では、`alt` のピークは $n_0 + n_1 + 1$ 以下。

    `peak_lower_right` の下界と一致するので、**そのような族では
    $p_{\min} = n_0 + n_1 + 1$ ちょうど**になる。

    条件の成否は実測と一致する: 完全二分木・幾何級数（比 3, 4）・$[20,10,5,3,2,1]$ は
    満たし、ピラミッド $h=5$ は満たす（$6 \le 6$）が $h=6$ は満たさない（$10 > 7$）——
    実測でも $h=5$ までタイトで $h=6$ から離れる。 -/
theorem alt_peak_of_sparse {V : Finset ℕ} {dep : ℕ → ℕ} {sink D n0 n1 : ℕ}
    (hD : 2 ≤ D)
    (h0 : (V.filter (fun v => dep v = 0)).card = n0)
    (h1 : (V.filter (fun v => dep v = 1)).card = n1)
    (hsparse : V.card ≤ 2 * n0 + n1 + 1)
    (hmax : ∀ v ∈ V, dep v ≤ D)
    (huniq : ∀ v ∈ V, dep v = D → v = sink)
    (hds : dep sink = D) :
    ∀ t, (alt V dep sink D t).card ≤ n0 + n1 + 1 := by
  intro t
  by_cases ht : t ≤ 2 ∨ 2 * D - 1 ≤ t
  · have hsub : alt V dep sink D t ⊆
        (V.filter (fun v => dep v = 0) ∪ V.filter (fun v => dep v = 1)) ∪ {sink} := by
      intro v hv
      obtain ⟨hvV, hm⟩ := mem_alt.mp hv
      by_cases hvs : v = sink
      · exact Finset.mem_union_right _ (by simp [hvs])
      · have hlt : dep v < D := dep_lt_of_ne_sink hmax huniq hvV hvs
        rw [altMem_ne hvs] at hm
        have hk : dep v = 0 ∨ dep v = 1 := by
          by_contra hc
          push_neg at hc
          revert hm
          split <;> omega
        refine Finset.mem_union_left _ ?_
        rcases hk with hk | hk
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hvV, hk⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hvV, hk⟩)
    have hc := Finset.card_le_card hsub
    have hu1 := Finset.card_union_le (V.filter (fun v => dep v = 0))
      (V.filter (fun v => dep v = 1))
    have hu2 := Finset.card_union_le
      (V.filter (fun v => dep v = 0) ∪ V.filter (fun v => dep v = 1)) ({sink} : Finset ℕ)
    simp only [Finset.card_singleton] at hu2
    omega
  · push_neg at ht
    obtain ⟨ht1, ht2⟩ := ht
    have hsub : alt V dep sink D t ⊆ V \ V.filter (fun v => dep v = 0) := by
      intro v hv
      obtain ⟨hvV, hm⟩ := mem_alt.mp hv
      rw [Finset.mem_sdiff]
      refine ⟨hvV, ?_⟩
      intro hc
      have hd0 : dep v = 0 := (Finset.mem_filter.mp hc).2
      have hvs : v ≠ sink := by intro he; rw [he, hds] at hd0; omega
      rw [altMem_ne hvs, hd0] at hm
      simp only [Nat.zero_add] at hm
      revert hm
      norm_num
      omega
    have hc := Finset.card_le_card hsub
    have hint : V.filter (fun v => dep v = 0) ∩ V = V.filter (fun v => dep v = 0) :=
      Finset.inter_eq_left.mpr (Finset.filter_subset _ _)
    rw [Finset.card_sdiff, hint, h0] at hc
    omega


/-- ⭐⭐⭐ **層が十分速く減る層状 DAG では $p_{\min} = n_0 + n_1 + 1$ ちょうど**（両側とも機械証明）。

    条件は $|V| \le 2n_0 + n_1 + 1$、すなわち $\sum_{k \ge 2} n_k \le n_0 + 1$
    （**層 2 以降を全部足しても層 0 とほぼ同じ**）。

    * **上界** `alt_peak_of_sparse`: `alt` が長さ $2D+1$・終状態 `{sink}`・ピーク $\le n_0+n_1+1$
    * **下界** `peak_lower_right`: どの合法なペブリングも時刻 $2D-1$ に $n_0+n_1+1$ 個以上

    **満たす族**: 完全二分木（$\sum_{k\ge2} 2^{D-k} = 2^{D-1}-1 \le 2^D+1$）、
    幾何級数（比 $\ge 2$）、$[20,10,5,3,2,1]$ など。
    **満たさない族**: ピラミッド $h \ge 6$（$h=6$ で $10 > 7$）、定数幅。
    **条件の成否は実測のタイト性と完全に一致する。** -/
theorem sparse_layered_pmin_exact {V : Finset ℕ} {dep : ℕ → ℕ} {sink D n0 n1 : ℕ}
    (hD : 2 ≤ D)
    (h0 : (V.filter (fun v => dep v = 0)).card = n0)
    (h1 : (V.filter (fun v => dep v = 1)).card = n1)
    (hsparse : V.card ≤ 2 * n0 + n1 + 1)
    (hsV : sink ∈ V) (hds : dep sink = D)
    (hmax : ∀ v ∈ V, dep v ≤ dep sink)
    (huniq : ∀ v ∈ V, dep v = D → v = sink)
    (hpaV : ∀ v ∈ V, ∀ u ∈ pa v, u ∈ V)
    (hpa1 : ∀ v ∈ V, ∀ u ∈ pa v, dep u + 1 = dep v)
    (hdown : ∀ v ∈ V, dep v ≠ 0 → ∃ u ∈ pa v, dep u + 1 = dep v)
    (hup : ∀ v ∈ V, v ≠ sink → ∃ c ∈ V, v ∈ pa c ∧ dep c = dep v + 1) :
    (Pebbling pa (alt V dep sink D) (2 * D + 1) ∧
      alt V dep sink D (2 * D + 1) = {sink} ∧
      ∀ t, (alt V dep sink D t).card ≤ n0 + n1 + 1) ∧
    (∀ P : ℕ → Finset ℕ, Pebbling pa P (2 * D + 1) → sink ∈ P (2 * D + 1) →
      (∀ v ∈ V, v ≠ sink → v ∉ P (2 * D + 1)) → n0 + n1 + 1 ≤ (P (2 * D - 1)).card) := by
  have hmaxD : ∀ v ∈ V, dep v ≤ D := by
    intro v hv; have := hmax v hv; omega
  refine ⟨⟨(alt_par_time_exact hsV hds (by omega) hmaxD huniq hpaV hpa1).1,
           (alt_par_time_exact hsV hds (by omega) hmaxD huniq hpaV hpa1).2,
           alt_peak_of_sparse hD h0 h1 hsparse hmaxD huniq hds⟩, ?_⟩
  intro P hp hsin hgone
  exact peak_lower_levels01 hp hpaV hdown hmax huniq hgone hsV hds hD hsin hup h0 h1

/-- ⭐⭐⭐ **完全二分木の最小ピークは一般の $D$ で $3\cdot2^{D-1}+1$**（両側とも機械証明）。

    仮定は「木の形」を濃度で与えたもの:
    $|V| = 2^{D+1}-1$・層 0 が $2^D$ 個・層 1 が $2^{D-1}$ 個、
    ＋ `alt` / `peak_lower_right` の共通仮定（親の深さがちょうど 1 小さい・
    sink 以外は深さ +1 の子を持つ・最深は sink のみ）。

    * **上界**: `alt` が長さ $2D+1$ の合法なペブリングで終状態 `{sink}`、ピークは
      $3\cdot2^{D-1}+1$ 以下
    * **下界**: どの合法なペブリングも時刻 $2D-1$ に $3\cdot2^{D-1}+1$ 個以上を持つ

    **含意**: 空間最適なら $\Theta(D)$ で足りる（Královič 2004 Thm 4.9 の
    $h + \Theta(\lg^* h)$、並列模型でも同じ）のに対し、**時間最適を課すと $\Theta(2^D)$ 要る。
    時間最適性の空間コストは指数的。** -/
theorem tree_pmin_exact {V : Finset ℕ} {dep : ℕ → ℕ} {sink D : ℕ}
    (hD : 2 ≤ D)
    (hV : V.card = 2 ^ (D + 1) - 1)
    (h0 : (V.filter (fun v => dep v = 0)).card = 2 ^ D)
    (h1 : (V.filter (fun v => dep v = 1)).card = 2 ^ (D - 1))
    (hsV : sink ∈ V) (hds : dep sink = D)
    (hmax : ∀ v ∈ V, dep v ≤ dep sink)
    (huniq : ∀ v ∈ V, dep v = D → v = sink)
    (hpaV : ∀ v ∈ V, ∀ u ∈ pa v, u ∈ V)
    (hpa1 : ∀ v ∈ V, ∀ u ∈ pa v, dep u + 1 = dep v)
    (hclosed : ∀ v ∈ V, ∀ u ∈ pa v, u ∈ V)
    (hdown : ∀ v ∈ V, dep v ≠ 0 → ∃ u ∈ pa v, dep u + 1 = dep v)
    (hup : ∀ v ∈ V, v ≠ sink → ∃ c ∈ V, v ∈ pa c ∧ dep c = dep v + 1) :
    -- 上界: `alt` が達成する
    (Pebbling pa (alt V dep sink D) (2 * D + 1) ∧
      alt V dep sink D (2 * D + 1) = {sink} ∧
      ∀ t, (alt V dep sink D t).card ≤ 3 * 2 ^ (D - 1) + 1) ∧
    -- 下界: どの合法なペブリングも必要とする
    (∀ P : ℕ → Finset ℕ, Pebbling pa P (2 * D + 1) → sink ∈ P (2 * D + 1) →
      (∀ v ∈ V, v ≠ sink → v ∉ P (2 * D + 1)) →
      3 * 2 ^ (D - 1) + 1 ≤ (P (2 * D - 1)).card) := by
  have hmaxD : ∀ v ∈ V, dep v ≤ D := by
    intro v hv; have := hmax v hv; omega
  refine ⟨⟨(alt_par_time_exact hsV hds (by omega) hmaxD huniq hpaV hpa1).1,
           (alt_par_time_exact hsV hds (by omega) hmaxD huniq hpaV hpa1).2,
           tree_alt_peak hD hV h0 hmaxD huniq hds h1⟩, ?_⟩
  intro P hp hsin hgone
  exact tree_peak_lower hp hclosed hdown hmax huniq hgone hsV hds (by omega) hsin hup h0 h1


/-! ### ピラミッド $h = 6, 7$ の**上界**（`alt` が最適である範囲）

    ピラミッドでは `alt` が $h \le 8$ で最適（$h=9$ から劣る）。ここでは $h=6,7$ の
    上界（`alt` のピークが 13 / 16 以下）を機械証明する。
    下界は拡大性つき整数計画の DRAT 証明書（層2・`data/q2_pyr_lower_cert.csv`）で
    同じ値が出ているので、**$h \le 8$ は上界が層1・下界が層2 で決着している**。
    $h=6$ の下界 13 は `pyr6_peak_lower_13` で層1になった（2026-10-13）。
    $h=7$ も同じ数え上げで下界 16 が出て、`alt` の上界と合わせて `pyr7_pmin_eq_16`
    （2026-10-14）。$h=8$ ではこの数え上げは 19 しか出さない（DRAT の下界は 20）。 -/

section Pyramid67

def paPY6 : ℕ → Finset ℕ := fun v => if v = 6 then {0, 1} else if v = 7 then {1, 2} else if v = 8 then {2, 3} else if v = 9 then {3, 4} else if v = 10 then {4, 5} else if v = 11 then {6, 7} else if v = 12 then {7, 8} else if v = 13 then {8, 9} else if v = 14 then {9, 10} else if v = 15 then {11, 12} else if v = 16 then {12, 13} else if v = 17 then {13, 14} else if v = 18 then {15, 16} else if v = 19 then {16, 17} else if v = 20 then {18, 19} else ∅
def depPY6 : ℕ → ℕ := fun v => if v ≤ 5 then 0 else if v ≤ 10 then 1 else if v ≤ 14 then 2 else if v ≤ 17 then 3 else if v ≤ 19 then 4 else 5
def VPY6 : Finset ℕ := {0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20}

theorem paPY6_is_pyramid :
    (∀ v ∈ VPY6, depPY6 v = 0 ↔ paPY6 v = ∅) ∧
    (∀ v ∈ VPY6, depPY6 v ≠ 0 → (paPY6 v).card = 2) ∧
    (VPY6.filter (fun v => depPY6 v = 0)).card = 6 ∧
    (VPY6.filter (fun v => depPY6 v = 1)).card = 5 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- **ピラミッド $h=6$: `alt` はピーク 13 で時間最適を達成する**（実測の $p_{\min}$ と一致）。 -/
theorem pyr6_alt_peak_13 :
    Pebbling paPY6 (alt VPY6 depPY6 20 5) (2 * 5 + 1) ∧
    alt VPY6 depPY6 20 5 (2 * 5 + 1) = {20} ∧
    ∀ t, t ≤ 2 * 5 + 1 → (alt VPY6 depPY6 20 5 t).card ≤ 13 := by
  refine ⟨(alt_par_time_exact (pa := paPY6) (V := VPY6) (dep := depPY6) (sink := 20) (d := 5)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).1,
    (alt_par_time_exact (pa := paPY6) (V := VPY6) (dep := depPY6) (sink := 20) (d := 5)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).2, ?_⟩
  intro t ht
  interval_cases t <;> decide

/-- **ピラミッド $h=6$ の下界: どの時間最適なペブリングも時刻 7 に 13 個以上を置く**
    （2026-10-13・第83夜 周3。これで $h=6$ は下界も層1）。

    数え上げ（`peak_lower_right`）が出すのは 12 で、それを 1 段ずらして足す:
    時刻 7（$=2D-3$）には深さ 2・3 の 7 頂点と sink が居る（8 個）。
    深さ 1 の頂点 $6+i$（$i<5$）は時刻 8 に必ず居るので、時刻 7 に居なければ 7→8 で
    置かれ、そのとき親 $i$（深さ 0）が時刻 7 に居る。$\{i, 6+i\}$ の 5 対は互いに素なので
    時刻 7 には深さ 0・1 の頂点が 5 個以上居る。計 13。 -/
theorem pyr6_peak_lower_13 :
    ∀ P : ℕ → Finset ℕ, Pebbling paPY6 P (2 * 5 + 1) → (20 : ℕ) ∈ P (2 * 5 + 1) →
      (∀ v ∈ VPY6, v ≠ 20 → v ∉ P (2 * 5 + 1)) → 13 ≤ (P 7).card := by
  intro P hp hsin hgone
  have h7 := peak_lower_right (pa := paPY6) (V := VPY6) (dep := depPY6) (sink := 20) (D := 5)
    hp (by decide) (by decide) (by decide) (by decide) hgone
    (by decide) (by decide) (by decide) hsin (by decide) 2 (by omega)
  have h8 := peak_lower_right (pa := paPY6) (V := VPY6) (dep := depPY6) (sink := 20) (D := 5)
    hp (by decide) (by decide) (by decide) (by decide) hgone
    (by decide) (by decide) (by decide) hsin (by decide) 1 (by omega)
  have ht7 : 2 * 5 - 2 - 1 = 7 := by norm_num
  have ht8 : 2 * 5 - 1 - 1 = 8 := by norm_num
  rw [ht7] at h7
  rw [ht8] at h8
  -- 深さ 1 の頂点 6+i は、時刻 7 に居るか、さもなくば親 i が居る
  have hpair : ∀ i, i < 5 → (6 + i) ∈ P 7 ∨ i ∈ P 7 := by
    intro i hi
    by_cases hv : (6 + i) ∈ P 7
    · exact Or.inl hv
    · right
      have hmem : (6 + i) ∈ insert 20 (VPY6.filter
          (fun v => (depPY6 v = 1 ∨ depPY6 v = 1 + 1) ∧ v ≠ 20)) := by
        interval_cases i <;> decide
      have hv8 : (6 + i) ∈ P (7 + 1) := h8 hmem
      have hch : Changed (P 7) (P (7 + 1)) (6 + i) := Or.inr ⟨hv, hv8⟩
      have hpa : i ∈ paPY6 (6 + i) := by interval_cases i <;> decide
      exact (hp.legal 7 (by norm_num) (6 + i) hch i hpa).1
  -- 各対から 1 つを選ぶ写像は単射で、値は 10 以下
  classical
  let f : ℕ → ℕ := fun i => if (6 + i) ∈ P 7 then 6 + i else i
  have hfP : ∀ i ∈ Finset.range 5, f i ∈ P 7 := by
    intro i hi
    have hi' : i < 5 := Finset.mem_range.mp hi
    show (if (6 + i) ∈ P 7 then 6 + i else i) ∈ P 7
    split_ifs with h
    · exact h
    · exact (hpair i hi').resolve_left h
  have hfle : ∀ i ∈ Finset.range 5, f i ≤ 10 := by
    intro i hi
    have hi' : i < 5 := Finset.mem_range.mp hi
    show (if (6 + i) ∈ P 7 then 6 + i else i) ≤ 10
    split_ifs <;> omega
  have hinj : Set.InjOn f (Finset.range 5 : Set ℕ) := by
    intro i hi j hj hij
    have hi' : i < 5 := Finset.mem_range.mp hi
    have hj' : j < 5 := Finset.mem_range.mp hj
    simp only [f] at hij
    split_ifs at hij <;> omega
  set U := (Finset.range 5).image f with hU
  set S := insert 20 (VPY6.filter
      (fun v => (depPY6 v = 2 ∨ depPY6 v = 2 + 1) ∧ v ≠ 20)) with hS
  have hUcard : U.card = 5 := by
    rw [hU, Finset.card_image_of_injOn hinj]; simp
  have hScard : S.card = 8 := by rw [hS]; decide
  have hSge : ∀ x ∈ S, 11 ≤ x := by rw [hS]; decide
  have hdisj : Disjoint U S := by
    rw [Finset.disjoint_left]
    intro x hxU hxS
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hxU
    have := hfle i hi
    have := hSge _ hxS
    omega
  have hsub : U ∪ S ⊆ P 7 := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact hfP i hi
    · exact h7 hx
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, hUcard, hScard] at hcard
  omega

/-- **$p_{\min}(\mathrm{pyr}\,6) = 13$**（両側とも機械証明）。上界は `pyr6_alt_peak_13`、
    下界は `pyr6_peak_lower_13`。 -/
theorem pyr6_pmin_eq_13 :
    (Pebbling paPY6 (alt VPY6 depPY6 20 5) (2 * 5 + 1) ∧
      alt VPY6 depPY6 20 5 (2 * 5 + 1) = {20} ∧
      ∀ t, t ≤ 2 * 5 + 1 → (alt VPY6 depPY6 20 5 t).card ≤ 13) ∧
    (∀ P : ℕ → Finset ℕ, Pebbling paPY6 P (2 * 5 + 1) → (20 : ℕ) ∈ P (2 * 5 + 1) →
      (∀ v ∈ VPY6, v ≠ 20 → v ∉ P (2 * 5 + 1)) → 13 ≤ (P 7).card) :=
  ⟨pyr6_alt_peak_13, pyr6_peak_lower_13⟩

def paPY7 : ℕ → Finset ℕ := fun v => if v = 7 then {0, 1} else if v = 8 then {1, 2} else if v = 9 then {2, 3} else if v = 10 then {3, 4} else if v = 11 then {4, 5} else if v = 12 then {5, 6} else if v = 13 then {7, 8} else if v = 14 then {8, 9} else if v = 15 then {9, 10} else if v = 16 then {10, 11} else if v = 17 then {11, 12} else if v = 18 then {13, 14} else if v = 19 then {14, 15} else if v = 20 then {15, 16} else if v = 21 then {16, 17} else if v = 22 then {18, 19} else if v = 23 then {19, 20} else if v = 24 then {20, 21} else if v = 25 then {22, 23} else if v = 26 then {23, 24} else if v = 27 then {25, 26} else ∅
def depPY7 : ℕ → ℕ := fun v => if v ≤ 6 then 0 else if v ≤ 12 then 1 else if v ≤ 17 then 2 else if v ≤ 21 then 3 else if v ≤ 24 then 4 else if v ≤ 26 then 5 else 6
def VPY7 : Finset ℕ := {0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27}

theorem paPY7_is_pyramid :
    (∀ v ∈ VPY7, depPY7 v = 0 ↔ paPY7 v = ∅) ∧
    (∀ v ∈ VPY7, depPY7 v ≠ 0 → (paPY7 v).card = 2) ∧
    (VPY7.filter (fun v => depPY7 v = 0)).card = 7 ∧
    (VPY7.filter (fun v => depPY7 v = 1)).card = 6 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- **ピラミッド $h=7$: `alt` はピーク 16 で時間最適を達成する**。 -/
theorem pyr7_alt_peak_16 :
    Pebbling paPY7 (alt VPY7 depPY7 27 6) (2 * 6 + 1) ∧
    alt VPY7 depPY7 27 6 (2 * 6 + 1) = {27} ∧
    ∀ t, t ≤ 2 * 6 + 1 → (alt VPY7 depPY7 27 6 t).card ≤ 16 := by
  refine ⟨(alt_par_time_exact (pa := paPY7) (V := VPY7) (dep := depPY7) (sink := 27) (d := 6)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).1,
    (alt_par_time_exact (pa := paPY7) (V := VPY7) (dep := depPY7) (sink := 27) (d := 6)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).2, ?_⟩
  intro t ht
  interval_cases t <;> decide

/-- **ピラミッド $h=7$ の下界: どの時間最適なペブリングも時刻 9 に 16 個以上を置く**
    （2026-10-14・第84夜 周2。`pyr6_peak_lower_13` と同じ数え上げ）。
    時刻 9（$=2D-3$）には深さ 2・3 の 9 頂点と sink が居る（10 個）。
    深さ 1 の頂点 $7+i$（$i<6$）は時刻 10 に必ず居るので、時刻 9 に居なければ 9→10 で
    置かれ、そのとき親 $i$（深さ 0）が時刻 9 に居る。6 対は互いに素なので計 16。 -/
theorem pyr7_peak_lower_16 :
    ∀ P : ℕ → Finset ℕ, Pebbling paPY7 P (2 * 6 + 1) → (27 : ℕ) ∈ P (2 * 6 + 1) →
      (∀ v ∈ VPY7, v ≠ 27 → v ∉ P (2 * 6 + 1)) → 16 ≤ (P 9).card := by
  intro P hp hsin hgone
  have h9 := peak_lower_right (pa := paPY7) (V := VPY7) (dep := depPY7) (sink := 27) (D := 6)
    hp (by decide) (by decide) (by decide) (by decide) hgone
    (by decide) (by decide) (by decide) hsin (by decide) 2 (by omega)
  have h10 := peak_lower_right (pa := paPY7) (V := VPY7) (dep := depPY7) (sink := 27) (D := 6)
    hp (by decide) (by decide) (by decide) (by decide) hgone
    (by decide) (by decide) (by decide) hsin (by decide) 1 (by omega)
  have ht9 : 2 * 6 - 2 - 1 = 9 := by norm_num
  have ht10 : 2 * 6 - 1 - 1 = 10 := by norm_num
  rw [ht9] at h9
  rw [ht10] at h10
  -- 深さ 1 の頂点 7+i は、時刻 9 に居るか、さもなくば親 i が居る
  have hpair : ∀ i, i < 6 → (7 + i) ∈ P 9 ∨ i ∈ P 9 := by
    intro i hi
    by_cases hv : (7 + i) ∈ P 9
    · exact Or.inl hv
    · right
      have hmem : (7 + i) ∈ insert 27 (VPY7.filter
          (fun v => (depPY7 v = 1 ∨ depPY7 v = 1 + 1) ∧ v ≠ 27)) := by
        interval_cases i <;> decide
      have hv10 : (7 + i) ∈ P (9 + 1) := h10 hmem
      have hch : Changed (P 9) (P (9 + 1)) (7 + i) := Or.inr ⟨hv, hv10⟩
      have hpa : i ∈ paPY7 (7 + i) := by interval_cases i <;> decide
      exact (hp.legal 9 (by norm_num) (7 + i) hch i hpa).1
  -- 各対から 1 つを選ぶ写像は単射で、値は 12 以下
  classical
  let f : ℕ → ℕ := fun i => if (7 + i) ∈ P 9 then 7 + i else i
  have hfP : ∀ i ∈ Finset.range 6, f i ∈ P 9 := by
    intro i hi
    have hi' : i < 6 := Finset.mem_range.mp hi
    show (if (7 + i) ∈ P 9 then 7 + i else i) ∈ P 9
    split_ifs with h
    · exact h
    · exact (hpair i hi').resolve_left h
  have hfle : ∀ i ∈ Finset.range 6, f i ≤ 12 := by
    intro i hi
    have hi' : i < 6 := Finset.mem_range.mp hi
    show (if (7 + i) ∈ P 9 then 7 + i else i) ≤ 12
    split_ifs <;> omega
  have hinj : Set.InjOn f (Finset.range 6 : Set ℕ) := by
    intro i hi j hj hij
    have hi' : i < 6 := Finset.mem_range.mp hi
    have hj' : j < 6 := Finset.mem_range.mp hj
    simp only [f] at hij
    split_ifs at hij <;> omega
  set U := (Finset.range 6).image f with hU
  set S := insert 27 (VPY7.filter
      (fun v => (depPY7 v = 2 ∨ depPY7 v = 2 + 1) ∧ v ≠ 27)) with hS
  have hUcard : U.card = 6 := by
    rw [hU, Finset.card_image_of_injOn hinj]; simp
  have hScard : S.card = 10 := by rw [hS]; decide
  have hSge : ∀ x ∈ S, 13 ≤ x := by rw [hS]; decide
  have hdisj : Disjoint U S := by
    rw [Finset.disjoint_left]
    intro x hxU hxS
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hxU
    have := hfle i hi
    have := hSge _ hxS
    omega
  have hsub : U ∪ S ⊆ P 9 := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact hfP i hi
    · exact h9 hx
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, hUcard, hScard] at hcard
  omega

/-- **$p_{\min}(\mathrm{pyr}\,7) = 16$**（両側とも機械証明）。上界は `pyr7_alt_peak_16`、
    下界は `pyr7_peak_lower_16`。 -/
theorem pyr7_pmin_eq_16 :
    (Pebbling paPY7 (alt VPY7 depPY7 27 6) (2 * 6 + 1) ∧
      alt VPY7 depPY7 27 6 (2 * 6 + 1) = {27} ∧
      ∀ t, t ≤ 2 * 6 + 1 → (alt VPY7 depPY7 27 6 t).card ≤ 16) ∧
    (∀ P : ℕ → Finset ℕ, Pebbling paPY7 P (2 * 6 + 1) → (27 : ℕ) ∈ P (2 * 6 + 1) →
      (∀ v ∈ VPY7, v ≠ 27 → v ∉ P (2 * 6 + 1)) → 16 ≤ (P 9).card) :=
  ⟨pyr7_alt_peak_16, pyr7_peak_lower_16⟩

end Pyramid67

/-! ## 3.9991 ⭐ 一般の高さのピラミッド: 時間最適ならピークは `3h - 5` 以上（2026-10-14・第84夜 周4）

    `pyr6_peak_lower_13` / `pyr7_peak_lower_16` の数え上げを、`PyramidGeneric` の符号化
    （`pyrPa`・`pyrLevel`）の上で一般の `h ≥ 5` について行う。`peak_lower_right` の側条件は
    `decide` ではなく一般の補題（`pyr_closed` ほか）で与える。`h = 5, 6, 7` では交互構成が
    ちょうど `3h - 5` を取る（`pyr_alt_peak_3h5_567`）のでタイト。`h = 8` では実測（DRAT）の 20 に届かない（19）。 -/

section PyramidPeakGeneric


/-- ピラミッドの頂点全体（層 `0 .. h-1`）。 -/
def pyrV (h : ℕ) : Finset ℕ := (Finset.range h).biUnion (pyrLevel h)

/-- 深さ = 層番号 = `v / h`。 -/
def pyrDep (h : ℕ) : ℕ → ℕ := fun v => v / h

/-- `h * k + i`（`i < h`）の商と余り。 -/
theorem pyr_divmod {h k i : ℕ} (hi : i < h) :
    (h * k + i) / h = k ∧ (h * k + i) % h = i := by
  have hpos : 0 < h := by omega
  refine ⟨?_, ?_⟩
  · rw [Nat.mul_add_div hpos, Nat.div_eq_of_lt hi]; omega
  · rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hi]

theorem mem_pyrV {h v : ℕ} (hpos : 0 < h) :
    v ∈ pyrV h ↔ v / h < h ∧ v % h + v / h < h := by
  unfold pyrV
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨k, hk, hv⟩
    have hk' := Finset.mem_range.mp hk
    have := pyrLevel_spec hk' hv
    omega
  · rintro ⟨h1, h2⟩
    refine ⟨v / h, Finset.mem_range.mpr h1, ?_⟩
    rw [mem_pyrLevel]
    refine ⟨v % h, by omega, ?_⟩
    exact (Nat.div_add_mod v h).symm

theorem pyrPa_pos {h v : ℕ} (hk : v / h ≠ 0) :
    pyrPa h v = {h * (v / h - 1) + v % h, h * (v / h - 1) + v % h + 1} := by
  unfold pyrPa
  rw [if_neg hk]

theorem pyr_closed {h : ℕ} (hpos : 0 < h) :
    ∀ v ∈ pyrV h, ∀ u ∈ pyrPa h v, u ∈ pyrV h := by
  intro v hv u hu
  rw [mem_pyrV hpos] at hv ⊢
  obtain ⟨h1, h2⟩ := hv
  have h0 := Nat.zero_le (v / h)
  by_cases hk : v / h = 0
  · simp [pyrPa, hk] at hu
  · rw [pyrPa_pos hk] at hu
    have hm := Nat.mod_lt v hpos
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl
    · obtain ⟨a, b⟩ := pyr_divmod (k := v / h - 1) hm
      rw [a, b]
      omega
    · have hm' : v % h + 1 < h := by omega
      have e : h * (v / h - 1) + v % h + 1 = h * (v / h - 1) + (v % h + 1) := by
        rw [Nat.add_assoc]
      obtain ⟨a, b⟩ := pyr_divmod (k := v / h - 1) hm'
      rw [e, a, b]
      omega

theorem pyr_down {h : ℕ} (hpos : 0 < h) :
    ∀ v ∈ pyrV h, pyrDep h v ≠ 0 → ∃ u ∈ pyrPa h v, pyrDep h u + 1 = pyrDep h v := by
  intro v hv hd
  simp only [pyrDep] at hd ⊢
  rw [mem_pyrV hpos] at hv
  have hm := Nat.mod_lt v hpos
  have h0 := Nat.zero_le (v / h)
  refine ⟨h * (v / h - 1) + v % h, ?_, ?_⟩
  · rw [pyrPa_pos hd]
    simp
  · obtain ⟨a, _⟩ := pyr_divmod (k := v / h - 1) hm
    rw [a]
    omega

theorem pyr_max {h : ℕ} (hpos : 0 < h) :
    ∀ v ∈ pyrV h, pyrDep h v ≤ pyrDep h (h * (h - 1)) := by
  intro v hv
  rw [mem_pyrV hpos] at hv
  simp only [pyrDep]
  rw [Nat.mul_div_cancel_left _ hpos]
  omega

theorem pyr_uniq {h : ℕ} (hpos : 0 < h) :
    ∀ v ∈ pyrV h, pyrDep h v = h - 1 → v = h * (h - 1) := by
  intro v hv hd
  simp only [pyrDep] at hd
  rw [mem_pyrV hpos] at hv
  have h0 : v % h = 0 := by omega
  have := Nat.div_add_mod v h
  rw [hd, h0] at this
  omega

theorem pyr_sink_mem {h : ℕ} (hpos : 0 < h) : h * (h - 1) ∈ pyrV h := by
  rw [mem_pyrV hpos]
  have h1 : h * (h - 1) / h = h - 1 := Nat.mul_div_cancel_left _ hpos
  have h2 : h * (h - 1) % h = 0 := Nat.mul_mod_right _ _
  rw [h1, h2]
  omega

theorem pyr_sink_dep {h : ℕ} (hpos : 0 < h) : pyrDep h (h * (h - 1)) = h - 1 := by
  simp only [pyrDep]
  exact Nat.mul_div_cancel_left _ hpos

theorem pyr_up {h : ℕ} (hpos : 0 < h) :
    ∀ v ∈ pyrV h, v ≠ h * (h - 1) →
      ∃ c ∈ pyrV h, v ∈ pyrPa h c ∧ pyrDep h c = pyrDep h v + 1 := by
  intro v hv hne
  rw [mem_pyrV hpos] at hv
  obtain ⟨h1, h2⟩ := hv
  have hm := Nat.mod_lt v hpos
  have hdm := Nat.div_add_mod v h
  have h0 := Nat.zero_le (v / h)
  have hklt : v / h < h - 1 := by
    by_contra hcon
    apply hne
    have hk : v / h = h - 1 := by omega
    have h0 : v % h = 0 := by omega
    rw [hk, h0] at hdm
    omega
  simp only [pyrDep]
  by_cases hi : v % h + 1 + v / h < h
  · -- c = (k+1, i)
    have hm' : v % h < h := hm
    obtain ⟨a, b⟩ := pyr_divmod (k := v / h + 1) hm'
    refine ⟨h * (v / h + 1) + v % h, ?_, ?_, ?_⟩
    · rw [mem_pyrV hpos, a, b]
      omega
    · have hk : (h * (v / h + 1) + v % h) / h ≠ 0 := by rw [a]; omega
      rw [pyrPa_pos hk, a, b]
      simp only [Nat.add_sub_cancel, Finset.mem_insert, Finset.mem_singleton]
      left
      omega
    · rw [a]
  · -- c = (k+1, i-1)，i = h - k - 1 ≥ 1
    have hipos : 1 ≤ v % h := by omega
    have hm' : v % h - 1 < h := by omega
    obtain ⟨a, b⟩ := pyr_divmod (k := v / h + 1) hm'
    refine ⟨h * (v / h + 1) + (v % h - 1), ?_, ?_, ?_⟩
    · rw [mem_pyrV hpos, a, b]
      omega
    · have hk : (h * (v / h + 1) + (v % h - 1)) / h ≠ 0 := by rw [a]; omega
      rw [pyrPa_pos hk, a, b]
      simp only [Nat.add_sub_cancel, Finset.mem_insert, Finset.mem_singleton]
      right
      omega
    · rw [a]

theorem card_pyrLevel (h k : ℕ) : (pyrLevel h k).card = h - k := by
  unfold pyrLevel
  rw [Finset.card_image_of_injective, Finset.card_range]
  intro a b hab
  simp only at hab
  omega

/-- **一般の高さ `h ≥ 5` のピラミッドの下界**: どの時間最適なペブリングも
    時刻 `2D - 3`（`D = h - 1`）に `3h - 5` 個以上を置く。 -/
theorem pyr_peak_lower_3h5 (h : ℕ) (hh : 5 ≤ h) :
    ∀ P : ℕ → Finset ℕ, Pebbling (pyrPa h) P (2 * (h - 1) + 1) →
      h * (h - 1) ∈ P (2 * (h - 1) + 1) →
      (∀ v ∈ pyrV h, v ≠ h * (h - 1) → v ∉ P (2 * (h - 1) + 1)) →
      3 * h - 5 ≤ (P (2 * (h - 1) - 3)).card := by
  intro P hp hsin hgone
  have hpos : 0 < h := by omega
  have hsd : (h * (h - 1)) / h = h - 1 := Nat.mul_div_cancel_left _ hpos
  have h2 := peak_lower_right (pa := pyrPa h) (V := pyrV h) (dep := pyrDep h)
    (sink := h * (h - 1)) (D := h - 1)
    hp (pyr_closed hpos) (pyr_down hpos) (pyr_max hpos) (by
      intro v hv hd
      exact pyr_uniq hpos v hv hd)
    hgone (pyr_sink_mem hpos) (pyr_sink_dep hpos) (by omega) hsin (pyr_up hpos) 2 (by omega)
  have h1 := peak_lower_right (pa := pyrPa h) (V := pyrV h) (dep := pyrDep h)
    (sink := h * (h - 1)) (D := h - 1)
    hp (pyr_closed hpos) (pyr_down hpos) (pyr_max hpos) (by
      intro v hv hd
      exact pyr_uniq hpos v hv hd)
    hgone (pyr_sink_mem hpos) (pyr_sink_dep hpos) (by omega) hsin (pyr_up hpos) 1 (by omega)
  have e2 : 2 * (h - 1) - 2 - 1 = 2 * (h - 1) - 3 := by omega
  have e1 : 2 * (h - 1) - 1 - 1 = (2 * (h - 1) - 3) + 1 := by omega
  rw [e2] at h2
  rw [e1] at h1
  -- 深さ 1 の頂点 h+i は、時刻 t に居るか、さもなくば親 i が居る
  have hpair : ∀ i, i < h - 1 → (h + i) ∈ P (2 * (h - 1) - 3) ∨ i ∈ P (2 * (h - 1) - 3) := by
    intro i hi
    by_cases hv : (h + i) ∈ P (2 * (h - 1) - 3)
    · exact Or.inl hv
    · right
      obtain ⟨a, b⟩ := pyr_divmod (h := h) (k := 1) (i := i) (by omega)
      rw [Nat.mul_one] at a b
      have hmem : (h + i) ∈ insert (h * (h - 1)) ((pyrV h).filter
          (fun v => (pyrDep h v = 1 ∨ pyrDep h v = 1 + 1) ∧ v ≠ h * (h - 1))) := by
        apply Finset.mem_insert_of_mem
        rw [Finset.mem_filter, mem_pyrV hpos]
        simp only [pyrDep]
        refine ⟨⟨?_, ?_⟩, Or.inl ?_, ?_⟩
        · rw [a]; omega
        · rw [a, b]; omega
        · exact a
        · intro heq
          rw [heq, hsd] at a
          omega
      have hv10 : (h + i) ∈ P ((2 * (h - 1) - 3) + 1) := h1 hmem
      have hch : Changed (P (2 * (h - 1) - 3)) (P ((2 * (h - 1) - 3) + 1)) (h + i) :=
        Or.inr ⟨hv, hv10⟩
      have hpa : i ∈ pyrPa h (h + i) := by
        have hk : (h + i) / h ≠ 0 := by rw [a]; omega
        rw [pyrPa_pos hk, a, b]
        simp
      exact (hp.legal (2 * (h - 1) - 3) (by omega) (h + i) hch i hpa).1
  classical
  let f : ℕ → ℕ := fun i => if (h + i) ∈ P (2 * (h - 1) - 3) then h + i else i
  have hfP : ∀ i ∈ Finset.range (h - 1), f i ∈ P (2 * (h - 1) - 3) := by
    intro i hi
    have hi' : i < h - 1 := Finset.mem_range.mp hi
    show (if (h + i) ∈ P (2 * (h - 1) - 3) then h + i else i) ∈ P (2 * (h - 1) - 3)
    split_ifs with hc
    · exact hc
    · exact (hpair i hi').resolve_left hc
  have hflt : ∀ i ∈ Finset.range (h - 1), f i < 2 * h := by
    intro i hi
    have hi' : i < h - 1 := Finset.mem_range.mp hi
    show (if (h + i) ∈ P (2 * (h - 1) - 3) then h + i else i) < 2 * h
    split_ifs <;> omega
  have hinj : Set.InjOn f (Finset.range (h - 1) : Set ℕ) := by
    intro i hi j hj hij
    have hi' : i < h - 1 := Finset.mem_range.mp hi
    have hj' : j < h - 1 := Finset.mem_range.mp hj
    simp only [f] at hij
    split_ifs at hij <;> omega
  set U := (Finset.range (h - 1)).image f with hU
  set S := insert (h * (h - 1)) (pyrLevel h 2 ∪ pyrLevel h 3) with hS
  have hUcard : U.card = h - 1 := by
    rw [hU, Finset.card_image_of_injOn hinj]; simp
  -- 層 2, 3 の頂点の商
  have hdiv2 : ∀ x ∈ pyrLevel h 2, x / h = 2 := fun x hx => (pyrLevel_spec (by omega) hx).1
  have hdiv3 : ∀ x ∈ pyrLevel h 3, x / h = 3 := fun x hx => (pyrLevel_spec (by omega) hx).1
  have hdisjL : Disjoint (pyrLevel h 2) (pyrLevel h 3) := by
    rw [Finset.disjoint_left]
    intro x hx2 hx3
    have := hdiv2 x hx2
    have := hdiv3 x hx3
    omega
  have hsnot : h * (h - 1) ∉ pyrLevel h 2 ∪ pyrLevel h 3 := by
    intro hx
    rcases Finset.mem_union.mp hx with hx | hx
    · have := hdiv2 _ hx
      omega
    · have := hdiv3 _ hx
      omega
  have hScard : S.card = 1 + (h - 2) + (h - 3) := by
    rw [hS, Finset.card_insert_of_notMem hsnot, Finset.card_union_of_disjoint hdisjL,
      card_pyrLevel, card_pyrLevel]
    omega
  have hSge : ∀ x ∈ S, 2 * h ≤ x := by
    intro x hx
    rw [hS] at hx
    have key : 2 ≤ x / h := by
      rcases Finset.mem_insert.mp hx with rfl | hx
      · rw [hsd]; omega
      · rcases Finset.mem_union.mp hx with hx | hx
        · rw [hdiv2 x hx]
        · rw [hdiv3 x hx]; omega
    have := (Nat.le_div_iff_mul_le hpos).mp key
    omega
  have hdisj : Disjoint U S := by
    rw [Finset.disjoint_left]
    intro x hxU hxS
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hxU
    have := hflt i hi
    have := hSge _ hxS
    omega
  have hSsub : S ⊆ P (2 * (h - 1) - 3) := by
    intro x hx
    rw [hS] at hx
    apply h2
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      rw [Finset.mem_filter, mem_pyrV hpos]
      simp only [pyrDep]
      rcases Finset.mem_union.mp hx with hx | hx
      · have hs := pyrLevel_spec (by omega : 2 < h) hx
        have := hdiv2 x hx
        refine ⟨⟨by omega, by omega⟩, Or.inl this, ?_⟩
        intro heq
        rw [heq, hsd] at this
        omega
      · have hs := pyrLevel_spec (by omega : 3 < h) hx
        have := hdiv3 x hx
        refine ⟨⟨by omega, by omega⟩, Or.inr (by omega), ?_⟩
        intro heq
        rw [heq, hsd] at this
        omega
  have hsub : U ∪ S ⊆ P (2 * (h - 1) - 3) := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact hfP i hi
    · exact hSsub hx
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, hUcard, hScard] at hcard
  omega

theorem pyr_pa1 {h : ℕ} (hpos : 0 < h) :
    ∀ v ∈ pyrV h, ∀ u ∈ pyrPa h v, pyrDep h u + 1 = pyrDep h v := by
  intro v hv u hu
  rw [mem_pyrV hpos] at hv
  simp only [pyrDep]
  have h0 := Nat.zero_le (v / h)
  by_cases hk : v / h = 0
  · simp [pyrPa, hk] at hu
  · rw [pyrPa_pos hk] at hu
    have hm := Nat.mod_lt v hpos
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl
    · obtain ⟨a, _⟩ := pyr_divmod (k := v / h - 1) hm
      rw [a]; omega
    · have hm' : v % h + 1 < h := by omega
      have e : h * (v / h - 1) + v % h + 1 = h * (v / h - 1) + (v % h + 1) := by
        rw [Nat.add_assoc]
      obtain ⟨a, _⟩ := pyr_divmod (k := v / h - 1) hm'
      rw [e, a]; omega

/-- 仮定が空虚でないこと: 一般の `h ≥ 2` で交互構成は時間最適なペブリングで、終状態は sink だけ。 -/
theorem pyr_alt_pebbling (h : ℕ) (hh : 2 ≤ h) :
    Pebbling (pyrPa h) (alt (pyrV h) (pyrDep h) (h * (h - 1)) (h - 1)) (2 * (h - 1) + 1) ∧
    alt (pyrV h) (pyrDep h) (h * (h - 1)) (h - 1) (2 * (h - 1) + 1) = {h * (h - 1)} := by
  have hpos : 0 < h := by omega
  exact alt_par_time_exact (pyr_sink_mem hpos) (pyr_sink_dep hpos) (by omega)
    (fun v hv => (pyr_sink_dep hpos) ▸ pyr_max hpos v hv) (pyr_uniq hpos) (pyr_closed hpos)
    (pyr_pa1 hpos)

/-- **`3h - 5` は h = 5, 6, 7 でタイト**（一般の符号化の上で）: 交互構成のピークはちょうど `3h - 5`。 -/
theorem pyr_alt_peak_3h5_567 :
    (∀ t, t ≤ 2 * 4 + 1 → (alt (pyrV 5) (pyrDep 5) 20 4 t).card ≤ 10) ∧
    (∀ t, t ≤ 2 * 5 + 1 → (alt (pyrV 6) (pyrDep 6) 30 5 t).card ≤ 13) ∧
    (∀ t, t ≤ 2 * 6 + 1 → (alt (pyrV 7) (pyrDep 7) 42 6 t).card ≤ 16) := by
  refine ⟨?_, ?_, ?_⟩ <;> intro t ht <;> interval_cases t <;> decide


/-! ### `3h - 4`（`h ≥ 8`）: 時刻 `2D-3` が締まるなら時刻 `2D-5` が溢れる（2026-10-15・第85夜 周1）

    時刻 `2D-3` の数え上げ（`pyr_peak_lower_3h5`）が `3h-5` で締まるのは、深さ 1 が全部居て深さ 0 が
    1 つも居ないときに限る（`pyr_pair_count_strict`）。すると深さ 1 は時刻 `2D-4` にも居るので、
    時刻 `2D-5` で深さ 0/1 の対 `h-1`・深さ 2/3 の対 `h-3`・sink と深さ 4, 5 の `2h-8` が数えられ、
    計 `4h-12 ≥ 3h-4`（`h ≥ 8`）。SAT（`autoresearch/jobs/night85r1_pyr8_explore.py`）では
    `h = 8, 9, 10` の厳密値が 20, 23, 26 で、どの単独の時刻も 20 を強制せず、対 `{2D-5, 2D-3}` だけが強制する。
    交互構成は `h = 8` で 20（タイト）、`h = 9, 10` では 24, 29 で、こちらは一致しない。 -/

/-- 層 `k ≥ 1` の頂点 `h*k+i` の 2 つの親（層 `k-1` の位置 `i` と `i+1`）。 -/
theorem pyr3h4_parents {h k i : ℕ} (hk1 : 1 ≤ k) (hkh : k < h) (hi : i < h - k) :
    h * (k - 1) + i ∈ pyrPa h (h * k + i) ∧ h * (k - 1) + i + 1 ∈ pyrPa h (h * k + i) := by
  obtain ⟨a, b⟩ := pyr_divmod (h := h) (k := k) (i := i) (by omega)
  have hk0 : (h * k + i) / h ≠ 0 := by rw [a]; omega
  have hpa := pyrPa_pos hk0
  rw [a, b] at hpa
  rw [hpa]
  simp

/-- `h * k = h * (k-1) + h`（`k ≥ 1`）。 -/
theorem pyr3h4_mul {h k : ℕ} (hk1 : 1 ≤ k) : h * k = h * (k - 1) + h := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  simp [Nat.mul_succ]

/-- 層 `k` に属すれば商は `k`。 -/
theorem pyr3h4_div {h k x : ℕ} (hk : k < h) (hx : x ∈ pyrLevel h k) : x / h = k :=
  (pyrLevel_spec hk hx).1

/-- 対数え補題の強い版: 層 `k` の欠けた頂点があれば、層 `k-1`・`k` に `h-k+1` 個以上。 -/
theorem pyr_pair_count_strict {h k t T : ℕ} {P : ℕ → Finset ℕ} (hk1 : 1 ≤ k) (hkh : k < h)
    (hp : Pebbling (pyrPa h) P T) (ht : t < T)
    (hall : ∀ i, i < h - k → h * k + i ∈ P (t + 1))
    (j : ℕ) (hj : j < h - k) (hjn : h * k + j ∉ P t) :
    h - k + 1 ≤ (P t ∩ (pyrLevel h (k - 1) ∪ pyrLevel h k)).card := by
  classical
  have hmul := pyr3h4_mul (h := h) hk1
  -- 欠けた頂点は両方の親が居る
  have hpar : ∀ i, i < h - k → h * k + i ∉ P t →
      h * (k - 1) + i ∈ P t ∧ h * (k - 1) + i + 1 ∈ P t := by
    intro i hi hn
    have hch : Changed (P t) (P (t + 1)) (h * k + i) := Or.inr ⟨hn, hall i hi⟩
    have hl := hp.legal t ht (h * k + i) hch
    have hq := pyr3h4_parents hk1 hkh hi
    exact ⟨(hl _ hq.1).1, (hl _ hq.2).1⟩
  let f : ℕ → ℕ := fun i =>
    if h * k + i ∈ P t then h * k + i
    else if i < j then h * (k - 1) + i else h * (k - 1) + (i + 1)
  have hj' := hpar j hj hjn
  have hfP : ∀ i ∈ Finset.range (h - k), f i ∈ P t := by
    intro i hi
    have hi' : i < h - k := Finset.mem_range.mp hi
    show (if h * k + i ∈ P t then h * k + i
      else if i < j then h * (k - 1) + i else h * (k - 1) + (i + 1)) ∈ P t
    split_ifs with hc hij
    · exact hc
    · exact (hpar i hi' hc).1
    · exact (hpar i hi' hc).2
  have hfL : ∀ i ∈ Finset.range (h - k), f i ∈ pyrLevel h (k - 1) ∪ pyrLevel h k := by
    intro i hi
    have hi' : i < h - k := Finset.mem_range.mp hi
    show (if h * k + i ∈ P t then h * k + i
      else if i < j then h * (k - 1) + i else h * (k - 1) + (i + 1)) ∈ _
    rw [Finset.mem_union]
    split_ifs with hc hij
    · exact Or.inr (mem_pyrLevel.mpr ⟨i, hi', rfl⟩)
    · exact Or.inl (mem_pyrLevel.mpr ⟨i, by omega, rfl⟩)
    · exact Or.inl (mem_pyrLevel.mpr ⟨i + 1, by omega, rfl⟩)
  have hinj : Set.InjOn f (Finset.range (h - k) : Set ℕ) := by
    intro i hi i' hi2 hii
    have hi' : i < h - k := Finset.mem_range.mp hi
    have hi2' : i' < h - k := Finset.mem_range.mp hi2
    simp only [f] at hii
    split_ifs at hii <;> omega
  set U := (Finset.range (h - k)).image f with hU
  have hUcard : U.card = h - k := by
    rw [hU, Finset.card_image_of_injOn hinj]; simp
  have hnot : h * (k - 1) + j ∉ U := by
    intro hx
    obtain ⟨i, hi, hfi⟩ := Finset.mem_image.mp hx
    have hi' : i < h - k := Finset.mem_range.mp hi
    simp only [f] at hfi
    split_ifs at hfi <;> omega
  have hsub : insert (h * (k - 1) + j) U ⊆ P t ∩ (pyrLevel h (k - 1) ∪ pyrLevel h k) := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · refine Finset.mem_inter.mpr ⟨hj'.1, Finset.mem_union.mpr (Or.inl ?_)⟩
      exact mem_pyrLevel.mpr ⟨j, by omega, rfl⟩
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_inter.mpr ⟨hfP i hi, hfL i hi⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnot, hUcard] at hcard
  exact hcard

/-- 対数え補題: 時刻 `t+1` に層 `k` が全部居れば、時刻 `t` の層 `k-1`・`k` に `h-k` 個以上。 -/
theorem pyr_pair_count {h k t T : ℕ} {P : ℕ → Finset ℕ} (hk1 : 1 ≤ k) (hkh : k < h)
    (hp : Pebbling (pyrPa h) P T) (ht : t < T)
    (hall : ∀ i, i < h - k → h * k + i ∈ P (t + 1)) :
    h - k ≤ (P t ∩ (pyrLevel h (k - 1) ∪ pyrLevel h k)).card := by
  classical
  by_cases hmiss : ∃ j, j < h - k ∧ h * k + j ∉ P t
  · obtain ⟨j, hj, hjn⟩ := hmiss
    have := pyr_pair_count_strict hk1 hkh hp ht hall j hj hjn
    omega
  · push Not at hmiss
    have hsub : pyrLevel h k ⊆ P t ∩ (pyrLevel h (k - 1) ∪ pyrLevel h k) := by
      intro x hx
      refine Finset.mem_inter.mpr ⟨?_, Finset.mem_union.mpr (Or.inr hx)⟩
      obtain ⟨i, hi, rfl⟩ := mem_pyrLevel.mp hx
      exact hmiss i hi
    have := Finset.card_le_card hsub
    rw [card_pyrLevel] at this
    exact this

/-! ### 層の補助 -/

/-- `L_a ∪ L_{a+1}` の頂点の商は `a` か `a+1`。 -/
theorem pyr3h4_W_div {h a x : ℕ} (ha : a + 1 < h)
    (hx : x ∈ pyrLevel h a ∪ pyrLevel h (a + 1)) : a ≤ x / h ∧ x / h ≤ a + 1 := by
  rcases Finset.mem_union.mp hx with hx | hx
  · have := pyr3h4_div (by omega) hx
    omega
  · have := pyr3h4_div ha hx
    omega

/-- `{sink} ∪ L_b ∪ L_{b+1}` の頂点の商は `b` 以上。 -/
theorem pyr3h4_Ws_div {h b x : ℕ} (hpos : 0 < h) (hb : b + 1 < h - 1)
    (hx : x ∈ insert (h * (h - 1)) (pyrLevel h b ∪ pyrLevel h (b + 1))) : b ≤ x / h := by
  rcases Finset.mem_insert.mp hx with rfl | hx
  · rw [Nat.mul_div_cancel_left _ hpos]; omega
  · have := pyr3h4_W_div (by omega) hx
    omega

theorem pyr3h4_disj_W_W {h a b : ℕ} (hb : b + 1 < h) (hab : a + 2 ≤ b)
    {X Y : Finset ℕ} (hX : X ⊆ pyrLevel h a ∪ pyrLevel h (a + 1))
    (hY : Y ⊆ pyrLevel h b ∪ pyrLevel h (b + 1)) : Disjoint X Y := by
  rw [Finset.disjoint_left]
  intro x hxX hxY
  have h1 := pyr3h4_W_div (by omega) (hX hxX)
  have h2 := pyr3h4_W_div hb (hY hxY)
  omega

theorem pyr3h4_disj_W_Ws {h a b : ℕ} (hpos : 0 < h) (hb : b + 1 < h - 1) (hab : a + 2 ≤ b)
    {X Y : Finset ℕ} (hX : X ⊆ pyrLevel h a ∪ pyrLevel h (a + 1))
    (hY : Y ⊆ insert (h * (h - 1)) (pyrLevel h b ∪ pyrLevel h (b + 1))) : Disjoint X Y := by
  rw [Finset.disjoint_left]
  intro x hxX hxY
  have h1 := pyr3h4_W_div (by omega) (hX hxX)
  have h2 := pyr3h4_Ws_div hpos hb (hY hxY)
  omega

theorem pyr3h4_card_W {h a : ℕ} (ha : a + 1 < h) :
    (pyrLevel h a ∪ pyrLevel h (a + 1)).card = (h - a) + (h - (a + 1)) := by
  rw [Finset.card_union_of_disjoint, card_pyrLevel, card_pyrLevel]
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  have := pyr3h4_div (by omega) hx1
  have := pyr3h4_div ha hx2
  omega

theorem pyr3h4_card_Ws {h b : ℕ} (hpos : 0 < h) (hb : b + 1 < h - 1) :
    (insert (h * (h - 1)) (pyrLevel h b ∪ pyrLevel h (b + 1))).card
      = 1 + (h - b) + (h - (b + 1)) := by
  have hn : h * (h - 1) ∉ pyrLevel h b ∪ pyrLevel h (b + 1) := by
    intro hx
    have := pyr3h4_W_div (by omega) hx
    rw [Nat.mul_div_cancel_left _ hpos] at this
    omega
  rw [Finset.card_insert_of_notMem hn, pyr3h4_card_W (by omega)]
  omega

/-- `peak_lower_right` の出力から `{sink} ∪ L_k ∪ L_{k+1} ⊆ S` を取り出す。 -/
theorem pyr3h4_Ws_sub {h k : ℕ} (hpos : 0 < h) (hk : k + 2 ≤ h - 1) {S : Finset ℕ}
    (hS : insert (h * (h - 1)) ((pyrV h).filter
        (fun v => (pyrDep h v = k ∨ pyrDep h v = k + 1) ∧ v ≠ h * (h - 1))) ⊆ S) :
    insert (h * (h - 1)) (pyrLevel h k ∪ pyrLevel h (k + 1)) ⊆ S := by
  intro x hx
  apply hS
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact Finset.mem_insert_self _ _
  · apply Finset.mem_insert_of_mem
    rw [Finset.mem_filter, mem_pyrV hpos]
    simp only [pyrDep]
    have hw := pyr3h4_W_div (by omega) hx
    have hlt : x / h ≤ k + 1 := hw.2
    have hge : k ≤ x / h := hw.1
    have hsp : x % h < h - (x / h) := by
      rcases Finset.mem_union.mp hx with hx | hx
      · have := pyrLevel_spec (by omega : k < h) hx
        rw [this.1] at *
        omega
      · have := pyrLevel_spec (by omega : k + 1 < h) hx
        rw [this.1] at *
        omega
    refine ⟨⟨by omega, by omega⟩, by omega, ?_⟩
    intro heq
    rw [heq, Nat.mul_div_cancel_left _ hpos] at hlt
    omega

/-- **一般の高さ `h ≥ 8` のピラミッド**: 時間最適なペブリングは時刻 `2D-5` か `2D-3` に
    `3h-4` 個以上を置く。 -/
theorem pyr_peak_lower_3h4 (h : ℕ) (hh : 8 ≤ h) :
    ∀ P : ℕ → Finset ℕ, Pebbling (pyrPa h) P (2 * (h - 1) + 1) →
      h * (h - 1) ∈ P (2 * (h - 1) + 1) →
      (∀ v ∈ pyrV h, v ≠ h * (h - 1) → v ∉ P (2 * (h - 1) + 1)) →
      3 * h - 4 ≤ (P (2 * (h - 1) - 5)).card ∨ 3 * h - 4 ≤ (P (2 * (h - 1) - 3)).card := by
  intro P hp hsin hgone
  classical
  have hpos : 0 < h := by omega
  have key : ∀ k, k + 2 ≤ h - 1 → ∀ S : Finset ℕ,
      S = P (2 * (h - 1) - k - 1) →
      insert (h * (h - 1)) (pyrLevel h k ∪ pyrLevel h (k + 1)) ⊆ S := by
    intro k hk S hS
    have h2 := peak_lower_right (pa := pyrPa h) (V := pyrV h) (dep := pyrDep h)
      (sink := h * (h - 1)) (D := h - 1)
      hp (pyr_closed hpos) (pyr_down hpos) (pyr_max hpos) (by
        intro v hv hd
        exact pyr_uniq hpos v hv hd)
      hgone (pyr_sink_mem hpos) (pyr_sink_dep hpos) (by omega) hsin (pyr_up hpos) k hk
    rw [hS]
    exact pyr3h4_Ws_sub hpos hk h2
  obtain ⟨t0, ht0⟩ : ∃ t0, t0 = 2 * (h - 1) - 5 := ⟨_, rfl⟩
  have eA : 2 * (h - 1) - 5 = t0 := ht0.symm
  have eB : 2 * (h - 1) - 3 = t0 + 1 + 1 := by omega
  have hT : t0 + 1 + 1 + 1 < 2 * (h - 1) + 1 := by omega
  rw [eA, eB]
  have k2 := key 2 (by omega) (P (t0 + 1 + 1)) (by congr 1; omega)
  have k1 := key 1 (by omega) (P (t0 + 1 + 1 + 1)) (by congr 1; omega)
  have k3 := key 3 (by omega) (P (t0 + 1)) (by congr 1; omega)
  have k4 := key 4 (by omega) (P t0) (by congr 1)
  by_cases hc : 3 * h - 4 ≤ (P (t0 + 1 + 1)).card
  · exact Or.inr hc
  · left
    push Not at hc
    have hWs2card := pyr3h4_card_Ws (h := h) (b := 2) hpos (by omega)
    -- (a) L1 ⊆ P t1
    have hA : ∀ i, i < h - 1 → h * 1 + i ∈ P (t0 + 1 + 1) := by
      intro i hi
      by_contra hn
      have hall : ∀ i, i < h - 1 → h * 1 + i ∈ P (t0 + 1 + 1 + 1) := by
        intro i hi
        apply k1
        apply Finset.mem_insert_of_mem
        apply Finset.mem_union_left
        exact mem_pyrLevel.mpr ⟨i, hi, rfl⟩
      have hst := pyr_pair_count_strict (h := h) (k := 1) (t := t0 + 1 + 1) (T := 2 * (h - 1) + 1)
        (P := P) (by omega) (by omega) hp (by omega) hall i hi hn
      have hdisj : Disjoint (P (t0 + 1 + 1) ∩ (pyrLevel h (1 - 1) ∪ pyrLevel h 1))
          (insert (h * (h - 1)) (pyrLevel h 2 ∪ pyrLevel h (2 + 1))) :=
        pyr3h4_disj_W_Ws (a := 0) (b := 2) hpos (by omega) (by omega)
          (Finset.inter_subset_right) (Finset.Subset.refl _)
      have hsub : (P (t0 + 1 + 1) ∩ (pyrLevel h (1 - 1) ∪ pyrLevel h 1)) ∪
          insert (h * (h - 1)) (pyrLevel h 2 ∪ pyrLevel h (2 + 1)) ⊆ P (t0 + 1 + 1) :=
        Finset.union_subset Finset.inter_subset_left k2
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_union_of_disjoint hdisj, hWs2card] at hcard
      omega
    -- (b) L0 ∩ P t1 = ∅
    have hB : ∀ i, i < h → i ∉ P (t0 + 1 + 1) := by
      intro i hi hmem
      have hn : i ∉ pyrLevel h 1 := by
        intro hx
        obtain ⟨j, hj, hij⟩ := mem_pyrLevel.mp hx
        omega
      have hXsub : insert i (pyrLevel h 1) ⊆ pyrLevel h 0 ∪ pyrLevel h (0 + 1) := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact Finset.mem_union_left _ (mem_pyrLevel.mpr ⟨x, by omega, by simp⟩)
        · exact Finset.mem_union_right _ hx
      have hdisj : Disjoint (insert i (pyrLevel h 1))
          (insert (h * (h - 1)) (pyrLevel h 2 ∪ pyrLevel h (2 + 1))) :=
        pyr3h4_disj_W_Ws (a := 0) (b := 2) hpos (by omega) (by omega) hXsub (Finset.Subset.refl _)
      have hsub : insert i (pyrLevel h 1) ∪
          insert (h * (h - 1)) (pyrLevel h 2 ∪ pyrLevel h (2 + 1)) ⊆ P (t0 + 1 + 1) := by
        apply Finset.union_subset _ k2
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hmem
        · obtain ⟨j, hj, rfl⟩ := mem_pyrLevel.mp hx
          exact hA j (by omega)
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_union_of_disjoint hdisj, hWs2card, Finset.card_insert_of_notMem hn,
        card_pyrLevel] at hcard
      omega
    -- (c) L1 ⊆ P (t0+1)
    have hC : ∀ i, i < h - 1 → h * 1 + i ∈ P (t0 + 1) := by
      intro i hi
      by_contra hn
      have hch : Changed (P (t0 + 1)) (P (t0 + 1 + 1)) (h * 1 + i) := Or.inr ⟨hn, hA i hi⟩
      have hl := hp.legal (t0 + 1) (by omega) (h * 1 + i) hch
      have hq := pyr3h4_parents (h := h) (k := 1) (i := i) (by omega) (by omega) hi
      have := (hl _ hq.1).2
      exact hB (h * (1 - 1) + i) (by simp; omega) this
    -- (d) t0 での数え上げ
    have hall3 : ∀ i, i < h - 3 → h * 3 + i ∈ P (t0 + 1) := by
      intro i hi
      apply k3
      apply Finset.mem_insert_of_mem
      apply Finset.mem_union_left
      exact mem_pyrLevel.mpr ⟨i, hi, rfl⟩
    have c1 := pyr_pair_count (h := h) (k := 1) (t := t0) (T := 2 * (h - 1) + 1) (P := P)
      (by omega) (by omega) hp (by omega) hC
    have c3 := pyr_pair_count (h := h) (k := 3) (t := t0) (T := 2 * (h - 1) + 1) (P := P)
      (by omega) (by omega) hp (by omega) hall3
    have hd12 : Disjoint (P t0 ∩ (pyrLevel h (1 - 1) ∪ pyrLevel h 1))
        (P t0 ∩ (pyrLevel h (3 - 1) ∪ pyrLevel h 3)) :=
      pyr3h4_disj_W_W (a := 0) (b := 2) (by omega) (by omega)
        (Finset.inter_subset_right) (Finset.inter_subset_right)
    have hd3 : Disjoint ((P t0 ∩ (pyrLevel h (1 - 1) ∪ pyrLevel h 1)) ∪
          (P t0 ∩ (pyrLevel h (3 - 1) ∪ pyrLevel h 3)))
        (insert (h * (h - 1)) (pyrLevel h 4 ∪ pyrLevel h (4 + 1))) := by
      rw [Finset.disjoint_union_left]
      exact ⟨pyr3h4_disj_W_Ws (a := 0) (b := 4) hpos (by omega) (by omega)
          (Finset.inter_subset_right) (Finset.Subset.refl _),
        pyr3h4_disj_W_Ws (a := 2) (b := 4) hpos (by omega) (by omega)
          (Finset.inter_subset_right) (Finset.Subset.refl _)⟩
    have hsub : ((P t0 ∩ (pyrLevel h (1 - 1) ∪ pyrLevel h 1)) ∪
          (P t0 ∩ (pyrLevel h (3 - 1) ∪ pyrLevel h 3))) ∪
        insert (h * (h - 1)) (pyrLevel h 4 ∪ pyrLevel h (4 + 1)) ⊆ P t0 :=
      Finset.union_subset (Finset.union_subset Finset.inter_subset_left
        Finset.inter_subset_left) k4
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hd3, Finset.card_union_of_disjoint hd12,
      pyr3h4_card_Ws (h := h) (b := 4) hpos (by omega)] at hcard
    omega

/-- `h = 8` の交互構成のピークは `20`（`3h - 4` と一致）。 -/
theorem pyr_alt_peak_20 :
    ∀ t, t ≤ 2 * 7 + 1 → (alt (pyrV 8) (pyrDep 8) 56 7 t).card ≤ 20 := by
  intro t ht; interval_cases t <;> decide

/-- 高さ 8 のピラミッドの最小ピークは **ちょうど 20**: 交互構成が時間最適で 20 以下、
    どの時間最適ペブリングも時刻 `2D-5` か `2D-3` に 20 個以上を置く。 -/
theorem pyr8_pmin_eq_20 :
    (Pebbling (pyrPa 8) (alt (pyrV 8) (pyrDep 8) 56 7) (2 * 7 + 1) ∧
      alt (pyrV 8) (pyrDep 8) 56 7 (2 * 7 + 1) = {56}) ∧
    (∀ t, t ≤ 2 * 7 + 1 → (alt (pyrV 8) (pyrDep 8) 56 7 t).card ≤ 20) ∧
    (∀ P : ℕ → Finset ℕ, Pebbling (pyrPa 8) P (2 * 7 + 1) →
      56 ∈ P (2 * 7 + 1) →
      (∀ v ∈ pyrV 8, v ≠ 56 → v ∉ P (2 * 7 + 1)) →
      20 ≤ (P (2 * 7 - 5)).card ∨ 20 ≤ (P (2 * 7 - 3)).card) :=
  ⟨pyr_alt_pebbling 8 (by norm_num), pyr_alt_peak_20, pyr_peak_lower_3h4 8 (by norm_num)⟩


/-! ### `h = 9, 10` のタイト性: SAT の証人を `decide` で確かめる（2026-10-15・第85夜 周2）

    交互構成は `h = 9, 10` でピーク 24, 29 なので `3h-4` に届かない。証人は cadical の解
    （`autoresearch/jobs/night85r2_pyr_witness.py` が独立の再生器で確かめてから書き出した表）。
    上界側（存在）なので道具の成熟度は問わない: 合法性・終状態・頂点集合・ピークはここで `decide` が確かめる。 -/

/-- `LegalStep` は `∀ v : ℕ` を走るが、変化した頂点は `P ∪ Q` に居るのでそこへ制限してよい
    （`ParPebbleExtremal.legalStep_iff_legalOn` と同じ議論。あちらはこのファイルを import する側なので写す）。 -/
theorem pyr_legalStep_of_union {pa : ℕ → Finset ℕ} {P Q : Finset ℕ}
    (h : ∀ v ∈ P ∪ Q, (v ∈ P ∧ v ∉ Q ∨ v ∉ P ∧ v ∈ Q) → ∀ u ∈ pa v, u ∈ P ∧ u ∈ Q) :
    LegalStep pa P Q := by
  intro v hch u hu
  refine h v ?_ hch u hu
  rcases hch with ⟨h1, _⟩ | ⟨_, h2⟩
  · exact Finset.mem_union_left _ h1
  · exact Finset.mem_union_right _ h2

/-- 高さ 9 の証人（SAT の解。`autoresearch/jobs/night85r2_pyr_witness.py` が再生して書き出した）。 -/
def pyr9W : ℕ → Finset ℕ := fun t =>
  (([
    [],
    [0, 1, 2, 3, 4, 5, 6, 7, 8],
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16],
    [0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 19, 20, 21, 22, 23, 24],
    [0, 4, 5, 6, 7, 8, 9, 10, 11, 12, 18, 19, 20, 21, 22, 23, 24, 27, 28, 29, 30, 31, 32],
    [0, 1, 9, 10, 11, 12, 21, 22, 23, 24, 27, 28, 29, 30, 31, 32, 36, 37, 38, 39, 40],
    [0, 1, 10, 11, 12, 21, 22, 23, 24, 27, 28, 29, 36, 37, 38, 39, 40, 45, 46, 47, 48],
    [0, 1, 10, 11, 12, 21, 22, 23, 24, 27, 28, 29, 37, 38, 39, 40, 45, 46, 47, 48, 54, 55, 56],
    [0, 1, 9, 10, 11, 12, 21, 22, 23, 24, 27, 28, 29, 37, 38, 39, 40, 45, 54, 55, 56, 63, 64],
    [0, 9, 10, 11, 12, 21, 22, 23, 24, 27, 28, 29, 37, 38, 39, 40, 45, 54, 55, 56, 63, 64, 72],
    [9, 10, 11, 12, 21, 22, 23, 24, 27, 28, 29, 37, 38, 39, 40, 45, 46, 47, 48, 54, 55, 56, 72],
    [9, 10, 11, 12, 20, 21, 22, 23, 24, 27, 28, 29, 31, 36, 37, 38, 39, 40, 45, 46, 47, 48, 72],
    [9, 10, 11, 12, 21, 22, 23, 24, 27, 28, 29, 30, 31, 32, 36, 37, 38, 39, 40, 72],
    [4, 5, 6, 7, 8, 9, 10, 11, 12, 18, 19, 20, 21, 22, 23, 24, 27, 28, 29, 30, 31, 32, 72],
    [0, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 19, 20, 21, 22, 23, 24, 72],
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 72],
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 72],
    [72]] : List (List ℕ)).getD t []).toFinset

/-- 高さ 10 の証人（SAT の解。`autoresearch/jobs/night85r2_pyr_witness.py` が再生して書き出した）。 -/
def pyr10W : ℕ → Finset ℕ := fun t =>
  (([
    [],
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18],
    [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 21, 22, 23, 24, 25, 26, 27],
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 20, 21, 22, 23, 24, 25, 26, 27, 30, 31, 32, 33, 34, 35, 36],
    [0, 1, 2, 11, 20, 21, 22, 23, 24, 25, 26, 27, 30, 31, 32, 33, 34, 35, 36, 40, 41, 42, 43, 44, 45],
    [0, 1, 10, 11, 20, 21, 22, 23, 24, 25, 26, 27, 40, 41, 42, 43, 44, 45, 50, 51, 52, 53, 54],
    [0, 1, 10, 11, 21, 22, 23, 24, 25, 26, 27, 40, 41, 42, 43, 44, 45, 50, 51, 52, 53, 54, 60, 61, 62, 63],
    [0, 10, 11, 21, 22, 23, 24, 25, 26, 27, 40, 41, 42, 43, 44, 45, 50, 51, 52, 60, 61, 62, 63, 70, 71, 72],
    [0, 10, 11, 21, 22, 23, 24, 25, 26, 27, 40, 41, 42, 43, 44, 45, 50, 51, 52, 62, 63, 70, 71, 72, 80, 81],
    [10, 11, 21, 22, 23, 24, 25, 26, 27, 40, 41, 42, 43, 44, 45, 50, 51, 52, 62, 63, 70, 71, 72, 80, 81, 90],
    [10, 11, 21, 22, 23, 24, 25, 26, 27, 40, 41, 42, 43, 44, 45, 50, 51, 52, 60, 61, 62, 63, 70, 71, 72, 90],
    [10, 11, 20, 21, 22, 23, 24, 25, 26, 27, 40, 41, 42, 43, 44, 45, 50, 51, 52, 53, 54, 60, 61, 62, 63, 90],
    [7, 8, 10, 11, 20, 21, 22, 23, 24, 25, 26, 27, 30, 40, 41, 42, 43, 44, 45, 50, 51, 52, 53, 54, 90],
    [7, 8, 10, 11, 20, 21, 22, 23, 24, 25, 26, 27, 30, 31, 32, 33, 34, 35, 36, 40, 41, 42, 43, 44, 45, 90],
    [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 20, 21, 22, 23, 24, 25, 26, 27, 30, 31, 32, 33, 34, 35, 36, 90],
    [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 21, 22, 23, 24, 25, 26, 27, 90],
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 90],
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 90],
    [90]] : List (List ℕ)).getD t []).toFinset

theorem pyr9W_legal : ∀ t < 2 * 8 + 1, ∀ v ∈ pyr9W t ∪ pyr9W (t + 1),
    (v ∈ pyr9W t ∧ v ∉ pyr9W (t + 1) ∨ v ∉ pyr9W t ∧ v ∈ pyr9W (t + 1)) →
    ∀ u ∈ pyrPa 9 v, u ∈ pyr9W t ∧ u ∈ pyr9W (t + 1) := by
  intro t ht; interval_cases t <;> decide

theorem pyr10W_legal : ∀ t < 2 * 9 + 1, ∀ v ∈ pyr10W t ∪ pyr10W (t + 1),
    (v ∈ pyr10W t ∧ v ∉ pyr10W (t + 1) ∨ v ∉ pyr10W t ∧ v ∈ pyr10W (t + 1)) →
    ∀ u ∈ pyrPa 10 v, u ∈ pyr10W t ∧ u ∈ pyr10W (t + 1) := by
  intro t ht; interval_cases t <;> decide

/-- 高さ 9 のピラミッドの最小ピークは **ちょうど 23**（`3h - 4`）: 証人 `pyr9W` は時間最適な clean
    ペブリングで頂点だけを使いピーク 23、どの時間最適ペブリングも時刻 `2D-5` か `2D-3` に 23 個以上。 -/
theorem pyr9_pmin_eq_23 :
    (Pebbling (pyrPa 9) pyr9W (2 * 8 + 1) ∧ pyr9W (2 * 8 + 1) = {72} ∧
      (∀ t, t ≤ 2 * 8 + 1 → pyr9W t ⊆ pyrV 9) ∧
      ∀ t, t ≤ 2 * 8 + 1 → (pyr9W t).card ≤ 23) ∧
    (∀ P : ℕ → Finset ℕ, Pebbling (pyrPa 9) P (2 * 8 + 1) →
      72 ∈ P (2 * 8 + 1) →
      (∀ v ∈ pyrV 9, v ≠ 72 → v ∉ P (2 * 8 + 1)) →
      23 ≤ (P (2 * 8 - 5)).card ∨ 23 ≤ (P (2 * 8 - 3)).card) :=
  ⟨⟨⟨by decide, fun t ht => pyr_legalStep_of_union (pyr9W_legal t ht)⟩, by decide,
    by intro t ht; interval_cases t <;> decide,
    by intro t ht; interval_cases t <;> decide⟩,
   pyr_peak_lower_3h4 9 (by norm_num)⟩

/-- 高さ 10 のピラミッドの最小ピークは **ちょうど 26**（`3h - 4`）。 -/
theorem pyr10_pmin_eq_26 :
    (Pebbling (pyrPa 10) pyr10W (2 * 9 + 1) ∧ pyr10W (2 * 9 + 1) = {90} ∧
      (∀ t, t ≤ 2 * 9 + 1 → pyr10W t ⊆ pyrV 10) ∧
      ∀ t, t ≤ 2 * 9 + 1 → (pyr10W t).card ≤ 26) ∧
    (∀ P : ℕ → Finset ℕ, Pebbling (pyrPa 10) P (2 * 9 + 1) →
      90 ∈ P (2 * 9 + 1) →
      (∀ v ∈ pyrV 10, v ≠ 90 → v ∉ P (2 * 9 + 1)) →
      26 ≤ (P (2 * 9 - 5)).card ∨ 26 ≤ (P (2 * 9 - 3)).card) :=
  ⟨⟨⟨by decide, fun t ht => pyr_legalStep_of_union (pyr10W_legal t ht)⟩, by decide,
    by intro t ht; interval_cases t <;> decide,
    by intro t ht; interval_cases t <;> decide⟩,
   pyr_peak_lower_3h4 10 (by norm_num)⟩

/-! ### `h = 11, 12` のタイト性と `h = 13` の上界（2026-10-16・第85夜 周4）

    周 2 と同じ形: 証人は cadical の解（`autoresearch/jobs/night85r4_pyr_witness.py` が独立の再生器で確かめてから
    書き出した表）、合法性・終状態・頂点集合・ピークは `decide`。`h = 11, 12` は下界 `pyr_peak_lower_3h4` と対で
    ちょうど `3h - 4`。`h = 13` は上界 37 (`= 3h - 2`) だけを置く: 一般の下界は 35 しか出さず、
    ピーク 36 の時間最適ペブリングが無いことは Lean ではなく DRAT 証明書（`autoresearch/jobs/night85r4_pyr13_drat.py`、
    drat-trim が VERIFIED）による。したがって `3h - 4` の等号は `h = 13` で破れる（層 2）。 -/

/-- 高さ 11 の証人（SAT の解。`autoresearch/jobs/night85r4_pyr_witness.py` が再生して書き出した）。 -/
def pyr11W : ℕ → Finset ℕ := fun t =>
  (([
    [],
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20],
    [0, 1, 2, 3, 4, 5, 6, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 22, 23, 24, 25, 26, 27, 28, 29, 30],
    [0, 1, 2, 3, 4, 5, 6, 17, 18, 19, 20, 22, 23, 24, 25, 26, 27, 28, 29, 30, 33, 34, 35, 36, 37, 38, 39, 40],
    [0, 6, 7, 8, 17, 18, 19, 20, 22, 23, 24, 25, 26, 27, 33, 34, 35, 36, 37, 38, 39, 40, 44, 45, 46, 47, 48, 49, 50],
    [0, 6, 7, 8, 19, 20, 22, 23, 24, 25, 26, 27, 37, 38, 39, 40, 44, 45, 46, 47, 48, 49, 50, 55, 56, 57, 58, 59, 60],
    [0, 1, 19, 20, 22, 23, 24, 25, 26, 27, 37, 38, 39, 40, 44, 45, 46, 47, 55, 56, 57, 58, 59, 60, 66, 67, 68, 69, 70],
    [0, 1, 19, 20, 22, 23, 24, 25, 26, 27, 38, 39, 40, 44, 45, 46, 47, 58, 59, 60, 66, 67, 68, 69, 70, 77, 78, 79, 80],
    [0, 19, 20, 22, 23, 24, 25, 26, 27, 38, 39, 40, 44, 45, 46, 47, 58, 59, 60, 66, 67, 68, 77, 78, 79, 80, 88, 89, 90],
    [0, 19, 20, 22, 23, 24, 25, 26, 27, 38, 39, 40, 44, 45, 46, 47, 58, 59, 60, 66, 67, 68, 79, 80, 88, 89, 90, 99, 100],
    [19, 20, 22, 23, 24, 25, 26, 27, 38, 39, 40, 44, 45, 46, 47, 58, 59, 60, 66, 67, 68, 79, 80, 88, 89, 90, 99, 100, 110],
    [19, 20, 22, 23, 24, 25, 26, 27, 38, 39, 40, 44, 45, 46, 47, 58, 59, 60, 66, 67, 68, 77, 78, 79, 80, 88, 89, 90, 110],
    [19, 20, 22, 23, 24, 25, 26, 27, 37, 38, 39, 40, 44, 45, 46, 47, 58, 59, 60, 66, 67, 68, 69, 70, 77, 78, 79, 80, 110],
    [19, 20, 22, 23, 24, 25, 26, 27, 37, 38, 39, 40, 44, 45, 46, 47, 48, 55, 56, 57, 58, 59, 60, 66, 67, 68, 69, 70, 110],
    [6, 7, 8, 19, 20, 22, 23, 24, 25, 26, 27, 38, 39, 40, 44, 45, 46, 47, 48, 49, 50, 55, 56, 57, 58, 59, 60, 110],
    [6, 7, 8, 17, 18, 19, 20, 22, 23, 24, 25, 26, 27, 33, 34, 35, 36, 37, 38, 39, 40, 44, 45, 46, 47, 48, 49, 50, 110],
    [0, 1, 2, 3, 4, 5, 6, 17, 18, 19, 20, 22, 23, 24, 25, 26, 27, 28, 29, 30, 33, 34, 35, 36, 37, 38, 39, 40, 110],
    [0, 1, 2, 3, 4, 5, 6, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 22, 23, 24, 25, 26, 27, 28, 29, 30, 110],
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 110],
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 110],
    [110]] : List (List ℕ)).getD t []).toFinset

/-- 高さ 12 の証人（SAT の解。`autoresearch/jobs/night85r4_pyr_witness.py` が再生して書き出した）。 -/
def pyr12W : ℕ → Finset ℕ := fun t =>
  (([
    [],
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11],
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22],
    [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33],
    [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 36, 37, 38, 39, 40, 41, 42, 43, 44],
    [0, 1, 2, 12, 13, 25, 26, 27, 28, 29, 30, 31, 32, 33, 36, 37, 38, 39, 40, 41, 42, 43, 44, 48, 49, 50, 51, 52, 53, 54, 55],
    [0, 1, 2, 25, 26, 27, 28, 29, 30, 31, 32, 33, 36, 37, 38, 39, 43, 48, 49, 50, 51, 52, 53, 54, 55, 60, 61, 62, 63, 64, 65, 66],
    [25, 26, 27, 28, 29, 30, 31, 32, 33, 36, 37, 38, 39, 51, 52, 53, 54, 55, 60, 61, 62, 63, 64, 65, 66, 72, 73, 74, 75, 76, 77],
    [25, 26, 27, 28, 29, 30, 31, 32, 33, 36, 51, 52, 53, 54, 55, 60, 61, 62, 63, 64, 72, 73, 74, 75, 76, 77, 84, 85, 86, 87, 88],
    [25, 26, 27, 28, 29, 30, 31, 32, 33, 36, 51, 52, 53, 54, 55, 60, 61, 62, 63, 66, 75, 76, 77, 84, 85, 86, 87, 88, 96, 97, 98, 99],
    [25, 26, 27, 28, 29, 30, 31, 32, 33, 36, 51, 52, 53, 54, 55, 60, 61, 62, 73, 75, 76, 77, 84, 85, 86, 96, 97, 98, 99, 108, 109, 110],
    [25, 26, 27, 28, 29, 30, 31, 32, 33, 36, 51, 52, 53, 54, 55, 60, 61, 62, 75, 76, 77, 84, 85, 86, 96, 98, 99, 108, 109, 110, 120, 121],
    [25, 26, 27, 28, 29, 30, 31, 32, 33, 36, 51, 52, 53, 54, 55, 60, 61, 62, 75, 76, 77, 84, 85, 86, 98, 99, 108, 109, 110, 120, 121, 132],
    [25, 26, 27, 28, 29, 30, 31, 32, 33, 36, 51, 52, 53, 54, 55, 60, 61, 62, 75, 76, 77, 84, 85, 86, 96, 97, 98, 99, 108, 109, 110, 132],
    [25, 26, 27, 28, 29, 30, 31, 32, 33, 36, 51, 52, 53, 54, 55, 60, 61, 62, 63, 75, 76, 77, 84, 85, 86, 87, 88, 96, 97, 98, 99, 132],
    [25, 26, 27, 28, 29, 30, 31, 32, 33, 36, 39, 51, 52, 53, 54, 55, 60, 61, 62, 63, 72, 73, 74, 75, 76, 77, 84, 85, 86, 87, 88, 132],
    [25, 26, 27, 28, 29, 30, 31, 32, 33, 36, 37, 38, 39, 51, 52, 53, 54, 55, 60, 61, 62, 63, 64, 65, 66, 72, 73, 74, 75, 76, 77, 132],
    [0, 1, 2, 25, 26, 27, 28, 29, 30, 31, 32, 33, 36, 37, 38, 39, 48, 49, 50, 51, 52, 53, 54, 55, 60, 61, 62, 63, 64, 65, 66, 132],
    [0, 1, 2, 12, 13, 25, 26, 27, 28, 29, 30, 31, 32, 33, 36, 37, 38, 39, 40, 41, 42, 43, 44, 48, 49, 50, 51, 52, 53, 54, 55, 132],
    [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 36, 37, 38, 39, 40, 41, 42, 43, 44, 132],
    [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 132],
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 132],
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 132],
    [132]] : List (List ℕ)).getD t []).toFinset

/-- 高さ 13 の証人（SAT の解。`autoresearch/jobs/night85r4_pyr_witness.py` が再生して書き出した）。 -/
def pyr13W : ℕ → Finset ℕ := fun t =>
  (([
    [],
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24],
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36],
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 22, 23, 24, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48],
    [9, 10, 11, 12, 22, 23, 24, 26, 27, 28, 29, 30, 31, 32, 33, 34, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 52, 53, 54, 55, 56, 57, 58, 59, 60],
    [9, 10, 11, 12, 26, 27, 28, 29, 30, 31, 32, 33, 34, 42, 43, 44, 45, 46, 47, 48, 52, 53, 54, 55, 56, 57, 58, 59, 60, 65, 66, 67, 68, 69, 70, 71, 72],
    [1, 26, 27, 28, 29, 30, 31, 32, 33, 34, 42, 43, 44, 45, 46, 47, 48, 52, 53, 54, 56, 60, 65, 66, 67, 68, 69, 70, 71, 72, 78, 79, 80, 81, 82, 83, 84],
    [26, 27, 28, 29, 30, 31, 32, 33, 34, 43, 44, 47, 48, 52, 53, 54, 67, 68, 69, 70, 71, 72, 78, 79, 80, 81, 82, 83, 84, 91, 92, 93, 94, 95, 96],
    [26, 27, 28, 29, 30, 31, 32, 33, 34, 46, 47, 48, 52, 53, 54, 67, 68, 69, 70, 71, 72, 78, 79, 80, 81, 91, 92, 93, 94, 95, 96, 104, 105, 106, 107, 108],
    [26, 27, 28, 29, 30, 31, 32, 33, 34, 47, 48, 52, 53, 54, 67, 68, 69, 70, 71, 72, 78, 79, 80, 81, 94, 95, 96, 104, 105, 106, 107, 108, 117, 118, 119, 120],
    [26, 27, 28, 29, 30, 31, 32, 33, 34, 47, 48, 52, 53, 54, 66, 67, 68, 69, 70, 71, 72, 78, 79, 94, 95, 96, 104, 105, 106, 117, 118, 119, 120, 130, 131, 132],
    [26, 27, 28, 29, 30, 31, 32, 33, 34, 47, 48, 52, 53, 54, 66, 67, 68, 69, 70, 71, 72, 78, 80, 94, 95, 96, 104, 105, 106, 119, 120, 130, 131, 132, 143, 144],
    [1, 26, 27, 28, 29, 30, 31, 32, 33, 34, 47, 48, 52, 53, 54, 66, 67, 68, 69, 70, 71, 72, 78, 94, 95, 96, 104, 105, 106, 119, 120, 130, 131, 132, 143, 144, 156],
    [26, 27, 28, 29, 30, 31, 32, 33, 34, 47, 48, 52, 53, 54, 66, 67, 68, 69, 70, 71, 72, 78, 79, 94, 95, 96, 104, 105, 106, 117, 118, 119, 120, 130, 131, 132, 156],
    [26, 27, 28, 29, 30, 31, 32, 33, 34, 47, 48, 52, 53, 54, 67, 68, 69, 70, 71, 72, 78, 79, 80, 81, 94, 95, 96, 104, 105, 106, 107, 108, 117, 118, 119, 120, 156],
    [26, 27, 28, 29, 30, 31, 32, 33, 34, 42, 47, 48, 52, 53, 54, 67, 68, 69, 70, 71, 72, 78, 79, 80, 81, 91, 92, 93, 94, 95, 96, 104, 105, 106, 107, 108, 156],
    [26, 27, 28, 29, 30, 31, 32, 33, 34, 39, 42, 43, 47, 48, 52, 53, 54, 67, 68, 69, 70, 71, 72, 78, 79, 80, 81, 82, 83, 84, 91, 92, 93, 94, 95, 96, 156],
    [11, 26, 27, 28, 29, 30, 31, 32, 33, 34, 42, 43, 44, 45, 46, 47, 48, 52, 53, 54, 55, 65, 66, 67, 68, 69, 70, 71, 72, 78, 79, 80, 81, 82, 83, 84, 156],
    [9, 10, 11, 12, 26, 27, 28, 29, 30, 31, 32, 33, 34, 43, 44, 45, 46, 47, 48, 52, 53, 54, 55, 56, 57, 58, 59, 60, 65, 66, 67, 68, 69, 70, 71, 72, 156],
    [9, 10, 11, 12, 22, 23, 24, 26, 27, 28, 29, 30, 31, 32, 33, 34, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 52, 53, 54, 55, 56, 57, 58, 59, 60, 156],
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 22, 23, 24, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 156],
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 156],
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 156],
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 156],
    [156]] : List (List ℕ)).getD t []).toFinset

theorem pyr11W_legal : ∀ t < 2 * 10 + 1, ∀ v ∈ pyr11W t ∪ pyr11W (t + 1),
    (v ∈ pyr11W t ∧ v ∉ pyr11W (t + 1) ∨ v ∉ pyr11W t ∧ v ∈ pyr11W (t + 1)) →
    ∀ u ∈ pyrPa 11 v, u ∈ pyr11W t ∧ u ∈ pyr11W (t + 1) := by
  intro t ht; interval_cases t <;> decide

set_option maxRecDepth 8000 in
theorem pyr12W_legal : ∀ t < 2 * 11 + 1, ∀ v ∈ pyr12W t ∪ pyr12W (t + 1),
    (v ∈ pyr12W t ∧ v ∉ pyr12W (t + 1) ∨ v ∉ pyr12W t ∧ v ∈ pyr12W (t + 1)) →
    ∀ u ∈ pyrPa 12 v, u ∈ pyr12W t ∧ u ∈ pyr12W (t + 1) := by
  intro t ht; interval_cases t <;> decide

set_option maxRecDepth 8000 in
theorem pyr13W_legal : ∀ t < 2 * 12 + 1, ∀ v ∈ pyr13W t ∪ pyr13W (t + 1),
    (v ∈ pyr13W t ∧ v ∉ pyr13W (t + 1) ∨ v ∉ pyr13W t ∧ v ∈ pyr13W (t + 1)) →
    ∀ u ∈ pyrPa 13 v, u ∈ pyr13W t ∧ u ∈ pyr13W (t + 1) := by
  intro t ht; interval_cases t <;> decide

/-- 高さ 11 のピラミッドの最小ピークは **ちょうど 29**（`3h - 4`）。 -/
theorem pyr11_pmin_eq_29 :
    (Pebbling (pyrPa 11) pyr11W (2 * 10 + 1) ∧ pyr11W (2 * 10 + 1) = {110} ∧
      (∀ t, t ≤ 2 * 10 + 1 → pyr11W t ⊆ pyrV 11) ∧
      ∀ t, t ≤ 2 * 10 + 1 → (pyr11W t).card ≤ 29) ∧
    (∀ P : ℕ → Finset ℕ, Pebbling (pyrPa 11) P (2 * 10 + 1) →
      110 ∈ P (2 * 10 + 1) →
      (∀ v ∈ pyrV 11, v ≠ 110 → v ∉ P (2 * 10 + 1)) →
      29 ≤ (P (2 * 10 - 5)).card ∨ 29 ≤ (P (2 * 10 - 3)).card) :=
  ⟨⟨⟨by decide, fun t ht => pyr_legalStep_of_union (pyr11W_legal t ht)⟩, by decide,
    by intro t ht; interval_cases t <;> decide,
    by intro t ht; interval_cases t <;> decide⟩,
   pyr_peak_lower_3h4 11 (by norm_num)⟩

/-- 高さ 12 のピラミッドの最小ピークは **ちょうど 32**（`3h - 4`）。 -/
theorem pyr12_pmin_eq_32 :
    (Pebbling (pyrPa 12) pyr12W (2 * 11 + 1) ∧ pyr12W (2 * 11 + 1) = {132} ∧
      (∀ t, t ≤ 2 * 11 + 1 → pyr12W t ⊆ pyrV 12) ∧
      ∀ t, t ≤ 2 * 11 + 1 → (pyr12W t).card ≤ 32) ∧
    (∀ P : ℕ → Finset ℕ, Pebbling (pyrPa 12) P (2 * 11 + 1) →
      132 ∈ P (2 * 11 + 1) →
      (∀ v ∈ pyrV 12, v ≠ 132 → v ∉ P (2 * 11 + 1)) →
      32 ≤ (P (2 * 11 - 5)).card ∨ 32 ≤ (P (2 * 11 - 3)).card) :=
  ⟨⟨⟨by decide, fun t ht => pyr_legalStep_of_union (pyr12W_legal t ht)⟩, by decide,
    by intro t ht; interval_cases t <;> decide,
    by intro t ht; interval_cases t <;> decide⟩,
   pyr_peak_lower_3h4 12 (by norm_num)⟩

set_option maxRecDepth 8000 in
/-- 高さ 13 のピラミッドにはピーク 37 の時間最適 clean ペブリングがある（上界のみ。下界 37 は DRAT）。 -/
theorem pyr13_peak_le_37 :
    (Pebbling (pyrPa 13) pyr13W (2 * 12 + 1) ∧ pyr13W (2 * 12 + 1) = {156} ∧
      (∀ t, t ≤ 2 * 12 + 1 → pyr13W t ⊆ pyrV 13) ∧
      ∀ t, t ≤ 2 * 12 + 1 → (pyr13W t).card ≤ 37) :=
  ⟨⟨by decide, fun t ht => pyr_legalStep_of_union (pyr13W_legal t ht)⟩, by decide,
    by intro t ht; interval_cases t <;> decide,
    by intro t ht; interval_cases t <;> decide⟩

end PyramidPeakGeneric

/-! ## 4. 有限 DAG での両側（`paD`: `0 → 2 ← 1`）

    `par_time_exact_dag` の上界（`layered` 構成）と、上で直した下界を
    **同じ有限 DAG** に適用して突き合わせる。これが `time_lower_bound_path` では
    できなかったこと（`paD_no_infinite_path`）。 -/

/-! ## 3.5 鎖への適用: 構造補題 L1 / L2 の厳密形

    `data/q2_structure_lemmas.md` の L1（初出時刻は固定）と L2（最終除去は降順）を
    **厳密な等式の形**で得る。L1 は「ほぼ強制」と書かれたまま未証明で、そのため
    `scripts/q2_cnf.py --fix-first` の UNSAT を不可能性の根拠に使えなかった。
    以下で L1 が証明されるので、**その制限が外れる**。 -/

/-- 鎖 `0 → 1 → ⋯`。`paL (v+1) = {v}`、`paL 0 = ∅`。 -/
def paL : ℕ → Finset ℕ := fun v => if v = 0 then ∅ else {v - 1}

/-- **鎖の窓定理（L1 と L2 の厳密形）**。

    頂点数 `n = d+2` の鎖を時間最適 `T = 2d+3 = 2n-1` で clean にペブリングするとき、
    各頂点 `j ≤ d` について

    * **L1**: `j ∈ P (j+1)`（初出時刻はちょうど `j+1`。下界と合わせて等式）
    * **L2**: `j ∈ P (2d+2-j)` かつ `t ≤ 2d+2-j`（最終存在時刻はちょうど `2d+2-j = T-1-j`）

    L2 は元の文書の「`τ` が降順」より強く、**値そのものを決めている**。 -/
theorem chain_window {P : ℕ → Finset ℕ} {d : ℕ}
    (hp : Pebbling paL P (2 * d + 3))
    (hsink : d + 1 ∈ P (2 * d + 3))
    (hg : ∀ i, i ≤ d → i ∉ P (2 * d + 3)) :
    ∀ j, j ≤ d →
      j ∈ P (j + 1) ∧ j ∈ P (2 * d + 2 - j) ∧
      (∀ t, t ≤ 2 * d + 3 → j ∈ P t → j + 1 ≤ t ∧ t ≤ 2 * d + 2 - j) := by
  have hw : ∀ j, j ≤ d → (id j) ∈ paL (id (j + 1)) := by
    intro j _
    simp [paL, id]
  exact no_slack (w := id) hp hw hsink hg

/-- **鎖の sink も最早時刻に置かれる**: `d+1 ∈ P (d+2)`。
    頂点数 `n = d+2` なので、sink は時刻 `n` にちょうど置かれる。 -/
theorem chain_sink_at_n {P : ℕ → Finset ℕ} {d : ℕ}
    (hp : Pebbling paL P (2 * d + 3))
    (hsink : d + 1 ∈ P (2 * d + 3))
    (hg : ∀ i, i ≤ d → i ∉ P (2 * d + 3)) :
    d + 1 ∈ P (d + 2) := by
  have hw : ∀ j, j ≤ d → (id j) ∈ paL (id (j + 1)) := by
    intro j _
    simp [paL, id]
  exact present_at_window_start (w := id) hp hw hsink hg (d + 1) (le_refl _)

/-- **鎖の sink は置かれたら二度と消えない**: `d+2 ≤ t ≤ 2d+3` なら `d+1 ∈ P t`。

    証明: sink を消すには親 `d` が前後の両方に要る。ところが `d` の窓の右端は
    `2d+2-d = d+2` なので、消せる瞬間は `t = d+2` 以前しかない。
    一方 sink は `d+2` より前には居られない（深さの下界）ので、消す瞬間が存在しない。

    CNF ではこれが `x[sink][t] = 1`（`t ≥ n`）という **n 本の単位節**になる。 -/
theorem chain_sink_stays {P : ℕ → Finset ℕ} {d : ℕ}
    (hp : Pebbling paL P (2 * d + 3))
    (hsink : d + 1 ∈ P (2 * d + 3))
    (hg : ∀ i, i ≤ d → i ∉ P (2 * d + 3)) :
    ∀ t, d + 2 ≤ t → t ≤ 2 * d + 3 → d + 1 ∈ P t := by
  intro t ht1 ht2
  by_contra hno
  have hstart := chain_sink_at_n hp hsink hg
  obtain ⟨r, hr1, hr2, hr3, hr4⟩ := exists_removal ht1 hstart hno
  have hch : Changed (P (r - 1)) (P r) (d + 1) := Or.inl ⟨hr3, hr4⟩
  have heq : r - 1 + 1 = r := by omega
  have hpar := hp.legal (r - 1) (by omega) _ (by rw [heq]; exact hch) d (by simp [paL])
  have hd : d ∈ P r := by rw [← heq]; exact hpar.2
  have hwin := (chain_window hp hsink hg d (le_refl d)).2.2 r (by omega) hd
  omega

/-- **両側（一般の有限 DAG）**。`par_time_exact_dag` の上界と、直した下界を
    同じ仮定の下で並べる。sink へ至る深さ `d` の路 `w 0 → ⋯ → w d = sink` を
    明示的に与えるので、**有限 DAG でも仮定が満たせる**（`paD` で確認済み）。

    結論: 空間無制約なら時間最適値はちょうど `2d + 1`。 -/
theorem par_time_exact_dag_two_sided
    {V : Finset ℕ} {dep : ℕ → ℕ} {sink d : ℕ} {w : ℕ → ℕ}
    (hs : sink ∈ V) (hds : dep sink = d) (hd : 1 ≤ d)
    (hmax : ∀ v ∈ V, dep v ≤ d) (huniq : ∀ v ∈ V, dep v = d → v = sink)
    (hpaV : ∀ v ∈ V, ∀ u ∈ pa v, u ∈ V)
    (hpad : ∀ v ∈ V, ∀ u ∈ pa v, dep u < dep v)
    (hw : ∀ j, j < d → w j ∈ pa (w (j + 1))) (hwd : w d = sink) :
    (Pebbling pa (layered V dep sink d) (2 * d + 1) ∧
      layered V dep sink d (2 * d + 1) = {sink}) ∧
    (∀ (P : ℕ → Finset ℕ) (T : ℕ), Pebbling pa P T → sink ∈ P T →
      (∀ j, j < d → w j ∉ P T) → 2 * d + 1 ≤ T) := by
  refine ⟨par_time_exact_dag hs hds hd hmax huniq hpaV hpad, ?_⟩
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  intro P T hp hsink hgone
  have hw' : ∀ j, j ≤ e → w j ∈ pa (w (j + 1)) := fun j hj => hw j (by omega)
  have hsink' : w (e + 1) ∈ P T := by rw [hwd]; exact hsink
  have hgone' : ∀ j, j ≤ e → w j ∉ P T := fun j hj => hgone j (by omega)
  have := time_lower_bound_seg hp hw' hsink' hgone'
  omega

section PaD

/-- 路 `0 → 2`。`d = 0` なので必要なのは `j ≤ 0` の 1 段だけ。 -/
def wD : ℕ → ℕ := fun j => if j = 0 then 0 else 2

/-- **下界が `paD` に適用できる。** 頂点 2 を残し頂点 0 を消すなら `T ≥ 3`。 -/
theorem paD_time_lower {P : ℕ → Finset ℕ} {T : ℕ}
    (hp : Pebbling paD P T) (hsink : 2 ∈ P T) (hgone : 0 ∉ P T) : 3 ≤ T := by
  have hw : ∀ j, j ≤ 0 → wD j ∈ paD (wD (j + 1)) := by
    intro j hj
    have hj0 : j = 0 := Nat.le_zero.mp hj
    subst hj0
    decide
  -- `wD (0+1) = 2` も `wD 0 = 0` も定義的に等しいので、そのまま渡せる。
  have hs : wD (0 + 1) ∈ P T := hsink
  have hg : ∀ j, j ≤ 0 → wD j ∉ P T := by
    intro j hj
    have hj0 : j = 0 := Nat.le_zero.mp hj
    subst hj0
    exact hgone
  have h : 2 * 0 + 3 ≤ T := time_lower_bound_seg (d := 0) (w := wD) hp hw hs hg
  omega

/-- **両側（有限 DAG）。** `paD` について、時間最適値はちょうど 3 である。

    * 上界: `layered VD depD 2 1` が長さ 3 の合法な列で、終状態は `{2}`
    * 下界: 2 を残し 0 を消すどんな列も長さ 3 以上（`paD_time_lower`） -/
theorem par_time_exact_paD :
    (Pebbling paD (layered VD depD 2 1) 3 ∧ layered VD depD 2 1 3 = {2}) ∧
    (∀ (P : ℕ → Finset ℕ) (T : ℕ), Pebbling paD P T → 2 ∈ P T → 0 ∉ P T → 3 ≤ T) := by
  refine ⟨?_, fun P T hp hs hg => paD_time_lower hp hs hg⟩
  have := par_time_exact_dag (pa := paD) (V := VD) (dep := depD) (sink := 2) (d := 1)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  simpa using this

/-- **非空虚性の要**: `no_slack` を `paD` の実際の列に適用する（`d = 0`, `T = 3`）。

    抽象定理は仮定が満たせなければ空虚なので、`layered VD depD 2 1` という
    具体的な配置列に対して実際に適用し、結論が計算値と一致することを確かめる。
    頂点 0 の窓は `[1, 2]` で、両端 1 と 2 の**両方**に居る。 -/
theorem paD_no_slack_applied :
    wD 0 ∈ layered VD depD 2 1 1 ∧ wD 0 ∈ layered VD depD 2 1 2 := by
  have hp : Pebbling paD (layered VD depD 2 1) (2 * 0 + 3) := by
    simpa using par_time_exact_paD.1.1
  have hw : ∀ j, j ≤ 0 → wD j ∈ paD (wD (j + 1)) := by
    intro j hj
    have hj0 : j = 0 := Nat.le_zero.mp hj
    subst hj0
    decide
  have hsink : wD (0 + 1) ∈ layered VD depD 2 1 (2 * 0 + 3) := by decide
  have hg : ∀ i, i ≤ 0 → wD i ∉ layered VD depD 2 1 (2 * 0 + 3) := by
    intro i hi
    have hi0 : i = 0 := Nat.le_zero.mp hi
    subst hi0
    decide
  have h := no_slack hp hw hsink hg 0 (le_refl 0)
  exact ⟨h.1, by simpa using h.2.1⟩

/-- **深さ関数版の非空虚性**: `present_at_dep` を分岐のある DAG `paD`（`0 → 2 ← 1`）に
    実適用する。sink `2` は親を **2 つ**持つので、鎖では試せない形になっている。

    結論は「各頂点 `v` は `dep v + 1` と `dep v + 2` の両方に居る」で、
    実際の列 `∅ → {0,1} → {0,1,2} → {2}` と一致する。 -/
theorem paD_present_at_dep_applied :
    (0 : ℕ) ∈ layered VD depD 2 1 1 ∧ (0 : ℕ) ∈ layered VD depD 2 1 2 ∧
    (2 : ℕ) ∈ layered VD depD 2 1 2 ∧ (2 : ℕ) ∈ layered VD depD 2 1 3 := by
  have hp : Pebbling paD (layered VD depD 2 1) (2 * 1 + 1) := par_time_exact_paD.1.1
  have h := present_at_dep (V := VD) (dep := depD) (sink := 2) (D := 1) hp
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have h0 := h 0 (by decide)
  have h2 := h 2 (by decide)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [depD] using h0.1
  · simpa [depD] using h0.2
  · simpa [depD] using h2.1
  · simpa [depD] using h2.2

/-- **非空虚性（下界がタイトな例）**: `paD`（`0 → 2 ← 1`、深さ 0 が 2 個・深さ 1 が 1 個）に
    `peak_lower_left` を `k = 0` で当てると「時刻 2 に 3 頂点すべてが居る」となり、
    実際 `layered VD depD 2 1 2 = {0,1,2}` と一致する。**下界 3 は達成される。** -/
theorem paD_peak_lower_tight :
    VD.filter (fun v => depD v = 0 ∨ depD v = 0 + 1) ⊆ layered VD depD 2 1 (0 + 2) ∧
    (VD.filter (fun v => depD v = 0 ∨ depD v = 0 + 1)).card = 3 ∧
    (layered VD depD 2 1 2).card = 3 := by
  refine ⟨?_, by decide, by decide⟩
  have hp : Pebbling paD (layered VD depD 2 1) (2 * 1 + 1) := par_time_exact_paD.1.1
  exact peak_lower_left (V := VD) (dep := depD) (sink := 2) (D := 1) hp
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) 0

/-- 窓定理を具体列で確かめる。頂点 0（深さ 0・最終状態に残らない）の窓は
    `[1, T-1] = [1, 2]`。実際の列でも 1 と 2 にのみ居る。 -/
theorem paD_window_check :
    0 ∉ layered VD depD 2 1 0 ∧ 0 ∈ layered VD depD 2 1 1 ∧
    0 ∈ layered VD depD 2 1 2 ∧ 0 ∉ layered VD depD 2 1 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

end PaD

/-! ## 5. ⭐ ピラミッド $h = 3, 4, 5$ の $p_{\min}$ を**完全に機械証明**する

    下界（`peak_lower_right`）と上界（`alt_par_time_exact`）が一致するので、
    $p_{\min}(\mathrm{pyr}\,h)$ が**両側とも機械証明**で決まる:

    | $h$ | 2 | 3 | 4 | 5 |
    |---|---|---|---|---|
    | $p_{\min}$ | 3 | **6** | **8** | **10** |

    （$h=2$ は `paD` = `0 → 2 ← 1` として既に扱っている。）
    $h \ge 6$ では下界（$2h$）と上界が離れるので、この方法では決まらない。 -/

section Pyramids

/-! ### $h = 3$（頂点 6・深さ 2） -/

def paP3 : ℕ → Finset ℕ := fun v =>
  if v = 3 then {0, 1} else if v = 4 then {1, 2} else if v = 5 then {3, 4} else ∅
def depP3 : ℕ → ℕ := fun v => if v ≤ 2 then 0 else if v ≤ 4 then 1 else 2
def VP3 : Finset ℕ := {0, 1, 2, 3, 4, 5}

/-- **$p_{\min}(\mathrm{pyr}\,3) = 6$。** 上界は `alt`（ピーク 6）、下界は
    「時刻 3 に深さ 0・1 の 5 頂点と sink が同時に居る」。 -/
theorem pyr3_pmin_eq_six :
    (Pebbling paP3 (alt VP3 depP3 5 2) (2 * 2 + 1) ∧
      alt VP3 depP3 5 2 (2 * 2 + 1) = {5} ∧
      ∀ t, t ≤ 2 * 2 + 1 → (alt VP3 depP3 5 2 t).card ≤ 6) ∧
    (∀ P : ℕ → Finset ℕ, Pebbling paP3 P (2 * 2 + 1) → (5 : ℕ) ∈ P (2 * 2 + 1) →
      (∀ v ∈ VP3, v ≠ 5 → v ∉ P (2 * 2 + 1)) → 6 ≤ (P 3).card) := by
  constructor
  · refine ⟨(alt_par_time_exact (pa := paP3) (V := VP3) (dep := depP3) (sink := 5) (d := 2)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).1,
      (alt_par_time_exact (pa := paP3) (V := VP3) (dep := depP3) (sink := 5) (d := 2)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).2,
      ?_⟩
    intro t ht
    interval_cases t <;> decide
  · intro P hp hsin hgone
    have hsub := peak_lower_right (pa := paP3) (V := VP3) (dep := depP3) (sink := 5) (D := 2)
      hp (by decide) (by decide) (by decide) (by decide) hgone
      (by decide) (by decide) (by decide) hsin (by decide) 0 (by omega)
    have ht : 2 * 2 - 0 - 1 = 3 := by norm_num
    rw [ht] at hsub
    have hcard : (insert 5 (VP3.filter
        (fun v => (depP3 v = 0 ∨ depP3 v = 0 + 1) ∧ v ≠ 5))).card = 6 := by decide
    have := Finset.card_le_card hsub
    omega

/-! ### $h = 4$（頂点 10・深さ 3） -/

def paP4 : ℕ → Finset ℕ := fun v =>
  if v = 4 then {0, 1} else if v = 5 then {1, 2} else if v = 6 then {2, 3}
  else if v = 7 then {4, 5} else if v = 8 then {5, 6} else if v = 9 then {7, 8} else ∅
def depP4 : ℕ → ℕ := fun v => if v ≤ 3 then 0 else if v ≤ 6 then 1 else if v ≤ 8 then 2 else 3
def VP4 : Finset ℕ := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}

/-- **$p_{\min}(\mathrm{pyr}\,4) = 8$。** -/
theorem pyr4_pmin_eq_eight :
    (Pebbling paP4 (alt VP4 depP4 9 3) (2 * 3 + 1) ∧
      alt VP4 depP4 9 3 (2 * 3 + 1) = {9} ∧
      ∀ t, t ≤ 2 * 3 + 1 → (alt VP4 depP4 9 3 t).card ≤ 8) ∧
    (∀ P : ℕ → Finset ℕ, Pebbling paP4 P (2 * 3 + 1) → (9 : ℕ) ∈ P (2 * 3 + 1) →
      (∀ v ∈ VP4, v ≠ 9 → v ∉ P (2 * 3 + 1)) → 8 ≤ (P 5).card) := by
  constructor
  · refine ⟨(alt_par_time_exact (pa := paP4) (V := VP4) (dep := depP4) (sink := 9) (d := 3)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).1,
      (alt_par_time_exact (pa := paP4) (V := VP4) (dep := depP4) (sink := 9) (d := 3)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).2,
      ?_⟩
    intro t ht
    interval_cases t <;> decide
  · intro P hp hsin hgone
    have hsub := peak_lower_right (pa := paP4) (V := VP4) (dep := depP4) (sink := 9) (D := 3)
      hp (by decide) (by decide) (by decide) (by decide) hgone
      (by decide) (by decide) (by decide) hsin (by decide) 0 (by omega)
    have ht : 2 * 3 - 0 - 1 = 5 := by norm_num
    rw [ht] at hsub
    have hcard : (insert 9 (VP4.filter
        (fun v => (depP4 v = 0 ∨ depP4 v = 0 + 1) ∧ v ≠ 9))).card = 8 := by decide
    have := Finset.card_le_card hsub
    omega


/-! ### $h = 5$（頂点 15・深さ 4） -/

def paP5 : ℕ → Finset ℕ := fun v =>
  if v = 5 then {0, 1} else if v = 6 then {1, 2} else if v = 7 then {2, 3}
  else if v = 8 then {3, 4} else if v = 9 then {5, 6} else if v = 10 then {6, 7}
  else if v = 11 then {7, 8} else if v = 12 then {9, 10} else if v = 13 then {10, 11}
  else if v = 14 then {12, 13} else ∅
def depP5 : ℕ → ℕ := fun v =>
  if v ≤ 4 then 0 else if v ≤ 8 then 1 else if v ≤ 11 then 2 else if v ≤ 13 then 3 else 4
def VP5 : Finset ℕ := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14}

/-- **$p_{\min}(\mathrm{pyr}\,5) = 10$。** -/
theorem pyr5_pmin_eq_ten :
    (Pebbling paP5 (alt VP5 depP5 14 4) (2 * 4 + 1) ∧
      alt VP5 depP5 14 4 (2 * 4 + 1) = {14} ∧
      ∀ t, t ≤ 2 * 4 + 1 → (alt VP5 depP5 14 4 t).card ≤ 10) ∧
    (∀ P : ℕ → Finset ℕ, Pebbling paP5 P (2 * 4 + 1) → (14 : ℕ) ∈ P (2 * 4 + 1) →
      (∀ v ∈ VP5, v ≠ 14 → v ∉ P (2 * 4 + 1)) → 10 ≤ (P 7).card) := by
  constructor
  · refine ⟨(alt_par_time_exact (pa := paP5) (V := VP5) (dep := depP5) (sink := 14) (d := 4)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).1,
      (alt_par_time_exact (pa := paP5) (V := VP5) (dep := depP5) (sink := 14) (d := 4)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).2,
      ?_⟩
    intro t ht
    interval_cases t <;> decide
  · intro P hp hsin hgone
    have hsub := peak_lower_right (pa := paP5) (V := VP5) (dep := depP5) (sink := 14) (D := 4)
      hp (by decide) (by decide) (by decide) (by decide) hgone
      (by decide) (by decide) (by decide) hsin (by decide) 0 (by omega)
    have ht : 2 * 4 - 0 - 1 = 7 := by norm_num
    rw [ht] at hsub
    have hcard : (insert 14 (VP5.filter
        (fun v => (depP5 v = 0 ∨ depP5 v = 0 + 1) ∧ v ≠ 14))).card = 10 := by decide
    have := Finset.card_le_card hsub
    omega


/-! ### ⚠ 定義が本当にピラミッドであることの検査

    上の定理は `paP3` / `paP4` / `paP5` が**そう定義されているもの**についての主張なので、
    定義を打ち間違えても定理は（別の DAG について）真のままになりうる。
    実際、変異注入で `paP5 12` の親を 1 本落としても検出できなかった。
    そこで**構造そのもの**を固定する: 深さ 0 の頂点だけが親を持たず、
    それ以外はちょうど 2 つの親を持ち、深さごとの頂点数が `h, h-1, …, 1` である。 -/

theorem paP3_is_pyramid :
    (∀ v ∈ VP3, depP3 v = 0 ↔ paP3 v = ∅) ∧
    (∀ v ∈ VP3, depP3 v ≠ 0 → (paP3 v).card = 2) ∧
    (VP3.filter (fun v => depP3 v = 0)).card = 3 ∧
    (VP3.filter (fun v => depP3 v = 1)).card = 2 ∧
    (VP3.filter (fun v => depP3 v = 2)).card = 1 := by decide

theorem paP4_is_pyramid :
    (∀ v ∈ VP4, depP4 v = 0 ↔ paP4 v = ∅) ∧
    (∀ v ∈ VP4, depP4 v ≠ 0 → (paP4 v).card = 2) ∧
    (VP4.filter (fun v => depP4 v = 0)).card = 4 ∧
    (VP4.filter (fun v => depP4 v = 1)).card = 3 ∧
    (VP4.filter (fun v => depP4 v = 2)).card = 2 ∧
    (VP4.filter (fun v => depP4 v = 3)).card = 1 := by decide

theorem paP5_is_pyramid :
    (∀ v ∈ VP5, depP5 v = 0 ↔ paP5 v = ∅) ∧
    (∀ v ∈ VP5, depP5 v ≠ 0 → (paP5 v).card = 2) ∧
    (VP5.filter (fun v => depP5 v = 0)).card = 5 ∧
    (VP5.filter (fun v => depP5 v = 1)).card = 4 ∧
    (VP5.filter (fun v => depP5 v = 2)).card = 3 ∧
    (VP5.filter (fun v => depP5 v = 3)).card = 2 ∧
    (VP5.filter (fun v => depP5 v = 4)).card = 1 := by decide

end Pyramids

/-! ## 3.99995 一般の高さのピラミッドの符号化の固定（2026-10-16・第86夜 周3）

    `pyr_peak_lower_3h4`・`pyr8_pmin_eq_20` 〜 `pyr12_pmin_eq_32` は一般の符号化
    `pyrPa`・`pyrV`・`pyrDep` の上で述べている。`paP5_is_pyramid` ほか（`h ≤ 7` の具体の符号化）
    と同じ固定を、ここで**一般の `h`** について与える: 親を持たないのはちょうど深さ 0、
    それ以外は親がちょうど 2 つで、どちらも頂点集合に入り深さが 1 つ浅い。層 `k` の大きさは `h - k`。
    ⚠ これが無いと、`pyrPa` を打ち間違えても上の定理は**別の DAG について**真のままになる。 -/
section PyramidGenericShape

/-- 深さ `k` の頂点はちょうど層 `k`。 -/
theorem pyr_level_filter {h k : ℕ} (hk : k < h) :
    (pyrV h).filter (fun v => pyrDep h v = k) = pyrLevel h k := by
  have hpos : 0 < h := by omega
  ext v
  rw [Finset.mem_filter, mem_pyrV hpos, mem_pyrLevel]
  simp only [pyrDep]
  constructor
  · rintro ⟨⟨_, h2⟩, rfl⟩
    exact ⟨v % h, by omega, (Nat.div_add_mod v h).symm⟩
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨a, b⟩ := pyr_divmod (k := k) (show i < h by omega)
    rw [a, b]
    omega

/-- 層 `k` の大きさは `h - k`。 -/
theorem pyrLevel_card (h k : ℕ) : (pyrLevel h k).card = h - k := by
  unfold pyrLevel
  rw [Finset.card_image_of_injective _ (add_right_injective (h * k)), Finset.card_range]

/-- **一般の符号化はピラミッドである**（`h ≥ 1`）。 -/
theorem pyr_is_pyramid (h : ℕ) (hpos : 0 < h) :
    (∀ v ∈ pyrV h, pyrDep h v = 0 ↔ pyrPa h v = ∅) ∧
    (∀ v ∈ pyrV h, pyrDep h v ≠ 0 → (pyrPa h v).card = 2) ∧
    (∀ v ∈ pyrV h, ∀ u ∈ pyrPa h v, u ∈ pyrV h ∧ pyrDep h u + 1 = pyrDep h v) ∧
    (∀ k < h, ((pyrV h).filter (fun v => pyrDep h v = k)).card = h - k) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v _
    simp only [pyrDep]
    constructor
    · intro hk
      simp [pyrPa, hk]
    · intro he
      by_contra hk
      rw [pyrPa_pos hk] at he
      simp at he
  · intro v _ hd
    simp only [pyrDep] at hd
    rw [pyrPa_pos hd]
    exact Finset.card_pair (by omega)
  · intro v hv u hu
    refine ⟨pyr_closed hpos v hv u hu, ?_⟩
    rw [mem_pyrV hpos] at hv
    obtain ⟨h1, h2⟩ := hv
    simp only [pyrDep]
    by_cases hk : v / h = 0
    · simp [pyrPa, hk] at hu
    · rw [pyrPa_pos hk] at hu
      have hm := Nat.mod_lt v hpos
      have hk1 : 1 ≤ v / h := Nat.one_le_iff_ne_zero.mpr hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · obtain ⟨a, _⟩ := pyr_divmod (k := v / h - 1) hm
        rw [a]
        exact Nat.sub_add_cancel hk1
      · have hm' : v % h + 1 < h := by omega
        have e : h * (v / h - 1) + v % h + 1 = h * (v / h - 1) + (v % h + 1) := by
          rw [Nat.add_assoc]
        obtain ⟨a, _⟩ := pyr_divmod (k := v / h - 1) hm'
        rw [e, a]
        exact Nat.sub_add_cancel hk1
  · intro k hk
    rw [pyr_level_filter hk, pyrLevel_card]

end PyramidGenericShape

end ParPebbleDAG

/-! ## 原稿 `paper-ieice-q2/q2paper.tex` §5 の有界事例（`decide` による全数検査）

    第 84 夜 周 3 に `paper-ieice-q2/lean/Q2Audit.lean` から**文言を変えずに**移した。
    監査ファイルにあると、ライブラリのルート `Revgarbage.lean` から届かない
    （査読 S4 (a)・出口 X-exact-rev-complexity-04）。名前空間 `Q2Paper` はそのままなので
    監査の出力は変わらない。

    Thm 6 の疎条件 `|V| <= 2n0+n1+1` が**上界側で外せない**ことを示す証人。
    ピラミッド `h = 6`（深さ `D = 5`）は疎条件を満たさず（`21 > 18`）、
    実際 `alt` のピークは `n0+n1+1 = 12` ではなく **13** である。 -/
namespace Q2Paper
open ParPebbleDAG

/-- ピラミッド `h=6` の層の大きさ: `n0 = 6`, `n1 = 5`, `|V| = 21`。
    疎条件 `|V| <= 2*n0 + n1 + 1` は `21 <= 18` となり**成り立たない**。 -/
theorem pyr6_not_sparse :
    (VPY6.filter (fun v => depPY6 v = 0)).card = 6 ∧
    (VPY6.filter (fun v => depPY6 v = 1)).card = 5 ∧
    VPY6.card = 21 ∧
    ¬ (VPY6.card ≤ 2 * 6 + 5 + 1) := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- `alt` のピークはピラミッド `h=6` でちょうど 13（時刻 7 で達成）。
    `n0 + n1 + 1 = 12` を**超える**ので、Thm 6 の上界は疎条件なしには成り立たない。 -/
theorem pyr6_alt_peak_exceeds :
    (alt VPY6 depPY6 20 5 7).card = 13 ∧ ¬ ((alt VPY6 depPY6 20 5 7).card ≤ 6 + 5 + 1) := by
  refine ⟨by decide, by decide⟩

/-- 完全二分木 `D=3` の層の大きさは疎条件を満たす（`15 <= 21`）。 -/
theorem tree4_sparse :
    VT4.card = 15 ∧ (VT4.card ≤ 2 * 8 + 4 + 1) := by
  refine ⟨by decide, by decide⟩

/-- ピラミッド `h=5`（`D=4`）は疎条件を**等号で**満たす（`15 <= 15`）。境界の実例。 -/
theorem pyr5_sparse_tight :
    VP5.card = 15 ∧ (VP5.card ≤ 2 * 5 + 4 + 1) ∧ ¬ (VP5.card ≤ 2 * 5 + 4) := by
  refine ⟨by decide, by decide, by decide⟩

end Q2Paper
