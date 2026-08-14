/-
  並列可逆ペブリング（鎖）の構造補題。

  模型は Blocki–Holman–Lee, *The Parallel Reversible Pebbling Game*
  (arXiv:2110.04191v3, TCC 2022) の Definition 1 に従う。同定義の条件

    (2) x ∈ P_i \ P_{i-1} → parents(x) ⊆ P_{i-1}
    (3) x ∈ P_{i-1} \ P_i → parents(x) ⊆ P_{i-1}   （No-Deletion）
    (4) x ∈ parents(P_i △ P_{i-1}) → x ∈ P_i        （Reversibility）

  を合成すると「変化した頂点の親は**前後の両方**に居る」になる。
  鎖 L_n（頂点 0 → 1 → ⋯ → n-1）では頂点 v (v ≥ 1) の親は v-1 ただ一つ。

  ここで示すのは実測から立てた構造補題のうち、規則だけから従うもの:
  * `not_changed_pred` (L3): 同時に変化する頂点は隣接しない
  * `changed_antichain`: 変化集合は「隣接しない」という意味での独立集合
  * `last_removal_decreasing` (L2): 最終除去は頂点の降順に起きる

  実測との対応は `data/q2_structure_lemmas.md`（最適スケジュール 12 本で反例 0）。
-/
import Mathlib.Data.Finset.Basic

namespace ParPebble

/-- 頂点 `v` が配置 `P` と `Q` の間で変化した。 -/
def Changed (P Q : Finset ℕ) (v : ℕ) : Prop :=
  (v ∈ P ∧ v ∉ Q) ∨ (v ∉ P ∧ v ∈ Q)

/-- 鎖上の 1 ステップが合法。変化した頂点 `v ≥ 1` の親 `v-1` は
    `P` と `Q` の**両方**に居なければならない。 -/
def LegalStep (P Q : Finset ℕ) : Prop :=
  ∀ v, 1 ≤ v → Changed P Q v → (v - 1 ∈ P ∧ v - 1 ∈ Q)

/-- 変化していないなら、両方に居るか両方に居ないか。 -/
theorem not_changed_iff {P Q : Finset ℕ} {v : ℕ} :
    ¬ Changed P Q v ↔ (v ∈ P ↔ v ∈ Q) := by
  constructor
  · intro h
    constructor
    · intro hp; by_contra hq; exact h (Or.inl ⟨hp, hq⟩)
    · intro hq; by_contra hp; exact h (Or.inr ⟨hp, hq⟩)
  · rintro h (⟨hp, hq⟩ | ⟨hp, hq⟩)
    · exact hq (h.mp hp)
    · exact hp (h.mpr hq)

/-- **補題 L3**: 合法な 1 ステップでは、隣り合う 2 頂点が同時に変化することはない。

    直観: `v` を動かすには親 `v-1` が前後の両方に居る必要があるが、
    `v-1` が変化するとは前後のどちらかに居ないということ。 -/
theorem not_changed_pred {P Q : Finset ℕ} (h : LegalStep P Q) {v : ℕ}
    (hv : 1 ≤ v) (hc : Changed P Q v) : ¬ Changed P Q (v - 1) := by
  obtain ⟨hp, hq⟩ := h v hv hc
  rintro (⟨_, hn⟩ | ⟨hn, _⟩)
  · exact hn hq
  · exact hn hp

/-- L3 の言い換え: 変化集合は「隣接しない」。 -/
theorem changed_antichain {P Q : Finset ℕ} (h : LegalStep P Q) {u v : ℕ}
    (huv : v = u + 1) (hcu : Changed P Q u) : ¬ Changed P Q v := by
  intro hcv
  have hv : 1 ≤ v := by omega
  have := not_changed_pred h hv hcv
  have hvu : v - 1 = u := by omega
  rw [hvu] at this
  exact this hcu

/-- 合法なペブリング列。`P 0 = ∅` から始まり、各ステップが合法。 -/
structure Pebbling (P : ℕ → Finset ℕ) (T : ℕ) : Prop where
  start : P 0 = ∅
  legal : ∀ t, t < T → LegalStep (P t) (P (t + 1))

/-- 「頂点 `v` は時刻 `t` 以降ずっと不在」＝ `t` までに最終除去されている。 -/
def RemovedFrom (P : ℕ → Finset ℕ) (v t : ℕ) : Prop :=
  ∀ s, t ≤ s → v ∉ P s

/-- **補題 L2 の核**: 頂点 `v (≥1)` を時刻 `t` に除去するには、
    その瞬間に親 `v-1` が居なければならない。
    したがって親が既に最終除去されていたら `v` はもう除去できない。 -/
theorem cannot_remove_if_parent_gone {P : ℕ → Finset ℕ} {T t v : ℕ}
    (hp : Pebbling P T) (ht : t < T) (hv : 1 ≤ v)
    (hgone : RemovedFrom P (v - 1) t) : ¬ Changed (P t) (P (t + 1)) v := by
  intro hc
  obtain ⟨h1, _⟩ := hp.legal t ht v hv hc
  exact hgone t le_rfl h1

/-- 系: 親が最終除去された後は、子は在るなら在り続ける（動かせない）。 -/
theorem child_frozen_after_parent_gone {P : ℕ → Finset ℕ} {T t v : ℕ}
    (hp : Pebbling P T) (ht : t < T) (hv : 1 ≤ v)
    (hgone : RemovedFrom P (v - 1) t) : (v ∈ P t ↔ v ∈ P (t + 1)) :=
  not_changed_iff.mp (cannot_remove_if_parent_gone hp ht hv hgone)

/-! ## 深さの下界（補題 L1 の前半） -/

/-- **補題 L1（前半・深さの下界）**: 空から始まる合法なペブリングでは、
    頂点 `v` は時刻 `v` 以前には決して置かれていない。すなわち `v ∈ P t → v + 1 ≤ t`。

    直観: `v` を置くには前の時刻に `v-1` が要り、`v-1` には `v-2` が要る…と
    鎖をさかのぼるので、`v` に到達するまでに少なくとも `v+1` ステップかかる。

    証明は時刻 `t` についての帰納法だけで済む（各段で「そのままか、動いたか」で場合分け）。 -/
theorem depth_bound {P : ℕ → Finset ℕ} {T : ℕ} (hp : Pebbling P T) :
    ∀ t, t ≤ T → ∀ v, v ∈ P t → v + 1 ≤ t := by
  intro t
  induction t with
  | zero =>
      intro _ v hv
      rw [hp.start] at hv
      simp at hv
  | succ t IH =>
      intro htT v hv
      by_cases hvt : v ∈ P t
      · have := IH (by omega) v hvt; omega
      · -- `v` は t → t+1 で置かれた
        rcases Nat.eq_zero_or_pos v with rfl | hvpos
        · omega
        · have hch : Changed (P t) (P (t + 1)) v := Or.inr ⟨hvt, hv⟩
          have hpar := (hp.legal t (by omega) v hvpos hch).1
          have := IH (by omega) (v - 1) hpar
          omega

/-- 系: sink `n-1` に到達するには少なくとも `n` ステップかかる。 -/
theorem sink_time {P : ℕ → Finset ℕ} {T n t : ℕ} (hp : Pebbling P T)
    (hn : 1 ≤ n) (ht : t ≤ T) (hs : n - 1 ∈ P t) : n ≤ t := by
  have := depth_bound hp t ht (n - 1) hs
  omega

/-! ## 時間の下界（$T \ge 2n-2$ へ向けて） -/

/-- `v` が時刻 `t` に居て時刻 `u` に居ないなら、その間に**除去の瞬間**がある。 -/
theorem exists_removal {P : ℕ → Finset ℕ} {v t u : ℕ}
    (htu : t ≤ u) (hin : v ∈ P t) (hout : v ∉ P u) :
    ∃ r, t < r ∧ r ≤ u ∧ v ∈ P (r - 1) ∧ v ∉ P r := by
  induction u with
  | zero =>
      exfalso; have : t = 0 := Nat.le_zero.mp htu
      exact hout (this ▸ hin)
  | succ u IH =>
      by_cases hu : v ∈ P u
      · -- u で居て u+1 で居ない ⇒ ちょうどそこが除去
        refine ⟨u + 1, ?_, le_rfl, ?_, hout⟩
        · rcases Nat.lt_or_ge t (u + 1) with h | h
          · exact h
          · exact absurd (Nat.le_antisymm htu h ▸ hin) hout
        · simpa using hu
      · -- u で既に居ない ⇒ 帰納法の仮定
        rcases Nat.lt_or_ge u t with h | h
        · exfalso
          have : t = u + 1 := by omega
          exact hout (this ▸ hin)
        · obtain ⟨r, h1, h2, h3, h4⟩ := IH h hu
          exact ⟨r, h1, by omega, h3, h4⟩

/-- `exists_removal` の対: 居なかったものが居るなら、その間に**配置の瞬間**がある。 -/
theorem exists_placement {P : ℕ → Finset ℕ} {v t u : ℕ}
    (htu : t ≤ u) (hout : v ∉ P t) (hin : v ∈ P u) :
    ∃ r, t < r ∧ r ≤ u ∧ v ∉ P (r - 1) ∧ v ∈ P r := by
  induction u with
  | zero =>
      exfalso; have : t = 0 := Nat.le_zero.mp htu
      exact hout (this ▸ hin)
  | succ u IH =>
      by_cases hu : v ∈ P u
      · rcases Nat.lt_or_ge u t with h | h
        · exfalso
          have : t = u + 1 := by omega
          exact hout (this ▸ hin)
        · obtain ⟨r, h1, h2, h3, h4⟩ := IH h hu
          exact ⟨r, h1, by omega, h3, h4⟩
      · refine ⟨u + 1, ?_, le_rfl, by simpa using hu, hin⟩
        rcases Nat.lt_or_ge t (u + 1) with h | h
        · exact h
        · exfalso
          have ht : t = u + 1 := Nat.le_antisymm htu h
          subst ht
          exact hout hin

/-- **階段補題**: 鎖の clean なペブリング（`P T = {n-1}`）では、
    頂点 `v (< n-1)` が時刻 `t` に居るなら、その親 `v-1` は**より遅い時刻**に居る。

    理由: `v` は最終的に消えねばならず（`P T = {n-1}`）、消す瞬間には
    親 `v-1` が前後の両方に居る必要がある（可逆性）。 -/
theorem parent_later {P : ℕ → Finset ℕ} {T n v t : ℕ}
    (hp : Pebbling P T) (hclean : P T = {n - 1})
    (hv : v ∈ P t) (htT : t ≤ T) (hvn : v ≠ n - 1) (hvpos : 1 ≤ v) :
    ∃ u, t < u ∧ u ≤ T ∧ v - 1 ∈ P u := by
  have hout : v ∉ P T := by
    rw [hclean]; simpa using hvn
  obtain ⟨r, hr1, hr2, hr3, hr4⟩ := exists_removal htT hv hout
  have hch : Changed (P (r - 1)) (P r) v := Or.inl ⟨hr3, hr4⟩
  have hrT : r - 1 < T := by omega
  have heq : r - 1 + 1 = r := by omega
  have := hp.legal (r - 1) hrT v hvpos (by rw [heq]; exact hch)
  exact ⟨r, hr1, hr2, by rw [← heq] at this ⊢; exact this.2⟩

/-- 階段を `k` 回下る: 頂点 `v` が時刻 `t` に居るなら、`v - k` は時刻 `t + k` 以降に居る。 -/
theorem descend {P : ℕ → Finset ℕ} {T n : ℕ}
    (hp : Pebbling P T) (hclean : P T = {n - 1}) :
    ∀ k v t, v ∈ P t → t ≤ T → k ≤ v →
      (∀ j, j < k → v - j ≠ n - 1) → ∃ u, t + k ≤ u ∧ u ≤ T ∧ v - k ∈ P u := by
  intro k
  induction k with
  | zero => intro v t hv htT _ _; exact ⟨t, by omega, htT, by simpa using hv⟩
  | succ k IH =>
      intro v t hv htT hkv hne
      have hv1 : 1 ≤ v := by omega
      have hvn : v ≠ n - 1 := hne 0 (by omega)
      obtain ⟨u, hu1, hu2, hu3⟩ := parent_later hp hclean hv htT hvn hv1
      have hsub : v - 1 - k = v - (k + 1) := by omega
      have : ∀ j, j < k → v - 1 - j ≠ n - 1 := by
        intro j hj
        have : v - 1 - j = v - (j + 1) := by omega
        rw [this]; exact hne (j + 1) (by omega)
      obtain ⟨w, hw1, hw2, hw3⟩ := IH (v - 1) u hu3 hu2 (by omega) this
      exact ⟨w, by omega, hw2, by rw [← hsub]; exact hw3⟩

/-- **定理: 鎖の clean な並列可逆ペブリングは少なくとも `2n-1` ステップかかる。**

    実測ではこの下界がちょうど達成される（`data/q2_parallel_findings.md`）。 -/
theorem time_lower_bound {P : ℕ → Finset ℕ} {T n : ℕ}
    (hp : Pebbling P T) (hclean : P T = {n - 1}) (hn : 2 ≤ n) : 2 * n - 1 ≤ T := by
  -- sink は P T に居る
  have hsink : n - 1 ∈ P T := by rw [hclean]; simp
  -- sink は時刻 0 には居ない
  have h0 : n - 1 ∉ P 0 := by rw [hp.start]; simp
  -- sink の配置の瞬間 r を取る
  obtain ⟨r, hr1, hr2, hr3, hr4⟩ := exists_placement (Nat.zero_le T) h0 hsink
  -- 深さの下界より r >= n
  have hrn : n ≤ r := by
    have := depth_bound hp r hr2 (n - 1) hr4
    omega
  -- 配置の瞬間、親 n-2 が居る
  have hpar : n - 1 - 1 ∈ P r := by
    have hch : Changed (P (r - 1)) (P r) (n - 1) := Or.inr ⟨hr3, hr4⟩
    have hrT : r - 1 < T := by omega
    have heq : r - 1 + 1 = r := by omega
    have := hp.legal (r - 1) hrT (n - 1) (by omega) (by rw [heq]; exact hch)
    rw [← heq]; exact this.2
  -- n-2 から n-2 段下って頂点 0 へ
  have hne : ∀ j, j < n - 2 → n - 2 - j ≠ n - 1 := by intro j hj; omega
  have hn2 : n - 1 - 1 = n - 2 := by omega
  rw [hn2] at hpar
  obtain ⟨u, hu1, hu2, hu3⟩ :=
    descend hp hclean (n - 2) (n - 2) r hpar hr2 le_rfl hne
  have hzero : n - 2 - (n - 2) = 0 := by omega
  rw [hzero] at hu3
  -- 頂点 0 も最後には消えている（n >= 2 なので 0 ≠ n-1 … n = 2 のときは 0 = n-2 = 0, n-1 = 1）
  have h0out : (0 : ℕ) ∉ P T := by
    rw [hclean]; simp; omega
  obtain ⟨r', hr'1, hr'2, _, _⟩ := exists_removal hu2 hu3 h0out
  omega

/-! ## 上界（構成）: `2n-1` は達成できる -/

/-- BHL の naive 戦略（§1.2）を明示的に書き下したもの。
    前半 `t ≤ n` は `{0,…,t-1}` を積み上げ、後半は sink を残して上から崩す。 -/
def naive (n t : ℕ) : Finset ℕ :=
  if t ≤ n then Finset.range t else insert (n - 1) (Finset.range (2 * n - 1 - t))

theorem naive_start (n : ℕ) : naive n 0 = ∅ := by
  simp [naive]

theorem naive_final {n : ℕ} (hn : 1 ≤ n) : naive n (2 * n - 1) = {n - 1} := by
  unfold naive
  rcases Nat.eq_or_lt_of_le hn with h | h
  · -- n = 1: 2*1-1 = 1 ≤ 1 なので前半の枝
    subst_vars
    simp
  · have : ¬ (2 * n - 1 ≤ n) := by omega
    rw [if_neg this]
    have : 2 * n - 1 - (2 * n - 1) = 0 := by omega
    rw [this]
    simp

/-- 前半の 1 ステップ: `t` を置く。変化するのは `t` だけ。 -/
theorem naive_step_up {n t : ℕ} (ht : t < n) :
    naive n (t + 1) = insert t (naive n t) := by
  unfold naive
  rw [if_pos (by omega), if_pos (by omega)]
  ext x
  simp only [Finset.mem_range, Finset.mem_insert]
  omega

theorem naive_down {n t : ℕ} (hn : 1 ≤ n) (ht : n ≤ t) :
    naive n t = insert (n - 1) (Finset.range (2 * n - 1 - t)) := by
  unfold naive
  rcases Nat.eq_or_lt_of_le ht with h | h
  · subst h; rw [if_pos le_rfl]; ext x
    simp only [Finset.mem_range, Finset.mem_insert]; omega
  · rw [if_neg (by omega)]

theorem naive_legal {n : ℕ} (hn : 1 ≤ n) : Pebbling (naive n) (2 * n - 1) where
  start := naive_start n
  legal := by
    intro t htT v hv hch
    by_cases hup : t < n
    · -- 前半: t を置く
      have hstep := naive_step_up hup
      have hnt : naive n t = Finset.range t := by unfold naive; rw [if_pos (by omega)]
      have hvt : v = t := by
        rw [hstep] at hch
        rcases hch with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact absurd (Finset.mem_insert_of_mem h1) h2
        · rcases Finset.mem_insert.mp h2 with h | h
          · exact h
          · exact absurd h h1
      subst hvt
      refine ⟨?_, ?_⟩
      · rw [hnt]; exact Finset.mem_range.mpr (by omega)
      · rw [hstep]; exact Finset.mem_insert_of_mem (by rw [hnt]; exact Finset.mem_range.mpr (by omega))
    · -- 後半: 上から崩す
      have hup : n ≤ t := Nat.not_lt.mp hup
      have hA := naive_down hn hup
      have hB := naive_down hn (show n ≤ t + 1 by omega)
      have hveq : v = 2 * n - 1 - (t + 1) := by
        have ha : v ∈ naive n t ∧ v ∉ naive n (t + 1) := by
          rcases hch with h | h
          · exact h
          · exfalso
            rw [hA, hB] at h
            rcases Finset.mem_insert.mp h.2 with hx | hx
            · exact h.1 (hx ▸ Finset.mem_insert_self _ _)
            · exact h.1 (Finset.mem_insert_of_mem (Finset.mem_range.mpr
                (by have := Finset.mem_range.mp hx; omega)))
        obtain ⟨ha1, ha2⟩ := ha
        rw [hA] at ha1; rw [hB] at ha2
        simp only [Finset.mem_insert, Finset.mem_range, not_or, not_lt] at ha1 ha2
        rcases ha1 with h | h
        · exact absurd h ha2.1
        · omega
      subst hveq
      rw [hA, hB]
      exact ⟨Finset.mem_insert_of_mem (Finset.mem_range.mpr (by omega)),
             Finset.mem_insert_of_mem (Finset.mem_range.mpr (by omega))⟩

/-- **主定理: 空間無制約なら `T_par(L_n) = 2n-1`。**

    * 下界は `time_lower_bound`（どんな clean なペブリングも `2n-1` 以上）
    * 上界は `naive`（`2n-1` ちょうどで clean に到達する具体的な構成）

    ⚠ ここでは**ピークに制約を課していない**（`naive` は `n` 個使う）。
    空間 `p` を絞ったときの限界 `n*(p)` は別問題で、
    そちらは DRAT の証明書つき（`data/q2_parallel_findings.md`）。 -/
theorem par_time_exact {n : ℕ} (hn : 1 ≤ n) :
    (Pebbling (naive n) (2 * n - 1) ∧ naive n (2 * n - 1) = {n - 1}) ∧
    (∀ (P : ℕ → Finset ℕ) (T : ℕ), Pebbling P T → P T = {n - 1} → 2 ≤ n → 2 * n - 1 ≤ T) :=
  ⟨⟨naive_legal hn, naive_final hn⟩, fun P T hp hc hn2 => time_lower_bound hp hc hn2⟩

end ParPebble
