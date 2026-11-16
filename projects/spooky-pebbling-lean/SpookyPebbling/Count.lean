/-
# 数え上げ（段(i)）— 頭の手は `2k-1` 手以上

分解の $\ge$ 方向の段(i)。ある時刻 `t₁` で頂点 `u` にペブルが在り、`0..u-1` には無い
とする（`u` はその時刻の最下位ペブル）。始状態では `0..u` のどれにもペブルが無い。
このとき `t₁` までの手は **`2u+1` 手以上**ある（`k = u+1` と置けば `2k-1`）。

*内訳*: 各 `i ≤ u` は少なくとも 1 回**置かれ**（`u` を置くには `u-1` が要り、下向きに
`0` まで下りる）、各 `i < u` は少なくとも 1 回**外される**（時刻 `t₁` で空だから）。
置く手と外す手は操作で排他、頂点も互いに素なので、合計 `(u+1) + u = 2u+1`。

「置く」= `pebble` または `unghost`、「外す」= `unpebble` または `ghost`。
どちらも「作用した頂点の $\varphi$ を反転させる」の両向きにあたる（`Parity.lean`）。
-/
import SpookyPebbling.Project

namespace Spooky

/-! ## 手順の分割に関する基本 -/

theorem exec_append (l₁ l₂ : List Move) (c : Config) :
    exec c (l₁ ++ l₂) = exec (exec c l₁) l₂ := by
  induction l₁ generalizing c with
  | nil => rfl
  | cons a as ih => simpa [exec] using ih (step c a)

theorem valid_append_left {n : ℕ} : ∀ (l₁ l₂ : List Move) (c : Config),
    valid n c (l₁ ++ l₂) = true → valid n c l₁ = true := by
  intro l₁
  induction l₁ with
  | nil => intro _ _ _; rfl
  | cons a as ih =>
      intro l₂ c h
      simp only [List.cons_append, valid_cons, Bool.and_eq_true] at h ⊢
      exact ⟨h.1, ih l₂ (step c a) h.2⟩

/-! ## 置く手・外す手 -/

def isPlace (i : ℕ) (m : Move) : Bool :=
  decide (m.v = i) && (decide (m.op = Op.pebble) || decide (m.op = Op.unghost))

def isRemove (i : ℕ) (m : Move) : Bool :=
  decide (m.v = i) && (decide (m.op = Op.unpebble) || decide (m.op = Op.ghost))

theorem isPlace_v {i : ℕ} {m : Move} (h : isPlace i m = true) : m.v = i := by
  unfold isPlace at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem isRemove_v {i : ℕ} {m : Move} (h : isRemove i m = true) : m.v = i := by
  unfold isRemove at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem isPlace_op {i : ℕ} {m : Move} (h : isPlace i m = true) :
    m.op = Op.pebble ∨ m.op = Op.unghost := by
  unfold isPlace at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  exact h.2

theorem isRemove_op {i : ℕ} {m : Move} (h : isRemove i m = true) :
    m.op = Op.unpebble ∨ m.op = Op.ghost := by
  unfold isRemove at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  exact h.2

/-- 置く手と外す手は**操作で**排他（頂点は関係ない）。 -/
theorem isPlace_isRemove {i j : ℕ} {m : Move} (h : isPlace i m = true) : isRemove j m = false := by
  unfold isRemove
  rcases isPlace_op h with hop | hop <;> simp [hop]

theorem isRemove_isPlace {i j : ℕ} {m : Move} (h : isRemove i m = true) : isPlace j m = false := by
  unfold isPlace
  rcases isRemove_op h with hop | hop <;> simp [hop]

/-! ## 状態が変わるなら、その頂点への手が打たれている -/

theorem step_ne_of_ne {c : Config} {m : Move} {i : ℕ} (h : m.v ≠ i) : step c m i = c i :=
  Function.update_of_ne (Ne.symm h) _ _

theorem step_self (c : Config) (m : Move) : step c m m.v = result m.op :=
  Function.update_self _ _ _

/-- 空/ゴースト → ペブル の遷移は「置く手」。 -/
theorem isPlace_of_becomes {c : Config} {m : Move} {i : ℕ}
    (h0 : c i ≠ Cell.pebble) (h1 : step c m i = Cell.pebble) : isPlace i m = true := by
  by_cases hv : m.v = i
  · subst hv
    have hres : result m.op = Cell.pebble := by rw [← step_self c m]; exact h1
    have hop : m.op = Op.pebble ∨ m.op = Op.unghost := by
      cases hcase : m.op
      · exact Or.inl rfl
      · rw [hcase] at hres; simp [result] at hres
      · rw [hcase] at hres; simp [result] at hres
      · exact Or.inr rfl
    unfold isPlace
    rcases hop with hop | hop <;> simp [hop]
  · rw [step_ne_of_ne hv] at h1; exact absurd h1 h0

/-- ペブル → 空/ゴースト の遷移は「外す手」。 -/
theorem isRemove_of_leaves {c : Config} {m : Move} {i : ℕ}
    (h0 : c i = Cell.pebble) (h1 : step c m i ≠ Cell.pebble) : isRemove i m = true := by
  by_cases hv : m.v = i
  · subst hv
    have hres : result m.op ≠ Cell.pebble := by rw [step_self c m] at h1; exact h1
    have hop : m.op = Op.unpebble ∨ m.op = Op.ghost := by
      cases hcase : m.op
      · rw [hcase] at hres; simp [result] at hres
      · exact Or.inl rfl
      · exact Or.inr rfl
      · rw [hcase] at hres; simp [result] at hres
    unfold isRemove
    rcases hop with hop | hop <;> simp [hop]
  · rw [step_ne_of_ne hv] at h1; exact absurd h0 h1

/-! ## 「置かれた」「外された」の存在 -/

theorem exists_place {i : ℕ} : ∀ (ms : List Move) (c : Config), c i ≠ Cell.pebble →
    exec c ms i = Cell.pebble → 0 < ms.countP (isPlace i) := by
  intro ms
  induction ms with
  | nil => intro c h0 h1; exact absurd h1 h0
  | cons m ms ih =>
      intro c h0 h1
      rw [List.countP_cons]
      by_cases hstep : step c m i = Cell.pebble
      · have hp := isPlace_of_becomes h0 hstep
        simp [hp]
      · have := ih (step c m) hstep h1
        omega

theorem exists_remove {i : ℕ} : ∀ (ms : List Move) (c : Config), c i = Cell.pebble →
    exec c ms i ≠ Cell.pebble → 0 < ms.countP (isRemove i) := by
  intro ms
  induction ms with
  | nil => intro c h0 h1; exact absurd h0 h1
  | cons m ms ih =>
      intro c h0 h1
      rw [List.countP_cons]
      by_cases hstep : step c m i = Cell.pebble
      · have := ih (step c m) hstep h1
        omega
      · have hr := isRemove_of_leaves h0 hstep
        simp [hr]

/-! ## 置く手には直前の頂点のペブルが要る（下向きの連鎖） -/

/-- `i` を置く手が在れば、その手の直前までの手順で `i-1` にペブルが在る。 -/
theorem pred_pebbled {n : ℕ} : ∀ (ms : List Move) (c : Config), valid n c ms = true →
    ∀ {i : ℕ}, 0 < i → 0 < ms.countP (isPlace i) →
    ∃ l₁ l₂, ms = l₁ ++ l₂ ∧ exec c l₁ (i - 1) = Cell.pebble := by
  intro ms
  induction ms with
  | nil => intro c _ i _ h; simp at h
  | cons m ms ih =>
      intro c hv i hi h
      simp only [valid_cons, Bool.and_eq_true] at hv
      by_cases hm : isPlace i m = true
      · refine ⟨[], m :: ms, rfl, ?_⟩
        have hleg := hv.1
        unfold legal at hleg
        simp only [Bool.and_eq_true] at hleg
        have h2 := hleg.2
        have hr : ready c m.v = true := by
          rcases isPlace_op hm with hop | hop <;> rw [hop] at h2 <;> exact Bool.and_elim_right h2
        rw [isPlace_v hm] at hr
        unfold ready at hr
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hr
        rcases hr with hr | hr
        · omega
        · exact hr
      · have hcount : 0 < ms.countP (isPlace i) := by
          rw [List.countP_cons] at h
          simp only [hm, Bool.false_eq_true, if_false, Nat.add_zero] at h
          exact h
        obtain ⟨l₁, l₂, heq, hp⟩ := ih (step c m) hv.2 hi hcount
        exact ⟨m :: l₁, l₂, by rw [List.cons_append, ← heq], hp⟩

/-- **下向きの連鎖**: `u` にペブルが届いたなら、`j ≤ u` のどれにも「ペブルが在る時刻」が在る。 -/
theorem reaches_below {n : ℕ} : ∀ (i : ℕ) (ms : List Move) (c : Config), valid n c ms = true →
    (∀ j, j ≤ i → c j ≠ Cell.pebble) → exec c ms i = Cell.pebble →
    ∀ j, j ≤ i → ∃ l₁ l₂, ms = l₁ ++ l₂ ∧ exec c l₁ j = Cell.pebble := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
      intro ms c hv hc hi j hj
      rcases Nat.eq_or_lt_of_le hj with rfl | hlt
      · exact ⟨ms, [], by simp, hi⟩
      · have hi0 : 0 < i := by omega
        have hplace : 0 < ms.countP (isPlace i) := exists_place ms c (hc i le_rfl) hi
        obtain ⟨l₁, l₂, heq, hp⟩ := pred_pebbled ms c hv hi0 hplace
        have hv₁ : valid n c l₁ = true := valid_append_left l₁ l₂ c (heq ▸ hv)
        obtain ⟨r₁, r₂, hr, hrp⟩ :=
          ih (i - 1) (by omega) l₁ c hv₁ (fun j hj => hc j (by omega)) hp j (by omega)
        exact ⟨r₁, r₂ ++ l₂, by rw [heq, hr, List.append_assoc], hrp⟩

/-! ## 合計が `2u+1` 以上 -/

/-- 互いに素な述語族の `countP` の総和は長さを超えない。 -/
theorem sum_countP_le_length (p : ℕ → Move → Bool)
    (hd : ∀ (m : Move) (i j : ℕ), i ≠ j → p i m = true → p j m = false) :
    ∀ (l : List Move) (k : ℕ), ∑ i ∈ Finset.range k, l.countP (p i) ≤ l.length := by
  intro l
  induction l with
  | nil => intro k; simp
  | cons a l ih =>
      intro k
      have hstep : ∑ i ∈ Finset.range k, (a :: l).countP (p i)
          = (∑ i ∈ Finset.range k, l.countP (p i))
            + ∑ i ∈ Finset.range k, (if p i a = true then 1 else 0) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [List.countP_cons]
      have hone : ∑ i ∈ Finset.range k, (if p i a = true then 1 else 0) ≤ 1 := by
        rw [← Finset.card_filter]
        refine Finset.card_le_one.mpr fun x hx y hy => ?_
        simp only [Finset.mem_filter] at hx hy
        by_contra hne
        exact absurd hy.2 (by rw [hd a x y hne hx.2]; simp)
      have := ih k
      simp only [List.length_cons]
      omega

/-- 段(i) 用の述語: `j ≤ u` は「`j` を置く」、`u < j` は「`j-(u+1)` を外す」。 -/
def headTag (u : ℕ) (j : ℕ) (m : Move) : Bool :=
  if j ≤ u then isPlace j m else isRemove (j - (u + 1)) m

theorem headTag_le {u j : ℕ} (h : j ≤ u) : headTag u j = isPlace j := by
  funext m; unfold headTag; rw [if_pos h]

theorem headTag_gt {u j : ℕ} (h : ¬ j ≤ u) : headTag u j = isRemove (j - (u + 1)) := by
  funext m; unfold headTag; rw [if_neg h]

theorem headTag_disjoint (u : ℕ) :
    ∀ (m : Move) (i j : ℕ), i ≠ j → headTag u i m = true → headTag u j m = false := by
  intro m i j hne h
  by_cases hi : i ≤ u
  · rw [headTag_le hi] at h
    by_cases hj : j ≤ u
    · -- どちらも「置く」: 頂点が違う
      rw [headTag_le hj]
      unfold isPlace
      have hv : m.v = i := isPlace_v h
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
      exact Or.inl (by rw [hv]; exact hne)
    · -- 「置く」と「外す」: 操作で排他
      rw [headTag_gt hj]
      exact isPlace_isRemove h
  · rw [headTag_gt hi] at h
    by_cases hj : j ≤ u
    · rw [headTag_le hj]
      exact isRemove_isPlace h
    · -- どちらも「外す」: 頂点が違う
      rw [headTag_gt hj]
      unfold isRemove
      have hv : m.v = i - (u + 1) := isRemove_v h
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
      refine Or.inl ?_
      rw [hv]
      omega

/-- **段(i)**: 頂点 `u` にペブルが届き、`0..u-1` が空で終わるなら、手数は `2u+1` 以上。 -/
theorem length_ge_two_mul_add_one {n u : ℕ} (ms : List Move) (c : Config)
    (hv : valid n c ms = true)
    (hc : ∀ j, j ≤ u → c j ≠ Cell.pebble)
    (hu : exec c ms u = Cell.pebble)
    (hlow : ∀ j, j < u → exec c ms j ≠ Cell.pebble) :
    2 * u + 1 ≤ ms.length := by
  have hone : ∀ j, j < 2 * u + 1 → 1 ≤ ms.countP (headTag u j) := by
    intro j hj
    by_cases hju : j ≤ u
    · rw [headTag_le hju]
      obtain ⟨l₁, l₂, heq, hp⟩ := reaches_below u ms c hv hc hu j hju
      have h1 : 0 < l₁.countP (isPlace j) := exists_place l₁ c (hc j hju) hp
      have hsub : l₁.countP (isPlace j) ≤ ms.countP (isPlace j) := by
        rw [heq, List.countP_append]; omega
      omega
    · rw [headTag_gt hju]
      have hiu : j - (u + 1) < u := by omega
      obtain ⟨l₁, l₂, heq, hp⟩ := reaches_below u ms c hv hc hu (j - (u + 1)) (by omega)
      have hne : exec (exec c l₁) l₂ (j - (u + 1)) ≠ Cell.pebble := by
        rw [← exec_append l₁ l₂ c, ← heq]
        exact hlow _ hiu
      have h1 : 0 < l₂.countP (isRemove (j - (u + 1))) := exists_remove l₂ (exec c l₁) hp hne
      have hsub : l₂.countP (isRemove (j - (u + 1))) ≤ ms.countP (isRemove (j - (u + 1))) := by
        rw [heq, List.countP_append]; omega
      omega
  have hsum : 2 * u + 1 ≤ ∑ j ∈ Finset.range (2 * u + 1), ms.countP (headTag u j) := by
    calc 2 * u + 1 = ∑ _j ∈ Finset.range (2 * u + 1), 1 := by simp
      _ ≤ _ := Finset.sum_le_sum fun j hj => hone j (Finset.mem_range.mp hj)
  exact le_trans hsum (sum_countP_le_length _ (headTag_disjoint u) ms _)

end Spooky
