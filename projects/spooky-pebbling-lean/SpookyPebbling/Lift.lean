/-
# 持ち上げ — 部分鎖の手順を元の鎖へ戻す（$\le$ 方向の土台）

`Project.lean` は「大きい鎖の手順 → 部分鎖の手順」（射影）だった。$\le$ 方向では逆に
**部分鎖で作った手順を大きい鎖へ持ち上げる**。

- **尻尾**（頂点 `k..n-1`）: 添字を `+k` して戻す。持ち上げた手が妥当であるためには
  **頭の `v_{k-1}` にペブルが在り続ける**ことが要る（孤立鎖では前提の無かった `v_k` の
  手が、元の鎖では `v_{k-1} ∈ P` を要求するため）
- **頭**（頂点 `0..k-1`）: 添字はそのまま。`k ≤ n` なら範囲の検査が緩むだけなので
  そのまま妥当（`valid_mono`）

あわせて、手順の連結（`valid_append` / `traj_append_mem`）と、
`< k` で一致する配置から始めた軌跡どうしが `< k` で一致すること（`traj_agree`）を用意する。
-/
import SpookyPebbling.Decomp

namespace Spooky

/-! ## 連結 -/

theorem valid_append {n : ℕ} : ∀ (l₁ l₂ : List Move) (c : Config),
    valid n c l₁ = true → valid n (exec c l₁) l₂ = true → valid n c (l₁ ++ l₂) = true := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ c _ h; exact h
  | cons a as ih =>
      intro l₂ c h1 h2
      rw [List.cons_append]
      simp only [valid_cons, Bool.and_eq_true] at h1 ⊢
      exact ⟨h1.1, ih l₂ (step c a) h1.2 h2⟩

theorem exec_mem_traj : ∀ (ms : List Move) (c : Config), exec c ms ∈ traj c ms := by
  intro ms
  induction ms with
  | nil => intro c; simp only [traj_nil, List.mem_singleton]; rfl
  | cons m ms ih => intro c; simp only [traj_cons, List.mem_cons]; exact Or.inr (ih (step c m))

theorem traj_append_mem : ∀ (l₁ : List Move) (c : Config) (l₂ : List Move),
    ∀ d ∈ traj c (l₁ ++ l₂), d ∈ traj c l₁ ∨ d ∈ traj (exec c l₁) l₂ := by
  intro l₁
  induction l₁ with
  | nil => intro c l₂ d h; exact Or.inr h
  | cons a as ih =>
      intro c l₂ d h
      simp only [List.cons_append, traj_cons, List.mem_cons] at h
      rcases h with rfl | h
      · exact Or.inl (by simp)
      · rcases ih (step c a) l₂ d h with h' | h'
        · exact Or.inl (by simp only [traj_cons, List.mem_cons]; exact Or.inr h')
        · exact Or.inr h'

/-! ## `< k` での一致は軌跡に伝わる -/

theorem traj_agree {k : ℕ} : ∀ (ms : List Move) (c d : Config), AgreeOn k c d →
    ∀ e ∈ traj c ms, ∃ e' ∈ traj d ms, AgreeOn k e e' := by
  intro ms
  induction ms with
  | nil =>
      intro c d h e he
      simp only [traj_nil, List.mem_singleton] at he
      subst he
      exact ⟨d, by simp, h⟩
  | cons m ms ih =>
      intro c d h e he
      simp only [traj_cons, List.mem_cons] at he
      rcases he with rfl | he
      · exact ⟨d, by simp, h⟩
      · obtain ⟨e', he', hagree⟩ := ih (step c m) (step d m) (step_congr h m) e he
        exact ⟨e', by simp only [traj_cons, List.mem_cons]; exact Or.inr he', hagree⟩

/-! ## 頭: 短い鎖の手順はそのまま長い鎖でも妥当 -/

theorem legal_mono {n k : ℕ} (hkn : k ≤ n) {c : Config} {m : Move} (h : legal k c m = true) :
    legal n c m = true := by
  unfold legal at h ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  exact ⟨by omega, h.2⟩

theorem valid_mono {n k : ℕ} (hkn : k ≤ n) : ∀ (ms : List Move) (c : Config),
    valid k c ms = true → valid n c ms = true := by
  intro ms
  induction ms with
  | nil => intro _ _; rfl
  | cons m ms ih =>
      intro c h
      simp only [valid_cons, Bool.and_eq_true] at h ⊢
      exact ⟨legal_mono hkn h.1, ih (step c m) h.2⟩

theorem valid_lt {k : ℕ} : ∀ (ms : List Move) (c : Config), valid k c ms = true →
    ∀ m ∈ ms, m.v < k := by
  intro ms
  induction ms with
  | nil => intro _ _ m hm; simp at hm
  | cons a as ih =>
      intro c h m hm
      simp only [valid_cons, Bool.and_eq_true] at h
      simp only [List.mem_cons] at hm
      rcases hm with rfl | hm
      · exact legal_lt h.1
      · exact ih (step c a) h.2 m hm

/-- 頭だけに作用する手順は `≥ k` の配置を変えない。 -/
theorem traj_above {k : ℕ} : ∀ (ms : List Move) (c : Config), (∀ m ∈ ms, m.v < k) →
    ∀ d ∈ traj c ms, ∀ j, k ≤ j → d j = c j := by
  intro ms
  induction ms with
  | nil =>
      intro c _ d hd j _
      simp only [traj_nil, List.mem_singleton] at hd
      subst hd; rfl
  | cons m ms ih =>
      intro c hlt d hd j hj
      simp only [traj_cons, List.mem_cons] at hd
      rcases hd with rfl | hd
      · rfl
      · have hmv : m.v < k := hlt m (by simp)
        rw [ih (step c m) (fun m' hm' => hlt m' (by simp [hm'])) d hd j hj]
        exact Function.update_of_ne (by omega) _ _

/-! ## 尻尾: 部分鎖の手順を `+k` して持ち上げる -/

def liftM (k : ℕ) (m : Move) : Move := ⟨m.op, m.v + k⟩

def liftT (k : ℕ) (ms : List Move) : List Move := ms.map (liftM k)

@[simp] theorem liftM_op (k : ℕ) (m : Move) : (liftM k m).op = m.op := rfl
@[simp] theorem liftM_v (k : ℕ) (m : Move) : (liftM k m).v = m.v + k := rfl

@[simp] theorem liftT_nil (k : ℕ) : liftT k [] = [] := rfl

@[simp] theorem liftT_cons (k : ℕ) (m : Move) (ms : List Move) :
    liftT k (m :: ms) = liftM k m :: liftT k ms := rfl

@[simp] theorem liftT_length (k : ℕ) (ms : List Move) : (liftT k ms).length = ms.length := by
  simp [liftT]

/-- 持ち上げた手は頭の配置を変えない。 -/
theorem step_lift_below {k : ℕ} (c : Config) (m : Move) {j : ℕ} (hj : j < k) :
    step c (liftM k m) j = c j :=
  Function.update_of_ne (by simp only [liftM_v]; omega) _ _

/-- 持ち上げは `step` と可換（尻尾側で見れば同じ手）。 -/
theorem shiftC_step_lift (k : ℕ) (c : Config) (m : Move) :
    shiftC k (step c (liftM k m)) = step (shiftC k c) m := by
  funext v
  show Function.update c (m.v + k) (result m.op) (v + k)
     = Function.update (shiftC k c) m.v (result m.op) v
  by_cases hv : v = m.v
  · subst hv; simp
  · rw [Function.update_of_ne (by omega), Function.update_of_ne hv, shiftC_apply]

theorem ready_lift {k : ℕ} (hk : 0 < k) {c : Config} {v : ℕ}
    (hped : c (k - 1) = Cell.pebble) (h : ready (shiftC k c) v = true) :
    ready c (v + k) = true := by
  unfold ready at h ⊢
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h ⊢
  refine Or.inr ?_
  by_cases hv : v = 0
  · subst hv
    have : 0 + k - 1 = k - 1 := by omega
    rw [this]; exact hped
  · rcases h with h | h
    · exact absurd h hv
    · rw [shiftC_apply] at h
      have : v + k - 1 = v - 1 + k := by omega
      rw [this]; exact h

theorem legal_lift {n k : ℕ} (hk : 0 < k) {c : Config} {m : Move}
    (hped : c (k - 1) = Cell.pebble) (h : legal (n - k) (shiftC k c) m = true) :
    legal n c (liftM k m) = true := by
  unfold legal at h ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq, liftM_v, liftM_op] at h ⊢
  obtain ⟨hlt, hrest⟩ := h
  refine ⟨by omega, ?_⟩
  have hcell : c (m.v + k) = shiftC k c m.v := rfl
  cases hop : m.op with
  | pebble =>
      rw [hop] at hrest
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hrest ⊢
      exact ⟨by rw [hcell]; exact hrest.1, ready_lift hk hped hrest.2⟩
  | unpebble =>
      rw [hop] at hrest
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hrest ⊢
      exact ⟨by rw [hcell]; exact hrest.1, ready_lift hk hped hrest.2⟩
  | ghost =>
      rw [hop] at hrest
      simp only [decide_eq_true_eq] at hrest ⊢
      rw [hcell]; exact hrest
  | unghost =>
      rw [hop] at hrest
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hrest ⊢
      exact ⟨by rw [hcell]; exact hrest.1, ready_lift hk hped hrest.2⟩

/-- **持ち上げた尻尾の手順は妥当**（頭の `v_{k-1}` にペブルが在り続けるので）。 -/
theorem valid_liftT {n k : ℕ} (hk : 0 < k) : ∀ (ms : List Move) (c : Config),
    c (k - 1) = Cell.pebble → valid (n - k) (shiftC k c) ms = true →
    valid n c (liftT k ms) = true := by
  intro ms
  induction ms with
  | nil => intro _ _ _; rfl
  | cons m ms ih =>
      intro c hped h
      simp only [liftT_cons, valid_cons, Bool.and_eq_true] at h ⊢
      refine ⟨legal_lift hk hped h.1, ?_⟩
      refine ih (step c (liftM k m)) ?_ ?_
      · rw [step_lift_below c m (by omega)]; exact hped
      · rw [shiftC_step_lift]; exact h.2

/-- 持ち上げた手順の軌跡: 頭は不変、尻尾は部分鎖の軌跡そのもの。 -/
theorem traj_liftT {k : ℕ} : ∀ (ms : List Move) (c : Config), ∀ d ∈ traj c (liftT k ms),
    (∀ j, j < k → d j = c j) ∧ shiftC k d ∈ traj (shiftC k c) ms := by
  intro ms
  induction ms with
  | nil =>
      intro c d hd
      simp only [liftT_nil, traj_nil, List.mem_singleton] at hd
      subst hd
      exact ⟨fun _ _ => rfl, by simp⟩
  | cons m ms ih =>
      intro c d hd
      simp only [liftT_cons, traj_cons, List.mem_cons] at hd
      rcases hd with rfl | hd
      · exact ⟨fun _ _ => rfl, by simp⟩
      · obtain ⟨hbelow, hin⟩ := ih (step c (liftM k m)) d hd
        refine ⟨fun j hj => by rw [hbelow j hj]; exact step_lift_below c m hj, ?_⟩
        rw [shiftC_step_lift] at hin
        simp only [traj_cons, List.mem_cons]
        exact Or.inr hin

theorem exec_liftT_shift (k : ℕ) : ∀ (ms : List Move) (c : Config),
    shiftC k (exec c (liftT k ms)) = exec (shiftC k c) ms := by
  intro ms
  induction ms with
  | nil => intro c; rfl
  | cons m ms ih =>
      intro c
      show shiftC k (exec (step c (liftM k m)) (liftT k ms)) = exec (step (shiftC k c) m) ms
      rw [ih (step c (liftM k m)), shiftC_step_lift]

theorem exec_liftT_below {k : ℕ} : ∀ (ms : List Move) (c : Config) {j : ℕ}, j < k →
    exec c (liftT k ms) j = c j := by
  intro ms
  induction ms with
  | nil => intro c j _; rfl
  | cons m ms ih =>
      intro c j hj
      show exec (step c (liftM k m)) (liftT k ms) j = c j
      rw [ih (step c (liftM k m)) hj, step_lift_below c m hj]

/-! ## `pcount` の刻み -/

theorem pcount_succ (m : ℕ) (c : Config) :
    pcount (m + 1) c = pcount m c + (if c m = Cell.pebble then 1 else 0) := by
  unfold pcount
  rw [Finset.range_add_one, Finset.filter_insert]
  by_cases h : c m = Cell.pebble
  · rw [if_pos h, Finset.card_insert_of_notMem (by simp), if_pos h]
  · rw [if_neg h, if_neg h, Nat.add_zero]

end Spooky
