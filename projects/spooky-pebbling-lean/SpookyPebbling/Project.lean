/-
# 射影 — 手順を頭 `0..u` と尻尾 `u+1..n-1` に分ける

分解の $\ge$ 方向は、1 本の妥当な手順 `ms` を頂点で 2 つに切り、それぞれが**部分鎖の
妥当な手順になっている**ことを使う。本ファイルはその土台だけを用意する
（$k$ の選び方と数え上げは `Decomp.lean`）。

- **頭** = 頂点 `0..u` に作用する手。鎖の先頭を含むので**添字のずらしが要らない**
- **尻尾** = 頂点 `u+1..n-1` に作用する手。`u+1` だけずらす

尻尾が妥当になる要は、**孤立した鎖では先頭に前提条件が無い**こと。元の鎖では
`pebble v_{u+1}` に `v_u ∈ P` が要るが、長さ `n-(u+1)` の鎖では `v_{u+1}` が始点なので
前提が消える（a fortiori 妥当）。

上限（ペブル数）はここでは扱わず、`valid`（妥当性のみ）と `traj`（各時刻の配置）に
分けておく。上限は $k$ の選び方から出るので `Decomp.lean` で合流させる。
-/
import SpookyPebbling.Defs

namespace Spooky

/-! ## 軌跡と、妥当性・上限の分離 -/

/-- 各時刻の配置（長さ `ms.length + 1`）。 -/
def traj (c : Config) : List Move → List Config
  | [] => [c]
  | m :: ms => c :: traj (step c m) ms

@[simp] theorem traj_nil (c : Config) : traj c [] = [c] := rfl

@[simp] theorem traj_cons (c : Config) (m : Move) (ms : List Move) :
    traj c (m :: ms) = c :: traj (step c m) ms := rfl

theorem traj_length (c : Config) (ms : List Move) : (traj c ms).length = ms.length + 1 := by
  induction ms generalizing c with
  | nil => simp
  | cons m ms ih => simp [ih]

theorem mem_traj_self (c : Config) (ms : List Move) : c ∈ traj c ms := by
  cases ms <;> simp

/-- 妥当性のみ（ペブル上限を課さない）。 -/
def valid (n : ℕ) (c : Config) : List Move → Bool
  | [] => true
  | m :: ms => legal n c m && valid n (step c m) ms

@[simp] theorem valid_nil (n : ℕ) (c : Config) : valid n c [] = true := rfl

@[simp] theorem valid_cons (n : ℕ) (c : Config) (m : Move) (ms : List Move) :
    valid n c (m :: ms) = (legal n c m && valid n (step c m) ms) := rfl

theorem valid_congr {n : ℕ} {c d : Config} (h : AgreeOn n c d) : ∀ (ms : List Move),
    valid n c ms = true → valid n d ms = true := by
  intro ms
  induction ms generalizing c d with
  | nil => intro _; rfl
  | cons m ms ih =>
      intro hv
      simp only [valid_cons, Bool.and_eq_true] at hv ⊢
      exact ⟨by rw [← legal_congr h m]; exact hv.1, ih (step_congr h m) hv.2⟩

/-- `ok` は「妥当性」と「全時刻の上限」に分かれる。 -/
theorem ok_iff {n s : ℕ} : ∀ (ms : List Move) (c : Config),
    (ok n s c ms = true) ↔ (valid n c ms = true ∧ ∀ d ∈ traj c ms, pcount n d ≤ s) := by
  intro ms
  induction ms with
  | nil =>
      intro c
      constructor
      · intro h
        refine ⟨rfl, ?_⟩
        intro d hd
        simp only [traj_nil, List.mem_singleton] at hd
        subst hd
        unfold ok at h
        exact of_decide_eq_true h
      · intro ⟨_, h⟩
        unfold ok
        exact decide_eq_true (h c (by simp))
  | cons m ms ih =>
      intro c
      constructor
      · intro h
        unfold ok at h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨hcap, hleg⟩, htail⟩ := h
        obtain ⟨hv, hall⟩ := (ih (step c m)).mp htail
        refine ⟨by simp [hleg, hv], ?_⟩
        intro d hd
        simp only [traj_cons, List.mem_cons] at hd
        rcases hd with rfl | hd
        · exact hcap
        · exact hall d hd
      · intro ⟨hv, hall⟩
        simp only [valid_cons, Bool.and_eq_true] at hv
        unfold ok
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        refine ⟨⟨hall c (by simp), hv.1⟩, (ih (step c m)).mpr ⟨hv.2, ?_⟩⟩
        intro d hd
        exact hall d (by simp [hd])

/-! ## `pcount` の単調性 -/

theorem pcount_mono {m n : ℕ} (h : m ≤ n) (c : Config) : pcount m c ≤ pcount n c := by
  unfold pcount
  apply Finset.card_le_card
  intro v hv
  simp only [Finset.mem_filter, Finset.mem_range] at hv ⊢
  exact ⟨by omega, hv.2⟩

/-! ## 添字のずらし -/

/-- 配置の添字を `j` だけずらす（尻尾の部分鎖を見る）。 -/
def shiftC (j : ℕ) (c : Config) : Config := fun v => c (v + j)

/-- 手の添字を `j` だけずらす。 -/
def shiftM (j : ℕ) (m : Move) : Move := ⟨m.op, m.v - j⟩

@[simp] theorem shiftM_op (j : ℕ) (m : Move) : (shiftM j m).op = m.op := rfl
@[simp] theorem shiftM_v (j : ℕ) (m : Move) : (shiftM j m).v = m.v - j := rfl

theorem shiftC_apply (j : ℕ) (c : Config) (v : ℕ) : shiftC j c v = c (v + j) := rfl

/-- ずらしても、対応する頂点の状態は同じ。 -/
theorem shiftC_at {u : ℕ} (c : Config) {v : ℕ} (hv : u < v) :
    shiftC (u + 1) c (v - (u + 1)) = c v := by
  unfold shiftC
  congr 1
  omega

/-- 前提条件はずらしても保たれる（孤立鎖の始点では前提が消えるので a fortiori）。 -/
theorem ready_shift {u : ℕ} {c : Config} {v : ℕ} (hv : u < v) (h : ready c v = true) :
    ready (shiftC (u + 1) c) (v - (u + 1)) = true := by
  unfold ready at h ⊢
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h ⊢
  by_cases h0 : v - (u + 1) = 0
  · exact Or.inl h0
  · right
    have he : v - (u + 1) - 1 + (u + 1) = v - 1 := by omega
    rw [shiftC_apply, he]
    rcases h with h | h
    · exact absurd h (by omega)
    · exact h

/-! ## 1 手の射影 -/

/-- 頭に落ちる手は、長さ `u+1` の鎖でも妥当（添字はそのまま）。 -/
theorem legal_head {n u : ℕ} {c : Config} {m : Move} (h : legal n c m = true) (hm : m.v ≤ u) :
    legal (u + 1) c m = true := by
  unfold legal at h ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  exact ⟨by omega, h.2⟩

/-- 尻尾に落ちる手は、長さ `n-(u+1)` の鎖でも妥当（添字を `u+1` ずらす）。 -/
theorem legal_tail {n u : ℕ} {c : Config} {m : Move} (h : legal n c m = true) (hm : u < m.v) :
    legal (n - (u + 1)) (shiftC (u + 1) c) (shiftM (u + 1) m) = true := by
  unfold legal at h ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq, shiftM_v, shiftM_op] at h ⊢
  obtain ⟨hlt, hrest⟩ := h
  refine ⟨by omega, ?_⟩
  have hcell : shiftC (u + 1) c (m.v - (u + 1)) = c m.v := shiftC_at c hm
  cases hop : m.op with
  | pebble =>
      rw [hop] at hrest
      simp only [Bool.and_eq_true, decide_eq_true_eq, hcell] at hrest ⊢
      exact ⟨hrest.1, ready_shift hm hrest.2⟩
  | unpebble =>
      rw [hop] at hrest
      simp only [Bool.and_eq_true, decide_eq_true_eq, hcell] at hrest ⊢
      exact ⟨hrest.1, ready_shift hm hrest.2⟩
  | ghost =>
      rw [hop] at hrest
      simp only [decide_eq_true_eq, hcell] at hrest ⊢
      exact hrest
  | unghost =>
      rw [hop] at hrest
      simp only [Bool.and_eq_true, decide_eq_true_eq, hcell] at hrest ⊢
      exact ⟨hrest.1, ready_shift hm hrest.2⟩

/-- 頭の手は尻尾の配置を変えない。 -/
theorem shiftC_step_head {u : ℕ} {c : Config} {m : Move} (hm : m.v ≤ u) :
    shiftC (u + 1) (step c m) = shiftC (u + 1) c := by
  funext v
  rw [shiftC_apply, shiftC_apply]
  exact Function.update_of_ne (by omega) _ _

/-- 尻尾の手は頭の配置を変えない。 -/
theorem agree_step_tail {u : ℕ} {c : Config} {m : Move} (hm : u < m.v) :
    AgreeOn (u + 1) c (step c m) := by
  intro v hv
  exact (Function.update_of_ne (by omega) _ _).symm

/-- 尻尾の手のずらしは `step` と可換。 -/
theorem shiftC_step_tail {u : ℕ} {c : Config} {m : Move} (hm : u < m.v) :
    shiftC (u + 1) (step c m) = step (shiftC (u + 1) c) (shiftM (u + 1) m) := by
  funext v
  rw [shiftC_apply]
  show Function.update c m.v (result m.op) (v + (u + 1))
     = Function.update (shiftC (u + 1) c) (m.v - (u + 1)) (result m.op) v
  by_cases hv : v = m.v - (u + 1)
  · subst hv
    rw [Function.update_self]
    have : m.v - (u + 1) + (u + 1) = m.v := by omega
    rw [this, Function.update_self]
  · rw [Function.update_of_ne hv, Function.update_of_ne (by omega), shiftC_apply]

/-! ## 手順の射影 -/

/-- 頭 = 頂点 `0..u` に作用する手（順序を保つ）。 -/
def headMoves (u : ℕ) (ms : List Move) : List Move := ms.filter (fun m => decide (m.v ≤ u))

/-- 尻尾 = 頂点 `u+1..` に作用する手（添字を `u+1` ずらす）。 -/
def tailMoves (u : ℕ) (ms : List Move) : List Move :=
  (ms.filter (fun m => decide (u < m.v))).map (shiftM (u + 1))

@[simp] theorem headMoves_nil (u : ℕ) : headMoves u [] = [] := rfl
@[simp] theorem tailMoves_nil (u : ℕ) : tailMoves u [] = [] := rfl

theorem headMoves_cons_head {u : ℕ} {m : Move} (ms : List Move) (h : m.v ≤ u) :
    headMoves u (m :: ms) = m :: headMoves u ms := by simp [headMoves, h]

theorem headMoves_cons_tail {u : ℕ} {m : Move} (ms : List Move) (h : u < m.v) :
    headMoves u (m :: ms) = headMoves u ms := by
  simp [headMoves, Nat.not_le.mpr h]

theorem tailMoves_cons_tail {u : ℕ} {m : Move} (ms : List Move) (h : u < m.v) :
    tailMoves u (m :: ms) = shiftM (u + 1) m :: tailMoves u ms := by simp [tailMoves, h]

theorem tailMoves_cons_head {u : ℕ} {m : Move} (ms : List Move) (h : m.v ≤ u) :
    tailMoves u (m :: ms) = tailMoves u ms := by
  simp [tailMoves, Nat.not_lt.mpr h]

/-- **頭の射影は妥当**。 -/
theorem valid_headMoves {n u : ℕ} : ∀ (ms : List Move) (c : Config), valid n c ms = true →
    valid (u + 1) c (headMoves u ms) = true := by
  intro ms
  induction ms with
  | nil => intro c _; simp
  | cons m ms ih =>
      intro c h
      simp only [valid_cons, Bool.and_eq_true] at h
      by_cases hm : m.v ≤ u
      · rw [headMoves_cons_head ms hm]
        simp only [valid_cons, Bool.and_eq_true]
        exact ⟨legal_head h.1 hm, ih (step c m) h.2⟩
      · simp only [Nat.not_le] at hm
        rw [headMoves_cons_tail ms hm]
        exact valid_congr (fun v hv => (agree_step_tail hm v hv).symm) _ (ih (step c m) h.2)

/-- **尻尾の射影は妥当**。 -/
theorem valid_tailMoves {n u : ℕ} : ∀ (ms : List Move) (c : Config), valid n c ms = true →
    valid (n - (u + 1)) (shiftC (u + 1) c) (tailMoves u ms) = true := by
  intro ms
  induction ms with
  | nil => intro c _; simp
  | cons m ms ih =>
      intro c h
      simp only [valid_cons, Bool.and_eq_true] at h
      by_cases hm : u < m.v
      · rw [tailMoves_cons_tail ms hm]
        simp only [valid_cons, Bool.and_eq_true]
        refine ⟨legal_tail h.1 hm, ?_⟩
        rw [← shiftC_step_tail hm]
        exact ih (step c m) h.2
      · simp only [Nat.not_lt] at hm
        rw [tailMoves_cons_head ms hm, ← shiftC_step_head (c := c) hm]
        exact ih (step c m) h.2

end Spooky
