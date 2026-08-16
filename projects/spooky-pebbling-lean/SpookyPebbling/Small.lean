/-
# 小さい閉形式の下界 — `T_UP(k,s) ≥ 2k-1` と `T_UG(n,s) ≥ 2n`

θ の証明鎖（定理A の望遠鏡）が最初に要求する 2 本。どちらも
**「各頂点が 1 回は置かれ、1 回は外される」**という数え上げだけで出る。

- **unpebbling**（`sinkPebble k → 空`）: `v_0..v_{k-2}` は置かれ（`k-1` 手）、
  `v_0..v_{k-1}` は外される（`k` 手）。合計 `2k-1`
  （`v_{k-1}` は初めからペブルなので置かれるとは限らない）
- **unghosting**（`sinkGhost n → 空`）: `v_0..v_{n-1}` は**すべて**置かれ（`n` 手。
  終端のゴーストも `unghost`＝置く手で消すしかない）、すべて外される（`n` 手）。合計 `2n`

`Count.lean` の `sum_countP_le_length`（互いに素な述語族の `countP` の総和 ≤ 長さ）を
「置く `p` 個・外す `r` 個」の形に一般化して使う。
-/
import SpookyPebbling.Unghost

namespace Spooky

/-! ## 置く手・外す手を並べた述語族 -/

/-- `i < p` なら「`i` を置く」、そうでなければ「`i-p` を外す」。 -/
def prTag (p : ℕ) (i : ℕ) (m : Move) : Bool :=
  if i < p then isPlace i m else isRemove (i - p) m

theorem prTag_lt {p i : ℕ} (h : i < p) : prTag p i = isPlace i := by
  funext m; unfold prTag; rw [if_pos h]

theorem prTag_ge {p i : ℕ} (h : ¬ i < p) : prTag p i = isRemove (i - p) := by
  funext m; unfold prTag; rw [if_neg h]

theorem prTag_disjoint (p : ℕ) :
    ∀ (m : Move) (i j : ℕ), i ≠ j → prTag p i m = true → prTag p j m = false := by
  intro m i j hne h
  by_cases hi : i < p
  · rw [prTag_lt hi] at h
    by_cases hj : j < p
    · rw [prTag_lt hj]
      unfold isPlace
      have hv : m.v = i := isPlace_v h
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
      exact Or.inl (by rw [hv]; exact hne)
    · rw [prTag_ge hj]
      exact isPlace_isRemove h
  · rw [prTag_ge hi] at h
    by_cases hj : j < p
    · rw [prTag_lt hj]
      exact isRemove_isPlace h
    · rw [prTag_ge hj]
      unfold isRemove
      have hv : m.v = i - p := isRemove_v h
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
      refine Or.inl ?_
      rw [hv]
      omega

/-- **数え上げの下界**: `0..p-1` の各頂点に置く手が、`0..r-1` の各頂点に外す手があれば、
手数は `p + r` 以上。 -/
theorem length_ge_of_places_removes {ms : List Move} {p r : ℕ}
    (hp : ∀ j, j < p → 0 < ms.countP (isPlace j))
    (hr : ∀ j, j < r → 0 < ms.countP (isRemove j)) :
    p + r ≤ ms.length := by
  have hone : ∀ i, i < p + r → 1 ≤ ms.countP (prTag p i) := by
    intro i hi
    by_cases hip : i < p
    · rw [prTag_lt hip]; exact hp i hip
    · rw [prTag_ge hip]; exact hr (i - p) (by omega)
  have hsum : p + r ≤ ∑ i ∈ Finset.range (p + r), ms.countP (prTag p i) := by
    calc p + r = ∑ _i ∈ Finset.range (p + r), 1 := by simp
      _ ≤ _ := Finset.sum_le_sum fun i hi => hone i (Finset.mem_range.mp hi)
  exact le_trans hsum (sum_countP_le_length _ (prTag_disjoint p) ms _)

/-! ## unpebbling の下界 `2k-1` -/

theorem unpebble_removes {k s : ℕ} {ms : List Move}
    (h : Run k s (sinkPebble k) ms allEmpty) :
    ∀ j, j < k → 0 < ms.countP (isRemove j) := by
  intro j hj
  obtain ⟨hok, hagree⟩ := h
  have hend : ∀ t, t < k → exec (sinkPebble k) ms t ≠ Cell.pebble := by
    intro t ht
    rw [hagree t ht]; simp [allEmpty]
  by_cases hjk : j + 1 < k
  · -- 途中でペブルが載る時刻があるので、そこから外す手が要る
    obtain ⟨l₁, l₂, hr, hrp⟩ := head_pebbled ⟨hok, hagree⟩ j hjk
    have hne : exec (exec (sinkPebble k) l₁) l₂ j ≠ Cell.pebble := by
      rw [← exec_append l₁ l₂ (sinkPebble k), ← hr]
      exact hend j hj
    have h1 : 0 < l₂.countP (isRemove j) := exists_remove l₂ (exec (sinkPebble k) l₁) hrp hne
    have h2 : l₂.countP (isRemove j) ≤ ms.countP (isRemove j) := by
      rw [hr, List.countP_append]; omega
    omega
  · -- j = k-1: 初めからペブル
    have hjeq : j = k - 1 := by omega
    subst hjeq
    exact exists_remove ms (sinkPebble k) (by rw [sinkPebble_apply]; simp) (hend _ hj)

/-- **`T_UP(k,s) ≥ 2k-1`**（無条件）。 -/
theorem two_mul_sub_one_le_TUP {k s : ℕ} (hk : 1 ≤ k) (hne : (UPLengths k s).Nonempty) :
    2 * k - 1 ≤ TUP k s := by
  obtain ⟨ms, hlen, hrun⟩ := Nat.sInf_mem hne
  have hb : (k - 1) + k ≤ ms.length :=
    length_ge_of_places_removes (fun j hj => head_places hrun j (by omega))
      (fun j hj => unpebble_removes hrun j hj)
  unfold TUP
  rw [← hlen]
  omega

/-! ## unghosting の下界 `2n` -/

/-- unghosting では**終端も含めて**すべての頂点にペブルが載る時刻がある。 -/
theorem unghost_pebbled {n s : ℕ} (hn : 1 ≤ n) {ms : List Move}
    (h : Run n s (sinkGhost n) ms allEmpty) :
    ∀ j, j < n → ∃ l₁ l₂, ms = l₁ ++ l₂ ∧ exec (sinkGhost n) l₁ j = Cell.pebble := by
  intro j hj
  obtain ⟨hok, hagree⟩ := h
  obtain ⟨hv, _⟩ := (ok_iff ms (sinkGhost n)).mp hok
  have hstart : sinkGhost n (n - 1) = Cell.ghost := by rw [sinkGhost_apply]; simp
  have hend : exec (sinkGhost n) ms (n - 1) = Cell.empty := by
    rw [hagree (n - 1) (by omega)]; rfl
  obtain ⟨l₁, l₂, heq, _, hpp⟩ := ghost_becomes_pebble ms (sinkGhost n) hv hstart hend
  have hv₁ : valid n (sinkGhost n) l₁ = true := valid_append_left l₁ l₂ _ (heq ▸ hv)
  obtain ⟨r₁, r₂, hr, hrp⟩ :=
    reaches_below (n - 1) l₁ (sinkGhost n) hv₁ (fun t _ => sinkGhost_ne_pebble n t) hpp j
      (by omega)
  exact ⟨r₁, r₂ ++ l₂, by rw [heq, hr, List.append_assoc], hrp⟩

theorem unghost_places {n s : ℕ} (hn : 1 ≤ n) {ms : List Move}
    (h : Run n s (sinkGhost n) ms allEmpty) :
    ∀ j, j < n → 0 < ms.countP (isPlace j) := by
  intro j hj
  obtain ⟨r₁, r₂, hr, hrp⟩ := unghost_pebbled hn h j hj
  have h1 : 0 < r₁.countP (isPlace j) :=
    exists_place r₁ (sinkGhost n) (sinkGhost_ne_pebble n j) hrp
  have h2 : r₁.countP (isPlace j) ≤ ms.countP (isPlace j) := by
    rw [hr, List.countP_append]; omega
  omega

theorem unghost_removes {n s : ℕ} (hn : 1 ≤ n) {ms : List Move}
    (h : Run n s (sinkGhost n) ms allEmpty) :
    ∀ j, j < n → 0 < ms.countP (isRemove j) := by
  intro j hj
  obtain ⟨hok, hagree⟩ := h
  obtain ⟨r₁, r₂, hr, hrp⟩ := unghost_pebbled hn ⟨hok, hagree⟩ j hj
  have hne : exec (exec (sinkGhost n) r₁) r₂ j ≠ Cell.pebble := by
    rw [← exec_append r₁ r₂ (sinkGhost n), ← hr, hagree j hj]
    simp [allEmpty]
  have h1 : 0 < r₂.countP (isRemove j) := exists_remove r₂ (exec (sinkGhost n) r₁) hrp hne
  have h2 : r₂.countP (isRemove j) ≤ ms.countP (isRemove j) := by
    rw [hr, List.countP_append]; omega
  omega

/-- **`T_UG(n,s) ≥ 2n`**（無条件）。 -/
theorem two_mul_le_TUG {n s : ℕ} (hn : 1 ≤ n) (hne : (UGLengths n s).Nonempty) :
    2 * n ≤ TUG n s := by
  obtain ⟨ms, hlen, hrun⟩ := Nat.sInf_mem hne
  have hb : n + n ≤ ms.length :=
    length_ge_of_places_removes (fun j hj => unghost_places hn hrun j hj)
      (fun j hj => unghost_removes hn hrun j hj)
  unfold TUG
  rw [← hlen]
  omega

end Spooky
