/-
# `k` を選ぶための道具

分解の $\ge$ 方向で `k` を「与えられた手順の内側」で取る:

$$s^\dagger := \max_t |P_t|,\qquad F := \{t : |P_t| = s^\dagger\},\qquad
  u := \max_{t\in F}\ \min\{i : v_i\in P_t\},\qquad k := u+1.$$

そのために要るのは 3 つ。

1. **ペブル数の分割** `pcount n c = pcount (u+1) c + pcount (n-(u+1)) (shiftC (u+1) c)`
   （頭と尻尾に分かれる）
2. **最下位ペブル** `minPeb`
3. **有限リスト上の最大元の存在**（`s†` と `u` の両方を取るのに使う）
-/
import SpookyPebbling.Count

namespace Spooky

/-! ## ペブル数の分割 -/

theorem pcount_split (n u : ℕ) (h : u + 1 ≤ n) (c : Config) :
    pcount n c = pcount (u + 1) c + pcount (n - (u + 1)) (shiftC (u + 1) c) := by
  classical
  have hlow : (Finset.range n).filter (fun v => c v = Cell.pebble ∧ v < u + 1)
      = (Finset.range (u + 1)).filter (fun v => c v = Cell.pebble) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨_, hp, hv⟩; exact ⟨hv, hp⟩
    · rintro ⟨hv, hp⟩; exact ⟨by omega, hp, hv⟩
  have hhigh : (Finset.range n).filter (fun v => c v = Cell.pebble ∧ u + 1 ≤ v)
      = ((Finset.range (n - (u + 1))).filter
          (fun w => shiftC (u + 1) c w = Cell.pebble)).image (fun w => w + (u + 1)) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, shiftC_apply]
    constructor
    · rintro ⟨hv, hp, hu⟩
      exact ⟨v - (u + 1), ⟨by omega, by rw [Nat.sub_add_cancel hu]; exact hp⟩, by omega⟩
    · rintro ⟨w, ⟨hw, hp⟩, rfl⟩
      exact ⟨by omega, hp, by omega⟩
  have hinj : Set.InjOn (fun w => w + (u + 1))
      ((Finset.range (n - (u + 1))).filter (fun w => shiftC (u + 1) c w = Cell.pebble) : Finset ℕ) := by
    intro a _ b _ hab
    simp only at hab
    omega
  have hdisj : Disjoint
      ((Finset.range n).filter (fun v => c v = Cell.pebble ∧ v < u + 1))
      ((Finset.range n).filter (fun v => c v = Cell.pebble ∧ u + 1 ≤ v)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_filter, Finset.mem_range] at ha hb
    obtain ⟨-, -, h1⟩ := ha
    obtain ⟨-, -, h2⟩ := hb
    omega
  have hunion : (Finset.range n).filter (fun v => c v = Cell.pebble)
      = ((Finset.range n).filter (fun v => c v = Cell.pebble ∧ v < u + 1))
        ∪ ((Finset.range n).filter (fun v => c v = Cell.pebble ∧ u + 1 ≤ v)) := by
    ext v
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hv, hp⟩
      rcases Nat.lt_or_ge v (u + 1) with hlt | hge
      · exact Or.inl ⟨hv, hp, hlt⟩
      · exact Or.inr ⟨hv, hp, hge⟩
    · rintro (⟨hv, hp, _⟩ | ⟨hv, hp, _⟩) <;> exact ⟨hv, hp⟩
  unfold pcount
  rw [hunion, Finset.card_union_of_disjoint hdisj, hlow, hhigh,
    Finset.card_image_of_injOn hinj]

/-- 頭にペブルが無いことと `pcount (u+1) c = 0` は同値。 -/
theorem pcount_eq_zero_iff {k : ℕ} {c : Config} :
    pcount k c = 0 ↔ ∀ v, v < k → c v ≠ Cell.pebble := by
  unfold pcount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h v hv; exact h (Finset.mem_range.mpr hv)
  · intro h v hv; exact h v (Finset.mem_range.mp hv)

/-- 相異なる 2 頂点にペブルが在れば `pcount ≥ 2`。 -/
theorem two_le_pcount {n : ℕ} {c : Config} {a b : ℕ} (hab : a ≠ b) (ha : a < n) (hb : b < n)
    (hpa : c a = Cell.pebble) (hpb : c b = Cell.pebble) : 2 ≤ pcount n c := by
  classical
  unfold pcount
  have hsub : ({a, b} : Finset ℕ) ⊆ (Finset.range n).filter (fun v => c v = Cell.pebble) := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl <;> simp [Finset.mem_filter, Finset.mem_range, ha, hb, hpa, hpb]
  calc 2 = ({a, b} : Finset ℕ).card := by rw [Finset.card_insert_of_notMem (by simpa using hab)]; simp
    _ ≤ _ := Finset.card_le_card hsub

/-! ## 最下位ペブル -/

/-- 頂点 `0..n-1` のうちペブルが在る最小の添字（無ければ `n`）。 -/
noncomputable def minPeb (n : ℕ) (c : Config) : ℕ :=
  if h : ((Finset.range n).filter (fun v => c v = Cell.pebble)).Nonempty then
    ((Finset.range n).filter (fun v => c v = Cell.pebble)).min' h
  else n

theorem minPeb_spec {n : ℕ} {c : Config} (h : 0 < pcount n c) :
    minPeb n c < n ∧ c (minPeb n c) = Cell.pebble ∧ ∀ v, v < minPeb n c → c v ≠ Cell.pebble := by
  classical
  have hne : ((Finset.range n).filter (fun v => c v = Cell.pebble)).Nonempty :=
    Finset.card_pos.mp h
  unfold minPeb
  rw [dif_pos hne]
  have hmem := Finset.min'_mem _ hne
  simp only [Finset.mem_filter, Finset.mem_range] at hmem
  refine ⟨hmem.1, hmem.2, ?_⟩
  intro v hv hpv
  have : ((Finset.range n).filter (fun x => c x = Cell.pebble)).min' hne ≤ v :=
    Finset.min'_le _ _ (by
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hpv⟩)
  omega

/-- ペブルが在る頂点は最下位ペブル以上。 -/
theorem minPeb_le {n : ℕ} {c : Config} {v : ℕ} (hv : v < n) (hp : c v = Cell.pebble) :
    minPeb n c ≤ v := by
  classical
  have hne : ((Finset.range n).filter (fun x => c x = Cell.pebble)).Nonempty :=
    ⟨v, by simp [Finset.mem_filter, Finset.mem_range, hv, hp]⟩
  unfold minPeb
  rw [dif_pos hne]
  exact Finset.min'_le _ _ (by simp [Finset.mem_filter, Finset.mem_range, hv, hp])

/-! ## 有限リスト上の最大元 -/

theorem exists_max_on {α : Type} (f : α → ℕ) :
    ∀ (l : List α), l ≠ [] → ∃ a ∈ l, ∀ b ∈ l, f b ≤ f a := by
  intro l
  induction l with
  | nil => intro h; exact absurd rfl h
  | cons x xs ih =>
      intro _
      rcases List.eq_nil_or_concat xs with rfl | _
      · exact ⟨x, by simp, by intro b hb; simp at hb; subst hb; exact le_rfl⟩
      · by_cases hxs : xs = []
        · subst hxs
          exact ⟨x, by simp, by intro b hb; simp at hb; subst hb; exact le_rfl⟩
        · obtain ⟨a, ha, hmax⟩ := ih hxs
          by_cases hle : f a ≤ f x
          · refine ⟨x, by simp, ?_⟩
            intro b hb
            simp only [List.mem_cons] at hb
            rcases hb with rfl | hb
            · exact le_rfl
            · exact le_trans (hmax b hb) hle
          · refine ⟨a, by simp [ha], ?_⟩
            intro b hb
            simp only [List.mem_cons] at hb
            rcases hb with rfl | hb
            · omega
            · exact hmax b hb

theorem traj_ne_nil (c : Config) (ms : List Move) : traj c ms ≠ [] := by
  cases ms <;> simp

end Spooky
