/-
# 補題G — 余分なゴーストは損にならない

分解の $\ge$ 方向で、頭 $v_1..v_k$ の後半は「$v_k$ にペブル・**$v_1..v_{k-1}$ にゴーストが
残っているかもしれない**状態」から始まる。ところが $T_{UP}$ はゴースト無しの始状態で
定義されているので、そのままでは $T_{UP}(k,s)$ で下から押さえられない。

押さえられる。**ゴーストが余分に在っても手数は減らない**からである。

*証明の中身*: 同じ手列を replay し、`unghost v` のうち**新しい走りで $v$ がゴーストで
ないもの**だけを `pebble v` に読み替える。前提（$v$ の直前がペブル）も $P$ への効果も
同じなので、

$$P^{new}_t = P^{old}_t,\qquad G^{new}_t \subseteq G^{old}_t$$

が各時刻で保たれる。ペブル数が等しいので上限も同じ。終状態が全空なら新しい走りも全空。

この読み替えを `strip` として定義し、不変量を `Dom` として書く。
-/
import SpookyPebbling.Defs

namespace Spooky

/-- 不変量: `c`（ゴーストを落とした側）は `a` とペブルを共有し、ゴーストは高々 `a` の分だけ。

各頂点で「一致している」か「`c` は空・`a` はゴースト」のどちらか。 -/
def Dom (c a : Config) : Prop :=
  ∀ v, c v = a v ∨ (c v = Cell.empty ∧ a v = Cell.ghost)

/-- 始状態からゴーストを落とす。 -/
def stripGhosts (a : Config) : Config :=
  fun v => if a v = Cell.ghost then Cell.empty else a v

theorem Dom_stripGhosts (a : Config) : Dom (stripGhosts a) a := by
  intro v
  unfold stripGhosts
  by_cases h : a v = Cell.ghost
  · exact Or.inr ⟨by simp [h], h⟩
  · exact Or.inl (by simp [h])

theorem Dom_refl (a : Config) : Dom a a := fun _ => Or.inl rfl

/-- `Dom` はペブルの位置を保つ。 -/
theorem Dom_pebble {c a : Config} (h : Dom c a) (v : ℕ) :
    c v = Cell.pebble ↔ a v = Cell.pebble := by
  rcases h v with he | ⟨h1, h2⟩
  · rw [he]
  · rw [h1, h2]; simp

theorem Dom_pcount {n : ℕ} {c a : Config} (h : Dom c a) : pcount n c = pcount n a := by
  unfold pcount
  exact congrArg Finset.card (Finset.filter_congr fun v _ => by
    simp [Dom_pebble h v])

theorem Dom_ready {c a : Config} (h : Dom c a) (v : ℕ) : ready c v = ready a v := by
  unfold ready
  simp [Dom_pebble h (v - 1)]

/-- 読み替え: `unghost v` は、**新しい走りで `v` がゴーストでない**ときだけ `pebble v` にする。 -/
def tweak (c : Config) (m : Move) : Move :=
  if m.op = Op.unghost ∧ c m.v ≠ Cell.ghost then ⟨Op.pebble, m.v⟩ else m

@[simp] theorem tweak_v (c : Config) (m : Move) : (tweak c m).v = m.v := by
  unfold tweak; split <;> rfl

theorem tweak_pos {c : Config} {m : Move} (h : m.op = Op.unghost ∧ c m.v ≠ Cell.ghost) :
    tweak c m = ⟨Op.pebble, m.v⟩ := by unfold tweak; simp [h]

theorem tweak_neg {c : Config} {m : Move} (h : ¬(m.op = Op.unghost ∧ c m.v ≠ Cell.ghost)) :
    tweak c m = m := by unfold tweak; simp [h]

/-- ゴースト無しの走りでの読み替え。`c` は**新しい走りの現在の配置**。 -/
def strip (c : Config) : List Move → List Move
  | [] => []
  | m :: ms => tweak c m :: strip (step c (tweak c m)) ms

@[simp] theorem strip_nil (c : Config) : strip c [] = [] := rfl

@[simp] theorem strip_cons (c : Config) (m : Move) (ms : List Move) :
    strip c (m :: ms) = tweak c m :: strip (step c (tweak c m)) ms := rfl

theorem strip_length (c : Config) (ms : List Move) : (strip c ms).length = ms.length := by
  induction ms generalizing c with
  | nil => simp
  | cons m ms ih => simp [ih]

/-- **補題G の核**: 不変量 `Dom` のもとで、読み替えた手順は妥当性・上限・終状態を保つ。 -/
theorem strip_ok {n s : ℕ} : ∀ (ms : List Move) (c a : Config), Dom c a → ok n s a ms = true →
    ok n s c (strip c ms) = true ∧ Dom (exec c (strip c ms)) (exec a ms) := by
  intro ms
  induction ms with
  | nil =>
      intro c a hd h
      refine ⟨?_, hd⟩
      simp only [strip_nil, ok, decide_eq_true_eq] at *
      rw [Dom_pcount hd]
      exact h
  | cons m ms ih =>
      intro c a hd h
      have hcap : pcount n a ≤ s := by
        unfold ok at h
        exact of_decide_eq_true (Bool.and_elim_left (Bool.and_elim_left h))
      have hleg : legal n a m = true := by
        unfold ok at h; exact Bool.and_elim_right (Bool.and_elim_left h)
      have htail : ok n s (step a m) ms = true := by
        unfold ok at h; exact Bool.and_elim_right h
      have hlt : m.v < n := legal_lt hleg
      have h2 : (match m.op with
          | .pebble => decide (a m.v = Cell.empty) && ready a m.v
          | .unpebble => decide (a m.v = Cell.pebble) && ready a m.v
          | .ghost => decide (a m.v = Cell.pebble)
          | .unghost => decide (a m.v = Cell.ghost) && ready a m.v) = true := by
        unfold legal at hleg; exact Bool.and_elim_right hleg
      -- 新しい走りでも 1 手目は妥当
      have hleg' : legal n c (tweak c m) = true := by
        by_cases hcond : m.op = Op.unghost ∧ c m.v ≠ Cell.ghost
        · rw [tweak_pos hcond]
          rw [hcond.1] at h2
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
          have hc : c m.v = Cell.empty := by
            rcases hd m.v with he | ⟨h1, _⟩
            · exact absurd (he.trans h2.1) hcond.2
            · exact h1
          unfold legal
          simp [hlt, hc, Dom_ready hd m.v, h2.2]
        · rw [tweak_neg hcond]
          unfold legal
          refine Bool.and_eq_true _ _ ▸ ?_
          simp only [decide_eq_true_eq, Bool.and_eq_true]
          refine ⟨hlt, ?_⟩
          cases hop : m.op with
          | pebble =>
              rw [hop] at h2
              simp only [Bool.and_eq_true, decide_eq_true_eq] at h2 ⊢
              have hc : c m.v = Cell.empty := by
                rcases hd m.v with he | ⟨h1, _⟩
                · exact he.trans h2.1
                · exact h1
              exact ⟨hc, by rw [Dom_ready hd m.v]; exact h2.2⟩
          | unpebble =>
              rw [hop] at h2
              simp only [Bool.and_eq_true, decide_eq_true_eq] at h2 ⊢
              exact ⟨(Dom_pebble hd m.v).mpr h2.1, by rw [Dom_ready hd m.v]; exact h2.2⟩
          | ghost =>
              rw [hop] at h2
              simp only [decide_eq_true_eq] at h2 ⊢
              exact (Dom_pebble hd m.v).mpr h2
          | unghost =>
              have hc : c m.v = Cell.ghost := by
                by_contra hne; exact hcond ⟨hop, hne⟩
              rw [hop] at h2
              simp only [Bool.and_eq_true, decide_eq_true_eq] at h2 ⊢
              exact ⟨hc, by rw [Dom_ready hd m.v]; exact h2.2⟩
      -- 1 手後も不変量が保たれる
      have hd' : Dom (step c (tweak c m)) (step a m) := by
        intro v
        by_cases hv : v = m.v
        · subst hv
          left
          show Function.update c (tweak c m).v (result (tweak c m).op) m.v
             = Function.update a m.v (result m.op) m.v
          simp only [tweak_v, Function.update_self]
          by_cases hcond : m.op = Op.unghost ∧ c m.v ≠ Cell.ghost
          · simp [tweak_pos hcond, hcond.1, result]
          · simp [tweak_neg hcond]
        · have e1 : step c (tweak c m) v = c v :=
            Function.update_of_ne (by simpa using hv) _ _
          have e2 : step a m v = a v := Function.update_of_ne hv _ _
          rw [e1, e2]
          exact hd v
      obtain ⟨hok', hdom'⟩ := ih (step c (tweak c m)) (step a m) hd' htail
      refine ⟨?_, hdom'⟩
      show ok n s c (tweak c m :: strip (step c (tweak c m)) ms) = true
      unfold ok
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨by rw [Dom_pcount hd]; exact hcap, hleg'⟩, hok'⟩

/-- **補題G**: 始状態のゴーストを落としても、同じ長さの妥当な手順が在る。 -/
theorem Run_stripGhosts {n s : ℕ} {a : Config} {ms : List Move}
    (h : Run n s a ms allEmpty) :
    Run n s (stripGhosts a) (strip (stripGhosts a) ms) allEmpty ∧
      (strip (stripGhosts a) ms).length = ms.length := by
  obtain ⟨hok, hagree⟩ := h
  obtain ⟨hok', hdom'⟩ := strip_ok ms (stripGhosts a) a (Dom_stripGhosts a) hok
  refine ⟨⟨hok', ?_⟩, strip_length _ _⟩
  intro v hv
  rcases hdom' v with he | ⟨h1, _⟩
  · rw [he]; exact hagree v hv
  · rw [h1]; rfl

/-- 使う形: 「$v_{k-1}$ にペブル＋ゴースト任意」から全空への手順は `TUP k s` 以上。 -/
theorem TUP_le_of_ghosts {k s : ℕ} {a : Config} {ms : List Move}
    (hstrip : AgreeOn k (stripGhosts a) (sinkPebble k))
    (h : Run k s a ms allEmpty) : TUP k s ≤ ms.length := by
  obtain ⟨hrun, hlen⟩ := Run_stripGhosts h
  obtain ⟨hok, hagree⟩ := hrun
  have : TUP k s ≤ (strip (stripGhosts a) ms).length :=
    TUP_le ⟨strip (stripGhosts a) ms, rfl, ok_congr hstrip hok,
      fun v hv => (exec_congr _ hstrip v hv).symm.trans (hagree v hv)⟩
  omega

end Spooky
