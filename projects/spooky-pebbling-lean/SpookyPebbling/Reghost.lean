/-
# ゴーストの回収 — 掃きが残したゴーストは頭の手順が「ついでに」消す

`Sweep.lean` の掃きは `v_0..v_{k-2}` にゴーストを残す。一方 $T_{UP}(k,s)$ は
**ゴーストの無い**始状態 `sinkPebble k` で定義されている。両者を繋ぐのが本ファイル。

> **補題（再ゴースト）**: `sinkPebble k` から全空への妥当な手順 `ms` があり、
> 余分にゴーストが在る頂点それぞれに `ms` 中の「置く手」が 1 つ以上あるなら、
> **同じ手数**でゴースト入りの始状態から全空へ行ける。

読み替えは 1 種類だけ: `pebble v` のうち、新しい走りで `v` がゴーストであるものを
`unghost v` にする。前提（`v` の直前がペブル）も `P` への効果も同じで、ついでに
ゴーストが 1 つ消える。**`Ghost.lean` の補題G のちょうど逆向き**である。

「置く手が 1 つ以上ある」ことは本当に成り立つ: `v_{k-1}` は始めペブルで終わりは空、
その最後のペブル除去は `unpebble`（ゴーストにすると後で unghost が要る）なので
`v_{k-2}` にペブルが要り、下向きに `v_0` まで下りる（`head_places`）。
-/
import SpookyPebbling.Sweep

namespace Spooky

/-! ## 「置く手が在る」ことの保証 -/

/-- ペブルの在る頂点 `i (0<i)` が最後に空になるなら、途中で `i-1` がペブルになる時刻が在る。 -/
theorem pred_pebbled_of_clear {n : ℕ} : ∀ (N : ℕ) (ms : List Move), ms.length ≤ N →
    ∀ (c : Config), valid n c ms = true →
    ∀ {i : ℕ}, 0 < i → c i = Cell.pebble → exec c ms i = Cell.empty →
    ∃ l₁ l₂, ms = l₁ ++ l₂ ∧ exec c l₁ (i - 1) = Cell.pebble := by
  intro N
  induction N with
  | zero =>
      intro ms hlen c _ i _ hp he
      have hnil : ms = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hnil
      rw [show exec c [] i = c i from rfl, hp] at he
      exact absurd he (by simp)
  | succ N ih =>
      intro ms hlen c hv i hi hp he
      match ms with
      | [] =>
          rw [show exec c [] i = c i from rfl, hp] at he
          exact absurd he (by simp)
      | m :: ms' =>
          simp only [valid_cons, Bool.and_eq_true] at hv
          simp only [List.length_cons] at hlen
          by_cases hmv : m.v = i
          · subst hmv
            have hleg := hv.1
            unfold legal at hleg
            simp only [Bool.and_eq_true] at hleg
            have h2 := hleg.2
            have hop : m.op = Op.unpebble ∨ m.op = Op.ghost := by
              cases hcase : m.op <;> rw [hcase] at h2 <;>
                simp only [Bool.and_eq_true, decide_eq_true_eq] at h2 <;> simp_all
            rcases hop with hop | hop
            · -- unpebble: 直前の頂点がペブル
              refine ⟨[], m :: ms', rfl, ?_⟩
              have hr : ready c m.v = true := by rw [hop] at h2; exact Bool.and_elim_right h2
              unfold ready at hr
              simp only [Bool.or_eq_true, decide_eq_true_eq] at hr
              rcases hr with hr | hr
              · omega
              · exact hr
            · -- ghost: いつか unghost に戻るので、そこから再帰
              have hgh : step c m m.v = Cell.ghost := by rw [step_self, hop]; rfl
              have he' : exec (step c m) ms' m.v = Cell.empty := he
              obtain ⟨l₁, l₂, heq, hne, hpp⟩ :=
                ghost_becomes_pebble ms' (step c m) hv.2 hgh he'
              have hl₁ : 0 < l₁.length := List.length_pos_of_ne_nil hne
              have hlen₂ : l₂.length ≤ N := by
                have hsum : l₁.length + l₂.length = ms'.length := by rw [heq]; simp
                omega
              have hv₂ : valid n (exec (step c m) l₁) l₂ = true :=
                valid_append_right l₁ l₂ (step c m) (heq ▸ hv.2)
              have he₂ : exec (exec (step c m) l₁) l₂ m.v = Cell.empty := by
                rw [← exec_append l₁ l₂ (step c m), ← heq]; exact he'
              obtain ⟨r₁, r₂, hr, hrp⟩ :=
                ih l₂ hlen₂ (exec (step c m) l₁) hv₂ hi hpp he₂
              refine ⟨m :: (l₁ ++ r₁), r₂, ?_, ?_⟩
              · rw [heq, hr, List.cons_append, List.append_assoc]
              · show exec (step c m) (l₁ ++ r₁) (m.v - 1) = Cell.pebble
                rw [exec_append]; exact hrp
          · have hp' : step c m i = Cell.pebble := by rw [step_ne_of_ne hmv]; exact hp
            obtain ⟨l₁, l₂, heq, hpp⟩ := ih ms' (by omega) (step c m) hv.2 hi hp' he
            exact ⟨m :: l₁, l₂, by rw [List.cons_append, ← heq], hpp⟩

/-- **頭の手順は `v_0 .. v_{k-2}` のどれにもペブルが載る時刻を持つ**。 -/
theorem head_pebbled {k s : ℕ} {ms : List Move}
    (h : Run k s (sinkPebble k) ms allEmpty) :
    ∀ j, j + 1 < k → ∃ l₁ l₂, ms = l₁ ++ l₂ ∧ exec (sinkPebble k) l₁ j = Cell.pebble := by
  intro j hj
  obtain ⟨hok, hagree⟩ := h
  obtain ⟨hv, _⟩ := (ok_iff ms (sinkPebble k)).mp hok
  have hstart : sinkPebble k (k - 1) = Cell.pebble := by rw [sinkPebble_apply]; simp
  have hend : exec (sinkPebble k) ms (k - 1) = Cell.empty := by
    rw [hagree (k - 1) (by omega)]; rfl
  obtain ⟨l₁, l₂, heq, hpp⟩ :=
    pred_pebbled_of_clear ms.length ms le_rfl (sinkPebble k) hv (by omega) hstart hend
  have hv₁ : valid k (sinkPebble k) l₁ = true := valid_append_left l₁ l₂ _ (heq ▸ hv)
  have hc : ∀ t, t ≤ k - 1 - 1 → sinkPebble k t ≠ Cell.pebble := by
    intro t ht
    rw [sinkPebble_apply, if_neg (by omega)]
    simp
  obtain ⟨r₁, r₂, hr, hrp⟩ :=
    reaches_below (k - 1 - 1) l₁ (sinkPebble k) hv₁ hc hpp j (by omega)
  exact ⟨r₁, r₂ ++ l₂, by rw [heq, hr, List.append_assoc], hrp⟩

/-- **頭の手順は `v_0 .. v_{k-2}` のどれも 1 回以上「置く」**。 -/
theorem head_places {k s : ℕ} {ms : List Move}
    (h : Run k s (sinkPebble k) ms allEmpty) :
    ∀ j, j + 1 < k → 0 < ms.countP (isPlace j) := by
  intro j hj
  obtain ⟨r₁, r₂, hr, hrp⟩ := head_pebbled h j hj
  have hc : sinkPebble k j ≠ Cell.pebble := by
    rw [sinkPebble_apply, if_neg (by omega)]; simp
  have hplace : 0 < r₁.countP (isPlace j) := exists_place r₁ (sinkPebble k) hc hrp
  have h1 : r₁.countP (isPlace j) ≤ ms.countP (isPlace j) := by
    rw [hr, List.countP_append]; omega
  omega

/-! ## 再ゴースト（補題G の逆向き） -/

/-- 不変量: `c`（ゴーストを足した側）は `a` とペブルを共有し、`a` が空の所に
余分なゴーストを持ちうる。ただしその頂点には**残りの手順に置く手が在る**。 -/
def Dom2 (ms : List Move) (c a : Config) : Prop :=
  ∀ v, c v = a v ∨ (c v = Cell.ghost ∧ a v = Cell.empty ∧ 0 < ms.countP (isPlace v))

theorem Dom2_pebble {ms : List Move} {c a : Config} (h : Dom2 ms c a) (v : ℕ) :
    c v = Cell.pebble ↔ a v = Cell.pebble := by
  rcases h v with he | ⟨h1, h2, _⟩
  · rw [he]
  · rw [h1, h2]; simp

theorem Dom2_pcount {n : ℕ} {ms : List Move} {c a : Config} (h : Dom2 ms c a) :
    pcount n c = pcount n a :=
  congrArg Finset.card (Finset.filter_congr fun v _ => by simp [Dom2_pebble h v])

theorem Dom2_ready {ms : List Move} {c a : Config} (h : Dom2 ms c a) (v : ℕ) :
    ready c v = ready a v := by
  unfold ready
  simp [Dom2_pebble h (v - 1)]

/-- 空の残り手順では、`Dom2` は「一致」に潰れる。 -/
theorem Dom2_nil {c a : Config} (h : Dom2 [] c a) (v : ℕ) : c v = a v := by
  rcases h v with he | ⟨_, _, hlt⟩
  · exact he
  · simp at hlt

/-- 読み替え: `pebble v` は、新しい走りで `v` がゴーストなら `unghost v` にする。 -/
def tweak2 (c : Config) (m : Move) : Move :=
  if m.op = Op.pebble ∧ c m.v = Cell.ghost then ⟨Op.unghost, m.v⟩ else m

@[simp] theorem tweak2_v (c : Config) (m : Move) : (tweak2 c m).v = m.v := by
  unfold tweak2; split <;> rfl

theorem tweak2_result (c : Config) (m : Move) : result (tweak2 c m).op = result m.op := by
  unfold tweak2
  by_cases h : m.op = Op.pebble ∧ c m.v = Cell.ghost
  · simp [h, h.1, result]
  · simp [h]

def strip2 (c : Config) : List Move → List Move
  | [] => []
  | m :: ms => tweak2 c m :: strip2 (step c (tweak2 c m)) ms

@[simp] theorem strip2_nil (c : Config) : strip2 c [] = [] := rfl

@[simp] theorem strip2_cons (c : Config) (m : Move) (ms : List Move) :
    strip2 c (m :: ms) = tweak2 c m :: strip2 (step c (tweak2 c m)) ms := rfl

theorem strip2_length (c : Config) (ms : List Move) : (strip2 c ms).length = ms.length := by
  induction ms generalizing c with
  | nil => simp
  | cons m ms ih => simp [ih]

/-- **再ゴーストの核**: `Dom2` のもとで読み替えた手順は妥当性・上限・終状態を保つ。 -/
theorem strip2_ok {n s : ℕ} : ∀ (ms : List Move) (c a : Config), Dom2 ms c a →
    ok n s a ms = true →
    ok n s c (strip2 c ms) = true ∧ Dom2 [] (exec c (strip2 c ms)) (exec a ms) := by
  intro ms
  induction ms with
  | nil =>
      intro c a hd h
      refine ⟨?_, hd⟩
      unfold ok at h ⊢
      simp only [strip2_nil, decide_eq_true_eq] at h ⊢
      rw [Dom2_pcount hd]
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
      have hleg' : legal n c (tweak2 c m) = true := by
        by_cases hcond : m.op = Op.pebble ∧ c m.v = Cell.ghost
        · have : tweak2 c m = ⟨Op.unghost, m.v⟩ := by unfold tweak2; simp [hcond]
          rw [this]
          rw [hcond.1] at h2
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
          unfold legal
          simp [hlt, hcond.2, Dom2_ready hd m.v, h2.2]
        · have hid : tweak2 c m = m := by unfold tweak2; simp [hcond]
          rw [hid]
          unfold legal
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          refine ⟨hlt, ?_⟩
          cases hop : m.op with
          | pebble =>
              rw [hop] at h2
              simp only [Bool.and_eq_true, decide_eq_true_eq] at h2 ⊢
              have hce : c m.v = Cell.empty := by
                rcases hd m.v with he | ⟨h1, _⟩
                · exact he.trans h2.1
                · exact absurd h1 (by intro hg; exact hcond ⟨hop, hg⟩)
              exact ⟨hce, by rw [Dom2_ready hd m.v]; exact h2.2⟩
          | unpebble =>
              rw [hop] at h2
              simp only [Bool.and_eq_true, decide_eq_true_eq] at h2 ⊢
              exact ⟨(Dom2_pebble hd m.v).mpr h2.1, by rw [Dom2_ready hd m.v]; exact h2.2⟩
          | ghost =>
              rw [hop] at h2
              simp only [decide_eq_true_eq] at h2 ⊢
              exact (Dom2_pebble hd m.v).mpr h2
          | unghost =>
              rw [hop] at h2
              simp only [Bool.and_eq_true, decide_eq_true_eq] at h2 ⊢
              have hcg : c m.v = Cell.ghost := by
                rcases hd m.v with he | ⟨_, h2', _⟩
                · exact he.trans h2.1
                · rw [h2'] at h2; exact absurd h2.1 (by simp)
              exact ⟨hcg, by rw [Dom2_ready hd m.v]; exact h2.2⟩
      -- 1 手後も不変量が保たれる
      have hd' : Dom2 ms (step c (tweak2 c m)) (step a m) := by
        intro v
        by_cases hv : v = m.v
        · subst hv
          left
          show Function.update c (tweak2 c m).v (result (tweak2 c m).op) m.v
             = Function.update a m.v (result m.op) m.v
          rw [tweak2_v, Function.update_self, Function.update_self, tweak2_result]
        · have e1 : step c (tweak2 c m) v = c v :=
            Function.update_of_ne (by simpa using hv) _ _
          have e2 : step a m v = a v := Function.update_of_ne hv _ _
          rw [e1, e2]
          rcases hd v with he | ⟨h1, h2', h3⟩
          · exact Or.inl he
          · refine Or.inr ⟨h1, h2', ?_⟩
            have hnp : isPlace v m = false := by
              unfold isPlace
              simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
              exact Or.inl (fun hc => hv hc.symm)
            rw [List.countP_cons, hnp] at h3
            simpa using h3
      obtain ⟨hok', hdom'⟩ := ih (step c (tweak2 c m)) (step a m) hd' htail
      refine ⟨?_, hdom'⟩
      show ok n s c (tweak2 c m :: strip2 (step c (tweak2 c m)) ms) = true
      unfold ok
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨by rw [Dom2_pcount hd]; exact hcap, hleg'⟩, hok'⟩

/-- **補題（再ゴースト）**: ゴーストを足した始状態からでも、同じ手数で全空に行ける。 -/
theorem Run_reghost {k s : ℕ} {c a : Config} {ms : List Move}
    (hd : Dom2 ms c a) (h : Run k s a ms allEmpty) :
    Run k s c (strip2 c ms) allEmpty ∧ (strip2 c ms).length = ms.length := by
  obtain ⟨hok, hagree⟩ := h
  obtain ⟨hok', hdom'⟩ := strip2_ok ms c a hd hok
  refine ⟨⟨hok', ?_⟩, strip2_length c ms⟩
  intro v hv
  rw [Dom2_nil hdom' v]
  exact hagree v hv

end Spooky
