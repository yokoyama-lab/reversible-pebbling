/-
# KSS の意味論への移行（木）

`Game.lean` の `Legal` は、KSS Def 2.6/2.7 に対して **1 点だけ広い**: `ghost` に前提が無いので、
子が揃っている（`Ready`）頂点にも打てる。KSS ではゴーストは導出であって選べない:
ペブルを外すとき、子が揃っていればゴーストは**生じず**、揃っていなければ**必ず**生じる。

したがって、広いモデルで示した**下界**はそのまま KSS に移るが、**上界**は自動では移らない。
このファイルはその差を埋める（鎖についての `SpookyPebbling/KSSModel.lean` と同じ読み替え）。

* `ValidK`: 妥当な手順で、しかも `ghost` を子が揃っていないときにしか打たないもの（= KSS の意味論の手順。
  KSS の place は「空なら pebble・ゴーストなら unghost」、remove は「子が揃っていれば unpebble・そうでなければ ghost」に当たる）。
* `validK_of_valid`: 妥当な手順は、**手数もペブル数も変えずに** `ValidK` の手順に直せる。
  読み替え: 子が揃っているときの `ghost v` を `unpebble v` に、その結果ゴーストが無くなった頂点への `unghost v` を `pebble v` に。
  不変条件は「ペブルの位置は一致・新しい側のゴーストは元の側でもゴースト」。
* `time_theta_kss`: 上界と下界を `ValidK` について並べた形。

注意: KSS の定義の字面（集合の列 `P_i` とゴースト列 `G_i`）そのものは形式化していない。`ValidK` は 4 操作への符号化である。
-/
import SpookyTree.UpperFinal

namespace SpookyTree

instance (h : ℕ) (c : Config) (v : Node) : Decidable (Ready h c v) := by
  unfold Ready; infer_instance

/-- **KSS の意味論の手順.** 妥当で、`ghost` は子が揃っていないときにしか打たない。 -/
structure ValidK (h cap T : ℕ) (ms : ℕ → Move) : Prop where
  valid : Valid h cap T ms
  derived : ∀ t < T, (ms t).op = .ghost → ¬ Ready h (st ms t) (ms t).v

/-- 読み替え: 子が揃っているときの `ghost` は `unpebble` に、ゴーストでない頂点への `unghost` は `pebble` に。 -/
def tweakK (h : ℕ) (c : Config) (m : Move) : Move :=
  match m.op with
  | .ghost => if Ready h c m.v then ⟨.unpebble, m.v⟩ else m
  | .unghost => if c m.v = .ghost then m else ⟨.pebble, m.v⟩
  | _ => m

/-- 読み替えた手順の配置。 -/
def stK (h : ℕ) (ms : ℕ → Move) : ℕ → Config
  | 0 => fun _ => .empty
  | t + 1 => step (stK h ms t) (tweakK h (stK h ms t) (ms t))

/-- 読み替えた手順。 -/
def msK (h : ℕ) (ms : ℕ → Move) : ℕ → Move := fun t => tweakK h (stK h ms t) (ms t)

theorem st_msK (h : ℕ) (ms : ℕ → Move) : ∀ t, st (msK h ms) t = stK h ms t := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
    show step (st (msK h ms) t) (msK h ms t) = step (stK h ms t) (tweakK h (stK h ms t) (ms t))
    rw [ih]
    rfl

/-- ペブルの位置は一致し、新しい側（`c'`）のゴーストは元の側（`c`）でもゴースト。 -/
def Dom (c c' : Config) : Prop :=
  ∀ v, (c v = .pebble ↔ c' v = .pebble) ∧ (c' v = .ghost → c v = .ghost)

theorem Dom.ready {h : ℕ} {c c' : Config} (hD : Dom c c') (v : Node) :
    Ready h c v ↔ Ready h c' v := by
  unfold Ready
  rw [(hD (v ++ [false])).1, (hD (v ++ [true])).1]

theorem Dom.pcount_eq {h : ℕ} {c c' : Config} (hD : Dom c c') : pcount h c = pcount h c' := by
  unfold pcount
  congr 1
  ext l
  simp only [Finset.mem_filter]
  rw [(hD l).1]

theorem dom_update {c c' : Config} (hD : Dom c c') (v : Node) {x x' : Cell}
    (h1 : x = .pebble ↔ x' = .pebble) (h2 : x' = .ghost → x = .ghost) :
    Dom (Function.update c v x) (Function.update c' v x') := by
  intro w
  by_cases hw : w = v
  · subst hw
    simpa using ⟨h1, h2⟩
  · simpa [Function.update, hw] using hD w

/-- **1 手の読み替え.** 元の手が合法なら、読み替えた手も合法で、`ghost` なら子は揃っておらず、不変条件は保たれる。 -/
theorem dom_step {h : ℕ} {c c' : Config} {m : Move} (hD : Dom c c') (hL : Legal h c m) :
    Legal h c' (tweakK h c' m) ∧
    ((tweakK h c' m).op = .ghost → ¬ Ready h c' (tweakK h c' m).v) ∧
    Dom (step c m) (step c' (tweakK h c' m)) := by
  obtain ⟨op, v⟩ := m
  obtain ⟨hv, hop⟩ := hL
  have hnp : c v ≠ .pebble → c' v ≠ .pebble := fun hne hp => hne ((hD v).1.mpr hp)
  cases op with
  | pebble =>
    obtain ⟨hc, hr⟩ : c v = .empty ∧ Ready h c v := hop
    have hc' : c' v = .empty := by
      cases hx : c' v with
      | empty => rfl
      | pebble => exact absurd hx (hnp (by rw [hc]; decide))
      | ghost => have := (hD v).2 hx; rw [hc] at this; exact absurd this (by decide)
    refine ⟨And.intro hv (And.intro hc' ((hD.ready v).mp hr)), fun hg => by simp [tweakK] at hg, ?_⟩
    exact dom_update hD v Iff.rfl id
  | unpebble =>
    obtain ⟨hc, hr⟩ : c v = .pebble ∧ Ready h c v := hop
    have hc' : c' v = .pebble := (hD v).1.mp hc
    refine ⟨And.intro hv (And.intro hc' ((hD.ready v).mp hr)), fun hg => by simp [tweakK] at hg, ?_⟩
    exact dom_update hD v Iff.rfl id
  | ghost =>
    have hc : c v = .pebble := hop
    have hc' : c' v = .pebble := (hD v).1.mp hc
    by_cases hr : Ready h c' v
    · have ht : tweakK h c' ⟨.ghost, v⟩ = ⟨.unpebble, v⟩ := by simp [tweakK, hr]
      rw [ht]
      refine ⟨And.intro hv (And.intro hc' hr), fun hg => by simp at hg, ?_⟩
      exact dom_update hD v (x := .ghost) (x' := .empty) (by decide) (fun hx => absurd hx (by decide))
    · have ht : tweakK h c' ⟨.ghost, v⟩ = ⟨.ghost, v⟩ := by simp [tweakK, hr]
      rw [ht]
      refine ⟨And.intro hv hc', fun _ => hr, ?_⟩
      exact dom_update hD v Iff.rfl id
  | unghost =>
    obtain ⟨hc, hr⟩ : c v = .ghost ∧ Ready h c v := hop
    have hr' : Ready h c' v := (hD.ready v).mp hr
    by_cases hg : c' v = .ghost
    · have ht : tweakK h c' ⟨.unghost, v⟩ = ⟨.unghost, v⟩ := by simp [tweakK, hg]
      rw [ht]
      refine ⟨And.intro hv (And.intro hg hr'), fun hgo => by simp at hgo, ?_⟩
      exact dom_update hD v Iff.rfl id
    · have ht : tweakK h c' ⟨.unghost, v⟩ = ⟨.pebble, v⟩ := by simp [tweakK, hg]
      rw [ht]
      have hc' : c' v = .empty := by
        cases hx : c' v with
        | empty => rfl
        | pebble => exact absurd hx (hnp (by rw [hc]; decide))
        | ghost => exact absurd hx hg
      refine ⟨And.intro hv (And.intro hc' hr'), fun hgo => by simp at hgo, ?_⟩
      exact dom_update hD v (x := .pebble) (x' := .pebble) Iff.rfl (fun hx => absurd hx (by decide))

/-- **妥当な手順は、手数もペブル数も変えずに KSS の意味論の手順に直せる。** -/
theorem validK_of_valid {h cap T : ℕ} {ms : ℕ → Move} (hV : Valid h cap T ms) :
    ValidK h cap T (msK h ms) := by
  have hD : ∀ t ≤ T, Dom (st ms t) (stK h ms t) := by
    intro t
    induction t with
    | zero => intro _ v; simp [st, stK]
    | succ t ih =>
      intro ht
      exact (dom_step (ih (by omega)) (hV.legal t (by omega))).2.2
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro t ht
    rw [st_msK]
    exact (dom_step (hD t (by omega)) (hV.legal t ht)).1
  · intro t ht
    rw [st_msK, ← (hD t ht).pcount_eq]
    exact hV.cap_le t ht
  · rw [st_msK]
    exact ((hD T le_rfl) []).1.mp hV.root
  · intro l hl hne
    rw [st_msK]
    have hc := hV.others l hl hne
    obtain ⟨h1, h2⟩ := hD T le_rfl l
    cases hx : stK h ms T l with
    | empty => rfl
    | pebble => have := h1.mpr hx; rw [hc] at this; exact absurd this (by decide)
    | ghost => have := h2 hx; rw [hc] at this; exact absurd this (by decide)
  · intro t ht hop
    rw [st_msK]
    exact (dom_step (hD t (by omega)) (hV.legal t ht)).2.1 hop

/-- **上界（KSS の意味論、パラメータつき）.** -/
theorem time_upper_bound_kss {h Λ : ℕ} (hΛ : 1 ≤ Λ) (hcap : 2 ^ (Λ + 1) ≤ h + 1) :
    ∃ (T : ℕ) (ms : ℕ → Move), ValidK h (h + 1) T ms ∧
      T + 3 ≤ 2 * (2 ^ Λ + (h - 1) / Λ + 1) * 2 ^ h := by
  obtain ⟨T, ms, hV, hT⟩ := time_upper_bound hΛ hcap
  exact ⟨T, msK h ms, validK_of_valid hV, hT⟩

/-- **上界（KSS の意味論、`log` の形）.** -/
theorem time_upper_bound_log_kss {h : ℕ} (hh : 4 ≤ h) :
    ∃ (T : ℕ) (ms : ℕ → Move), ValidK h (h + 1) T ms ∧
      Nat.log 2 h * (T + 3) ≤ 2 * (4 * h + Nat.log 2 h) * 2 ^ h := by
  obtain ⟨T, ms, hV, hT⟩ := time_upper_bound_log hh
  exact ⟨T, msK h ms, validK_of_valid hV, hT⟩

/-- **KSS の意味論での手数の増大度.** 完全二分木 `T_h`（`h ≥ 4`）をペブル `h + 1` 個で解く KSS の意味論の手順について、
手数 `T` が `⌊log₂ h⌋ · (T + 3) ≤ 2 (4h + ⌊log₂ h⌋) · 2^h` のものがあり、
どの手順も `T + 1 ≥ 2 (2^h − 1) + (⌊(h−1)/(2⌊log₂ h⌋+3)⌋ − 2) · 2^h`。 -/
theorem time_theta_kss {h : ℕ} (hh : 4 ≤ h) :
    (∃ (T : ℕ) (ms : ℕ → Move), ValidK h (h + 1) T ms ∧
      Nat.log 2 h * (T + 3) ≤ 2 * (4 * h + Nat.log 2 h) * 2 ^ h) ∧
    (∀ (T : ℕ) (ms : ℕ → Move), ValidK h (h + 1) T ms →
      2 * ((2 : ℝ) ^ h - 1) + ((((h - 1) / (2 * Nat.log 2 h + 3) : ℕ) : ℝ) - 2) * 2 ^ h ≤ T + 1) :=
  ⟨time_upper_bound_log_kss hh, fun _ _ hV => time_lower_bound_log hV.valid (by omega)⟩

end SpookyTree
