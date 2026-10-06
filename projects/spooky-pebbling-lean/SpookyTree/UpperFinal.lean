/-
# 上界: 最小ペブル数 `h + 1` での手数は `O(2^h · h / log h)`

手順（`strategy h Λ`）:
1. 木全体を計算する（根だけペブル、他は全部ゴースト）。ペブルは `h + 1` 個以下。
2. 根の左の子・右の子をそれぞれブロック根として `block` で空にする。根はペブルのまま。

`block` は `Λ` 段ごと（浅いところは 1 段ごと）に部分木を計算し直すので、
置く手は 1 頂点あたり「上にあるブロック根の数」`≤ 2^Λ + (h − 1)/Λ + 1` 回で済む。

* `time_upper_bound`: `1 ≤ Λ`、`2^(Λ+1) ≤ h + 1` なら、手数 `T` が
  `T + 3 ≤ 2 (2^Λ + ⌊(h−1)/Λ⌋ + 1) · 2^h` を満たす妥当な手順がある。
* `time_upper_bound_log`: `Λ = ⌊log₂ h⌋ − ⌊log₂ ⌊log₂ h⌋⌋` と取ると、`h ≥ 4` で
  `⌊log₂ h⌋ · (T + 3) ≤ 2 (4h + ⌊log₂ h⌋) · 2^h`、すなわち `T = O(2^h · h / log h) = O(n log n / log log n)`。
* `time_theta`: 既存の下界 `time_lower_bound_log` と並べた形。

モデルは下界と同じ `Valid`（`ghost` が無条件の広いモデル）。この手順は `ghost` を子が揃っている頂点にも打つので、
KSS の意味論（ゴーストは導出）での合法性は、この定理からは直接には出ない
（KSS の意味論で合法な版は `notes/spooky-pebbling/tree-gap/blockgen.py` の手順で、再生で検査している）。
-/
import SpookyTree.UpperBlock
import SpookyTree.Final

namespace SpookyTree

/-! ## リストの手順から `Valid` へ -/

/-- 各時刻の合法性と、各手の直後のペブル数（リストの添字で）。 -/
theorem Runs.nth {h k : ℕ} {y : Node} {p : ℕ} :
    ∀ {l : List Move} {c : Config}, Runs h k y p c l → ∀ (t : ℕ) (ht : t < l.length),
      Legal h (run c (l.take t)) l[t] ∧ pc k y (run c (l.take (t + 1))) ≤ p := by
  intro l
  induction l with
  | nil => intro c _ t ht; simp at ht
  | cons m l ih =>
    intro c hR t ht
    obtain ⟨h1, -, h3, h4⟩ := Runs_cons.mp hR
    cases t with
    | zero => exact ⟨by simpa using h1, by simpa using h3⟩
    | succ t =>
      have := ih h4 t (by simpa using ht)
      simpa using this

/-- リストを無限列に延ばす（範囲外は何でもよい）。 -/
def seqOf (l : List Move) : ℕ → Move := fun i => l.getD i default

theorem seqOf_lt {l : List Move} {t : ℕ} (ht : t < l.length) : seqOf l t = l[t] := by
  simp [seqOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]

theorem st_seqOf (l : List Move) :
    ∀ t, t ≤ l.length → st (seqOf l) t = run (fun _ => Cell.empty) (l.take t) := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro ht
    have hlt : t < l.length := by omega
    rw [st, ih (by omega), seqOf_lt hlt, List.take_succ_eq_append_getElem hlt, run_append]
    rfl

theorem valid_of_runs {h cap : ℕ} {l : List Move}
    (hR : Runs h h [] cap (fun _ => Cell.empty) l)
    (hroot : run (fun _ => Cell.empty) l [] = .pebble)
    (hothers : ∀ z : Node, z.length < h → z ≠ [] → run (fun _ => Cell.empty) l z = .empty) :
    Valid h cap l.length (seqOf l) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t ht
    rw [st_seqOf l t (by omega), seqOf_lt ht]
    exact (hR.nth t ht).1
  · intro t ht
    cases t with
    | zero => simp [st, pcount]
    | succ t =>
      rw [st_seqOf l (t + 1) ht, ← pc_root]
      exact (hR.nth t (by omega)).2
  · rw [st_seqOf l l.length le_rfl, List.take_length]; exact hroot
  · intro z hz hne
    rw [st_seqOf l l.length le_rfl, List.take_length]; exact hothers z hz hne

/-! ## 手順全体 -/

/-- 木全体を計算し、根の 2 つの子をブロック根として空にする。 -/
def strategy (h Λ : ℕ) : List Move :=
  compute .pebble h [] ++ block h Λ (h - 1) (h - 1) [false] ++ block h Λ (h - 1) (h - 1) [true]

theorem strategy_spec {h Λ : ℕ} (hΛ : 1 ≤ Λ) (hcap : 2 ^ (Λ + 1) ≤ h + 1) :
    Runs h h [] (h + 1) (fun _ => Cell.empty) (strategy h Λ) ∧
    run (fun _ => Cell.empty) (strategy h Λ) [] = .pebble ∧
    ∀ z : Node, z.length < h → z ≠ [] → run (fun _ => Cell.empty) (strategy h Λ) z = .empty := by
  have h4 : 4 ≤ 2 ^ (Λ + 1) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (Λ + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 := ⟨h - 1, by omega⟩
  have hstrat : strategy (k + 1) Λ =
      compute .pebble (k + 1) [] ++ block (k + 1) Λ k k [false] ++ block (k + 1) Λ k k [true] := by
    simp [strategy]
  rw [hstrat]
  -- 1. 木全体を計算する
  obtain ⟨hR1, hQ1⟩ := compute_spec (h := k + 1) (pl := .pebble) (X := .empty)
    (Or.inl ⟨rfl, rfl⟩) (k + 1) [] (fun _ => Cell.empty) (by omega) (by simp) (fun w _ => rfl)
  obtain ⟨hroot1, hG0, hG1⟩ := Pat_succ.mp hQ1
  rw [scp_zero] at hroot1
  rw [scp_shift] at hG0 hG1
  simp only [List.nil_append] at hG0 hG1
  -- 2. 左の子のブロック
  obtain ⟨hR2, hQ2⟩ := block_spec hΛ hcap k k [false] _ le_rfl (by omega) (by simp; omega) (by simp) hG0
  have hU2 := hR2.under
  have hL2 := Runs.lift0 (y := []) (q := 1) hR2 (by
    simp only [List.nil_append]
    rw [hroot1, pc_of_Pat _ _ _ hG1, pcPat_cst (X := .ghost) (by decide)]
    simp)
  have hroot2 := (run_outside hU2 _ (not_prefix_parent [] false)).trans hroot1
  have hG1' := (Pat_run_disj hU2 (disj01 [])).mpr hG1
  -- 3. 右の子のブロック
  obtain ⟨hR3, hQ3⟩ := block_spec hΛ hcap k k [true] _ le_rfl (by omega) (by simp; omega) (by simp) hG1'
  have hU3 := hR3.under
  have hL3 := Runs.lift1 (y := []) (q := 1) hR3 (by
    simp only [List.nil_append]
    rw [hroot2, pc_of_Pat _ _ _ hQ2, pcPat_cst (X := .empty) (by decide)]
    simp)
  have hroot3 := (run_outside hU3 _ (not_prefix_parent [] true)).trans hroot2
  have hE0 := (Pat_run_disj hU3 (disj10 [])).mpr hQ2
  refine ⟨?_, ?_, ?_⟩
  · simp only [Runs_append, run_append]
    exact ⟨⟨hR1, hL2⟩, hL3⟩
  · simp only [run_append]
    exact hroot3
  · intro z hz hne
    simp only [run_append]
    match z, hz, hne with
    | [], _, hne => exact absurd rfl hne
    | false :: w, hz, _ => exact hE0 w (by simpa using hz)
    | true :: w, hz, _ => exact hQ3 w (by simpa using hz)

/-- **上界（パラメータつき）.** `1 ≤ Λ`、`2^(Λ+1) ≤ h + 1` なら、完全二分木 `T_h` をペブル `h + 1` 個で解く
妥当な手順で、手数 `T` が `T + 3 ≤ 2 (2^Λ + ⌊(h−1)/Λ⌋ + 1) · 2^h` を満たすものがある。 -/
theorem time_upper_bound {h Λ : ℕ} (hΛ : 1 ≤ Λ) (hcap : 2 ^ (Λ + 1) ≤ h + 1) :
    ∃ (T : ℕ) (ms : ℕ → Move), Valid h (h + 1) T ms ∧
      T + 3 ≤ 2 * (2 ^ Λ + (h - 1) / Λ + 1) * 2 ^ h := by
  obtain ⟨hR, hroot, hothers⟩ := strategy_spec hΛ hcap
  refine ⟨(strategy h Λ).length, seqOf (strategy h Λ), valid_of_runs hR hroot hothers, ?_⟩
  have h4 : 4 ≤ 2 ^ (Λ + 1) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (Λ + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 := ⟨h - 1, by omega⟩
  have hlen : (strategy (k + 1) Λ).length = (compute .pebble (k + 1) []).length +
      (block (k + 1) Λ k k [false]).length + (block (k + 1) Λ k k [true]).length := by
    simp [strategy, Nat.add_assoc]
  have e1 : (compute .pebble (k + 1) []).length + 3 = 2 ^ (k + 1 + 1) :=
    length_compute .pebble (k + 1) [] (by omega)
  have e2 := length_block_le (h := k + 1) hΛ k k [false]
  have e3 := length_block_le (h := k + 1) hΛ k k [true]
  have e4 := nb_le (h := k + 1) hΛ k k (by omega)
  have e5 : k + 1 - k = 1 := by omega
  have e6 : 1 ≤ 2 ^ Λ := Nat.one_le_two_pow
  have e7 : nb (k + 1) Λ k k ≤ 2 ^ Λ + k / Λ := by rw [e5] at e4; omega
  have e8 : nb (k + 1) Λ k k * 2 ^ k ≤ (2 ^ Λ + k / Λ) * 2 ^ k := Nat.mul_le_mul_right _ e7
  have e9 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  have e10 : 2 ^ (k + 1 + 1) = 4 * 2 ^ k := by rw [pow_succ, pow_succ]; ring
  rw [hlen, Nat.add_sub_cancel, e9]
  rw [e10] at e1
  nlinarith [e1, e2, e3, e8]

/-! ## `log` の形 -/

theorem two_mul_le_two_pow (n : ℕ) : 2 * n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have h2 : 2 ≤ 2 ^ n := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      rw [pow_succ]
      omega

/-- **上界（`log` の形）.** `h ≥ 4` なら、ペブル `h + 1` 個の妥当な手順で、手数 `T` が
`⌊log₂ h⌋ · (T + 3) ≤ 2 (4h + ⌊log₂ h⌋) · 2^h` を満たすものがある。
すなわち `T ≤ (8h/⌊log₂ h⌋ + 2) · 2^h = O(n log n / log log n)`。 -/
theorem time_upper_bound_log {h : ℕ} (hh : 4 ≤ h) :
    ∃ (T : ℕ) (ms : ℕ → Move), Valid h (h + 1) T ms ∧
      Nat.log 2 h * (T + 3) ≤ 2 * (4 * h + Nat.log 2 h) * 2 ^ h := by
  obtain ⟨lg, hlg⟩ : ∃ lg, lg = Nat.log 2 h := ⟨_, rfl⟩
  obtain ⟨ll, hll⟩ : ∃ ll, ll = Nat.log 2 lg := ⟨_, rfl⟩
  rw [← hlg]
  have hpow_lg : 2 ^ lg ≤ h := by rw [hlg]; exact Nat.pow_log_le_self 2 (by omega)
  have hlg2 : 2 ≤ lg := by
    rw [hlg]; exact (Nat.le_log_iff_pow_le (by norm_num) (by omega)).mpr (by omega)
  have hpow_ll : 2 ^ ll ≤ lg := by rw [hll]; exact Nat.pow_log_le_self 2 (by omega)
  have hll1 : 1 ≤ ll := by
    rw [hll]; exact (Nat.le_log_iff_pow_le (by norm_num) (by omega)).mpr (by omega)
  have hlt_ll : lg < 2 ^ (ll + 1) := by
    rw [hll]; exact Nat.lt_pow_succ_log_self (by norm_num) lg
  have h2ll : 2 * ll ≤ lg := le_trans (two_mul_le_two_pow ll) hpow_ll
  obtain ⟨Λ, hΛdef⟩ : ∃ Λ, lg = Λ + ll := ⟨lg - ll, by omega⟩
  have hΛ1 : 1 ≤ Λ := by omega
  have hΛlg : lg ≤ 2 * Λ := by omega
  have hcap : 2 ^ (Λ + 1) ≤ h + 1 := by
    have : 2 ^ (Λ + 1) ≤ 2 ^ lg := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨T, ms, hV, hT⟩ := time_upper_bound hΛ1 hcap
  refine ⟨T, ms, hV, ?_⟩
  have hA : 2 ^ Λ * lg ≤ 2 * h := by
    have h1 : 2 ^ Λ * 2 ^ ll = 2 ^ lg := by rw [hΛdef, pow_add]
    have h2 : 2 ^ (ll + 1) = 2 * 2 ^ ll := by rw [pow_succ]; ring
    calc 2 ^ Λ * lg ≤ 2 ^ Λ * (2 * 2 ^ ll) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 * (2 ^ Λ * 2 ^ ll) := by ring
      _ = 2 * 2 ^ lg := by rw [h1]
      _ ≤ 2 * h := by omega
  have hB : (h - 1) / Λ * lg ≤ 2 * h := by
    calc (h - 1) / Λ * lg ≤ (h - 1) / Λ * (2 * Λ) := Nat.mul_le_mul_left _ hΛlg
      _ = 2 * ((h - 1) / Λ * Λ) := by ring
      _ ≤ 2 * (h - 1) := Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _)
      _ ≤ 2 * h := by omega
  calc lg * (T + 3) ≤ lg * (2 * (2 ^ Λ + (h - 1) / Λ + 1) * 2 ^ h) := Nat.mul_le_mul_left _ hT
    _ = 2 * (2 ^ Λ * lg + (h - 1) / Λ * lg + lg) * 2 ^ h := by ring
    _ ≤ 2 * (2 * h + 2 * h + lg) * 2 ^ h := by gcongr
    _ = 2 * (4 * h + lg) * 2 ^ h := by ring

/-- **最小ペブル数での手数の増大度.** `h ≥ 4` のとき、上界（構成）と下界（`time_lower_bound_log`）を並べる:
手数 `T` が `⌊log₂ h⌋ · (T + 3) ≤ 2 (4h + ⌊log₂ h⌋) · 2^h` の妥当な手順があり、
どの妥当な手順も `T + 1 ≥ 2 (2^h − 1) + (⌊(h−1)/(2⌊log₂ h⌋+3)⌋ − 2) · 2^h`。
`n = 2^h − 1` で書けば `T(T_h, h+1) = Θ(n log n / log log n)`。 -/
theorem time_theta {h : ℕ} (hh : 4 ≤ h) :
    (∃ (T : ℕ) (ms : ℕ → Move), Valid h (h + 1) T ms ∧
      Nat.log 2 h * (T + 3) ≤ 2 * (4 * h + Nat.log 2 h) * 2 ^ h) ∧
    (∀ (T : ℕ) (ms : ℕ → Move), Valid h (h + 1) T ms →
      2 * ((2 : ℝ) ^ h - 1) + ((((h - 1) / (2 * Nat.log 2 h + 3) : ℕ) : ℝ) - 2) * 2 ^ h ≤ T + 1) :=
  ⟨time_upper_bound_log hh, fun _ _ hV => time_lower_bound_log hV (by omega)⟩

end SpookyTree
