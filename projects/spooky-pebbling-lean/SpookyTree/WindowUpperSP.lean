/-
# 窓の上界の準備: 割った前線（大きさが 2 の冪でない前線）

紙 `notes/spooky-pebbling/tree-gap/WINDOW_UB_2026-11.md` の構成 B★ は、大きさ `f`（2 の冪とは限らない）の
前線を使う。紙は「深さ `e` の右の `u` 個を割る」形だが、ここでは同じ大きさで扱いやすい形として、
`n` 個の前線を左右の子に `⌈n/2⌉`・`⌊n/2⌋` 個ずつ再帰的に割る（`n ≤ 1` ならその頂点が前線）。

* `SP G k A n y c`: 高さ `k` の `T(y)` で、`n` 個の割った前線について、内部の深さ `i` の頂点は `A i`、
  前線の各頂点の部分木は `Pat G`（層状）。
* `Shp lo hi k n`: 形が作れて（`1 ≤ n ≤ 2^D`、`D + lo ≤ k`）、前線の部分木の高さが `[lo, hi]` に入る
  （`2^d ≤ n`、`k ≤ hi + d`）。
* `onSp f`: 前線の各頂点に左から `f` を打つ。`plSp`: 内部を後順に全部置く。`rmSp`: 内部を前順に全部外す。
* `pair_spec`: 左右の子の部分木の中の実行をつなぐ道具（`UpperProg` の各仕様の帰納段の共通部分）。
-/
import SpookyTree.UpperProg

namespace SpookyTree

/-! ## 割った前線の上の配置 -/

/-- 割った前線の上の配置。内部の深さ `i` の頂点は `A i`、前線の部分木は `Pat G`。 -/
def SP (G : ℕ → Cell) : ℕ → (ℕ → Cell) → ℕ → Node → Config → Prop
  | 0, _, _, _, _ => True
  | k + 1, A, n, y, c => if n ≤ 1 then Pat G (k + 1) y c else
      c y = A 0 ∧ SP G k (fun i => A (i + 1)) ((n + 1) / 2) (y ++ [false]) c ∧
        SP G k (fun i => A (i + 1)) (n / 2) (y ++ [true]) c

/-- `SP` の形のペブル数。 -/
def pcSP (G : ℕ → Cell) : ℕ → (ℕ → Cell) → ℕ → ℕ
  | 0, _, _ => 0
  | k + 1, A, n => if n ≤ 1 then pcPat G (k + 1) else
      (if A 0 = .pebble then 1 else 0) + pcSP G k (fun i => A (i + 1)) ((n + 1) / 2) +
        pcSP G k (fun i => A (i + 1)) (n / 2)

theorem SP_front {G A : ℕ → Cell} {k n : ℕ} {y : Node} {c : Config} (hn : n ≤ 1) :
    SP G (k + 1) A n y c ↔ Pat G (k + 1) y c := by
  rw [SP, if_pos hn]

theorem SP_int {G A : ℕ → Cell} {k n : ℕ} {y : Node} {c : Config} (hn : ¬ n ≤ 1) :
    SP G (k + 1) A n y c ↔ c y = A 0 ∧ SP G k (fun i => A (i + 1)) ((n + 1) / 2) (y ++ [false]) c ∧
        SP G k (fun i => A (i + 1)) (n / 2) (y ++ [true]) c := by
  rw [SP, if_neg hn]

/-- 前線が 1 個（`n ≤ 1`）なら、内部の状態 `A` は見えない。 -/
theorem SP_front_A {G A A' : ℕ → Cell} {k n : ℕ} {y : Node} {c : Config} (hn : n ≤ 1) :
    SP G k A n y c ↔ SP G k A' n y c := by
  cases k with
  | zero => simp [SP]
  | succ k => rw [SP_front hn, SP_front hn]

theorem pc_of_SP {G : ℕ → Cell} {c : Config} :
    ∀ (k : ℕ) (A : ℕ → Cell) (n : ℕ) (y : Node), SP G k A n y c → pc k y c = pcSP G k A n := by
  intro k
  induction k with
  | zero => intro A n y _; rfl
  | succ k ih =>
    intro A n y hS
    by_cases hn : n ≤ 1
    · rw [SP_front hn] at hS
      rw [pcSP, if_pos hn]
      exact pc_of_Pat _ _ _ hS
    · rw [SP_int hn] at hS
      obtain ⟨h0, h1, h2⟩ := hS
      rw [pcSP, if_neg hn, pc, h0, ih _ _ _ h1, ih _ _ _ h2]

theorem SP_congr {G : ℕ → Cell} {c c' : Config} :
    ∀ (k : ℕ) (A : ℕ → Cell) (n : ℕ) (y : Node), (∀ w : Node, c' (y ++ w) = c (y ++ w)) →
      (SP G k A n y c' ↔ SP G k A n y c) := by
  intro k
  induction k with
  | zero => intro A n y _; simp [SP]
  | succ k ih =>
    intro A n y hw
    by_cases hn : n ≤ 1
    · rw [SP_front hn, SP_front hn]; exact Pat_congr hw
    · rw [SP_int hn, SP_int hn]
      have h0 : c' y = c y := by simpa using hw []
      have hb : ∀ b : Bool, ∀ w : Node, c' ((y ++ [b]) ++ w) = c ((y ++ [b]) ++ w) := fun b w => by
        simpa using hw (b :: w)
      rw [h0, ih _ _ _ (hb false), ih _ _ _ (hb true)]

theorem SP_run_disj {z y : Node} {l : List Move} (hl : ∀ m ∈ l, z <+: m.v)
    (hd : ∀ w : Node, ¬ z <+: y ++ w) {G A : ℕ → Cell} {k n : ℕ} {c : Config} :
    SP G k A n y (run c l) ↔ SP G k A n y c :=
  SP_congr k A n y (fun w => run_outside hl c (hd w))

theorem SP_step_out {y v : Node} (hv : ¬ y <+: v) {G A : ℕ → Cell} {k n : ℕ} {c : Config}
    (op : Op) : SP G k A n y (step c ⟨op, v⟩) ↔ SP G k A n y c :=
  SP_congr k A n y (fun w => step_ne c op (fun e => hv (e ▸ List.prefix_append y w)))

theorem SP_top {G A : ℕ → Cell} {k n : ℕ} {y : Node} {c : Config} (hS : SP G (k + 1) A n y c) :
    c y = if n ≤ 1 then G 0 else A 0 := by
  by_cases hn : n ≤ 1
  · rw [SP_front hn] at hS; rw [if_pos hn]; simpa using hS [] (by simp)
  · rw [SP_int hn] at hS; rw [if_neg hn]; exact hS.1

theorem SP_top_peb {G A : ℕ → Cell} {k n : ℕ} {y : Node} {c : Config} (hk : 1 ≤ k)
    (hS : SP G k A n y c) (hG : G 0 = .pebble) (hA : A 0 = .pebble) : c y = .pebble := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [SP_top hS]; split_ifs <;> assumption

/-- 全部同じ状態なら、割った前線の形でも層状でも同じ。 -/
theorem SP_cst {X : Cell} {c : Config} :
    ∀ (k n : ℕ) (y : Node), SP (cst X) k (cst X) n y c ↔ Pat (cst X) k y c := by
  intro k
  induction k with
  | zero => intro n y; simp [SP, Pat]
  | succ k ih =>
    intro n y
    by_cases hn : n ≤ 1
    · exact SP_front hn
    · rw [SP_int hn, cst_shift, ih, ih, Pat_succ, cst_shift, cst_apply]

/-! ## 形の条件 -/

/-- 形が作れて、前線の部分木の高さが `[lo, hi]` に入る。 -/
def Shp (lo hi k n : ℕ) : Prop :=
  ∃ D d : ℕ, 1 ≤ n ∧ n ≤ 2 ^ D ∧ D + lo ≤ k ∧ 2 ^ d ≤ n ∧ k ≤ hi + d

theorem Shp.front {lo hi k n : ℕ} (hS : Shp lo hi k n) (hn : n ≤ 1) :
    n = 1 ∧ lo ≤ k ∧ k ≤ hi := by
  obtain ⟨D, d, h1, h2, h3, h4, h5⟩ := hS
  cases d with
  | zero => exact ⟨by omega, by omega, by omega⟩
  | succ d =>
    have : 2 ≤ 2 ^ (d + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (d + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

theorem Shp.child {lo hi k n : ℕ} (hS : Shp lo hi (k + 1) n) (hn : ¬ n ≤ 1) :
    Shp lo hi k ((n + 1) / 2) ∧ Shp lo hi k (n / 2) := by
  obtain ⟨D, d, h1, h2, h3, h4, h5⟩ := hS
  cases D with
  | zero => rw [pow_zero] at h2; omega
  | succ D' =>
    rw [pow_succ] at h2
    cases d with
    | zero =>
      rw [pow_zero] at h4
      exact ⟨⟨D', 0, by omega, by omega, by omega, by rw [pow_zero]; omega, by omega⟩,
        ⟨D', 0, by omega, by omega, by omega, by rw [pow_zero]; omega, by omega⟩⟩
    | succ d' =>
      rw [pow_succ] at h4
      exact ⟨⟨D', d', by omega, by omega, by omega, by omega, by omega⟩,
        ⟨D', d', by omega, by omega, by omega, by omega, by omega⟩⟩

theorem Shp.pos {lo hi k n : ℕ} (hS : Shp lo hi k n) (hlo : 1 ≤ lo) : 1 ≤ k := by
  obtain ⟨D, d, h1, h2, h3, h4, h5⟩ := hS
  omega

theorem Shp.one {lo hi k n : ℕ} (hS : Shp lo hi k n) : 1 ≤ n := by
  obtain ⟨D, d, h1, -⟩ := hS
  exact h1

theorem half_sum (n : ℕ) : (n + 1) / 2 + n / 2 = n := by omega

/-! ## ペブル数の上界 -/

theorem pcSP_le_peb {G : ℕ → Cell} :
    ∀ (k : ℕ) (A : ℕ → Cell) (n : ℕ), pcSP G k A n ≤ pcSP G k (cst .pebble) n := by
  intro k
  induction k with
  | zero => intro A n; simp [pcSP]
  | succ k ih =>
    intro A n
    by_cases hn : n ≤ 1
    · rw [pcSP, pcSP, if_pos hn, if_pos hn]
    · rw [pcSP, pcSP, if_neg hn, if_neg hn, cst_shift, cst_apply, if_pos rfl]
      have h1 := ih (fun i => A (i + 1)) ((n + 1) / 2)
      have h2 := ih (fun i => A (i + 1)) (n / 2)
      split_ifs <;> omega

theorem pcSP_cst_le {G : ℕ → Cell} {lo hi w : ℕ} {X : Cell} (hX : X ≠ .pebble)
    (hG : ∀ j, lo ≤ j → j ≤ hi → pcPat G j ≤ w) :
    ∀ (k n : ℕ), Shp lo hi k n → pcSP G k (cst X) n ≤ n * w := by
  intro k
  induction k with
  | zero => intro n _; simp [pcSP]
  | succ k ih =>
    intro n hS
    by_cases hn : n ≤ 1
    · obtain ⟨h1, h2, h3⟩ := hS.front hn
      rw [pcSP, if_pos hn, h1, one_mul]; exact hG _ h2 h3
    · obtain ⟨hL, hR⟩ := hS.child hn
      rw [pcSP, if_neg hn, cst_shift, cst_apply, if_neg hX]
      have a := ih _ hL
      have b := ih _ hR
      have hs := half_sum n
      calc 0 + pcSP G k (cst X) ((n + 1) / 2) + pcSP G k (cst X) (n / 2)
          ≤ (n + 1) / 2 * w + n / 2 * w := by omega
        _ = n * w := by rw [← add_mul, hs]

theorem pcSP_peb_le {G : ℕ → Cell} {lo hi w : ℕ}
    (hG : ∀ j, lo ≤ j → j ≤ hi → pcPat G j ≤ w) :
    ∀ (k n : ℕ), Shp lo hi k n → pcSP G k (cst .pebble) n + 1 ≤ n * (w + 1) := by
  intro k
  induction k with
  | zero => intro n hS; have := hS.one; simp [pcSP]; nlinarith
  | succ k ih =>
    intro n hS
    by_cases hn : n ≤ 1
    · obtain ⟨h1, h2, h3⟩ := hS.front hn
      rw [pcSP, if_pos hn, h1, one_mul]; have := hG _ h2 h3; omega
    · obtain ⟨hL, hR⟩ := hS.child hn
      rw [pcSP, if_neg hn, cst_shift, cst_apply, if_pos rfl]
      have a := ih _ hL
      have b := ih _ hR
      have hs := half_sum n
      calc 1 + pcSP G k (cst .pebble) ((n + 1) / 2) + pcSP G k (cst .pebble) (n / 2) + 1
          ≤ (n + 1) / 2 * (w + 1) + n / 2 * (w + 1) := by omega
        _ = n * (w + 1) := by rw [← add_mul, hs]

theorem pcSP_scp_le {G : ℕ → Cell} {lo hi w : ℕ}
    (hG : ∀ j, lo ≤ j → j ≤ hi → pcPat G j ≤ w) {k n : ℕ} (hS : Shp lo hi k n) :
    pcSP G k scp n ≤ 1 + n * w := by
  cases k with
  | zero => simp [pcSP]
  | succ k =>
    by_cases hn : n ≤ 1
    · obtain ⟨h1, h2, h3⟩ := hS.front hn
      rw [pcSP, if_pos hn, h1, one_mul]; have := hG _ h2 h3; omega
    · obtain ⟨hL, hR⟩ := hS.child hn
      rw [pcSP, if_neg hn, scp_shift, scp_zero, if_pos rfl]
      have a := pcSP_cst_le (X := .ghost) (by decide) hG k _ hL
      have b := pcSP_cst_le (X := .ghost) (by decide) hG k _ hR
      have hs := half_sum n
      calc 1 + pcSP G k (cst .ghost) ((n + 1) / 2) + pcSP G k (cst .ghost) (n / 2)
          ≤ 1 + ((n + 1) / 2 * w + n / 2 * w) := by omega
        _ = 1 + n * w := by rw [← add_mul, hs]

theorem pcPat_scp_le (j : ℕ) : pcPat scp j ≤ 1 := by
  cases j with
  | zero => simp [pcPat]
  | succ j => rw [pcPat_scp]

theorem pcPat_cst_le {X : Cell} (hX : X ≠ .pebble) (j : ℕ) : pcPat (cst X) j ≤ 0 := by
  rw [pcPat_cst hX]

/-! ## 左右の子をつなぐ -/

/-- 左の子の部分木で `l0`、右の子の部分木で `l1` を打つ。`y` の状態は変わらない。 -/
theorem pair_spec {h k n0 n1 p0 p1 P : ℕ} {y : Node}
    {G0 A0 G1 A1 G1' A1' : ℕ → Cell} {l0 l1 : List Move} {c : Config}
    (hR0 : Runs h k (y ++ [false]) p0 c l0)
    (hQ0 : SP G0 k A0 n0 (y ++ [false]) (run c l0))
    (hP1 : SP G1 k A1 n1 (y ++ [true]) c)
    (s1 : ∀ c' : Config, SP G1 k A1 n1 (y ++ [true]) c' →
      Runs h k (y ++ [true]) p1 c' l1 ∧ SP G1' k A1' n1 (y ++ [true]) (run c' l1))
    (hb0 : p0 + ((if c y = .pebble then 1 else 0) + pcSP G1 k A1 n1) ≤ P)
    (hb1 : p1 + ((if c y = .pebble then 1 else 0) + pcSP G0 k A0 n0) ≤ P) :
    Runs h (k + 1) y P c (l0 ++ l1) ∧ run c (l0 ++ l1) y = c y ∧
      SP G0 k A0 n0 (y ++ [false]) (run c (l0 ++ l1)) ∧
      SP G1' k A1' n1 (y ++ [true]) (run c (l0 ++ l1)) := by
  have hU0 := hR0.under
  have hcy1 : run c l0 y = c y := run_outside hU0 c (not_prefix_parent y false)
  have hP1' : SP G1 k A1 n1 (y ++ [true]) (run c l0) := (SP_run_disj hU0 (disj01 y)).mpr hP1
  obtain ⟨hR1, hQ1⟩ := s1 _ hP1'
  have hU1 := hR1.under
  have hcy2 : run (run c l0) l1 y = c y :=
    (run_outside hU1 _ (not_prefix_parent y true)).trans hcy1
  have hQ0' : SP G0 k A0 n0 (y ++ [false]) (run (run c l0) l1) :=
    (SP_run_disj hU1 (disj10 y)).mpr hQ0
  have hL0 := hR0.lift0 (q := (if c y = .pebble then 1 else 0) + pcSP G1 k A1 n1)
    (le_of_eq (by rw [pc_of_SP _ _ _ _ hP1]))
  have hL1 := hR1.lift1 (q := (if c y = .pebble then 1 else 0) + pcSP G0 k A0 n0)
    (le_of_eq (by rw [hcy1, pc_of_SP _ _ _ _ hQ0]))
  refine ⟨Runs_append.mpr ⟨hL0.mono hb0, hL1.mono hb1⟩, ?_, ?_, ?_⟩
  · rw [run_append]; exact hcy2
  · rw [run_append]; exact hQ0'
  · rw [run_append]; exact hQ1

/-- 1 手だけの実行。 -/
theorem one_spec {h k : ℕ} {y : Node} {c : Config} {op : Op} (hL : Legal h c ⟨op, y⟩) {P : ℕ}
    (hP : pc k y (step c ⟨op, y⟩) ≤ P) : Runs h k y P c [⟨op, y⟩] :=
  Runs_cons.mpr ⟨hL, List.prefix_refl _, hP, Runs_nil⟩

theorem pc_step_self {k : ℕ} {y : Node} {c : Config} {op : Op} :
    pc (k + 1) y (step c ⟨op, y⟩) =
      (if result op = .pebble then 1 else 0) + pc k (y ++ [false]) c + pc k (y ++ [true]) c := by
  rw [pc, step_self, pc_step_out (not_prefix_parent y false),
    pc_step_out (not_prefix_parent y true)]

/-! ## 前線への写し -/

/-- 割った前線の各頂点に、左から順に `f` を打つ。 -/
def onSp (f : Node → List Move) : ℕ → ℕ → Node → List Move
  | 0, _, _ => []
  | k + 1, n, y => if n ≤ 1 then f y else
      onSp f k ((n + 1) / 2) (y ++ [false]) ++ onSp f k (n / 2) (y ++ [true])

theorem arith_split {p w a b X : ℕ} (ha : 1 ≤ a) (hX : X ≤ b * w) :
    p + (a - 1) * w + X ≤ p + (a + b - 1) * w := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  rw [show a' + 1 + b - 1 = a' + b by omega, show a' + 1 - 1 = a' by omega, add_mul]
  omega

/-- **割った前線への写しの仕様.** 内部はペブルでない `ci` のまま、前線の部分木が `G0` から `G1` に変わる。
ペブル数は `p + (n − 1) w` 以下（`p` は前線 1 個の手順の上限、`w` は前線 1 個の部分木のペブル数の上界）。 -/
theorem onSp_spec {h lo hi p w : ℕ} {ci : Cell} (hci : ci ≠ .pebble) {G0 G1 : ℕ → Cell}
    {f : Node → List Move}
    (hf : ∀ (a : Node) (j : ℕ) (c : Config), a.length + j = h → lo ≤ j → j ≤ hi →
      Pat G0 j a c → Runs h j a p c (f a) ∧ Pat G1 j a (run c (f a)))
    (hw0 : ∀ j, lo ≤ j → j ≤ hi → pcPat G0 j ≤ w) (hw1 : ∀ j, lo ≤ j → j ≤ hi → pcPat G1 j ≤ w) :
    ∀ (k n : ℕ) (y : Node) (c : Config), Shp lo hi k n → y.length + k = h →
      SP G0 k (cst ci) n y c →
      Runs h k y (p + (n - 1) * w) c (onSp f k n y) ∧
        SP G1 k (cst ci) n y (run c (onSp f k n y)) := by
  intro k
  induction k with
  | zero => intro n y c _ _ _; exact ⟨Runs_nil, by simp [SP]⟩
  | succ k ih =>
    intro n y c hS hy hP
    by_cases hn : n ≤ 1
    · obtain ⟨h1, h2, h3⟩ := hS.front hn
      rw [SP_front hn] at hP
      have hon : onSp f (k + 1) n y = f y := by rw [onSp, if_pos hn]
      rw [hon, SP_front hn]
      obtain ⟨hR, hQ⟩ := hf y (k + 1) c hy h2 h3 hP
      subst h1
      exact ⟨hR.mono (by simp), hQ⟩
    · obtain ⟨hSL, hSR⟩ := hS.child hn
      rw [SP_int hn] at hP
      obtain ⟨hcy, hP0, hP1⟩ := hP
      rw [cst_shift] at hP0 hP1
      have hon : onSp f (k + 1) n y =
          onSp f k ((n + 1) / 2) (y ++ [false]) ++ onSp f k (n / 2) (y ++ [true]) := by
        rw [onSp, if_neg hn]
      obtain ⟨hR0, hQ0⟩ := ih _ _ c hSL (by simp; omega) hP0
      have hb0 := pcSP_cst_le hci hw0 k (n / 2) hSR
      have hb1 := pcSP_cst_le hci hw1 k ((n + 1) / 2) hSL
      have hs := half_sum n
      have hci0 : (if c y = .pebble then 1 else 0) = 0 := by rw [hcy, cst_apply, if_neg hci]
      obtain ⟨hR, hy', hQ0', hQ1'⟩ := pair_spec (P := p + (n - 1) * w) hR0 hQ0 hP1
        (fun c' hc' => ih _ _ c' hSR (by simp; omega) hc')
        (by
          rw [hci0, Nat.zero_add]
          have := arith_split (p := p) (w := w) hSL.one hb0
          rw [hs] at this; exact this)
        (by
          rw [hci0, Nat.zero_add]
          have := arith_split (p := p) (w := w) hSR.one hb1
          rw [Nat.add_comm (n / 2), hs] at this; exact this)
      rw [hon]
      refine ⟨hR, ?_⟩
      rw [SP_int hn, cst_shift]
      exact ⟨by rw [hy', hcy], hQ0', hQ1'⟩

/-! ## 内部を置く・外す -/

/-- 割った前線の内部を後順で全部置く。 -/
def plSp (pl : Op) : ℕ → ℕ → Node → List Move
  | 0, _, _ => []
  | k + 1, n, y => if n ≤ 1 then [] else
      plSp pl k ((n + 1) / 2) (y ++ [false]) ++ plSp pl k (n / 2) (y ++ [true]) ++ [⟨pl, y⟩]

/-- 割った前線の内部を前順で全部 unpebble する。 -/
def rmSp : ℕ → ℕ → Node → List Move
  | 0, _, _ => []
  | k + 1, n, y => if n ≤ 1 then [] else
      ⟨.unpebble, y⟩ :: (rmSp k ((n + 1) / 2) (y ++ [false]) ++ rmSp k (n / 2) (y ++ [true]))

/-- **内部を置く.** 内部が全部 `X`、前線がペブル（`G 0 = pebble`）なら、内部は全部ペブルになる。 -/
theorem plSp_spec {h lo hi : ℕ} (hlo : 1 ≤ lo) {pl : Op} {X : Cell} (hpl : PlOk pl X)
    {G : ℕ → Cell} (hG : G 0 = .pebble) :
    ∀ (k n : ℕ) (y : Node) (c : Config), Shp lo hi k n → y.length + k = h →
      SP G k (cst X) n y c →
      Runs h k y (pcSP G k (cst .pebble) n) c (plSp pl k n y) ∧
        SP G k (cst .pebble) n y (run c (plSp pl k n y)) := by
  intro k
  induction k with
  | zero => intro n y c _ _ _; exact ⟨Runs_nil, by simp [SP]⟩
  | succ k ih =>
    intro n y c hS hy hP
    by_cases hn : n ≤ 1
    · have hon : plSp pl (k + 1) n y = [] := by rw [plSp, if_pos hn]
      rw [hon]
      exact ⟨Runs_nil, (SP_front_A hn).mp hP⟩
    · obtain ⟨hSL, hSR⟩ := hS.child hn
      have hk : 1 ≤ k := hSL.pos hlo
      rw [SP_int hn] at hP
      obtain ⟨hcy, hP0, hP1⟩ := hP
      rw [cst_shift] at hP0 hP1
      rw [cst_apply] at hcy
      obtain ⟨hR0, hQ0⟩ := ih _ _ c hSL (by simp; omega) hP0
      have hm0 := pcSP_le_peb (G := G) k (cst X) (n / 2)
      have hXne : (if c y = .pebble then 1 else 0) = 0 := by rw [hcy, if_neg hpl.ne_pebble]
      obtain ⟨hR, hy', hQ0', hQ1'⟩ := pair_spec
        (P := pcSP G k (cst .pebble) ((n + 1) / 2) + pcSP G k (cst .pebble) (n / 2))
        hR0 hQ0 hP1 (fun c' hc' => ih _ _ c' hSR (by simp; omega) hc')
        (by rw [hXne]; omega) (by rw [hXne]; omega)
      set c1 := run c (plSp pl k ((n + 1) / 2) (y ++ [false]) ++ plSp pl k (n / 2) (y ++ [true]))
        with hc1
      have hc1y : c1 y = X := by rw [hy', hcy]
      have hready : Ready h c1 y := ready_of (n := k) (by omega) (fun _ =>
        ⟨SP_top_peb hk hQ0' hG rfl, SP_top_peb hk hQ1' hG rfl⟩)
      have hlegal := legal_place hpl (by omega) hc1y hready
      have hres : step c1 ⟨pl, y⟩ y = .pebble := by rw [step_self, hpl.result]
      have hF0 := (SP_step_out (not_prefix_parent y false) pl).mpr hQ0'
      have hF1 := (SP_step_out (not_prefix_parent y true) pl).mpr hQ1'
      have hfin : pcSP G (k + 1) (cst .pebble) n =
          1 + pcSP G k (cst .pebble) ((n + 1) / 2) + pcSP G k (cst .pebble) (n / 2) := by
        rw [pcSP, if_neg hn, cst_shift, cst_apply, if_pos rfl]
      have hpc1 : pc (k + 1) y (step c1 ⟨pl, y⟩) = pcSP G (k + 1) (cst .pebble) n := by
        rw [pc_step_self, hpl.result, if_pos rfl, pc_of_SP _ _ _ _ hQ0', pc_of_SP _ _ _ _ hQ1', hfin]
      have hpl' : plSp pl (k + 1) n y =
          plSp pl k ((n + 1) / 2) (y ++ [false]) ++ plSp pl k (n / 2) (y ++ [true]) ++ [⟨pl, y⟩] := by
        rw [plSp, if_neg hn]
      rw [hpl']
      refine ⟨Runs_append.mpr ⟨hR.mono (by omega), ?_⟩, ?_⟩
      · rw [← hc1]; exact one_spec hlegal (le_of_eq hpc1)
      · rw [run_append, ← hc1, run_cons, run_nil, SP_int hn, cst_shift]
        exact ⟨hres, hF0, hF1⟩

/-- **内部を外す.** 内部が全部ペブル、前線がペブルなら、内部は全部空になる。 -/
theorem rmSp_spec {h lo hi : ℕ} (hlo : 1 ≤ lo) {G : ℕ → Cell} (hG : G 0 = .pebble) :
    ∀ (k n : ℕ) (y : Node) (c : Config), Shp lo hi k n → y.length + k = h →
      SP G k (cst .pebble) n y c →
      Runs h k y (pcSP G k (cst .pebble) n) c (rmSp k n y) ∧
        SP G k (cst .empty) n y (run c (rmSp k n y)) := by
  intro k
  induction k with
  | zero => intro n y c _ _ _; exact ⟨Runs_nil, by simp [SP]⟩
  | succ k ih =>
    intro n y c hS hy hP
    by_cases hn : n ≤ 1
    · have hon : rmSp (k + 1) n y = [] := by rw [rmSp, if_pos hn]
      rw [hon]
      exact ⟨Runs_nil, (SP_front_A hn).mp hP⟩
    · obtain ⟨hSL, hSR⟩ := hS.child hn
      have hk : 1 ≤ k := hSL.pos hlo
      rw [SP_int hn] at hP
      obtain ⟨hcy, hP0, hP1⟩ := hP
      rw [cst_shift] at hP0 hP1
      rw [cst_apply] at hcy
      have hready : Ready h c y := ready_of (n := k) (by omega) (fun _ =>
        ⟨SP_top_peb hk hP0 hG rfl, SP_top_peb hk hP1 hG rfl⟩)
      have hlegal : Legal h c ⟨.unpebble, y⟩ := legal_unpebble (by omega) hcy hready
      set c1 := step c ⟨.unpebble, y⟩ with hc1
      have hc1y : c1 y = .empty := by rw [hc1, step_self]; rfl
      have hP0' := (SP_step_out (not_prefix_parent y false) .unpebble (c := c)).mpr hP0
      have hP1' := (SP_step_out (not_prefix_parent y true) .unpebble (c := c)).mpr hP1
      have hfin : pcSP G (k + 1) (cst .pebble) n =
          1 + pcSP G k (cst .pebble) ((n + 1) / 2) + pcSP G k (cst .pebble) (n / 2) := by
        rw [pcSP, if_neg hn, cst_shift, cst_apply, if_pos rfl]
      have hpc1 : pc (k + 1) y c1 ≤ pcSP G (k + 1) (cst .pebble) n := by
        rw [hc1, pc_step_self, pc_of_SP _ _ _ _ hP0, pc_of_SP _ _ _ _ hP1, hfin]
        simp [result]
      obtain ⟨hR0, hQ0⟩ := ih _ _ c1 hSL (by simp; omega) hP0'
      have hm0 := pcSP_le_peb (G := G) k (cst .empty) ((n + 1) / 2)
      have hE : (if c1 y = .pebble then 1 else 0) = 0 := by rw [hc1y]; rfl
      obtain ⟨hR, hy', hQ0', hQ1'⟩ := pair_spec (P := pcSP G (k + 1) (cst .pebble) n)
        hR0 hQ0 hP1' (fun c' hc' => ih _ _ c' hSR (by simp; omega) hc')
        (by rw [hE, hfin]; omega) (by rw [hE, hfin]; omega)
      have hrm : rmSp (k + 1) n y = ⟨.unpebble, y⟩ ::
          (rmSp k ((n + 1) / 2) (y ++ [false]) ++ rmSp k (n / 2) (y ++ [true])) := by
        rw [rmSp, if_neg hn]
      rw [hrm]
      refine ⟨Runs_cons.mpr ⟨hlegal, List.prefix_refl _, hpc1, hR⟩, ?_⟩
      rw [run_cons, ← hc1, SP_int hn, cst_shift, cst_apply]
      exact ⟨by rw [hy', hc1y], hQ0', hQ1'⟩

end SpookyTree
