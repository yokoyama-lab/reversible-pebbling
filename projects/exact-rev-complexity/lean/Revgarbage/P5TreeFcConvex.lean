/-
# P5 補題 M: Knill の再帰 `Fc` の凸性と，差分の単調性

`p5/cc/CONST.md` §1 の機械証明。予算一定の SORT（頂上だけに石がある鎖の森は長い鎖から順に作るのが最短）の
交換の一歩に使う不等式である。

  * `Fc_mono_conv`: `S ≥ 1` で `n ↦ Fc n S` は `n ≥ 1` で単調（`Fc n S ≤ Fc (n+1) S`）かつ凸
    （`2·Fc (n+1) S ≤ Fc n S + Fc (n+2) S`）。`∞` を含めた `ℕ∞` での主張
  * `Fc_diff_local`: `F(n+1,S+1) + F(n,S) ≤ F(n,S+1) + F(n+1,S)`（ペブルを 1 個増やすと増分が小さくなるか等しい）
  * `Fc_diff_mono`（**補題 M**）: `y ≤ x` で `F(x,S+1) + F(y,S) ≤ F(y,S+1) + F(x,S)`
    （ペブルを 1 個増やしたときの減り方 `F(n,S) − F(n,S+1)` は `n` について非減少）

凸性は下限たたみ込みの交換（最適な分割 2 つを 1 ずつ寄せる 4 つの場合）で，`G_S = F(·,S+1) + F(·,S)` が
`F(·,S+1)` 自身を含む自己参照は `n` についての帰納法で処理する。補題 M は最適な分割 `(a, b)` で
`F(n+1,S+1) ≤ G(a) + F(b+1,S)` とし，`F(·,S)` の凸性で増分を `n` の位置まで押し上げる。
使うのは `Fc` の定義（`P5TreeChain.lean`）だけ。
-/
import Revgarbage.P5TreeChain

namespace P5Tree

open Finset

/-! ### 再帰の形 -/

lemma Fc_le_split' {m r : ℕ} (hm : 1 ≤ m) (hr : 1 ≤ r) (S : ℕ) :
    Fc (m + r) (S + 1) ≤ Fc m (S + 1) + Fc m S + Fc r S := by
  have h := Fc_le_split (n := m + r) hm (by omega) S
  rwa [show m + r - m = r by omega] at h

lemma Fc_exists_split {n : ℕ} (hn : 2 ≤ n) (S : ℕ) :
    ∃ m r, 1 ≤ m ∧ 1 ≤ r ∧ m + r = n ∧
      Fc n (S + 1) = Fc m (S + 1) + Fc m S + Fc r S := by
  have h := Fc.eq_2 n S
  rw [if_neg (by omega)] at h
  have hne : ((Ico 1 n).attach).Nonempty := ⟨⟨1, mem_Ico.2 ⟨le_rfl, by omega⟩⟩, mem_attach _ _⟩
  obtain ⟨m, -, hm⟩ := Finset.exists_mem_eq_inf _ hne
    (fun m : {m // m ∈ Ico 1 n} => Fc m.1 (S + 1) + Fc m.1 S + Fc (n - m.1) S)
  have hmI := mem_Ico.1 m.2
  exact ⟨m.1, n - m.1, hmI.1, by omega, by omega, h.trans hm⟩

lemma Fc_one_top {n : ℕ} (hn : 2 ≤ n) : Fc n 1 = ⊤ := by
  obtain ⟨m, r, -, -, -, h⟩ := Fc_exists_split hn 0
  rw [h, Fc_zero]; simp

lemma Fc_two (S : ℕ) : Fc 2 (S + 2) = 3 := by
  obtain ⟨m, r, hm, hr, hmr, h⟩ := Fc_exists_split (n := 2) le_rfl (S + 1)
  obtain rfl : m = 1 := by omega
  obtain rfl : r = 1 := by omega
  rw [h, Fc_one, Fc_one]; rfl

lemma Fc_two_ge {S : ℕ} (hS : 1 ≤ S) : 3 ≤ Fc 2 S := by
  obtain ⟨S, rfl⟩ := Nat.exists_eq_add_of_le hS
  rcases S with _ | S
  · rw [Fc_one_top le_rfl]; exact le_top
  · rw [show 1 + (S + 1) = S + 2 by omega, Fc_two]

lemma Fc_one' {S : ℕ} (hS : 1 ≤ S) : Fc 1 S = 1 := by
  obtain ⟨S, rfl⟩ := Nat.exists_eq_add_of_le hS
  rw [add_comm]; exact Fc_one S

lemma Fc_two_succ {S : ℕ} (hS : 1 ≤ S) : Fc 2 (S + 1) = 3 := by
  obtain ⟨S, rfl⟩ := Nat.exists_eq_add_of_le hS
  rw [show 1 + S + 1 = S + 2 by omega, Fc_two]

/-- ペブルを 1 個増やしても再帰の値は増えない（`P5TreeKnill.lean` の `Fc_succ_le` と同じ主張．
そちらは非公開の鎖のリポを import するので，ここに写した）。 -/
theorem Fc_succ_le' : ∀ S n, Fc n (S + 1) ≤ Fc n S := by
  intro S
  induction S with
  | zero => intro n; rw [Fc_zero]; exact le_top
  | succ S ih =>
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ihn =>
    rw [Fc.eq_2 n (S + 1), Fc.eq_2 n S]
    split_ifs with h
    · exact le_rfl
    · apply Finset.le_inf
      intro m _
      refine le_trans (Finset.inf_le (mem_attach _ m)) ?_
      have hm := mem_Ico.1 m.2
      exact add_le_add (add_le_add (ihn m.1 hm.2) (ih m.1)) (ih (n - m.1))

/-! ### `ℕ∞` の小道具 -/

lemma enat_le_of_add_le_add_right {x y z : ℕ∞} (hz : z ≠ ⊤) (h : x + z ≤ y + z) : x ≤ y := by
  induction z using ENat.recTopCoe with
  | top => exact absurd rfl hz
  | coe c =>
    induction y using ENat.recTopCoe with
    | top => exact le_top
    | coe b =>
      induction x using ENat.recTopCoe with
      | top =>
        exfalso; rw [top_add, top_le_iff] at h
        exact (by exact_mod_cast ENat.coe_ne_top (b + c) : (b : ℕ∞) + c ≠ ⊤) h
      | coe a => norm_cast at h ⊢; omega

lemma enat_add_ne_top {x y : ℕ∞} (hx : x ≠ ⊤) (hy : y ≠ ⊤) : x + y ≠ ⊤ := by
  induction x using ENat.recTopCoe with
  | top => exact absurd rfl hx
  | coe a =>
    induction y using ENat.recTopCoe with
    | top => exact absurd rfl hy
    | coe b => exact_mod_cast ENat.coe_ne_top (a + b)

/-- 単調な列の 2 点の比較。 -/
lemma mono_le {f : ℕ → ℕ∞} {N : ℕ} (hmono : ∀ i, 1 ≤ i → i + 1 ≤ N → f i ≤ f (i + 1)) :
    ∀ k i, 1 ≤ i → i + k ≤ N → f i ≤ f (i + k) := by
  intro k
  induction k with
  | zero => intro i _ _; exact le_rfl
  | succ k ih =>
    intro i hi hik
    exact (ih i hi (by omega)).trans (by rw [← add_assoc]; exact hmono _ (by omega) (by omega))

/-- 局所の凸性から弦の不等式: `f(a+1) + f(a+1+k) ≤ f(a) + f(a+2+k)`（`a+2+k ≤ N` まで）。 -/
lemma chord {f : ℕ → ℕ∞} {N : ℕ}
    (hmono : ∀ i, 1 ≤ i → i + 1 ≤ N → f i ≤ f (i + 1))
    (hconv : ∀ i, 1 ≤ i → i + 2 ≤ N → f (i + 1) + f (i + 1) ≤ f i + f (i + 2)) :
    ∀ k a, 1 ≤ a → a + 2 + k ≤ N → f (a + 1) + f (a + 1 + k) ≤ f a + f (a + 2 + k) := by
  intro k
  induction k with
  | zero => intro a ha haN; simpa using hconv a ha (by omega)
  | succ k ih =>
    intro a ha haN
    have IH := ih a ha (by omega)
    have C := hconv (a + 1 + k) (by omega) (by omega)
    rw [show a + 1 + k + 1 = a + 2 + k by omega, show a + 1 + k + 2 = a + 3 + k by omega] at C
    rw [show a + 1 + (k + 1) = a + 2 + k by omega, show a + 2 + (k + 1) = a + 3 + k by omega]
    by_cases htop : f (a + 3 + k) = ⊤
    · rw [htop]; simp
    have h2 : f (a + 2 + k) ≠ ⊤ :=
      ne_top_of_le_ne_top htop (by
        have := mono_le hmono 1 (a + 2 + k) (by omega) (by omega)
        rwa [show a + 2 + k + 1 = a + 3 + k by omega] at this)
    have h1 : f (a + 1 + k) ≠ ⊤ :=
      ne_top_of_le_ne_top h2 (by
        have := mono_le hmono 1 (a + 1 + k) (by omega) (by omega)
        rwa [show a + 1 + k + 1 = a + 2 + k by omega] at this)
    apply enat_le_of_add_le_add_right (z := f (a + 1 + k) + f (a + 2 + k)) (enat_add_ne_top h1 h2)
    calc f (a + 1) + f (a + 2 + k) + (f (a + 1 + k) + f (a + 2 + k))
        = (f (a + 1) + f (a + 1 + k)) + (f (a + 2 + k) + f (a + 2 + k)) := by ring
      _ ≤ (f a + f (a + 2 + k)) + (f (a + 1 + k) + f (a + 3 + k)) := add_le_add IH C
      _ = f a + f (a + 3 + k) + (f (a + 1 + k) + f (a + 2 + k)) := by ring

/-! ### 凸性（段 `S` から段 `S+1` へ） -/

/-- 段 `S`（`S ≥ 1`）が単調かつ凸なら，段 `S+1` も単調かつ凸。 -/
theorem Fc_step {S : ℕ} (hS : 1 ≤ S)
    (hmono : ∀ i, 1 ≤ i → Fc i S ≤ Fc (i + 1) S)
    (hconv : ∀ i, 1 ≤ i → Fc (i + 1) S + Fc (i + 1) S ≤ Fc i S + Fc (i + 2) S) :
    ∀ N, ∀ n, 1 ≤ n → n ≤ N →
      Fc n (S + 1) ≤ Fc (n + 1) (S + 1) ∧
      Fc (n + 1) (S + 1) + Fc (n + 1) (S + 1) ≤ Fc n (S + 1) + Fc (n + 2) (S + 1) := by
  -- 段 S の弦（上限なし）
  have hchordS : ∀ k a, 1 ≤ a →
      Fc (a + 1) S + Fc (a + 1 + k) S ≤ Fc a S + Fc (a + 2 + k) S := fun k a ha =>
    chord (f := fun i => Fc i S) (N := a + 2 + k) (fun i hi _ => hmono i hi)
      (fun i hi _ => hconv i hi) k a ha le_rfl
  have h1 : Fc 1 S = 1 := Fc_one' hS
  have f1 : Fc 1 (S + 1) = 1 := Fc_one S
  have f2 : Fc 2 (S + 1) = 3 := Fc_two_succ hS
  have h2 : 3 ≤ Fc 2 S := Fc_two_ge hS
  intro N
  induction N with
  | zero => intro n hn hnN; omega
  | succ N ih =>
    intro n hn hnN
    rcases Nat.lt_or_ge n (N + 1) with hlt | hge
    · exact ih n hn (by omega)
    obtain rfl : n = N + 1 := by omega
    -- 帰納法の仮定（n より小さい添字）
    have IHm : ∀ i, 1 ≤ i → i ≤ N → Fc i (S + 1) ≤ Fc (i + 1) (S + 1) := fun i hi hiN =>
      (ih i hi hiN).1
    have IHc : ∀ i, 1 ≤ i → i ≤ N →
        Fc (i + 1) (S + 1) + Fc (i + 1) (S + 1) ≤ Fc i (S + 1) + Fc (i + 2) (S + 1) :=
      fun i hi hiN => (ih i hi hiN).2
    -- 単調性（添字 N+1）
    have hM : Fc (N + 1) (S + 1) ≤ Fc (N + 1 + 1) (S + 1) := by
      rcases Nat.lt_or_ge N 1 with h0 | hN1
      · obtain rfl : N = 0 := by omega
        rw [f1, f2]; norm_num
      obtain ⟨a, b, ha, hb, hab, hsplit⟩ := Fc_exists_split (n := N + 1 + 1) (by omega) S
      rw [hsplit]
      rcases Nat.lt_or_ge b 2 with hb1 | hb2
      · obtain rfl : b = 1 := by omega
        have ha' : a = N + 1 := by omega
        subst ha'
        have hs := Fc_le_split' (m := N) (r := 1) hN1 le_rfl S
        refine hs.trans ?_
        exact add_le_add (add_le_add (IHm N hN1 le_rfl) (hmono N hN1)) le_rfl
      · have hs := Fc_le_split' (m := a) (r := b - 1) ha (by omega) S
        rw [show a + (b - 1) = N + 1 by omega] at hs
        refine hs.trans (add_le_add le_rfl ?_)
        have := hmono (b - 1) (by omega)
        rwa [show b - 1 + 1 = b by omega] at this
    refine ⟨hM, ?_⟩
    -- 凸性（添字 N+1）
    -- 段 S+1 の弦は添字 N+2 まで使える
    have hchordF : ∀ k a, 1 ≤ a → a + 2 + k ≤ N + 2 →
        Fc (a + 1) (S + 1) + Fc (a + 1 + k) (S + 1) ≤ Fc a (S + 1) + Fc (a + 2 + k) (S + 1) :=
      chord (f := fun i => Fc i (S + 1)) (N := N + 2)
        (fun i hi hiN => by
          rcases Nat.lt_or_ge i (N + 1) with h | h
          · exact IHm i hi (by omega)
          · obtain rfl : i = N + 1 := by omega
            exact hM)
        (fun i hi hiN => IHc i hi (by omega))
    rcases Nat.lt_or_ge N 1 with h0 | hN1
    · -- n = 1: 2·F(2) ≤ F(1) + F(3)
      obtain rfl : N = 0 := by omega
      obtain ⟨a, b, ha, hb, hab, hsplit⟩ := Fc_exists_split (n := 0 + 1 + 2) (by omega) S
      rw [hsplit, show 0 + 1 + 1 = 2 by rfl, show (0 + 1 : ℕ) = 1 by rfl, f1, f2]
      rcases Nat.lt_or_ge a 2 with ha1 | ha2
      · obtain rfl : a = 1 := by omega
        obtain rfl : b = 2 := by omega
        rw [f1, h1]
        generalize Fc 2 S = t at h2 ⊢
        induction t using ENat.recTopCoe with
        | top => simp
        | coe c =>
          have : 3 ≤ c := by exact_mod_cast h2
          exact_mod_cast (show 3 + 3 ≤ 1 + (1 + 1 + c) by omega)
      · obtain rfl : a = 2 := by omega
        obtain rfl : b = 1 := by omega
        rw [f2, h1]
        generalize Fc 2 S = t at h2 ⊢
        induction t using ENat.recTopCoe with
        | top => simp
        | coe c =>
          have : 3 ≤ c := by exact_mod_cast h2
          exact_mod_cast (show 3 + 3 ≤ 1 + (3 + c + 1) by omega)
    -- n = N+1 ≥ 2: 最適な分割 n = a + b，n + 2 = c + d
    obtain ⟨a, b, ha, hb, hab, hn⟩ := Fc_exists_split (n := N + 1) (by omega) S
    obtain ⟨c, d, hc, hd, hcd, hn2⟩ := Fc_exists_split (n := N + 1 + 2) (by omega) S
    rw [hn, hn2]
    rcases Nat.lt_or_ge (a + 1) c with hac | hac
    · -- c ≥ a + 2: (a+1, b) と (c−1, d)
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (show a + 2 ≤ c by omega)
      have s1 := Fc_le_split' (m := a + 1) (r := b) (by omega) hb S
      have s2 := Fc_le_split' (m := a + 1 + k) (r := d) (by omega) hd S
      rw [show a + 1 + b = N + 1 + 1 by omega] at s1
      rw [show a + 1 + k + d = N + 1 + 1 by omega] at s2
      have cF := hchordF k a ha (by omega)
      have cS := hchordS k a ha
      calc Fc (N + 1 + 1) (S + 1) + Fc (N + 1 + 1) (S + 1)
          ≤ (Fc (a + 1) (S + 1) + Fc (a + 1) S + Fc b S)
            + (Fc (a + 1 + k) (S + 1) + Fc (a + 1 + k) S + Fc d S) := add_le_add s1 s2
        _ = (Fc (a + 1) (S + 1) + Fc (a + 1 + k) (S + 1)) + (Fc (a + 1) S + Fc (a + 1 + k) S)
            + (Fc b S + Fc d S) := by ring
        _ ≤ (Fc a (S + 1) + Fc (a + 2 + k) (S + 1)) + (Fc a S + Fc (a + 2 + k) S)
            + (Fc b S + Fc d S) := add_le_add (add_le_add cF cS) le_rfl
        _ = _ := by ring
    rcases Nat.lt_or_ge a c with hac2 | hac2
    · -- c = a + 1, d = b + 1: (a+1, b) と (a, b+1)
      obtain rfl : c = a + 1 := by omega
      obtain rfl : d = b + 1 := by omega
      have s1 := Fc_le_split' (m := a + 1) (r := b) (by omega) hb S
      have s2 := Fc_le_split' (m := a) (r := b + 1) ha (by omega) S
      rw [show a + 1 + b = N + 1 + 1 by omega] at s1
      rw [show a + (b + 1) = N + 1 + 1 by omega] at s2
      calc Fc (N + 1 + 1) (S + 1) + Fc (N + 1 + 1) (S + 1)
          ≤ (Fc (a + 1) (S + 1) + Fc (a + 1) S + Fc b S)
            + (Fc a (S + 1) + Fc a S + Fc (b + 1) S) := add_le_add s1 s2
        _ = _ := by ring
    rcases Nat.lt_or_ge c a with hca | hca
    · -- c < a: (a, b+1) と (c, d−1)，段 S の弦を b から d へ
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (show c + 1 ≤ a by omega)
      have hdj : d = b + 2 + (j + 1) := by omega
      subst hdj
      have s1 := Fc_le_split' (m := c + 1 + j) (r := b + 1) (by omega) (by omega) S
      have s2 := Fc_le_split' (m := c) (r := b + 1 + (j + 1)) hc (by omega) S
      rw [show c + 1 + j + (b + 1) = N + 1 + 1 by omega] at s1
      rw [show c + (b + 1 + (j + 1)) = N + 1 + 1 by omega] at s2
      have cS := hchordS (j + 1) b hb
      calc Fc (N + 1 + 1) (S + 1) + Fc (N + 1 + 1) (S + 1)
          ≤ (Fc (c + 1 + j) (S + 1) + Fc (c + 1 + j) S + Fc (b + 1) S)
            + (Fc c (S + 1) + Fc c S + Fc (b + 1 + (j + 1)) S) := add_le_add s1 s2
        _ = (Fc (c + 1 + j) (S + 1) + Fc (c + 1 + j) S + Fc c (S + 1) + Fc c S)
            + (Fc (b + 1) S + Fc (b + 1 + (j + 1)) S) := by ring
        _ ≤ (Fc (c + 1 + j) (S + 1) + Fc (c + 1 + j) S + Fc c (S + 1) + Fc c S)
            + (Fc b S + Fc (b + 2 + (j + 1)) S) := add_le_add le_rfl cS
        _ = _ := by ring
    · -- c = a, d = b + 2: (a, b+1) を 2 回，段 S の凸性
      obtain rfl : a = c := by omega
      obtain rfl : d = b + 2 := by omega
      have s := Fc_le_split' (m := a) (r := b + 1) ha (by omega) S
      rw [show a + (b + 1) = N + 1 + 1 by omega] at s
      have cS := hconv b hb
      calc Fc (N + 1 + 1) (S + 1) + Fc (N + 1 + 1) (S + 1)
          ≤ (Fc a (S + 1) + Fc a S + Fc (b + 1) S) + (Fc a (S + 1) + Fc a S + Fc (b + 1) S) :=
            add_le_add s s
        _ = (Fc a (S + 1) + Fc a S) + (Fc a (S + 1) + Fc a S) + (Fc (b + 1) S + Fc (b + 1) S) := by
            ring
        _ ≤ (Fc a (S + 1) + Fc a S) + (Fc a (S + 1) + Fc a S) + (Fc b S + Fc (b + 2) S) :=
            add_le_add le_rfl cS
        _ = _ := by ring

/-- **凸性と単調性**: `S ≥ 1` で `n ↦ Fc n S` は `n ≥ 1` で単調かつ凸。 -/
theorem Fc_mono_conv : ∀ S, 1 ≤ S →
    (∀ i, 1 ≤ i → Fc i S ≤ Fc (i + 1) S) ∧
    (∀ i, 1 ≤ i → Fc (i + 1) S + Fc (i + 1) S ≤ Fc i S + Fc (i + 2) S) := by
  intro S hS
  induction S with
  | zero => omega
  | succ S ih =>
    rcases Nat.lt_or_ge S 1 with h0 | hS1
    · obtain rfl : S = 0 := by omega
      refine ⟨fun i hi => ?_, fun i hi => ?_⟩
      · rw [Fc_one_top (n := i + 1) (by omega)]; exact le_top
      · rw [Fc_one_top (n := i + 2) (by omega)]; simp
    · obtain ⟨hm, hc⟩ := ih hS1
      exact ⟨fun i hi => (Fc_step hS1 hm hc i i hi le_rfl).1,
        fun i hi => (Fc_step hS1 hm hc i i hi le_rfl).2⟩

/-! ### 補題 M -/

/-- 局所版: `F(n+1,S+1) + F(n,S) ≤ F(n,S+1) + F(n+1,S)`（`S ≥ 1`，`n ≥ 1`）。 -/
theorem Fc_diff_local {S : ℕ} (hS : 1 ≤ S) {n : ℕ} (hn : 1 ≤ n) :
    Fc (n + 1) (S + 1) + Fc n S ≤ Fc n (S + 1) + Fc (n + 1) S := by
  obtain ⟨hmono, hconv⟩ := Fc_mono_conv S hS
  rcases Nat.lt_or_ge n 2 with hn1 | hn2
  · obtain rfl : n = 1 := by omega
    rw [Fc_two_succ hS, Fc_one' hS, Fc_one]
    have h2 := Fc_two_ge hS
    generalize Fc 2 S = t at h2 ⊢
    induction t using ENat.recTopCoe with
    | top => simp
    | coe c =>
      have : 3 ≤ c := by exact_mod_cast h2
      exact_mod_cast (show 3 + 1 ≤ 1 + c by omega)
  obtain ⟨a, b, ha, hb, hab, hsplit⟩ := Fc_exists_split hn2 S
  obtain ⟨a', rfl⟩ := Nat.exists_eq_add_of_le ha
  have s := Fc_le_split' (m := 1 + a') (r := b + 1) ha (by omega) S
  rw [show 1 + a' + (b + 1) = n + 1 by omega] at s
  have cS := chord (f := fun i => Fc i S) (N := b + 2 + a') (fun i hi _ => hmono i hi)
    (fun i hi _ => hconv i hi) a' b hb le_rfl
  rw [show b + 1 + a' = n by omega, show b + 2 + a' = n + 1 by omega] at cS
  rw [hsplit]
  calc Fc (n + 1) (S + 1) + Fc n S
      ≤ Fc (1 + a') (S + 1) + Fc (1 + a') S + Fc (b + 1) S + Fc n S := add_le_add s le_rfl
    _ = Fc (1 + a') (S + 1) + Fc (1 + a') S + (Fc (b + 1) S + Fc n S) := by ring
    _ ≤ Fc (1 + a') (S + 1) + Fc (1 + a') S + (Fc b S + Fc (n + 1) S) := add_le_add le_rfl cS
    _ = _ := by ring

/-- **補題 M**: `1 ≤ y ≤ x` で `F(x,S+1) + F(y,S) ≤ F(y,S+1) + F(x,S)`（`S ≥ 1`）。
`CONST.md` の形 `F(y,S) + F(x,S−1) ≥ F(x,S) + F(y,S−1)`（`S ≥ 2`）は `S` を 1 ずらしたもの。 -/
theorem Fc_diff_mono {S : ℕ} (hS : 1 ≤ S) {y : ℕ} (hy : 1 ≤ y) :
    ∀ k, Fc (y + k) (S + 1) + Fc y S ≤ Fc y (S + 1) + Fc (y + k) S := by
  obtain ⟨hmono, -⟩ := Fc_mono_conv S hS
  intro k
  induction k with
  | zero => simp [add_comm]
  | succ k ih =>
    have L := Fc_diff_local hS (n := y + k) (by omega)
    rw [show y + k + 1 = y + (k + 1) by omega] at L
    by_cases htop : Fc (y + (k + 1)) S = ⊤
    · rw [htop]; simp
    have hh : Fc (y + k) S ≠ ⊤ := ne_top_of_le_ne_top htop
      (by have := hmono (y + k) (by omega); rwa [show y + k + 1 = y + (k + 1) by omega] at this)
    have hf : Fc (y + k) (S + 1) ≠ ⊤ := ne_top_of_le_ne_top hh (Fc_succ_le' S (y + k))
    apply enat_le_of_add_le_add_right (z := Fc (y + k) (S + 1) + Fc (y + k) S) (enat_add_ne_top hf hh)
    calc Fc (y + (k + 1)) (S + 1) + Fc y S + (Fc (y + k) (S + 1) + Fc (y + k) S)
        = (Fc (y + (k + 1)) (S + 1) + Fc (y + k) S) + (Fc (y + k) (S + 1) + Fc y S) := by ring
      _ ≤ (Fc (y + k) (S + 1) + Fc (y + (k + 1)) S) + (Fc y (S + 1) + Fc (y + k) S) :=
          add_le_add L ih
      _ = Fc y (S + 1) + Fc (y + (k + 1)) S + (Fc (y + k) (S + 1) + Fc (y + k) S) := by ring

/-- 補題 M を `CONST.md` の形で: `S ≥ 2`，`1 ≤ y ≤ x` で `F(x,S) + F(y,S−1) ≤ F(y,S) + F(x,S−1)`。 -/
theorem lemmaM {S x y : ℕ} (hS : 2 ≤ S) (hy : 1 ≤ y) (hyx : y ≤ x) :
    Fc x S + Fc y (S - 1) ≤ Fc y S + Fc x (S - 1) := by
  obtain ⟨S', rfl⟩ := Nat.exists_eq_add_of_le (show 1 + 1 ≤ S from hS)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hyx
  have h := Fc_diff_mono (S := 1 + S') (by omega) hy k
  rw [show 1 + 1 + S' - 1 = 1 + S' by omega, show 1 + 1 + S' = 1 + S' + 1 by omega]
  exact h

end P5Tree
