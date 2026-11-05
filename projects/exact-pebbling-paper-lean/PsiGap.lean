import lean.PsiCheck
import RevPebbling.CompositionAnchor

/-!
# 格子点の間を埋める受け渡しのうち countLe 側（m96、§C-1 の残り）

`psi329_count`（m95）は本番格子の各点 i で Ψ_{329}(2^{ℓ_i/R}) ≤ countLe(行 329)(gv[i]) を出す。
格子点の間の値 y（gv[i] ≤ y）と、より小さい指数 ℓ' ≤ ℓ_i へ広げるには 2 つの単調性が要る。

* countLe の閾値についての単調性: Lean リポの `CompositionAnchor.countLe_mono_val`（一般の証明）。
* `PsiLe` の x についての単調性: `psiLe_mono_x`（一般の証明。m95 の `psiLe_mono` と同じ文）。
* `PsiLe` の ℓ についての単調性（Ψ が指数について非減少）: **未証明**。ここでは仮定
  `PsiAntiL sh` として名指しし、`gap_fill` の前提に置く。形（節点の折れ線）が単調であることから
  出るはずだが、`classify` の場合分け（cap／0／区分 E）をまたぐ証明はまだ無い。

すべて一般の証明で、native_decide も本番の定数も使わない（数値は担がない）。
-/

namespace RevPebbling.PsiGap

open RevPebbling.PsiCheck RevPebbling.CountRecursion

/-- 未証明の残り: Ψ は指数 ℓ について非減少（小さい ℓ' の Ψ は大きい ℓ の Ψ 以下）。 -/
def PsiAntiL (sh : Shape) : Prop :=
  ∀ l l' x : Nat, l' ≤ l → PsiLe sh l x → PsiLe sh l' x

/-- `PsiLe` は x について単調（一般の証明）。 -/
theorem psiLe_mono_x (sh : Shape) (l : Nat) {x y : Nat} (hxy : x ≤ y) (h : PsiLe sh l x) :
    PsiLe sh l y := by
  unfold PsiLe at h ⊢
  revert h
  cases classify sh l with
  | zero => intro _; trivial
  | capped => intro h; exact Nat.le_trans h hxy
  | exp p q =>
    intro h
    exact h.imp (fun h => Nat.le_trans h hxy) (fun h => Nat.le_trans h (Nat.pow_le_pow_left hxy q))
  | lost => intro h; exact h.elim

/-- countLe 側の受け渡し（一般の証明、仮定なし）: 格子点 g で成り立てば、g 以上の任意の y で成り立つ。 -/
theorem count_side (sh : Shape) (row : List Nat) {l g y : Nat} (hg : g ≤ y)
    (h : PsiLe sh l (countLe row g)) : PsiLe sh l (countLe row y) :=
  psiLe_mono_x sh l (RevPebbling.CompositionAnchor.countLe_mono_val row hg) h

/-- 格子点の間を埋める結合。`PsiAntiL sh` を仮定すれば、ℓ' ≤ ℓ・g ≤ y へ広がる。 -/
theorem gap_fill (sh : Shape) (row : List Nat) (hA : PsiAntiL sh) {l l' g y : Nat}
    (hl : l' ≤ l) (hg : g ≤ y) (h : PsiLe sh l (countLe row g)) :
    PsiLe sh l' (countLe row y) :=
  hA l l' _ hl (count_side sh row hg h)

/-! ## PsiAntiL を x を含まない分類の比較へ帰着する（m96 周 2）

`PsiAntiL` は x を量化するので有限検査に載らない。ここでは点の分類 `Cls` の間の順序 `ClsLe` を置き、
「ℓ' ≤ ℓ なら classify ℓ' ≤ classify ℓ」（`ClsMono`）から `PsiAntiL` が出ることを一般に示す。
`exp` どうしは 2^{p'/q'} ≤ 2^{p/q}、すなわち p'·q ≤ p·q'（q, q' > 0）で比べる。 -/

/-- 分類だけで書いた仕様（`PsiLe` と同じ場合分け）。 -/
def PsiC (sh : Shape) (c : Cls) (x : Nat) : Prop :=
  match c with
  | .zero => True
  | .capped => sh.cap ≤ x
  | .exp p q => sh.cap ≤ x ∨ 2 ^ p ≤ x ^ q
  | .lost => False

theorem psiLe_eq (sh : Shape) (l x : Nat) : PsiLe sh l x = PsiC sh (classify sh l) x := by
  unfold PsiLe PsiC
  generalize classify sh l = c
  cases c <;> rfl

/-- 分類の順序（左が小さい ℓ' の側）。`lost` が右なら仮定が偽なので常に真。 -/
def ClsLe : Cls → Cls → Prop
  | _, .lost => True
  | .zero, _ => True
  | .exp p' q', .exp p q => 0 < q' ∧ 0 < q ∧ p' * q ≤ p * q'
  | .exp _ _, .capped => True
  | .capped, .capped => True
  | _, _ => False

/-- 有理指数の受け渡し: 2^{p/q} ≤ x かつ p'/q' ≤ p/q なら 2^{p'/q'} ≤ x。 -/
theorem exp_transfer {p q p' q' x : Nat} (hq : 0 < q) (hq' : 0 < q')
    (hpq : p' * q ≤ p * q') (h : 2 ^ p ≤ x ^ q) : 2 ^ p' ≤ x ^ q' := by
  have _ := hq'
  have h1 : (2 ^ p') ^ q ≤ (x ^ q') ^ q :=
    calc (2 ^ p') ^ q = 2 ^ (p' * q) := (Nat.pow_mul 2 p' q).symm
      _ ≤ 2 ^ (p * q') := Nat.pow_le_pow_right (by decide) hpq
      _ = (2 ^ p) ^ q' := Nat.pow_mul 2 p q'
      _ ≤ (x ^ q) ^ q' := Nat.pow_le_pow_left h q'
      _ = (x ^ q') ^ q := by rw [← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm]
  exact (Nat.pow_le_pow_iff_left (Nat.pos_iff_ne_zero.mp hq)).mp h1

/-- 分類の順序は仕様を小さい側へ運ぶ（一般の証明）。 -/
theorem psiC_mono (sh : Shape) {x : Nat} :
    ∀ c' c : Cls, ClsLe c' c → PsiC sh c x → PsiC sh c' x
  | .zero, _, _, _ => trivial
  | _, .lost, _, h => (h : False).elim
  | .capped, .capped, _, h => h
  | .exp _ _, .capped, _, h => Or.inl h
  | .exp _ _, .exp _ _, ⟨hq', hq, hpq⟩, h => h.imp id (exp_transfer hq hq' hpq)
  | .capped, .zero, hc, _ => (hc : False).elim
  | .capped, .exp _ _, hc, _ => (hc : False).elim
  | .exp _ _, .zero, hc, _ => (hc : False).elim
  | .lost, .zero, hc, _ => (hc : False).elim
  | .lost, .capped, hc, _ => (hc : False).elim
  | .lost, .exp _ _, hc, _ => (hc : False).elim

/-- x を含まない単調性の条件（有限検査に載せる対象）。 -/
def ClsMono (sh : Shape) : Prop :=
  ∀ l l' : Nat, l' ≤ l → ClsLe (classify sh l') (classify sh l)

/-- 帰着（一般の証明）: `ClsMono sh` なら `PsiAntiL sh`。 -/
theorem psiAntiL_of_clsMono (sh : Shape) (hM : ClsMono sh) : PsiAntiL sh := by
  intro l l' x hl h
  rw [psiLe_eq] at h ⊢
  exact psiC_mono sh _ _ (hM l l' hl) h

/-! ## ClsMono を有限の隣接検査へ帰着する（m96 周 3）

`ClsMono` は ℓ 全体を量化するが、ℓ·D ≥ x_top·R では `classify` が常に `capped` を返す（`classify_capped`）。
`ClsLe` は推移的（`clsLe_trans`）なので、0..N の隣接対と反射を Bool で検査すれば足りる（`clsMono_of_stepChk`）。
反射は `exp p 0` で偽になるので、検査器は反射も点ごとに見る。数値（本番の形）は担がない。 -/

/-- `ClsLe` の Bool 版。 -/
def clsLeB : Cls → Cls → Bool
  | _, .lost => true
  | .zero, _ => true
  | .exp p' q', .exp p q => decide (0 < q') && decide (0 < q) && decide (p' * q ≤ p * q')
  | .exp _ _, .capped => true
  | .capped, .capped => true
  | _, _ => false

theorem clsLeB_sound : ∀ a b : Cls, clsLeB a b = true → ClsLe a b := by
  intro a b h
  cases a <;> cases b <;> simp_all [clsLeB, ClsLe]

/-- 推移律の算術の核: p''/q'' ≤ p'/q' ≤ p/q（q' > 0）。 -/
theorem ratLe_trans {p q p' q' p'' q'' : Nat} (hq' : 0 < q')
    (h1 : p'' * q' ≤ p' * q'') (h2 : p' * q ≤ p * q') : p'' * q ≤ p * q'' := by
  have h : p'' * q * q' ≤ p * q'' * q' :=
    calc p'' * q * q' = (p'' * q') * q := by rw [Nat.mul_assoc, Nat.mul_comm q, ← Nat.mul_assoc]
      _ ≤ (p' * q'') * q := Nat.mul_le_mul_right q h1
      _ = (p' * q) * q'' := by rw [Nat.mul_assoc, Nat.mul_comm q'', ← Nat.mul_assoc]
      _ ≤ (p * q') * q'' := Nat.mul_le_mul_right q'' h2
      _ = p * q'' * q' := by rw [Nat.mul_assoc, Nat.mul_comm q', ← Nat.mul_assoc]
  exact Nat.le_of_mul_le_mul_right h hq'

theorem clsLe_trans : ∀ a b c : Cls, ClsLe a b → ClsLe b c → ClsLe a c := by
  intro a b c hab hbc
  cases a <;> cases b <;> cases c
  all_goals first
    | trivial
    | exact (hab : False).elim
    | exact (hbc : False).elim
    | exact ⟨hab.1, hbc.2.1, ratLe_trans hab.2.1 hab.2.2 hbc.2.2⟩

/-- 0..N の反射と隣接対の検査器。 -/
def stepChk (sh : Shape) : Nat → Bool
  | 0 => clsLeB (classify sh 0) (classify sh 0)
  | n + 1 => stepChk sh n && clsLeB (classify sh n) (classify sh (n + 1)) &&
      clsLeB (classify sh (n + 1)) (classify sh (n + 1))

theorem stepChk_spec (sh : Shape) : ∀ n : Nat, stepChk sh n = true →
    (∀ k, k ≤ n → ClsLe (classify sh k) (classify sh k)) ∧
    (∀ k, k < n → ClsLe (classify sh k) (classify sh (k + 1)))
  | 0, h => by
    refine ⟨fun k hk => ?_, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
    rw [Nat.le_zero.mp hk]
    exact clsLeB_sound _ _ h
  | n + 1, h => by
    unfold stepChk at h
    rcases Bool.and_eq_true_iff.mp h with ⟨h12, h3⟩
    rcases Bool.and_eq_true_iff.mp h12 with ⟨h1, h2⟩
    obtain ⟨ihr, ihs⟩ := stepChk_spec sh n h1
    refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · rcases Nat.lt_or_eq_of_le hk with hk | rfl
      · exact ihr k (Nat.le_of_lt_succ hk)
      · exact clsLeB_sound _ _ h3
    · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hk | rfl
      · exact ihs k hk
      · exact clsLeB_sound _ _ h2

/-- ℓ·D ≥ x_top·R なら `capped`（一般の証明）。 -/
theorem classify_capped (sh : Shape) {xt y : Nat} {rest : List (Nat × Nat)}
    (hk : sh.knots = (xt, y) :: rest) {l : Nat} (hl : xt * sh.R ≤ l * sh.D) :
    classify sh l = .capped := by
  unfold classify
  rw [hk]
  cases h : ((xt, y) :: rest).getLast? with
  | none => simp at h
  | some v => exact if_pos hl

/-- 帰着（一般の証明）: 有限の検査 `stepChk sh N` と、N が x_top を越えていることから `ClsMono sh`。 -/
theorem clsMono_of_stepChk (sh : Shape) (N : Nat) {xt y : Nat} {rest : List (Nat × Nat)}
    (hk : sh.knots = (xt, y) :: rest) (hN : xt * sh.R ≤ N * sh.D) (h : stepChk sh N = true) :
    ClsMono sh := by
  obtain ⟨hr, hs⟩ := stepChk_spec sh N h
  have tail : ∀ k, N ≤ k → classify sh k = .capped := fun k hNk =>
    classify_capped sh hk (Nat.le_trans hN (Nat.mul_le_mul_right _ hNk))
  have refl : ∀ k, ClsLe (classify sh k) (classify sh k) := fun k => by
    rcases Nat.lt_or_ge N k with hk | hk
    · rw [tail k (Nat.le_of_lt hk)]; trivial
    · exact hr k hk
  have step : ∀ k, ClsLe (classify sh k) (classify sh (k + 1)) := fun k => by
    rcases Nat.lt_or_ge k N with hk | hk
    · exact hs k hk
    · rw [tail k hk, tail (k + 1) (Nat.le_succ_of_le hk)]; trivial
  intro l l' hl
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hl
  induction d with
  | zero => exact refl l'
  | succ d ih =>
    exact clsLe_trans _ _ _ (ih (Nat.le_add_right _ _)) (step (l' + d))

theorem psiAntiL_of_stepChk (sh : Shape) (N : Nat) {xt y : Nat} {rest : List (Nat × Nat)}
    (hk : sh.knots = (xt, y) :: rest) (hN : xt * sh.R ≤ N * sh.D) (h : stepChk sh N = true) :
    PsiAntiL sh :=
  psiAntiL_of_clsMono sh (clsMono_of_stepChk sh N hk hN h)

/-- 計算例: 小さい形 `tiny`（x_top·R = 160 ≤ 16·D）では有限検査が通り、PsiAntiL が無条件に出る（kernel decide）。 -/
example : PsiAntiL tiny := psiAntiL_of_stepChk tiny 16 rfl (by decide) (by decide)

end RevPebbling.PsiGap

#print axioms RevPebbling.PsiGap.psiLe_mono_x
#print axioms RevPebbling.PsiGap.count_side
#print axioms RevPebbling.PsiGap.gap_fill
#print axioms RevPebbling.PsiGap.exp_transfer
#print axioms RevPebbling.PsiGap.psiC_mono
#print axioms RevPebbling.PsiGap.psiAntiL_of_clsMono
#print axioms RevPebbling.PsiGap.clsLe_trans
#print axioms RevPebbling.PsiGap.clsMono_of_stepChk
#print axioms RevPebbling.PsiGap.psiAntiL_of_stepChk
