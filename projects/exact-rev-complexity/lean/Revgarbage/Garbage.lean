/-
候補10 — 最小ガベージ幅の Lean 形式化。

**manifest（層の区別）**

* **L1（一般証明・無条件）**
  - `garbage_iff_card_fiber_le` : 自由ガベージ模型での最小幅の特徴づけ（両方向）。
    **Hall の結婚定理は不要**で、ファイバーごとの埋め込みの貼り合わせだけで済む。
    これが「素朴な定式化は自明である」ことの形式的な内容。
  - `garbage_iff_clog_le` : 上を $\lceil \log_2 \rceil$ の形にしたもの。
  - `proj_lower_bound` : 射影ガベージ模型は自由ガベージ模型の特殊形なので
    情報論的下界が同じく成り立つ（緩む側の証明はここには無い＝反例は L2）。
  - `sign_gate_pow`, `sign_gate_eq_one`, `closure_gates_le_ker_sign` :
    **arity < N のゲートは偶置換しか生成しない**（パリティ障害）。
    これは既知（Shende–Prasad–Markov–Hayes 2003）だが、非自明な下界の唯一の源。

* **L2（有界全数検査・`decide`）**
  - `maj3_maxFiber`, `maj3_free_two`, `maj3_proj_needs_all_three` :
    多数決 $\mathrm{MAJ}_3$ で射影ガベージ模型の下界が緩む（$1$ ビットの差）。
  - `gap2_lb_one`, `gap2_proj_needs_all_three` :
    $n=3$ に下界との差が **2** の例がある（差は 1 で止まらない）。
-/
import Mathlib

namespace RevGarbage

open Finset

/-! ## L1-A 自由ガベージ模型 — 下界と達成可能性（Hall 不要） -/

section FreeGarbage

variable {α β G : Type*} [Fintype α] [DecidableEq β] [Fintype G]

/-- $f$ のファイバー $f^{-1}(y)$。 -/
def fiber (f : α → β) (y : β) : Finset α := univ.filter fun x => f x = y

/-- **下界方向**: ガベージ付き写像 $x \mapsto (f x, \gamma x)$ が単射なら、
どのファイバーもガベージ空間に収まる。 -/
theorem card_fiber_le_of_injective (f : α → β) (γ : α → G)
    (h : Function.Injective fun x => (f x, γ x)) (y : β) :
    (fiber f y).card ≤ Fintype.card G := by
  classical
  have : Set.InjOn γ (fiber f y) := by
    intro a ha b hb hab
    apply h
    simp only [mem_coe, fiber, mem_filter] at ha hb
    simp [ha.2, hb.2, hab]
  calc (fiber f y).card ≤ (univ.image γ).card := by
        rw [← card_image_of_injOn this]
        exact card_le_card (image_subset_image (subset_univ _))
    _ ≤ Fintype.card G := card_le_univ _

/-- **達成可能方向**: 各ファイバーがガベージ空間に収まるなら、単射なガベージ割当が存在する。
**Hall の結婚定理は使わない**: ファイバーは互いに素で、割り当て先の制約もファイバーごとに
独立なので、ファイバーごとに埋め込みを 1 個選んで貼り合わせるだけでよい。 -/
theorem exists_garbage_of_card_fiber_le (f : α → β)
    (h : ∀ y, (fiber f y).card ≤ Fintype.card G) :
    ∃ γ : α → G, Function.Injective fun x => (f x, γ x) := by
  classical
  -- 各 y について、ファイバーの部分型から G への埋め込みを 1 個選ぶ。
  have hcard : ∀ y : β, Fintype.card {x : α // f x = y} ≤ Fintype.card G := by
    intro y
    have : Fintype.card {x : α // f x = y} = (fiber f y).card := by
      simp [fiber, Fintype.card_subtype]
    rw [this]; exact h y
  -- ガベージ空間が空なら、すべてのファイバーが空 = α が空なので自明。
  rcases isEmpty_or_nonempty G with hG | hG
  · have : IsEmpty α := by
      refine ⟨fun x => ?_⟩
      have h1 : (fiber f (f x)).card ≤ 0 := by simpa using h (f x)
      have : x ∈ fiber f (f x) := by simp [fiber]
      exact absurd (card_pos.mpr ⟨x, this⟩) (by omega)
    exact ⟨fun x => (this.elim x : G), fun a _ _ => this.elim a⟩
  -- ファイバーごとに「そのファイバー上で単射な全域関数」を選ぶ（依存型を避ける）。
  have key : ∀ y : β, ∃ γ : α → G, Set.InjOn γ (fiber f y) := by
    intro y
    obtain ⟨emb⟩ := Function.Embedding.nonempty_of_card_le (hcard y)
    refine ⟨Function.extend Subtype.val emb fun _ => Classical.arbitrary G, ?_⟩
    intro a ha b hb hab
    simp only [mem_coe, fiber, mem_filter] at ha hb
    have ea := Subtype.val_injective.extend_apply emb
      (fun _ => Classical.arbitrary G) (⟨a, ha.2⟩ : {x : α // f x = y})
    have eb := Subtype.val_injective.extend_apply emb
      (fun _ => Classical.arbitrary G) (⟨b, hb.2⟩ : {x : α // f x = y})
    simp only [] at ea eb
    rw [ea] at hab
    rw [eb] at hab
    exact congrArg Subtype.val (emb.injective hab)
  choose γ hγ using key
  -- γ (f x) x を使えば、添字も引数も非依存なので書き換えが素直に通る。
  refine ⟨fun x => γ (f x) x, ?_⟩
  intro a b hab
  simp only [Prod.mk.injEq] at hab
  obtain ⟨h1, h2⟩ := hab
  rw [← h1] at h2
  refine hγ (f a) ?_ ?_ h2
  · simp [fiber]
  · simp [fiber, h1]

/-- **自由ガベージ模型の特徴づけ（L1 の本体）。**
幅 $g$ のガベージで $f$ を可逆に埋め込めることは、
すべてのファイバーが $2^g$ 以下であることと同値。 -/
theorem garbage_iff_card_fiber_le (f : α → β) (g : ℕ) :
    (∃ γ : α → Fin (2 ^ g), Function.Injective fun x => (f x, γ x))
      ↔ ∀ y, (fiber f y).card ≤ 2 ^ g := by
  constructor
  · intro ⟨γ, hγ⟩ y
    simpa using card_fiber_le_of_injective f γ hγ y
  · intro h
    apply exists_garbage_of_card_fiber_le
    simpa using h

/-- 同じことを $\lceil \log_2 \rceil$ の形で。$g^*(f) = \lceil \log_2 \max_y |f^{-1}(y)| \rceil$。 -/
theorem garbage_iff_clog_le [Fintype β] (f : α → β) (g : ℕ) :
    (∃ γ : α → Fin (2 ^ g), Function.Injective fun x => (f x, γ x))
      ↔ Nat.clog 2 (univ.sup fun y => (fiber f y).card) ≤ g := by
  rw [garbage_iff_card_fiber_le]
  constructor
  · intro h
    rw [Nat.clog_le_iff_le_pow (b := 2) (by norm_num)]
    exact Finset.sup_le fun y _ => h y
  · intro h y
    have hs : (univ.sup fun y => (fiber f y).card) ≤ 2 ^ g := by
      rw [← Nat.clog_le_iff_le_pow (b := 2) (by norm_num)]; exact h
    exact le_trans (Finset.le_sup (f := fun y => (fiber f y).card) (mem_univ y)) hs

end FreeGarbage

/-! ## L1-B 射影ガベージ模型 — 下界は同じく成り立つ（タイトさは別問題） -/

section Projection

variable {n : ℕ}

/-- 入力ビットの部分集合 `S` だけをガベージとして残す（Bennett 型の節約版）。 -/
def ProjOK (f : (Fin n → Bool) → Bool) (S : Fin n → Bool) : Prop :=
  Function.Injective fun x : Fin n → Bool => (f x, fun i => S i && x i)

instance (f : (Fin n → Bool) → Bool) (S : Fin n → Bool) : Decidable (ProjOK f S) := by
  unfold ProjOK Function.Injective; infer_instance

/-- 射影ガベージも自由ガベージの特殊形なので、情報論的下界は射影模型にも効く。
`S` の 1 の個数を `g` とすると、ファイバーは $2^g$ 以下でなければならない。 -/
theorem projOK_iff_subcube (f : (Fin n → Bool) → Bool) (S : Fin n → Bool) :
    ProjOK f S ↔ ∀ a b : Fin n → Bool,
      (∀ i, S i = true → a i = b i) → f a = f b → a = b := by
  constructor
  · intro h a b hS hf
    refine h (Prod.ext hf ?_)
    funext i
    by_cases hi : S i = true
    · simp [hi, hS i hi]
    · simp [Bool.not_eq_true] at hi
      simp [hi]
  · intro h a b hab
    simp only [Prod.mk.injEq] at hab
    obtain ⟨hf, hg⟩ := hab
    refine h a b (fun i hi => ?_) hf
    have := congrFun hg i
    simpa [hi] using this

theorem proj_lower_bound
    (f : (Fin n → Bool) → Bool) (S : Fin n → Bool) (h : ProjOK f S) (y : Bool) :
    (fiber f y).card ≤ 2 ^ (univ.filter fun i => S i = true).card := by
  classical
  -- ガベージの値域は「S が立っているビットの割り当て」に含まれるので、
  -- 濃度は 2 ^ |S| 以下。
  set T : Finset (Fin n) := univ.filter fun i => S i = true with hT
  have key : Set.InjOn (fun x : Fin n → Bool => fun i : T => x i) (fiber f y) := by
    intro a ha b hb hab
    apply h
    simp only [mem_coe, fiber, mem_filter] at ha hb
    refine Prod.ext (by simp [ha.2, hb.2]) ?_
    funext i
    by_cases hi : S i = true
    · have : (⟨i, by simp [hT, hi]⟩ : T) ∈ (univ : Finset T) := mem_univ _
      have := congrFun hab (⟨i, by simp [hT, hi]⟩ : T)
      simp only at this
      simp [hi, this]
    · simp [Bool.not_eq_true] at hi
      simp [hi]
  calc (fiber f y).card
      ≤ Fintype.card (T → Bool) := by
        have := Finset.card_le_card_of_injOn _ (fun x _ => mem_univ (α := T → Bool) _) key
        simpa using this
    _ = 2 ^ T.card := by simp
end Projection

/-! ## L1-C ゲート引数個数の制約 — パリティ障害（非自明な下界の唯一の源）

$N$ 本の線のうち $k < N$ 本にしか作用しないゲートは、$\{0,1\}^N$ 上で
**必ず偶置換**を誘導する。したがって奇置換を実現するには線を 1 本増やすしかない。
既知: Shende–Prasad–Markov–Hayes 2003。 -/

section Parity

open Equiv Equiv.Perm

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- 「$B$ 側（対象線）に置換 `π` を、$A$ 側（非対象線）には恒等を載せたゲート」の符号は
$\mathrm{sign}(\pi)^{|A|}$。 -/
theorem sign_gate_pow (π : Perm B) :
    sign (prodCongrRight fun _ : A => π) = sign π ^ Fintype.card A := by
  rw [sign_prodCongrRight, Finset.prod_const, Finset.card_univ]
  rfl

/-- 非対象線が 1 本以上ある（= $|A|$ が偶数）なら、そのゲートは偶置換。 -/
theorem sign_gate_eq_one (π : Perm B) (h : Even (Fintype.card A)) :
    sign (prodCongrRight fun _ : A => π) = 1 := by
  rw [sign_gate_pow]
  rcases Int.units_eq_one_or (sign π) with hs | hs
  · simp [hs]
  · rw [hs]; exact h.neg_one_pow

/-- ビット模型での言い換え: 対象線が `k` 本、非対象線が `m ≥ 1` 本なら
非対象線側の濃度は $2^m$ で偶数。 -/
theorem card_nontarget_even (m : ℕ) (hm : 1 ≤ m) :
    Even (Fintype.card (Fin m → Bool)) := by
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  exact (Nat.even_pow' (by omega)).mpr even_two

/-- ゲート集合（arity が真に小さいゲートたち）が生成する部分群は
符号写像の核に含まれる。すなわち **有限個のそのようなゲートをいくら合成しても奇置換は作れない**。 -/
theorem closure_gates_le_ker_sign (Gs : Set (Perm (A × B)))
    (h : ∀ σ ∈ Gs, sign σ = 1) :
    Subgroup.closure Gs ≤ (sign : Perm (A × B) →* ℤˣ).ker := by
  rw [Subgroup.closure_le]
  intro σ hσ
  simpa [MonoidHom.mem_ker] using h σ hσ

/-- 系: 奇置換は arity が真に小さいゲートだけでは実現できない
（= ガベージ／アンシラ線を 1 本増やす必要がある）。 -/
theorem odd_perm_not_in_closure (Gs : Set (Perm (A × B)))
    (h : ∀ σ ∈ Gs, sign σ = 1) (τ : Perm (A × B)) (hτ : sign τ = -1) :
    τ ∉ Subgroup.closure Gs := by
  intro hmem
  have := closure_gates_le_ker_sign Gs h hmem
  rw [MonoidHom.mem_ker, hτ] at this
  exact absurd this (by decide)

end Parity

/-! ## L2 有界全数検査 — 射影ガベージ模型では下界が緩む

Python の全数計算（`scripts/exp10_garbage.py`）と突き合わせる層。 -/

section Bounded

/-- 3 変数多数決。 -/
def maj3 (x : Fin 3 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 0 && x 2)

/-- $\mathrm{MAJ}_3$ のファイバーはどちらも 4 元 → 情報論的下界は $\lceil\log_2 4\rceil = 2$。 -/
theorem maj3_maxFiber : ∀ y : Bool, (fiber maj3 y).card = 4 := by decide

/-- 自由ガベージ模型では 2 ビットで足りる（明示的な $\gamma$）。
$\gamma(x) = (x_0 \oplus x_2,\; x_1 \oplus x_2)$。 -/
theorem maj3_free_two :
    Function.Injective fun x : Fin 3 → Bool =>
      (maj3 x, (xor (x 0) (x 2), xor (x 1) (x 2))) := by decide

/-- しかし射影ガベージ模型では 3 ビット全部が必要
（= 情報論的下界 2 が緩む。差 1）。 -/
theorem maj3_proj_needs_all_three :
    ∀ S : Fin 3 → Bool, ProjOK maj3 S → ∀ i, S i = true := by decide

/-- 上の系: $|S| \le 2$ のガベージでは $\mathrm{MAJ}_3$ を埋め込めない。 -/
theorem maj3_proj_two_fails (S : Fin 3 → Bool) (h : ∃ i, S i = false) : ¬ ProjOK maj3 S := by
  intro hok
  obtain ⟨i, hi⟩ := h
  simp [maj3_proj_needs_all_three S hok i] at hi

/-! ### 差は 1 で止まらない: $n=3$ に差 2 の例がある

`scripts/exp10_garbage.py` 実験 B で見つけた 4 ブロック分割
$\{000,111\},\{001,101\},\{010,011\},\{100,110\}$（真理値表 `30201123`）。
ファイバーはすべて 2 元なので情報論的下界は 1 だが、射影ガベージは 3 ビット必要。 -/

/-- 上記分割を与える 2 出力関数（値を `Fin 4` で表す）。 -/
def gap2 (x : Fin 3 → Bool) : Fin 4 :=
  match x 0, x 1, x 2 with
  | false, false, false => 3   -- 000
  | true,  true,  true  => 3   -- 111
  | true,  false, false => 0   -- 001（ビット順: x 0 が LSB）
  | true,  false, true  => 0   -- 101
  | false, true,  false => 2   -- 010
  | true,  true,  false => 2   -- 011
  | false, false, true  => 1   -- 100
  | false, true,  true  => 1   -- 110

/-- ファイバーはすべて 2 元 → 情報論的下界は $\lceil\log_2 2\rceil = 1$。 -/
theorem gap2_lb_one : ∀ y : Fin 4, (fiber gap2 y).card = 2 := by decide

/-- 射影ガベージ模型（一般の出力型に拡張した版）。 -/
def ProjOK' {m : Type*} [DecidableEq m] (f : (Fin 3 → Bool) → m) (S : Fin 3 → Bool) : Prop :=
  Function.Injective fun x : Fin 3 → Bool => (f x, fun i => S i && x i)

instance {m : Type*} [DecidableEq m] (f : (Fin 3 → Bool) → m) (S : Fin 3 → Bool) :
    Decidable (ProjOK' f S) := by unfold ProjOK' Function.Injective; infer_instance

/-- それでも射影ガベージは 3 ビット必要 → 下界 1 に対して差 2。 -/
theorem gap2_proj_needs_all_three :
    ∀ S : Fin 3 → Bool, ProjOK' gap2 S → ∀ i, S i = true := by decide

end Bounded

end RevGarbage
