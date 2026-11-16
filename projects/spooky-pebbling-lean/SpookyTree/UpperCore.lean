/-
# 上界の準備: 手のリストの実行・部分木の中のペブル数・層状の配置

上界（構成）は、手の有限リスト `l : List Move` を作り、それが妥当な手順であることを示す形で証明する。
このファイルはその道具をそろえる。

* `run c l`: 配置 `c` から `l` を順に打った後の配置。
* `pc k y c`: 高さ `k` の部分木 `T(y)` の中のペブルの数（木の形に沿った再帰。`pc h [] c = pcount h c`）。
* `Pat f k y c`: `T(y)`（高さ `k`）の、`y` から `i` 段下の頂点の状態がすべて `f i`（層状の配置）。
  構成に現れる配置は、ブロック根から見てすべて層状なので、これ 1 つで足りる。
* `Runs h k y p c l`: `c` から `l` を打つとき、各手は合法で `T(y)` の中にあり、
  各手の直後の `T(y)` 内のペブル数は `p` 以下。
-/
import SpookyTree.Count

namespace SpookyTree

/-! ## 手のリストの実行 -/

/-- 配置 `c` から手のリスト `l` を順に打った後の配置。 -/
def run (c : Config) : List Move → Config
  | [] => c
  | m :: l => run (step c m) l

@[simp] theorem run_nil (c : Config) : run c [] = c := rfl

@[simp] theorem run_cons (c : Config) (m : Move) (l : List Move) :
    run c (m :: l) = run (step c m) l := rfl

theorem run_append (c : Config) (l₁ l₂ : List Move) :
    run c (l₁ ++ l₂) = run (run c l₁) l₂ := by
  induction l₁ generalizing c with
  | nil => rfl
  | cons m l ih => simp only [List.cons_append, run_cons, ih]

theorem step_self (c : Config) (op : Op) (v : Node) : step c ⟨op, v⟩ v = result op := by
  simp [step]

theorem step_ne (c : Config) (op : Op) {v z : Node} (hne : v ≠ z) : step c ⟨op, v⟩ z = c z := by
  simp [step, Function.update, Ne.symm hne]

/-- `l` の手がすべて `T(z)` の中なら、`T(z)` の外の頂点の状態は変わらない。 -/
theorem run_outside {z : Node} {l : List Move} (hl : ∀ m ∈ l, z <+: m.v) (c : Config)
    {x : Node} (hx : ¬ z <+: x) : run c l x = c x := by
  induction l generalizing c with
  | nil => rfl
  | cons m l ih =>
    have hm : z <+: m.v := hl m (by simp)
    rw [run_cons, ih (fun m' hm' => hl m' (List.mem_cons_of_mem _ hm'))]
    obtain ⟨op, v⟩ := m
    exact step_ne c op (fun h => hx (h ▸ hm))

/-! ## 接頭辞の小さな事実 -/

/-- 兄弟の部分木は交わらない。 -/
theorem not_prefix_sib (p : Node) (b : Bool) (w : Node) : ¬ (p ++ [b]) <+: (p ++ [!b]) ++ w := by
  rw [List.append_assoc, List.prefix_append_right_inj]
  cases b <;> simp

/-- 親は子の部分木に入らない。 -/
theorem not_prefix_parent (p : Node) (b : Bool) : ¬ (p ++ [b]) <+: p := by
  intro hp
  have := hp.length_le
  simp at this

/-! ## 部分木の中のペブル数 -/

/-- 高さ `k` の部分木 `T(y)` の中のペブルの数。 -/
def pc : ℕ → Node → Config → ℕ
  | 0, _, _ => 0
  | k + 1, y, c => (if c y = .pebble then 1 else 0) + pc k (y ++ [false]) c + pc k (y ++ [true]) c

/-- `pc k y` は `T(y)` の中の頂点の状態だけで決まる。 -/
theorem pc_congr {c c' : Config} :
    ∀ (k : ℕ) (y : Node), (∀ w : Node, c' (y ++ w) = c (y ++ w)) → pc k y c' = pc k y c := by
  intro k
  induction k with
  | zero => intro y _; rfl
  | succ k ih =>
    intro y hw
    have h0 : c' y = c y := by simpa using hw []
    have hb : ∀ b : Bool, pc k (y ++ [b]) c' = pc k (y ++ [b]) c := fun b =>
      ih (y ++ [b]) (fun w => by simpa using hw (b :: w))
    simp only [pc, h0, hb]

/-- `pc` は `nodes` の上の数え上げと一致する。 -/
theorem pc_eq_card (c : Config) : ∀ (k : ℕ) (y : Node),
    pc k y c = ((nodes k).filter (fun w => c (y ++ w) = .pebble)).card := by
  intro k
  induction k with
  | zero => intro y; simp [pc, nodes]
  | succ k ih =>
    intro y
    have hA : ∀ b : Bool,
        (((nodes k).image (List.cons b)).filter (fun w => c (y ++ w) = .pebble)).card
          = pc k (y ++ [b]) c := by
      intro b
      rw [ih (y ++ [b]), Finset.filter_image,
        Finset.card_image_of_injective _ (List.cons_injective)]
      congr 1
      ext w
      simp
    have hdis : Disjoint
        (((nodes k).image (List.cons false)).filter (fun w => c (y ++ w) = .pebble))
        (((nodes k).image (List.cons true)).filter (fun w => c (y ++ w) = .pebble)) := by
      rw [Finset.disjoint_left]
      intro w h1 h2
      simp only [Finset.mem_filter, Finset.mem_image] at h1 h2
      obtain ⟨⟨a, -, rfl⟩, -⟩ := h1
      obtain ⟨⟨a', -, ha'⟩, -⟩ := h2
      simp at ha'
    have hnil : ([] : Node) ∉
        ((nodes k).image (List.cons false) ∪ (nodes k).image (List.cons true)).filter
          (fun w => c (y ++ w) = .pebble) := by
      simp
    have hU : (((nodes k).image (List.cons false) ∪ (nodes k).image (List.cons true)).filter
        (fun w => c (y ++ w) = .pebble)).card = pc k (y ++ [false]) c + pc k (y ++ [true]) c := by
      rw [Finset.filter_union, Finset.card_union_of_disjoint hdis, hA false, hA true]
    rw [pc, nodes, Finset.filter_insert]
    by_cases hy : c y = .pebble
    · have hy' : c (y ++ []) = Cell.pebble := by rw [List.append_nil]; exact hy
      rw [if_pos hy, if_pos hy', Finset.card_insert_of_notMem hnil, hU]
      omega
    · have hy' : ¬ c (y ++ []) = Cell.pebble := by rw [List.append_nil]; exact hy
      rw [if_neg hy, if_neg hy', hU]
      omega

theorem pc_root (h : ℕ) (c : Config) : pc h [] c = pcount h c := by
  rw [pc_eq_card]; simp [pcount]

/-! ## 層状の配置 -/

/-- `T(y)`（高さ `k`）の、`y` から `i` 段下の頂点の状態がすべて `f i`。 -/
def Pat (f : ℕ → Cell) (k : ℕ) (y : Node) (c : Config) : Prop :=
  ∀ w : Node, w.length < k → c (y ++ w) = f w.length

theorem Pat_congr {f : ℕ → Cell} {k : ℕ} {y : Node} {c c' : Config}
    (hw : ∀ w : Node, c' (y ++ w) = c (y ++ w)) : Pat f k y c' ↔ Pat f k y c := by
  unfold Pat
  constructor <;> intro hP w hk
  · rw [← hw]; exact hP w hk
  · rw [hw]; exact hP w hk

theorem Pat_succ {f : ℕ → Cell} {k : ℕ} {y : Node} {c : Config} :
    Pat f (k + 1) y c ↔ c y = f 0 ∧ Pat (fun i => f (i + 1)) k (y ++ [false]) c ∧
      Pat (fun i => f (i + 1)) k (y ++ [true]) c := by
  constructor
  · intro hP
    refine ⟨by simpa using hP [] (by simp), ?_, ?_⟩
    · intro w hw; simpa using hP (false :: w) (by simpa using hw)
    · intro w hw; simpa using hP (true :: w) (by simpa using hw)
  · rintro ⟨h0, h1, h2⟩ w hw
    match w with
    | [] => simpa using h0
    | false :: w => simpa using h1 w (by simpa using hw)
    | true :: w => simpa using h2 w (by simpa using hw)

/-- 層状の配置のペブル数。 -/
def pcPat (f : ℕ → Cell) : ℕ → ℕ
  | 0 => 0
  | k + 1 => (if f 0 = .pebble then 1 else 0) + 2 * pcPat (fun i => f (i + 1)) k

theorem pc_of_Pat {c : Config} :
    ∀ (k : ℕ) (f : ℕ → Cell) (y : Node), Pat f k y c → pc k y c = pcPat f k := by
  intro k
  induction k with
  | zero => intro f y _; rfl
  | succ k ih =>
    intro f y hP
    obtain ⟨h0, h1, h2⟩ := Pat_succ.mp hP
    simp only [pc, pcPat, h0, ih _ _ h1, ih _ _ h2]
    ring

/-- 全部同じ状態。 -/
def cst (X : Cell) : ℕ → Cell := fun _ => X

/-- 上の `L` 段は `ci`、その下は `g`。 -/
def glue (ci : Cell) (L : ℕ) (g : ℕ → Cell) : ℕ → Cell := fun i => if i < L then ci else g (i - L)

/-- 根だけペブルで、その下は全部ゴースト。 -/
def scp : ℕ → Cell := glue .pebble 1 (cst .ghost)

@[simp] theorem glue_zero (ci : Cell) (g : ℕ → Cell) : glue ci 0 g = g := by
  funext i; simp [glue]

@[simp] theorem glue_succ_zero (ci : Cell) (L : ℕ) (g : ℕ → Cell) : glue ci (L + 1) g 0 = ci := by
  simp [glue]

theorem glue_succ_shift (ci : Cell) (L : ℕ) (g : ℕ → Cell) :
    (fun i => glue ci (L + 1) g (i + 1)) = glue ci L g := by
  funext i; simp [glue]

@[simp] theorem glue_cst (X : Cell) (L : ℕ) : glue X L (cst X) = cst X := by
  funext i; simp [glue, cst]

@[simp] theorem cst_apply (X : Cell) (i : ℕ) : cst X i = X := rfl

theorem cst_shift (X : Cell) : (fun i => cst X (i + 1)) = cst X := rfl

@[simp] theorem scp_zero : scp 0 = .pebble := by simp [scp, glue]

theorem scp_shift : (fun i => scp (i + 1)) = cst .ghost := by
  funext i; simp [scp, glue]

theorem pcPat_cst {X : Cell} (hX : X ≠ .pebble) : ∀ k : ℕ, pcPat (cst X) k = 0 := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => rw [pcPat, cst_shift, ih, cst_apply, if_neg hX]

theorem pcPat_scp (k : ℕ) : pcPat scp (k + 1) = 1 := by
  rw [pcPat, scp_zero, scp_shift, if_pos rfl, pcPat_cst (X := .ghost) (by decide)]

theorem pcPat_glue_ne {ci : Cell} (hci : ci ≠ .pebble) (g : ℕ → Cell) (j : ℕ) :
    ∀ L : ℕ, pcPat (glue ci L g) (j + L) = 2 ^ L * pcPat g j := by
  intro L
  induction L with
  | zero => simp
  | succ L ih =>
    rw [← Nat.add_assoc, pcPat, glue_succ_zero, glue_succ_shift, ih, if_neg hci, pow_succ]
    ring

theorem pcPat_glue_peb (g : ℕ → Cell) (j : ℕ) :
    ∀ L : ℕ, pcPat (glue .pebble L g) (j + L) + 1 = 2 ^ L * (pcPat g j + 1) := by
  intro L
  induction L with
  | zero => simp
  | succ L ih =>
    rw [← Nat.add_assoc, pcPat, glue_succ_zero, glue_succ_shift, if_pos rfl, pow_succ]
    linarith

theorem pcPat_glue_le (X : Cell) (g : ℕ → Cell) :
    ∀ n L : ℕ, pcPat (glue X L g) n ≤ pcPat (glue .pebble L g) n := by
  intro n
  induction n with
  | zero => intro L; exact le_rfl
  | succ n ih =>
    intro L
    cases L with
    | zero => simp
    | succ L =>
      rw [pcPat, pcPat, glue_succ_zero, glue_succ_zero, glue_succ_shift, glue_succ_shift, if_pos rfl]
      have := ih L
      split_ifs <;> omega

/-- 高さがブロック幅以下なら、`glue` の下の部分は見えない。 -/
theorem Pat_glue_short {X : Cell} {L n : ℕ} (g : ℕ → Cell) (hn : n ≤ L) {y : Node} {c : Config} :
    Pat (glue X L g) n y c ↔ Pat (cst X) n y c := by
  unfold Pat
  constructor <;> intro hP w hw
  · have := hP w hw
    simpa [glue, show w.length < L by omega] using this
  · have := hP w hw
    simpa [glue, show w.length < L by omega] using this

/-- 全部 `X` の配置から、個々の頂点の状態を取り出す。 -/
theorem Pat_cst_apply {X : Cell} {k : ℕ} {y : Node} {c : Config} (hP : Pat (cst X) k y c)
    (w : Node) (hw : w.length < k) : c (y ++ w) = X := hP w hw

/-! ## 合法な実行と、部分木の中のペブル数の上限 -/

/-- `c` から `l` を順に打つ: 各手は合法で `T(y)` の中にあり、各手の直後の `T(y)`（高さ `k`）内の
ペブル数は `p` 以下。 -/
def Runs (h k : ℕ) (y : Node) (p : ℕ) : Config → List Move → Prop
  | _, [] => True
  | c, m :: l => Legal h c m ∧ y <+: m.v ∧ pc k y (step c m) ≤ p ∧ Runs h k y p (step c m) l

theorem Runs_nil {h k : ℕ} {y : Node} {p : ℕ} {c : Config} : Runs h k y p c [] := by
  unfold Runs; trivial

theorem Runs_cons {h k : ℕ} {y : Node} {p : ℕ} {c : Config} {m : Move} {l : List Move} :
    Runs h k y p c (m :: l) ↔
      Legal h c m ∧ y <+: m.v ∧ pc k y (step c m) ≤ p ∧ Runs h k y p (step c m) l := by
  constructor <;> intro hR
  · unfold Runs at hR; exact hR
  · unfold Runs; exact hR

theorem Runs_append {h k : ℕ} {y : Node} {p : ℕ} :
    ∀ {l₁ l₂ : List Move} {c : Config},
    Runs h k y p c (l₁ ++ l₂) ↔ Runs h k y p c l₁ ∧ Runs h k y p (run c l₁) l₂ := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ c; simp [Runs_nil]
  | cons m l ih =>
    intro l₂ c
    simp only [List.cons_append, Runs_cons, run_cons, ih]
    tauto

theorem Runs.mono {h k : ℕ} {y : Node} {p q : ℕ} (hpq : p ≤ q) :
    ∀ {l : List Move} {c : Config}, Runs h k y p c l → Runs h k y q c l := by
  intro l
  induction l with
  | nil => intro c _; exact Runs_nil
  | cons m l ih =>
    intro c hR
    obtain ⟨h1, h2, h3, h4⟩ := Runs_cons.mp hR
    exact Runs_cons.mpr ⟨h1, h2, le_trans h3 hpq, ih h4⟩

theorem Runs.under {h k : ℕ} {y : Node} {p : ℕ} :
    ∀ {l : List Move} {c : Config}, Runs h k y p c l → ∀ m ∈ l, y <+: m.v := by
  intro l
  induction l with
  | nil => intro c _ m hm; simp at hm
  | cons m l ih =>
    intro c hR m' hm'
    obtain ⟨-, h2, -, h4⟩ := Runs_cons.mp hR
    rcases List.mem_cons.mp hm' with rfl | hin
    · exact h2
    · exact ih h4 m' hin

/-- 子の部分木の中の実行を、親の部分木の実行に持ち上げる。親自身と兄弟の部分木のペブルは動かない。 -/
theorem Runs.lift {h k : ℕ} {y : Node} {b : Bool} {p q : ℕ} :
    ∀ {l : List Move} {c : Config}, Runs h k (y ++ [b]) p c l →
    (if c y = .pebble then 1 else 0) + pc k (y ++ [!b]) c ≤ q → Runs h (k + 1) y (p + q) c l := by
  intro l
  induction l with
  | nil => intro c _ _; exact Runs_nil
  | cons m l ih =>
    intro c hR hq
    obtain ⟨hL, hpre, hpc, hR'⟩ := Runs_cons.mp hR
    obtain ⟨op, v⟩ := m
    have hyv : y <+: v := (List.prefix_append y [b]).trans hpre
    have hne : v ≠ y := fun e => not_prefix_parent y b (e ▸ hpre)
    have hcy : step c ⟨op, v⟩ y = c y := step_ne c op hne
    have hsib : pc k (y ++ [!b]) (step c ⟨op, v⟩) = pc k (y ++ [!b]) c :=
      pc_congr k _ (fun w => step_ne c op (fun e => not_prefix_sib y b w (e ▸ hpre)))
    refine Runs_cons.mpr ⟨hL, hyv, ?_, ih hR' (by rw [hcy, hsib]; exact hq)⟩
    rw [pc, hcy]
    cases b with
    | false =>
      have hs : pc k (y ++ [true]) (step c ⟨op, v⟩) = pc k (y ++ [true]) c := hsib
      have hq' : (if c y = .pebble then 1 else 0) + pc k (y ++ [true]) c ≤ q := hq
      omega
    | true =>
      have hs : pc k (y ++ [false]) (step c ⟨op, v⟩) = pc k (y ++ [false]) c := hsib
      have hq' : (if c y = .pebble then 1 else 0) + pc k (y ++ [false]) c ≤ q := hq
      omega

/-- 手が `T(z)` の中だけなら、`T(z)` と交わらない部分木の層状の配置は保たれる。 -/
theorem Pat_run_disj {z y : Node} {l : List Move} (hl : ∀ m ∈ l, z <+: m.v)
    (hd : ∀ w : Node, ¬ z <+: y ++ w) {f : ℕ → Cell} {k : ℕ} {c : Config} :
    Pat f k y (run c l) ↔ Pat f k y c :=
  Pat_congr (fun w => run_outside hl c (hd w))

theorem pc_run_disj {z y : Node} {l : List Move} (hl : ∀ m ∈ l, z <+: m.v)
    (hd : ∀ w : Node, ¬ z <+: y ++ w) (k : ℕ) (c : Config) :
    pc k y (run c l) = pc k y c :=
  pc_congr k y (fun w => run_outside hl c (hd w))

/-- 1 手 `⟨op, v⟩` が `T(y)` の外なら、`T(y)` の層状の配置は保たれる。 -/
theorem Pat_step_out {y v : Node} (hv : ¬ y <+: v) {f : ℕ → Cell} {k : ℕ} {c : Config} (op : Op) :
    Pat f k y (step c ⟨op, v⟩) ↔ Pat f k y c :=
  Pat_congr (fun w => step_ne c op (fun e => hv (e ▸ List.prefix_append y w)))

theorem pc_step_out {y v : Node} (hv : ¬ y <+: v) (k : ℕ) (c : Config) (op : Op) :
    pc k y (step c ⟨op, v⟩) = pc k y c :=
  pc_congr k y (fun w => step_ne c op (fun e => hv (e ▸ List.prefix_append y w)))

/-- 子は親の接頭辞ではない。 -/
theorem not_child_prefix (y : Node) (b : Bool) : ¬ (y ++ [b]) <+: y := not_prefix_parent y b

theorem disj01 (y w : Node) : ¬ (y ++ [false]) <+: (y ++ [true]) ++ w := not_prefix_sib y false w

theorem disj10 (y w : Node) : ¬ (y ++ [true]) <+: (y ++ [false]) ++ w := not_prefix_sib y true w

theorem Runs.lift0 {h k : ℕ} {y : Node} {p q : ℕ} {l : List Move} {c : Config}
    (hR : Runs h k (y ++ [false]) p c l)
    (hq : (if c y = .pebble then 1 else 0) + pc k (y ++ [true]) c ≤ q) :
    Runs h (k + 1) y (p + q) c l := Runs.lift (b := false) hR hq

theorem Runs.lift1 {h k : ℕ} {y : Node} {p q : ℕ} {l : List Move} {c : Config}
    (hR : Runs h k (y ++ [true]) p c l)
    (hq : (if c y = .pebble then 1 else 0) + pc k (y ++ [false]) c ≤ q) :
    Runs h (k + 1) y (p + q) c l := Runs.lift (b := true) hR hq

/-- 上の `L` 段が `ci`、その下が `g` の配置のペブル数の上界。`e` は `ci` がペブルなら 1。 -/
theorem pcPat_glue_bound {ci : Cell} {g : ℕ → Cell} {j w e : ℕ} (hw : pcPat g j ≤ w)
    (he : (if ci = .pebble then 1 else 0) ≤ e) :
    ∀ L : ℕ, pcPat (glue ci L g) (j + L) ≤ (2 ^ L - 1) * e + 2 ^ L * w := by
  intro L
  induction L with
  | zero => simpa using hw
  | succ L ih =>
    rw [← Nat.add_assoc, pcPat, glue_succ_zero, glue_succ_shift]
    obtain ⟨a, ha⟩ : ∃ a, 2 ^ L = a + 1 :=
      ⟨2 ^ L - 1, by have := Nat.one_le_two_pow (n := L); omega⟩
    rw [pow_succ]
    rw [ha] at ih ⊢
    have h1 : a + 1 - 1 = a := by omega
    have h2 : (a + 1) * 2 - 1 = 2 * a + 1 := by omega
    rw [h1] at ih
    rw [h2]
    nlinarith [ih, he]

theorem glue_peb_zero {L : ℕ} {g : ℕ → Cell} (hg : L = 0 → g 0 = .pebble) :
    glue .pebble L g 0 = .pebble := by
  cases L with
  | zero => simpa using hg rfl
  | succ L => simp

end SpookyTree
