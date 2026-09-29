/-
# 完全二分木の spooky pebble game と、補題 R・補題 F

規則は `SpookyPebbling/Defs.lean`（鎖）と同じ型の 4 操作。前提条件だけが木になる:
頂点 `v` が「揃っている」⇔ `v` が葉（`h ≤ |v| + 1`）か、両方の子がペブル。
`ghost` は前提なし（子が揃っていても打てる）なので、KSS Def 2.6/2.7 より**広い**。
広いモデルでの最小手数は KSS の最小手数以下なので、**ここで示す下界は KSS の意味論にもそのまま移る**。

手順は `ms : ℕ → Move` の先頭 `T` 手。`st ms t` は `t` 手打った後の配置。
妥当な手順（`Valid`）: 各手が合法で、全ての時刻でペブル数が上限以下。
-/
import SpookyTree.Tree

namespace SpookyTree

inductive Cell where
  | empty | pebble | ghost
  deriving DecidableEq, Repr, Inhabited

inductive Op where
  | pebble | unpebble | ghost | unghost
  deriving DecidableEq, Repr, Inhabited

structure Move where
  op : Op
  v : Node
  deriving DecidableEq, Repr, Inhabited

abbrev Config := Node → Cell

def result : Op → Cell
  | .pebble => .pebble
  | .unpebble => .empty
  | .ghost => .ghost
  | .unghost => .pebble

def step (c : Config) (m : Move) : Config := Function.update c m.v (result m.op)

/-- `v` が揃っている: 葉か、両方の子がペブル。 -/
def Ready (h : ℕ) (c : Config) (v : Node) : Prop :=
  h ≤ v.length + 1 ∨ (c (v ++ [false]) = .pebble ∧ c (v ++ [true]) = .pebble)

def Legal (h : ℕ) (c : Config) (m : Move) : Prop :=
  m.v.length < h ∧
  match m.op with
  | .pebble => c m.v = .empty ∧ Ready h c m.v
  | .unpebble => c m.v = .pebble ∧ Ready h c m.v
  | .ghost => c m.v = .pebble
  | .unghost => c m.v = .ghost ∧ Ready h c m.v

/-- 高さ `h` の木の上のペブルの数。 -/
def pcount (h : ℕ) (c : Config) : ℕ := ((nodes h).filter (fun l => c l = .pebble)).card

/-- `t` 手打った後の配置（始状態は全部空）。 -/
def st (ms : ℕ → Move) : ℕ → Config
  | 0 => fun _ => .empty
  | t + 1 => step (st ms t) (ms t)

/-- 妥当な手順: 先頭 `T` 手が合法で、時刻 `0..T` でペブル数 `≤ cap`、終状態は根だけペブルで他は空。 -/
structure Valid (h cap T : ℕ) (ms : ℕ → Move) : Prop where
  legal : ∀ t < T, Legal h (st ms t) (ms t)
  cap_le : ∀ t ≤ T, pcount h (st ms t) ≤ cap
  root : st ms T [] = .pebble
  others : ∀ l : Node, l.length < h → l ≠ [] → st ms T l = .empty

/-- 置く手（pebble か unghost）。 -/
def IsPlace (m : Move) : Prop := m.op = .pebble ∨ m.op = .unghost

instance : DecidablePred IsPlace := fun m => inferInstanceAs (Decidable (_ ∨ _))

theorem st_succ_ne {ms : ℕ → Move} {t : ℕ} {v : Node} (hv : (ms t).v ≠ v) :
    st ms (t + 1) v = st ms t v := by
  simp [st, step, Function.update, Ne.symm hv]

theorem st_succ_eq {ms : ℕ → Move} {t : ℕ} : st ms (t + 1) (ms t).v = result (ms t).op := by
  simp [st, step]

/-- 状態が「ペブルでない」から「ペブル」に変わったなら、その手はその頂点への置く手。 -/
theorem place_of_change {ms : ℕ → Move} {t : ℕ} {v : Node}
    (h0 : st ms t v ≠ .pebble) (h1 : st ms (t + 1) v = .pebble) :
    (ms t).v = v ∧ IsPlace (ms t) := by
  by_cases hv : (ms t).v = v
  · subst hv
    refine ⟨rfl, ?_⟩
    rw [st_succ_eq] at h1
    unfold IsPlace
    cases hop : (ms t).op <;> simp_all [result]
  · rw [st_succ_ne hv] at h1; exact absurd h1 h0

/-- 離散の中間値: `¬P g` かつ `P t`（`g ≤ t`）なら、`[g, t)` のどこかで `¬P i ∧ P (i+1)`。 -/
theorem exists_cross {P : ℕ → Prop} {g t : ℕ} (hgt : g ≤ t) (hg : ¬P g) (ht : P t) :
    ∃ i, g ≤ i ∧ i < t ∧ ¬P i ∧ P (i + 1) := by
  induction t, hgt using Nat.le_induction with
  | base => exact absurd ht hg
  | succ t hle ih =>
    by_cases hPt : P t
    · obtain ⟨i, h1, h2, h3, h4⟩ := ih hPt
      exact ⟨i, h1, by omega, h3, h4⟩
    · exact ⟨t, hle, by omega, hPt, ht⟩

/-! ## 補題 R: 空になった部分木は、根が再び乗るまでに全頂点が置き直される -/

/-- **補題 R.** 時刻 `g` に部分木 `T(c)` にペブルが無く、時刻 `t ≥ g` に `c` がペブルなら、
`T(c)` の各頂点 `z` への置く手が `[g, t)` の中にある。 -/
theorem lemmaR {h cap T : ℕ} {ms : ℕ → Move} (hV : Valid h cap T ms) :
    ∀ (k : ℕ) (c : Node), h - c.length = k → c.length < h →
    ∀ g t, g ≤ t → t ≤ T →
    (∀ z ∈ subtree h c, st ms g z ≠ .pebble) → st ms t c = .pebble →
    ∀ z ∈ subtree h c, ∃ i, g ≤ i ∧ i < t ∧ (ms i).v = z ∧ IsPlace (ms i) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro c hk hc g t hgt htT hfree hct z hz
  have hcself : c ∈ subtree h c := mem_subtree.mpr ⟨hc, List.prefix_refl c⟩
  obtain ⟨i, hgi, hit, hi0, hi1⟩ :=
    exists_cross (P := fun s => st ms s c = .pebble) hgt (hfree c hcself) hct
  obtain ⟨hmv, hplace⟩ := place_of_change hi0 hi1
  by_cases hzc : z = c
  · subst hzc; exact ⟨i, hgi, hit, hmv, hplace⟩
  · -- z は子 c ++ [b] の部分木にある
    obtain ⟨hzl, hpz⟩ := mem_subtree.mp hz
    obtain ⟨b, hb⟩ := prefix_child hpz hzc
    have hbl : (c ++ [b]).length ≤ z.length := hb.length_le
    have hcl : (c ++ [b]).length < h := lt_of_le_of_lt hbl hzl
    -- 手 i は c に打つ置く手なので、状態 i で c は揃っている。c は葉でないので子はペブル
    have hready : Ready h (st ms i) c := by
      have hL := (hV.legal i (by omega)).2
      rw [hmv] at hL
      rcases hplace with hop | hop <;> rw [hop] at hL <;> exact hL.2
    have hchild : st ms i (c ++ [b]) = .pebble := by
      rcases hready with hleaf | ⟨h0, h1⟩
      · simp at hcl; omega
      · cases b <;> assumption
    have hsub : ∀ w ∈ subtree h (c ++ [b]), st ms g w ≠ .pebble := by
      intro w hw
      obtain ⟨hwl, hwp⟩ := mem_subtree.mp hw
      exact hfree w (mem_subtree.mpr ⟨hwl, (List.prefix_append c [b]).trans hwp⟩)
    obtain ⟨j, hgj, hji, hjv, hjp⟩ :=
      ih (h - (c ++ [b]).length) (by simp at hcl ⊢; omega) (c ++ [b]) rfl hcl g i hgi
        (by omega) hsub hchild z (mem_subtree.mpr ⟨hzl, hb⟩)
    exact ⟨j, hgj, by omega, hjv, hjp⟩

/-! ## 補題 F: 根以外の頂点がペブルなら、その子はそれ以後のどこかで両方ペブル -/

/-- 根以外の内部頂点 `u` が時刻 `s ≤ T` にペブルなら、`s ≤ s' < T` のある時刻 `s'` で両方の子がペブル。
（`u` は終状態で空なので、いずれ unpebble されるか、ghost の後に unghost される。どちらも子が揃っている） -/
theorem lemmaF_step {h cap T : ℕ} {ms : ℕ → Move} (hV : Valid h cap T ms) {u : Node}
    (hu : u ≠ []) (hint : u.length + 1 < h) {s : ℕ} (hsT : s ≤ T) (hus : st ms s u = .pebble) :
    ∃ s', s ≤ s' ∧ s' < T ∧ st ms s' (u ++ [false]) = .pebble ∧ st ms s' (u ++ [true]) = .pebble := by
  have hend : st ms T u = .empty := hV.others u (by omega) hu
  obtain ⟨f, hsf, hfT, hf0, hf1⟩ :=
    exists_cross (P := fun r => st ms r u ≠ .pebble) hsT (by simpa using hus) (by simp [hend])
  simp only [not_not] at hf0
  -- 手 f は u に打たれている
  have hmv : (ms f).v = u := by
    by_contra hne; rw [st_succ_ne hne] at hf1; exact hf1 hf0
  have hL := hV.legal f hfT
  unfold Legal at hL
  rw [hmv] at hL
  have hres : st ms (f + 1) u = result (ms f).op := by rw [← hmv]; exact st_succ_eq
  have kids : ∀ r, Ready h (st ms r) u →
      st ms r (u ++ [false]) = .pebble ∧ st ms r (u ++ [true]) = .pebble := by
    intro r hr
    rcases hr with hleaf | hk
    · omega
    · exact hk
  cases hop : (ms f).op with
  | pebble => rw [hop] at hL; rw [hL.2.1] at hf0; exact absurd hf0 (by decide)
  | unghost => rw [hop] at hL; rw [hL.2.1] at hf0; exact absurd hf0 (by decide)
  | unpebble =>
    rw [hop] at hL
    exact ⟨f, hsf, hfT, kids f hL.2.2⟩
  | ghost =>
    -- u は時刻 f+1 で幽霊。終状態では空なので、あとで幽霊でなくなる手（unghost しかない）がある
    have hg : st ms (f + 1) u = .ghost := by rw [hres, hop]; rfl
    obtain ⟨f2, hf2a, hf2b, hf20, hf21⟩ :=
      exists_cross (P := fun r => st ms r u ≠ .ghost) (show f + 1 ≤ T by omega)
        (by simpa using hg) (by simp [hend])
    simp only [not_not] at hf20
    have hmv2 : (ms f2).v = u := by
      by_contra hne; rw [st_succ_ne hne] at hf21; exact hf21 hf20
    have hL2 := hV.legal f2 hf2b
    unfold Legal at hL2
    rw [hmv2] at hL2
    cases hop2 : (ms f2).op with
    | pebble => rw [hop2] at hL2; rw [hL2.2.1] at hf20; exact absurd hf20 (by decide)
    | unpebble => rw [hop2] at hL2; rw [hL2.2.1] at hf20; exact absurd hf20 (by decide)
    | ghost => rw [hop2] at hL2; rw [hL2.2] at hf20; exact absurd hf20 (by decide)
    | unghost =>
      rw [hop2] at hL2
      exact ⟨f2, by omega, hf2b, kids f2 hL2.2.2⟩

/-- **補題 F.** 根以外の `u` が時刻 `s ≤ T` にペブルなら、`T(u)` の各頂点は `s` 以後 `T` 以前のある時刻にペブル。 -/
theorem lemmaF {h cap T : ℕ} {ms : ℕ → Move} (hV : Valid h cap T ms) :
    ∀ (k : ℕ) (u : Node), h - u.length = k → u ≠ [] → u.length < h →
    ∀ s, s ≤ T → st ms s u = .pebble →
    ∀ w ∈ subtree h u, ∃ s', s ≤ s' ∧ s' ≤ T ∧ st ms s' w = .pebble := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro u hk hu hul s hsT hus w hw
  by_cases hwu : w = u
  · subst hwu; exact ⟨s, le_rfl, hsT, hus⟩
  · obtain ⟨hwl, hpw⟩ := mem_subtree.mp hw
    obtain ⟨b, hb⟩ := prefix_child hpw hwu
    have hbl : (u ++ [b]).length ≤ w.length := hb.length_le
    have hint : u.length + 1 < h := by simp at hbl; omega
    obtain ⟨s1, hs1, hs1T, hk0, hk1⟩ := lemmaF_step hV hu hint hsT hus
    have hchild : st ms s1 (u ++ [b]) = .pebble := by cases b <;> assumption
    obtain ⟨s2, h21, h22, h23⟩ :=
      ih (h - (u ++ [b]).length) (by simp; omega) (u ++ [b]) rfl (by simp)
        (by simp; omega) s1 (by omega) hchild w (mem_subtree.mpr ⟨hwl, hb⟩)
    exact ⟨s2, by omega, h22, h23⟩

end SpookyTree
