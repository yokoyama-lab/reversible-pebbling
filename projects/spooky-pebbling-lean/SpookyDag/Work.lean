/-
# 仕事量と手数の厳密な対応（一般のグラフ）

`SpookyTree/Work.lean` の恒等式 `W* = (T*+1)/2 + 2^h − 2` を、全ての頂点が目標の祖先である
任意の有限グラフ（頂点数 `n`）へ移す: **`W* = (T*+1)/2 + (n − 1)`**。

* `unpebble_lower`: 目標以外の各頂点に少なくとも 1 回 unpebble が要る（`n − 1` 回以上）。
  各頂点は一度は置かれ（`anc_placed`）、最後に空になる手は unpebble しかない。
* `valid_msW`・`nUnpebble_msW_le`: 読み替え「あとで同じ頂点に手が来る unpebble を ghost に、
  ゴーストの頂点への pebble を unghost に」で、手数もペブルの位置も変えずに unpebble を `n − 1` 以下にする。
  この向きには祖先の仮定が要らない。
* `work_feasible_iff`: `2W = T + 1 + 2(n − 1)` で手数と仕事量が厳密に対応する。

`Legal` の前提はペブルの位置だけを見る（ゴーストを見ない）ことが読み替えの根拠で、これは
Lee–Lee–Jeong の規則の性質。KSS の規則（ghost は入力が揃わないときだけ）では成り立たない。
-/
import SpookyDag.Count

namespace SpookyDag

-- 補題ごとに `[Fintype V]`・`[DecidableEq V]` の要不要が分かれるので、未使用の警告は止める。
set_option linter.unusedSectionVars false

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- 時刻 `< t` の unpebble の数。 -/
def nUnpebble (ms : ℕ → Move V) (t : ℕ) : ℕ :=
  ((Finset.range t).filter (fun i => (ms i).op = .unpebble)).card

/-- Lee–Lee–Jeong の仕事量: 置く手と unpebble の数。ghost は数えない。 -/
def work (ms : ℕ → Move V) (T : ℕ) : ℕ := nPlace ms T + nUnpebble ms T

/-! ## 下界: 目標以外の各頂点に unpebble が要る -/

/-- 目標以外の祖先 `z` には、`T` より前に unpebble が打たれる。 -/
theorem exists_unpebble {G : Dag V} {cap T : ℕ} {ms : ℕ → Move V} (hV : Valid G cap T ms)
    {z : V} (hz : Anc G z) (hne : z ≠ G.root) :
    ∃ j, j < T ∧ (ms j).op = .unpebble ∧ (ms j).v = z := by
  obtain ⟨i, hiT, hiv, hip⟩ := anc_placed hV hz
  have hi1 : st ms (i + 1) z = .pebble := by
    rw [← hiv, st_succ_eq]
    rcases hip with h1 | h1 <;> rw [h1] <;> rfl
  have hend : st ms T z = .empty := hV.others z hne
  obtain ⟨j, -, hjT, hj0, hj1⟩ :=
    exists_cross (P := fun r => st ms r z = .empty) (show i + 1 ≤ T by omega)
      (by simp [hi1]) hend
  have hjv : (ms j).v = z := by
    by_contra hne'
    rw [st_succ_ne hne'] at hj1
    exact hj0 hj1
  have hres : st ms (j + 1) z = result (ms j).op := by rw [← hjv]; exact st_succ_eq
  rw [hj1] at hres
  refine ⟨j, hjT, ?_, hjv⟩
  cases hop : (ms j).op <;> simp [hop, result] at hres ⊢

/-- **unpebble の下界.** 全ての頂点が目標の祖先なら、unpebble は `n − 1` 回以上。 -/
theorem unpebble_lower {G : Dag V} {cap T : ℕ} {ms : ℕ → Move V} (hV : Valid G cap T ms)
    (hall : ∀ v, Anc G v) : Fintype.card V - 1 ≤ nUnpebble ms T := by
  have hcover : Finset.univ.erase G.root ⊆
      ((Finset.range T).filter (fun i => (ms i).op = .unpebble)).image (fun i => (ms i).v) := by
    intro z hz
    have hne := (Finset.mem_erase.mp hz).1
    obtain ⟨j, hjT, hop, hjv⟩ := exists_unpebble hV (hall z) hne
    exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjT, hop⟩, hjv⟩
  have h1 := le_trans (Finset.card_le_card hcover) Finset.card_image_le
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ] at h1
  unfold nUnpebble
  omega

/-! ## 上界: unpebble を ghost に読み替える -/

/-- 読み替え: あとで同じ頂点に手が来る unpebble は ghost に、ゴーストの頂点への pebble は unghost に。 -/
def tweakW (ms : ℕ → Move V) (T : ℕ) (c : Config V) (t : ℕ) (m : Move V) : Move V :=
  match m.op with
  | .unpebble => if ∃ t' ∈ Finset.Ioo t T, (ms t').v = m.v then ⟨.ghost, m.v⟩ else m
  | .pebble => if c m.v = .ghost then ⟨.unghost, m.v⟩ else m
  | _ => m

/-- 読み替えた手順の配置。 -/
def stW (ms : ℕ → Move V) (T : ℕ) : ℕ → Config V
  | 0 => fun _ => .empty
  | t + 1 => step (stW ms T t) (tweakW ms T (stW ms T t) t (ms t))

/-- 読み替えた手順。 -/
def msW (ms : ℕ → Move V) (T : ℕ) : ℕ → Move V := fun t => tweakW ms T (stW ms T t) t (ms t)

theorem st_msW (ms : ℕ → Move V) (T : ℕ) : ∀ t, st (msW ms T) t = stW ms T t := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
    show step (st (msW ms T) t) (msW ms T t) = step (stW ms T t) (tweakW ms T (stW ms T t) t (ms t))
    rw [ih]
    rfl

/-- 不変条件: 食い違うのは、元が空で新がゴーストで、その頂点に時刻 `t` 以後 `T` より前に手が来る場合だけ。 -/
def InvW (ms : ℕ → Move V) (T t : ℕ) (c c' : Config V) : Prop :=
  ∀ v, c' v = c v ∨ (c v = .empty ∧ c' v = .ghost ∧ ∃ t', t ≤ t' ∧ t' < T ∧ (ms t').v = v)

theorem InvW.peb_iff {ms : ℕ → Move V} {T t : ℕ} {c c' : Config V} (hI : InvW ms T t c c') (v : V) :
    c v = .pebble ↔ c' v = .pebble := by
  rcases hI v with h | ⟨h1, h2, -⟩
  · rw [h]
  · rw [h1, h2]; decide

theorem InvW.ready {G : Dag V} {ms : ℕ → Move V} {T t : ℕ} {c c' : Config V}
    (hI : InvW ms T t c c') (v : V) : Ready G c v ↔ Ready G c' v := by
  unfold Ready
  exact forall_congr' fun u => imp_congr_right fun _ => hI.peb_iff u

theorem InvW.pcount_eq {ms : ℕ → Move V} {T t : ℕ} {c c' : Config V} (hI : InvW ms T t c c') :
    pcount c = pcount c' := by
  unfold pcount
  congr 1
  ext l
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact hI.peb_iff l

theorem invW_update {ms : ℕ → Move V} {T t : ℕ} {c c' : Config V} {v : V} {x x' : Cell}
    (hI : InvW ms T t c c') (hv : (ms t).v = v)
    (hx : x' = x ∨ (x = .empty ∧ x' = .ghost ∧ ∃ t', t + 1 ≤ t' ∧ t' < T ∧ (ms t').v = v)) :
    InvW ms T (t + 1) (Function.update c v x) (Function.update c' v x') := by
  intro w
  by_cases hw : w = v
  · subst hw
    simpa using hx
  · have e1 : Function.update c v x w = c w := by simp [Function.update, hw]
    have e2 : Function.update c' v x' w = c' w := by simp [Function.update, hw]
    rw [e1, e2]
    rcases hI w with h | ⟨h1, h2, t', ht1, ht2, ht3⟩
    · exact Or.inl h
    · have hne : t' ≠ t := by
        rintro rfl
        exact hw (ht3.symm.trans hv)
      exact Or.inr ⟨h1, h2, t', by omega, ht2, ht3⟩

/-- **1 手の読み替え.** 元の手が合法なら読み替えた手も合法で、不変条件は保たれる。 -/
theorem invW_step {G : Dag V} {T t : ℕ} {ms : ℕ → Move V} {c c' : Config V}
    (hI : InvW ms T t c c') (hL : Legal G c (ms t)) :
    Legal G c' (tweakW ms T c' t (ms t)) ∧
      InvW ms T (t + 1) (step c (ms t)) (step c' (tweakW ms T c' t (ms t))) := by
  rcases hm : ms t with ⟨op, v⟩
  rw [hm] at hL
  have hmv : (ms t).v = v := by rw [hm]
  cases op with
  | pebble =>
    obtain ⟨hc, hr⟩ : c v = .empty ∧ Ready G c v := hL
    have hr' := (hI.ready (G := G) v).mp hr
    by_cases hg : c' v = .ghost
    · have ht : tweakW ms T c' t ⟨.pebble, v⟩ = ⟨.unghost, v⟩ := by simp [tweakW, hg]
      rw [ht]
      exact ⟨And.intro hg hr', invW_update hI hmv (Or.inl rfl)⟩
    · have ht : tweakW ms T c' t ⟨.pebble, v⟩ = ⟨.pebble, v⟩ := by simp [tweakW, hg]
      rw [ht]
      have hc' : c' v = .empty := by
        rcases hI v with h | ⟨-, h2, -⟩
        · rw [h, hc]
        · exact absurd h2 hg
      exact ⟨And.intro hc' hr', invW_update hI hmv (Or.inl rfl)⟩
  | unpebble =>
    obtain ⟨hc, hr⟩ : c v = .pebble ∧ Ready G c v := hL
    have hc' : c' v = .pebble := (hI.peb_iff v).mp hc
    by_cases hex : ∃ t' ∈ Finset.Ioo t T, (ms t').v = v
    · have ht : tweakW ms T c' t ⟨.unpebble, v⟩ = ⟨.ghost, v⟩ := by
        show (if ∃ t' ∈ Finset.Ioo t T, (ms t').v = v then (⟨.ghost, v⟩ : Move V)
          else ⟨.unpebble, v⟩) = _
        rw [if_pos hex]
      rw [ht]
      obtain ⟨t', ht', hv'⟩ := hex
      rw [Finset.mem_Ioo] at ht'
      exact ⟨hc', invW_update hI hmv (Or.inr ⟨rfl, rfl, t', by omega, ht'.2, hv'⟩)⟩
    · have ht : tweakW ms T c' t ⟨.unpebble, v⟩ = ⟨.unpebble, v⟩ := by
        show (if ∃ t' ∈ Finset.Ioo t T, (ms t').v = v then (⟨.ghost, v⟩ : Move V)
          else ⟨.unpebble, v⟩) = _
        rw [if_neg hex]
      rw [ht]
      exact ⟨And.intro hc' ((hI.ready (G := G) v).mp hr), invW_update hI hmv (Or.inl rfl)⟩
  | ghost =>
    have hc : c v = .pebble := hL
    have hc' : c' v = .pebble := (hI.peb_iff v).mp hc
    have ht : tweakW ms T c' t ⟨.ghost, v⟩ = ⟨.ghost, v⟩ := rfl
    rw [ht]
    exact ⟨hc', invW_update hI hmv (Or.inl rfl)⟩
  | unghost =>
    obtain ⟨hc, hr⟩ : c v = .ghost ∧ Ready G c v := hL
    have hc' : c' v = .ghost := by
      rcases hI v with h | ⟨h1, -, -⟩
      · rw [h, hc]
      · rw [hc] at h1; exact absurd h1 (by decide)
    have ht : tweakW ms T c' t ⟨.unghost, v⟩ = ⟨.unghost, v⟩ := rfl
    rw [ht]
    exact ⟨And.intro hc' ((hI.ready (G := G) v).mp hr), invW_update hI hmv (Or.inl rfl)⟩

/-- **読み替えた手順も妥当**（手数・ペブル数の上限は同じ）。祖先の仮定は要らない。 -/
theorem valid_msW {G : Dag V} {cap T : ℕ} {ms : ℕ → Move V} (hV : Valid G cap T ms) :
    Valid G cap T (msW ms T) := by
  have hI : ∀ t ≤ T, InvW ms T t (st ms t) (stW ms T t) := by
    intro t
    induction t with
    | zero => intro _ v; exact Or.inl rfl
    | succ t ih =>
      intro ht
      exact (invW_step (ih (by omega)) (hV.legal t (by omega))).2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t ht
    rw [st_msW]
    exact (invW_step (hI t (by omega)) (hV.legal t ht)).1
  · intro t ht
    rw [st_msW, ← (hI t ht).pcount_eq]
    exact hV.cap_le t ht
  · rw [st_msW]
    exact ((hI T le_rfl).peb_iff G.root).mp hV.root
  · intro l hne
    rw [st_msW]
    rcases hI T le_rfl l with h | ⟨-, -, t', h1, h2, -⟩
    · rw [h]; exact hV.others l hne
    · omega

/-- 読み替えた手が unpebble なら、元の手も unpebble で、その頂点には `T` より前にもう手が来ない。 -/
theorem tweakW_unpebble {ms : ℕ → Move V} {T t : ℕ} {c : Config V} {m : Move V}
    (h : (tweakW ms T c t m).op = .unpebble) :
    m.op = .unpebble ∧ ¬ ∃ t' ∈ Finset.Ioo t T, (ms t').v = m.v := by
  obtain ⟨op, v⟩ := m
  cases op with
  | unpebble =>
    by_cases hex : ∃ t' ∈ Finset.Ioo t T, (ms t').v = v
    · have ht : tweakW ms T c t ⟨.unpebble, v⟩ = ⟨.ghost, v⟩ := by
        show (if ∃ t' ∈ Finset.Ioo t T, (ms t').v = v then (⟨.ghost, v⟩ : Move V)
          else ⟨.unpebble, v⟩) = _
        rw [if_pos hex]
      rw [ht] at h
      simp at h
    · exact ⟨rfl, hex⟩
  | pebble =>
    by_cases hg : c v = .ghost
    · have ht : tweakW ms T c t ⟨.pebble, v⟩ = ⟨.unghost, v⟩ := by simp [tweakW, hg]
      rw [ht] at h
      simp at h
    · have ht : tweakW ms T c t ⟨.pebble, v⟩ = ⟨.pebble, v⟩ := by simp [tweakW, hg]
      rw [ht] at h
      simp at h
  | ghost => simp [tweakW] at h
  | unghost => simp [tweakW] at h

/-- 時刻 `a` 以後 `k` より前に `v` へ手が来なければ、`v` の状態は変わらない。 -/
theorem st_stable {ms : ℕ → Move V} {v : V} {a : ℕ} :
    ∀ k, a ≤ k → (∀ i, a ≤ i → i < k → (ms i).v ≠ v) → st ms k v = st ms a v := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => intro _; rfl
  | succ k hak ih =>
    intro hno
    rw [st_succ_ne (hno k hak (by omega))]
    exact ih (fun i h1 h2 => hno i h1 (by omega))

/-- **読み替えた手順の unpebble は `n − 1` 回以下.** 残る unpebble は各頂点への最後の手で、目標には打たれない。 -/
theorem nUnpebble_msW_le {G : Dag V} {cap T : ℕ} {ms : ℕ → Move V} (hV : Valid G cap T ms) :
    nUnpebble (msW ms T) T ≤ Fintype.card V - 1 := by
  unfold nUnpebble
  set U := (Finset.range T).filter (fun i => (msW ms T i).op = .unpebble) with hU
  have key : ∀ i ∈ U, i < T ∧ (ms i).op = .unpebble ∧
      ¬ ∃ t' ∈ Finset.Ioo i T, (ms t').v = (ms i).v := by
    intro i hi
    obtain ⟨hiT, hop⟩ := Finset.mem_filter.mp hi
    have hop' : (tweakW ms T (stW ms T i) i (ms i)).op = .unpebble := hop
    exact ⟨Finset.mem_range.mp hiT, tweakW_unpebble hop'⟩
  have hmap : ∀ i ∈ U, (ms i).v ∈ Finset.univ.erase G.root := by
    intro i hi
    obtain ⟨hiT, hop, hno⟩ := key i hi
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
    intro hroot
    have hs := st_stable (ms := ms) (v := (ms i).v) (a := i + 1) T (by omega)
      (fun j h1 h2 hj => hno ⟨j, Finset.mem_Ioo.mpr ⟨by omega, h2⟩, hj⟩)
    have h1 : st ms (i + 1) (ms i).v = .empty := by rw [st_succ_eq, hop]; rfl
    have hr := hV.root
    rw [← hroot, hs, h1] at hr
    exact absurd hr (by decide)
  have hinj : Set.InjOn (fun i => (ms i).v) (U : Set ℕ) := by
    intro a ha b hb hab
    simp only at hab
    obtain ⟨haT, -, hnoa⟩ := key a (Finset.mem_coe.mp ha)
    obtain ⟨hbT, -, hnob⟩ := key b (Finset.mem_coe.mp hb)
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact hnoa ⟨b, Finset.mem_Ioo.mpr ⟨hlt, hbT⟩, hab.symm⟩
    · exact hnob ⟨a, Finset.mem_Ioo.mpr ⟨hlt, haT⟩, hab⟩
  have hc := Finset.card_le_card_of_injOn (fun i => (ms i).v) (by intro i hi; exact hmap i hi) hinj
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ] at hc
  omega

/-! ## 手数と仕事量の厳密な対応 -/

/-- **仕事量の下界.** 全ての頂点が目標の祖先なら、どの妥当な手順も `2W ≥ T + 1 + 2(n − 1)`。 -/
theorem work_lower {G : Dag V} {cap T : ℕ} {ms : ℕ → Move V} (hV : Valid G cap T ms)
    (hall : ∀ v, Anc G v) : T + 1 + 2 * (Fintype.card V - 1) ≤ 2 * work ms T := by
  have h1 := moves_eq hV
  have h2 := unpebble_lower hV hall
  unfold work
  omega

/-- **読み替えで等号.** 手数・ペブル数の上限を保ったまま `2W = T + 1 + 2(n − 1)` にできる。 -/
theorem work_convert {G : Dag V} {cap T : ℕ} {ms : ℕ → Move V} (hV : Valid G cap T ms)
    (hall : ∀ v, Anc G v) :
    Valid G cap T (msW ms T) ∧ 2 * work (msW ms T) T = T + 1 + 2 * (Fintype.card V - 1) := by
  have hV' := valid_msW hV
  have h1 := moves_eq hV'
  have h2 := unpebble_lower hV' hall
  have h3 := nUnpebble_msW_le hV
  refine ⟨hV', ?_⟩
  unfold work
  omega

/-- **手数と仕事量の対応（一般のグラフ）.** 全ての頂点が目標の祖先なら、ペブル `cap` 個で仕事量
`W` 以下の手順があることと、手数 `T` が `T + 1 + 2(n − 1) ≤ 2W` を満たす手順があることは同値。
したがって `W* = (T* + 1)/2 + (n − 1)`。 -/
theorem work_feasible_iff {G : Dag V} {cap W : ℕ} (hall : ∀ v, Anc G v) :
    (∃ T ms, Valid G cap T ms ∧ work ms T ≤ W) ↔
      (∃ T ms, Valid G cap T ms ∧ T + 1 + 2 * (Fintype.card V - 1) ≤ 2 * W) := by
  constructor
  · rintro ⟨T, ms, hV, hW⟩
    exact ⟨T, ms, hV, le_trans (work_lower hV hall) (by omega)⟩
  · rintro ⟨T, ms, hV, hT⟩
    obtain ⟨hV', he⟩ := work_convert hV hall
    exact ⟨T, msW ms T, hV', by omega⟩

end SpookyDag
