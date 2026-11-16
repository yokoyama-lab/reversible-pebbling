/-
# Lee–Lee–Jeong の仕事量と手数の厳密な対応

Lee–Lee–Jeong（arXiv:2610.09434）は仕事量 `W = #Pebble + #Unpebble` を数える（ゴーストにする手は 0、
ゴーストの頂点に置く手は Pebble に含む）。`Game.lean` の `Valid` は同論文の逐次モデルそのもの
（`ghost` に前提が無い）なので、`W = nPlace + nUnpebble` である。

* `unpebble_lower`: どの妥当な手順も、根以外の各頂点に少なくとも 1 回 unpebble を打つ
  （最後に外す手は ghost にできない。残ったゴーストを消すには置き直すしかないから）。
* `valid_msW`・`nUnpebble_msW_le`: 読み替え「あとで同じ頂点に手が来る unpebble を ghost に、
  その結果ゴーストになった頂点への pebble を unghost に」で、手数もペブルの位置も変えずに
  unpebble を根以外の頂点数 `2^h − 2` 以下にできる。不変条件は「ペブルの位置は一致し、
  食い違うのは元が空・新がゴーストで、その頂点に `T` より前にまだ手が来る場合だけ」。
* `work_feasible_iff`: 手数 `T` と仕事量 `W` は `2W = T + 1 + 2(2^h − 2)` で厳密に対応する
  （最小値どうしでも同じ）。`moves_eq`（`T + 1 = 2 · nPlace`）と合わせた。
* `work_lower_bound_sharp`・`work_upper_bound_sharp`: 係数 2 の手数の上下界（`SharpFinal.lean`）を
  仕事量に移したもの。ペブル `h + 1` 個での最小の仕事量の先頭の係数は 1（`2^h·h/log₂h` を単位として）。
-/
import SpookyTree.SharpFinal

namespace SpookyTree

/-- 時刻 `< t` の unpebble の数。 -/
def nUnpebble (ms : ℕ → Move) (t : ℕ) : ℕ :=
  ((Finset.range t).filter (fun i => (ms i).op = .unpebble)).card

/-- Lee–Lee–Jeong の仕事量: 置く手（pebble・unghost）と unpebble の数。ghost は数えない。 -/
def work (ms : ℕ → Move) (T : ℕ) : ℕ := nPlace ms T + nUnpebble ms T

/-! ## 下界: 根以外の各頂点に unpebble が要る -/

/-- 根以外の頂点 `z` には、`T` より前に unpebble が打たれる。 -/
theorem exists_unpebble {h cap T : ℕ} {ms : ℕ → Move} (hV : Valid h cap T ms) (hh : 1 ≤ h)
    {z : Node} (hz : z.length < h) (hne : z ≠ []) :
    ∃ j, j < T ∧ (ms j).op = .unpebble ∧ (ms j).v = z := by
  have hroot : ([] : Node).length < h := by simp; omega
  -- z は一度は置かれる（補題 R を根と時刻 0 に使う）
  obtain ⟨i, -, hiT, hiv, hip⟩ :=
    lemmaR hV _ [] rfl hroot 0 T (Nat.zero_le _) le_rfl (fun w _ => by simp [st]) hV.root z
      (mem_subtree.mpr ⟨hz, List.nil_prefix⟩)
  have hi1 : st ms (i + 1) z = .pebble := by
    rw [← hiv, st_succ_eq]
    rcases hip with h1 | h1 <;> rw [h1] <;> rfl
  have hend : st ms T z = .empty := hV.others z hz hne
  -- 最後に空になる手は unpebble（ghost の結果はゴースト、置く手の結果はペブル）
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

/-- **unpebble の下界.** どの妥当な手順も unpebble を `2^h − 2` 回以上打つ。 -/
theorem unpebble_lower {h cap T : ℕ} {ms : ℕ → Move} (hV : Valid h cap T ms) (hh : 1 ≤ h) :
    2 ^ h - 2 ≤ nUnpebble ms T := by
  have hcover : (nodes h).erase [] ⊆
      ((Finset.range T).filter (fun i => (ms i).op = .unpebble)).image (fun i => (ms i).v) := by
    intro z hz
    obtain ⟨hne, hzn⟩ := Finset.mem_erase.mp hz
    obtain ⟨j, hjT, hop, hjv⟩ := exists_unpebble hV hh (mem_nodes.mp hzn) hne
    exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjT, hop⟩, hjv⟩
  have h1 := le_trans (Finset.card_le_card hcover) Finset.card_image_le
  rw [Finset.card_erase_of_mem (mem_nodes.mpr (by simp; omega)), card_nodes] at h1
  unfold nUnpebble
  omega

/-! ## 上界: unpebble を ghost に読み替える -/

/-- 読み替え: あとで同じ頂点に手が来る unpebble は ghost に、ゴーストの頂点への pebble は unghost に。 -/
def tweakW (ms : ℕ → Move) (T : ℕ) (c : Config) (t : ℕ) (m : Move) : Move :=
  match m.op with
  | .unpebble => if ∃ t' ∈ Finset.Ioo t T, (ms t').v = m.v then ⟨.ghost, m.v⟩ else m
  | .pebble => if c m.v = .ghost then ⟨.unghost, m.v⟩ else m
  | _ => m

/-- 読み替えた手順の配置。 -/
def stW (ms : ℕ → Move) (T : ℕ) : ℕ → Config
  | 0 => fun _ => .empty
  | t + 1 => step (stW ms T t) (tweakW ms T (stW ms T t) t (ms t))

/-- 読み替えた手順。 -/
def msW (ms : ℕ → Move) (T : ℕ) : ℕ → Move := fun t => tweakW ms T (stW ms T t) t (ms t)

theorem st_msW (ms : ℕ → Move) (T : ℕ) : ∀ t, st (msW ms T) t = stW ms T t := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
    show step (st (msW ms T) t) (msW ms T t) = step (stW ms T t) (tweakW ms T (stW ms T t) t (ms t))
    rw [ih]
    rfl

/-- 不変条件: 食い違うのは、元（`c`）が空で新（`c'`）がゴーストで、その頂点に時刻 `t` 以後 `T` より前に手が来る場合だけ。 -/
def InvW (ms : ℕ → Move) (T t : ℕ) (c c' : Config) : Prop :=
  ∀ v, c' v = c v ∨ (c v = .empty ∧ c' v = .ghost ∧ ∃ t', t ≤ t' ∧ t' < T ∧ (ms t').v = v)

theorem InvW.peb_iff {ms : ℕ → Move} {T t : ℕ} {c c' : Config} (hI : InvW ms T t c c') (v : Node) :
    c v = .pebble ↔ c' v = .pebble := by
  rcases hI v with h | ⟨h1, h2, -⟩
  · rw [h]
  · rw [h1, h2]; decide

theorem InvW.ready {h : ℕ} {ms : ℕ → Move} {T t : ℕ} {c c' : Config} (hI : InvW ms T t c c')
    (v : Node) : Ready h c v ↔ Ready h c' v := by
  unfold Ready
  rw [hI.peb_iff (v ++ [false]), hI.peb_iff (v ++ [true])]

theorem InvW.pcount_eq {h : ℕ} {ms : ℕ → Move} {T t : ℕ} {c c' : Config} (hI : InvW ms T t c c') :
    pcount h c = pcount h c' := by
  unfold pcount
  congr 1
  ext l
  simp only [Finset.mem_filter]
  rw [hI.peb_iff l]

theorem invW_update {ms : ℕ → Move} {T t : ℕ} {c c' : Config} {v : Node} {x x' : Cell}
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
theorem invW_step {h T t : ℕ} {ms : ℕ → Move} {c c' : Config} (hI : InvW ms T t c c')
    (hL : Legal h c (ms t)) :
    Legal h c' (tweakW ms T c' t (ms t)) ∧
      InvW ms T (t + 1) (step c (ms t)) (step c' (tweakW ms T c' t (ms t))) := by
  rcases hm : ms t with ⟨op, v⟩
  rw [hm] at hL
  have hmv : (ms t).v = v := by rw [hm]
  obtain ⟨hv, hop⟩ := hL
  cases op with
  | pebble =>
    obtain ⟨hc, hr⟩ : c v = .empty ∧ Ready h c v := hop
    have hr' := (hI.ready (h := h) v).mp hr
    by_cases hg : c' v = .ghost
    · have ht : tweakW ms T c' t ⟨.pebble, v⟩ = ⟨.unghost, v⟩ := by simp [tweakW, hg]
      rw [ht]
      exact ⟨And.intro hv (And.intro hg hr'), invW_update hI hmv (Or.inl rfl)⟩
    · have ht : tweakW ms T c' t ⟨.pebble, v⟩ = ⟨.pebble, v⟩ := by simp [tweakW, hg]
      rw [ht]
      have hc' : c' v = .empty := by
        rcases hI v with h | ⟨-, h2, -⟩
        · rw [h, hc]
        · exact absurd h2 hg
      exact ⟨And.intro hv (And.intro hc' hr'), invW_update hI hmv (Or.inl rfl)⟩
  | unpebble =>
    obtain ⟨hc, hr⟩ : c v = .pebble ∧ Ready h c v := hop
    have hc' : c' v = .pebble := (hI.peb_iff v).mp hc
    by_cases hex : ∃ t' ∈ Finset.Ioo t T, (ms t').v = v
    · have ht : tweakW ms T c' t ⟨.unpebble, v⟩ = ⟨.ghost, v⟩ := by
        show (if ∃ t' ∈ Finset.Ioo t T, (ms t').v = v then (⟨.ghost, v⟩ : Move)
          else ⟨.unpebble, v⟩) = _
        rw [if_pos hex]
      rw [ht]
      obtain ⟨t', ht', hv'⟩ := hex
      rw [Finset.mem_Ioo] at ht'
      exact ⟨And.intro hv hc', invW_update hI hmv (Or.inr ⟨rfl, rfl, t', by omega, ht'.2, hv'⟩)⟩
    · have ht : tweakW ms T c' t ⟨.unpebble, v⟩ = ⟨.unpebble, v⟩ := by
        show (if ∃ t' ∈ Finset.Ioo t T, (ms t').v = v then (⟨.ghost, v⟩ : Move)
          else ⟨.unpebble, v⟩) = _
        rw [if_neg hex]
      rw [ht]
      exact ⟨And.intro hv (And.intro hc' ((hI.ready v).mp hr)), invW_update hI hmv (Or.inl rfl)⟩
  | ghost =>
    have hc : c v = .pebble := hop
    have hc' : c' v = .pebble := (hI.peb_iff v).mp hc
    have ht : tweakW ms T c' t ⟨.ghost, v⟩ = ⟨.ghost, v⟩ := rfl
    rw [ht]
    exact ⟨And.intro hv hc', invW_update hI hmv (Or.inl rfl)⟩
  | unghost =>
    obtain ⟨hc, hr⟩ : c v = .ghost ∧ Ready h c v := hop
    have hc' : c' v = .ghost := by
      rcases hI v with h | ⟨h1, -, -⟩
      · rw [h, hc]
      · rw [hc] at h1; exact absurd h1 (by decide)
    have ht : tweakW ms T c' t ⟨.unghost, v⟩ = ⟨.unghost, v⟩ := rfl
    rw [ht]
    exact ⟨And.intro hv (And.intro hc' ((hI.ready v).mp hr)), invW_update hI hmv (Or.inl rfl)⟩

/-- **読み替えた手順も妥当**（手数・ペブル数の上限は同じ）。 -/
theorem valid_msW {h cap T : ℕ} {ms : ℕ → Move} (hV : Valid h cap T ms) :
    Valid h cap T (msW ms T) := by
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
    exact ((hI T le_rfl).peb_iff []).mp hV.root
  · intro l hl hne
    rw [st_msW]
    rcases hI T le_rfl l with h | ⟨-, -, t', h1, h2, -⟩
    · rw [h]; exact hV.others l hl hne
    · omega

/-- 読み替えた手が unpebble なら、元の手も unpebble で、その頂点には `T` より前にもう手が来ない。 -/
theorem tweakW_unpebble {ms : ℕ → Move} {T t : ℕ} {c : Config} {m : Move}
    (h : (tweakW ms T c t m).op = .unpebble) :
    m.op = .unpebble ∧ ¬ ∃ t' ∈ Finset.Ioo t T, (ms t').v = m.v := by
  obtain ⟨op, v⟩ := m
  cases op with
  | unpebble =>
    by_cases hex : ∃ t' ∈ Finset.Ioo t T, (ms t').v = v
    · have ht : tweakW ms T c t ⟨.unpebble, v⟩ = ⟨.ghost, v⟩ := by
        show (if ∃ t' ∈ Finset.Ioo t T, (ms t').v = v then (⟨.ghost, v⟩ : Move)
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
theorem st_stable {ms : ℕ → Move} {v : Node} {a : ℕ} :
    ∀ k, a ≤ k → (∀ i, a ≤ i → i < k → (ms i).v ≠ v) → st ms k v = st ms a v := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => intro _; rfl
  | succ k hak ih =>
    intro hno
    rw [st_succ_ne (hno k hak (by omega))]
    exact ih (fun i h1 h2 => hno i h1 (by omega))

/-- **読み替えた手順の unpebble は `2^h − 2` 回以下.** 残る unpebble は各頂点への最後の手で、根には打たれない。 -/
theorem nUnpebble_msW_le {h cap T : ℕ} {ms : ℕ → Move} (hV : Valid h cap T ms) (hh : 1 ≤ h) :
    nUnpebble (msW ms T) T ≤ 2 ^ h - 2 := by
  unfold nUnpebble
  set U := (Finset.range T).filter (fun i => (msW ms T i).op = .unpebble) with hU
  have key : ∀ i ∈ U, i < T ∧ (ms i).op = .unpebble ∧
      ¬ ∃ t' ∈ Finset.Ioo i T, (ms t').v = (ms i).v := by
    intro i hi
    obtain ⟨hiT, hop⟩ := Finset.mem_filter.mp hi
    have hop' : (tweakW ms T (stW ms T i) i (ms i)).op = .unpebble := hop
    exact ⟨Finset.mem_range.mp hiT, tweakW_unpebble hop'⟩
  have hmap : ∀ i ∈ U, (ms i).v ∈ (nodes h).erase [] := by
    intro i hi
    obtain ⟨hiT, hop, hno⟩ := key i hi
    refine Finset.mem_erase.mpr ⟨?_, mem_nodes.mpr (hV.legal i hiT).1⟩
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
  rw [Finset.card_erase_of_mem (mem_nodes.mpr (by simp; omega)), card_nodes] at hc
  omega

/-! ## 手数と仕事量の厳密な対応 -/

/-- **仕事量の下界.** どの妥当な手順も `2W ≥ T + 1 + 2(2^h − 2)`。 -/
theorem work_lower {h cap T : ℕ} {ms : ℕ → Move} (hV : Valid h cap T ms) (hh : 1 ≤ h) :
    T + 1 + 2 * (2 ^ h - 2) ≤ 2 * work ms T := by
  have h1 := moves_eq hV hh
  have h2 := unpebble_lower hV hh
  unfold work
  omega

/-- **読み替えで等号.** 手数・ペブル数の上限を保ったまま `2W = T + 1 + 2(2^h − 2)` にできる。 -/
theorem work_convert {h cap T : ℕ} {ms : ℕ → Move} (hV : Valid h cap T ms) (hh : 1 ≤ h) :
    Valid h cap T (msW ms T) ∧ 2 * work (msW ms T) T = T + 1 + 2 * (2 ^ h - 2) := by
  have hV' := valid_msW hV
  have h1 := moves_eq hV' hh
  have h2 := unpebble_lower hV' hh
  have h3 := nUnpebble_msW_le hV hh
  refine ⟨hV', ?_⟩
  unfold work
  omega

/-- **手数と仕事量の対応.** ペブル `cap` 個で仕事量 `W` 以下の手順があることと、
手数 `T` が `T + 1 + 2(2^h − 2) ≤ 2W` を満たす手順があることは同値。
したがって最小の仕事量 `W*` と最小の手数 `T*` は `W* = (T* + 1)/2 + 2^h − 2`。 -/
theorem work_feasible_iff {h cap W : ℕ} (hh : 1 ≤ h) :
    (∃ T ms, Valid h cap T ms ∧ work ms T ≤ W) ↔
      (∃ T ms, Valid h cap T ms ∧ T + 1 + 2 * (2 ^ h - 2) ≤ 2 * W) := by
  constructor
  · rintro ⟨T, ms, hV, hW⟩
    exact ⟨T, ms, hV, le_trans (work_lower hV hh) (by omega)⟩
  · rintro ⟨T, ms, hV, hT⟩
    obtain ⟨hV', he⟩ := work_convert hV hh
    exact ⟨T, msW ms T, hV', by omega⟩

/-! ## 仕事量での先頭の係数 1 -/

/-- **仕事量の鋭い下界.** ペブル `h + 1` 個の妥当な手順の仕事量は
`W ≥ (2^h − 1) + 2^h · (h − 3⌈log₂(h+1)⌉ − 1) / (log₂(h+1) + 4) + (2^h − 2)`。先頭の係数は 1。 -/
theorem work_lower_bound_sharp {h T : ℕ} {ms : ℕ → Move} (hV : Valid h (h + 1) T ms)
    (hh : 1 ≤ h) :
    ((2 : ℝ) ^ h - 1)
      + 2 ^ h * (((h : ℝ) - (3 * (Nat.clog 2 (h + 1) : ℝ) + 1))
          / (Real.logb 2 ((h : ℝ) + 1) + 4))
      + ((2 : ℝ) ^ h - 2) ≤ work ms T := by
  have hT := time_lower_bound_sharp hV hh
  have hw := work_lower hV hh
  have h2 : 2 ≤ 2 ^ h := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ h := Nat.pow_le_pow_right (by norm_num) hh
  have hwR : ((T : ℝ) + 1) + 2 * ((2 : ℝ) ^ h - 2) ≤ 2 * (work ms T : ℝ) := by
    have := (Nat.cast_le (α := ℝ)).mpr hw
    push_cast [Nat.cast_sub h2] at this
    linarith
  linarith

/-- **仕事量の鋭い上界.** `h ≥ 32`、`lg = ⌊log₂ h⌋`、`ll = ⌊log₂ lg⌋` として、ペブル `h + 1` 個で
`lg · (lg − 2 ll) · (2W + 2) ≤ 2 (lg · h + 4h + lg²) · 2^h + lg · (lg − 2 ll) · 2(2^h − 2)` を満たす手順がある。
すなわち `W ≤ 2^h · h / (lg − 2 ll) · (1 + 4/lg + lg/h) + 2^h`。先頭の係数は 1。 -/
theorem work_upper_bound_sharp {h : ℕ} (hh : 32 ≤ h) :
    ∃ (T : ℕ) (ms : ℕ → Move), Valid h (h + 1) T ms ∧
      Nat.log 2 h * (Nat.log 2 h - 2 * Nat.log 2 (Nat.log 2 h)) * (2 * work ms T + 2)
        ≤ 2 * (Nat.log 2 h * h + 4 * h + Nat.log 2 h * Nat.log 2 h) * 2 ^ h
          + Nat.log 2 h * (Nat.log 2 h - 2 * Nat.log 2 (Nat.log 2 h)) * (2 * (2 ^ h - 2)) := by
  obtain ⟨T, ms, hV, hT⟩ := time_upper_bound_sharp hh
  obtain ⟨hV', he⟩ := work_convert hV (by omega)
  refine ⟨T, msW ms T, hV', ?_⟩
  rw [show 2 * work (msW ms T) T + 2 = (T + 3) + 2 * (2 ^ h - 2) by omega, Nat.mul_add]
  exact Nat.add_le_add_right hT _

end SpookyTree
