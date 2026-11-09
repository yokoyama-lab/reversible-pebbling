import ErasurePebbling.Potential

/-!
# Theorem A (saturation), RC-02 §4

`M*(n, p, e) = 2n − 1  ⇔  e ≥ e*(n, p) = ⌈(n−1)/(p−1)⌉ − 1`   (p ≥ 2).

* Floor (Knill, Observation 2.2(i)): every clean plan has at least
  `2n − 1` moves, because every cell is placed at least once and every
  cell but the last is removed at least once (`floor_length`).
* `⇐` is the block sweep of `Sweep.lean` (`theoremA_upper`).
* `⇒`: a plan with exactly `2n − 1` moves is *tight* — every cell is
  toggled exactly the forced number of times (`tight_of_length`) — and
  along a tight play the potential `pot` of `Potential.lean` never
  drops except by one at an irreversible removal (`pot_le_erasures`).
  Since `pot(empty) = e*(n, p)` and `pot({n}) = 0`, the plan has at
  least `e*(n, p)` erasures.

The tightness invariant `Tight n b s` records, for the remaining moves
`s` from board `b`, how often each cell will still be toggled: a
pebbled cell once (the final cell never), a cell above every pebble
twice (the final cell once), an empty cell below some pebble never.
-/

namespace ErasurePebbling

open RevPebbling.PebblingFoundations

/-! ## Tightness -/

structure Tight (n : Nat) (b : Board) (s : List Nat) : Prop where
  bounds : ∀ i ∈ s, i < n
  peb : ∀ j, j < n → nth b j = true → j ≠ n - 1 → s.count j = 1
  last : nth b (n - 1) = true → s.count (n - 1) = 0
  above : ∀ j, j < n → (∀ j', j ≤ j' → j' < n → nth b j' = false) → j ≠ n - 1 → s.count j = 2
  above_last : nth b (n - 1) = false → s.count (n - 1) = 1
  below : ∀ j, j < n → nth b j = false → (∃ j', j < j' ∧ j' < n ∧ nth b j' = true) → s.count j = 0

/-- If every cell from `i` upwards is empty and `i` is never toggled, then no
move of an admissible play touches a cell `≥ i`. -/
theorem frozen_above (i : Nat) : ∀ (s : List Nat) (b : Board),
    legalE b s = true → (∀ j, i ≤ j → nth b j = false) → i ∉ s → ∀ k ∈ s, k < i := by
  intro s
  induction s with
  | nil => intro _ _ _ _ k hk; simp at hk
  | cons m rest ih =>
      intro b hleg hemp hnot k hk
      have h := hleg
      simp only [legalE_cons, Bool.and_eq_true] at h
      have hm : m < i := by
        rcases Nat.lt_or_ge m i with hlt | hge
        · exact hlt
        · exfalso
          have hne : m ≠ i := fun e => hnot (e ▸ List.mem_cons_self)
          have h1 : nth b m = false := hemp m hge
          have h2 : nth b (m - 1) = false := hemp (m - 1) (by omega)
          have h0 : (m == 0) = false := by simp; omega
          have : okE b m = false := by simp [okE, okMove, h0, h1, h2]
          rw [this] at h; exact absurd h.1 (by simp)
      rcases List.mem_cons.mp hk with rfl | hk'
      · exact hm
      · exact ih (toggle b m) h.2
          (fun j hj => by rw [nth_toggle_ne b (by omega)]; exact hemp j hj)
          (fun h' => hnot (List.mem_cons_of_mem _ h')) k hk'

/-! ## Preservation of tightness -/

theorem tight_remove (n : Nat) (b : Board) (hb : b.length = n) (i : Nat) (rest : List Nat)
    (T : Tight n b (i :: rest)) (hi : i < n) (hpeb : nth b i = true) (hlast : i ≠ n - 1)
    (hnot_top : ∃ j', i < j' ∧ j' < n ∧ nth b j' = true) :
    Tight n (toggle b i) rest := by
  have hib : i < b.length := by omega
  have hself : nth (toggle b i) i = false := by rw [nth_toggle_self b hib, hpeb]; rfl
  have hcnt : rest.count i = 0 := by
    have := T.peb i hi hpeb hlast
    rw [List.count_cons_self] at this; omega
  obtain ⟨j', hij', hj'n, hj'peb⟩ := hnot_top
  refine ⟨fun k hk => T.bounds k (List.mem_cons_of_mem _ hk), ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj hpj hjl
    have hji : j ≠ i := fun e => by rw [e, hself] at hpj; cases hpj
    rw [nth_toggle_ne b (Ne.symm hji)] at hpj
    have := T.peb j hj hpj hjl
    rwa [List.count_cons_of_ne hji.symm] at this
  · intro hpl
    have := T.last (by rwa [nth_toggle_ne b hlast] at hpl)
    rwa [List.count_cons_of_ne hlast] at this
  · intro j hj hab hjl
    have hji : i < j := by
      rcases Nat.lt_or_ge i j with h | h
      · exact h
      · exfalso
        have := hab j' (by omega) hj'n
        rw [nth_toggle_ne b (by omega)] at this
        rw [this] at hj'peb; cases hj'peb
    have := T.above j hj (fun j'' h1 h2 => by
      have := hab j'' h1 h2
      rwa [nth_toggle_ne b (by omega)] at this) hjl
    rwa [List.count_cons_of_ne (by omega)] at this
  · intro hpl
    rw [nth_toggle_ne b hlast] at hpl
    have := T.above_last hpl
    rwa [List.count_cons_of_ne hlast] at this
  · intro j hj hpj ⟨k, hjk, hkn, hpk⟩
    by_cases hji : j = i
    · subst hji; exact hcnt
    · rw [nth_toggle_ne b (Ne.symm hji)] at hpj
      have hki : k ≠ i := fun e => by rw [e, hself] at hpk; cases hpk
      rw [nth_toggle_ne b (Ne.symm hki)] at hpk
      have := T.below j hj hpj ⟨k, hjk, hkn, hpk⟩
      rwa [List.count_cons_of_ne (Ne.symm hji)] at this

theorem tight_place (n : Nat) (b : Board) (hb : b.length = n) (i : Nat) (rest : List Nat)
    (T : Tight n b (i :: rest)) (hi : i < n) (hemp : nth b i = false) (hok : okMove b i = true)
    (habove : ∀ j, i ≤ j → j < n → nth b j = false) :
    Tight n (toggle b i) rest := by
  have hib : i < b.length := by omega
  have hself : nth (toggle b i) i = true := by rw [nth_toggle_self b hib, hemp]; rfl
  refine ⟨fun k hk => T.bounds k (List.mem_cons_of_mem _ hk), ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj hpj hjl
    by_cases hji : j = i
    · subst hji
      have := T.above j hj habove hjl
      rw [List.count_cons_self] at this; omega
    · rw [nth_toggle_ne b (Ne.symm hji)] at hpj
      have := T.peb j hj hpj hjl
      rwa [List.count_cons_of_ne (Ne.symm hji)] at this
  · intro hpl
    by_cases hli : n - 1 = i
    · have := T.above_last (by rw [hli]; exact hemp)
      rw [hli, List.count_cons_self] at this
      rw [hli]; omega
    · rw [nth_toggle_ne b (Ne.symm hli)] at hpl
      have := T.last hpl
      rwa [List.count_cons_of_ne (Ne.symm hli)] at this
  · intro j hj hab hjl
    have hji : i < j := by
      rcases Nat.lt_or_ge i j with h | h
      · exact h
      · exfalso
        have := hab i h hi
        rw [hself] at this; cases this
    have := T.above j hj (fun j'' h1 h2 => by
      have := hab j'' h1 h2
      rwa [nth_toggle_ne b (by omega)] at this) hjl
    rwa [List.count_cons_of_ne (by omega)] at this
  · intro hpl
    have hli : n - 1 ≠ i := fun e => by rw [e, hself] at hpl; cases hpl
    rw [nth_toggle_ne b (Ne.symm hli)] at hpl
    have := T.above_last hpl
    rwa [List.count_cons_of_ne (Ne.symm hli)] at this
  · intro j hj hpj ⟨k, hjk, hkn, hpk⟩
    have hji : j ≠ i := fun e => by rw [e, hself] at hpj; cases hpj
    rw [nth_toggle_ne b (Ne.symm hji)] at hpj
    have hwit : ∃ k', j < k' ∧ k' < n ∧ nth b k' = true := by
      by_cases hki : k = i
      · -- j < i, and cell i − 1 is pebbled (okMove); j ≠ i − 1 since j is empty
        have h0 : i ≠ 0 := by omega
        have hpred : nth b (i - 1) = true := by
          unfold okMove at hok
          have h0' : (i == 0) = false := by simpa using h0
          rw [h0'] at hok; simpa using hok
        have hjp : j ≠ i - 1 := fun e => by rw [e, hpred] at hpj; cases hpj
        exact ⟨i - 1, by omega, by omega, hpred⟩
      · rw [nth_toggle_ne b (Ne.symm hki)] at hpk
        exact ⟨k, hjk, hkn, hpk⟩
    have := T.below j hj hpj hwit
    rwa [List.count_cons_of_ne (Ne.symm hji)] at this

/-! ## The potential along a tight play -/

theorem pot_le_erasures (n p : Nat) (hp : 2 ≤ p) (hn : 1 ≤ n) : ∀ (s : List Nat) (b : Board),
    b.length = n → Tight n b s → legalE b s = true → maxOnes b s ≤ p → execB b s = target n →
    pot n p b ≤ erasures b s := by
  intro s
  induction s with
  | nil =>
      intro b hb _ _ _ hfin
      have : b = target n := hfin
      subst this
      rw [pot_target n p hn hp]; exact Nat.zero_le _
  | cons i rest ih =>
      intro b hb T hleg hpeak hfin
      have hi : i < n := T.bounds i List.mem_cons_self
      have hib : i < b.length := by omega
      simp only [legalE_cons, Bool.and_eq_true] at hleg
      have hpeak' : maxOnes (toggle b i) rest ≤ p := by
        simp only [maxOnes] at hpeak; omega
      have hones : ones b ≤ p := by
        simp only [maxOnes] at hpeak; omega
      have hfin' : execB (toggle b i) rest = target n := hfin
      have hlen' : (toggle b i).length = n := by rw [length_toggle]; exact hb
      rw [erasures_cons]
      cases hpeb : nth b i with
      | true =>
          have hlast : i ≠ n - 1 := by
            intro e
            have := T.last (e ▸ hpeb)
            rw [← e, List.count_cons_self] at this; omega
          by_cases htop : ∃ j', i < j' ∧ j' < n ∧ nth b j' = true
          · have T' := tight_remove n b hb i rest T hi hpeb hlast htop
            have h1 := pot_remove n p hp b hb i hi hpeb htop hones
            have h2 := ih (toggle b i) hlen' T' hleg.2 hpeak' hfin'
            omega
          · exfalso
            -- i is the highest pebble: cell i + 1 can never be placed again
            have hemp : ∀ j, i ≤ j → nth (toggle b i) j = false := by
              intro j hj
              rcases Nat.lt_or_ge j n with hjn | hjn
              · by_cases hji : j = i
                · subst hji; rw [nth_toggle_self b hib, hpeb]; rfl
                · rw [nth_toggle_ne b (Ne.symm hji)]
                  cases h : nth b j
                  · rfl
                  · exact absurd ⟨j, by omega, hjn, h⟩ htop
              · exact nth_ge_length _ j (by rw [length_toggle]; omega)
            have hcnt : rest.count i = 0 := by
              have := T.peb i hi hpeb hlast
              rw [List.count_cons_self] at this; omega
            have hnot : i ∉ rest := List.count_eq_zero.mp hcnt
            have hfro := frozen_above i rest (toggle b i) hleg.2 hemp hnot
            have hi1 : i + 1 < n := by omega
            have hcount : 1 ≤ rest.count (i + 1) := by
              have hab : ∀ j', i + 1 ≤ j' → j' < n → nth b j' = false := by
                intro j' h1 h2
                cases h : nth b j'
                · rfl
                · exact absurd ⟨j', by omega, h2, h⟩ htop
              by_cases hl : i + 1 = n - 1
              · have := T.above_last (by rw [← hl]; exact hab (i + 1) (Nat.le_refl _) hi1)
                rw [← hl, List.count_cons_of_ne (by omega)] at this; omega
              · have := T.above (i + 1) hi1 hab hl
                rw [List.count_cons_of_ne (by omega)] at this; omega
            have hmem : i + 1 ∈ rest := List.count_pos_iff.mp hcount
            have := hfro (i + 1) hmem
            omega
      | false =>
          have hok : okMove b i = true := by
            have := hleg.1
            simp [okE, hpeb] at this
            exact this
          have habove : ∀ j, i ≤ j → j < n → nth b j = false := by
            intro j hj hjn
            by_cases hji : j = i
            · subst hji; exact hpeb
            · cases h : nth b j
              · rfl
              · exfalso
                have := T.below i hi hpeb ⟨j, by omega, hjn, h⟩
                rw [List.count_cons_self] at this; omega
          have T' := tight_place n b hb i rest T hi hpeb hok habove
          have h1 := pot_place n p b hb i hi hpeb hok habove
          have h2 := ih (toggle b i) hlen' T' hleg.2 hpeak' hfin'
          have her : isErase b i = false := by simp [isErase, hpeb]
          rw [her]
          simp only [Bool.false_eq_true, if_false, Nat.zero_add]
          omega

/-! ## Counting toggles: parity, coverage, and the floor `2n − 1` -/

/-- Parity law: the final state of a cell is its initial state flipped by the
parity of the number of moves on it. -/
theorem nth_execB_parity : ∀ (s : List Nat) (b : Board) (j : Nat), j < b.length →
    nth (execB b s) j = xor (nth b j) (decide (s.count j % 2 = 1)) := by
  intro s
  induction s with
  | nil => intro b j _; simp [execB]
  | cons i rest ih =>
      intro b j hj
      have hx : execB b (i :: rest) = execB (toggle b i) rest := rfl
      rw [hx, ih (toggle b i) j (by rw [length_toggle]; exact hj)]
      by_cases hij : i = j
      · subst hij
        rw [nth_toggle_self b hj, List.count_cons_self]
        rcases Nat.mod_two_eq_zero_or_one (rest.count i) with h | h
        · have h' : (rest.count i + 1) % 2 = 1 := by omega
          simp [h, h']
        · have h' : ¬ (rest.count i + 1) % 2 = 1 := by omega
          simp [h, h']
      · rw [nth_toggle_ne b hij, List.count_cons_of_ne hij]

/-- Sums over `j < n`. -/
def rsum : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | k + 1, f => rsum k f + f k

theorem rsum_add (f g : Nat → Nat) : ∀ k, rsum k (fun j => f j + g j) = rsum k f + rsum k g := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => simp only [rsum, ih]; omega

theorem rsum_congr (f g : Nat → Nat) : ∀ k, (∀ j, j < k → f j = g j) → rsum k f = rsum k g := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih => intro h; simp only [rsum, ih (fun j hj => h j (by omega)), h k (by omega)]

theorem rsum_indicator_lt (i : Nat) : ∀ k, k ≤ i → rsum k (fun j => if i = j then 1 else 0) = 0 := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
      intro h
      have hne : ¬ (i = k) := by omega
      simp only [rsum, ih (by omega), if_neg hne]

theorem rsum_indicator (i : Nat) : ∀ k, i < k → rsum k (fun j => if i = j then 1 else 0) = 1 := by
  intro k
  induction k with
  | zero => intro h; omega
  | succ k ih =>
      intro h
      simp only [rsum]
      by_cases hik : i = k
      · subst hik
        rw [rsum_indicator_lt i i (Nat.le_refl _), if_pos rfl]
      · rw [if_neg hik, ih (by omega)]

theorem rsum_zero_fun : ∀ k, rsum k (fun _ => 0) = 0 := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => simp [rsum, ih]

/-- `Σ_{j<n} count j s = |s|` when every move is `< n`. -/
theorem rsum_count (n : Nat) : ∀ (s : List Nat), (∀ i ∈ s, i < n) →
    rsum n (fun j => s.count j) = s.length := by
  intro s
  induction s with
  | nil => intro _; simp [rsum_zero_fun]
  | cons i rest ih =>
      intro hb
      have hi : i < n := hb i List.mem_cons_self
      have h1 : rsum n (fun j => (i :: rest).count j) =
          rsum n (fun j => rest.count j + if i = j then 1 else 0) := by
        apply rsum_congr
        intro j _
        rw [List.count_cons]
        by_cases hij : i = j
        · subst hij; simp
        · have : (i == j) = false := by simpa using hij
          simp [this, hij]
      rw [h1, rsum_add, rsum_indicator i n hi, ih (fun k hk => hb k (List.mem_cons_of_mem _ hk))]
      simp

theorem rsum_le (f g : Nat → Nat) : ∀ k, (∀ j, j < k → f j ≤ g j) → rsum k f ≤ rsum k g := by
  intro k
  induction k with
  | zero => intro _; exact Nat.le_refl _
  | succ k ih =>
      intro h
      simp only [rsum]
      have := ih (fun j hj => h j (by omega))
      have := h k (by omega)
      omega

theorem rsum_eq_of_le (f g : Nat → Nat) : ∀ k, (∀ j, j < k → f j ≤ g j) → rsum k f = rsum k g →
    ∀ j, j < k → f j = g j := by
  intro k
  induction k with
  | zero => intro _ _ j hj; omega
  | succ k ih =>
      intro h heq j hj
      simp only [rsum] at heq
      have hle := rsum_le f g k (fun j hj => h j (by omega))
      have hk := h k (by omega)
      have hfk : f k = g k := by omega
      have hs : rsum k f = rsum k g := by omega
      rcases Nat.lt_or_ge j k with hjk | hjk
      · exact ih (fun j hj => h j (by omega)) hs j hjk
      · have : j = k := by omega
        subst this; exact hfk

/-- The forced number of toggles of cell `j` in a clean plan. -/
def forced (n j : Nat) : Nat := if j = n - 1 then 1 else 2

theorem rsum_forced (n : Nat) (hn : 1 ≤ n) : rsum n (forced n) = 2 * n - 1 := by
  cases n with
  | zero => omega
  | succ n =>
      simp only [rsum]
      have h1 : rsum n (forced (n + 1)) = rsum n (fun _ => 2) := by
        apply rsum_congr
        intro j hj
        simp [forced]; omega
      have h2 : ∀ k, rsum k (fun _ => 2) = 2 * k := by
        intro k
        induction k with
        | zero => rfl
        | succ k ih => simp [rsum, ih]; omega
      have h3 : forced (n + 1) n = 1 := by simp [forced]
      rw [h1, h2, h3]
      omega

/-- In a clean plan every cell is toggled at least the forced number of times. -/
theorem forced_le_count (n : Nat) (hn : 1 ≤ n) (s : List Nat) (hb : ∀ i ∈ s, i < n)
    (hleg : legalE (empty n) s = true) (hfin : execB (empty n) s = target n) :
    ∀ j, j < n → forced n j ≤ s.count j := by
  -- parity at every cell
  have hpar : ∀ j, j < n → decide (s.count j % 2 = 1) = decide (j = n - 1) := by
    intro j hj
    have := nth_execB_parity s (empty n) j (by rw [length_empty]; exact hj)
    rw [hfin, nth_target n j hn, nth_empty] at this
    simpa using this.symm
  -- coverage: every cell is touched
  have hcov : ∀ j, j < n → j ∈ s := by
    intro j hj
    apply Classical.byContradiction
    intro hnot
    have hfro := frozen_above j s (empty n) hleg (fun j' _ => nth_empty n j') hnot
    have hlast : n - 1 ∈ s := by
      have h := hpar (n - 1) (by omega)
      simp at h
      exact List.count_pos_iff.mp (by omega)
    have := hfro (n - 1) hlast
    omega
  intro j hj
  have hpos : 0 < s.count j := List.count_pos_iff.mpr (hcov j hj)
  have hp := hpar j hj
  unfold forced
  by_cases hl : j = n - 1
  · rw [if_pos hl]; exact hpos
  · rw [if_neg hl]
    simp [hl] at hp
    omega

/-- **Floor.**  Every clean plan has at least `2n − 1` moves. -/
theorem floor_length (n p e : Nat) (hn : 1 ≤ n) (s : List Nat) (h : IsPlay n p e s) :
    2 * n - 1 ≤ s.length := by
  have h1 := forced_le_count n hn s h.bounds h.legal h.final
  have h2 := rsum_le (forced n) (fun j => s.count j) n h1
  rw [rsum_forced n hn, rsum_count n s h.bounds] at h2
  exact h2

/-- A `2n − 1`-move clean plan is tight. -/
theorem tight_of_length (n p e : Nat) (hn : 1 ≤ n) (s : List Nat) (h : IsPlay n p e s)
    (hlen : s.length = 2 * n - 1) : Tight n (empty n) s := by
  have h1 := forced_le_count n hn s h.bounds h.legal h.final
  have heq : rsum n (forced n) = rsum n (fun j => s.count j) := by
    rw [rsum_forced n hn, rsum_count n s h.bounds, hlen]
  have hexact := rsum_eq_of_le (forced n) (fun j => s.count j) n h1 heq
  refine ⟨h.bounds, ?_, ?_, ?_, ?_, ?_⟩
  · intro j _ hpj; rw [nth_empty] at hpj; cases hpj
  · intro hpj; rw [nth_empty] at hpj; cases hpj
  · intro j hj _ hjl
    have := hexact j hj
    simp [forced, hjl] at this
    exact this.symm
  · intro _
    have := hexact (n - 1) (by omega)
    simp [forced] at this
    exact this.symm
  · intro j _ _ ⟨j', _, _, hpj'⟩; rw [nth_empty] at hpj'; cases hpj'

/-! ## Theorem A -/

/-- **Theorem A, lower bound.**  A clean plan with exactly `2n − 1` moves uses
at least `e*(n, p)` irreversible removals. -/
theorem estar_le_erasures (n p e : Nat) (hp : 2 ≤ p) (hn : 1 ≤ n) (s : List Nat)
    (h : IsPlay n p e s) (hlen : s.length = 2 * n - 1) :
    estar n p ≤ erasures (empty n) s := by
  have T := tight_of_length n p e hn s h hlen
  have := pot_le_erasures n p hp hn s (empty n) (length_empty n) T h.legal h.peak h.final
  rwa [pot_empty] at this

theorem theoremA_lower (n p e : Nat) (hp : 2 ≤ p) (hn : 1 ≤ n) (s : List Nat)
    (h : IsPlay n p e s) (hlen : s.length = 2 * n - 1) : estar n p ≤ e :=
  Nat.le_trans (estar_le_erasures n p e hp hn s h hlen) h.budget

/-- **Theorem A (saturation).**  For `p ≥ 2` and `n ≥ 1`:
`M*(n, p, e) = 2n − 1` iff `e ≥ e*(n, p) = ⌈(n − 1)/(p − 1)⌉ − 1`. -/
theorem theoremA (n p e : Nat) (hp : 2 ≤ p) (hn : 1 ≤ n) :
    MstarIs n p e (2 * n - 1) ↔ estar n p ≤ e := by
  constructor
  · intro ⟨⟨s, hs, hlen⟩, _⟩
    exact theoremA_lower n p e hp hn s hs hlen
  · intro he
    obtain ⟨t, ht, hl⟩ := theoremA_upper n p hp hn
    exact ⟨⟨t, ht.mono_budget he, hl⟩, fun s hs => floor_length n p e hn s hs⟩

/-- Corollary (RC-02 Table 1 / `drops.md`): below the threshold the floor is not
attained, so `M*(n, p, e) > 2n − 1` whenever `e < e*(n, p)`. -/
theorem floor_not_attained (n p e : Nat) (hp : 2 ≤ p) (hn : 1 ≤ n) (he : e < estar n p)
    (s : List Nat) (h : IsPlay n p e s) : 2 * n - 1 < s.length := by
  have hfl := floor_length n p e hn s h
  rcases Nat.lt_or_ge (2 * n - 1) s.length with hlt | hge
  · exact hlt
  · exfalso
    have := theoremA_lower n p e hp hn s h (by omega)
    omega

end ErasurePebbling
