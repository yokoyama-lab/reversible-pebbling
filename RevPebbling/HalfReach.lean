import RevPebbling.GameCompleteCost

/-!
# Half-reach `gameH`, and `gameT = 2 * gameH` (this work, 2026-08-24)

The complete variant's cost is *exactly* twice the half-reach cost.
The reason is that the board graph is undirected: a complete
computation is a walk from empty to empty through a board carrying the
far end, and the cheapest such walk goes out and comes straight back.

`GameCompleteCost.gameT_le_two_mul_gameF` bounds `T` by twice the
*clean* reach; this file replaces `gameF` by the *half* reach and turns
the inequality into an equality.
-/

namespace RevPebbling.HalfReach

open RevPebbling.PebblingFoundations RevPebbling.GameReach
open RevPebbling.GameCost RevPebbling.CompleteReach RevPebbling.GameCompleteCost

/-- A half-reach of at most `t` moves: from the empty board, the far end
is pebbled at some point.  Nothing is required of the final board — this
is `ReachIn` with the clean-up dropped. -/
def HalfIn (n p t : Nat) : Prop :=
  ∃ s : List Nat, s.length ≤ t ∧ (∀ i ∈ s, i < n) ∧
    legalB (emptyBoard n) s = true ∧
    maxOnes (emptyBoard n) s ≤ p ∧
    everOn (emptyBoard n) s (n - 1)

/-- **The half-reach optimum.** -/
noncomputable def gameH (n p : Nat) : Nat := sInf {t | HalfIn n p t}

theorem gameH_le {n p t : Nat} (h : HalfIn n p t) : gameH n p ≤ t :=
  Nat.sInf_le h

theorem halfIn_gameH {n p : Nat} (h : ∃ t, HalfIn n p t) :
    HalfIn n p (gameH n p) := Nat.sInf_mem h

theorem completeInAt_gameT {n p : Nat} (h : ∃ t, CompleteInAt n p t) :
    CompleteInAt n p (gameT n p) := Nat.sInf_mem h

/-- A half-reach can be trimmed so that it *ends* with the far end
pebbled, without getting longer. -/
theorem halfIn_tight {n p t : Nat} (h : HalfIn n p t) :
    ∃ s : List Nat, s.length ≤ t ∧ (∀ i ∈ s, i < n) ∧
      legalB (emptyBoard n) s = true ∧
      maxOnes (emptyBoard n) s ≤ p ∧
      nth (execB (emptyBoard n) s) (n - 1) = true := by
  obtain ⟨s, hlen, hlt, hleg, hpk, hev⟩ := h
  obtain ⟨k, hk⟩ := hev
  have hsplit : s.take k ++ s.drop k = s := List.take_append_drop k s
  have hlegs : legalB (emptyBoard n) (s.take k ++ s.drop k) = true := by
    rw [hsplit]; exact hleg
  rw [legal_append] at hlegs
  have hpks : maxOnes (emptyBoard n) (s.take k ++ s.drop k) ≤ p := by
    rw [hsplit]; exact hpk
  rw [maxOnes_append] at hpks
  refine ⟨s.take k, ?_, ?_, (Bool.and_eq_true _ _).mp hlegs |>.1, ?_, hk⟩
  · have : (s.take k).length ≤ s.length := by
      rw [List.length_take]; exact Nat.min_le_right _ _
    exact le_trans this hlen
  · intro i hi
    exact hlt i (List.take_subset _ _ hi)
  · exact le_trans (le_max_left _ _) hpks

/-- Out and back: a half-reach yields a complete computation of twice
the length at the same peak. -/
theorem completeInAt_of_halfIn {n p t : Nat} (h : HalfIn n p t) :
    CompleteInAt n p (2 * t) := by
  obtain ⟨s, hlen, hlt, hleg, hpk, htop⟩ := halfIn_tight h
  obtain ⟨hleg', hexec', hpk'⟩ := reverse_append_roundtrip (emptyBoard n) s hleg
  refine ⟨s ++ s.reverse, ?_, ?_, hleg', hexec', ?_, ?_⟩
  · simp only [List.length_append, List.length_reverse]
    omega
  · intro i hi
    rcases List.mem_append.mp hi with h1 | h2
    · exact hlt i h1
    · exact hlt i (List.mem_reverse.mp h2)
  · rw [hpk']; exact hpk
  · refine ⟨s.length, ?_⟩
    have hpre : (s ++ s.reverse).take s.length = s := by simp
    rw [hpre]; exact htop

/-- Cutting a complete computation where the far end is on gives two
half-reaches, the second by playing the tail backwards. -/
theorem two_mul_gameH_le_gameT {n p : Nat} (h : ∃ t, CompleteInAt n p t) :
    2 * gameH n p ≤ gameT n p := by
  obtain ⟨s, hlen, hlt, hleg, hexec, hpk, hev⟩ := completeInAt_gameT h
  obtain ⟨k, hk⟩ := hev
  set A := s.take k with hA
  set B := s.drop k with hB
  have hsplit : A ++ B = s := List.take_append_drop k s
  -- legality and peak split along the cut
  have hlegs : legalB (emptyBoard n) (A ++ B) = true := by rw [hsplit]; exact hleg
  rw [legal_append] at hlegs
  have hlegA : legalB (emptyBoard n) A = true := ((Bool.and_eq_true _ _).mp hlegs).1
  have hlegB : legalB (execB (emptyBoard n) A) B = true :=
    ((Bool.and_eq_true _ _).mp hlegs).2
  have hpks : maxOnes (emptyBoard n) (A ++ B) ≤ p := by rw [hsplit]; exact hpk
  rw [maxOnes_append] at hpks
  have hexecs : execB (execB (emptyBoard n) A) B = emptyBoard n := by
    rw [← exec_append, hsplit]; exact hexec
  -- the first half
  have hHA : HalfIn n p A.length :=
    ⟨A, le_refl _, fun i hi => hlt i (by rw [← hsplit]; exact List.mem_append_left _ hi),
      hlegA, le_trans (le_max_left _ _) hpks, ⟨k, by
        have : A.take k = A := by
          rw [hA, List.take_take, Nat.min_self]
        rw [this]; exact hk⟩⟩
  -- the second half, played backwards
  have hHB : HalfIn n p B.length := by
    refine ⟨B.reverse, by simp, ?_, ?_, ?_, ?_⟩
    · intro i hi
      exact hlt i (by rw [← hsplit]; exact List.mem_append_right _ (List.mem_reverse.mp hi))
    · have := legal_reverse (execB (emptyBoard n) A) B hlegB
      rwa [hexecs] at this
    · have := maxOnes_reverse (execB (emptyBoard n) A) B
      rw [hexecs] at this
      rw [this]
      exact le_trans (le_max_right _ _) hpks
    · refine ⟨B.reverse.length, ?_⟩
      have hb : B.reverse.take B.reverse.length = B.reverse := by simp
      rw [hb]
      have := exec_reverse_cancel (execB (emptyBoard n) A) B
      rw [hexecs] at this
      rw [this]; exact hk
  have h1 : gameH n p ≤ A.length := gameH_le hHA
  have h2 : gameH n p ≤ B.length := gameH_le hHB
  have hAB : A.length + B.length = s.length := by
    rw [← hsplit]; simp
  omega

theorem gameT_le_two_mul_gameH {n p : Nat} (h : ∃ t, HalfIn n p t) :
    gameT n p ≤ 2 * gameH n p :=
  gameT_le (completeInAt_of_halfIn (halfIn_gameH h))

/-- **The bridge, as an equality**: completing costs exactly twice
half-reaching. -/
theorem gameT_eq_two_mul_gameH {n p : Nat} (h : ∃ t, CompleteInAt n p t) :
    gameT n p = 2 * gameH n p := by
  have hH : ∃ t, HalfIn n p t := by
    obtain ⟨t, ht⟩ := h
    obtain ⟨s, hlen, hlt, hleg, _, hpk, hev⟩ := ht
    exact ⟨s.length, s, le_refl _, hlt, hleg, hpk, hev⟩
  exact le_antisymm (gameT_le_two_mul_gameH hH) (two_mul_gameH_le_gameT h)

-- ==================================================================
-- Stage B: the new bridge  gameF n (p+1) + 1 ≤ gameT n p
-- ==================================================================

/-- A play that never touches `v` leaves `v` as it found it. -/
theorem nth_exec_of_not_mem (v : Nat) : ∀ (s : List Nat) (b : Board),
    (∀ i ∈ s, i ≠ v) → nth (execB b s) v = nth b v := by
  intro s
  induction s with
  | nil => intro b _; rfl
  | cons i rest ih =>
      intro b h
      have hne : i ≠ v := h i (List.mem_cons_self)
      have hstep : nth (toggle b i) v = nth b v := nth_set_ne b i v _ hne
      have := ih (toggle b i) (fun j hj => h j (List.mem_cons_of_mem _ hj))
      show nth (execB (toggle b i) rest) v = nth b v
      rw [this, hstep]

/-- Toggles at distinct cells commute. -/
theorem toggle_comm_ne (b : Board) (i v : Nat) (h : i ≠ v) :
    toggle (toggle b v) i = toggle (toggle b i) v := by
  unfold toggle
  rw [nth_set_ne b v i _ (Ne.symm h), nth_set_ne b i v _ h]
  exact set_comm b v i _ _ (Ne.symm h)

/-- Carrying an extra pebble at `v` through a play that never touches `v`. -/
theorem exec_toggle_add (v : Nat) : ∀ (s : List Nat) (b : Board),
    (∀ i ∈ s, i ≠ v) → execB (toggle b v) s = toggle (execB b s) v := by
  intro s
  induction s with
  | nil => intro b _; rfl
  | cons i rest ih =>
      intro b h
      have hne : i ≠ v := h i (List.mem_cons_self)
      show execB (toggle (toggle b v) i) rest = _
      rw [toggle_comm_ne b i v hne]
      exact ih (toggle b i) (fun j hj => h j (List.mem_cons_of_mem _ hj))

/-- The extra pebble never makes a move illegal, provided no move reads it. -/
theorem legal_toggle_add (v : Nat) : ∀ (s : List Nat) (b : Board),
    (∀ i ∈ s, i ≠ v ∧ i ≠ v + 1) → legalB b s = true →
      legalB (toggle b v) s = true := by
  intro s
  induction s with
  | nil => intro b _ _; rfl
  | cons i rest ih =>
      intro b h hleg
      obtain ⟨hne, hne1⟩ := h i (List.mem_cons_self)
      rw [legalB] at hleg ⊢
      obtain ⟨hok, hrest⟩ := (Bool.and_eq_true _ _).mp hleg
      have hok' : okMove (toggle b v) i = true := by
        rcases Nat.eq_zero_or_pos i with hi | hi
        · simp [okMove, hi]
        · have hd : v ≠ i - 1 := by omega
          have : nth (toggle b v) (i - 1) = nth b (i - 1) := nth_set_ne b v (i - 1) _ hd
          simpa [okMove, this] using hok
      rw [hok', Bool.true_and, toggle_comm_ne b i v hne]
      exact ih (toggle b i) (fun j hj => h j (List.mem_cons_of_mem _ hj)) hrest

theorem ones_toggle_le (b : Board) (v : Nat) : ones (toggle b v) ≤ ones b + 1 := by
  by_cases hv : v < b.length
  · have := ones_set b v (!(nth b v)) hv
    cases hb : nth b v <;> simp [toggle, hb] at this ⊢ <;> omega
  · have : toggle b v = b := by
      unfold toggle; exact set_ge_length b v _ (Nat.le_of_not_lt hv)
    rw [this]; omega

theorem maxOnes_toggle_add (v : Nat) : ∀ (s : List Nat) (b : Board),
    (∀ i ∈ s, i ≠ v) → maxOnes (toggle b v) s ≤ maxOnes b s + 1 := by
  intro s
  induction s with
  | nil => intro b _; exact ones_toggle_le b v
  | cons i rest ih =>
      intro b h
      have hne : i ≠ v := h i (List.mem_cons_self)
      have h1 : ones (toggle b v) ≤ ones b + 1 := ones_toggle_le b v
      have h2 : maxOnes (toggle (toggle b v) i) rest ≤ maxOnes (toggle b i) rest + 1 := by
        rw [toggle_comm_ne b i v hne]
        exact ih (toggle b i) (fun j hj => h j (List.mem_cons_of_mem _ hj))
      simp only [maxOnes]
      omega

/-- Split a list at the first occurrence of `v`. -/
theorem split_first_occ (v : Nat) : ∀ (s : List Nat), v ∈ s →
    ∃ A C, s = A ++ v :: C ∧ ∀ i ∈ A, i ≠ v := by
  intro s
  induction s with
  | nil => intro h; cases h
  | cons a rest ih =>
      intro h
      by_cases ha : a = v
      · exact ⟨[], rest, by rw [ha]; rfl, by intro i hi; cases hi⟩
      · have hv : v ∈ rest := by
          rcases List.mem_cons.mp h with h1 | h2
          · exact absurd h1.symm ha
          · exact h2
        obtain ⟨A, C, hAC, hA⟩ := ih hv
        refine ⟨a :: A, C, by rw [hAC]; rfl, ?_⟩
        intro i hi
        rcases List.mem_cons.mp hi with h1 | h2
        · rw [h1]; exact ha
        · exact hA i h2

/-- A half-reach can be cut so that its **last** move is the one that
first pebbles the far end. -/
theorem halfIn_split {n p t : Nat} (h : HalfIn n p t) :
    ∃ A : List Nat, A.length + 1 ≤ t ∧ (∀ i ∈ A, i < n) ∧ (∀ i ∈ A, i ≠ n - 1) ∧
      legalB (emptyBoard n) (A ++ [n - 1]) = true ∧
      maxOnes (emptyBoard n) (A ++ [n - 1]) ≤ p := by
  obtain ⟨s, hlen, hlt, hleg, hpk, htop⟩ := halfIn_tight h
  have hempty : nth (emptyBoard n) (n - 1) = false := nth_replicate n (n - 1)
  have hmem : (n - 1) ∈ s := by
    by_contra hc
    have : nth (execB (emptyBoard n) s) (n - 1) = nth (emptyBoard n) (n - 1) :=
      nth_exec_of_not_mem (n - 1) s (emptyBoard n) (fun i hi hEq => hc (hEq ▸ hi))
    rw [htop, hempty] at this
    exact Bool.noConfusion this
  obtain ⟨A, C, hAC, hA⟩ := split_first_occ (n - 1) s hmem
  have hpre : (A ++ [n - 1]) ++ C = s := by rw [hAC]; simp
  refine ⟨A, ?_, ?_, hA, ?_, ?_⟩
  · have : (A ++ [n - 1]).length ≤ s.length := by
      rw [← hpre]; simp
    simp only [List.length_append, List.length_cons] at this
    omega
  · intro i hi; exact hlt i (by rw [← hpre]; exact List.mem_append_left _ (List.mem_append_left _ hi))
  · have h2 : legalB (emptyBoard n) ((A ++ [n - 1]) ++ C) = true := by rw [hpre]; exact hleg
    rw [legal_append] at h2
    exact ((Bool.and_eq_true _ _).mp h2).1
  · have h2 : maxOnes (emptyBoard n) ((A ++ [n - 1]) ++ C) ≤ p := by rw [hpre]; exact hpk
    rw [maxOnes_append] at h2
    exact le_trans (le_max_left _ _) h2

/-- **The new bridge.** Running a half-reach, then replaying it backwards
while *holding* the far end, is a clean reach with one more pebble. -/
theorem reachIn_of_halfIn {n p t : Nat} (hn : 1 ≤ n) (h : HalfIn n p t) :
    ReachIn n (p + 1) (2 * t - 1) := by
  obtain ⟨A, hlen, hlt, hne, hleg, hpk⟩ := halfIn_split h
  have hlegA : legalB (emptyBoard n) A = true := by
    rw [legal_append] at hleg; exact ((Bool.and_eq_true _ _).mp hleg).1
  have hexecS : execB (emptyBoard n) (A ++ [n - 1])
      = toggle (execB (emptyBoard n) A) (n - 1) := by
    rw [exec_append]; rfl
  have hrevne : ∀ i ∈ A.reverse, i ≠ n - 1 :=
    fun i hi => hne i (List.mem_reverse.mp hi)
  refine ⟨(A ++ [n - 1]) ++ A.reverse, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : ((A ++ [n - 1]) ++ A.reverse).length = 2 * A.length + 1 := by
      simp only [List.length_append, List.length_reverse, List.length_cons,
        List.length_nil]
      omega
    omega
  · intro i hi
    rcases List.mem_append.mp hi with h1 | h2
    · rcases List.mem_append.mp h1 with h3 | h4
      · exact hlt i h3
      · have hi4 : i = n - 1 := by simpa using h4
        rw [hi4]; omega
    · exact hlt i (List.mem_reverse.mp h2)
  · rw [legal_append, hleg, Bool.true_and, hexecS]
    refine legal_toggle_add (n - 1) A.reverse (execB (emptyBoard n) A) ?_ ?_
    · intro i hi
      have hi' := List.mem_reverse.mp hi
      exact ⟨hne i hi', by have := hlt i hi'; omega⟩
    · exact legal_reverse (emptyBoard n) A hlegA
  · rw [exec_append, hexecS,
      exec_toggle_add (n - 1) A.reverse (execB (emptyBoard n) A) hrevne,
      exec_reverse_cancel]
    show toggle (emptyBoard n) (n - 1) = doneBoard n
    unfold toggle doneBoard
    rw [show nth (emptyBoard n) (n - 1) = false from nth_replicate n (n - 1)]
    rfl
  · rw [maxOnes_append, hexecS]
    refine max_le (by omega) ?_
    have h2 : maxOnes (toggle (execB (emptyBoard n) A) (n - 1)) A.reverse
        ≤ maxOnes (execB (emptyBoard n) A) A.reverse + 1 :=
      maxOnes_toggle_add (n - 1) A.reverse (execB (emptyBoard n) A) hrevne
    have h3 : maxOnes (execB (emptyBoard n) A) A.reverse = maxOnes (emptyBoard n) A :=
      maxOnes_reverse (emptyBoard n) A
    have h4 : maxOnes (emptyBoard n) A ≤ maxOnes (emptyBoard n) (A ++ [n - 1]) := by
      rw [maxOnes_append]; exact le_max_left _ _
    omega

/-- **`F(n, p+1) + 1 ≤ T(n, p)`** — the direction the manuscript records
as *not* transferring.  A complete computation with `p` pebbles is at
least as expensive as a clean reach with `p+1`. -/
theorem gameF_succ_add_one_le_gameT {n p : Nat} (hn : 1 ≤ n)
    (h : ∃ t, HalfIn n p t) : gameF n (p + 1) + 1 ≤ gameT n p := by
  have hH : HalfIn n p (gameH n p) := halfIn_gameH h
  have hpos : 1 ≤ gameH n p := by
    obtain ⟨A, hlen, _, _, _, _⟩ := halfIn_split hH
    omega
  have hF : gameF n (p + 1) ≤ 2 * gameH n p - 1 :=
    gameF_le (reachIn_of_halfIn hn hH)
  have hT : gameT n p = 2 * gameH n p := by
    refine gameT_eq_two_mul_gameH ?_
    obtain ⟨t, ht⟩ := h
    exact ⟨2 * t, completeInAt_of_halfIn ht⟩
  omega

end RevPebbling.HalfReach
