import RevPebbling.HalfReach

/-!
# Retention premium `gameF - 2 * gameH` (this work, 2026-08-29)

`gameT = 2 * gameH` (`HalfReach`) says a *complete* computation is
exactly twice the half-reach: out and straight back.  Keeping the far
end pebbled breaks that mirror.  This file certifies the first values
of the *retention premium* `gameF n p - 2 * gameH n p`:

| (n, p)  | gameH | gameF | premium |
|---------|-------|-------|---------|
| (2, 2)  |   2   |   3   |   -1    |
| (4, 3)  |   5   |   9   |   -1    |
| (5, 4)  |   6   |  11   |   -1    |
| (8, 4)  |  12   |  25   |   +1    |

The sign changes: at `(8,4)` keeping the answer costs one more than
computing it and erasing everything (`gameF 8 4 = gameT 8 4 + 1`).

## Method: a verified breadth-first search

`ReachIn`/`HalfIn` quantify over move lists, so they are not decidable
by instance search.  We compute the set `reachSet n p t` of boards
reachable from the empty chain in at most `t` peak-respecting moves,
and prove it sound (`reachSet_sound`) and complete
(`reachSet_complete_from`) for the trace predicates.  This makes both
predicates decidable; small values follow by `decide`/`native_decide`
(kernel `decide` for `(2,2)`; `native_decide`, audited below, for the
larger boards).

## Correspondence with the paper-side oracle

The oracle `2026_exact_reversible_pebbling/autoresearch/
retention_premium_oracle.py` (independent BFS cross-checked against the
Knill recurrence) uses 1-indexed nodes `1..T`; here cell `k-1` is that
node `k`, `n = T`, `p = Q`.  The move rules coincide definitionally:
`okMove b i = (i == 0 || nth b (i-1))` is "node 1 is free, node `k`
needs a pebble on `k-1`", and `maxOnes` bounds the peak over the whole
trace including the start.  The table above matches the oracle's
`H(2,2)=2, F(2,2)=3, H(4,3)=5, F(4,3)=9, H(5,4)=6, F(5,4)=11,
H(8,4)=12, F(8,4)=25` (premiums `-1,-1,-1,+1`).  Origin:
topic-mining `exp/FINDINGS_2026-08-28.md`, registry Q15.
-/

namespace RevPebbling.RetentionPremium

open RevPebbling.PebblingFoundations RevPebbling.GameReach
open RevPebbling.GameCost RevPebbling.GameCompleteCost RevPebbling.HalfReach

/-- All boards obtained from `b` by one legal move inside the chain
that keeps the pebble count within `p`. -/
def stepBoards (n p : Nat) (b : Board) : List Board :=
  (List.range n).filterMap fun i =>
    if okMove b i = true ∧ ones (toggle b i) ≤ p then some (toggle b i) else none

theorem mem_stepBoards {n p : Nat} {b b' : Board} :
    b' ∈ stepBoards n p b ↔
      ∃ i, i < n ∧ okMove b i = true ∧ ones (toggle b i) ≤ p ∧ toggle b i = b' := by
  unfold stepBoards
  simp only [List.mem_filterMap, List.mem_range]
  constructor
  · rintro ⟨i, hi, hf⟩
    by_cases hc : okMove b i = true ∧ ones (toggle b i) ≤ p
    · rw [if_pos hc] at hf
      exact ⟨i, hi, hc.1, hc.2, Option.some.inj hf⟩
    · rw [if_neg hc] at hf
      cases hf
  · rintro ⟨i, hi, h1, h2, h3⟩
    exact ⟨i, hi, by rw [if_pos ⟨h1, h2⟩, h3]⟩

/-- Boards reachable from the empty chain in at most `t` moves, every
intermediate board holding at most `p` pebbles. -/
def reachSet (n p : Nat) : Nat → List Board
  | 0 => [emptyBoard n]
  | t + 1 =>
      let R := reachSet n p t
      (R ++ R.flatMap (stepBoards n p)).dedup

theorem reachSet_succ (n p t : Nat) :
    reachSet n p (t + 1) =
      (reachSet n p t ++ (reachSet n p t).flatMap (stepBoards n p)).dedup := rfl

theorem mem_reachSet_succ_of_mem {n p t : Nat} {b : Board}
    (h : b ∈ reachSet n p t) : b ∈ reachSet n p (t + 1) := by
  rw [reachSet_succ, List.mem_dedup, List.mem_append]
  exact Or.inl h

theorem mem_reachSet_succ_of_step {n p t : Nat} {b b' : Board}
    (hb : b ∈ reachSet n p t) (h : b' ∈ stepBoards n p b) :
    b' ∈ reachSet n p (t + 1) := by
  rw [reachSet_succ, List.mem_dedup, List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨b, hb, h⟩

theorem reachSet_mono {n p t t' : Nat} (h : t ≤ t') {b : Board}
    (hb : b ∈ reachSet n p t) : b ∈ reachSet n p t' := by
  induction h with
  | refl => exact hb
  | step _ ih => exact mem_reachSet_succ_of_mem ih

/-- Every board in `reachSet` is the end of a legal, range-respecting,
peak-respecting trace of the corresponding length. -/
theorem reachSet_sound {n p : Nat} :
    ∀ t : Nat, ∀ b ∈ reachSet n p t,
      ∃ s : List Nat, s.length ≤ t ∧ (∀ i ∈ s, i < n) ∧
        legalB (emptyBoard n) s = true ∧ maxOnes (emptyBoard n) s ≤ p ∧
        execB (emptyBoard n) s = b := by
  intro t
  induction t with
  | zero =>
      intro b hb
      simp only [reachSet, List.mem_singleton] at hb
      subst hb
      refine ⟨[], by simp, by simp, rfl, ?_, rfl⟩
      show ones (emptyBoard n) ≤ p
      simp [ones_emptyBoard]
  | succ t ih =>
      intro b hb
      rw [reachSet_succ, List.mem_dedup, List.mem_append, List.mem_flatMap] at hb
      rcases hb with hb | ⟨b0, hb0, hstep⟩
      · obtain ⟨s, h1, h2, h3, h4, h5⟩ := ih b hb
        exact ⟨s, Nat.le_succ_of_le h1, h2, h3, h4, h5⟩
      · obtain ⟨s, h1, h2, h3, h4, h5⟩ := ih b0 hb0
        obtain ⟨i, hi, hok, hones, hbi⟩ := mem_stepBoards.mp hstep
        have hones0 : ones b0 ≤ p := by
          have := ones_le_maxOnes (execB (emptyBoard n) s) []
          calc ones b0 = ones (execB (emptyBoard n) s) := by rw [h5]
            _ ≤ maxOnes (emptyBoard n) s := by
                have h' := ones_le_maxOnes (emptyBoard n) s
                calc ones (execB (emptyBoard n) s)
                    = maxOnes (execB (emptyBoard n) s) [] := rfl
                  _ ≤ maxOnes (emptyBoard n) (s ++ []) := by
                      rw [maxOnes_append]; exact Nat.le_max_right _ _
                  _ = maxOnes (emptyBoard n) s := by rw [List.append_nil]
            _ ≤ p := h4
        refine ⟨s ++ [i], ?_, ?_, ?_, ?_, ?_⟩
        · rw [List.length_append, List.length_singleton]; omega
        · intro j hj
          rcases List.mem_append.mp hj with hj | hj
          · exact h2 j hj
          · rw [List.mem_singleton] at hj; omega
        · rw [legal_append, h3, Bool.true_and, h5]
          show (okMove b0 i && legalB (toggle b0 i) []) = true
          rw [hok]; rfl
        · rw [maxOnes_append, h5]
          show max (maxOnes (emptyBoard n) s)
                (max (ones b0) (maxOnes (toggle b0 i) [])) ≤ p
          have : maxOnes (toggle b0 i) [] = ones (toggle b0 i) := rfl
          rw [this]
          omega
        · rw [exec_append, h5]
          show execB b0 [i] = b
          rw [← hbi]; rfl

/-- Every legal, range-respecting, peak-respecting trace from a board
in `reachSet` lands in `reachSet` after its length. -/
theorem reachSet_complete_from {n p : Nat} :
    ∀ (s : List Nat) (b : Board) (t : Nat),
      b ∈ reachSet n p t → (∀ i ∈ s, i < n) →
      legalB b s = true → maxOnes b s ≤ p →
      execB b s ∈ reachSet n p (t + s.length) := by
  intro s
  induction s with
  | nil => intro b t hb _ _ _; exact hb
  | cons i rest ih =>
      intro b t hb hrange hleg hpk
      have hleg' : (okMove b i && legalB (toggle b i) rest) = true := hleg
      rw [Bool.and_eq_true] at hleg'
      have hpk' : max (ones b) (maxOnes (toggle b i) rest) ≤ p := hpk
      have hpkrest : maxOnes (toggle b i) rest ≤ p := le_trans (Nat.le_max_right _ _) hpk'
      have honesi : ones (toggle b i) ≤ p :=
        le_trans (ones_le_maxOnes _ _) hpkrest
      have hstep : toggle b i ∈ stepBoards n p b :=
        mem_stepBoards.mpr ⟨i, hrange i List.mem_cons_self, hleg'.1, honesi, rfl⟩
      have hb' := mem_reachSet_succ_of_step hb hstep
      have hrest := ih (toggle b i) (t + 1) hb'
        (fun j hj => hrange j (List.mem_cons_of_mem _ hj)) hleg'.2 hpkrest
      have harith : t + 1 + rest.length = t + (i :: rest).length := by
        rw [List.length_cons]; omega
      rw [harith] at hrest
      exact hrest

theorem reachIn_iff_mem {n p t : Nat} :
    ReachIn n p t ↔ doneBoard n ∈ reachSet n p t := by
  constructor
  · rintro ⟨s, hlen, hr, hleg, hex, hpk⟩
    have h0 : emptyBoard n ∈ reachSet n p 0 := by simp [reachSet]
    have h := reachSet_complete_from s (emptyBoard n) 0 h0 hr hleg hpk
    rw [hex] at h
    exact reachSet_mono (by omega) h
  · intro hb
    obtain ⟨s, h1, h2, h3, h4, h5⟩ := reachSet_sound t (doneBoard n) hb
    exact ⟨s, h1, h2, h3, h5, h4⟩

theorem halfIn_iff_mem {n p t : Nat} :
    HalfIn n p t ↔ ∃ b ∈ reachSet n p t, nth b (n - 1) = true := by
  constructor
  · intro h
    obtain ⟨s, hlen, hlt, hleg, hpk, htop⟩ := halfIn_tight h
    have h0 : emptyBoard n ∈ reachSet n p 0 := by simp [reachSet]
    have hmem := reachSet_complete_from s (emptyBoard n) 0 h0 hlt hleg hpk
    exact ⟨execB (emptyBoard n) s, reachSet_mono (by omega) hmem, htop⟩
  · rintro ⟨b, hb, htop⟩
    obtain ⟨s, h1, h2, h3, h4, h5⟩ := reachSet_sound t b hb
    exact ⟨s, h1, h2, h3, h4, ⟨s.length, by rw [List.take_length, h5]; exact htop⟩⟩

instance (n p t : Nat) : Decidable (ReachIn n p t) :=
  decidable_of_iff _ reachIn_iff_mem.symm

instance (n p t : Nat) : Decidable (HalfIn n p t) :=
  decidable_of_iff _ halfIn_iff_mem.symm

/-- Pin the clean optimum from a witness at `v` and a refutation at `v-1`. -/
theorem gameF_eq_of {n p v : Nat} (h1 : ReachIn n p v)
    (h2 : ¬ ReachIn n p (v - 1)) : gameF n p = v := by
  refine Nat.le_antisymm (gameF_le h1) (Nat.le_of_not_lt fun hlt => ?_)
  have hatt : ReachIn n p (gameF n p) := reachIn_gameF ⟨v, h1⟩
  exact h2 (hatt.mono (by omega))

theorem halfIn_mono {n p t t' : Nat} (h : HalfIn n p t) (ht : t ≤ t') :
    HalfIn n p t' := by
  obtain ⟨s, h1, h2, h3, h4, h5⟩ := h
  exact ⟨s, le_trans h1 ht, h2, h3, h4, h5⟩

/-- Pin the half-reach optimum the same way. -/
theorem gameH_eq_of {n p v : Nat} (h1 : HalfIn n p v)
    (h2 : ¬ HalfIn n p (v - 1)) : gameH n p = v := by
  refine Nat.le_antisymm (gameH_le h1) (Nat.le_of_not_lt fun hlt => ?_)
  have hatt : HalfIn n p (gameH n p) := halfIn_gameH ⟨v, h1⟩
  exact h2 (halfIn_mono hatt (by omega))

-- ------------------------------------------------------------------
-- Certified values.  `(2,2)` goes through the kernel; the larger
-- boards use `native_decide` (audited at the end of the file).
-- ------------------------------------------------------------------

theorem gameH_2_2 : gameH 2 2 = 2 := gameH_eq_of (by decide) (by decide)
theorem gameF_2_2 : gameF 2 2 = 3 := gameF_eq_of (by decide) (by decide)

theorem gameH_4_3 : gameH 4 3 = 5 := gameH_eq_of (by native_decide) (by native_decide)
theorem gameF_4_3 : gameF 4 3 = 9 := gameF_eq_of (by native_decide) (by native_decide)

theorem gameH_5_4 : gameH 5 4 = 6 := gameH_eq_of (by native_decide) (by native_decide)
theorem gameF_5_4 : gameF 5 4 = 11 := gameF_eq_of (by native_decide) (by native_decide)

theorem gameH_8_4 : gameH 8 4 = 12 := gameH_eq_of (by native_decide) (by native_decide)
theorem gameF_8_4 : gameF 8 4 = 25 := gameF_eq_of (by native_decide) (by native_decide)

-- ------------------------------------------------------------------
-- The retention premium and its sign change
-- ------------------------------------------------------------------

/-- Near-full premium `-1` at `(2,2)`. -/
theorem premium_2_2 : gameF 2 2 + 1 = 2 * gameH 2 2 := by
  rw [gameF_2_2, gameH_2_2]

/-- Near-full premium `-1` at `(4,3)`. -/
theorem premium_4_3 : gameF 4 3 + 1 = 2 * gameH 4 3 := by
  rw [gameF_4_3, gameH_4_3]

/-- Near-full premium `-1` at `(5,4)`. -/
theorem premium_5_4 : gameF 5 4 + 1 = 2 * gameH 5 4 := by
  rw [gameF_5_4, gameH_5_4]

/-- **The sign change**: at `(8,4)` the premium is `+1`. -/
theorem premium_8_4 : gameF 8 4 = 2 * gameH 8 4 + 1 := by
  rw [gameF_8_4, gameH_8_4]

/-- The complete-computation optimum at `(8,4)`, via `gameT = 2 * gameH`. -/
theorem gameT_8_4 : gameT 8 4 = 24 := by
  have hH : HalfIn 8 4 12 := by native_decide
  have hex : ∃ t, CompleteInAt 8 4 t := ⟨2 * 12, completeInAt_of_halfIn hH⟩
  rw [gameT_eq_two_mul_gameH hex, gameH_8_4]

/-- **Keeping the answer beats erasing it by exactly one move at `(8,4)`**:
retaining the far-end pebble costs one more than a complete computation
that touches it and erases everything. -/
theorem retention_beats_erasure_8_4 : gameF 8 4 = gameT 8 4 + 1 := by
  rw [gameF_8_4, gameT_8_4]

-- Axiom audit.  The kernel-only route must not use the compiler:
#print axioms premium_2_2
-- The native route may additionally use `Lean.ofReduceBool`:
#print axioms premium_8_4
#print axioms retention_beats_erasure_8_4

end RevPebbling.RetentionPremium
