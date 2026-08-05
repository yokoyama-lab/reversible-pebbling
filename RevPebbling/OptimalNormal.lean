import RevPebbling.GameStructure

/-!
# Normalising an optimal play (this work, link (1), `≥` side, step (D))

Step (D) of the roadmap is the one where Knill's published argument has a
gap (LAUR-95-2258 p. 5): to cut an optimal play into three optimal pieces
one needs to know that the play does not waste moves, and the paper's
reason for that does not follow from what it assumes.  The project notes
record the intended repair as three lemmas — "no repeated
configuration", "no upper move before", "freeze above" — none of which
existed.

This file proves the first and the third, as `no_repeat_cfg` and
`freeze_above`.

## Splicing

Everything rests on one observation: legality of a play depends only on
the running board, so a segment that **returns the board to where it
started** can be deleted outright.  `legal_splice`, `exec_splice` and
`maxOnes_splice` say that deleting such a segment keeps the play legal,
keeps its final board, and cannot raise its peak.

## `no_repeat_cfg`

Hence, in a play of minimum length, **no configuration occurs twice**: a
repeat would be a deletable segment, and deleting it gives a strictly
shorter play with the same endpoints and no larger peak, contradicting
minimality.  This is the normalisation step (D) needs — it is what rules
out the "wasted" plays for which the three-way cut would lose moves.

## `freeze_above`

The other half is a locality fact: if the cells strictly above `x` are
empty and `x` itself stays empty, then **the play cannot go above `x` at
all** (`no_move_above`).  The only way in is a move on `x+1`, and that
needs a pebble on `x`.  So the region above a cut that is never occupied
stays untouched, and the whole play lives below the cut.

## What is still missing for `GameAttain`

The third lemma of the intended repair — the one the project notes call
the "no upper move before" step.  With `no_repeat_cfg` the optimal play
is loop-free, and with `no_move_above` the region above an unoccupied cut
is inert; but the cut Knill needs sits at `CutVocabulary.cutAt` over a
*time window*, and relating that window's endpoints to the first and last
moves above the cut is exactly what the remaining lemma does.  It is
**not proved here**, so `GameDecomposition.GameAttain` stays a
hypothesis.

(The identifier is deliberately not written out above: `check_claims.py`
looks for names from the working notes in the sources, and spelling it
here would make an unproved lemma look present.)
-/

namespace RevPebbling.OptimalNormal

open RevPebbling.PebblingFoundations RevPebbling.GameReach RevPebbling.GameCost

-- ------------------------------------------------------------------
-- Splicing out a segment that returns the board to where it started
-- ------------------------------------------------------------------

/-- The board after `u ++ v` is the board after `u`, restated for the
running board. -/
theorem exec_loop {b : Board} {u v : List Nat}
    (hcfg : execB b (u ++ v) = execB b u) : execB (execB b u) v = execB b u := by
  rw [← exec_append]; exact hcfg

/-- **A LOOP CAN BE DELETED AND THE PLAY STAYS LEGAL.** -/
theorem legal_splice {b : Board} {u v w : List Nat}
    (h : legalB b (u ++ (v ++ w)) = true)
    (hcfg : execB b (u ++ v) = execB b u) :
    legalB b (u ++ w) = true := by
  rw [legal_append, Bool.and_eq_true] at h
  obtain ⟨hu, hvw⟩ := h
  rw [legal_append, Bool.and_eq_true] at hvw
  obtain ⟨_, hw⟩ := hvw
  rw [exec_loop hcfg] at hw
  rw [legal_append, Bool.and_eq_true]
  exact ⟨hu, hw⟩

/-- …and ends on the same board. -/
theorem exec_splice {b : Board} {u v w : List Nat}
    (hcfg : execB b (u ++ v) = execB b u) :
    execB b (u ++ w) = execB b (u ++ (v ++ w)) := by
  rw [exec_append, exec_append, exec_append, exec_loop hcfg]

/-- …and never needs more pebbles. -/
theorem maxOnes_splice {b : Board} {u v w : List Nat}
    (hcfg : execB b (u ++ v) = execB b u) :
    maxOnes b (u ++ w) ≤ maxOnes b (u ++ (v ++ w)) := by
  rw [maxOnes_append, maxOnes_append, maxOnes_append, exec_loop hcfg]
  omega

-- ------------------------------------------------------------------
-- `no_repeat_cfg`: an optimal play never revisits a configuration
-- ------------------------------------------------------------------

/-- **NO CONFIGURATION REPEATS IN A PLAY OF MINIMUM LENGTH.**

If it did, the moves between the two occurrences form a loop; deleting it
leaves a legal play with the same final board, no larger peak, and
strictly fewer moves — so the original was not optimal.

This is the normalisation that step (D) of the `≥` side needs: it is what
forbids the "wasted" plays on which a three-way cut would lose moves. -/
theorem no_repeat_cfg {n p : Nat} {s : List Nat}
    (hr : ∀ i ∈ s, i < n) (hleg : legalB (emptyBoard n) s = true)
    (hex : execB (emptyBoard n) s = doneBoard n)
    (hpk : maxOnes (emptyBoard n) s ≤ p)
    (hopt : s.length ≤ gameF n p)
    {i j : Nat} (hij : i < j) (hj : j ≤ s.length) :
    execB (emptyBoard n) (s.take i) ≠ execB (emptyBoard n) (s.take j) := by
  intro heq
  -- s = u ++ (v ++ w) with u the first i moves and v the loop
  have hsplit1 : s.take i ++ (s.drop i).take (j - i) = s.take j := by
    rw [← List.take_add]
    congr 1
    omega
  have hsplit : s.take i ++ ((s.drop i).take (j - i) ++ s.drop j) = s := by
    rw [← List.append_assoc, hsplit1, List.take_append_drop]
  -- the loop returns the board to where it started
  have hcfg : execB (emptyBoard n) (s.take i ++ (s.drop i).take (j - i))
      = execB (emptyBoard n) (s.take i) := by
    rw [hsplit1]; exact heq.symm
  -- the spliced play
  have hlegS : legalB (emptyBoard n) (s.take i ++ s.drop j) = true := by
    refine legal_splice ?_ hcfg
    rw [hsplit]; exact hleg
  have hexS : execB (emptyBoard n) (s.take i ++ s.drop j) = doneBoard n := by
    rw [exec_splice hcfg, hsplit]; exact hex
  have hpkS : maxOnes (emptyBoard n) (s.take i ++ s.drop j) ≤ p := by
    refine Nat.le_trans (maxOnes_splice hcfg) ?_
    rw [hsplit]; exact hpk
  have hrS : ∀ x ∈ s.take i ++ s.drop j, x < n := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hr x (List.mem_of_mem_take hx)
    · exact hr x (List.mem_of_mem_drop hx)
  -- it is strictly shorter
  have hlenS : (s.take i ++ s.drop j).length < s.length := by
    rw [List.length_append, List.length_take, List.length_drop]
    omega
  have hreach : ReachIn n p (s.take i ++ s.drop j).length :=
    ⟨_, Nat.le_refl _, hrS, hlegS, hexS, hpkS⟩
  have := gameF_le hreach
  omega

-- ------------------------------------------------------------------
-- `freeze_above`: an unoccupied cut cannot be crossed
-- ------------------------------------------------------------------

/-- **NOTHING GETS ABOVE AN EMPTY CUT THAT STAYS EMPTY.**  If the cells
strictly above `x` start empty and cell `x` is empty at every time, then
no move of the play is above `x`.

The only entrance is a move on `x + 1`, and that needs a pebble on `x`;
every higher cell needs the one below it, which is empty by induction. -/
theorem no_move_above (x : Nat) : ∀ (s : List Nat) (b : Board),
    legalB b s = true →
    (∀ i, x < i → nth b i = false) →
    (∀ k, nth (execB b (s.take k)) x = false) →
    ∀ i ∈ s, i ≤ x
  | [], _, _, _, _ => by simp
  | j :: rest, b, hleg, habove, hoff => by
      simp only [legalB, Bool.and_eq_true] at hleg
      -- the head move is below the cut
      have hjx : j ≤ x := by
        by_contra hc
        have hj : x < j := by omega
        have hok := hleg.1
        rcases Nat.eq_zero_or_pos j with rfl | hjpos
        · omega
        · have hne : ¬ (j = 0) := by omega
          simp only [okMove, Bool.or_eq_true, beq_iff_eq, hne, false_or] at hok
          rcases Nat.lt_or_ge x (j - 1) with hlt | hge
          · rw [habove (j - 1) hlt] at hok
            exact Bool.noConfusion hok
          · have hjx1 : j - 1 = x := by omega
            rw [hjx1] at hok
            have := hoff 0
            simp only [List.take_zero] at this
            rw [show execB b [] = b from rfl] at this
            rw [this] at hok
            exact Bool.noConfusion hok
      -- and the rest of the play sees the same situation
      have habove' : ∀ i, x < i → nth (toggle b j) i = false := by
        intro i hi
        rw [toggle, nth_set_ne _ _ _ _ (by omega : j ≠ i)]
        exact habove i hi
      have hoff' : ∀ k, nth (execB (toggle b j) (rest.take k)) x = false := by
        intro k
        have := hoff (k + 1)
        simpa [execB] using this
      have hrec := no_move_above x rest (toggle b j) hleg.2 habove' hoff'
      intro i hi
      rcases List.mem_cons.mp hi with rfl | hi
      · exact hjx
      · exact hrec i hi

/-- The board above such a cut never changes: it is empty throughout. -/
theorem freeze_above (x : Nat) (s : List Nat) (b : Board)
    (hleg : legalB b s = true)
    (habove : ∀ i, x < i → nth b i = false)
    (hoff : ∀ k, nth (execB b (s.take k)) x = false) :
    ∀ k i, x < i → nth (execB b (s.take k)) i = false := by
  intro k i hi
  have hnot : i ∉ s.take k := by
    intro hc
    have := no_move_above x s b hleg habove hoff i (List.mem_of_mem_take hc)
    omega
  rw [nth_exec_of_not_mem _ _ _ hnot]
  exact habove i hi

end RevPebbling.OptimalNormal
