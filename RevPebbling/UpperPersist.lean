import RevPebbling.LowerSuffixPeak
import RevPebbling.CutOptimal

/-!
# The upper region never empties again (this work, link (1), `≥` side)

This is the last claim about plays that `GameAttain` needed, and it
settles `KnillRecursion`'s hypothesis `hpk`.

## The argument

Moves below the cut and moves above it are almost independent: a move on
cell `i ≤ x` needs cell `i-1 ≤ x-1`, so **the lower part of the play does
not depend on the upper part at all**.  The dependence runs one way only
— a move on `x+1` needs the cut cell.

So suppose an optimal play has already moved above the cut, and at some
later time `q` the region above the cut is empty again.  Delete every
move above the cut that happens before `q`.  What is left is still a
legal play:

* the lower trace is untouched, because lower moves never consulted the
  upper cells;
* the upper moves after `q` start from the same (empty) upper region as
  before, and the cut cell they may need is a lower cell, also untouched.

It ends on the same board and its peak cannot have risen, yet it is
strictly shorter — contradicting optimality.  Hence

  `upper_nonempty_of_optimal` — in a play of minimum length, once a move
  above the cut has happened, the region above the cut is never empty
  again.

At the cut time produced by `CutTime.cutFull_attained` the board is
*full*, so `S` pebbles sit strictly above the cut and moves above it have
certainly happened.  Feeding that into
`LowerSuffixPeak.hpk_of_upper_nonempty` gives `hpk`.

## Provenance

The three-part decomposition and the idea of choosing the interval so
that a pebble stays above the cut are Královič's (*Time and space
complexity of reversible pebbling*, RAIRO-ITA 38 (2004) 137–161,
doi:10.1051/ita:2004008, proof of Thm 3.4).  His Lemma 3.3 plays the role
of `CutFull.cutFull_lt` here.  The exchange argument below is not his —
he chooses a bounded interval on which the cut cell happens to stay
pebbled, whereas this file shows the property holds on the whole suffix
of an optimal play.
-/

namespace RevPebbling.UpperPersist

open RevPebbling.PebblingFoundations RevPebbling.GameReach
open RevPebbling.GameCost RevPebbling.CutOptimal
open RevPebbling.CutAccounting RevPebbling.LowerSuffixPeak

/-- A board with no pebbles is the empty board. -/
theorem eq_emptyBoard_of_ones_zero : ∀ (c : Board), ones c = 0 →
    c = emptyBoard c.length
  | [], _ => rfl
  | a :: t, h => by
      cases a with
      | true => simp [ones] at h
      | false =>
          have ht : ones t = 0 := by simpa [ones] using h
          have := eq_emptyBoard_of_ones_zero t ht
          show false :: t = emptyBoard (t.length + 1)
          rw [show emptyBoard (t.length + 1) = false :: emptyBoard t.length from rfl,
              ← this]

/-- Every move kept by `keepBelow (x+1)` is below the cut. -/
theorem keepBelow_lt {x : Nat} {t : List Nat} {i : Nat}
    (h : i ∈ keepBelow (x + 1) t) : i < x + 1 := by
  have := List.of_mem_filter h
  simpa using this

/-- **THE SPLICED PLAY REACHES THE SAME BOARD.**  If the region above the
cut is empty at time `q`, then replaying only the lower moves of the
first `q` steps lands on exactly the configuration at time `q`. -/
theorem exec_keepBelow_prefix {n x q : Nat} {s : List Nat}
    (hx : x + 1 ≤ n)
    (hup : ones ((execB (emptyBoard n) (s.take q)).drop (x + 1)) = 0) :
    execB (emptyBoard n) (keepBelow (x + 1) (s.take q))
      = execB (emptyBoard n) (s.take q) := by
  have hlen : (emptyBoard (x + 1)).length = x + 1 := by simp
  have hrange : ∀ i ∈ keepBelow (x + 1) (s.take q), i < (emptyBoard (x + 1)).length := by
    intro i hi; rw [hlen]; exact keepBelow_lt hi
  have hsplit : emptyBoard n = emptyBoard (x + 1) ++ emptyBoard (n - (x + 1)) := by
    rw [← emptyBoard_split]
    congr 1
    omega
  -- the lower half is the truncation of the configuration at time q
  have hlow : execB (emptyBoard (x + 1)) (keepBelow (x + 1) (s.take q))
      = (execB (emptyBoard n) (s.take q)).take (x + 1) := by
    have h := execB_keepBelow (x + 1) (s.take q) (emptyBoard n)
    have ht : (emptyBoard n).take (x + 1) = emptyBoard (x + 1) := by
      show (List.replicate n false).take (x + 1) = List.replicate (x + 1) false
      rw [List.take_replicate, Nat.min_eq_left hx]
    rw [ht] at h
    exact h.symm
  -- the upper half is empty
  have hclen : (execB (emptyBoard n) (s.take q)).length = n := by
    rw [CutVocabulary.execB_length]; simp
  have hdrop : (execB (emptyBoard n) (s.take q)).drop (x + 1)
      = emptyBoard (n - (x + 1)) := by
    have h := eq_emptyBoard_of_ones_zero _ hup
    rw [List.length_drop, hclen] at h
    exact h
  calc execB (emptyBoard n) (keepBelow (x + 1) (s.take q))
      = execB (emptyBoard (x + 1)) (keepBelow (x + 1) (s.take q))
          ++ emptyBoard (n - (x + 1)) := by
        rw [hsplit, execB_pad _ _ _ hrange]
    _ = (execB (emptyBoard n) (s.take q)).take (x + 1)
          ++ (execB (emptyBoard n) (s.take q)).drop (x + 1) := by
        rw [hlow, hdrop]
    _ = execB (emptyBoard n) (s.take q) := List.take_append_drop _ _

/-- **ONCE ABOVE THE CUT, ALWAYS ABOVE IT.**  In a play of minimum
length, if some move before time `q` is above the cut, then the region
above the cut is not empty at time `q`.

Otherwise the moves above the cut before `q` can be deleted, giving a
strictly shorter legal play with the same endpoints and no larger
peak. -/
theorem upper_nonempty_of_optimal {n S x q : Nat} {s : List Nat}
    (hx : x + 1 ≤ n)
    (hr : ∀ i ∈ s, i < n)
    (hleg : legalB (emptyBoard n) s = true)
    (hex : execB (emptyBoard n) s = doneBoard n)
    (hpeak : maxOnes (emptyBoard n) s ≤ S)
    (hopt : s.length ≤ gameF n S)
    (hmove : shiftAbove x (s.take q) ≠ []) :
    1 ≤ ones ((execB (emptyBoard n) (s.take q)).drop (x + 1)) := by
  by_contra hc
  have hup : ones ((execB (emptyBoard n) (s.take q)).drop (x + 1)) = 0 := by omega
  -- the spliced play
  have hcfg := exec_keepBelow_prefix (n := n) (x := x) (q := q) (s := s) hx hup
  have hsplit : emptyBoard n = emptyBoard (x + 1) ++ emptyBoard (n - (x + 1)) := by
    rw [← emptyBoard_split]; congr 1; omega
  have hlen1 : (emptyBoard (x + 1)).length = x + 1 := by simp
  have hrange : ∀ i ∈ keepBelow (x + 1) (s.take q), i < (emptyBoard (x + 1)).length := by
    intro i hi; rw [hlen1]; exact keepBelow_lt hi
  -- prefix legality, via padding
  have hlegPre : legalB (emptyBoard n) (keepBelow (x + 1) (s.take q)) = true := by
    have hb := legalB_keepBelow (x + 1) (s.take q) (emptyBoard n) (legal_take q hleg)
    have ht : (emptyBoard n).take (x + 1) = emptyBoard (x + 1) := by
      show (List.replicate n false).take (x + 1) = List.replicate (x + 1) false
      rw [List.take_replicate, Nat.min_eq_left hx]
    rw [ht] at hb
    rw [hsplit, legalB_pad _ _ _ hrange]
    exact hb
  -- suffix legality from the same board
  have hlegSuf : legalB (execB (emptyBoard n) (s.take q)) (s.drop q) = true := by
    have h := hleg
    rw [← List.take_append_drop q s, legal_append, Bool.and_eq_true] at h
    exact h.2
  set t := keepBelow (x + 1) (s.take q) ++ s.drop q with ht
  have hlegT : legalB (emptyBoard n) t = true := by
    rw [ht, legal_append, hlegPre, hcfg, hlegSuf]
    simp
  have hexT : execB (emptyBoard n) t = doneBoard n := by
    rw [ht, exec_append, hcfg, ← exec_append, List.take_append_drop]
    exact hex
  have hrT : ∀ i ∈ t, i < n := by
    intro i hi
    rw [ht] at hi
    rcases List.mem_append.mp hi with h | h
    · have := keepBelow_lt h; omega
    · exact hr i (List.mem_of_mem_drop h)
  -- the peak cannot have risen
  have hpkT : maxOnes (emptyBoard n) t ≤ S := by
    rw [ht, maxOnes_append, hcfg]
    have h1 : maxOnes (emptyBoard n) (keepBelow (x + 1) (s.take q)) ≤ S := by
      rw [hsplit, maxOnes_pad _ _ _ hrange]
      have hkb := CutPlays.maxOnes_keepBelow_le (x + 1) (emptyBoard n) (s.take q)
      have ht' : (emptyBoard n).take (x + 1) = emptyBoard (x + 1) := by
        show (List.replicate n false).take (x + 1) = List.replicate (x + 1) false
        rw [List.take_replicate, Nat.min_eq_left hx]
      rw [ht'] at hkb
      have h2 := maxOnes_take_le (emptyBoard n) s q
      have h3 : ones (emptyBoard (n - (x + 1))) = 0 := ones_emptyBoard _
      omega
    have h2 : maxOnes (execB (emptyBoard n) (s.take q)) (s.drop q) ≤ S := by
      have h := maxOnes_append (emptyBoard n) (s.take q) (s.drop q)
      rw [List.take_append_drop] at h
      omega
    omega
  -- but it is strictly shorter
  have hcut := length_cut x (s.take q)
  have hpos : 0 < (shiftAbove x (s.take q)).length := by
    cases hsa : shiftAbove x (s.take q) with
    | nil => exact absurd hsa hmove
    | cons a l => simp [hsa]
  have hlenT : t.length < s.length := by
    have hq : (s.take q).length + (s.drop q).length = s.length := by
      rw [← List.length_append, List.take_append_drop]
    rw [ht, List.length_append]
    omega
  have := gameF_le (n := n) (S := S) ⟨t, Nat.le_refl _, hrT, hlegT, hexT, hpkT⟩
  omega

end RevPebbling.UpperPersist
