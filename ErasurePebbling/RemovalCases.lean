import ErasurePebbling.UpperBound

/-!
# The removal lemma: stronger forms, two proved special cases, wider checks

`UpperBound.lean` reduces the upper bound of Conjecture B2 to `RemovalLemma p`:
a pebble whose predecessor is pebbled can be removed without raising the
potential `phi`.  This file records what the second attempt (2026-11-06)
established around that lemma.

## Stronger forms (statements only, checked by computer)

* `FreeRemoval p` (R′): a pebble whose *gap* is at most the threshold at the
  current count can be removed without raising `phi`.  `RemovalLemma` is the
  case gap = 1.  Computer check (`data/erasure/rcheck.c`): all gap sequences
  with `p = 5` and gaps `≤ 20`, `p = 6` and gaps `≤ 22`, `p = 7` and gaps
  `≤ 11`.
* `SlackRemoval p` (S): removing *any* pebble raises `phi` by at most its
  excess at the current count.  (S) implies (R′) implies `RemovalLemma`
  (`freeRemoval_of_slackRemoval`, `removalLemma_of_freeRemoval`).
  Same computer check.  (S) refines `phi_toggle_le_of_remove`
  (`2^(p−2)`); the two bounds together, `min(excess, 2^(p−2))`, match the
  measured maximum exactly.

Both forms are equivalent to "`phi` is invariant on the reversible
components of the game": a free removal (gap ≤ threshold) is reversible
(reach the predecessor with the free pebbles, remove, undo), every
reversible move is a free removal or its inverse, and free removals are
confluent (if `x` and `z` are both free then each stays free after the
other is removed, since the merged gap is at most `2·thr = thr'`).  So
every reversible component has a unique *reduced* board (no free pebble),
and (R′) says `phi` is the value at the reduced board.

## Two proved special cases of (R′)

* `phi_toggle_le_of_top`: removing the highest pebble never raises `phi`
  (no gap condition at all);
* `phi_toggle_le_of_lowest_free`: removing the lowest pebble when its gap
  (its node number) is at most the threshold never raises `phi`.

Both follow the recursion of `phi`: the pebble `z` chosen first by an
optimal order either is `x` (then `phi` drops by `exc x`), or lies on one
side of `x` where its gap is unchanged or merged with the small gap of `x`
and the doubled threshold absorbs the merge.  The general case fails to
close exactly when `z` is the *predecessor* of `x` (the pebble just below)
and has positive excess; `NOTES.md` §4 records the analysis of that case.
-/

namespace ErasurePebbling
namespace UpperBound

open RevPebbling.PebblingFoundations

/-! ## Stronger forms -/

/-- (R′) A pebble whose gap is at most the current threshold can be removed
without raising the potential. -/
def FreeRemoval (p : Nat) : Prop :=
  ∀ (b : Board) (x : Nat), x < b.length → nth b x = true → ones b ≤ p →
    gap b x ≤ thr p (ones b) → phi p (toggle b x) ≤ phi p b

/-- (S) Removing any pebble raises the potential by at most its excess. -/
def SlackRemoval (p : Nat) : Prop :=
  ∀ (b : Board) (x : Nat), x < b.length → nth b x = true → ones b ≤ p →
    phi p (toggle b x) ≤ phi p b + exc p b x

theorem removalLemma_of_freeRemoval {p : Nat} (hF : FreeRemoval p) : RemovalLemma p := by
  intro b x hl hx hok hk
  apply hF b x hl hx hk
  rw [gap_eq_one_of_okMove b hok]
  exact one_le_thr p _

theorem freeRemoval_of_slackRemoval {p : Nat} (hS : SlackRemoval p) : FreeRemoval p := by
  intro b x hl hx hk hg
  have h := hS b x hl hx hk
  have : exc p b x = 0 := by unfold exc; omega
  omega

/-! ## Special case 1: the highest pebble -/

/-- Removing the highest pebble never raises `phi`. -/
theorem phi_toggle_le_of_top (p : Nat) :
    ∀ (k : Nat) (b : Board) (x : Nat), ones b = k → ones b ≤ p → nth b x = true → x < b.length →
      (∀ j, x < j → nth b j = false) → phi p (toggle b x) ≤ phi p b := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
  intro b x hk hkp hx hl htop
  have hpos : 0 < ones b := ones_pos_of_nth hx
  obtain ⟨z, hzl, hz, hphi⟩ := phi_attained (p := p) hpos
  by_cases hzx : z = x
  · rw [hzx] at hphi
    omega
  -- `z` lies below `x`
  have hzlt : z < x := by
    rcases Nat.lt_or_ge z x with h | h
    · exact h
    · have : x < z := by omega
      rw [htop z this] at hz; simp at hz
  have hkz : ones (toggle b z) + 1 = ones b := ones_toggle_of_true hz hzl
  have hxz : nth (toggle b z) x = true := by rw [nth_toggle_ne b hzx]; exact hx
  have hxzl : x < (toggle b z).length := by rw [length_toggle]; exact hl
  have htop' : ∀ j, x < j → nth (toggle b z) j = false := by
    intro j hj
    rw [nth_toggle_ne b (by omega)]
    exact htop j hj
  have h2 := ih (ones (toggle b z)) (by omega) (toggle b z) x rfl (by omega) hxz hxzl htop'
  have hzx' : nth (toggle b x) z = true := by rw [nth_toggle_ne b (Ne.symm hzx)]; exact hz
  have hzxl : z < (toggle b x).length := by rw [length_toggle]; exact hzl
  have h1 := phi_le (p := p) hzx' hzxl
  rw [toggle_comm b (Ne.symm hzx)] at h1
  have hkx : ones (toggle b x) + 1 = ones b := ones_toggle_of_true hx hl
  have hthr : thr p (ones b) ≤ thr p (ones (toggle b x)) := thr_le_thr_of_le p (by omega)
  have hg : gap (toggle b x) z = gap b z := gap_toggle_of_le b x z (Nat.le_of_lt hzlt)
  have h3 : exc p (toggle b x) z ≤ exc p b z := by
    unfold exc; rw [hg]; omega
  omega

/-! ## Special case 2: the lowest pebble, when it is free -/

/-- Removing the lowest pebble never raises `phi` when its gap (= its node
number) is at most the threshold at the current count. -/
theorem phi_toggle_le_of_lowest_free (p : Nat) :
    ∀ (k : Nat) (b : Board) (x : Nat), ones b = k → ones b ≤ p → nth b x = true → x < b.length →
      (∀ j, j < x → nth b j = false) → gap b x ≤ thr p (ones b) →
      phi p (toggle b x) ≤ phi p b := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
  intro b x hk hkp hx hl hlow hg
  have hpos : 0 < ones b := ones_pos_of_nth hx
  obtain ⟨z, hzl, hz, hphi⟩ := phi_attained (p := p) hpos
  by_cases hzx : z = x
  · rw [hzx] at hphi
    omega
  -- `z` lies above `x`
  have hxlt : x < z := by
    rcases Nat.lt_or_ge x z with h | h
    · exact h
    · have : z < x := by omega
      rw [hlow z this] at hz; simp at hz
  have hkz : ones (toggle b z) + 1 = ones b := ones_toggle_of_true hz hzl
  have hxz : nth (toggle b z) x = true := by rw [nth_toggle_ne b hzx]; exact hx
  have hxzl : x < (toggle b z).length := by rw [length_toggle]; exact hl
  have hlow' : ∀ j, j < x → nth (toggle b z) j = false := by
    intro j hj
    rw [nth_toggle_ne b (by omega)]
    exact hlow j hj
  have hgz : gap (toggle b z) x = gap b x := gap_toggle_of_le b z x (Nat.le_of_lt hxlt)
  have hthrz : thr p (ones b) ≤ thr p (ones (toggle b z)) := thr_le_thr_of_le p (by omega)
  have h2 := ih (ones (toggle b z)) (by omega) (toggle b z) x rfl (by omega) hxz hxzl hlow'
    (by rw [hgz]; omega)
  have hzx' : nth (toggle b x) z = true := by rw [nth_toggle_ne b (Ne.symm hzx)]; exact hz
  have hzxl : z < (toggle b x).length := by rw [length_toggle]; exact hzl
  have h1 := phi_le (p := p) hzx' hzxl
  rw [toggle_comm b (Ne.symm hzx)] at h1
  have hkx : ones (toggle b x) + 1 = ones b := ones_toggle_of_true hx hl
  have hk2 : 2 ≤ ones b := two_le_ones hx hz (Ne.symm hzx)
  have hT2 : thr p (ones (toggle b x)) = 2 * thr p (ones b) := by
    have := thr_pred p (k := ones b) (by omega) hkp
    rw [← this]; congr 1; omega
  have h3 : exc p (toggle b x) z ≤ exc p b z := by
    rcases Classical.em (Between b x z) with hb | hnb
    · have hgb : gap (toggle b x) z = gap b z := gap_toggle_of_between b hxlt hb
      unfold exc; rw [hgb, hT2]; omega
    · have hgs : gap (toggle b x) z = gap b z + gap b x := gap_toggle_of_not_between b hx hxlt hnb
      unfold exc; rw [hgs, hT2]; omega
  omega

/-! ## Wider computational anchors

`freeCheck p n` evaluates `FreeRemoval p` on all boards of length `n`
(the pebble count is at most `p` by the `ones` test); `slackCheck` does the
same for `SlackRemoval`.  Sanity checks, not proofs. -/

def freeCheck (p n : Nat) : Bool :=
  (allBoards n).all fun b =>
    !(decide (ones b ≤ p)) ||
      (List.range n).all fun x =>
        !(nth b x && decide (gap b x ≤ thr p (ones b))) || decide (phi p (toggle b x) ≤ phi p b)

def slackCheck (p n : Nat) : Bool :=
  (allBoards n).all fun b =>
    !(decide (ones b ≤ p)) ||
      (List.range n).all fun x =>
        !(nth b x) || decide (phi p (toggle b x) ≤ phi p b + exc p b x)

#guard freeCheck 2 10
#guard freeCheck 3 11
#guard freeCheck 4 12
#guard freeCheck 5 13
#guard slackCheck 2 10
#guard slackCheck 3 11
#guard slackCheck 4 12
#guard slackCheck 5 13

end UpperBound
end ErasurePebbling
