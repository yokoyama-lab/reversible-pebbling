import RevPebbling.AnchorDP

/-!
# The anchor DP, checked and read off in one pass (this work)

`AnchorCertify` spends **two** `native_decide` calls on each anchor:
`verify M N K` runs the DP and checks every row, and
`flPow2 K ≤ (rows M N K)[istar]!` runs the *same* DP again to read the
certificate cell.  At `T₀ = 1200` that is 2 × 1.8·10⁷ cells; the cost is
exactly twice what the certificate needs.

`certRun` runs it once.  `runAux` is `verifyAux` carrying the row it
ended on, with the verdict in an accumulator so that the recursion stays
tail-recursive — at `K ≈ 6000` transitions a non-tail-recursive fold
would put 6000 frames on the interpreter's stack.  `runAux_eq` says the
two components are exactly `verifyAux` and `iter`, so
`midv_le_of_certRun` is `AnchorDP.midv_le_of_verify` with its two
premisses read off one `Bool`.

Nothing here weakens the certificate: the same rows are computed, the
same checker is applied to every one of them, and the same cell is
compared against `2^K`.  The saving is only that the DP is not run
twice.
-/

namespace RevPebbling.AnchorRun

open RevPebbling.AnchorDP RevPebbling.AnchorPacked RevPebbling.AnchorGrid
open RevPebbling.CompositionAnchor

/-- Run and check `n` transitions, keeping the row they end on.  The
verdict is an accumulator, which keeps this tail-recursive. -/
def runAux (M N : Nat) : Nat → Array Nat → Bool → Bool × Array Nat
  | 0, A, ok => (ok, A)
  | n + 1, Lp, ok =>
      let r := step M N Lp
      runAux M N n r.1 (ok && okRow M N Lp r.1 r.2)

/-- **THE TWO COMPONENTS ARE `verifyAux` AND `iter`.** -/
theorem runAux_eq (M N : Nat) :
    ∀ (n : Nat) (A : Array Nat) (ok : Bool),
      runAux M N n A ok = (ok && verifyAux M N n A, iter M N n A)
  | 0, A, ok => by simp [runAux, verifyAux, iter]
  | n + 1, Lp, ok => by
      show runAux M N n (step M N Lp).1
          (ok && okRow M N Lp (step M N Lp).1 (step M N Lp).2) = _
      rw [runAux_eq M N n]
      show (_, _) = (_, _)
      have hv : verifyAux M N (n + 1) Lp
          = (okRow M N Lp (step M N Lp).1 (step M N Lp).2
              && verifyAux M N n (step M N Lp).1) := rfl
      have hi : iter M N (n + 1) Lp = iter M N n (step M N Lp).1 := rfl
      rw [hv, hi, Bool.and_assoc]

/-- One pass: run the DP, check every row, and compare the certificate
cell with `2^K`. -/
def certRun (M N K istar : Nat) : Bool :=
  let r := runAux M N K (Array.replicate N flOne) true
  r.1 && decide (flPow2 K ≤ r.2[istar]!)

/-- **THE ANCHOR, FROM ONE PASS.**  Same conclusion as
`AnchorDP.midv_le_of_verify`, with both of its premisses read off the
single `Bool` that `certRun` returns. -/
theorem midv_le_of_certRun {M N K istar : Nat} (hN : 1 ≤ N) (hi : istar < N)
    (h : certRun M N K istar = true) (s : Nat) :
    midv (s + K) ≤ midv s * gval M istar := by
  have hr := runAux_eq M N K (Array.replicate N flOne) true
  rw [show certRun M N K istar
        = ((runAux M N K (Array.replicate N flOne) true).1
            && decide (flPow2 K ≤ (runAux M N K (Array.replicate N flOne) true).2[istar]!))
      from rfl, hr] at h
  simp only [Bool.true_and, Bool.and_eq_true, decide_eq_true_eq] at h
  refine midv_le_of_verify hN ?_ hi ?_ s
  · exact h.1
  · rw [rows_eq_iter]; exact h.2

end RevPebbling.AnchorRun
