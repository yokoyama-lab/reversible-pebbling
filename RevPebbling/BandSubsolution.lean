import RevPebbling.CountRecursion
import RevPebbling.RowMax
import RevPebbling.ReadoutBridge

/-!
# Subsolution transfer with certified boundary zones

A Legendre-envelope shape is intended only in an interior band.  Pointwise
minimum/maximum gluing to a Pascal lower zone or a capped front need not
preserve the nonlinear split recursion.  This file avoids that false gluing:
the double induction uses the Legendre step inside `Band`, and invokes an
independently certified lower bound whenever it exits the band.
-/

namespace RevPebbling.BandSubsolution

open RevPebbling.CountRecursion
open RevPebbling.RowMax

/-- Abstract double induction with an arbitrary certified complement of the
interior band.  Children may leave `Band`; the induction then dispatches them
to `hboundary` instead of requiring a seam inequality across a glued kink. -/
theorem subsolution_le_of_band
    {C Psi : Nat → Nat → Nat} {Band : Nat → Nat → Prop} {S₀ : Nat}
    (hrec : ∀ s u w, 1 ≤ u + w →
      1 + C s (u + w) + min (C s u) (C (s + 1) w) ≤ C (s + 1) (u + w))
    (hbase : ∀ v, Psi S₀ v ≤ C S₀ v)
    (hboundary : ∀ s, S₀ ≤ s → ∀ v, ¬ Band s v → Psi s v ≤ C s v)
    (hsmall : ∀ s, S₀ ≤ s → ∀ v, Band (s + 1) v → v ≤ 1 →
      Psi (s + 1) v ≤ C (s + 1) v)
    (hstep : ∀ s, S₀ ≤ s → ∀ v, Band (s + 1) v → 2 ≤ v →
      ∃ u w, u + w = v ∧ 1 ≤ u ∧ 1 ≤ w ∧
        Psi (s + 1) v ≤ 1 + Psi s v + min (Psi s u) (Psi (s + 1) w)) :
    ∀ s, S₀ ≤ s → ∀ v, Psi s v ≤ C s v := by
  intro s hs
  induction s, hs using Nat.le_induction with
  | base => exact hbase
  | succ s hs ih =>
      intro v
      induction v using Nat.strong_induction_on with
      | _ v ihv =>
        by_cases hband : Band (s + 1) v
        · by_cases hv : v ≤ 1
          · exact hsmall s hs v hband hv
          · obtain ⟨u, w, huw, hu, hw, hPsi⟩ := hstep s hs v hband (by omega)
            have hwlt : w < v := by omega
            have hPw : Psi (s + 1) w ≤ C (s + 1) w := ihv w hwlt
            have hPu : Psi s u ≤ C s u := ih u
            have hPv : Psi s v ≤ C s v := ih v
            have hmin : min (Psi s u) (Psi (s + 1) w) ≤
                min (C s u) (C (s + 1) w) := min_le_min hPu hPw
            have hC := hrec s u w (by omega)
            rw [huw] at hC
            omega
        · exact hboundary (s + 1) (by omega) v hband

/-- The band transfer specialized to the reversible-pebbling count. -/
theorem subsolution_le_count_of_band
    {Psi : Nat → Nat → Nat} {Band : Nat → Nat → Prop} {S₀ : Nat}
    (hbase : ∀ v, Psi S₀ v ≤ countLe (rowIter S₀) v)
    (hboundary : ∀ s, S₀ ≤ s → ∀ v, ¬ Band s v →
      Psi s v ≤ countLe (rowIter s) v)
    (hsmall : ∀ s, S₀ ≤ s → ∀ v, Band (s + 1) v → v ≤ 1 →
      Psi (s + 1) v ≤ countLe (rowIter (s + 1)) v)
    (hstep : ∀ s, S₀ ≤ s → ∀ v, Band (s + 1) v → 2 ≤ v →
      ∃ u w, u + w = v ∧ 1 ≤ u ∧ 1 ≤ w ∧
        Psi (s + 1) v ≤ 1 + Psi s v + min (Psi s u) (Psi (s + 1) w)) :
    ∀ s, S₀ ≤ s → ∀ v, Psi s v ≤ countLe (rowIter s) v :=
  subsolution_le_of_band
    (fun s u w h => count_recursion_split s u w h)
    hbase hboundary hsmall hstep

/-- The exact Pascal certificate used at a low boundary. -/
theorem pascal_boundary (s k : Nat) :
    psum (s + 1) (k + 1) - 1 ≤ countLe (rowIter s) (2 ^ k) := by
  have h := count_partial_sum_lower s k
  omega

/-- Once `v` reaches the exact row maximum, the count is the full row. -/
theorem full_count_boundary {s v : Nat} (hfront : rowMax s ≤ v) :
    (rowIter s).length ≤ countLe (rowIter s) v := by
  obtain ⟨hsort, _⟩ := rowIter_invariant s
  unfold rowMax at hfront
  have hmax : listMax (rowIter s) ≤ v := hfront
  have hall : ∀ x ∈ rowIter s, x ≤ v := by
    intro x hx
    exact le_trans (le_listMax hx) hmax
  unfold countLe
  rw [List.countP_eq_length.mpr]
  exact fun x hx => by simpa using hall x hx

end RevPebbling.BandSubsolution
