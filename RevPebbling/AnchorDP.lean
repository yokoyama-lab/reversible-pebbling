import RevPebbling.AnchorPacked
import RevPebbling.AnchorGrid
import RevPebbling.CompositionAnchor

/-!
# The anchor DP, and the certificate it emits (this work)

`CompositionAnchor.midpoint_composition` accepts **any** function
`L : Nat → Nat → Nat` obeying

  `L 0 v ≤ 1`,
  `L (t+1) v ≤ L t v  ∨  ∃ w, 1 ≤ w < v ∧
      L (t+1) v ≤ L t v + min (L t (v - w)) (L (t+1) w)`,

and turns a finite certificate `2^t ≤ L t v*` into the unconditional
midpoint bound `m_{S+t} ≤ m_S * v*` for every space level `S`.

This file builds such an `L` by running the DP of `scripts/m33_anchor_c.c`
inside Lean, on the grid of `AnchorGrid` and with the packed values of
`AnchorPacked`.

## Why the loop needs no invariant

Reasoning about the two-pointer's optimality would be painful and is
**not needed**: the recursion only ever asks for *some* split.  So each
cell is defined as

  `Lc[i] = flAdd (Lp[i]) (min (Lp[rdIndex M i j]) (Lc[j]))`

for the `j` the loop happens to pick, and `step` returns that `j` as
well.  A `Bool` checker (`okRow`) then confirms, cell by cell, that the
row really has this shape — together with `wf` and monotonicity in the
index.  Proving "the checker passed ⇒ the inequality holds" is easy;
this is the same certification pattern the RLE layer uses.

If the loop ever picked a worse `j`, the certificate would simply come
out weaker — never wrong.
-/

namespace RevPebbling.AnchorDP

open RevPebbling.AnchorPacked RevPebbling.AnchorGrid

/-- One DP row, with the split index chosen for each cell. -/
def step (M N : Nat) (Lp : Array Nat) : Array Nat × Array Nat := Id.run do
  let mut Lc : Array Nat := Array.replicate N flOne
  let mut J : Array Nat := Array.replicate N 0
  let mut j := 0
  for i in [1:N] do
    -- advance the crossover pointer (monotone in `i`)
    for _ in [0:N] do
      if j + 1 ≤ i - 1 && Lc[j + 1]! ≤ Lp[rdIndex M i (j + 1)]! then
        j := j + 1
      else
        break
    let mut bj := j
    let mut best := min (Lp[rdIndex M i j]!) (Lc[j]!)
    if j + 1 ≤ i - 1 then
      let c2 := min (Lp[rdIndex M i (j + 1)]!) (Lc[j + 1]!)
      if best < c2 then
        best := c2
        bj := j + 1
    Lc := Lc.set! i (flAdd (Lp[i]!) best)
    J := J.set! i bj
  return (Lc, J)

/-- The row for `T = k + 2`. -/
def rows (M N : Nat) : Nat → Array Nat
  | 0 => Array.replicate N flOne
  | k + 1 => (step M N (rows M N k)).1

/-- Cell-by-cell check of one transition: normalised, monotone in the
index, and of the shape the recursion licenses. -/
def okRow (M N : Nat) (Lp Lc J : Array Nat) : Bool :=
  (Lc[0]! == flOne) &&
  (List.range N).all fun i =>
    decide (wf (Lc[i]!)) &&
    (i == 0 ||
      (decide (J[i]! < i) &&
        (Lc[i - 1]! ≤ Lc[i]!) &&
        (Lc[i]! == flAdd (Lp[i]!) (min (Lp[rdIndex M i (J[i]!)]!) (Lc[J[i]!]!)))))

def okStep (M N : Nat) (Lp : Array Nat) : Bool :=
  okRow M N Lp (step M N Lp).1 (step M N Lp).2

/-- Run and check `n` transitions in a single pass. -/
def verifyAux (M N : Nat) : Nat → Array Nat → Bool
  | 0, _ => true
  | n + 1, Lp =>
      let r := step M N Lp
      okRow M N Lp r.1 r.2 && verifyAux M N n r.1

def verify (M N K : Nat) : Bool := verifyAux M N K (Array.replicate N flOne)

/-- Iterating `step` from the left — the shape `verifyAux` walks. -/
def iter (M N : Nat) : Nat → Array Nat → Array Nat
  | 0, A => A
  | n + 1, A => iter M N n (step M N A).1

theorem iter_succ (M N : Nat) :
    ∀ (n : Nat) (A : Array Nat), iter M N (n + 1) A = (step M N (iter M N n A)).1
  | 0, _ => rfl
  | n + 1, A => by
      show iter M N (n + 1) (step M N A).1 = _
      rw [iter_succ M N n (step M N A).1]
      rfl

theorem rows_eq_iter (M N : Nat) (k : Nat) :
    rows M N k = iter M N k (Array.replicate N flOne) := by
  induction k with
  | zero => rfl
  | succ k ih => show (step M N (rows M N k)).1 = _; rw [ih, iter_succ]

/-- The checker's verdict transfers to every row it visited. -/
theorem okStep_of_verifyAux (M N : Nat) :
    ∀ (n : Nat) (Lp : Array Nat), verifyAux M N n Lp = true →
      ∀ k, k < n → okStep M N (iter M N k Lp) = true
  | 0, _, _, _, hk => absurd hk (by omega)
  | n + 1, Lp, h, k, hk => by
      have h' : okRow M N Lp (step M N Lp).1 (step M N Lp).2 = true ∧
          verifyAux M N n (step M N Lp).1 = true := by
        simpa [verifyAux, Bool.and_eq_true] using h
      match k with
      | 0 => exact h'.1
      | k + 1 =>
          have := okStep_of_verifyAux M N n (step M N Lp).1 h'.2 k (by omega)
          simpa [iter] using this

theorem okStep_of_verify {M N K : Nat} (h : verify M N K = true) {k : Nat}
    (hk : k < K) : okStep M N (rows M N k) = true := by
  rw [rows_eq_iter]
  exact okStep_of_verifyAux M N K _ h k hk


-- ------------------------------------------------------------------
-- From the checker's verdict to the recursion's inequality
-- ------------------------------------------------------------------

/-- What one passing cell says. -/
theorem cell_of_okRow {M N : Nat} {Lp Lc J : Array Nat}
    (h : okRow M N Lp Lc J = true) {i : Nat} (hi : i < N) :
    wf (Lc[i]!) ∧ (1 ≤ i →
      J[i]! < i ∧ Lc[i - 1]! ≤ Lc[i]! ∧
      Lc[i]! = flAdd (Lp[i]!) (min (Lp[rdIndex M i (J[i]!)]!) (Lc[J[i]!]!))) := by
  rw [okRow, Bool.and_eq_true, List.all_eq_true] at h
  have hmem : i ∈ List.range N := List.mem_range.mpr hi
  have hc := h.2 i hmem
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hc
  refine ⟨hc.1, ?_⟩
  intro hi1
  rcases hc.2 with h0 | hrest
  · omega
  · exact ⟨hrest.1.1, hrest.1.2, hrest.2⟩

/-- Rows are nondecreasing in the index. -/
theorem row_mono_of_okRow {M N : Nat} {Lp Lc J : Array Nat}
    (h : okRow M N Lp Lc J = true) :
    ∀ {i i' : Nat}, i ≤ i' → i' < N → Lc[i]! ≤ Lc[i']! := by
  intro i i' hle hlt
  induction i' with
  | zero => have : i = 0 := by omega
            rw [this]
  | succ n ih =>
      rcases Nat.eq_or_lt_of_le hle with rfl | hlt2
      · exact Nat.le_refl _
      · have hstep := (cell_of_okRow h hlt).2 (by omega)
        have : Lc[n]! ≤ Lc[n + 1]! := by simpa using hstep.2.1
        exact Nat.le_trans (ih (by omega) (by omega)) this

/-- **THE RECURSION'S INEQUALITY, IN VALUES.** -/
theorem kval_cell {M N : Nat} {Lp Lc J : Array Nat}
    (hwfp : ∀ i, i < N → wf (Lp[i]!))
    (h : okRow M N Lp Lc J = true) {i : Nat} (hi0 : 1 ≤ i) (hi : i < N)
    (hr : rdIndex M i (J[i]!) < N) :
    kval (Lc[i]!) ≤ kval (Lp[i]!)
      + min (kval (Lp[rdIndex M i (J[i]!)]!)) (kval (Lc[J[i]!]!)) := by
  obtain ⟨hj, _, heq⟩ := (cell_of_okRow h hi).2 hi0
  have hwf1 : wf (Lp[rdIndex M i (J[i]!)]!) := hwfp _ hr
  have hwf2 : wf (Lc[J[i]!]!) := (cell_of_okRow h (by omega)).1
  have hmin : kval (min (Lp[rdIndex M i (J[i]!)]!) (Lc[J[i]!]!))
      = min (kval (Lp[rdIndex M i (J[i]!)]!)) (kval (Lc[J[i]!]!)) := by
    rcases Nat.le_total (Lp[rdIndex M i (J[i]!)]!) (Lc[J[i]!]!) with hle | hle
    · rw [Nat.min_eq_left hle, Nat.min_eq_left (kval_mono hwf1 hwf2 hle)]
    · rw [Nat.min_eq_right hle, Nat.min_eq_right (kval_mono hwf2 hwf1 hle)]
  rw [heq, ← hmin]
  exact kval_flAdd_le _ _


theorem zero_of_okRow {M N : Nat} {Lp Lc J : Array Nat}
    (h : okRow M N Lp Lc J = true) : Lc[0]! = flOne := by
  rw [okRow, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

-- ------------------------------------------------------------------
-- The certificate function
-- ------------------------------------------------------------------

theorem replicate_get {N i x : Nat} (h : i < N) :
    (Array.replicate N x)[i]! = x := by
  rw [getElem!_pos _ _ (by simpa using h)]
  simp

theorem rows_zero (M N : Nat) : rows M N 0 = Array.replicate N flOne := rfl

/-- Every visited row is normalised. -/
theorem wf_rows {M N K : Nat} (hv : verify M N K = true) :
    ∀ k, k ≤ K → ∀ i, i < N → wf ((rows M N k)[i]!)
  | 0, _, i, hi => by rw [rows_zero, replicate_get hi]; exact wf_flOne
  | k + 1, hk, i, hi => by
      have h := okStep_of_verify hv (k := k) (by omega)
      have : (rows M N (k + 1))[i]! = ((step M N (rows M N k)).1)[i]! := rfl
      rw [this]
      exact (cell_of_okRow (M := M) h hi).1

/-- Every visited row is nondecreasing in the index. -/
theorem rows_mono {M N K : Nat} (hv : verify M N K = true) :
    ∀ k, k ≤ K → ∀ {i i' : Nat}, i ≤ i' → i' < N →
      (rows M N k)[i]! ≤ (rows M N k)[i']!
  | 0, _, i, i', hle, hlt => by
      rw [rows_zero, replicate_get (by omega), replicate_get hlt]
  | k + 1, hk, i, i', hle, hlt => by
      have h := okStep_of_verify hv (k := k) (by omega)
      exact row_mono_of_okRow (M := M) h hle hlt

/-- The certificate function `CompositionAnchor` is handed. -/
def Lg (M N K : Nat) (t v : Nat) : Nat := kval ((rows M N (min t K))[gidx M v]!)

/-- The largest value the grid can represent. -/
def Vcap (M N : Nat) : Nat := gval M (N - 1)

theorem Lg_base {M N K : Nat} (hN : 1 ≤ N) {v : Nat} (hv : 1 ≤ v)
    (hV : v ≤ Vcap M N) : Lg M N K 0 v ≤ 1 := by
  have hlt : gidx M v < N := gidx_lt hN hv hV
  show kval ((rows M N (min 0 K))[gidx M v]!) ≤ 1
  rw [Nat.min_eq_left (Nat.zero_le _), rows_zero, replicate_get hlt, kval_flOne]


theorem rows_zero_entry {M N K : Nat} (hN : 1 ≤ N) (hv : verify M N K = true) :
    ∀ k, k ≤ K → (rows M N k)[0]! = flOne
  | 0, _ => by rw [rows_zero, replicate_get hN]
  | k + 1, hk => by
      have h := okStep_of_verify hv (k := k) (by omega)
      exact zero_of_okRow (M := M) h

/-- **THE ONE-STEP PROPERTY.**  Either the row did not move, or the cell
was built from a split, and that split is a legal `w`. -/
theorem Lg_step {M N K : Nat} (hN : 1 ≤ N) (hv : verify M N K = true) (t v : Nat)
    (h1 : 1 ≤ v) (hV : v ≤ Vcap M N) :
    Lg M N K (t + 1) v ≤ Lg M N K t v ∨
      ∃ w, 1 ≤ w ∧ w < v ∧
        Lg M N K (t + 1) v
          ≤ Lg M N K t v + min (Lg M N K t (v - w)) (Lg M N K (t + 1) w) := by
  by_cases hK : K ≤ t
  · left
    have hmin : min (t + 1) K = min t K := by omega
    show kval ((rows M N (min (t + 1) K))[gidx M v]!)
      ≤ kval ((rows M N (min t K))[gidx M v]!)
    rw [hmin]
  · have ht1 : min t K = t := by omega
    have ht2 : min (t + 1) K = t + 1 := by omega
    have hilt : gidx M v < N := gidx_lt hN h1 hV
    have hgi : gval M (gidx M v) ≤ v := gval_gidx_le M v h1
    have hok := okStep_of_verify hv (k := t) (by omega)
    by_cases hi0 : gidx M v = 0
    · left
      show kval ((rows M N (min (t + 1) K))[gidx M v]!)
        ≤ kval ((rows M N (min t K))[gidx M v]!)
      rw [ht1, ht2, hi0, rows_zero_entry hN hv (t + 1) (by omega),
        rows_zero_entry hN hv t (by omega)]
    · right
      obtain ⟨j, hj⟩ : ∃ j, ((step M N (rows M N t)).2)[gidx M v]! = j := ⟨_, rfl⟩
      obtain ⟨hji, -, -⟩ := (cell_of_okRow (M := M) hok hilt).2 (by omega)
      rw [hj] at hji
      have hwlt : gval M j < v := Nat.lt_of_lt_of_le (gval_lt_of_lt M hji) hgi
      refine ⟨gval M j, gval_pos M j, hwlt, ?_⟩
      have hd1 : 1 ≤ v - gval M j := by omega
      have hdV : v - gval M j ≤ Vcap M N := by omega
      have hdlt : gidx M (v - gval M j) < N := gidx_lt hN hd1 hdV
      have hrd : gval M (rdIndex M (gidx M v) j) ≤ v - gval M j := by
        have h0 := gval_rdIndex_le M hji
        have hsub : gval M (gidx M v) - gval M j ≤ v - gval M j :=
          Nat.sub_le_sub_right hgi _
        omega
      have hrle : rdIndex M (gidx M v) j ≤ gidx M (v - gval M j) := le_gidx hd1 hrd
      have hrlt : rdIndex M (gidx M v) j < N := by omega
      have hwfp : ∀ x, x < N → wf ((rows M N t)[x]!) := wf_rows hv t (by omega)
      have hcell := kval_cell (M := M) hwfp hok (i := gidx M v) (by omega) hilt
        (by rw [hj]; exact hrlt)
      rw [hj] at hcell
      -- `rows M N (t+1)` is `(step M N (rows M N t)).1` by definition
      have hcell' : kval ((rows M N (t + 1))[gidx M v]!)
          ≤ kval ((rows M N t)[gidx M v]!)
            + min (kval ((rows M N t)[rdIndex M (gidx M v) j]!))
              (kval ((rows M N (t + 1))[j]!)) := hcell
      have hup : kval ((rows M N t)[rdIndex M (gidx M v) j]!)
          ≤ kval ((rows M N t)[gidx M (v - gval M j)]!) :=
        kval_mono (wf_rows hv t (by omega) _ hrlt)
          (wf_rows hv t (by omega) _ hdlt) (rows_mono hv t (by omega) hrle hdlt)
      show kval ((rows M N (min (t + 1) K))[gidx M v]!)
        ≤ kval ((rows M N (min t K))[gidx M v]!)
          + min (kval ((rows M N (min t K))[gidx M (v - gval M j)]!))
            (kval ((rows M N (min (t + 1) K))[gidx M (gval M j)]!))
      rw [ht1, ht2, gidx_gval]
      omega

/-- **THE CERTIFICATE.** -/
theorem Lg_cert {M N K : Nat} (hv : verify M N K = true) {istar : Nat}
    (hi : istar < N) (hc : flPow2 K ≤ (rows M N K)[istar]!) :
    2 ^ K ≤ Lg M N K K (gval M istar) := by
  show 2 ^ K ≤ kval ((rows M N (min K K))[gidx M (gval M istar)]!)
  rw [Nat.min_self, gidx_gval]
  have h := kval_mono (wf_flPow2 K) (wf_rows hv K (Nat.le_refl _) istar hi) hc
  rwa [kval_flPow2] at h


-- ------------------------------------------------------------------
-- The composition theorem, fed by the DP
-- ------------------------------------------------------------------

open RevPebbling.CompositionAnchor in
/-- **THE ANCHOR, AS A MIDPOINT BOUND FOR EVERY SPACE LEVEL.**  A single
`verify` run plus the certificate cell gives, unconditionally,

  `m_{S+K} ≤ m_S * gval M istar`   for every `S`.

Everything on the way is a theorem: the DP's own rounding (`kval_flAdd_le`,
`norm_le`) only ever weakens the value, and `CompositionAnchor` needs no
more than that. -/
theorem midv_le_of_verify {M N K : Nat} (hN : 1 ≤ N) (hv : verify M N K = true)
    {istar : Nat} (hi : istar < N) (hc : flPow2 K ≤ (rows M N K)[istar]!)
    (s : Nat) : midv (s + K) ≤ midv s * gval M istar := by
  refine midpoint_composition s (Vcap M N) K (gval M istar) (Lg M N K)
    (fun v h1 hV => Lg_base hN h1 hV)
    (fun t v h1 hV => Lg_step hN hv t v h1 hV)
    (gval_pos M istar) ?_ (Lg_cert hv hi hc)
  exact gval_mono M (by omega)

end RevPebbling.AnchorDP
