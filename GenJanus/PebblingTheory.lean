import GenJanus.PebblingGame
import Std

/-!
# Machine-checked verification of the reversible-pebbling literature

We formalise and check the central published theorems on reversible
pebbling of chains.  Scope labels are explicit:

* GENERAL (unbounded) proofs: closed forms of Bennett-family recurrences
  (Pesu–Phillips 2015, Sec. 2.3).
* BOUNDED exhaustive checks (native_decide over complete finite ranges):
  Knill 1995 Thm 2.1 (recursion = game optimum), Thm 2.3 (finiteness
  characterisation), Obs 2.2(i) (2n-1 floor), selected Table 1 entries;
  Královič 2004 Thm 3.1 (complete-variant space) and the Thm 3.4 time
  recurrence inequality against exact values; Pesu–Phillips Prop 3.4 and
  Prop 3.6; and the bridge A(n,k) ≤ C(n+k-1,k) matching Knill's
  Lemma 2.9 upper bound.

The game-side optimum reuses `GenJanus.Hard18.mstar` (clean-reach BFS).
-/

namespace GenJanus.PebblingTheory

open GenJanus.Hard18 (mstar popcount)

-- ------------------------------------------------------------------
-- Knill's recursion F(n,S)  (Thm 2.1; none = infinite)
-- ------------------------------------------------------------------

def optAdd : Option Nat → Option Nat → Option Nat
  | some a, some b => some (a + b)
  | _, _ => none

def optMin : Option Nat → Option Nat → Option Nat
  | some a, some b => some (min a b)
  | some a, none => some a
  | none, b => b

/-- Row S of the DP table (length N), given row S-1. -/
def knillRow (N : Nat) (prev : List (Option Nat)) : List (Option Nat) :=
  (List.range N).foldl
    (fun cur n1 =>
      if n1 = 0 then cur ++ [some 1]
      else
        let n := n1 + 1
        let val := (List.range (n - 1)).foldl
          (fun acc m1 =>
            let m := m1 + 1
            optMin acc
              (optAdd (cur[m - 1]?.getD none)
                (optAdd (prev[m - 1]?.getD none)
                  (prev[n - m - 1]?.getD none))))
          none
        cur ++ [val])
    []

def knillTable (N Smax : Nat) : List (List (Option Nat)) :=
  let row1 : List (Option Nat) :=
    (List.range N).map fun n1 => if n1 = 0 then some 1 else none
  (List.range (Smax - 1)).foldl
    (fun rows _ => rows ++ [knillRow N (rows.getLast!)])
    [row1]

/-- F(n,S) by Knill's recursion, on a fixed 64 × 24 table. -/
def F (n S : Nat) : Option Nat :=
  ((knillTable 64 24)[S - 1]?.getD [])[n - 1]?.getD none

/-- BOUNDED Thm 2.1: the recursion agrees with the game optimum
(including infinities) on the complete grid n ≤ 12, S ≤ 5. -/
theorem knill_recursion_agrees_with_game :
    ((List.range 12).all fun n1 =>
      (List.range 5).all fun s1 =>
        F (n1 + 1) (s1 + 1) == mstar (n1 + 1) (s1 + 1)) = true := by
  native_decide

/-- BOUNDED Thm 2.3: F(n,S) is finite iff n ≤ 2^(S-1), on the complete
grid n ≤ 64, S ≤ 8. -/
theorem knill_finiteness_characterisation :
    ((List.range 64).all fun n1 =>
      (List.range 8).all fun s1 =>
        (F (n1 + 1) (s1 + 1)).isSome == decide (n1 + 1 ≤ 2 ^ s1)) = true := by
  native_decide

/-- BOUNDED Obs 2.2(i): F(n,S) = 2n-1 whenever S ≥ n (checked at S = n,
n ≤ 20; monotonicity in S is checked separately below). -/
theorem knill_floor :
    ((List.range 20).all fun n1 =>
      F (n1 + 1) (n1 + 1) == some (2 * (n1 + 1) - 1)) = true := by
  native_decide

/-- BOUNDED Obs 2.2(ii): F is nonincreasing in S (grid n ≤ 32, S ≤ 7). -/
theorem knill_monotone_in_space :
    ((List.range 32).all fun n1 =>
      (List.range 7).all fun s1 =>
        match F (n1 + 1) (s1 + 1), F (n1 + 1) (s1 + 2) with
        | some a, some b => b ≤ a
        | none, _ => true
        | some _, none => false) = true := by
  native_decide

/-- BOUNDED selected entries of Knill's Table 1 (as printed in
LAUR-95-2258): the published table is correct at these entries. -/
theorem knill_table_entries :
    F 8 4 = some 25 ∧ F 8 5 = some 21 ∧ F 8 6 = some 19 ∧
    F 16 5 = some 71 ∧ F 16 6 = some 51 ∧ F 16 7 = some 49 ∧
    F 32 6 = some 193 := by
  native_decide

-- ------------------------------------------------------------------
-- Královič's complete-computation variant (empty → all covered → empty)
-- ------------------------------------------------------------------

/-- States are (pebble mask, max covered index), encoded as
mask * (n+1) + mc; popcount(mask) ≤ p. -/
def cSucc (n p : Nat) (code : Nat) : List Nat :=
  let st := code / (n + 1)
  let mc := code % (n + 1)
  (List.range n).filterMap fun i =>
    if i = 0 || st / 2 ^ (i - 1) % 2 = 1 then
      let ns := st ^^^ 2 ^ i
      if popcount ns ≤ p then
        some (ns * (n + 1) +
          (if ns / 2 ^ i % 2 = 1 then max mc (i + 1) else mc))
      else none
    else none

def cBfs (n p : Nat) : Nat → Std.HashSet Nat → List Nat → Nat → Option Nat
  | 0, _, _, _ => none
  | fuel + 1, visited, frontier, steps =>
      if frontier.contains n then some steps  -- code of (mask 0, mc n) is n
      else
        let (next, visited') := frontier.foldl
          (fun (acc : List Nat × Std.HashSet Nat) code =>
            (cSucc n p code).foldl
              (fun (acc : List Nat × Std.HashSet Nat) c =>
                if acc.2.contains c then acc
                else (c :: acc.1, acc.2.insert c))
              acc)
          ([], visited)
        match next with
        | [] => none
        | _ => cBfs n p fuel visited' next (steps + 1)

/-- Exact minimal time of a complete computation with ≤ p pebbles. -/
def T (n p : Nat) : Option Nat :=
  cBfs n p 300 (Std.HashSet.emptyWithCapacity.insert 0) [0] 0

/-- BOUNDED Thm 3.1 (Královič): a complete computation with p pebbles
exists iff n ≤ 2^p - 1, on the complete grid n ≤ 16, p ≤ 4. -/
theorem kralovic_space_characterisation :
    ((List.range 16).all fun n1 =>
      (List.range 4).all fun p1 =>
        (T (n1 + 1) (p1 + 1)).isSome ==
          decide (n1 + 1 ≤ 2 ^ (p1 + 1) - 1)) = true := by
  native_decide

/-- The exact space-optimal complete-computation times (new values). -/
theorem exact_complete_times :
    T 1 1 = some 2 ∧ T 3 2 = some 8 ∧ T 7 3 = some 26 ∧
    T 15 4 = some 76 := by
  native_decide

/-- BOUNDED Thm 3.4 (Královič): the recurrence inequality
T(2^{p+1}-1, p+1) ≥ 2(2^p-1) + 2 + 2 T(2^p-1, p) holds for the exact
values (p ≤ 3); at p = 1 it is an equality. -/
theorem kralovic_time_recurrence :
    ((List.range 3).all fun p1 =>
      let p := p1 + 1
      match T (2 ^ (p + 1) - 1) (p + 1), T (2 ^ p - 1) p with
      | some tBig, some tSmall =>
          2 * (2 ^ p - 1) + 2 + 2 * tSmall ≤ tBig
      | _, _ => false) = true := by
  native_decide

-- ------------------------------------------------------------------
-- Pesu–Phillips 2015: Bennett-family recurrences (GENERAL proofs)
-- ------------------------------------------------------------------

/-- Bennett move-count recurrence R(n,0)=1, R(n,k+1)=(2n-1)R(n,k). -/
def bennettR (n : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => (2 * n - 1) * bennettR n k

/-- GENERAL: closed form R(n,k) = (2n-1)^k (Pesu–Phillips Sec. 2.3). -/
theorem bennettR_closed (n k : Nat) : bennettR n k = (2 * n - 1) ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [bennettR, ih, Nat.pow_succ, Nat.mul_comm]

/-- Bennett pebble-count recurrence P(n,0)=1, P(n,k+1)=P(n,k)+n-1. -/
def bennettP (n : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => bennettP n k + (n - 1)

/-- GENERAL: closed form P(n,k) = k(n-1)+1 (Pesu–Phillips Sec. 2.3). -/
theorem bennettP_closed (n k : Nat) : bennettP n k = k * (n - 1) + 1 := by
  induction k with
  | zero => simp [bennettP]
  | succ k ih => simp [bennettP, ih, Nat.succ_mul]; omega

/-- k-ratic advancement A(n,0)=1, A(n,k+1)=1+Σ_{i=1}^{n-1} A(i,k). -/
def kraticA (n : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => 1 + ((List.range (n - 1)).map fun i => kraticA (i + 1) k).sum

/-- k-ratic move count S(n,0)=1, S(n,k+1)=1+2Σ_{i=1}^{n-1} S(i,k). -/
def kraticS (n : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => 1 + 2 * ((List.range (n - 1)).map fun i => kraticS (i + 1) k).sum

/-- BOUNDED Prop 3.4 (Pesu–Phillips): S(n,k) ≤ 2^k A(n,k)
(complete grid n ≤ 12, k ≤ 8). -/
theorem pesu_prop34 :
    ((List.range 12).all fun n1 =>
      (List.range 8).all fun k =>
        kraticS (n1 + 1) k ≤ 2 ^ k * kraticA (n1 + 1) k) = true := by
  native_decide

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

def choose : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => choose n k + choose n (k + 1)

/-- BOUNDED Prop 3.6 (Pesu–Phillips): k^k ≥ 2^{k-1} k! for k ≤ 17. -/
theorem pesu_prop36 :
    ((List.range 17).all fun k1 =>
      let k := k1 + 1
      2 ^ (k - 1) * fact k ≤ k ^ k) = true := by
  native_decide

/-- BOUNDED bridge: the k-ratic advancement never exceeds Knill's 1995
upper bound C(n+k-1, k) on the optimal trade-off frontier (Lemma 2.9 of
LAUR-95-2258); grid n ≤ 12, k ≤ 8.  This makes precise the sense in
which the k-ratic performance point was already pinned down in 1995. -/
theorem kratic_within_knill_bound :
    ((List.range 12).all fun n1 =>
      (List.range 8).all fun k =>
        kraticA (n1 + 1) k ≤ choose (n1 + k) k) = true := by
  native_decide

/-- BOUNDED: the k-ratic family saturates the clean-reach limit:
max over k ≤ n of A(n,k) equals 2^{n-1} for n ≤ 10 (matches Knill's
Thm 2.3 / our reach characterisation). -/
theorem kratic_saturates_reach :
    ((List.range 10).all fun n1 =>
      let n := n1 + 1
      (((List.range (n + 1)).map fun k => kraticA n k).foldl max 0)
        == 2 ^ (n - 1)) = true := by
  native_decide


-- ------------------------------------------------------------------
-- Variant bridge: complete-time T vs reach-time F, via half-reach H
-- ------------------------------------------------------------------

/-- Half-reach H(n,p): minimum moves of a legal peak-≤p computation from
the empty chain to any board with node n pebbled.  State = pebble mask
only; stop as soon as bit (n-1) is set. -/
def hSucc (n p mask : Nat) : List Nat :=
  (List.range n).filterMap fun i =>
    if i = 0 || mask / 2 ^ (i - 1) % 2 = 1 then
      let ns := mask ^^^ 2 ^ i
      if popcount ns ≤ p then some ns else none
    else none

def hBfs (n p : Nat) : Nat → Std.HashSet Nat → List Nat → Nat → Option Nat
  | 0, _, _, _ => none
  | fuel + 1, visited, frontier, steps =>
      if frontier.any (fun m => m / 2 ^ (n - 1) % 2 = 1) then some steps
      else
        let (next, visited') := frontier.foldl
          (fun (acc : List Nat × Std.HashSet Nat) mask =>
            (hSucc n p mask).foldl
              (fun (acc : List Nat × Std.HashSet Nat) c =>
                if acc.2.contains c then acc
                else (c :: acc.1, acc.2.insert c))
              acc)
          ([], visited)
        match next with
        | [] => none
        | _ => hBfs n p fuel visited' next (steps + 1)

def H (n p : Nat) : Option Nat :=
  hBfs n p 300 (Std.HashSet.emptyWithCapacity.insert 0) [0] 0

/-- BOUNDED bridge (Kr\'alovi\v{c} Lemma 3.2, exact form): the complete
computation time is exactly twice the half-reach, T(n,p) = 2 H(n,p), on
the full complete-domain grid n ≤ 15, p ≤ 4.  The general
`T(n,p) ≤ 2 H(n,p)` direction is proved constructively in
`PebblingFoundations.reverse_append_roundtrip`. -/
theorem bridge_complete_eq_twice_half :
    ((List.range 15).all fun n1 =>
      (List.range 4).all fun p1 =>
        match T (n1 + 1) (p1 + 1), H (n1 + 1) (p1 + 1) with
        | some t, some h => t == 2 * h
        | none, none => true
        | _, _ => false) = true := by
  native_decide

/-- BOUNDED linear regime: near the source the complete time exceeds the
reach time by exactly one move, T(n,p) = F(n,p) + 1 (p = 4, n = 1..7). -/
theorem bridge_linear_regime :
    ((List.range 7).all fun n1 =>
      match F (n1 + 1) 4, T (n1 + 1) 4 with
      | some f, some t => t == f + 1
      | _, _ => false) = true := by
  native_decide

/-- BOUNDED phenomenon: past the linear regime the ordering FLIPS -- a
complete computation (cover every node, return empty) can be strictly
CHEAPER than cleanly reaching the single far node, because the latter
must additionally clear all helper pebbles.  At the reach limits
F(8,4) = 25 > 24 = T(8,4) and F(16,5) = 71 > 58 = T(16,5). -/
theorem complete_can_beat_reach :
    T 8 4 = some 24 ∧ F 8 4 = some 25 ∧
    T 16 5 = some 58 ∧ F 16 5 = some 71 := by
  native_decide

-- ------------------------------------------------------------------
-- Corner-forced half-split lemma (this work): at the reach limit
-- n = 2^{p-1}, finiteness (Knill Thm 2.3) forces the minimiser of
-- Knill's recursion to the exact midpoint m = 2^{p-2}, so
--   f_p := F(2^{p-1}, p) = 2 f_{p-1} + F(2^{p-2}, p).
-- ------------------------------------------------------------------

/-- GENERAL arithmetic core of the forcing argument: if both children
of a split of 2^{k+1} fit under the child reach limit 2^k
(m ≤ 2^k from F(m, S-1) finite, 2^{k+1} - m ≤ 2^k from
F(n-m, S-1) finite, per Thm 2.3), the split is exactly the midpoint. -/
theorem corner_split_arith (k m : Nat)
    (h1 : m ≤ 2 ^ k) (h2 : 2 ^ (k + 1) - m ≤ 2 ^ k) : m = 2 ^ k := by
  have hsum : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by
    rw [Nat.pow_succ]; omega
  omega

/-- BOUNDED forcing at the reach limit: for n = 2^{p-1} every split
m ≠ 2^{p-2} has an infinite child term F(m, p-1) or F(n-m, p-1)
(checked over all splits, 3 ≤ p ≤ 7). Together with
`corner_split_arith` + `knill_finiteness_characterisation` this is the
full forcing argument. -/
theorem corner_split_forced :
    ((List.range 5).all fun p3 =>
      let p := p3 + 3
      let n := 2 ^ (p - 1)
      (List.range (n - 1)).all fun m1 =>
        let m := m1 + 1
        (m == 2 ^ (p - 2)) ||
          !((F m (p - 1)).isSome && (F (n - m) (p - 1)).isSome)) = true := by
  native_decide

/-- BOUNDED resulting exact recurrence f_p = 2 f_{p-1} + F(2^{p-2}, p)
for 2 ≤ p ≤ 7 (p = 7 uses the full table width n = 64). -/
theorem corner_half_split_recurrence :
    ((List.range 6).all fun p2 =>
      let p := p2 + 2
      match F (2 ^ (p - 1)) p, F (2 ^ (p - 2)) (p - 1), F (2 ^ (p - 2)) p with
      | some fp, some fprev, some fsame => fp == 2 * fprev + fsame
      | _, _, _ => false) = true := by
  native_decide

-- ------------------------------------------------------------------
-- Structure of the reach-limit difference row (this work).
--
-- Paper proof (notes/research-plan 追記6): rewriting Knill's recursion
-- through prefix sums gives the EXACT merge representation
--   Δ-row(S) = sorted merge of {2} ∪ Δ-row(S-1) ∪ B-stream,
--   B_i = Δ(i,S) + Δ(i,S-1),
-- from which sortedness, evenness, pointwise domination
-- Δ(n,S) ≤ Δ(n,S-1), and the five small-value count laws follow by
-- induction.  Below the representation and its consequences are
-- machine-checked exhaustively on the n ≤ 128, S ≤ 8 grid; the
-- general Lean formalisation of the merge lemma is future work.
-- ------------------------------------------------------------------

/-- Wider DP table for the structural laws: n ≤ 128, S ≤ 8. -/
def Fw (n S : Nat) : Option Nat :=
  ((knillTable 128 8)[S - 1]?.getD [])[n - 1]?.getD none

/-- Halved difference row at the reach limit:
[δ(2,S), …, δ(2^{S-1},S)], δ(n,S) = (F(n,S) - F(n-1,S)) / 2. -/
def deltaRow (S : Nat) : List Nat :=
  let row := (knillTable 128 8)[S - 1]?.getD []
  (List.range (2 ^ (S - 1) - 1)).map fun i =>
    match row[i + 1]?.getD none, row[i]?.getD none with
    | some a, some b => (a - b) / 2
    | _, _ => 0

def sortedLe : List Nat → Bool
  | [] => true
  | [_] => true
  | a :: b :: t => a ≤ b && sortedLe (b :: t)

/-- BOUNDED: every reach-limit difference is even (grid S ≤ 8). -/
theorem delta_even :
    ((List.range 7).all fun s1 =>
      let S := s1 + 2
      (List.range (2 ^ (S - 1) - 1)).all fun i =>
        match Fw (i + 2) S, Fw (i + 1) S with
        | some a, some b => (a - b) % 2 == 0
        | _, _ => false) = true := by
  native_decide

/-- BOUNDED: the difference rows are nondecreasing (S ≤ 8);
Knill's Lemma 2.5 monotonicity at the reach limit. -/
theorem delta_sorted :
    ((List.range 7).all fun s1 => sortedLe (deltaRow (s1 + 2))) = true := by
  native_decide

/-- BOUNDED merge representation (this work): the halved row of S is,
as a multiset, {1} ∪ row(S-1) ∪ {row(S)_i + row(S-1)_i} — the exact
prefix-sum restatement of Knill's recursion.  Checked for 3 ≤ S ≤ 8
(all values are < 40 on this grid and the lengths agree by
construction, so counting v < 40 decides multiset equality). -/
theorem delta_merge_representation :
    ((List.range 6).all fun s3 =>
      let S := s3 + 3
      let cur := deltaRow S
      let prev := deltaRow (S - 1)
      let B := (prev.zip cur).map fun pc => pc.1 + pc.2
      let merged := 1 :: prev ++ B
      cur.all (· < 40) &&
      cur.length == merged.length &&
      (List.range 40).all fun v => cur.count v == merged.count v) = true := by
  native_decide

/-- BOUNDED small-value count laws (this work), 2 ≤ S ≤ 8 with
Nat-truncated subtraction throughout:
count(1) = S-1, count(2) = C(S-1,2), count(3) = S-3,
count(4) = C(S-1,3) - (S-3), count(5) = C(S-3,2). -/
theorem delta_count_laws :
    ((List.range 7).all fun s1 =>
      let S := s1 + 2
      let r := deltaRow S
      r.count 1 == S - 1 &&
      r.count 2 == choose (S - 1) 2 &&
      r.count 3 == S - 3 &&
      r.count 4 == choose (S - 1) 3 - (S - 3) &&
      r.count 5 == choose (S - 3) 2) = true := by
  native_decide

/-- BOUNDED missing-value law: for S = 7, 8 exactly one value of
{1, …, max} is absent from the halved row, namely max - 3.
(Numerically verified much further, to S = 45, in
scripts/beta_profile.py-based checks.) -/
theorem delta_gap_law :
    ((List.range 2).all fun s7 =>
      let S := s7 + 7
      let r := deltaRow S
      let mx := r.foldl max 0
      ((List.range mx).filter fun v => v != 0 && !(r.contains v))
        == [mx - 3]) = true := by
  native_decide

-- ------------------------------------------------------------------
-- Tail invariance of the reach-limit row (this work).
--
-- Tail Transfer Lemma (paper proof, notes/research-plan 追記7): for
-- S ≥ 12, IF (i) row(S-1) has top-nine profile
-- counts(M'..M'-8) = 1,2,3,0,3,3,7,2,9, (ii) the last 30 entries of
-- row(S) before index 2^{S-2} all equal the midpoint value m_S
-- ("flatness", verified to S = 60 with exponentially growing
-- margins), and (iii) m_S ≥ 9, THEN row(S) has the same profile at
-- M = m_S + M'.  Proof: in the merge representation the A-part is
-- ≤ M - m_S ≤ M-9, B below the window is ≤ m_S + (M'-9) = M-9, and
-- B on the window is the bijective shift m_S + tail(row(S-1)).
-- Hence the top profile and the hole at M-3 propagate from the base
-- S = 11 (where flatness holds with margin EXACTLY 30, explaining why
-- invariance starts precisely there).  Below, the base case and the
-- first step are machine-checked on 1024/2048-wide tables via an
-- Array implementation of the same DP, cross-checked against `F`.
-- ------------------------------------------------------------------

def knillRowA (N : Nat) (prev : Array (Option Nat)) : Array (Option Nat) := Id.run do
  let mut cur : Array (Option Nat) := #[some 1]
  for n1 in [1:N] do
    let n := n1 + 1
    let mut best : Option Nat := none
    for m1 in [0:n-1] do
      let m := m1 + 1
      best := optMin best
        (optAdd (cur[m-1]!) (optAdd (prev[m-1]!) (prev[n-m-1]!)))
    cur := cur.push best
  return cur

def knillTableA (N Smax : Nat) : Array (Array (Option Nat)) := Id.run do
  let row1 : Array (Option Nat) :=
    (Array.range N).map fun i => if i = 0 then some 1 else none
  let mut rows := #[row1]
  for _ in [0:Smax-1] do
    rows := rows.push (knillRowA N rows.back!)
  return rows

/-- BOUNDED cross-check: the Array DP agrees with the List DP `F` on
the full n ≤ 64, S ≤ 8 grid (including infinities). -/
theorem knillA_agrees_with_F :
    ((List.range 8).all fun s1 =>
      let S := s1 + 1
      let row := (knillTableA 64 8)[S - 1]!
      (List.range 64).all fun n1 =>
        row[n1]! == F (n1 + 1) S) = true := by
  native_decide

/-- Halved difference row of space S on an N-wide Array table. -/
def deltaRowA (N S : Nat) : List Nat :=
  let row := (knillTableA N S)[S - 1]!
  (List.range (2 ^ (S - 1) - 1)).map fun i =>
    match row[i + 1]!, row[i]! with
    | some a, some b => (a - b) / 2
    | _, _ => 0

/-- BOUNDED base case S = 11 of the tail-invariance induction: the
top nine values M..M-8 (M = 41) occur with multiplicities
1,2,3,0,3,3,7,2,9 — in particular M-3 = 38 is absent — and 38 is the
only missing value in {1..41}; moreover the row is flat at its
midpoint window with margin exactly 30: entries n = 2^9-29 .. 2^9 all
equal m_11 = 11 while entry n = 2^9-30 is smaller. -/
theorem tail_invariance_base :
    (let r := deltaRowA 1024 11
     let M := r.foldl max 0
     M == 41 &&
     r.count M == 1 && r.count (M-1) == 2 && r.count (M-2) == 3 &&
     r.count (M-3) == 0 && r.count (M-4) == 3 && r.count (M-5) == 3 &&
     r.count (M-6) == 7 && r.count (M-7) == 2 && r.count (M-8) == 9 &&
     ((List.range M).filter fun v => v != 0 && !(r.contains v)) == [M-3] &&
     ((List.range 30).all fun j => r[2 ^ 9 - 2 - j]?.getD 0 == 11) &&
     r[2 ^ 9 - 32]?.getD 0 < 11) = true := by
  native_decide

/-- BOUNDED first induction step S = 12, exhibiting every moving part
of the Tail Transfer Lemma: separation m_12 = 16 ≥ 9, flatness of
row 12 at its own midpoint window (last 30 entries before index 2^10
all equal 16), and the transferred profile at
M = m_12 + M_11 = 16 + 41 = 57 with the hole at M-3 = 54, again the
only missing value. -/
theorem tail_invariance_step12 :
    (let r := deltaRowA 2048 12
     let M := r.foldl max 0
     M == 57 &&
     ((List.range 30).all fun j => r[2 ^ 10 - 2 - j]?.getD 0 == 16) &&
     r.count M == 1 && r.count (M-1) == 2 && r.count (M-2) == 3 &&
     r.count (M-3) == 0 && r.count (M-4) == 3 && r.count (M-5) == 3 &&
     r.count (M-6) == 7 && r.count (M-7) == 2 && r.count (M-8) == 9 &&
     ((List.range M).filter fun v => v != 0 && !(r.contains v)) == [M-3]) = true := by
  native_decide

-- ------------------------------------------------------------------
-- Unconditional midpoint bounds (this work, 追記8): via the merge
-- representation, C_S(v) = 1 + C_{S-1}(v) + Bcum(v) sandwiches the
-- midpoint value m_S = δ(2^{S-2}, S):
--   m_{S-1} ≤ m_S ≤ 2 m_{S-1}   (paper proof, unconditional),
-- so with the machine-checked base m_11 = 11 the separation
-- hypothesis m_S ≥ 9 of the Tail Transfer Lemma is ELIMINATED —
-- only flatness remains.  Also count_S(v) ≥ count_{S-1}(v) for every
-- v (amplification), immediate from the merge representation.
-- ------------------------------------------------------------------

/-- BOUNDED midpoint sandwich m_{S-1} ≤ m_S ≤ 2 m_{S-1} (S ≤ 8). -/
theorem midpoint_monotone_doubling :
    ((List.range 5).all fun s4 =>
      let S := s4 + 4
      let mPrev := (deltaRow (S - 1))[2 ^ (S - 3) - 2]?.getD 0
      let mCur := (deltaRow S)[2 ^ (S - 2) - 2]?.getD 0
      decide (mPrev ≤ mCur) && decide (mCur ≤ 2 * mPrev)) = true := by
  native_decide

/-- BOUNDED amplification count_S(v) ≥ count_{S-1}(v) (S ≤ 8, v < 40). -/
theorem count_amplification :
    ((List.range 6).all fun s3 =>
      let S := s3 + 3
      let cur := deltaRow S
      let prev := deltaRow (S - 1)
      (List.range 40).all fun v => prev.count v ≤ cur.count v) = true := by
  native_decide

-- ------------------------------------------------------------------
-- Count laws for values 6..8 and the first cumulative correction
-- P_3 ≡ 1 (this work, 追記9).  Paper proof by the same
-- interval-overlap induction as count(1..5): the only nonempty
-- convolution overlaps are conv(6) = 3 from the pair (2,4),
-- conv(7) = S-3 from (3,4), conv(8) = C(S-2,3) - 2S + 4 from (4,4);
-- telescoping gives the closed forms below, and summing them against
-- C(S-3,2) + C(S-2,2) = (S-3)^2 leaves exactly +1:
-- C_S(8) = x^{(4)} = Σ_{i≤4} C(S-1,i) EXACTLY (S ≥ 6). -/
-- ------------------------------------------------------------------

/-- BOUNDED count laws for 6..8 and P_3 ≡ 1, 6 ≤ S ≤ 8:
count(6) = 3S-16, count(7) = C(S-2,2) - 5,
count(8) = C(S-1,4) + 3S + 13 - S², and #{δ ≤ 8} = Σ_{i≤4} C(S-1,i). -/
theorem delta_count_laws_678_and_P3 :
    ((List.range 3).all fun s6 =>
      let S := s6 + 6
      let r := deltaRow S
      r.count 6 == 3 * S - 16 &&
      r.count 7 == choose (S - 2) 2 - 5 &&
      r.count 8 == choose (S - 1) 4 + 3 * S + 13 - S * S &&
      (r.filter (· ≤ 8)).length ==
        ((List.range 5).map fun i => choose (S - 1) i).sum) = true := by
  native_decide

-- ------------------------------------------------------------------
-- A RIGOROUS upper bound c < 3 (this work, 追記12).
--
-- The space-optimal reach cost f_p = F(2^{p-1}, p) is submultiplicative,
--   f_{p+q-1} ≤ f_p · f_q,
-- by nesting reach strategies (Bennett-style recursive composition:
-- run the outer p-pebble reach on a coarsened chain whose macro-nodes
-- are blocks of 2^{q-1}, implementing each macro-move by the inner
-- q-pebble reach; peak p+q-1 pebbles, moves f_p · f_q).  Hence by
-- Fekete's lemma c = lim f_{p+1}^{1/p} = inf_p f_{p+1}^{1/p}, so
-- c ≤ f_{m+1}^{1/m} for EVERY m.  With f_4 = 25 < 27 = 3^3 this gives
-- c ≤ 25^{1/3} < 3 unconditionally (and f_60 gives c ≤ 2.61).  The
-- submultiplicativity is machine-checked on a grid below; the Fekete
-- step is classical.
-- ------------------------------------------------------------------

/-- f_p = F(2^{p-1}, p), the space-optimal reach cost. -/
def fval (p : Nat) : Option Nat := F (2 ^ (p - 1)) p

/-- BOUNDED submultiplicativity f_{p+q-1} ≤ f_p · f_q on the grid
p, q ≥ 1, p + q ≤ 8 (so the argument 2^{p+q-2} ≤ 64 fits the table).
Evidence for the general composition lemma. -/
theorem fval_submult :
    ((List.range 7).all fun p0 =>
      (List.range 7).all fun q0 =>
        let p := p0 + 1
        let q := q0 + 1
        if p + q ≤ 8 then
          match fval (p + q - 1), fval p, fval q with
          | some a, some b, some cc => decide (a ≤ b * cc)
          | _, _, _ => false
        else true) = true := by
  native_decide

/-- BOUNDED witness making the Fekete bound strict: f_4 = 25 and
25 < 3^3 = 27, so c ≤ 25^{1/3} < 3.  (f_4 = F(8,4).) -/
theorem c_below_three_witness :
    fval 4 = some 25 ∧ 25 < 3 ^ 3 := by
  native_decide

-- ------------------------------------------------------------------
-- Lower-bound side (this work, 追記14): via the Merge Lemma,
-- total(row S) = 1 + total(row S-1) + total(B) and B_i ≥ δ(i,S-1),
-- so f_S ≥ 2 f_{S-1} - 1 and hence c ≥ 2 (matching the exponent of
-- Královič's Ω(n lg n)).  Beyond 2 the corner identity reduces a
-- bound c ≥ 2 + θ to the pointwise row ratio δ(i,S) ≥ θ δ(i,S-1)
-- (measured min = m_S/Δmax(S-1) ≈ 0.276 at S = 60); its
-- unconditional proof needs the transition regime and remains open.
-- ------------------------------------------------------------------

/-- BOUNDED lower recursion f_S ≥ 2 f_{S-1} - 1 (grid S ≤ 7). -/
theorem fval_lower_doubling :
    ((List.range 6).all fun s2 =>
      let S := s2 + 2
      match fval S, fval (S - 1) with
      | some a, some b => decide (2 * b - 1 ≤ a)
      | _, _ => false) = true := by
  native_decide

/-- BOUNDED pointwise row-ratio floor: 4 δ(i,S) ≥ δ(i,S-1) for all
i ≤ 2^{S-2} on the grid S ≤ 8 (the measured asymptotic floor is
≈ 0.276 > 1/4). -/
theorem delta_pointwise_ratio_floor :
    ((List.range 6).all fun s3 =>
      let S := s3 + 3
      let cur := deltaRow S
      let prev := deltaRow (S - 1)
      (List.range (2 ^ (S - 2) - 1)).all fun i =>
        decide (prev[i]?.getD 0 ≤ 4 * (cur[i]?.getD 0))) = true := by
  native_decide

-- ------------------------------------------------------------------
-- THEOREM c = 2d (this work, 追記15).  Sandwich:
--   2^{S-1} · m_S ≤ f_S ≤ 2^S · M_S   and   M_S ≤ S · m_S,
-- where m_S is the midpoint value and M_S = Δmax/2 the row maximum.
-- (Lower: sortedness puts ≥ 2^{S-2} entries ≥ m_S past the midpoint;
--  M_S ≤ S·m_S from the Merge-Lemma max decomposition
--  M_S = m_S + M_{S-1} and midpoint monotonicity; upper: trivial.)
-- Hence f_S = 2^S M_S · Θ(S)^{±1}, and since c = lim f_S^{1/(S-1)}
-- exists (Fekete, via fval_submult), the root limit
-- d = lim M_S^{1/(S-1)} exists and c = 2d.
-- ------------------------------------------------------------------

/-- BOUNDED sandwich for c = 2d, grid 3 ≤ S ≤ 8 (halved rows;
f_S = 1 + 2·Σδ). -/
theorem c_eq_2d_sandwich :
    ((List.range 6).all fun s3 =>
      let S := s3 + 3
      let r := deltaRow S
      let f := 1 + 2 * r.sum
      let m := r[2 ^ (S - 2) - 2]?.getD 0
      let M := r.foldl max 0
      decide (2 ^ (S - 1) * m ≤ f) &&
      decide (f ≤ 2 ^ S * M) &&
      decide (M ≤ S * m)) = true := by
  native_decide

/-- BOUNDED Merge-Lemma max decomposition M_S = m_S + M_{S-1}
(grid 4 ≤ S ≤ 8). -/
theorem max_decomposition :
    ((List.range 5).all fun s4 =>
      let S := s4 + 4
      let m := (deltaRow S)[2 ^ (S - 2) - 2]?.getD 0
      let M := (deltaRow S).foldl max 0
      let Mp := (deltaRow (S - 1)).foldl max 0
      M == m + Mp) = true := by
  native_decide


-- ------------------------------------------------------------------
-- The counting recursion behind the rigorous lower bound
-- c ≥ 2^{1+ε*} ≈ 2.4518 (this work, 追記25; paper proof in
-- notes/c-lower-bound-draft.md).  From the Merge Lemma and pointwise
-- domination: C_S(v) ≤ 1 + C_{S-1}(v) + C_S(⌊v/2⌋), whence
-- C_S(2^k) ≤ 2·C(S+k-1, k+1) − 1 by a Pascal induction, so all but
-- an exponentially small fraction of the row exceeds 2^{εS} for
-- ε < ε* (root of (1+ε)H(ε/(1+ε)) = 1) and f_S ≥ 2^{(1+ε)S − o(S)}.
-- ------------------------------------------------------------------

/-- #entries of the halved row of S with value ≤ v. -/
def cCount (S v : Nat) : Nat := ((deltaRow S).filter (· ≤ v)).length

/-- BOUNDED counting recursion C_S(v) ≤ 1 + C_{S-1}(v) + C_S(⌊v/2⌋)
(S ≤ 8, v ≤ 64). -/
theorem count_recursion :
    ((List.range 6).all fun s3 =>
      let S := s3 + 3
      (List.range 64).all fun v0 =>
        let v := v0 + 1
        decide (cCount S v ≤ 1 + cCount (S - 1) v + cCount S (v / 2))) =
      true := by
  native_decide

/-- BOUNDED binomial bound C_S(2^k) ≤ 2·C(S+k-1, k+1) − 1
(S ≤ 8, k ≤ 8). -/
theorem count_binomial_bound :
    ((List.range 7).all fun s2 =>
      let S := s2 + 2
      (List.range 9).all fun k =>
        decide (cCount S (2 ^ k) + 1 ≤ 2 * choose (S + k - 1) (k + 1))) =
      true := by
  native_decide


end GenJanus.PebblingTheory
