import RevPebbling.PebblingFoundations
import RevPebbling.LiftAbove

/-!
# Erasure-budgeted reversible pebbling of a chain (RC-02, definitions)

The chain is `0 → 1 → ⋯ → n` with a free entrance `0` that is always
available and never counted.  We reuse the board model of
`RevPebbling.PebblingFoundations`: a `Board` is a `List Bool` of
length `n`, cell `i` (0-based) is node `i+1`, `okMove b i` says node
`i+1` is *available* (`i = 0`, or node `i` carries a pebble), `toggle`
flips a cell, `maxOnes` is the peak over a trace.

RC-02 (Definition 2) adds one kind of move: an **irreversible
removal** (erasure) takes a pebble off a cell that is *not* available.
A play in the `e`-erasure game may use at most `e` of them.  We keep
the reversible game's `legalB` for the erasure-free sub-language and
introduce

* `okE b i`      – the move at `i` is admissible: reversible toggle, or
                   a removal (the cell carries a pebble);
* `isErase b i`  – the move is an irreversible removal;
* `legalE`       – every move admissible;
* `erasures`     – number of irreversible removals along the trace.

`IsPlay n p e s` is a *clean plan* with peak `p` and at most `e`
erasures: empty board of length `n` → exactly `{n}`, every move inside
the chain (`i < n`).  `Reachable n p e` is the reachability predicate
whose maximum `n` is `reach(p, e)`, and `MstarIs n p e m` says that
`m = M*(n, p, e)` (a play of length `m` exists and none is shorter).

The second half of the file is an executable oracle (`mstarE`,
`reachableE`, `reachE`) over bit-mask boards used for the bounded
checks and the tables; it is *not* linked to the predicates by proof
(see `ErasurePebbling/NOTES.md`).
-/

namespace ErasurePebbling

open RevPebbling.PebblingFoundations

/-! ## Moves with erasure -/

/-- Admissible move in the erasure game: a reversible toggle, or the
removal of a pebble (from any cell). -/
def okE (b : Board) (i : Nat) : Bool := okMove b i || nth b i

/-- Irreversible removal: a pebble is taken from a non-available cell. -/
def isErase (b : Board) (i : Nat) : Bool := nth b i && !okMove b i

def legalE : Board → List Nat → Bool
  | _, [] => true
  | b, i :: rest => okE b i && legalE (toggle b i) rest

def erasures : Board → List Nat → Nat
  | _, [] => 0
  | b, i :: rest => (if isErase b i then 1 else 0) + erasures (toggle b i) rest

@[simp] theorem legalE_nil (b : Board) : legalE b [] = true := rfl
@[simp] theorem legalE_cons (b : Board) (i : Nat) (s : List Nat) :
    legalE b (i :: s) = (okE b i && legalE (toggle b i) s) := rfl
@[simp] theorem erasures_nil (b : Board) : erasures b [] = 0 := rfl
@[simp] theorem erasures_cons (b : Board) (i : Nat) (s : List Nat) :
    erasures b (i :: s) = (if isErase b i then 1 else 0) + erasures (toggle b i) s := rfl

theorem legalE_append (b : Board) (x y : List Nat) :
    legalE b (x ++ y) = (legalE b x && legalE (execB b x) y) := by
  induction x generalizing b with
  | nil => simp [execB]
  | cons i rest ih =>
      simp only [List.cons_append, legalE_cons, ih, execB, List.foldl_cons, Bool.and_assoc]

theorem erasures_append (b : Board) (x y : List Nat) :
    erasures b (x ++ y) = erasures b x + erasures (execB b x) y := by
  induction x generalizing b with
  | nil => simp [execB]
  | cons i rest ih =>
      simp only [List.cons_append, erasures_cons, ih, execB, List.foldl_cons, Nat.add_assoc]

/-- A reversible move is admissible. -/
theorem okE_of_okMove {b : Board} {i : Nat} (h : okMove b i = true) : okE b i = true := by
  simp [okE, h]

/-- A reversible move is not an erasure. -/
theorem isErase_eq_false_of_okMove {b : Board} {i : Nat} (h : okMove b i = true) :
    isErase b i = false := by
  simp [isErase, h]

/-- Erasure-free plays (`legalB`) are plays of the erasure game ... -/
theorem legalE_of_legalB : ∀ (s : List Nat) (b : Board), legalB b s = true → legalE b s = true
  | [], _, _ => rfl
  | i :: rest, b, h => by
      have h' : okMove b i = true ∧ legalB (toggle b i) rest = true := by
        simpa [legalB, Bool.and_eq_true] using h
      simp [okE_of_okMove h'.1, legalE_of_legalB rest _ h'.2]

/-- ... with zero erasures. -/
theorem erasures_of_legalB : ∀ (s : List Nat) (b : Board), legalB b s = true → erasures b s = 0
  | [], _, _ => rfl
  | i :: rest, b, h => by
      have h' : okMove b i = true ∧ legalB (toggle b i) rest = true := by
        simpa [legalB, Bool.and_eq_true] using h
      simp [isErase_eq_false_of_okMove h'.1, erasures_of_legalB rest _ h'.2]

/-! ## Clean plans, reach and `M*` -/

/-- The empty chain of length `n`. -/
def empty (n : Nat) : Board := List.replicate n false

/-- The clean final configuration `{n}`: only the last cell pebbled. -/
def target (n : Nat) : Board := (List.replicate n false).set (n - 1) true

/-- A clean plan for the chain of length `n` with peak `p` and at most
`e` irreversible removals (RC-02, Definitions 1–2). -/
structure IsPlay (n p e : Nat) (s : List Nat) : Prop where
  bounds : ∀ i ∈ s, i < n
  legal : legalE (empty n) s = true
  peak : maxOnes (empty n) s ≤ p
  budget : erasures (empty n) s ≤ e
  final : execB (empty n) s = target n

/-- The chain of length `n` admits a clean plan with peak `p` and `e`
erasures; `reach(p, e)` is the largest such `n`. -/
def Reachable (n p e : Nat) : Prop := ∃ s, IsPlay n p e s

/-- `reach(p, e) = r`. -/
def ReachIs (p e r : Nat) : Prop := Reachable r p e ∧ ∀ n, Reachable n p e → n ≤ r

/-- `M*(n, p, e) ≤ m`. -/
def MstarLe (n p e m : Nat) : Prop := ∃ s, IsPlay n p e s ∧ s.length ≤ m

/-- `M*(n, p, e) = m`: some plan has exactly `m` moves and none is shorter. -/
def MstarIs (n p e m : Nat) : Prop :=
  (∃ s, IsPlay n p e s ∧ s.length = m) ∧ ∀ s, IsPlay n p e s → m ≤ s.length

/-- The saturation threshold `e*(n, p) = ⌈(n−1)/(p−1)⌉ − 1` of Theorem A,
written with natural-number arithmetic (`(a + b - 1) / b` is `⌈a/b⌉`). -/
def estar (n p : Nat) : Nat := (n - 1 + (p - 1) - 1) / (p - 1) - 1

/-! ## Basic lemmas on boards -/

theorem nth_empty (n j : Nat) : nth (empty n) j = false := nth_replicate n j

theorem length_empty (n : Nat) : (empty n).length = n := List.length_replicate

theorem ones_empty (n : Nat) : ones (empty n) = 0 := ones_replicate n

theorem length_execB (b : Board) : ∀ s : List Nat, (execB b s).length = b.length := by
  intro s
  induction s generalizing b with
  | nil => rfl
  | cons i rest ih =>
      show (execB (toggle b i) rest).length = b.length
      rw [ih, toggle, List.length_set]

theorem length_target (n : Nat) : (target n).length = n := by
  simp [target]

/-! ## Executable oracle (bit-mask boards)

`st` is a bit mask, bit `i` = cell `i`; the erasure budget consumed so
far is carried alongside.  `mstarE n p e` is `M*(n, p, e)` by breadth
first search (`none` when `{n}` is unreachable), `reachableE` its
reachability bit, `reachE p e bound` the largest reachable `n ≤ bound`.
These run under `#eval` / `native_decide`; nothing here is proved
against `IsPlay`. -/

def popcount : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) % 2 + popcount ((n + 1) / 2)

/-- One move of the erasure game on a bit-mask board.  Returns the new
state and whether the move was an irreversible removal. -/
def stepE (n p : Nat) (st : Nat) : List (Nat × Bool) :=
  (List.range n).filterMap fun i =>
    let has := st.testBit i
    let avail := i == 0 || st.testBit (i - 1)
    let ns := st ^^^ (1 <<< i)
    if has then some (ns, !avail)
    else if avail && popcount st < p then some (ns, false)
    else none

/-- Encode (board, erasures used) as one key. -/
def key (e : Nat) (st used : Nat) : Nat := st * (e + 1) + used

def expandE (n p e : Nat) (visited : Std.HashSet Nat) (frontier : List (Nat × Nat)) :
    Std.HashSet Nat × List (Nat × Nat) :=
  frontier.foldl (init := (visited, [])) fun (acc : Std.HashSet Nat × List (Nat × Nat)) su =>
    (stepE n p su.1).foldl (init := acc) fun (acc' : Std.HashSet Nat × List (Nat × Nat)) mv =>
      let used' := su.2 + (if mv.2 then 1 else 0)
      if used' ≤ e then
        let k := key e mv.1 used'
        if acc'.1.contains k then acc'
        else (acc'.1.insert k, (mv.1, used') :: acc'.2)
      else acc'

def bfsE (n p e : Nat) : Nat → Std.HashSet Nat → List (Nat × Nat) → Nat → Option Nat
  | 0, _, _, _ => none
  | fuel + 1, visited, frontier, steps =>
      if frontier.any (fun su => su.1 == 1 <<< (n - 1)) then some steps
      else
        match expandE n p e visited frontier with
        | (_, []) => none
        | (visited', next) => bfsE n p e fuel visited' next (steps + 1)

/-- `M*(n, p, e)` by BFS (oracle). -/
def mstarE (n p e : Nat) : Option Nat :=
  bfsE n p e (2 ^ n * (e + 1) + 2) ((Std.HashSet.emptyWithCapacity 1024).insert (key e 0 0)) [(0, 0)] 0

/-- Reachability bit of the oracle. -/
def reachableE (n p e : Nat) : Bool := (mstarE n p e).isSome

/-- Largest `n ≤ bound` with `reachableE n p e` (oracle); `0` if none. -/
def reachE (p e bound : Nat) : Nat :=
  (List.range (bound + 1)).foldl (fun acc n => if reachableE n p e then n else acc) 0

-- Sanity anchors from RC-02 Table 1 (`#guard` runs at elaboration time).
#guard mstarE 4 3 0 = some 9
#guard mstarE 4 3 1 = some 7
#guard mstarE 6 4 0 = some 15
#guard mstarE 6 4 1 = some 11

end ErasurePebbling

