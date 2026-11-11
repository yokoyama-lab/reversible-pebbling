import ErasurePebbling.Conjectures

/-!
# A layered search proved sound against `IsPlay`

`Basic.lean`'s oracle `mstarE` runs a bit-mask BFS over a hash set and is
**not** linked to `IsPlay` by proof, so the bounded statements derived from
it (`Bounded.lean`) are statements about the oracle.  This file gives a
second search, written on the same boards as `IsPlay` (lists of `Bool`) and
proved to over-approximate every clean plan:

* `layer n p e k` is a list of states `(board, erasures used)` closed under
  one admissible move (peak `≤ p`, budget `≤ e`) and containing every state
  reachable from the empty board in at most `k` moves (`mem_layer_of_play`);
* hence, if no state of `layer n p e m` carries the target board, **no**
  clean plan with peak `p`, at most `e` irreversible removals and at most `m`
  moves exists (`not_mstarLe_of_layer`).

Lower bounds on `M*` thus reduce to evaluating `layer`, and upper bounds to
exhibiting one play.  Together they give `MstarIs` (`mstarIs_of`), i.e.
statements about `IsPlay` itself.  Applied to the counterexample of
`Bounded.ineq_counterexample`, this proves `M*(10,3,3) = 21` and
`M*(10,4,2) = 19` (`counterexample_verified`).

The evaluation of `layer` uses `native_decide` (two calls, at a few hundred
states each); everything else is checked by the kernel.
-/

namespace ErasurePebbling
namespace Checker

open RevPebbling.PebblingFoundations

/-- A search state: the board and the number of irreversible removals so far. -/
abbrev St := Board × Nat

/-- The indicator of an irreversible removal. -/
def ind (b : Board) (i : Nat) : Nat := if isErase b i then 1 else 0

/-- All states one admissible move away, within peak `p` and budget `e`. -/
def succ1 (n p e : Nat) (st : St) : List St :=
  (List.range n).filterMap fun i =>
    if okE st.1 i = true ∧ ones (toggle st.1 i) ≤ p ∧ st.2 + ind st.1 i ≤ e then
      some (toggle st.1 i, st.2 + ind st.1 i)
    else none

/-- Insert unless already present. -/
def insertNew (acc : List St) (x : St) : List St := if x ∈ acc then acc else x :: acc

theorem mem_insertNew (acc : List St) (x y : St) :
    y ∈ insertNew acc x ↔ y = x ∨ y ∈ acc := by
  unfold insertNew
  split
  · constructor
    · intro h; exact Or.inr h
    · rintro (rfl | h) <;> assumption
  · simp

/-- Duplicate-free copy of a list (same members). -/
def dedupL (l : List St) : List St := l.foldl insertNew []

theorem mem_foldl_insertNew : ∀ (l acc : List St) (y : St),
    y ∈ l.foldl insertNew acc ↔ y ∈ l ∨ y ∈ acc
  | [], acc, y => by simp
  | x :: rest, acc, y => by
      rw [List.foldl_cons, mem_foldl_insertNew rest, mem_insertNew]
      simp only [List.mem_cons]
      constructor
      · rintro (h | h | h)
        · exact Or.inl (Or.inr h)
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
      · rintro ((h | h) | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)

theorem mem_dedupL (l : List St) (y : St) : y ∈ dedupL l ↔ y ∈ l := by
  unfold dedupL; rw [mem_foldl_insertNew]; simp

/-- States reachable in at most `k` moves (an over-approximation is all we need). -/
def layer (n p e : Nat) : Nat → List St
  | 0 => [(empty n, 0)]
  | k + 1 => let L := layer n p e k; dedupL (L ++ L.flatMap (succ1 n p e))

theorem layer_succ_sub (n p e k : Nat) (x : St) (h : x ∈ layer n p e k) :
    x ∈ layer n p e (k + 1) := by
  show x ∈ dedupL _
  rw [mem_dedupL]; exact List.mem_append_left _ h

theorem layer_mono (n p e k : Nat) : ∀ d (x : St), x ∈ layer n p e k → x ∈ layer n p e (k + d)
  | 0, _, h => h
  | d + 1, x, h => layer_succ_sub n p e (k + d) x (layer_mono n p e k d x h)

theorem layer_step (n p e k : Nat) (x y : St) (hx : x ∈ layer n p e k) (hy : y ∈ succ1 n p e x) :
    y ∈ layer n p e (k + 1) := by
  show y ∈ dedupL _
  rw [mem_dedupL]
  exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨x, hx, hy⟩)

/-- **Soundness of the search.**  Along an admissible play with all moves
below `n`, every intermediate board within peak `p`, and the erasure count
within budget, the final state lies in the layer of the play's length. -/
theorem mem_layer_of_play (n p e : Nat) : ∀ (s : List Nat) (b : Board) (u k : Nat),
    (b, u) ∈ layer n p e k → legalE b s = true → (∀ i ∈ s, i < n) →
    maxOnes b s ≤ p → u + erasures b s ≤ e →
    (execB b s, u + erasures b s) ∈ layer n p e (k + s.length)
  | [], b, u, k, h, _, _, _, _ => by simpa [execB, erasures_nil] using h
  | i :: rest, b, u, k, h, hl, hb, hp, he => by
      have hl' : okE b i = true ∧ legalE (toggle b i) rest = true := by
        simpa [legalE_cons, Bool.and_eq_true] using hl
      have hpk : ones (toggle b i) ≤ p := by
        have h1 := ones_le_maxOnes (toggle b i) rest
        have h2 : maxOnes b (i :: rest) = max (ones b) (maxOnes (toggle b i) rest) := rfl
        have h3 := Nat.le_max_right (ones b) (maxOnes (toggle b i) rest)
        omega
      have hpr : maxOnes (toggle b i) rest ≤ p := by
        have h2 : maxOnes b (i :: rest) = max (ones b) (maxOnes (toggle b i) rest) := rfl
        have h3 := Nat.le_max_right (ones b) (maxOnes (toggle b i) rest)
        omega
      have her : erasures b (i :: rest) = ind b i + erasures (toggle b i) rest := rfl
      have hstep : (toggle b i, u + ind b i) ∈ succ1 n p e (b, u) := by
        unfold succ1
        rw [List.mem_filterMap]
        refine ⟨i, List.mem_range.mpr (hb i (by simp)), ?_⟩
        simp only
        rw [if_pos ⟨hl'.1, hpk, by omega⟩]
      have h1 := layer_step n p e k _ _ h hstep
      have ih := mem_layer_of_play n p e rest (toggle b i) (u + ind b i) (k + 1) h1 hl'.2
        (fun j hj => hb j (by simp [hj])) hpr (by omega)
      have e1 : k + 1 + rest.length = k + (i :: rest).length := by simp; omega
      have e2 : u + ind b i + erasures (toggle b i) rest = u + erasures b (i :: rest) := by
        rw [her]; omega
      rw [e1, e2] at ih
      exact ih

/-- **Lower bounds from the search.**  If no state of `layer n p e m` has the
target board, no clean plan has at most `m` moves. -/
theorem not_mstarLe_of_layer (n p e m : Nat)
    (h : (layer n p e m).all (fun st => !decide (st.1 = target n)) = true) :
    ¬ MstarLe n p e m := by
  rintro ⟨s, hs, hlen⟩
  have h0 : ((empty n, 0) : St) ∈ layer n p e 0 := by simp [layer]
  have hm := mem_layer_of_play n p e s (empty n) 0 0 h0 hs.legal hs.bounds hs.peak
    (by simpa using hs.budget)
  rw [hs.final, Nat.zero_add] at hm
  have hm' := layer_mono n p e s.length (m - s.length) _ hm
  rw [Nat.add_sub_cancel' hlen] at hm'
  have := List.all_eq_true.mp h _ hm'
  simp at this

/-- `M*(n,p,e) = m` from one play of length `m` and an empty layer `m − 1`. -/
theorem mstarIs_of (n p e m : Nat) (s : List Nat) (hs : IsPlay n p e s) (hl : s.length = m)
    (hm : 1 ≤ m)
    (h : (layer n p e (m - 1)).all (fun st => !decide (st.1 = target n)) = true) :
    MstarIs n p e m := by
  refine ⟨⟨s, hs, hl⟩, fun t ht => Nat.le_of_not_lt fun hlt => ?_⟩
  exact not_mstarLe_of_layer n p e (m - 1) h ⟨t, ht, by omega⟩

/-! ## The counterexample to `M*(n,p,e+1) ≤ M*(n,p+1,e)`, against `IsPlay` -/

theorem play_10_3_3 :
    IsPlay 10 3 3 [0, 1, 0, 2, 3, 2, 0, 1, 0, 4, 5, 4, 3, 6, 7, 6, 5, 8, 9, 8, 7] :=
  ⟨by decide, by decide, by decide, by decide, by decide⟩

theorem play_10_4_2 :
    IsPlay 10 4 2 [0, 1, 2, 3, 2, 1, 0, 4, 5, 6, 5, 4, 3, 7, 8, 9, 8, 7, 6] :=
  ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- BOUNDED (`native_decide`): no clean plan for `n = 10`, `p = 3`, `e = 3`
has 20 moves or fewer. -/
theorem layer_10_3_3 :
    (layer 10 3 3 20).all (fun st => !decide (st.1 = target 10)) = true := by
  native_decide

/-- BOUNDED (`native_decide`): no clean plan for `n = 10`, `p = 4`, `e = 2`
has 18 moves or fewer. -/
theorem layer_10_4_2 :
    (layer 10 4 2 18).all (fun st => !decide (st.1 = target 10)) = true := by
  native_decide

/-- **The counterexample, as a statement about clean plans**:
`M*(10,3,3) = 21 > 19 = M*(10,4,2)`, i.e. one more irreversible removal is
worth less than one more pebble here. -/
theorem counterexample_verified : MstarIs 10 3 3 21 ∧ MstarIs 10 4 2 19 :=
  ⟨mstarIs_of 10 3 3 21 _ play_10_3_3 rfl (by omega) layer_10_3_3,
   mstarIs_of 10 4 2 19 _ play_10_4_2 rfl (by omega) layer_10_4_2⟩

/-- Control: the search is not vacuous — the target does appear at the optimum. -/
theorem layer_10_4_2_hit :
    (layer 10 4 2 19).any (fun st => decide (st.1 = target 10)) = true := by
  native_decide

end Checker
end ErasurePebbling
