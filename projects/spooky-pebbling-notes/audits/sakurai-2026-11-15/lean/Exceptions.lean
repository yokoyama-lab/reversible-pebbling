import Precut
namespace Exceptions
open SpookyRound TraceBridge

def exceptional (a : CutBound.Account) : Nat :=
  if a.cutPebble = 0 ∧ a.isRoot = 0 ∧ ¬ (a.postCompute = 1 ∧ a.postUncompute = 1) then 1 else 0

theorem charge (a : CutBound.Account) (h : CutBound.Valid a) :
    3 + exceptional a ≤ a.preCompute+a.postCompute+a.postUncompute+a.cutPebble+a.isRoot := by
  unfold exceptional CutBound.Valid at *
  split <;> omega

def removed (as : List CutBound.Account) : Nat :=
  CutBound.pebbles as + (as.map exceptional).sum

theorem global_charge (as : List CutBound.Account) (h : ∀ a ∈ as, CutBound.Valid a) :
    3*as.length+removed as ≤ CutBound.work as+2*CutBound.pebbles as+CutBound.roots as := by
  induction as with
  | nil => simp [removed,CutBound.work,CutBound.pebbles,CutBound.roots]
  | cons a as ih =>
    have hc := charge a (h a (by simp))
    have ht := ih (fun x hx => h x (by simp [hx]))
    simp only [removed,CutBound.work,CutBound.pebbles,CutBound.roots,List.map_cons,List.sum_cons,List.length_cons] at *
    omega

theorem exception_bound (as : List CutBound.Account) (h : ∀ a ∈ as, CutBound.Valid a)
    (hw : CutBound.work as ≤ 3*as.length+e) (hp : CutBound.pebbles as ≤ s)
    (hr : CutBound.roots as ≤ 1) : removed as ≤ e+2*s+1 := by
  have hh := global_charge as h
  omega

def accounts (pre post : List Action) (c : Config n) (root : Fin n) : List CutBound.Account :=
  (List.finRange n).map fun v =>
    { preCompute := CutBound.count .compute (events v pre)
      postCompute := CutBound.count .compute (events v post)
      postUncompute := CutBound.count .uncompute (events v post)
      cutPebble := if c.peb v then 1 else 0
      isRoot := if v = root then 1 else 0 }

theorem sum_le (xs : List α) (f g : α → Nat) (h : ∀ x ∈ xs, f x ≤ g x) :
    (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hh := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [List.map_cons,List.sum_cons]; omega

theorem account_work_le {pred : Fin n → Fin n → Bool}
    (h : ActionRuns pred q (pre++post) r) (c : Config n) (root : Fin n) :
    CutBound.work (accounts pre post c root) ≤ r.work := by
  rw [WorkBridge.work_by_vertices h]
  unfold CutBound.work accounts
  rw [List.map_map]
  apply sum_le
  intro v hv
  simp only [Function.comp_apply]
  rw [Precut.counts_split,Precut.counts_split]
  omega

-- Semantic work hypothesis is the actual run work, not an abstract budget.
-- Mandatory account conditions and cut-space/root counts remain explicit here.
theorem actual_exception_bound {pred : Fin n → Fin n → Bool}
    (h : ActionRuns pred q (pre++post) r) (c : Config n) (root : Fin n)
    (hv : ∀ a ∈ accounts pre post c root, CutBound.Valid a)
    (hw : r.work ≤ 3*n+e)
    (hp : CutBound.pebbles (accounts pre post c root) ≤ s)
    (hr : CutBound.roots (accounts pre post c root) ≤ 1) :
    removed (accounts pre post c root) ≤ e+2*s+1 := by
  apply exception_bound _ hv
  · have hh := account_work_le h c root
    have hl : (accounts pre post c root).length = n := by simp [accounts]
    rw [hl]
    omega
  · exact hp
  · exact hr
theorem indicator_count [DecidableEq α] (xs : List α) (a : α) :
    (xs.map fun x => if x = a then 1 else 0).sum = xs.count a := by
  induction xs with
  | nil => simp
  | cons x xs ih => by_cases hh : x = a <;> simp_all [List.count_cons,beq_iff_eq,Nat.add_comm]

theorem roots_bound (pre post : List Action) (c : Config n) (root : Fin n) :
    CutBound.roots (accounts pre post c root) ≤ 1 := by
  simp only [CutBound.roots,accounts,List.map_map]
  change ((List.finRange n).map fun v => if v = root then 1 else 0).sum ≤ 1
  rw [indicator_count]
  rw [(List.nodup_finRange n).count_of_mem (List.mem_finRange root)]
  omega

theorem count_positive (e : CutBound.Event) (es : List CutBound.Event) (h : e ∈ es) :
    1 ≤ CutBound.count e es := by
  unfold CutBound.count
  have hh : e ∈ es.filter (fun x => x == e) := by simp [h]
  have hh' := List.length_pos_of_mem hh
  omega

theorem accounts_valid {pred : Fin n → Fin n → Bool}
    (hpost : ActionRuns pred c post t) (root : Fin n)
    (hroot : c.peb root = true)
    (hc : ∀ v : Fin n, ∃ a ∈ pre, firstAt a v = .pebble)
    (hu : ∀ v : Fin n, v ≠ root → ∃ a ∈ post, firstAt a v = .unpebble) :
    ∀ a ∈ accounts pre post c root, CutBound.Valid a := by
  intro a ha
  obtain ⟨v,hv,he⟩ := List.mem_map.mp ha
  subst a
  have hpre := count_positive .compute (events v pre) ((compute_in_events v pre).mpr (hc v))
  by_cases hr : v = root
  · subst v
    simp [CutBound.Valid,hroot,hpre]
  · have hcleanup := (uncompute_in_events v post).mpr (hu v hr)
    have hU := count_positive .uncompute (events v post) hcleanup
    by_cases hp : c.peb v = true
    · simp [CutBound.Valid,hp,hr,hpre,hU]
    · have hn : kind c v ≠ .pebble := by cases hg : c.ghost v <;> simp [kind,hp,hg]
      have hC := CutBound.missing_requires_recompute (actionruns_scalar hpost v) hcleanup hn
      simp [CutBound.Valid,hp,hr,hpre,hU,hC]
theorem semantic_exception_bound {pred : Fin n → Fin n → Bool}
    (h : ActionRuns pred q (pre++post) r) (hpost : ActionRuns pred c post t)
    (root : Fin n) (hroot : c.peb root = true)
    (hc : ∀ v : Fin n, ∃ a ∈ pre, firstAt a v = .pebble)
    (hu : ∀ v : Fin n, v ≠ root → ∃ a ∈ post, firstAt a v = .unpebble)
    (hw : r.work ≤ 3*n+e)
    (hp : CutBound.pebbles (accounts pre post c root) ≤ s) :
    removed (accounts pre post c root) ≤ e+2*s+1 :=
  actual_exception_bound h c root (accounts_valid hpost root hroot hc hu) hw hp
    (roots_bound pre post c root)
#print axioms semantic_exception_bound
#print axioms accounts_valid
#print axioms roots_bound
#print axioms actual_exception_bound
#print axioms account_work_le
end Exceptions
