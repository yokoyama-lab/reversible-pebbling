import ConcreteRound
namespace SpookyReverse
open SpookyRound
variable {n : Nat} {pred : Fin n → Fin n → Bool} {q : Config n} {a : Action} {v u : Fin n}

def swap : Move → Move | .idle => .idle | .pebble => .unpebble | .unpebble => .pebble
def reverse (a : Action) : Action := ⟨a.first.map swap, a.ghosts⟩
@[simp] theorem swap_idle (m : Move) : swap m = .idle ↔ m = .idle := by cases m <;> simp [swap]
@[simp] theorem first_reverse (a : Action) (v : Fin n) : firstAt (reverse a) v = swap (firstAt a v) := by
  cases hh : a.first[v.val]? <;> simp [firstAt,reverse,List.getElem?_map,hh,swap]
@[simp] theorem ghost_reverse (a : Action) (v : Fin n) : ghostAt (reverse a) v = ghostAt a v := rfl

theorem predecessor_idle (hi : ∀ v, pred v v = false)
    (hl : Legal pred q a) (hv : firstAt a v ≠ .idle) (hu : pred v u = true) :
    firstAt a u = .idle := by
  by_cases hn : firstAt a u = .idle
  · exact hn
  exfalso
  have hne : v ≠ u := by intro he; subst u; simp [hi v] at hu
  exact hl.2.2.2.2.1 v u hne hv hn u (Or.inr hu) (Or.inl rfl)

theorem after_peb_idle (ha : firstAt a v = .idle) (hg : ghostAt a v = false) :
    (afterRound q a).peb v = q.peb v := by simp [afterRound,afterFirst,ha,hg]

theorem reverse_legal (hi : ∀ v, pred v v = false)
    (hl : Legal pred q a) (hq : ∀ v, q.ghost v = false)
    (hg : ∀ v : Fin n, ghostAt a v = false) :
    Legal pred (afterRound q a) (reverse a) := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro v
    simp [afterRound,afterFirst,hq v,hg v]
    cases firstAt a v <;> simp
  · intro v hv
    have hx : firstAt a v = .unpebble := by
      rw [first_reverse] at hv
      cases hh : firstAt a v <;> simp_all [swap]
    simp [afterRound,afterFirst,hx,hg v]
  · intro v hv
    have hx : firstAt a v = .pebble := by
      rw [first_reverse] at hv
      cases hh : firstAt a v <;> simp_all [swap]
    simp [afterRound,afterFirst,hx,hg v]
  · intro v hv u hu
    have hv' : firstAt a v ≠ .idle := by simpa using hv
    rw [after_peb_idle (predecessor_idle hi hl hv' hu) (hg u)]
    exact hl.2.2.2.1 v hv' u hu
  · intro v w hne hv hw u hu
    have hv' : firstAt a v ≠ .idle := by simpa using hv
    have hw' : firstAt a w ≠ .idle := by simpa using hw
    exact hl.2.2.2.2.1 v w hne hv' hw' u hu
  · intro v hv
    simp [hg v] at hv
theorem config_ext {x y : Config n} (hp : ∀ v, x.peb v = y.peb v)
    (hg : ∀ v, x.ghost v = y.ghost v) : x = y := by
  have hp' := funext hp
  have hg' := funext hg
  cases x; cases y
  cases hp'; cases hg'; rfl

theorem reverse_restores (hl : Legal pred q a) (hq : ∀ v, q.ghost v = false)
    (hg : ∀ v : Fin n, ghostAt a v = false) :
    afterRound (afterRound q a) (reverse a) = q := by
  apply config_ext
  · intro v
    cases hx : firstAt a v with
    | idle => simp [afterRound,afterFirst,first_reverse,hx,swap,hg v]
    | pebble =>
      have h := hl.2.1 v hx
      simp [afterRound,afterFirst,first_reverse,hx,swap,hg v,h]
    | unpebble =>
      have h := hl.2.2.1 v hx
      simp [afterRound,afterFirst,first_reverse,hx,swap,hg v,h]
  · intro v
    cases hx : firstAt a v <;> simp [afterRound,afterFirst,first_reverse,hx,swap,hg v,hq v]

theorem reverse_work (a : Action) : roundWork (reverse a) = roundWork a := by
  cases a with
  | mk ms gs =>
    simp only [roundWork,reverse]
    induction ms with
    | nil => rfl
    | cons m ms ih => cases m <;> simp_all [swap]

theorem no_ghost_first (hg : ∀ v : Fin n, ghostAt a v = false) :
    afterFirst q a = afterRound q a := by
  apply config_ext <;> intro v <;> simp [afterRound,hg v]

theorem reverse_space (hl : Legal pred q a) (hq : ∀ v, q.ghost v = false)
    (hg : ∀ v : Fin n, ghostAt a v = false) :
    roundSpace (afterRound q a) (reverse a) = roundSpace q a := by
  have hr : ∀ v : Fin n, ghostAt (reverse a) v = false := by simpa using hg
  unfold roundSpace
  rw [no_ghost_first hr, reverse_restores hl hq hg, no_ghost_first hg]
  congr 1
  apply List.filter_congr
  intro v hv
  exact Bool.or_comm _ _
theorem reverse_step (hi : ∀ v, pred v v = false)
    (hl : Legal pred q a) (hq : ∀ v, q.ghost v = false)
    (hg : ∀ v : Fin n, ghostAt a v = false)
    (hm : a.first.length = n) (hgs : a.ghosts.length = n) :
    PaperStep pred (afterRound q a) ⟨q,roundWork a,roundSpace q a⟩ := by
  refine ⟨reverse a,?_,hgs,reverse_legal hi hl hq hg,?_⟩
  · simpa [reverse] using hm
  · simp only [edge,reverse_restores hl hq hg,reverse_work,reverse_space hl hq hg]
#print axioms reverse_step
#print axioms reverse_legal
#print axioms reverse_restores
#print axioms reverse_work
#print axioms reverse_space
end SpookyReverse
