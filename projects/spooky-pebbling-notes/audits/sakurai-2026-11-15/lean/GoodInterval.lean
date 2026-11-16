import Area
namespace GoodInterval
open SpookyRound TraceBridge
variable {n : Nat} {q : Config n} {r : SpookyDP.Result (Config n)}

theorem compute_before_uncompute {pred : Fin n → Fin n → Bool}
    (h : ActionRuns pred q (xs++a::ys) r) (v : Fin n)
    (hs : kind q v ≠ .pebble) (ha : firstAt a v = .unpebble) :
    ∃ b ∈ xs, firstAt b v = .pebble := by
  obtain ⟨p,t,hp,ht,he⟩ := split_actions xs (a::ys) h
  cases ht with
  | cons hm hg hl htail =>
    apply compute_action_exists hp v hs
    have hh := hl.2.2.1 v ha
    simp [kind,hh]

theorem no_compute_after_unique (xs ys : List Action) (a : Action) (v : Fin n)
    (hc : CutBound.count .compute (events v (xs++a::ys)) = 1)
    (ha : firstAt a v = .pebble) :
    ∀ b ∈ ys, firstAt b v ≠ .pebble := by
  rw [Precut.counts_split] at hc
  have ht : CutBound.count .compute (events v (a::ys)) =
      1 + CutBound.count .compute (events v ys) := by
    cases hg : ghostAt a v <;> simp [events,firstEvent,secondEvent,CutBound.count,ha,hg,Nat.add_comm]
  rw [ht] at hc
  intro b hb hm
  have hh := Exceptions.count_positive .compute (events v ys)
    ((compute_in_events v ys).mpr ⟨b,hb,hm⟩)
  omega

theorem good_decomposition {pred : Fin n → Fin n → Bool}
    (h : ActionRuns pred q as r) (v : Fin n)
    (hs : kind q v ≠ .pebble)
    (hc : CutBound.count .compute (events v as) = 1)
    (hu : CutBound.count .uncompute (events v as) = 1) :
    ∃ xs c middle u tail, as = xs ++ c :: (middle ++ u :: tail) ∧
      firstAt c v = .pebble ∧ firstAt u v = .unpebble ∧
      (∀ b ∈ middle ++ u :: tail, firstAt b v ≠ .pebble) := by
  have hp : 0 < ((events v as).filter fun e => e == .uncompute).length := by
    simpa [CutBound.count] using (show 0 < CutBound.count .uncompute (events v as) by omega)
  obtain ⟨e,he⟩ := List.exists_mem_of_length_pos hp
  have hh := List.mem_filter.mp he
  have heq : e = .uncompute := by simpa using hh.2
  subst e
  obtain ⟨u,hU,huMove⟩ := (uncompute_in_events v as).mp hh.1
  obtain ⟨pre,tail,hsplit⟩ := Descendants.split_mem hU
  subst as
  obtain ⟨c,hC,hcMove⟩ := compute_before_uncompute h v hs huMove
  obtain ⟨xs,middle,hcsplit⟩ := Descendants.split_mem hC
  subst pre
  have heq : (xs ++ c :: middle) ++ u :: tail = xs ++ c :: (middle ++ u :: tail) := by simp
  rw [heq] at hc
  exact ⟨xs,c,middle,u,tail,heq,hcMove,huMove,no_compute_after_unique xs _ c v hc hcMove⟩

theorem live_through_cleanup {pred : Fin n → Fin n → Bool} (xs ys : List Action)
    (h : ActionRuns pred q (xs ++ a :: ys) r) (v : Fin n)
    (hu : firstAt a v = .unpebble)
    (hc : ∀ b ∈ xs ++ a :: ys, firstAt b v ≠ .pebble) :
    Area.live v q (xs++[a]) = xs.length+1 := by
  induction xs generalizing q r with
  | nil =>
    have hp := Area.occupied_until_cleanup h v ⟨a,by simp,hu⟩ hc
    simp [Area.live,hp]
  | cons b xs ih =>
    have hp := Area.occupied_until_cleanup h v ⟨a,by simp,hu⟩ hc
    cases h with
    | cons hm hg hl ht =>
      have hh := ih ht (fun c hm => hc c (by simp_all))
      simp only [List.cons_append,Area.live,hp,ite_true,List.length_cons]
      omega

-- The selected compute and cleanup are separated by actual round boundaries.
theorem good_live_interval {pred : Fin n → Fin n → Bool}
    (h : ActionRuns pred q as r) (v : Fin n)
    (hs : kind q v ≠ .pebble)
    (hc : CutBound.count .compute (events v as) = 1)
    (hu : CutBound.count .uncompute (events v as) = 1) :
    ∃ xs c middle u tail p t,
      as = xs ++ c :: (middle ++ u :: tail) ∧
      firstAt c v = .pebble ∧ firstAt u v = .unpebble ∧
      ActionRuns pred p (middle ++ u :: tail) t ∧ t.state = r.state ∧
      Area.live v p (middle++[u]) = middle.length+1 := by
  obtain ⟨xs,c,middle,u,tail,he,hcM,huM,hno⟩ := good_decomposition h v hs hc hu
  rw [he] at h
  obtain ⟨p,t,hp,ht,hfinal⟩ := split_actions xs (c::(middle++u::tail)) h
  cases ht with
  | cons hm hg hl htail =>
    exact ⟨xs,c,middle,u,tail,_,_,he,hcM,huM,htail,hfinal,
      live_through_cleanup middle tail htail v huM hno⟩
theorem unique_round_counts (xs ys : List Action) (a : Action) (v : Fin n)
    (m : Move) (e : CutBound.Event)
    (he : (m = .pebble ∧ e = .compute) ∨ (m = .unpebble ∧ e = .uncompute))
    (ha : firstAt a v = m)
    (hc : CutBound.count e (events v (xs++a::ys)) = 1) :
    CutBound.count e (events v xs) = 0 ∧ CutBound.count e (events v ys) = 0 := by
  rw [Precut.counts_split] at hc
  rcases he with ⟨hm,he⟩ | ⟨hm,he⟩
  · have hmove := ha.trans hm
    rw [he] at hc ⊢
    cases hg : ghostAt a v <;>
      simp [events,firstEvent,secondEvent,CutBound.count,hmove,hg] at hc <;>
      simp only [CutBound.count] <;> omega
  · have hmove := ha.trans hm
    rw [he] at hc ⊢
    cases hg : ghostAt a v <;>
      simp [events,firstEvent,secondEvent,CutBound.count,hmove,hg] at hc <;>
      simp only [CutBound.count] <;> omega
#print axioms unique_round_counts
#print axioms good_live_interval
end GoodInterval
