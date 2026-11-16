import TwoLifetimeExact
namespace ChainTwoProjection
open LocalCertificate ChainTrace ChainTwoLifetimeExact ChainUniqueLifetime

theorem split_first_count {α : Type} (f : α → Bool) (xs : List α) (n : Nat)
    (h : xs.countP f = n+1) :
    ∃ a p b, xs = a ++ p :: b ∧ f p = true ∧ a.countP f = 0 ∧ b.countP f = n := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
    cases hx : f x with
    | true =>
      refine ⟨[], x, xs, rfl, hx, rfl, ?_⟩
      simp [hx] at h
      omega
    | false =>
      have ht : xs.countP f = n+1 := by simpa [List.countP_cons, hx] using h
      obtain ⟨a,p,b,he,hp,ha,hb⟩ := ih ht
      refine ⟨x::a,p,b,?_,hp,?_,hb⟩
      · simp [he]
      · simp [hx,ha]

def projection (v : Nat) (es : List Event) : List Bool :=
  (es.filter (fun e => e.vertex == v)).map (fun e => e.place)

theorem projection_no_placement (v : Nat) (es : List Event)
    (hz : es.countP (isPlacement v) = 0) :
    projection v es = List.replicate (es.countP (isRemoval v)) false := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    have ht : es.countP (isPlacement v) = 0 := by
      simp only [List.countP_cons] at hz
      split at hz <;> omega
    have hh := ih ht
    by_cases hv : e.vertex = v
    · have hp : e.place = false := by
        cases he : e.place with
        | false => rfl
        | true =>
          have hn := zero_placements v (e::es) hz
          exact False.elim (hn e (by simp) he hv)
      simpa [projection, hv, hp, isRemoval, List.replicate_succ] using congrArg (List.cons false) hh
    · simpa [projection, List.filter_cons, hv, isRemoval] using hh

theorem two_placements_split (v : Nat) (es : List Event)
    (h : es.countP (isPlacement v) = 2) :
    ∃ a b c p q, es = a ++ p :: (b ++ q :: c) ∧
      p.place = true ∧ p.vertex = v ∧ q.place = true ∧ q.vertex = v := by
  obtain ⟨a,p,tail,he,hp,_,ht⟩ := split_first_count (isPlacement v) es 1 h
  obtain ⟨b,q,c,htail,hq,_,_⟩ := split_first_count (isPlacement v) tail 0 ht
  have hp' : p.place = true ∧ p.vertex = v := by simpa [isPlacement] using hp
  have hq' : q.place = true ∧ q.vertex = v := by simpa [isPlacement] using hq
  exact ⟨a,b,c,p,q,by simpa [htail] using he,hp'.1,hp'.2,hq'.1,hq'.2⟩

theorem two_lifetimes_projection (erasures board final : List Nat)
    (v : Nat) (es : List Event) (nd : board.Nodup)
    (initialAbsent : v ∉ board) (finalAbsent : v ∉ final)
    (count : es.countP (isPlacement v) = 2)
    (hr : run erasures board es = some final) :
    projection v es = [true, false, true, false] := by
  obtain ⟨a,b,c,p,q,he,hp,hpv,hq,hqv⟩ := two_placements_split v es count
  subst es
  have budget : (a ++ p :: (b ++ q :: c)).countP (isPlacement v) ≤ 2 := by omega
  obtain ⟨za,zb,zc⟩ := gaps_no_placements v a b c p q hp hpv hq hqv budget
  obtain ⟨ra,rb,rc⟩ := two_lifetimes_exact_gap_counts erasures board final v a b c p q
    nd initialAbsent finalAbsent hp hpv hq hqv budget hr
  have pa := projection_no_placement v a za
  have pb := projection_no_placement v b zb
  have pc := projection_no_placement v c zc
  rw [ra] at pa
  rw [rb] at pb
  rw [rc] at pc
  simp only [projection, List.filter_append, List.filter_cons, hpv, hqv,
    BEq.rfl, ite_true, List.map_append, List.map_cons, hp, hq]
  change projection v a ++ true :: (projection v b ++ true :: projection v c) = _
  rw [pa,pb,pc]
  rfl

#print axioms split_first_count
#print axioms projection_no_placement
#print axioms two_placements_split
#print axioms two_lifetimes_projection
end ChainTwoProjection
