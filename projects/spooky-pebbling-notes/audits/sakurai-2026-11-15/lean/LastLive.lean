import GapLength
namespace LastLive
open SpookyRound TraceBridge CutBound RefPartition

theorem last_compute_suffix {n : Nat} {pred : Fin n → Fin n → Bool}
 {q : Config n} {xs ys : List Action} {b : Action} {r : SpookyDP.Result (Config n)}
 (h : ActionRuns pred q (xs++b::ys) r) (u : Fin n)
 (hb : references pred u b=true) (hx : ∃a∈xs,firstAt a u=.pebble) :
 ∃pre c suffix before t,
 xs=pre++c::suffix ∧ (∃p, ActionRuns pred q pre p ∧ p.state=before) ∧ firstAt c u=.pebble ∧ ghostAt c u=false ∧
 (∀a∈suffix,firstAt a u≠.pebble) ∧
 ActionRuns pred (afterRound before c) (suffix++b::ys) t ∧
 (afterRound before c).peb u=true ∧
 Area.live u (afterRound before c) suffix=suffix.length ∧
 suffix.length≤Area.volume (afterRound before c) suffix := by
 obtain ⟨pre,c,suffix,he,hc,hn⟩ := RootCut.last_witness (fun a => firstAt a u=.pebble) xs hx
 obtain ⟨p,t,hp,ht,hs⟩ := split_actions pre (c::suffix++b::ys) (by
   simpa only [he,List.append_assoc,List.cons_append] using h)
 cases ht with
 | cons hm hg hl ht =>
   rename_i tail
   obtain ⟨z,zr,hz,hzr,hze⟩ := split_actions suffix (b::ys) ht
   have hlegal : Legal pred z.state b := by cases hzr; assumption
   have hkp := reference_old_pebble hlegal u hb
   have hzp : z.state.peb u=true := by
     by_cases hpb : z.state.peb u=true
     · exact hpb
     · cases hgb : z.state.ghost u <;> simp [kind,hpb,hgb] at hkp
   have hv := RefArea.no_compute_live hz u hn hzp
   have hgfalse : ghostAt c u=false := by
     cases hh : ghostAt c u
     · rfl
     · simp [afterRound,hh] at hv
   exact ⟨pre,c,suffix,p.state,tail,he,⟨p,hp,rfl⟩,hc,hgfalse,hn,ht,hv.1,hv.2,
     by rw [←hv.2]; exact RefArea.live_le_volume _ _ u⟩

#check last_compute_suffix
#print axioms last_compute_suffix

theorem prior_compute_required {n : Nat} {pred : Fin n → Fin n → Bool}
 {q : Config n} {xs ys : List Action} {b : Action} {r : SpookyDP.Result (Config n)}
 (h : ActionRuns pred q (xs++b::ys) r) (u : Fin n)
 (hb : references pred u b=true) (hq : kind q u≠.pebble) :
 ∃a∈xs,firstAt a u=.pebble := by
 obtain ⟨p,t,hp,ht,he⟩ := split_actions xs (b::ys) h
 have hl : Legal pred p.state b := by cases ht; assumption
 exact compute_action_exists hp u hq (reference_old_pebble hl u hb)
#print axioms prior_compute_required
end LastLive
