import FrameUpper
namespace FringeEmbed

def depth (i : Nat) := (i+1).log2
def embed (root i : Nat) := 2^(depth i)*root+i

theorem depth_left (i : Nat) : depth (2*i+1)=depth i+1 := by
 unfold depth
 have he : 2*i+1+1=2*(i+1) := by omega
 rw [he,Nat.log2_two_mul (by omega)]

theorem depth_right (i : Nat) : depth (2*i+2)=depth i+1 := by
 apply (Nat.log2_eq_iff (by omega)).mpr
 have hl := Nat.log2_self_le (n:=i+1) (by omega)
 have hu := Nat.lt_log2_self (n:=i+1)
 unfold depth
 rw [Nat.pow_succ]
 constructor
 · omega
 · rw [Nat.pow_succ]; omega

theorem embed_left (root i : Nat) : embed root (2*i+1)=2*embed root i+1 := by
 unfold embed
 rw [depth_left,Nat.pow_succ]
 simp [Nat.mul_add,Nat.add_mul,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
 omega

theorem embed_right (root i : Nat) : embed root (2*i+2)=2*embed root i+2 := by
 unfold embed
 rw [depth_right,Nat.pow_succ]
 simp [Nat.mul_add,Nat.add_mul,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
 omega

theorem depth_mono {i j : Nat} (h : i≤j) : depth i≤depth j := by
 apply (Nat.le_log2 (n:=j+1) (by omega)).mpr
 exact Nat.le_trans (Nat.log2_self_le (n:=i+1) (by omega)) (by omega)

theorem embed_strict (root : Nat) {i j : Nat} (h : i<j) : embed root i<embed root j := by
 have hd := depth_mono (Nat.le_of_lt h)
 have hp := Nat.pow_le_pow_right (n:=2) (by decide) hd
 have hm := Nat.mul_le_mul_right root hp
 unfold embed; omega

theorem embed_injective (root : Nat) : Function.Injective (embed root) := by
 intro i j he
 by_cases h : i<j
 · have hh := embed_strict root h; omega
 · by_cases hj : j<i
   · have hh := embed_strict root hj; omega
   · omega

theorem root_le_embed (root i : Nat) : root≤embed root i := by
 have hp : 1≤2^(depth i) := Nat.pow_pos (by decide)
 have hm := Nat.mul_le_mul_right root hp
 unfold embed; omega

theorem proper_excludes_root (root i : Nat) (hr : 0<root) : embed root i≠0 := by
 have hh := root_le_embed root i; omega

theorem depth_range (i : Nat) : 2^(depth i)≤i+1 ∧ i+1<2^(depth i+1) :=
 ⟨Nat.log2_self_le (by omega),Nat.lt_log2_self⟩

theorem embed_bounds (root i : Nat) :
 (root+1)*2^(depth i)≤embed root i+1 ∧ embed root i+1<(root+2)*2^(depth i) := by
 have hh := depth_range i
 rw [Nat.pow_succ] at hh
 unfold embed
 simp only [Nat.add_mul,Nat.one_mul,Nat.mul_comm root]
 omega

theorem same_layer_disjoint (r s i j : Nat)
 (hrs : r<s) (hij : depth i=depth j) : embed r i<embed s j := by
 have hi := (embed_bounds r i).2
 have hj := (embed_bounds s j).1
 have hm := Nat.mul_le_mul_right (2^(depth j)) (show r+2≤s+1 by omega)
 rw [hij] at hi
 omega

-- Root lies at depth D; loc tree height h terminates exactly at global depth D+h.
theorem embed_depth (root i D : Nat) (hr : 2^D≤root+1 ∧ root+1<2^(D+1)) :
 depth (embed root i)=D+depth i := by
 have hh := embed_bounds root i
 apply (Nat.log2_eq_iff (by omega)).mpr
 constructor
 · calc
    2^(D+depth i) = 2^D*2^(depth i) := Nat.pow_add _ _ _
    _ ≤ (root+1)*2^(depth i) := Nat.mul_le_mul_right _ hr.1
    _ ≤ embed root i+1 := hh.1
 · have hs : root+2≤2^(D+1) := by omega
   have hm := Nat.mul_le_mul_right (2^(depth i)) hs
   have he : 2^(D+depth i+1)=2^(D+1)*2^(depth i) := by
     rw [←Nat.pow_add]; congr 1; omega
   rw [he]
   exact Nat.lt_of_lt_of_le hh.2 hm

theorem embed_fin_bound (root i D h : Nat)
 (hr : 2^D≤root+1 ∧ root+1<2^(D+1)) (hi : i<2^h-1) :
 embed root i<2^(D+h)-1 := by
 have hdep : depth i<h := (Nat.log2_lt (n:=i+1) (by omega)).mpr (by omega)
 have hd := embed_depth root i D hr
 have hb := (depth_range (embed root i)).2
 rw [hd] at hb
 have hp := Nat.pow_le_pow_right (n:=2) (by decide) (show D+depth i+1≤D+h by omega)
 omega
theorem fringe_disjoint (r s i j D : Nat)
 (hr : 2^D≤r+1 ∧ r+1<2^(D+1))
 (hs : 2^D≤s+1 ∧ s+1<2^(D+1)) (hne : r≠s) : embed r i≠embed s j := by
 intro he
 have hd := congrArg depth he
 rw [embed_depth r i D hr,embed_depth s j D hs] at hd
 have hij : depth i=depth j := by omega
 by_cases h : r<s
 · have hh := same_layer_disjoint r s i j h hij; omega
 · have hh := same_layer_disjoint s r j i (by omega) hij.symm; omega

open SpookyRound
noncomputable def decode (root m : Nat) (v : Fin N) : Option (Fin m) :=
 if h : ∃i : Fin m, embed root i.val=v.val then some (Classical.choose h) else none

theorem decode_sound (root m : Nat) (v : Fin N) (i : Fin m)
 (h : decode root m v=some i) : embed root i.val=v.val := by
 unfold decode at h
 split at h
 · rename_i hh
   have he : Classical.choose hh=i := Option.some.inj h
   rw [←he]; exact Classical.choose_spec hh
 · contradiction

theorem decode_image (root m : Nat) (i : Fin m) (v : Fin N)
 (h : embed root i.val=v.val) : decode root m v=some i := by
 unfold decode
 have hh : ∃j : Fin m,embed root j.val=v.val := ⟨i,h⟩
 rw [dif_pos hh]
 congr 1
 apply Fin.ext
 apply embed_injective root
 exact (Classical.choose_spec hh).trans h.symm

theorem decode_root_none (root m : Nat) (hroot : 0<root) (hN : 0<N) :
 decode root m (⟨0,hN⟩ : Fin N)=none := by
 unfold decode
 apply dif_neg
 rintro ⟨i,hi⟩
 exact proper_excludes_root root i.val hroot hi

noncomputable def liftAction (root m N : Nat) (a : Action) : Action :=
 ⟨(List.finRange N).map (fun v=>match decode root m v with | none=>.idle | some i=>firstAt a i),
  (List.finRange N).map (fun v=>match decode root m v with | none=>false | some i=>ghostAt a i)⟩

@[simp] theorem first_lift (root m : Nat) (a : Action) (v : Fin N) :
 firstAt (liftAction root m N a) v = match decode root m v with | none=>.idle | some i=>firstAt a i := by
 simp [firstAt,liftAction]
@[simp] theorem ghost_lift (root m : Nat) (a : Action) (v : Fin N) :
 ghostAt (liftAction root m N a) v = match decode root m v with | none=>false | some i=>ghostAt a i := by
 simp [ghostAt,liftAction]

theorem lifted_root_avoids (root m N : Nat) (a : Action) (hr : 0<root) (hn : 0<N) :
 firstAt (liftAction root m N a) ⟨0,hn⟩=.idle ∧ ghostAt (liftAction root m N a) ⟨0,hn⟩=false := by
 simp [decode_root_none root m hr hn]

theorem lifted_run_preserves_root {pred : Fin N → Fin N → Bool} {q : Config N}
 {r : SpookyDP.Result (Config N)} (root m : Nat) (as : List Action)
 (hr : 0<root) (hn : 0<N)
 (h : TraceBridge.ActionRuns pred q (as.map (liftAction root m N)) r) :
 ∃t,PaperRuns pred as.length (FrameUpper.frame (fun v=>decide (v=(⟨0,hn⟩ : Fin N))) q) t ∧
 t.state.peb ⟨0,hn⟩=true ∧ t.work=r.work ∧ t.space≤r.space+1 := by
 obtain ⟨t,ht,hs,hp,hw,hsp⟩ := FrameUpper.protected_root h ⟨0,hn⟩ (by
   intro a ha
   obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
   exact lifted_root_avoids root m N b hr hn)
 exact ⟨t,by simpa using ht,hp,hw,hsp⟩
noncomputable def liftConfig (root : Nat) (outside : Config N) (loc : Config m) : Config N :=
 ⟨fun v=>match decode root m v with |none=>outside.peb v |some i=>loc.peb i,
  fun v=>match decode root m v with |none=>outside.ghost v |some i=>loc.ghost i⟩

theorem decode_same (root : Nat) (v w : Fin N) (i : Fin m)
 (hv : decode root m v=some i) (hw : decode root m w=some i) : v=w := by
 apply Fin.ext
 exact (decode_sound root m v i hv).symm.trans (decode_sound root m w i hw)

def DepClosed (root : Nat) (p : Fin m → Fin m → Bool) (P : Fin N → Fin N → Bool) :=
 ∀v i,decode root m v=some i → ∀u,P v u=true → ∃j,decode root m u=some j ∧ p i j=true

theorem lift_after_first (root : Nat) (outside : Config N) (loc : Config m) (a : Action) :
 afterFirst (liftConfig root outside loc) (liftAction root m N a)=
 liftConfig root outside (afterFirst loc a) := by
 apply SpookyReverse.config_ext <;> intro v <;>
 cases hd : decode root m v with
 | none => simp [afterFirst,liftConfig,hd]
 | some i => cases hm : firstAt a i <;> simp [afterFirst,liftConfig,hd,hm]

theorem lift_after_round (root : Nat) (outside : Config N) (loc : Config m) (a : Action) :
 afterRound (liftConfig root outside loc) (liftAction root m N a)=
 liftConfig root outside (afterRound loc a) := by
 apply SpookyReverse.config_ext <;> intro v <;>
 cases hd : decode root m v with
 | none => simp [afterRound,afterFirst,liftConfig,hd]
 | some i => cases hm : firstAt a i <;> simp [afterRound,afterFirst,liftConfig,hd,hm]

theorem lift_legal (root : Nat) (outside : Config N) (loc : Config m)
 (p : Fin m → Fin m → Bool) (P : Fin N → Fin N → Bool) (a : Action)
 (hc : DepClosed root p P) (ho : FillUpper.consistent outside)
 (hl : Legal p loc a) : Legal P (liftConfig root outside loc) (liftAction root m N a) := by
 refine ⟨?_,?_,?_,?_,?_,?_⟩
 · intro v
   cases hd : decode root m v with
   | none => simpa [liftConfig,hd] using ho v
   | some i => simpa [liftConfig,hd] using hl.1 i
 · intro v hv
   cases hd : decode root m v with
   | none => simp [hd] at hv
   | some i => have hh : firstAt a i=.pebble := by simpa [hd] using hv
               simpa [liftConfig,hd] using hl.2.1 i hh
 · intro v hv
   cases hd : decode root m v with
   | none => simp [hd] at hv
   | some i => have hh : firstAt a i=.unpebble := by simpa [hd] using hv
               simpa [liftConfig,hd] using hl.2.2.1 i hh
 · intro v hv u hu
   cases hd : decode root m v with
   | none => simp [hd] at hv
   | some i =>
     have hh : firstAt a i≠.idle := by simpa [hd] using hv
     obtain ⟨j,hj,hp⟩ := hc v i hd u hu
     simpa [liftConfig,hj] using hl.2.2.2.1 i hh j hp
 · intro v w hvw hv hw u huv huw
   cases hd : decode root m v with
   | none => simp [hd] at hv
   | some i =>
     cases he : decode root m w with
     | none => simp [he] at hw
     | some j =>
       have hi : firstAt a i≠.idle := by simpa [hd] using hv
       have hj : firstAt a j≠.idle := by simpa [he] using hw
       have hij : i≠j := by intro hh; subst j; exact hvw (decode_same root v w i hd he)
       have hleft : ∃k,decode root m u=some k ∧ (k=i ∨ p i k=true) := by
         rcases huv with rfl|hu
         · exact ⟨i,hd,Or.inl rfl⟩
         · obtain ⟨k,hk,hp⟩ := hc v i hd u hu; exact ⟨k,hk,Or.inr hp⟩
       have hright : ∃k,decode root m u=some k ∧ (k=j ∨ p j k=true) := by
         rcases huw with rfl|hu
         · exact ⟨j,he,Or.inl rfl⟩
         · obtain ⟨k,hk,hp⟩ := hc w j he u hu; exact ⟨k,hk,Or.inr hp⟩
       obtain ⟨k,hk,hki⟩ := hleft
       obtain ⟨l,hl',hlj⟩ := hright
       have hkl : k=l := Option.some.inj (hk.symm.trans hl')
       subst l
       exact hl.2.2.2.2.1 i j hij hi hj k hki hlj
 · intro v hv
   rw [lift_after_first]
   cases hd : decode root m v with
   | none => simp [hd] at hv
   | some i => have hh : ghostAt a i=true := by simpa [hd] using hv
               simpa [liftConfig,hd] using hl.2.2.2.2.2 i hh

theorem lift_actions (root : Nat) (outside : Config N)
 (p : Fin m → Fin m → Bool) (P : Fin N → Fin N → Bool)
 (hc : DepClosed root p P) (ho : FillUpper.consistent outside)
 (h : TraceBridge.ActionRuns p loc as r) :
 ∃t,TraceBridge.ActionRuns P (liftConfig root outside loc) (as.map (liftAction root m N)) t ∧
 t.state=liftConfig root outside r.state := by
 induction h with
 | nil q => exact ⟨_,TraceBridge.ActionRuns.nil _,rfl⟩
 | @cons q a as r hm hg hl ht ih =>
   obtain ⟨t,ht',hs⟩ := ih
   have ht'' : TraceBridge.ActionRuns P (afterRound (liftConfig root outside q) (liftAction root m N a))
       (as.map (liftAction root m N)) t := by rw [lift_after_round]; exact ht'
   exact ⟨_,TraceBridge.ActionRuns.cons (by simp [liftAction]) (by simp [liftAction])
     (lift_legal root outside q p P a hc ho hl) ht'',hs⟩
theorem local_bound_of_global (root j D h : Nat)
 (hr : 2^D≤root+1 ∧ root+1<2^(D+1))
 (hj : embed root j<2^(D+h)-1) : j<2^h-1 := by
 have hd : depth (embed root j)<D+h := (Nat.log2_lt (n:=embed root j+1) (by omega)).mpr (by omega)
 rw [embed_depth root j D hr] at hd
 have hjd : depth j<h := by omega
 have hh := (Nat.log2_lt (n:=j+1) (by omega)).mp hjd
 omega

theorem fringe_dep_closed (root D h : Nat)
 (hr : 2^D≤root+1 ∧ root+1<2^(D+1)) :
 DepClosed root (HeapPath.pred (n:=2^h-1)) (HeapPath.pred (n:=2^(D+h)-1)) := by
 intro v i hv u hu
 have he := decode_sound root (2^h-1) v i hv
 have hp : 0<u.val ∧ v.val=(u.val-1)/2 := by simpa [HeapPath.pred] using hu
 have hh : u.val=2*v.val+1 ∨ u.val=2*v.val+2 := by omega
 rcases hh with hh|hh
 · have hj : embed root (2*i.val+1)=u.val := by rw [embed_left,he,hh]
   have hb : 2*i.val+1<2^h-1 := local_bound_of_global root _ D h hr (by rw [hj]; exact u.isLt)
   refine ⟨⟨2*i.val+1,hb⟩,decode_image root _ _ u hj,?_⟩
   simp [HeapPath.pred]
 · have hj : embed root (2*i.val+2)=u.val := by rw [embed_right,he,hh]
   have hb : 2*i.val+2<2^h-1 := local_bound_of_global root _ D h hr (by rw [hj]; exact u.isLt)
   refine ⟨⟨2*i.val+2,hb⟩,decode_image root _ _ u hj,?_⟩
   simp [HeapPath.pred]; omega

theorem fringe_actions (root D h : Nat) {q : Config (2^h-1)} {r : SpookyDP.Result (Config (2^h-1))}
 (hr : 2^D≤root+1 ∧ root+1<2^(D+1)) (outside : Config (2^(D+h)-1))
 (ho : FillUpper.consistent outside)
 (ha : TraceBridge.ActionRuns (HeapPath.pred (n:=2^h-1)) q as r) :
 ∃t,TraceBridge.ActionRuns HeapPath.pred (liftConfig root outside q)
   (as.map (liftAction root (2^h-1) (2^(D+h)-1))) t ∧ t.state=liftConfig root outside r.state :=
 lift_actions root outside HeapPath.pred HeapPath.pred (fringe_dep_closed root D h hr) ho ha
theorem fringe_paper (root D h d : Nat) {q : Config (2^h-1)} {r : SpookyDP.Result (Config (2^h-1))}
 (hr : 2^D≤root+1 ∧ root+1<2^(D+1)) (outside : Config (2^(D+h)-1))
 (ho : FillUpper.consistent outside) (ha : PaperRuns HeapPath.pred d q r) :
 ∃t,PaperRuns HeapPath.pred d (liftConfig root outside q) t ∧
 t.state=liftConfig root outside r.state ∧
 (∀v,decode root (2^h-1) v=none → t.state.peb v=outside.peb v ∧ t.state.ghost v=outside.ghost v) := by
 obtain ⟨as,hd,hs⟩ := TraceBridge.extract_actions ha
 obtain ⟨t,ht,hf⟩ := fringe_actions root D h hr outside ho hs
 refine ⟨t,?_,hf,?_⟩
 · have hh := FrameUpper.actions_paper ht
   simpa [hd] using hh
 · intro v hv; rw [hf]; simp [liftConfig,hv]
#print axioms fringe_paper
#print axioms fringe_actions
#print axioms fringe_dep_closed
#print axioms lift_actions
#print axioms lifted_run_preserves_root
#print axioms fringe_disjoint
#print axioms embed_fin_bound
#print axioms embed_injective
end FringeEmbed
