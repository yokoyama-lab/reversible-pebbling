import LiftCost
namespace ParallelMerge
open SpookyRound

def pick (a b : Move) : Move := if a=.idle then b else a
def merge (n : Nat) (a b : Action) : Action :=
 ⟨(List.finRange n).map (fun v=>pick (firstAt a v) (firstAt b v)),
 (List.finRange n).map (fun v=>ghostAt a v || ghostAt b v)⟩
@[simp] theorem first_merge (a b : Action) (v : Fin n) :
 firstAt (merge n a b) v=pick (firstAt a v) (firstAt b v) := by simp [firstAt,merge]
@[simp] theorem ghost_merge (a b : Action) (v : Fin n) :
 ghostAt (merge n a b) v=(ghostAt a v || ghostAt b v) := by simp [ghostAt,merge]

def Apart (n : Nat) (a b : Action) := ∀v : Fin n,
 (firstAt a v≠.idle ∨ ghostAt a v=true) → firstAt b v=.idle ∧ ghostAt b v=false

theorem apart_symm (h : Apart n a b) : Apart n b a := by
 intro v hv
 have hh := h v
 constructor
 · by_cases ha : firstAt a v=.idle
   · exact ha
   · have hb := hh (Or.inl ha); rcases hv with hv|hv <;> simp_all
 · cases hg : ghostAt a v with
   | false => rfl
   | true => have hb := hh (Or.inr hg); rcases hv with hv|hv <;> simp_all

def Cross (pred : Fin n → Fin n → Bool) (a b : Action) :=
 ∀v w,firstAt a v≠.idle → firstAt b w≠.idle → ∀u,
 (u=v ∨ pred v u=true) → ¬(u=w ∨ pred w u=true)

theorem cross_symm (h : Cross pred a b) : Cross pred b a := by
 intro v w hv hw u hu hu'
 exact h w v hw hv u hu' hu

theorem picked_active (x y : Move) (h : pick x y≠.idle) : x≠.idle ∨ y≠.idle := by
 cases x <;> cases y <;> simp_all [pick]

theorem merge_legal {pred : Fin n → Fin n → Bool} {q : Config n}
 (ha : Legal pred q a) (hb : Legal pred q b)
 (hs : Apart n a b) (hc : Cross pred a b) : Legal pred q (merge n a b) := by
 refine ⟨ha.1,?_,?_,?_,?_,?_⟩
 · intro v hv
   simp only [first_merge,pick] at hv
   split at hv
   · exact hb.2.1 v hv
   · exact ha.2.1 v hv
 · intro v hv
   simp only [first_merge,pick] at hv
   split at hv
   · exact hb.2.2.1 v hv
   · exact ha.2.2.1 v hv
 · intro v hv u hu
   have hh := picked_active _ _ (by simpa using hv)
   rcases hh with hh|hh
   · exact ha.2.2.2.1 v hh u hu
   · exact hb.2.2.2.1 v hh u hu
 · intro v w hvw hv hw u hu hu'
   have h1 := picked_active _ _ (by simpa using hv)
   have h2 := picked_active _ _ (by simpa using hw)
   rcases h1 with h1|h1 <;> rcases h2 with h2|h2
   · exact ha.2.2.2.2.1 v w hvw h1 h2 u hu hu'
   · exact hc v w h1 h2 u hu hu'
   · exact cross_symm hc v w h1 h2 u hu hu'
   · exact hb.2.2.2.2.1 v w hvw h1 h2 u hu hu'
 · intro v hv
   have hg : ghostAt a v=true ∨ ghostAt b v=true := by simpa using hv
   rcases hg with hg|hg
   · have hi := (hs v (Or.inr hg)).1
     have hh := ha.2.2.2.2.2 v hg
     cases hm : firstAt a v <;> simpa [afterFirst,hm,hi,pick] using hh
   · have hi := (apart_symm hs v (Or.inr hg)).1
     have hh := hb.2.2.2.2.2 v hg
     simpa [afterFirst,hi,pick] using hh

theorem merge_round (a b : Action) (q : Config n) (hs : Apart n a b) :
 afterRound q (merge n a b)=afterRound (afterRound q a) b := by
 apply SpookyReverse.config_ext <;> intro v
 · have h1 := hs v
   have h2 := apart_symm hs v
   cases am : firstAt a v <;> cases bm : firstAt b v <;>
   cases ag : ghostAt a v <;> cases bg : ghostAt b v <;>
   simp_all [afterRound,afterFirst,pick]
 · have h1 := hs v
   have h2 := apart_symm hs v
   cases am : firstAt a v <;> cases bm : firstAt b v <;>
   cases ag : ghostAt a v <;> cases bg : ghostAt b v <;>
   simp_all [afterRound,afterFirst,pick]

theorem merge_work (a b : Action) (ha : a.first.length=n) (hb : b.first.length=n)
 (hs : Apart n a b) : roundWork (merge n a b)=roundWork a+roundWork b := by
 rw [WorkBridge.indexed_work (n:=n) _ (by simp [merge]),WorkBridge.indexed_work a ha,
   WorkBridge.indexed_work b hb,←HeapPath.sum_add]
 congr 1
 apply List.map_congr_left
 intro v hv
 have hh := hs v
 cases am : firstAt a v <;> cases bm : firstAt b v <;> simp_all [pick,WorkBridge.cost]

theorem merge_space (a b : Action) (q : Config n) (hs : Apart n a b) :
 roundSpace q (merge n a b)≤roundSpace q a+roundSpace q b := by
 unfold roundSpace
 rw [CutSpace.filter_sum,CutSpace.filter_sum,CutSpace.filter_sum,←HeapPath.sum_add]
 apply Exceptions.sum_le
 intro v hv
 have hh := hs v
 cases am : firstAt a v <;> cases bm : firstAt b v <;> cases hp : q.peb v <;>
   simp_all [afterFirst,pick]

theorem simultaneous_step {pred : Fin n → Fin n → Bool} {q : Config n}
 (ha : Legal pred q a) (hb : Legal pred q b)
 (ham : a.first.length=n) (hbm : b.first.length=n)
 (hs : Apart n a b) (hc : Cross pred a b) :
 ∃r,PaperRuns pred 1 q r ∧ r.state=afterRound (afterRound q a) b ∧
 r.work=roundWork a+roundWork b ∧ r.space≤roundSpace q a+roundSpace q b := by
 have step : PaperStep pred q (edge q (merge n a b)) :=
   ⟨merge n a b,by simp [merge],by simp [merge],merge_legal ha hb hs hc,rfl⟩
 have run := PaperRuns.step step (PaperRuns.zero (afterRound q (merge n a b)))
 refine ⟨_,run,?_,?_,?_⟩
 · simpa [SpookyDP.prepend,edge] using merge_round a b q hs
 · simpa [SpookyDP.prepend,edge] using merge_work a b ham hbm hs
 · simpa [SpookyDP.prepend,edge] using merge_space a b q hs
open FringeEmbed

theorem decode_disjoint (r s D : Nat)
 (hr : 2^D≤r+1 ∧ r+1<2^(D+1)) (hs : 2^D≤s+1 ∧ s+1<2^(D+1)) (hne : r≠s)
 (v : Fin N) (i : Fin m) (j : Fin k)
 (hi : decode r m v=some i) (hj : decode s k v=some j) : False := by
 exact fringe_disjoint r s i.val j.val D hr hs hne
   ((decode_sound r m v i hi).trans (decode_sound s k v j hj).symm)

theorem fringe_apart (r s D m k N : Nat)
 (hr : 2^D≤r+1 ∧ r+1<2^(D+1)) (hs : 2^D≤s+1 ∧ s+1<2^(D+1)) (hne : r≠s)
 (a b : Action) : Apart N (liftAction r m N a) (liftAction s k N b) := by
 intro v hv
 cases hi : decode r m v with
 | none => simp [hi] at hv
 | some i =>
   cases hj : decode s k v with
   | none => simp [hj]
   | some j => exact False.elim (decode_disjoint r s D hr hs hne v i j hi hj)

theorem fringe_cross (r s D h : Nat)
 (hr : 2^D≤r+1 ∧ r+1<2^(D+1)) (hs : 2^D≤s+1 ∧ s+1<2^(D+1)) (hne : r≠s)
 (a b : Action) : Cross (HeapPath.pred (n:=2^(D+h)-1))
   (liftAction r (2^h-1) (2^(D+h)-1) a) (liftAction s (2^h-1) (2^(D+h)-1) b) := by
 intro v w hv hw u hu hu'
 cases hi : decode r (2^h-1) v with
 | none => simp [hi] at hv
 | some i =>
   cases hj : decode s (2^h-1) w with
   | none => simp [hj] at hw
   | some j =>
     have hlu : ∃k : Fin (2^h-1),decode r (2^h-1) u=some k := by
       rcases hu with rfl|hu
       · exact ⟨i,hi⟩
       · obtain ⟨k,hk,_⟩ := fringe_dep_closed r D h hr v i hi u hu; exact ⟨k,hk⟩
     have hru : ∃k : Fin (2^h-1),decode s (2^h-1) u=some k := by
       rcases hu' with rfl|hu
       · exact ⟨j,hj⟩
       · obtain ⟨k,hk,_⟩ := fringe_dep_closed s D h hs w j hj u hu; exact ⟨k,hk⟩
     obtain ⟨k,hk⟩ := hlu
     obtain ⟨l,hl⟩ := hru
     exact decode_disjoint r s D hr hs hne u k l hk hl

theorem fringe_simultaneous_step (r s D h : Nat)
 (hr : 2^D≤r+1 ∧ r+1<2^(D+1)) (hs : 2^D≤s+1 ∧ s+1<2^(D+1)) (hne : r≠s)
 (a b : Action) (ha : a.first.length=2^h-1) (hb : b.first.length=2^h-1)
 (q : Config (2^(D+h)-1))
 (hla : Legal HeapPath.pred q (liftAction r (2^h-1) (2^(D+h)-1) a))
 (hlb : Legal HeapPath.pred q (liftAction s (2^h-1) (2^(D+h)-1) b)) :
 ∃t,PaperRuns HeapPath.pred 1 q t ∧ t.work=roundWork a+roundWork b ∧
 t.state=afterRound (afterRound q (liftAction r (2^h-1) (2^(D+h)-1) a))
   (liftAction s (2^h-1) (2^(D+h)-1) b) ∧
 t.space≤roundSpace q (liftAction r (2^h-1) (2^(D+h)-1) a)+
   roundSpace q (liftAction s (2^h-1) (2^(D+h)-1) b) := by
 obtain ⟨t,ht,hstate,hw,hsp⟩ := simultaneous_step hla hlb (by simp [liftAction]) (by simp [liftAction])
   (fringe_apart r s D _ _ _ hr hs hne a b) (fringe_cross r s D h hr hs hne a b)
 rw [LiftCost.lift_work r _ _ (fun i=>embed_fin_bound r i.val D h hr i.isLt) a ha,
     LiftCost.lift_work s _ _ (fun i=>embed_fin_bound s i.val D h hs i.isLt) b hb] at hw
 exact ⟨t,ht,hw,hstate,hsp⟩
#print axioms fringe_simultaneous_step
#print axioms simultaneous_step
end ParallelMerge
