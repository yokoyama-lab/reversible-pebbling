import RefGlobal
import Area
namespace RefArea
open SpookyRound TraceBridge CutBound RefPartition

theorem reverse_pebble (q : Config n) (a : Action) (v : Fin n)
 (hc : firstAt a v ≠ .pebble) (hp : (afterRound q a).peb v=true) : q.peb v=true := by
 cases hm : firstAt a v <;> simp_all [afterRound,afterFirst]

theorem no_compute_live {pred : Fin n → Fin n → Bool}
 (h : ActionRuns pred q as r) (v : Fin n)
 (hc : ∀a∈as,firstAt a v ≠ .pebble) (hp : r.state.peb v=true) :
 q.peb v=true ∧ Area.live v q as=as.length := by
 induction h with
 | nil q => exact ⟨hp,rfl⟩
 | @cons q a as r hm hg hl ht ih =>
   have hi := ih (fun b hb => hc b (by simp [hb])) hp
   have hq := reverse_pebble q a v (hc a (by simp)) hi.1
   refine ⟨hq,?_⟩
   simp only [Area.live,hq,ite_true,List.length_cons]
   omega

theorem reference_suffix_live {pred : Fin n → Fin n → Bool}
 (h : ActionRuns pred q (xs++b::ys) r) (v : Fin n)
 (hb : references pred v b=true) (hc : ∀a∈xs,firstAt a v ≠ .pebble) :
 Area.live v q xs=xs.length := by
 obtain ⟨p,t,hp,ht,he⟩ := split_actions xs (b::ys) h
 have hl : Legal pred p.state b := by cases ht; assumption
 have hk := reference_old_pebble hl v hb
 have hpb : p.state.peb v=true := by
   by_cases hh : p.state.peb v=true
   · exact hh
   · cases hg : p.state.ghost v <;> simp [kind,hh,hg] at hk
 exact (no_compute_live hp v hc hpb).2

-- A real two-vertex dependency example, not a clean-tree lower-bound counterexample.
def pred2 (v u : Fin 2) : Bool := v.val==0 && u.val==1
def q0 : Config 2 := ⟨fun v => v.val==1,fun _ => false⟩
def a : Action := ⟨[.pebble,.idle],[false,true]⟩
def wait : Action := ⟨[.idle,.idle],[false,false]⟩
def restore : Action := ⟨[.idle,.pebble],[false,false]⟩
def b : Action := ⟨[.unpebble,.idle],[false,false]⟩
def eval (q : Config n) : List Action → SpookyDP.Result (Config n)
 | [] => ⟨q,0,0⟩
 | a::as => SpookyDP.prepend (edge q a) (eval (afterRound q a) as)

theorem counterexample_run : ActionRuns pred2 q0 [a,wait,restore,b] (eval q0 [a,wait,restore,b]) := by
 apply ActionRuns.cons (by decide) (by decide) (by decide)
 apply ActionRuns.cons (by decide) (by decide) (by decide)
 apply ActionRuns.cons (by decide) (by decide) (by decide)
 apply ActionRuns.cons (by decide) (by decide) (by decide)
 exact ActionRuns.nil _

theorem endpoint_reference_not_continuity :
 references pred2 (1 : Fin 2) a=true ∧ references pred2 (1 : Fin 2) b=true ∧
 Area.live (1 : Fin 2) q0 [a,wait,restore]=1 ∧
 [a,wait,restore].length=3 ∧
 count .compute (events (1 : Fin 2) [a,wait,restore])=1 := by decide
#print axioms no_compute_live
#print axioms reference_suffix_live
#print axioms counterexample_run
#print axioms endpoint_reference_not_continuity

theorem term_le_sum (xs : List α) (f : α → Nat) (v : α) (hv : v∈xs) :
 f v≤(xs.map f).sum := by
 induction xs with
 | nil => simp at hv
 | cons x xs ih =>
   simp only [List.mem_cons] at hv
   simp only [List.map_cons,List.sum_cons]
   rcases hv with rfl|hv
   · omega
   · have hh := ih hv; omega

theorem live_le_volume (q : Config n) (as : List Action) (v : Fin n) :
 Area.live v q as≤Area.volume q as := by
 have hh := term_le_sum (List.finRange n) (fun u => Area.live u q as) v (by simp)
 rw [←Area.boundary_by_vertex] at hh
 exact Nat.le_trans hh (Area.boundary_le_volume as q)

theorem reference_area {pred : Fin n → Fin n → Bool}
 (h : ActionRuns pred q (xs++b::ys) r) (v : Fin n)
 (hb : references pred v b=true) (hc : ∀a∈xs,firstAt a v ≠ .pebble) :
 xs.length≤Area.volume q xs := by
 rw [←reference_suffix_live h v hb hc]
 exact live_le_volume q xs v
#print axioms reference_area
end RefArea
