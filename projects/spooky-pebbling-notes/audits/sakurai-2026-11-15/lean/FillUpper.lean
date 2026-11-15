import BatchUpper
namespace FillUpper
open SpookyRound BatchUpper

def consistent (q : Config n) := ∀v,¬(q.peb v=true ∧ q.ghost v=true)
def Saturated (q : Config n) (L : Nat) := consistent q ∧ ∀v,q.peb v=decide (L≤v.val)
def mask (L : Nat) (v : Fin n) := decide (L≤v.val ∧ v.val<2*L+1)

theorem evolve_consistent (q : Config n) (C : Fin n → Bool) (h : consistent q) :
 consistent (evolve q C (fun _=>false)) := by
 intro v
 have hh := h v
 cases hp : q.peb v <;> cases hg : q.ghost v <;> cases hc : C v <;> simp_all [evolve]

theorem fill_layer (q : Config n) (L : Nat) (h : Saturated q (2*L+1)) :
 Ready HeapPath.pred q (mask L) (fun _=>false) ∧
 Saturated (evolve q (mask L) (fun _=>false)) L := by
 have range : ∀v : Fin n,mask L v=true → L≤v.val ∧ v.val<2*L+1 := by simp [mask]
 have ready : Ready HeapPath.pred q (mask L) (fun _=>false) := by
   refine ⟨h.1,?_,?_,heap_layer_independent L (mask L) range,?_⟩
   · intro v hv; rw [h.2]; have hh := range v hv; simp; omega
   · intro v hv u hu
     have hh := range v hv
     simp [HeapPath.pred] at hu
     rw [h.2]; simp; omega
   · simp
 refine ⟨ready,evolve_consistent q _ h.1,?_⟩
 intro v
 by_cases h1 : L≤v.val
 · by_cases h2 : 2*L+1≤v.val
   · simp [evolve,h.2,mask,h1,h2]
   · have h3 : v.val<2*L+1 := by omega
     simp [evolve,h.2,mask,h1,h2,h3]
 · have h2 : ¬2*L+1≤v.val := by omega
   simp [evolve,h.2,mask,h1,h2]

def layers (n : Nat) : Nat → List (Layer n)
 | 0 => []
 | H+1 => ⟨mask (2^H-1),fun _=>false⟩::layers n H

theorem layer_length (n H : Nat) : (layers n H).length=H := by
 induction H with
 | zero => rfl
 | succ H ih => simp [layers,ih]

theorem fill_correct (H : Nat) (q : Config n) (h : Saturated q (2^H-1)) :
 Admissible HeapPath.pred q (layers n H) ∧ Saturated (execute q (layers n H)).state 0 := by
 induction H generalizing q with
 | zero => simpa [layers,execute,Admissible] using h
 | succ H ih =>
   have he : 2^(H+1)-1=2*(2^H-1)+1 := by
     have hp : 0<2^H := Nat.pow_pos (by decide)
     rw [Nat.pow_succ]; omega
   rw [he] at h
   have hl := fill_layer q (2^H-1) h
   have hr := ih _ hl.2
   exact ⟨⟨hl.1,hr.1⟩,hr.2⟩

theorem card_sum (C : Fin n → Bool) : card C=((List.finRange n).map fun v=>if C v then 1 else 0).sum :=
 CutSpace.filter_sum _ _

theorem pebs_evolve (q : Config n) (C : Fin n → Bool)
 (hf : ∀v,C v=true → q.peb v=false) :
 CutSpace.pebs (evolve q C (fun _=>false))=CutSpace.pebs q+card C := by
 rw [card_sum]
 unfold CutSpace.pebs
 rw [←HeapPath.sum_add]
 congr 1
 apply List.map_congr_left
 intro v hv
 have hh := hf v
 cases hp : q.peb v <;> cases hc : C v <;> simp_all [evolve]

theorem fill_work (H : Nat) (q : Config n) (h : Saturated q (2^H-1)) :
 (execute q (layers n H)).work+CutSpace.pebs q=CutSpace.pebs (execute q (layers n H)).state := by
 induction H generalizing q with
 | zero => simp [layers,execute]
 | succ H ih =>
   have he : 2^(H+1)-1=2*(2^H-1)+1 := by
     have hp : 0<2^H := Nat.pow_pos (by decide)
     rw [Nat.pow_succ]; omega
   rw [he] at h
   have hl := fill_layer q (2^H-1) h
   have hr := ih _ hl.2
   have hp := pebs_evolve q (mask (2^H-1)) hl.1.fresh
   simp only [layers,execute,SpookyDP.prepend]
   omega

theorem pebs_full (q : Config n) (h : Saturated q 0) : CutSpace.pebs q=n := by
 unfold CutSpace.pebs
 have he : (fun v : Fin n => if q.peb v then 1 else 0)=(fun _=>1) := by
   funext v; simp [h.2]
 rw [he]; simp [List.map_const',List.sum_replicate_nat]

theorem fill_space (q : Config n) (H : Nat) : (execute q (layers n H)).space≤n := by
 apply execute_space
 intro pre a post he
 unfold card
 exact Nat.le_trans (List.length_filter_le _ _) (by simp)

theorem full_storage_fill (H : Nat) (q : Config (2^H-1))
 (hc : consistent q) (hp : ∀v,q.peb v=false) :
 ∃r,PaperRuns HeapPath.pred H q r ∧ (∀v,r.state.peb v=true ∧ r.state.ghost v=false) ∧
 r.work=2^H-1 ∧ r.space≤2^H-1 := by
 have hs : Saturated q (2^H-1) := by
   refine ⟨hc,?_⟩; intro v; rw [hp]; simp [show ¬2^H-1≤v.val by omega]
 have hh := fill_correct H q hs
 refine ⟨execute q (layers (2^H-1) H),?_,?_,?_,fill_space q H⟩
 · simpa [layer_length] using execute_runs hh.1
 · intro v
   have hpp : (execute q (layers (2^H-1) H)).state.peb v=true := by simpa using hh.2.2 v
   refine ⟨hpp,?_⟩
   have hc := hh.2.1 v
   cases hg : (execute q (layers (2^H-1) H)).state.ghost v <;> simp_all
 · have hw := fill_work H q hs
   rw [pebs_full _ hh.2] at hw
   have hz : CutSpace.pebs q=0 := by simp [CutSpace.pebs,hp,List.map_const',List.sum_replicate_nat]
   omega
theorem evolve_noGhost (q : Config n) (C G : Fin n → Bool)
 (hq : ∀v,q.ghost v=false) (hg : ∀v,G v=false) :
 ∀v,(evolve q C G).ghost v=false := by intro v; simp [evolve,hq,hg]

theorem reverse_execute {pred : Fin n → Fin n → Bool}
 (hi : ∀v,pred v v=false) (as : List (Layer n)) (q : Config n)
 (hq : ∀v,q.ghost v=false) (hg : ∀a∈as,∀v,a.ghost v=false)
 (ha : Admissible pred q as) :
 PaperRuns pred as.length (execute q as).state
   ⟨q,(execute q as).work,(execute q as).space⟩ := by
 induction as generalizing q with
 | nil => exact PaperRuns.zero q
 | cons a as ih =>
   have hag := hg a (by simp)
   have htail := ih (evolve q a.compute a.ghost) (evolve_noGhost q _ _ hq hag)
     (fun b hb=>hg b (by simp [hb])) ha.2
   have hs := SpookyReverse.reverse_step hi (batch_legal ha.1) hq
     (by intro v; simpa using hag v) (by simp [batch]) (by simp [batch])
   rw [after_batch,work_batch,space_batch] at hs
   have one := PaperRuns.step hs (PaperRuns.zero q)
   have hh := runs_append htail one
   simpa [execute,SpookyDP.prepend,Nat.add_comm,Nat.max_comm] using hh

theorem layers_noGhost (n H : Nat) : ∀a∈layers n H,∀v,a.ghost v=false := by
 induction H with
 | zero => simp [layers]
 | succ H ih => intro a ha; simp only [layers,List.mem_cons] at ha; rcases ha with rfl|ha
                · simp
                · exact ih a ha

def empty (n : Nat) : Config n := ⟨fun _=>false,fun _=>false⟩

theorem full_storage_cleanup (H : Nat) (q : Config (2^H-1))
 (hc : consistent q) (hp : ∀v,q.peb v=false) :
 ∃r,PaperRuns HeapPath.pred (2*H) q r ∧ r.state=empty (2^H-1) ∧
 r.work=2*(2^H-1) ∧ r.space≤2^H-1 := by
 let n := 2^H-1
 have he : Saturated (empty n) n := by
   refine ⟨?_,?_⟩
   · simp [consistent,empty]
   · intro v; simp [empty,show ¬n≤v.val by omega]
 have hf := fill_correct H (empty n) he
 have hr := reverse_execute (pred:=HeapPath.pred)
   (by intro v; simp [HeapPath.pred]; omega) (layers n H) (empty n)
   (by simp [empty]) (layers_noGhost n H) hf.1
 have hfull := pebs_full _ hf.2
 have hw := fill_work H (empty n) he
 have hz : CutSpace.pebs (empty n)=0 := by simp [CutSpace.pebs,empty,List.map_const',List.sum_replicate_nat]
 rw [hz,Nat.add_zero,hfull] at hw
 obtain ⟨r,hpr,hpq,hwq,hsq⟩ := full_storage_fill H q hc hp
 have heq : (execute (empty n) (layers n H)).state=r.state := by
   apply SpookyReverse.config_ext
   · intro v; rw [(hpq v).1]; simpa using hf.2.2 v
   · intro v
     have hc := hf.2.1 v
     have hp : (execute (empty n) (layers n H)).state.peb v=true := by simpa using hf.2.2 v
     rw [(hpq v).2]
     cases hg : (execute (empty n) (layers n H)).state.ghost v <;> simp_all
 rw [heq,layer_length] at hr
 have hall := runs_append hpr hr
 refine ⟨⟨empty n,r.work+(execute (empty n) (layers n H)).work,max r.space (execute (empty n) (layers n H)).space⟩,?_,rfl,?_,?_⟩
 · simpa [Nat.two_mul] using hall
 · simp [hw,hwq,n,Nat.two_mul]
 · exact Nat.max_le.mpr ⟨hsq,fill_space _ _⟩
#print axioms full_storage_cleanup
#print axioms full_storage_fill
end FillUpper
