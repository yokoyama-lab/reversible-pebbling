import UpperProjectionBounds
namespace UpperProjectionRun
open LocalCertificate TerminalProjection UpperProjectionBounds
def board (m : Nat) (b : List Nat) := (high m b).map (fun v=>v-m)
def event (m : Nat) (e : Event) : Event := ⟨e.place,e.vertex-m⟩
def word (m : Nat) (es : List Event) := (es.filter (fun e=>decide (m<e.vertex))).map (event m)
theorem board_mem {m b v} (hv : m<v) : v-m∈board m b ↔ v∈b := by
 simp only [board,List.mem_map,high,List.mem_filter,decide_eq_true_eq]
 constructor
 · rintro ⟨x,⟨hx,hm⟩,he⟩
   have heq : x=v := by omega
   simpa [heq] using hx
 · intro h;exact ⟨v,⟨h,hv⟩,rfl⟩
theorem board_cons (m v : Nat) (b : List Nat) :
 board m (v::b)=if m<v then (v-m)::board m b else board m b := by
 by_cases h : m<v <;> simp [board,high,h]
theorem board_erase_high {m v} (b : List Nat) (hv : m<v) :
 board m (b.erase v)=(board m b).erase (v-m) := by
 induction b with
 | nil => simp [board,high]
 | cons x xs ih =>
  by_cases he : x=v
  · subst x;simp [board_cons,hv]
  · have hbe : (x==v)=false := by simp [he]
    by_cases hx : m<x
    · have hne : x-m≠v-m := by omega
      simp [List.erase_cons,hbe,board_cons,hx,ih,hne]
    · simp [List.erase_cons,hbe,board_cons,hx,ih]
theorem board_erase_low {m v} (b : List Nat) (hv : v≤m) : board m (b.erase v)=board m b := by
 induction b with
 | nil => simp [board,high]
 | cons x xs ih =>
  by_cases he : x=v
  · subst x;simp [board_cons,show ¬m<v by omega]
  · have hbe : (x==v)=false := by simp [he]
    simp only [List.erase_cons,hbe,Bool.false_eq_true,↓reduceIte]
    rw [board_cons,board_cons,ih]
theorem pred_shift {m b v} (hv : m<v) : pred (board m b) (v-m) ↔ upperPred m b v := by
 by_cases h : v=m+1
 · subst v;simp [pred,upperPred]
 · have hpred : m<v-1 := by omega
   have eq : v-m-1=(v-1)-m := by omega
   have hn : v-m≠1 := by omega
   simp [pred,upperPred,h,hn,eq,board_mem hpred,high,hpred]
theorem fee_shift {m b e} (hv : m<e.vertex) : fee (board m b) (event m e)=projectedFee m b e := by
 simp [fee,event,projectedFee,pred_shift hv]
theorem erasure_shift {m b e} (hv : m<e.vertex) : erasure (board m b) (event m e)=projectedErasure m b e := by
 simp [erasure,event,projectedErasure,pred_shift hv]
theorem high_step {p q m b a e} (hs : Step p b e a) (hv : m<e.vertex)
 (hc : (high m a).length≤q) : Step q (board m b) (event m e) (board m a) := by
 refine ⟨by simp [event];omega,by simpa [board] using hc,?_⟩
 cases hp : e.place with
 | true =>
  have he : e.vertex∉b ∧ pred b e.vertex ∧ a=e.vertex::b := by simpa [hp] using hs.2.2
  simp only [event,hp,↓reduceIte]
  refine ⟨fun hm => he.1 ((board_mem hv).mp hm),(pred_shift hv).mpr (predecessor_retained hv he.2.1),?_⟩
  rw [he.2.2,board_cons,if_pos hv]
 | false =>
  have he : e.vertex∈b ∧ a=b.erase e.vertex := by simpa [hp] using hs.2.2
  simp only [event,hp,Bool.false_eq_true,↓reduceIte]
  exact ⟨(board_mem hv).mpr he.1,by rw [he.2,board_erase_high _ hv]⟩
theorem low_step_disappears {p m b a e} (hs : Step p b e a) (hv : e.vertex≤m) : board m a=board m b := by
 cases hp : e.place with
 | true =>
  have he : e.vertex∉b ∧ pred b e.vertex ∧ a=e.vertex::b := by simpa [hp] using hs.2.2
  rw [he.2.2,board_cons,if_neg (by omega)]
 | false =>
  have he : e.vertex∈b ∧ a=b.erase e.vertex := by simpa [hp] using hs.2.2
  rw [he.2,board_erase_low _ hv]
def Safe (p q m : Nat) (initial : List Nat) (es : List Event) : Prop :=
 ∀pre e post b a cp rp,es=pre++e::post → Run p initial pre b cp rp → Step p b e a → (high m a).length≤q
theorem project_run {p b es z c r} (h : Run p b es z c r) (m q : Nat) (safe : Safe p q m b es) :
 ∃c' r',Run q (board m b) (word m es) (board m z) c' r' ∧ c'≤c ∧ r'≤r := by
 induction h with
 | nil b => exact ⟨0,0,by simpa [word] using Run.nil (p:=q) (board m b),by omega,by omega⟩
 | @cons b a z es c r e hs ht ih =>
  have hcap := safe [] e es b a 0 0 rfl (Run.nil b) hs
  have safetail : Safe p q m a es := by
   intro pre f post x y cp rp hw hpre hstep
   exact safe (e::pre) f post x y _ _ (by simp [hw]) (Run.cons hs hpre) hstep
  obtain ⟨c',r',hr,hc,he⟩ := ih safetail
  by_cases hv : m<e.vertex
  · have hstep := high_step hs hv hcap
    have hf := projected_fee_le (b:=b) hv
    have hre := projected_erasure_le (b:=b) hv
    refine ⟨fee (board m b) (event m e)+c',erasure (board m b) (event m e)+r',?_,?_,?_⟩
    · simpa [word,hv] using Run.cons hstep hr
    · rw [fee_shift hv];omega
    · rw [erasure_shift hv];omega
  · have hb := low_step_disappears hs (by omega : e.vertex≤m)
    exact ⟨c',r',by simpa [word,hv,hb] using hr,by omega,by omega⟩
def LowerOccupied (p m : Nat) (initial : List Nat) (es : List Event) : Prop :=
 ∀pre e post b a cp rp,es=pre++e::post → Run p initial pre b cp rp → Step p b e a → ∃v∈a,v≤m
theorem occupied_safe {p b es} (m : Nat) (occupied : LowerOccupied p m b es) : Safe p (p-1) m b es := by
 intro pre e post x y cp rp hw hp hs
 exact high_capacity hs.2.1 (occupied pre e post x y cp rp hw hp hs)
theorem project_with_lower_occupied {p b es z c r} (h : Run p b es z c r) (m : Nat)
 (occupied : LowerOccupied p m b es) :
 ∃c' r',Run (p-1) (board m b) (word m es) (board m z) c' r' ∧ c'≤c ∧ r'≤r :=
 project_run h m (p-1) (occupied_safe m occupied)
theorem safe_from_occupied_or_small {p m initial es} (hp : 2≤p)
 (condition : ∀pre e post b a cp rp,es=pre++e::post → Run p initial pre b cp rp → Step p b e a →
  (∃v∈a,v≤m) ∨ a.length≤1) : Safe p (p-1) m initial es := by
 intro pre e post b a cp rp hw hr hs
 rcases condition pre e post b a cp rp hw hr hs with occupied|small
 · exact high_capacity hs.2.1 occupied
 · have hlen : (high m a).length≤a.length := List.length_filter_le _ _
   omega
theorem project_endpoint {p n es c r} (h : Run p [] es [n] c r) (m : Nat) (hm : m<n)
 (safe : Safe p (p-1) m [] es) :
 ∃c' r',Run (p-1) [] (word m es) [n-m] c' r' ∧ c'≤c ∧ r'≤r := by
 obtain ⟨c',r',hr,hc,he⟩ := project_run h m (p-1) safe
 exact ⟨c',r',by simpa [board,high,hm] using hr,hc,he⟩
#print axioms safe_from_occupied_or_small
#print axioms project_endpoint
#print axioms project_run
#print axioms project_with_lower_occupied
#print axioms high_step
#print axioms low_step_disappears
end UpperProjectionRun
