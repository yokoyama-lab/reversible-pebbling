import SkeletonUnfill
namespace Sandwich
open SpookyRound FillUpper RetainRoot TraceBridge

def budget (H : Nat) : Nat := (6*2^H+H-1)/H

theorem ceil_bounds (a H : Nat) (hH : 0<H) :
 a≤H*((a+H-1)/H) ∧ H*((a+H-1)/H)≤a+H-1 := by
 have hd := Nat.mod_add_div (a+H-1) H
 have hm := Nat.mod_lt (a+H-1) hH
 have hu := Nat.mul_div_le (a+H-1) H
 constructor <;> omega

theorem budget_pos (H : Nat) (hH : 0<H) : 0<budget H := by
 have hp : 0<2^H := Nat.pow_pos (by decide)
 have hb := (ceil_bounds (6*2^H) H hH).1
 by_cases hz : budget H=0
 · change 6*2^H≤H*budget H at hb
   rw [hz,Nat.mul_zero] at hb; omega
 · omega

theorem budget_cost (H : Nat) (hH : 3≤H) : H*budget H≤8*(2^H-1) := by
 have hb := (ceil_bounds (6*2^H) H (by omega)).2
 have hh : H≤2^H := Nat.le_trans (Nat.le_mul_of_pos_left H (by decide : 0<2)) (SkeletonUnfill.twice_le_pow H (by omega))
 have hp := Nat.pow_le_pow_right (n:=2) (by decide) hH
 change H*budget H≤_ at hb
 omega

theorem budget_at_most_n (H : Nat) (hH : 7≤H) : budget H≤2^H-1 := by
 have hh : H≤2^H := Nat.le_trans (Nat.le_mul_of_pos_left H (by decide : 0<2)) (SkeletonUnfill.twice_le_pow H (by omega))
 have hm := Nat.mul_le_mul_right (2^H) hH
 have hp : 0<2^H := Nat.pow_pos (by decide)
 have eq : (2^H-1)*H+H=H*2^H := by
   calc
    _=H*((2^H-1)+1) := by rw [Nat.mul_add,Nat.mul_one,Nat.mul_comm (2^H-1) H]
    _=H*2^H := by congr 1; omega
 apply (Nat.div_le_iff_le_mul (by omega : 0<H)).mpr
 change 6*2^H+H-1≤(2^H-1)*H+H-1
 omega

theorem achievable (H : Nat) (hH : 2≤H) :
 ∃d t,PaperRuns HeapPath.pred d (empty (2^H-1)) t ∧ t.state=rootOnly (2^H-1) ∧
 t.work≤3*(2^H-1) ∧ d≤3*H*H.log2+2*H ∧ t.space≤budget H := by
 obtain ⟨d,t,ht,hs,hw,hd,hsp⟩ := SkeletonUnfill.height_upper H hH
 have hb := (ceil_bounds (6*2^H) H (by omega)).1
 exact ⟨d,t,ht,hs,hw,hd,Nat.le_of_mul_le_mul_left (Nat.le_trans hsp hb) (by omega)⟩

theorem lower (H d : Nat) (hH : 16384≤H) {t : SpookyDP.Result (Config (2^H-1))}
 (ht : PaperRuns HeapPath.pred d (empty (2^H-1)) t) (hs : t.state=rootOnly (2^H-1))
 (hw : t.work≤3*(2^H-1)) (hsp : t.space≤budget H) : H*H.log2≤16*d := by
 have hp : 0<2^H-1 := by
   have hh := Nat.pow_le_pow_right (n:=2) (by decide) (show 1≤H by omega)
   simp at hh; omega
 apply LogLower.paper_log_lower H 8 7 hp ht (s:=budget H) _ _ _ hw hsp
   (budget_pos H (by omega)) (by decide) (budget_cost H (by omega)) (by decide) (by simpa using hH)
 · intro u; simp [kind,empty]
 · rw [hs]; simp [kind,rootOnly]
 · intro u hu; rw [hs]; simp [kind,rootOnly,show u.val≠0 by omega]

#print axioms achievable
#print axioms lower
#print axioms budget_at_most_n


theorem small_budget_exceeds_n (H : Nat) (hp : 0<H) (hs : H<7) : 2^H-1<budget H := by
 have hh : H=1∨H=2∨H=3∨H=4∨H=5∨H=6 := by omega
 rcases hh with rfl|rfl|rfl|rfl|rfl|rfl <;> decide

theorem budget_range_iff (H : Nat) (hH : 0<H) : budget H≤2^H-1 ↔ 7≤H := by
 constructor
 · intro hb
   by_cases hh : 7≤H
   · exact hh
   · have hs := small_budget_exceeds_n H hH (by omega); omega
 · exact budget_at_most_n H

theorem sandwich (H : Nat) (hH : 16384≤H) :
 0<budget H ∧ budget H≤2^H-1 ∧
 (∃d t,PaperRuns HeapPath.pred d (empty (2^H-1)) t ∧ t.state=rootOnly (2^H-1) ∧
   t.work≤3*(2^H-1) ∧ t.space≤budget H ∧
   H*H.log2≤16*d ∧ d≤3*H*H.log2+2*H) ∧
 (∀d (t : SpookyDP.Result (Config (2^H-1))),
   PaperRuns HeapPath.pred d (empty (2^H-1)) t → t.state=rootOnly (2^H-1) →
   t.work≤3*(2^H-1) → t.space≤budget H → H*H.log2≤16*d) := by
 refine ⟨budget_pos H (by omega),budget_at_most_n H (by omega),?_,?_⟩
 · obtain ⟨d,t,ht,hs,hw,hd,hsp⟩ := achievable H (by omega)
   exact ⟨d,t,ht,hs,hw,hsp,lower H d hH ht hs hw hsp,hd⟩
 · intro d t ht hs hw hsp
   exact lower H d hH ht hs hw hsp
#print axioms sandwich
#print axioms budget_range_iff
end Sandwich
