import LowerProjection
import UpperProjectionBounds
import VisitMeasure
namespace LowCapacityProjection
open LocalCertificate TerminalProjection VisitMeasure LowerProjection
/-- Only after-move boards: Run.nil has no initial-capacity obligation. -/
def Safe (q m : Nat) (b : List Nat) (es : List Event) : Prop :=
 ∀a∈frames b es,(low m a).length≤q

theorem step_low_capacity {p q m b a e} (h : Step p b e a)
 (hv : e.vertex≤m) (cap : (low m a).length≤q) :
 Step q (low m b) e (low m a) := by
 have hl := step_low h hv
 exact ⟨hl.1,cap,hl.2.2⟩

theorem run_low_safe {p q m b es z c r} (h : Run p b es z c r)
 (safe : Safe q m b es) :
 ∃d s,Run q (low m b) (moves m es) (low m z) d s ∧ d≤c ∧ s≤r := by
 induction h with
 | nil b => exact ⟨0,0,by simpa [moves] using Run.nil (p:=q) (low m b),by omega,by omega⟩
 | @cons b a z es c r e hs hr ih =>
  have cap : (low m a).length≤q := safe a (by simp [frames,step_update hs])
  have st : Safe q m a es := by
   intro v hv;apply safe v; simp only [frames,step_update hs,List.mem_cons];exact Or.inr hv
  obtain ⟨d,s,ht,hc,he⟩ := ih st
  by_cases hv : e.vertex≤m
  · refine ⟨fee b e+d,erasure b e+s,?_,by omega,by omega⟩
    simpa [moves,hv,fee_low hv,erasure_low hv] using Run.cons (step_low_capacity hs hv cap) ht
  · have ha := upper_step_disappears hs (by omega : m<e.vertex)
    refine ⟨d,s,?_,by omega,by omega⟩
    simpa [moves,hv,ha] using ht

theorem low_capacity {m p b} (cap : b.length≤p) (occupied : ∃x∈b,m<x) :
 (low m b).length≤p-1 := by
 obtain ⟨x,hx,hxm⟩ := occupied
 have hh : x∈UpperProjectionBounds.high m b := by simp [UpperProjectionBounds.high,hx,hxm]
 have pos := List.length_pos_of_mem hh
 have eq := UpperProjectionBounds.partition_length m b
 change (low m b).length+(UpperProjectionBounds.high m b).length=b.length at eq
 omega

theorem frames_capacity {p b es z c r} (h : Run p b es z c r) :
 ∀a∈frames b es,a.length≤p := by
 induction h with
 | nil => simp [frames]
 | @cons b a z es c r e hs hr ih =>
  intro v hv
  simp only [frames,step_update hs,List.mem_cons] at hv
  rcases hv with rfl | hv
  · exact hs.2.1
  · exact ih v hv

theorem occupied_safe {p m b es z c r} (h : Run p b es z c r)
 (occupied : ∀a∈frames b es,∃x∈a,m<x) : Safe (p-1) m b es := by
 intro a ha
 exact low_capacity (frames_capacity h a ha) (occupied a ha)

theorem run_low_upper_occupied {p m b es z c r} (h : Run p b es z c r)
 (occupied : ∀a∈frames b es,∃x∈a,m<x) :
 ∃d s,Run (p-1) (low m b) (moves m es) (low m z) d s ∧ d≤c ∧ s≤r :=
 run_low_safe h (occupied_safe h occupied)

theorem run_low_empty_end {p m b es z c r} (h : Run p b es z c r)
 (occupied : ∀a∈frames b es,∃x∈a,m<x)
 (endHigh : ∀x∈z,m<x) :
 ∃d s,Run (p-1) (low m b) (moves m es) [] d s ∧ d≤c ∧ s≤r := by
 have hz : low m z=[] := by
  apply List.filter_eq_nil_iff.mpr
  intro x hx
  have hh := endHigh x hx
  simp only [decide_eq_true_eq]
  omega
 simpa only [hz] using run_low_upper_occupied h occupied

theorem low_singleton {m Q} (nd : Q.Nodup) (member : m∈Q)
 (only : ∀v∈Q,v≤m → v=m) : low m Q=[m] := by
 have nd' : (low m Q).Nodup := nd.filter _
 have mem : m∈low m Q := mem_low.mpr ⟨member,Nat.le_refl _⟩
 have all : ∀v∈low m Q,v=m := by
  intro v hv
  obtain ⟨hv,hvm⟩ := mem_low.mp hv
  exact only v hv hvm
 cases he : low m Q with
 | nil => simp [he] at mem
 | cons a tail =>
  have ha : a=m := all a (by simp [he])
  cases tail with
  | nil => simp [ha]
  | cons b rest =>
   have hb : b=m := all b (by simp [he])
   have hn : a∉b::rest := (List.nodup_cons.mp (he ▸ nd')).1
   exact False.elim (hn (by simp [ha,hb]))

#print axioms low_singleton

#print axioms step_low_capacity
#print axioms run_low_safe
#print axioms low_capacity
#print axioms frames_capacity
#print axioms occupied_safe
#print axioms run_low_upper_occupied
#print axioms run_low_empty_end
end LowCapacityProjection
