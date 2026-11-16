import LabelledCount
import SwapGraphBasics
namespace RawSwapGraph
open LocalCertificate ChainTrace ChainOccurrence ChainWholeBijection ChainLabelledCount

def Edge {α : Type} (u v : List α) : Prop := ∃pre a b post,u=pre++a::b::post ∧ v=pre++b::a::post
inductive Reach {α : Type} (L : List α→Prop) (root : List α) : List α→Prop
 | refl : L root → Reach L root root
 | step {u v} : Reach L root u → Edge u v → L v → Reach L root v

theorem map_edge {α β : Type} (f : α→β) {u v : List α} (h : Edge u v) : Edge (u.map f) (v.map f) := by
 obtain ⟨p,a,b,s,rfl,rfl⟩ := h
 exact ⟨p.map f,f a,f b,s.map f,by simp,by simp⟩

def eventAt (table : List Event) (i : Nat) : Event := table[i]?.getD ⟨false,0⟩
theorem decode_map {table ids raw} (h : decodeTrace table ids=some raw) : ids.map (eventAt table)=raw := by
 induction ids generalizing raw with
 | nil => simpa [decodeTrace] using h
 | cons i ids ih =>
  cases hi : table[i]? with
  | none => simp [decodeTrace,hi] at h
  | some a =>
   cases hd : decodeTrace table ids with
   | none => simp [decodeTrace,hi,hd] at h
   | some tail =>
    have eq : a::tail=raw := by simpa [decodeTrace,hi,hd] using h
    rw [←eq]
    simp only [List.map_cons,eventAt,hi,Option.getD_some]
    exact congrArg (List.cons a) (ih hd)

theorem decode_neighbor {table u v ru rv}
 (hu : decodeTrace table u=some ru) (hv : decodeTrace table v=some rv)
 (hn : v∈SwapComponents.neighbors u) : Edge ru rv := by
 rw [←decode_map hu,←decode_map hv]
 exact map_edge (eventAt table) (SwapGraphBasics.neighbor_shape hn)

theorem labelled_path_to_raw {r E u v}
 (h : SwapComponents.Reach (labelledLegal r E) u v) :
 ∀ru rv,decodeTrace (ChainAssembledTrace.fullTable r) u=some ru →
 decodeTrace (ChainAssembledTrace.fullTable r) v=some rv → Reach (FamilyCut.Trace (r+1) E) ru rv := by
 induction h with
 | refl legal =>
  intro ru rv du dv
  have eq : ru=rv := Option.some.inj (du.symm.trans dv)
  subst rv
  obtain ⟨raw,dec,tr⟩ := legal.2.2
  have eq : raw=ru := Option.some.inj (dec.symm.trans du)
  subst raw
  exact Reach.refl tr
 | @step u v path edge legal ih =>
  intro ru rv du dv
  obtain ⟨mid,dm,tm⟩ := (SwapGraphBasics.reach_legal path).2.2
  obtain ⟨out,dout,tout⟩ := legal.2.2
  have eq : out=rv := Option.some.inj (dout.symm.trans dv)
  subst out
  exact Reach.step (ih ru mid du dm) (decode_neighbor dm dv edge) tout

#print axioms labelled_path_to_raw
end RawSwapGraph
