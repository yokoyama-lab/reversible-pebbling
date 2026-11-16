import PaddingTransport
import EventEncoding
namespace ChainPaddedRelation
open LocalCertificate ErasureCover ChainPaddingTransport

def pad {n : Nat} (d : Nat) (Q : Fin n → Fin n → Prop)
    (a b : Fin (d+n+1)) : Prop :=
  (a.val<d ∧ a.val<b.val) ∨ (a.val<d+n ∧ b.val=d+n) ∨
  ∃ i j : Fin n, a.val=i.val+d ∧ b.val=j.val+d ∧ Q i j

theorem pad_strict {n : Nat} (d : Nat) (Q : Fin n → Fin n → Prop) (hQ : StrictOrder Q) :
    StrictOrder (pad d Q) := by
  constructor
  · intro a h
    rcases h with h | h | ⟨i,j,hi,hj,hij⟩
    · omega
    · omega
    · have he : i=j := Fin.ext (by omega)
      subst j
      exact hQ.1 i hij
  · intro a b c hab hbc
    rcases hab with ⟨ha,hab⟩ | ⟨ha,hb⟩ | ⟨i,j,ha,hb,hij⟩
    · rcases hbc with ⟨hb,hbc⟩ | ⟨hb,hc⟩ | ⟨l,m,hb,hc,hlm⟩
      · exact Or.inl ⟨ha,by omega⟩
      · exact Or.inr (Or.inl ⟨by omega,hc⟩)
      · exact Or.inl ⟨ha,by omega⟩
    · rcases hbc with ⟨hb',hbc⟩ | ⟨hb',hc⟩ | ⟨l,m,hb',hc,hlm⟩
      all_goals have := b.isLt; try {have := l.isLt}; omega
    · rcases hbc with ⟨hb',hbc⟩ | ⟨hb',hc⟩ | ⟨l,m,hb',hc,hlm⟩
      · omega
      · exact Or.inr (Or.inl ⟨by have := i.isLt; omega,hc⟩)
      · have he : j=l := Fin.ext (by omega)
        subst l
        exact Or.inr (Or.inr ⟨i,m,ha,hc,hQ.2 i j m hij hlm⟩)

def liftWord (d n : Nat) (u : List Nat) := List.range d ++ u.map (fun i=>i+d) ++ [d+n]

theorem canonical (d n : Nat) :
    List.range d ++ ((List.range n).map (fun i=>i+d) ++ [d+n]) = List.range (d+n+1) := by
  rw [List.range_succ,List.range_add]
  simp [Nat.add_comm,List.append_assoc]

theorem idx_range (N a : Nat) (ha : a<N) : (List.range N).idxOf a = a := by
  have hm : a ∈ List.range N := List.mem_range.mpr ha
  have ht := List.idxOf_lt_length_of_mem hm
  have hh := ChainEventEncoding.lookup_idxOf (List.range N) a hm
  simpa [List.getElem?_eq_getElem ht] using hh

theorem idx_map_add (u : List Nat) (d a : Nat) :
    (u.map (fun i=>i+d)).idxOf (a+d) = u.idxOf a := by
  induction u with
  | nil => rfl
  | cons b u ih =>
    simp only [List.map_cons,List.idxOf_cons,cond_eq_ite,beq_iff_eq,Nat.add_right_cancel_iff]
    split <;> simp_all

theorem extends_factor {n : Nat} (d : Nat) (Q : Fin n → Fin n → Prop)
    (w : List Nat) (h : Extends (semantics (d+n+1)) (pad d Q) w) :
    ∃ u, isPermutation n u ∧ w=liftWord d n u := by
  let core := (List.range n).map (fun i=>i+d)
  have canon := canonical d n
  have nd : (List.range d ++ (core ++ [d+n])).Nodup := by rw [canon]; exact List.nodup_range
  have hp : w.Perm (List.range d ++ (core ++ [d+n])) := by
    rw [canon]
    exact (EnumerationCorrectness.isPermutation_iff_perm_range _ _).mp h.1
  have first : ∀ a ∈ List.range d, ∀ b ∈ List.range d ++ (core ++ [d+n]),
      (List.range d ++ (core ++ [d+n])).idxOf a < (List.range d ++ (core ++ [d+n])).idxOf b → w.idxOf a < w.idxOf b := by
    intro a ha b hb hab
    have al : a<d := List.mem_range.mp ha
    have bl : b<d+n+1 := by rw [canon] at hb; exact List.mem_range.mp hb
    rw [canon,idx_range _ a (by omega),idx_range _ b bl] at hab
    exact h.2 ⟨a,by omega⟩ ⟨b,bl⟩ (Or.inl ⟨al,hab⟩)
  have last : ∀ b ∈ w, b ≠ d+n → w.idxOf b < w.idxOf (d+n) := by
    intro b hb hne
    have bl := h.1.2.2 b hb
    exact h.2 ⟨b,bl⟩ ⟨d+n,by omega⟩ (Or.inr (Or.inl ⟨(show b < d+n from by omega),rfl⟩))
  obtain ⟨mid,he,hm⟩ := boundary_factor (List.range d) core (d+n) w nd hp first last
  let u := mid.map (fun i=>i-d)
  have up : u.Perm (List.range n) := by
    have hh := hm.map (fun i=>i-d)
    simpa [u,core,List.map_map,Function.comp_def] using hh
  have back : u.map (fun i=>i+d)=mid := by
    rw [List.map_map]
    apply Eq.trans (b := mid.map (fun i=>i))
    · apply List.map_congr_left
      intro i hi
      obtain ⟨j,hj,hji⟩ := List.mem_map.mp (hm.mem_iff.mp hi)
      simp only [Function.comp_apply]
      omega
    · exact List.map_id' _
  exact ⟨u,(EnumerationCorrectness.isPermutation_iff_perm_range _ _).mpr up,by simpa [liftWord,back] using he⟩

#print axioms pad_strict
#print axioms extends_factor
theorem lift_permutation (d n : Nat) (u : List Nat) (hu : isPermutation n u) :
    isPermutation (d+n+1) (liftWord d n u) := by
  apply (EnumerationCorrectness.isPermutation_iff_perm_range _ _).mpr
  have hp := ((EnumerationCorrectness.isPermutation_iff_perm_range _ _).mp hu).map (fun i=>i+d)
  have hh := (hp.append_left (List.range d)).append_right [d+n]
  simpa [liftWord,← canonical d n,List.append_assoc] using hh

theorem idx_lift_prefix (d n : Nat) (u : List Nat) (a : Nat) (ha : a<d) :
    (liftWord d n u).idxOf a = a := by
  simp [liftWord,List.append_assoc,List.idxOf_append,List.mem_range.mpr ha,idx_range d a ha]

theorem idx_lift_local (d n : Nat) (u : List Nat) (a : Nat)
    (ha : a ∈ u) : (liftWord d n u).idxOf (a+d) = u.idxOf a+d := by
  have hn : a+d ∉ List.range d := by simp <;> omega
  have hm : a+d ∈ u.map (fun i=>i+d) := List.mem_map.mpr ⟨a,ha,rfl⟩
  simp [liftWord,List.append_assoc,List.idxOf_append,hn,hm,idx_map_add]

theorem idx_lift_last (d n : Nat) (u : List Nat) (hu : isPermutation n u) :
    (liftWord d n u).idxOf (d+n) = d+n := by
  have hn : d+n ∉ List.range d := by simp <;> omega
  have hm : d+n ∉ u.map (fun i=>i+d) := by
    intro hmem
    obtain ⟨a,ha,he⟩ := List.mem_map.mp hmem
    have h := hu.2.2 a ha
    omega
  simp [liftWord,List.append_assoc,List.idxOf_append,hn,hm,hu.1]
  omega

theorem lift_extends_iff {n : Nat} (d : Nat) (Q : Fin n → Fin n → Prop)
    (u : List Nat) (hu : isPermutation n u) :
    Extends (semantics (d+n+1)) (pad d Q) (liftWord d n u) ↔ Extends (semantics n) Q u := by
  have memu : ∀ a : Fin n, a.val ∈ u := fun a =>
    ((EnumerationCorrectness.isPermutation_iff_perm_range _ _).mp hu).mem_iff.mpr (List.mem_range.mpr a.isLt)
  constructor
  · intro h
    refine ⟨hu,?_⟩
    intro a b hab
    have hh := h.2 ⟨a.val+d,by omega⟩ ⟨b.val+d,by omega⟩ (Or.inr (Or.inr ⟨a,b,rfl,rfl,hab⟩))
    change (liftWord d n u).idxOf (a.val+d) < (liftWord d n u).idxOf (b.val+d) at hh
    rw [idx_lift_local d n u a.val (memu a),idx_lift_local d n u b.val (memu b)] at hh
    exact Nat.lt_of_add_lt_add_right hh
  · intro h
    refine ⟨lift_permutation d n u hu,?_⟩
    intro a b hab
    change (liftWord d n u).idxOf a.val < (liftWord d n u).idxOf b.val
    have localIndex (x : Nat) (lo : d≤x) (hi : x<d+n) :
        (liftWord d n u).idxOf x = u.idxOf (x-d)+d := by
      have hx : x-d<n := by omega
      have hh := idx_lift_local d n u (x-d) (memu ⟨x-d,hx⟩)
      simpa [Nat.sub_add_cancel lo] using hh
    rcases hab with ⟨ha,hab⟩ | ⟨ha,hb⟩ | ⟨i,j,ha,hb,hij⟩
    · rw [idx_lift_prefix d n u a.val ha]
      by_cases hb : b.val<d
      · rw [idx_lift_prefix d n u b.val hb]
        exact hab
      · by_cases bl : b.val<d+n
        · rw [localIndex b.val (by omega) bl]
          omega
        · have be : b.val=d+n := by have := b.isLt; omega
          rw [be,idx_lift_last d n u hu]
          omega
    · rw [hb,idx_lift_last d n u hu]
      by_cases al : a.val<d
      · rw [idx_lift_prefix d n u a.val al]
        omega
      · rw [localIndex a.val (by omega) ha]
        have hl := List.idxOf_lt_length_of_mem (memu ⟨a.val-d,by omega⟩)
        change u.idxOf (a.val-d) < u.length at hl
        rw [hu.1] at hl
        omega
    · rw [ha,hb,idx_lift_local d n u i.val (memu i),idx_lift_local d n u j.val (memu j)]
      exact Nat.add_lt_add_right (h.2 i j hij) d

theorem extends_iff_factor {n : Nat} (d : Nat) (Q : Fin n → Fin n → Prop) (w : List Nat) :
    Extends (semantics (d+n+1)) (pad d Q) w ↔
      ∃ u, Extends (semantics n) Q u ∧ w=liftWord d n u := by
  constructor
  · intro h
    obtain ⟨u,hu,he⟩ := extends_factor d Q w h
    exact ⟨u,(lift_extends_iff d Q u hu).mp (he ▸ h),he⟩
  · rintro ⟨u,hu,he⟩
    rw [he]
    exact (lift_extends_iff d Q u hu.1).mpr hu

#print axioms lift_permutation
#print axioms lift_extends_iff
#print axioms extends_iff_factor
theorem padded_sound {n : Nat} (d : Nat) (Q : Fin n → Fin n → Prop)
    (localLegal fullLegal : List Nat → Prop)
    (hs : Sound (semantics n) localLegal Q)
    (build : ∀ u, localLegal u → fullLegal (liftWord d n u)) :
    Sound (semantics (d+n+1)) fullLegal (pad d Q) := by
  intro w hw
  obtain ⟨u,hu,he⟩ := (extends_iff_factor d Q w).mp hw
  rw [he]
  exact build u (hs u hu)

theorem initial_padded_sound (Q : Fin 10 → Fin 10 → Prop)
    (hs : Sound (semantics 10) I.Legal Q) :
    Sound (semantics 17) (legal ChainInitialSegment.events [] ChainInitialSegment.final [5]) (pad 6 Q) := by
  exact padded_sound 6 Q I.Legal (legal ChainInitialSegment.events [] ChainInitialSegment.final [5]) hs
    (fun u hu => ChainInitialConverse.local_legal_lifts u hu)

theorem middle_padded_sound (Q : Fin 12 → Fin 12 → Prop)
    (hs : Sound (semantics 12) M.Legal Q) :
    Sound (semantics 16) (legal ChainMiddleSegment.events ChainMiddleSegment.initial
      ChainMiddleSegment.final [5,11]) (pad 3 Q) := by
  exact padded_sound 3 Q M.Legal (legal ChainMiddleSegment.events ChainMiddleSegment.initial
    ChainMiddleSegment.final [5,11]) hs (fun u hu => ChainMiddleConverse.local_legal_lifts u hu)

#print axioms padded_sound
#print axioms initial_padded_sound
#print axioms middle_padded_sound
end ChainPaddedRelation
