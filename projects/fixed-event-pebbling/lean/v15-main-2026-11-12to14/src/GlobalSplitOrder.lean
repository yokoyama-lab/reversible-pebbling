import GlobalSplitCount
namespace GlobalSplit
open LocalCertificate FamilyCut

def index (e : Event) : Nat := (e.vertex-11)/6

theorem filtered_order (p : Event → Bool) (f : Event → Nat) (word : List Event)
    (hb : ∀ pre e post, word=pre++e::post → p e=true →
      ∀ x∈pre, p x=true → f x < f e) :
    ((word.filter p).map f).Pairwise (· < ·) := by
  induction word with
  | nil => simp
  | cons a rest ih =>
    have ht : ((rest.filter p).map f).Pairwise (· < ·) := by
      apply ih
      intro pre e post he hp x hx hpx
      exact hb (a::pre) e post (by simp [he]) hp x (by simp [hx]) hpx
    cases ha : p a with
    | false => simpa [ha] using ht
    | true =>
      simp only [List.filter_cons,ha,ite_true,List.map_cons,List.pairwise_cons]
      refine ⟨?_,ht⟩
      intro z hz
      obtain ⟨e,he,rfl⟩ := List.mem_map.mp hz
      obtain ⟨her,hpe⟩ := List.mem_filter.mp he
      obtain ⟨pre,post,hs⟩ := List.mem_iff_append.mp her
      exact hb (a::pre) e post (by simp [hs]) hpe a (by simp) ha

theorem sorted_interval (xs : List Nat) (lo n : Nat)
    (hp : xs.Pairwise (· < ·))
    (hm : ∀ v, v∈xs ↔ lo≤v ∧ v<lo+n) :
    xs=List.range' lo n := by
  induction n generalizing xs lo with
  | zero =>
    have he : xs=[] := by
      cases xs with
      | nil => rfl
      | cons a rest =>
        have := (hm a).mp (by simp)
        omega
    simp [he]
  | succ n ih =>
    cases xs with
    | nil =>
      have := (hm lo).mpr (by omega)
      simp at this
    | cons a rest =>
      have ha := (hm a).mp (by simp)
      have hlo := (hm lo).mpr (by omega)
      have pr := List.pairwise_cons.mp hp
      have eq : a=lo := by
        rcases List.mem_cons.mp hlo with h | h
        · omega
        · have := pr.1 lo h; omega
      subst a
      have hr : ∀ v, v∈rest ↔ lo+1≤v ∧ v<lo+1+n := by
        intro v
        constructor
        · intro hv
          have := (hm v).mp (List.mem_cons_of_mem lo hv)
          have := pr.1 v hv
          omega
        · intro hv
          have h := (hm v).mpr (by omega)
          rcases List.mem_cons.mp h with h | h
          · omega
          · exact h
      have hrest := ih rest (lo+1) pr.2 hr
      simpa [List.range',hrest]

theorem trace_marker_order (k : Nat) (erasures : List Nat) (word : List Event)
    (model : Trace k erasures word) :
    ((word.filter marker).map index).Pairwise (· < ·) := by
  apply filtered_order
  intro pre e post hw hp x hx hpx
  have ew : e∈word := by rw [hw]; simp
  obtain ⟨j,hj,hep,hev⟩ := (marker_trace_iff k erasures word model e ew).mp hp
  have m : Trace k erasures (pre++e::post) := by rw [← hw]; exact model
  have sg := all_block_cut_signature k j (5+6*j) erasures pre post e hj rfl hep (by omega) m
  have bound := sg.2.2.1 x hx
  have xw : x∈word := by rw [hw]; exact List.mem_append_left _ hx
  obtain ⟨i,hi,hxp,hxv⟩ := (marker_trace_iff k erasures word model x xw).mp hpx
  unfold index
  omega

theorem trace_marker_range (k : Nat) (erasures : List Nat) (word : List Event)
    (model : Trace k erasures word) :
    (word.filter marker).map index = List.range k := by
  have h := sorted_interval ((word.filter marker).map index) 0 k (trace_marker_order k erasures word model)
  have hm : ∀ v, v∈(word.filter marker).map index ↔ 0≤v ∧ v<0+k := by
    intro v
    constructor
    · intro hv
      obtain ⟨e,he,hv⟩ := List.mem_map.mp hv
      obtain ⟨hew,hep⟩ := List.mem_filter.mp he
      obtain ⟨j,hj,hp,hjv⟩ := (marker_trace_iff k erasures word model e hew).mp hep
      unfold index at hv
      constructor <;> omega
    · intro hv
      have hc := each_cut_count k v erasures word model (by omega)
      have pos : 0<word.countP (P (11+6*v)) := by omega
      obtain ⟨e,he,hp⟩ := List.countP_pos_iff.mp pos
      have hh : e.place=true ∧ e.vertex=11+6*v := by simpa [P,RemovalOrder.isPlacement] using hp
      apply List.mem_map.mpr
      refine ⟨e,List.mem_filter.mpr ⟨he,?_⟩,?_⟩
      · exact (marker_trace_iff k erasures word model e he).mpr ⟨v,by omega,hh.1,hh.2⟩
      · unfold index; omega
  simpa only [List.range_eq_range'] using h hm

def endpointIndex (b : List Event) := index (b.getLastD ⟨false,0⟩)

theorem block_filter (b : List Event) (hb : Block marker b) :
    (b.filter marker).map index = [endpointIndex b] := by
  obtain ⟨pre,e,rfl,hp,hn⟩ := hb
  have hz : pre.filter marker=[] := List.filter_eq_nil_iff.mpr (by intro x hx; simp [hn x hx])
  simp [hz,hp,endpointIndex,List.getLastD_concat]

theorem trace_block_indices (k : Nat) (erasures : List Nat) (word : List Event)
    (model : Trace k erasures word) :
    (splitMarkers marker word).1.map endpointIndex = List.range k := by
  obtain ⟨hf,hb,ht⟩ := split_spec marker word
  have hz : (splitMarkers marker word).2.filter marker=[] := List.filter_eq_nil_iff.mpr (by intro x hx; simp [ht x hx])
  have blocks_eq (bs : List (List Event)) (hb : ∀ b∈bs, Block marker b) :
      (bs.flatten.filter marker).map index = bs.map endpointIndex := by
    induction bs with
    | nil => simp
    | cons b bs ih =>
      have h1 := block_filter b (hb b (by simp))
      have h2 := ih (fun c hc => hb c (by simp [hc]))
      simpa only [List.flatten_cons,List.filter_append,List.map_append,List.map_cons,h1,h2,List.singleton_append]
  have eq : (word.filter marker).map index = (splitMarkers marker word).1.map endpointIndex := by
    calc
      (word.filter marker).map index =
        (((splitMarkers marker word).1.flatten ++ (splitMarkers marker word).2).filter marker).map index :=
          congrArg (fun xs => (xs.filter marker).map index) hf.symm
      _ = _ := by simp only [List.filter_append,hz,List.append_nil]; exact blocks_eq _ hb
  exact eq.symm.trans (trace_marker_range k erasures word model)

#print axioms filtered_order
#print axioms sorted_interval
#print axioms trace_marker_order
#print axioms trace_marker_range
#print axioms block_filter
#print axioms trace_block_indices
end GlobalSplit
