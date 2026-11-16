import VerifiedIEdgeCount
import VerifiedMEdgeCount
import TEdgeCount
import EdgeSemantics
import GlobalStateCandidates
namespace ChainGlobalEdgeCandidates
open ChainLocalEdges ChainGlobalStateCandidates

def embedEdge (o : Nat) (e : Edge) : Edge := (embed o e.1,e.2+o)
theorem embedEdge_injective (o : Nat) (a b : Edge) (h : embedEdge o a=embedEdge o b) : a=b := by
  apply Prod.ext
  · exact embed_injective o a.1 b.1 (congrArg Prod.fst h)
  · have hh := congrArg Prod.snd h; simp only [embedEdge] at hh; omega

theorem embedEdge_nodup (o : Nat) (es : List Edge) (h : es.Nodup) :
    (es.map (embedEdge o)).Nodup :=
  h.map (embedEdge o) (fun a b hn he=>hn (embedEdge_injective o a b he))

def paddingEdges (d n : Nat) (es : List Edge) : List Edge :=
  (List.range d).map (fun t=>(List.range t,t)) ++ es.map (embedEdge d) ++ [(List.range (d+n),d+n)]

theorem padding_length (d n : Nat) (es : List Edge) :
    (paddingEdges d n es).length=d+es.length+1 := by simp [paddingEdges,Nat.add_assoc]

theorem edges_label_bound (n : Nat) (words : List (List Nat))
    (hb : ∀w∈words,∀a∈w,a<n) (e : Edge) (he : e∈edges n words) : e.2<n := by
  obtain ⟨w,hw,t,ht,rfl⟩ := (mem_edges_iff n words e).mp he
  have hg : w.getD t 0=w[t] := by simp [List.getD_eq_getElem?_getD,ht]
  change w.getD t 0<n
  rw [hg]
  exact hb w hw w[t] (List.getElem_mem ht)

theorem padding_bounds (d n : Nat) (es : List Edge) (hb : ∀e∈es,e.2<n)
    (e : Edge) (he : e∈paddingEdges d n es) : e.2<d+n+1 := by
  simp only [paddingEdges,List.mem_append,List.mem_singleton] at he
  rcases he with (h|h)|h
  · obtain ⟨t,ht,rfl⟩ := List.mem_map.mp h; have := List.mem_range.mp ht; simp; omega
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp h; have := hb a ha; simp [embedEdge]; omega
  · subst e; simp

theorem padding_nodup (d n : Nat) (es : List Edge) (hn : es.Nodup)
    (hb : ∀e∈es,e.2<n) : (paddingEdges d n es).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨?_,by simp,?_⟩
  · apply List.nodup_append.mpr
    refine ⟨?_,embedEdge_nodup d es hn,?_⟩
    · exact List.nodup_range.map _ (fun a b hn he=>hn (congrArg Prod.snd he))
    · intro a ha b hb' he
      obtain ⟨t,ht,rfl⟩ := List.mem_map.mp ha
      obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hb'
      have h := congrArg Prod.snd he
      have := List.mem_range.mp ht
      simp only [embedEdge] at h
      omega
  · intro a ha b hb' he
    have eb : b=(List.range (d+n),d+n) := List.mem_singleton.mp hb'
    rw [eb] at he
    cases List.mem_append.mp ha with
    | inl h =>
      obtain ⟨t,ht,rfl⟩ := List.mem_map.mp h
      have h := congrArg Prod.snd he; have := List.mem_range.mp ht; simp only at h; omega
    | inr h =>
      obtain ⟨x,hx,rfl⟩ := List.mem_map.mp h
      have h := congrArg Prod.snd he; have := hb x hx; simp only [embedEdge] at h; omega

def iFull := paddingEdges 6 10 iEdges
def mFull := paddingEdges 3 12 mEdges
def tFullEdges := edges 8 [ChainTailSegment.wordA,ChainTailSegment.wordB]
def rest : Nat → List Edge
  | 0 => tFullEdges
  | r+1 => mFull ++ (rest r).map (embedEdge 16)
def global (r : Nat) : List Edge := iFull ++ (rest r).map (embedEdge 17)

theorem i_bounds : ∀e∈iEdges,e.2<10 :=
  edges_label_bound 10 _ (fun w hw=>((EnumerationCorrectness.upper_physical_enumeration_legal
    LocalCertificate.I.events LocalCertificate.I.initial LocalCertificate.I.final LocalCertificate.I.erasures w).mp hw).1.2.2)

theorem m_bounds : ∀e∈mEdges,e.2<12 :=
  edges_label_bound 12 _ (fun w hw=>((EnumerationCorrectness.upper_physical_enumeration_legal
    LocalCertificate.M.events LocalCertificate.M.initial LocalCertificate.M.final LocalCertificate.M.erasures w).mp hw).1.2.2)

theorem separate_nodup (n : Nat) (es fs : List Edge) (he : es.Nodup) (hf : fs.Nodup)
    (hb : ∀e∈es,e.2<n) : (es ++ fs.map (embedEdge n)).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨he,embedEdge_nodup n fs hf,?_⟩
  intro a ha b hb' heq
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hb'
  have h := congrArg Prod.snd heq; have := hb a ha
  simp only [embedEdge] at h; omega

theorem rest_nodup (r : Nat) : (rest r).Nodup := by
  induction r with
  | zero => exact edges_nodup _ _
  | succ r ih =>
    exact separate_nodup 16 mFull (rest r) (padding_nodup 3 12 mEdges (edges_nodup _ _) m_bounds)
      ih (padding_bounds 3 12 mEdges m_bounds)
theorem global_nodup (r : Nat) : (global r).Nodup :=
  separate_nodup 17 iFull (rest r) (padding_nodup 6 10 iEdges (edges_nodup _ _) i_bounds)
    (rest_nodup r) (padding_bounds 6 10 iEdges i_bounds)
theorem rest_length (r : Nat) : (rest r).length=63*r+10 := by
  induction r with
  | zero => exact t_full_edge_count
  | succ r ih =>
    simp only [rest,List.length_append,List.length_map,mFull,padding_length,m_edge_count,ih]
    omega
theorem global_length (r : Nat) : (global r).length=63*(r+1)+1 := by
  simp only [global,List.length_append,List.length_map,iFull,padding_length,i_edge_count,rest_length]
  omega
#print axioms global_nodup
#print axioms global_length
end ChainGlobalEdgeCandidates
