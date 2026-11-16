import IStates
import TStates
import MStateCountVerified
namespace ChainGlobalStateCandidates
open ChainPrefixStates

def embed (o : Nat) (s : List Nat) : List Nat := List.range o ++ s.map (fun i => i+o)

theorem embed_length (o : Nat) (s : List Nat) : (embed o s).length=o+s.length := by
  simp [embed]

theorem embed_injective (o : Nat) (a b : List Nat) (h : embed o a=embed o b) : a=b := by
  have hm : a.map (fun i=>i+o)=b.map (fun i=>i+o) := List.append_cancel_left h
  have hh := congrArg (List.map (fun i=>i-o)) hm
  simpa only [List.map_map,Function.comp_def,Nat.add_sub_cancel,List.map_id'] using hh

theorem embed_nodup (o : Nat) (ss : List (List Nat)) (h : ss.Nodup) :
    (ss.map (embed o)).Nodup :=
  h.map (embed o) (fun a b hn he => hn (embed_injective o a b he))

theorem states_length_bound (n : Nat) (words : List (List Nat)) (s : List Nat)
    (h : s ∈ states n words) : s.length ≤ n := by
  obtain ⟨w,hw,t,ht,rfl⟩ := (mem_states_iff n words s).mp h
  have hh := List.length_filter_le (fun e => (w.take t).contains e) (List.range n)
  simpa using hh

/-- All prefix states of a fixed-prefix/local/final-event block except its final state. -/
def paddedHalf (d : Nat) (ss : List (List Nat)) : List (List Nat) :=
  (List.range d).map List.range ++ ss.map (embed d)

theorem paddedHalf_length (d : Nat) (ss : List (List Nat)) :
    (paddedHalf d ss).length=d+ss.length := by simp [paddedHalf]

theorem paddedHalf_nodup (d : Nat) (ss : List (List Nat)) (hn : ss.Nodup) :
    (paddedHalf d ss).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨?_,embed_nodup d ss hn,?_⟩
  · exact List.nodup_range.map List.range (fun a b hn he => hn (by
      have hh := congrArg List.length he
      simpa using hh))
  · intro a ha b hb he
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hb
    have hh := congrArg List.length he
    simp only [List.length_range,embed_length] at hh
    have := List.mem_range.mp hi
    omega

theorem paddedHalf_bound (d n : Nat) (ss : List (List Nat))
    (hb : ∀s∈ss,s.length≤n) (s : List Nat) (hs : s ∈ paddedHalf d ss) :
    s.length < d+n+1 := by
  cases List.mem_append.mp hs with
  | inl h =>
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp h
    have := List.mem_range.mp hi
    simp only [List.length_range]
    omega
  | inr h =>
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp h
    rw [embed_length]
    have := hb a ha
    omega

def iHalf := paddedHalf 6 iStates
def mHalf := paddedHalf 3 mStates
def tFull := states 8 [ChainTailSegment.wordA,ChainTailSegment.wordB]

def rest : Nat → List (List Nat)
  | 0 => tFull
  | r+1 => mHalf ++ (rest r).map (embed 16)
def global (r : Nat) : List (List Nat) := iHalf ++ (rest r).map (embed 17)

theorem rest_length (r : Nat) : (rest r).length=40*r+10 := by
  induction r with
  | zero => exact t_full_state_count
  | succ r ih =>
    simp only [rest,List.length_append,List.length_map,mHalf,paddedHalf_length,
      ChainMStateShards.m_state_count_verified,ih]
    omega

theorem global_length (r : Nat) : (global r).length=40*(r+1)+5 := by
  simp only [global,List.length_append,List.length_map,iHalf,paddedHalf_length,i_state_count,rest_length]
  omega

theorem separated_append_nodup (n : Nat) (left right : List (List Nat))
    (hl : left.Nodup) (hr : right.Nodup) (hb : ∀s∈left,s.length<n) :
    (left ++ right.map (embed n)).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨hl,embed_nodup n right hr,?_⟩
  intro a ha b hb' he
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hb'
  have hh := congrArg List.length he
  rw [embed_length] at hh
  have := hb a ha
  omega

theorem rest_nodup (r : Nat) : (rest r).Nodup := by
  induction r with
  | zero => exact states_nodup _ _
  | succ r ih =>
    exact separated_append_nodup 16 mHalf (rest r)
      (paddedHalf_nodup 3 mStates (states_nodup _ _)) ih
      (paddedHalf_bound 3 12 mStates (states_length_bound 12 _))

theorem global_nodup (r : Nat) : (global r).Nodup := by
  exact separated_append_nodup 17 iHalf (rest r)
    (paddedHalf_nodup 6 iStates (states_nodup _ _)) (rest_nodup r)
    (paddedHalf_bound 6 10 iStates (states_length_bound 10 _))

#print axioms global_length
#print axioms global_nodup
end ChainGlobalStateCandidates
