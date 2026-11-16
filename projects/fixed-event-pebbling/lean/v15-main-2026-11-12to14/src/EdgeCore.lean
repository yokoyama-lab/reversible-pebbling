import PrefixStateCorrectness
import LocalStateLanguages
namespace ChainLocalEdges
open ChainPrefixStates
abbrev Edge := List Nat × Nat

def edgeAt (n : Nat) (w : List Nat) (t : Nat) : Edge :=
  ((List.range n).filter (fun e => (w.take t).contains e), w.getD t 0)
def edgesOfWord (n : Nat) (w : List Nat) : List Edge :=
  (List.range w.length).map (edgeAt n w)
def edges (n : Nat) (words : List (List Nat)) : List Edge :=
  (words.flatMap (edgesOfWord n)).eraseDups

theorem mem_edges_iff (n : Nat) (words : List (List Nat)) (e : Edge) :
    e ∈ edges n words ↔ ∃w∈words,∃t,t<w.length ∧ edgeAt n w t=e := by
  simp only [edges,List.mem_eraseDups,List.mem_flatMap,edgesOfWord,List.mem_map,List.mem_range]

theorem edges_nodup (n : Nat) (words : List (List Nat)) : (edges n words).Nodup :=
  eraseDups_nodup _

def iEdges := edges 10 UpperCertificate.I.physicalWords
def mEdges := edges 12 UpperCertificate.M.physicalWords
def tEdges := edges 8 tWords
end ChainLocalEdges
