import UpperCore
import TailSegment
namespace ChainPrefixStates
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-- Prefix completed sets represented canonically by filtering the event universe. -/
def setsOfWord (n : Nat) (w : List Nat) : List (List Nat) :=
  (List.range (w.length+1)).map fun t => (List.range n).filter fun e => (w.take t).contains e
/-- All completable sets: exactly prefixes of the enumerated complete words. -/
def states (n : Nat) (words : List (List Nat)) : List (List Nat) :=
  (words.flatMap (setsOfWord n)).eraseDups

def iStates := states 10 UpperCertificate.I.physicalWords
def mStates := states 12 UpperCertificate.M.physicalWords
/-- T5 removes the shared forced three-event prefix from the existing T8 words. -/
def tWords := [ChainTailSegment.wordA.drop 3,ChainTailSegment.wordB.drop 3]
def tStates := states 8 tWords
end ChainPrefixStates
