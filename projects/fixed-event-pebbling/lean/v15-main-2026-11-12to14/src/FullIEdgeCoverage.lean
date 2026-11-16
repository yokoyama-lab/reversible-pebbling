import EdgeShardI00
import EdgeShardI01
import EdgeShardI02
import EdgeShardI03
import EdgeShardI04
import EdgeShardI05
import EdgeShardI06
namespace ChainLocalEdges
set_option maxHeartbeats 0
theorem coverageI : UpperCertificate.I.physicalWords.all (covered 10 candidatesI)=true := by
  have h7 : (UpperCertificate.I.physicalWords.drop 224).all (covered 10 candidatesI)=true := by
    have hl : UpperCertificate.I.physicalWords.length≤224 := by rw [UpperCertificate.I.physical_word_count]; decide
    rw [List.drop_eq_nil_of_le hl]
    rfl
  have h6 : (UpperCertificate.I.physicalWords.drop 192).all (covered 10 candidatesI)=true := by
    apply ChainMStateShards.join_take_drop (covered 10 candidatesI) (UpperCertificate.I.physicalWords.drop 192) 32
    · exact shardI06
    · simpa only [List.drop_drop] using h7
  have h5 : (UpperCertificate.I.physicalWords.drop 160).all (covered 10 candidatesI)=true := by
    apply ChainMStateShards.join_take_drop (covered 10 candidatesI) (UpperCertificate.I.physicalWords.drop 160) 32
    · exact shardI05
    · simpa only [List.drop_drop] using h6
  have h4 : (UpperCertificate.I.physicalWords.drop 128).all (covered 10 candidatesI)=true := by
    apply ChainMStateShards.join_take_drop (covered 10 candidatesI) (UpperCertificate.I.physicalWords.drop 128) 32
    · exact shardI04
    · simpa only [List.drop_drop] using h5
  have h3 : (UpperCertificate.I.physicalWords.drop 96).all (covered 10 candidatesI)=true := by
    apply ChainMStateShards.join_take_drop (covered 10 candidatesI) (UpperCertificate.I.physicalWords.drop 96) 32
    · exact shardI03
    · simpa only [List.drop_drop] using h4
  have h2 : (UpperCertificate.I.physicalWords.drop 64).all (covered 10 candidatesI)=true := by
    apply ChainMStateShards.join_take_drop (covered 10 candidatesI) (UpperCertificate.I.physicalWords.drop 64) 32
    · exact shardI02
    · simpa only [List.drop_drop] using h3
  have h1 : (UpperCertificate.I.physicalWords.drop 32).all (covered 10 candidatesI)=true := by
    apply ChainMStateShards.join_take_drop (covered 10 candidatesI) (UpperCertificate.I.physicalWords.drop 32) 32
    · exact shardI01
    · simpa only [List.drop_drop] using h2
  have h0 : (UpperCertificate.I.physicalWords.drop 0).all (covered 10 candidatesI)=true := by
    apply ChainMStateShards.join_take_drop (covered 10 candidatesI) (UpperCertificate.I.physicalWords.drop 0) 32
    · exact shardI00
    · simpa only [List.drop_drop] using h1
  exact h0
#print axioms coverageI
end ChainLocalEdges
