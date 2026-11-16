import EdgeShardM00
import EdgeShardM01
import EdgeShardM02
import EdgeShardM03
import EdgeShardM04
import EdgeShardM05
import EdgeShardM06
import EdgeShardM07
import EdgeShardM08
import EdgeShardM09
import EdgeShardM10
import EdgeShardM11
import EdgeShardM12
import EdgeShardM13
import EdgeShardM14
import EdgeShardM15
import EdgeShardM16
import EdgeShardM17
import EdgeShardM18
namespace ChainLocalEdges
set_option maxHeartbeats 0
theorem coverageM : UpperCertificate.M.physicalWords.all (covered 12 candidatesM)=true := by
  have h19 : (UpperCertificate.M.physicalWords.drop 608).all (covered 12 candidatesM)=true := by
    have hl : UpperCertificate.M.physicalWords.length≤608 := by rw [UpperCertificate.M.physical_word_count]; decide
    rw [List.drop_eq_nil_of_le hl]
    rfl
  have h18 : (UpperCertificate.M.physicalWords.drop 576).all (covered 12 candidatesM)=true := by
    apply ChainMStateShards.join_take_drop (covered 12 candidatesM) (UpperCertificate.M.physicalWords.drop 576) 32
    · exact shardM18
    · simpa only [List.drop_drop] using h19
  have h17 : (UpperCertificate.M.physicalWords.drop 544).all (covered 12 candidatesM)=true := by
    apply ChainMStateShards.join_take_drop (covered 12 candidatesM) (UpperCertificate.M.physicalWords.drop 544) 32
    · exact shardM17
    · simpa only [List.drop_drop] using h18
  have h16 : (UpperCertificate.M.physicalWords.drop 512).all (covered 12 candidatesM)=true := by
    apply ChainMStateShards.join_take_drop (covered 12 candidatesM) (UpperCertificate.M.physicalWords.drop 512) 32
    · exact shardM16
    · simpa only [List.drop_drop] using h17
  have h15 : (UpperCertificate.M.physicalWords.drop 480).all (covered 12 candidatesM)=true := by
    apply ChainMStateShards.join_take_drop (covered 12 candidatesM) (UpperCertificate.M.physicalWords.drop 480) 32
    · exact shardM15
    · simpa only [List.drop_drop] using h16
  have h14 : (UpperCertificate.M.physicalWords.drop 448).all (covered 12 candidatesM)=true := by
    apply ChainMStateShards.join_take_drop (covered 12 candidatesM) (UpperCertificate.M.physicalWords.drop 448) 32
    · exact shardM14
    · simpa only [List.drop_drop] using h15
  have h13 : (UpperCertificate.M.physicalWords.drop 416).all (covered 12 candidatesM)=true := by
    apply ChainMStateShards.join_take_drop (covered 12 candidatesM) (UpperCertificate.M.physicalWords.drop 416) 32
    · exact shardM13
    · simpa only [List.drop_drop] using h14
  have h12 : (UpperCertificate.M.physicalWords.drop 384).all (covered 12 candidatesM)=true := by
    apply ChainMStateShards.join_take_drop (covered 12 candidatesM) (UpperCertificate.M.physicalWords.drop 384) 32
    · exact shardM12
    · simpa only [List.drop_drop] using h13
  have h11 : (UpperCertificate.M.physicalWords.drop 352).all (covered 12 candidatesM)=true := by
    apply ChainMStateShards.join_take_drop (covered 12 candidatesM) (UpperCertificate.M.physicalWords.drop 352) 32
    · exact shardM11
    · simpa only [List.drop_drop] using h12
  have h10 : (UpperCertificate.M.physicalWords.drop 320).all (covered 12 candidatesM)=true := by
    apply ChainMStateShards.join_take_drop (covered 12 candidatesM) (UpperCertificate.M.physicalWords.drop 320) 32
    · exact shardM10
    · simpa only [List.drop_drop] using h11
  have h9 : (UpperCertificate.M.physicalWords.drop 288).all (covered 12 candidatesM)=true := by
    apply ChainMStateShards.join_take_drop (covered 12 candidatesM) (UpperCertificate.M.physicalWords.drop 288) 32
    · exact shardM09
    · simpa only [List.drop_drop] using h10
  have h8 : (UpperCertificate.M.physicalWords.drop 256).all (covered 12 candidatesM)=true := by
    apply ChainMStateShards.join_take_drop (covered 12 candidatesM) (UpperCertificate.M.physicalWords.drop 256) 32
    · exact shardM08
    · simpa only [List.drop_drop] using h9
  have h7 : (UpperCertificate.M.physicalWords.drop 224).all (covered 12 candidatesM)=true := by
    apply ChainMStateShards.join_take_drop (covered 12 candidatesM) (UpperCertificate.M.physicalWords.drop 224) 32
    · exact shardM07
    · simpa only [List.drop_drop] using h8
  have h6 : (UpperCertificate.M.physicalWords.drop 192).all (covered 12 candidatesM)=true := by
    apply ChainMStateShards.join_take_drop (covered 12 candidatesM) (UpperCertificate.M.physicalWords.drop 192) 32
    · exact shardM06
    · simpa only [List.drop_drop] using h7
  have h5 : (UpperCertificate.M.physicalWords.drop 160).all (covered 12 candidatesM)=true := by
    apply ChainMStateShards.join_take_drop (covered 12 candidatesM) (UpperCertificate.M.physicalWords.drop 160) 32
    · exact shardM05
    · simpa only [List.drop_drop] using h6
  have h4 : (UpperCertificate.M.physicalWords.drop 128).all (covered 12 candidatesM)=true := by
    apply ChainMStateShards.join_take_drop (covered 12 candidatesM) (UpperCertificate.M.physicalWords.drop 128) 32
    · exact shardM04
    · simpa only [List.drop_drop] using h5
  have h3 : (UpperCertificate.M.physicalWords.drop 96).all (covered 12 candidatesM)=true := by
    apply ChainMStateShards.join_take_drop (covered 12 candidatesM) (UpperCertificate.M.physicalWords.drop 96) 32
    · exact shardM03
    · simpa only [List.drop_drop] using h4
  have h2 : (UpperCertificate.M.physicalWords.drop 64).all (covered 12 candidatesM)=true := by
    apply ChainMStateShards.join_take_drop (covered 12 candidatesM) (UpperCertificate.M.physicalWords.drop 64) 32
    · exact shardM02
    · simpa only [List.drop_drop] using h3
  have h1 : (UpperCertificate.M.physicalWords.drop 32).all (covered 12 candidatesM)=true := by
    apply ChainMStateShards.join_take_drop (covered 12 candidatesM) (UpperCertificate.M.physicalWords.drop 32) 32
    · exact shardM01
    · simpa only [List.drop_drop] using h2
  have h0 : (UpperCertificate.M.physicalWords.drop 0).all (covered 12 candidatesM)=true := by
    apply ChainMStateShards.join_take_drop (covered 12 candidatesM) (UpperCertificate.M.physicalWords.drop 0) 32
    · exact shardM00
    · simpa only [List.drop_drop] using h1
  exact h0
#print axioms coverageM
end ChainLocalEdges
