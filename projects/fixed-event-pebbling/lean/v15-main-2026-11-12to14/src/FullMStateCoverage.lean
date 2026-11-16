import MStateShard00
import MStateShard01
import MStateShard02
import MStateShard03
import MStateShard04
import MStateShard05
import MStateShard06
import MStateShard07
import MStateShard08
import MStateShard09
import MStateShard10
import MStateShard11
import MStateShard12
import MStateShard13
import MStateShard14
import MStateShard15
import MStateShard16
import MStateShard17
import MStateShard18
namespace ChainMStateShards
set_option maxHeartbeats 0

theorem all_prefixes_covered : words.all covered = true := by
  have h19 : (words.drop 608).all covered = true := by
    have hLen : words.length ≤ 608 := by rw [UpperCertificate.M.physical_word_count]; decide
    rw [List.drop_eq_nil_of_le hLen]
    rfl
  have h18 : (words.drop 576).all covered = true := by
    apply join_take_drop covered (words.drop 576) 32
    · exact shard_18
    · simpa only [List.drop_drop] using h19
  have h17 : (words.drop 544).all covered = true := by
    apply join_take_drop covered (words.drop 544) 32
    · exact shard_17
    · simpa only [List.drop_drop] using h18
  have h16 : (words.drop 512).all covered = true := by
    apply join_take_drop covered (words.drop 512) 32
    · exact shard_16
    · simpa only [List.drop_drop] using h17
  have h15 : (words.drop 480).all covered = true := by
    apply join_take_drop covered (words.drop 480) 32
    · exact shard_15
    · simpa only [List.drop_drop] using h16
  have h14 : (words.drop 448).all covered = true := by
    apply join_take_drop covered (words.drop 448) 32
    · exact shard_14
    · simpa only [List.drop_drop] using h15
  have h13 : (words.drop 416).all covered = true := by
    apply join_take_drop covered (words.drop 416) 32
    · exact shard_13
    · simpa only [List.drop_drop] using h14
  have h12 : (words.drop 384).all covered = true := by
    apply join_take_drop covered (words.drop 384) 32
    · exact shard_12
    · simpa only [List.drop_drop] using h13
  have h11 : (words.drop 352).all covered = true := by
    apply join_take_drop covered (words.drop 352) 32
    · exact shard_11
    · simpa only [List.drop_drop] using h12
  have h10 : (words.drop 320).all covered = true := by
    apply join_take_drop covered (words.drop 320) 32
    · exact shard_10
    · simpa only [List.drop_drop] using h11
  have h9 : (words.drop 288).all covered = true := by
    apply join_take_drop covered (words.drop 288) 32
    · exact shard_09
    · simpa only [List.drop_drop] using h10
  have h8 : (words.drop 256).all covered = true := by
    apply join_take_drop covered (words.drop 256) 32
    · exact shard_08
    · simpa only [List.drop_drop] using h9
  have h7 : (words.drop 224).all covered = true := by
    apply join_take_drop covered (words.drop 224) 32
    · exact shard_07
    · simpa only [List.drop_drop] using h8
  have h6 : (words.drop 192).all covered = true := by
    apply join_take_drop covered (words.drop 192) 32
    · exact shard_06
    · simpa only [List.drop_drop] using h7
  have h5 : (words.drop 160).all covered = true := by
    apply join_take_drop covered (words.drop 160) 32
    · exact shard_05
    · simpa only [List.drop_drop] using h6
  have h4 : (words.drop 128).all covered = true := by
    apply join_take_drop covered (words.drop 128) 32
    · exact shard_04
    · simpa only [List.drop_drop] using h5
  have h3 : (words.drop 96).all covered = true := by
    apply join_take_drop covered (words.drop 96) 32
    · exact shard_03
    · simpa only [List.drop_drop] using h4
  have h2 : (words.drop 64).all covered = true := by
    apply join_take_drop covered (words.drop 64) 32
    · exact shard_02
    · simpa only [List.drop_drop] using h3
  have h1 : (words.drop 32).all covered = true := by
    apply join_take_drop covered (words.drop 32) 32
    · exact shard_01
    · simpa only [List.drop_drop] using h2
  have h0 : (words.drop 0).all covered = true := by
    apply join_take_drop covered (words.drop 0) 32
    · exact shard_00
    · simpa only [List.drop_drop] using h1
  exact h0

#print axioms all_prefixes_covered
end ChainMStateShards
