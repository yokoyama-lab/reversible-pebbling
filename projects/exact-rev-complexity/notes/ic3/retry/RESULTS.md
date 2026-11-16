# 再挑戦の回収（2026-09-06 16:49）

2026-09-06 10:49 に空いた機械（load 3.1）へ再投入した 2 本の結果。
初回の UNDECIDED は load 25〜29 の飽和した共用機での壁時計だった。

- **retry_h14p40**: Property UNDECIDED Time = 21600.88 sec / 到達 frame 15 
- **retry_h15p42**: Property proved Time =  5286.32 sec / 到達 frame 18 / Invariant F[15] : 52664 clauses with 99 flops

⚠ `Property proved` なら、`scripts/ic3_verify.py` で不変量を独立検査すること
（本文 §12 と同じ 3 本。`--split` は cube 数 / 1000 くらい）。
⚠ `UNDECIDED` は**打ち切り**であって「不変量が無い」ではない（本文 §0）。
