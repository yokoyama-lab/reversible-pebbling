# Witness plans for n = reach(p,e) = (e+2)·2^(p−2)

Files `witness_p{p}_e{e}.txt`: one move per line (`place i`, `remove i`, `ERASE i`), with the configuration after each move.  All plans were re-verified by `pebble.check_plan` (flip rule, peak, erasure count, clean end).

For p ≤ 5 (all e ≤ 6) and p = 6 (e ≤ 3) the file holds a BFS-optimal plan.  For the remaining cases the file holds the block construction (base: optimal clean plan to 2^(p−1) with p pebbles; then e blocks: optimal clean plan for 2^(p−2) with p−1 pebbles from the stepping stone b, followed by `ERASE b`).

| p | e | n | plan length | M*(n,p,e) | status |
|---|---|---|---|---|---|
| 3 | 0 | 4 | 9 | 9 | optimal (= M*) |
| 3 | 1 | 6 | 13 | 13 | optimal (= M*) |
| 3 | 2 | 8 | 17 | 17 | optimal (= M*) |
| 3 | 3 | 10 | 21 | 21 | optimal (= M*) |
| 3 | 4 | 12 | 25 | 25 | optimal (= M*) |
| 3 | 5 | 14 | 29 | 29 | optimal (= M*) |
| 3 | 6 | 16 | 33 | 33 | optimal (= M*) |
| 4 | 0 | 8 | 25 | 25 | optimal (= M*) |
| 4 | 1 | 12 | 35 | 35 | optimal (= M*) |
| 4 | 2 | 16 | 45 | 45 | optimal (= M*) |
| 4 | 3 | 20 | 55 | 55 | optimal (= M*) |
| 4 | 4 | 24 | 65 | 65 | optimal (= M*) |
| 4 | 5 | 28 | 75 | 75 | optimal (= M*) |
| 4 | 6 | 32 | 85 | 85 | optimal (= M*) |
| 5 | 0 | 16 | 71 | 71 | optimal (= M*) |
| 5 | 1 | 24 | 97 | 97 | optimal (= M*) |
| 5 | 2 | 32 | 123 | 123 | optimal (= M*) |
| 5 | 3 | 40 | 149 | 149 | optimal (= M*) |
| 5 | 4 | 48 | 175 | 175 | optimal (= M*) |
| 5 | 5 | 56 | 201 | 201 | optimal (= M*) |
| 5 | 6 | 64 | 227 | 227 | optimal (= M*) |
| 6 | 0 | 32 | 193 | 193 | optimal (= M*) |
| 6 | 1 | 48 | 265 | 265 | optimal (= M*) |
| 6 | 2 | 64 | 337 | 337 | optimal (= M*) |
| 6 | 3 | 80 | 409 | 409 | optimal (= M*) |
| 6 | 4 | 96 | 481 | 481 | optimal (= M*) |
| 6 | 5 | 112 | 553 | 553 | optimal (= M*) |
| 6 | 6 | 128 | 625 | 625 | optimal (= M*) |
| 7 | 0 | 64 | 531 | 531 | optimal (= M*) |
| 7 | 1 | 96 | 725 |  | length = M*(2^(p-1),p,0) + e*(M*(2^(p-2),p-1,0)+1), the pattern that is optimal for every p <= 6; M* unknown here |
| 7 | 2 | 128 | 919 |  | length = M*(2^(p-1),p,0) + e*(M*(2^(p-2),p-1,0)+1), the pattern that is optimal for every p <= 6; M* unknown here |
| 7 | 3 | 160 | 1113 |  | length = M*(2^(p-1),p,0) + e*(M*(2^(p-2),p-1,0)+1), the pattern that is optimal for every p <= 6; M* unknown here |
| 7 | 4 | 192 | 1307 |  | length = M*(2^(p-1),p,0) + e*(M*(2^(p-2),p-1,0)+1), the pattern that is optimal for every p <= 6; M* unknown here |
| 7 | 5 | 224 | 1501 |  | length = M*(2^(p-1),p,0) + e*(M*(2^(p-2),p-1,0)+1), the pattern that is optimal for every p <= 6; M* unknown here |
| 7 | 6 | 256 | 1695 |  | length = M*(2^(p-1),p,0) + e*(M*(2^(p-2),p-1,0)+1), the pattern that is optimal for every p <= 6; M* unknown here |
| 8 | 0 | 128 | 1593 |  | valid but NOT optimal (8-pebble base plan is the Bennett 3x composition, 3*M*(64,7,0) moves) |
| 8 | 1 | 192 | 2125 |  | valid but NOT optimal (8-pebble base plan is the Bennett 3x composition, 3*M*(64,7,0) moves) |
| 8 | 2 | 256 | 2657 |  | valid but NOT optimal (8-pebble base plan is the Bennett 3x composition, 3*M*(64,7,0) moves) |
| 8 | 3 | 320 | 3189 |  | valid but NOT optimal (8-pebble base plan is the Bennett 3x composition, 3*M*(64,7,0) moves) |
| 8 | 4 | 384 | 3721 |  | valid but NOT optimal (8-pebble base plan is the Bennett 3x composition, 3*M*(64,7,0) moves) |
| 8 | 5 | 448 | 4253 |  | valid but NOT optimal (8-pebble base plan is the Bennett 3x composition, 3*M*(64,7,0) moves) |
| 8 | 6 | 512 | 4785 |  | valid but NOT optimal (8-pebble base plan is the Bennett 3x composition, 3*M*(64,7,0) moves) |

Observed identity (all p ≤ 6, e ≤ 6): M*(reach(p,e), p, e) = M*(2^(p−1), p, 0) + e·(M*(2^(p−2), p−1, 0) + 1), i.e. the block construction with optimal sub-plans is optimal at the reach.  Base values M*(2^(p−1),p,0): p=1: 1, p=2: 3, p=3: 9, p=4: 25, p=5: 71, p=6: 193, p=7: 531.

Erasure positions in the BFS-optimal witnesses (p ≤ 5) versus the block construction 2^(p−1)+i·2^(p−2):

- p=3 e=0 n=4: erasures (in time order) at []; construction would use []
- p=3 e=1 n=6: erasures (in time order) at [4]; construction would use [4]
- p=3 e=2 n=8: erasures (in time order) at [4, 6]; construction would use [4, 6]
- p=3 e=3 n=10: erasures (in time order) at [4, 6, 8]; construction would use [4, 6, 8]
- p=3 e=4 n=12: erasures (in time order) at [4, 6, 8, 10]; construction would use [4, 6, 8, 10]
- p=3 e=5 n=14: erasures (in time order) at [4, 6, 8, 10, 12]; construction would use [4, 6, 8, 10, 12]
- p=3 e=6 n=16: erasures (in time order) at [4, 6, 8, 10, 12, 14]; construction would use [4, 6, 8, 10, 12, 14]
- p=4 e=0 n=8: erasures (in time order) at []; construction would use []
- p=4 e=1 n=12: erasures (in time order) at [8]; construction would use [8]
- p=4 e=2 n=16: erasures (in time order) at [8, 12]; construction would use [8, 12]
- p=4 e=3 n=20: erasures (in time order) at [8, 12, 16]; construction would use [8, 12, 16]
- p=4 e=4 n=24: erasures (in time order) at [8, 12, 16, 20]; construction would use [8, 12, 16, 20]
- p=4 e=5 n=28: erasures (in time order) at [8, 12, 16, 20, 24]; construction would use [8, 12, 16, 20, 24]
- p=4 e=6 n=32: erasures (in time order) at [8, 12, 16, 20, 24, 28]; construction would use [8, 12, 16, 20, 24, 28]
- p=6 e=0 n=32: erasures (in time order) at []; construction would use []
- p=6 e=1 n=48: erasures (in time order) at [32]; construction would use [32]
- p=6 e=2 n=64: erasures (in time order) at [32, 48]; construction would use [32, 48]
- p=5 e=0 n=16: erasures (in time order) at []; construction would use []
- p=5 e=1 n=24: erasures (in time order) at [16]; construction would use [16]
- p=5 e=2 n=32: erasures (in time order) at [16, 24]; construction would use [16, 24]
- p=5 e=3 n=40: erasures (in time order) at [16, 24, 32]; construction would use [16, 24, 32]
- p=5 e=4 n=48: erasures (in time order) at [16, 24, 32, 40]; construction would use [16, 24, 32, 40]
- p=5 e=5 n=56: erasures (in time order) at [16, 24, 32, 40, 48]; construction would use [16, 24, 32, 40, 48]
- p=5 e=6 n=64: erasures (in time order) at [16, 24, 32, 40, 48, 56]; construction would use [16, 24, 32, 40, 48, 56]
- p=6 e=0 n=32: erasures (in time order) at []; construction would use []
- p=6 e=1 n=48: erasures (in time order) at [32]; construction would use [32]
- p=6 e=2 n=64: erasures (in time order) at [32, 48]; construction would use [32, 48]
- p=6 e=3 n=80: erasures (in time order) at [32, 48, 64]; construction would use [32, 48, 64]
- p=2 e=0 n=2: erasures (in time order) at []; construction would use []
- p=2 e=1 n=3: erasures (in time order) at [2]; construction would use [2]
- p=2 e=2 n=4: erasures (in time order) at [2, 3]; construction would use [2, 3]
- p=2 e=3 n=5: erasures (in time order) at [2, 3, 4]; construction would use [2, 3, 4]
- p=2 e=4 n=6: erasures (in time order) at [2, 3, 4, 5]; construction would use [2, 3, 4, 5]
- p=2 e=5 n=7: erasures (in time order) at [2, 3, 4, 5, 6]; construction would use [2, 3, 4, 5, 6]
- p=2 e=6 n=8: erasures (in time order) at [2, 3, 4, 5, 6, 7]; construction would use [2, 3, 4, 5, 6, 7]
