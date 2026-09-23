# reach(p,e): largest n admitting a clean plan with peak p and at most e erasures

Conjecture B2 of the note: reach(p,e) = (e+2)·2^(p−2).  'proved' = the chain of length reach+1 was exhausted (exhaustive BFS over all configs with ≤ p pebbles, or the exact normal-form search).  Entries marked * are only lower bounds (search space truncated).

| p \ e | 0 | 1 | 2 | 3 | 4 | 5 | 6 |
|---|---|---|---|---|---|---|---|
| 2 | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
| 3 | 4 | 6 | 8 | 10 | 12 | 14 | 16 |
| 4 | 8 | 12 | 16 | 20 | 24 | 28 | 32 |
| 5 | 16 | 24 | 32 | 40 | 48 | 56 | 64 |
| 6 | 32 | 48 | 64 | 80 | 96 | 112 | 128 |
| 7 | 64 | 96 | 128 | 160 | 192 |  |  |

## Method per row

- p=2: exhaustive BFS N=9 (proved)
- p=3: exhaustive BFS N=17 (proved)
- p=4: exhaustive BFS N=33 (proved)
- p=5: exhaustive BFS N=65 (proved)
- p=6: exhaustive BFS N=129 (proved)
- p=7: normal-form search nmax=161 (proved); normal-form search nmax=193 (proved)

## Candidate closed forms vs all proved values

- `(e+2)*2^(p-2)`: FITS ALL
- `2^p-1+e*2^(p-2)`: 40 mismatches, e.g. [(6, 0, 32), (6, 1, 48), (6, 2, 64)]
- `2^(p-1)+e*2^(p-2)`: FITS ALL
- `(e+1)*2^(p-2) (LTV lemma 1)`: 40 mismatches, e.g. [(6, 0, 32), (6, 1, 48), (6, 2, 64)]
- `2^(p-1)*(1+e/2)`: FITS ALL

## M*(reach(p,e), p, e) (optimal move count at the reach)

| p \ e | 0 | 1 | 2 | 3 | 4 | 5 | 6 |
|---|---|---|---|---|---|---|---|
| 2 | 3 | 5 | 7 | 9 | 11 | 13 | 15 |
| 3 | 9 | 13 | 17 | 21 | 25 | 29 | 33 |
| 4 | 25 | 35 | 45 | 55 | 65 | 75 | 85 |
| 5 | 71 | 97 | 123 | 149 | 175 | 201 | 227 |
| 6 | 193 | 265 | 337 | 409 | 481 | 553 | 625 |
| 7 |  |  |  |  |  |  |  |
