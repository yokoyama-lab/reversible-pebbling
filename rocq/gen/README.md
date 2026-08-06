# `gen/` — the generator for the Zone I ledger cover

`LedgerA.window_24` closes Lemma A's ledger on one window of `q₁`, with
the slope bracket assumed.  Zone I needs that on the whole slope range
`q₁ ∈ [1.45, 3.25]`.  Every window is the same proof with different
constants, so the constants are computed here and the Rocq text is
printed.

```sh
make cover        # from rocq/ — regenerates LedgerCoverP*.v and LedgerCover.v
make -j8          # ≈ 3 min wall; the parts are independent
```

or directly

```sh
python3 gencover.py QLO QHI MARGIN OUTDIR [PER_PART] [MAXWINDOWS]
python3 gencover.py 1.45 3.25 0.001 .. 40
```

Needs `mpmath`.

## Files

| file | contents |
|---|---|
| `ledger.py` | the numerics: `ρ_c`, `f`, outward rounding, an interval class, and `window()` which returns every constant one window needs |
| `emit.py` | the Rocq text: `emit_node` (three point enclosures of `f` plus the two halves of a slope bracket), `emit_window` (nine enclosures plus one application of `ledger_window`) |
| `gencover.py` | the driver: picks the grid, splits into parts, writes the index |
| `prologue.v` | the source of `rocq/CoverGlue.v` (kept here so the generated and hand-written halves live together; `CoverGlue.v` is the copy the build uses) |

## The rule every constant obeys

**Compute numerically first, round *outward*, then transcribe.**  Nothing
is guessed and nothing is edited by hand afterwards.  `mp.dps = 40`
throughout; grid points carry 7 decimals, derived window constants 9,
`ρ`-boxes and point values of `f` 12.  `ledger.py:dn/up` take a whole
extra ulp beyond the correct direction.

The safety net is that the prover is the arbiter.  A constant that came
out too tight makes `rocq c` fail on the corresponding `interval` call;
it can never make the proof unsound, because the emitted lemma states the
bound and `interval` has to prove it.  The Python interval arithmetic is
therefore a *predictor* of what CoqInterval will accept, not part of the
trust base.

To predict well it must imitate the tactic, and the point where that
matters is **decoupling**: `interval` treats each occurrence of a variable
as independent, so `w₁·q₁ + (1−w₁)·q₂` is evaluated over independent
copies of `w₁`.  `ledger.py`'s interval class does the same, by
enumerating corners.  Where the tactic would be tighter than the corner
hull (a genuinely monotone one-variable expression) the corner hull is
still valid, just conservative.

Do **not** string-replace constants in a generated `.v` file: a substring
match once turned `777586/1000000` into `777585/1000000` silently.
Regenerate instead.

## How the grid is chosen

At each node, bisection on the width finds the largest window whose
ledger enclosure still clears `MARGIN`; the width is then shrunk by 10%
and the window recomputed.  Widths span two orders of magnitude across
the range because the ledger's own margin does — the pointwise value of
the ledger is `0.0409` at `q₁ = 1.45`, dips to its minimum `0.01175` at
`q₁ ≈ 2.40`, and climbs to `0.0268` at `q₁ = 3.25`, while the *width* of
the enclosure at fixed `W` shrinks steadily as `q₁` grows.

## What was measured, and what it bought

| measurement | result |
|---|---|
| `G` with the two terms decoupled, on the `window_24` `z`-box | `[0.013772, 0.013990]`, width `2.18·10⁻⁴` |
| … with `interval with (i_bisect z, i_prec 120)` | `[0.0138730, 0.0138887]`, width `1.57·10⁻⁵` — a **13.9×** recovery, against a true width of `1.436·10⁻⁵` |
| cost of that | ≈ **1.6 s** per window, versus ≈ 0.05 s for the plain call |
| effect on the ledger | `G` enters with weight `1−w₁ ≤ 0.25`, so `2·10⁻⁴` of excess costs `5·10⁻⁵` of a ledger enclosure that is `6·10⁻³` wide |

So `i_bisect` is **not** used in the cover: it would have tripled the
build for a change three orders of magnitude below what decides whether a
window closes.  What does decide is the width of `f` at the composite
slope `q̃`, which comes from `w₁`, which comes from `E = q₁b + f₁`.

Other measurements that fixed the design:

- per window (nine `interval` calls at `i_prec 120`) plus one node
  (three at `i_prec 200`, plus two `beta_bracket` applications):
  **≈ 1.1 s**, and **≈ 11 MB** of prover memory.  The memory is why the
  cover is split into parts: one file with ~950 windows would need about
  10 GB.
- the ledger's enclosure at `q₁ = 2.4`: `W = 10⁻³` → lower end `0.0056`;
  `W = 2·10⁻³` → `−0.0005`.  So `2·10⁻³` is genuinely past the edge, as
  `LedgerA`'s note says, and the usable width there is `≈ 1.5·10⁻³`.
- the node slope bracket at `h = 10⁻⁵` is `≈ 1.4·10⁻⁶` wide, against
  `|f''|·W ≈ 1.9·10⁻⁴` for the window's own slope variation — i.e. the
  bracket is not what limits `W`, so there is no reason to spend more
  point enclosures on it.
