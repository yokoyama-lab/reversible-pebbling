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
| `emit.py` | the Rocq text: `emit_node` (three point enclosures of `f` plus the two halves of a slope bracket), `emit_window` (nine enclosures plus one application of `ledger_window`).  Also holds `EPSB` and `CBAR` — see below |
| `gencover.py` | the driver: picks the grid, splits into parts, writes the index |
| `prologue.v` | the source of `rocq/CoverGlue.v` (kept here so the generated and hand-written halves live together; `CoverGlue.v` is the copy the build uses) |
| `check_tiling.py` | re-derives the coverage claim from the *emitted theorems* |
| `spotcheck.py` | checks that each sampled window's slope bracket really contains `−f'(q₁)` |

## Checking the claim the prover does not check

Rocq checks each of the 932 windows.  Nothing in Rocq checks that their
*union* is `[1.45, 3.25]`, or that any of them says something non-vacuous.
Two scripts do, both reading the generated `.v` files rather than the
generator's own bookkeeping:

```sh
python3 check_tiling.py .. 1.45 3.25   # stdlib only
python3 spotcheck.py .. 60             # needs mpmath
```

`check_tiling.py` parses each `window_i`'s hypothesis `qa ≤ q1 ≤ qb` and
its conclusion `val ≤ ledger …`, and verifies that the windows are
consecutive, that consecutive ones share an endpoint *exactly*, that the
union runs from end to end, that every `val` is positive, and that every
**slope bracket is non-empty** — `hz_i` is trivially provable when
`blo > bhi`, so an empty bracket would make a whole window say nothing.
(An empty bracket is exactly the signature of a `q` that is not a
minimiser; it is what happens below `q ≈ 0.5`, where `f` is concave.)

`spotcheck.py` rules out the subtler vacuity: a non-empty bracket sitting
where the true slope never goes.  It recomputes `−f'` at window midpoints
and checks containment.

The eps-widening makes non-emptiness *easier* — the narrowest bracket
went from `4.10·10⁻⁶` to `8.10·10⁻⁶`, the extra `4·10⁻⁶` being exactly
`2·CBAR`.  So `check_tiling.py` alone is a weaker guard than it was, and
`spotcheck.py`'s containment test is the one that still has teeth.

Current output:

```
932 windows, union [1.45, 3.25]
widths  2.000e-07 .. 3.651e-02
ledger  >= 0.002047 (smallest certified value)
slope brackets: 932, widths 8.104e-06 .. 2.714e-03, all non-empty
TILING OK
```

## The eps-form

The windows assume only **eps-minimality** of the slope
(`LedgerParam.EminEps`), because that is the version
`EminExists.emin_eps_exists` proves to exist at every slope; exact
minimality was never shown satisfiable at all.

Two constants in `emit.py` carry it:

| constant | value | meaning |
|---|---|---|
| `EPSB` | `1e-11` | the largest `eps` the cover is proved for; **must equal `CoverGlue.EPSB`** |
| `CBAR` | `2e-6` | the slope-bracket widening, `>= 2*EPSB/H`; handed to `CoverGlue.slope_hi_eps` / `slope_lo_eps` |

`node_data` adds `CBAR` to `bhi` and subtracts it from `blo` **before**
the outward rounding, so a node constant absorbs both the `eps/h` the
difference quotient loses and the further `eps/h` the transport to the
window's interior loses.  Nothing else in the pipeline changes: the
widened bracket propagates through `window()` exactly as a wider slope
bracket would.

**Measured before it was built.**  Rerunning `window()` on the previous
925-window grid with the bracket widened by `C`, the smallest certified
ledger value goes

| `C` | `eps = C·h/2` | min ledger | binding window |
|---|---|---|---|
| `0` | `0` | `0.0020580` | 740 |
| `1e-6` | `5e-12` | `0.0020152` | 740 |
| `1e-5` | `5e-11` | `0.0016094` | 683 |
| `3.987e-5` | `1.99e-10` | `~0` | 522, `q₁ ∈ [2.11790, 2.11902]` |
| `1e-4` | `5e-10` | `-0.0039247` | 366 |

so `eps = 1.99e-10` is the cliff and `EPSB = 1e-11` is a factor 20
inside it.  Re-running the adaptive grid with the widened brackets needs
932 windows instead of 925 — the extra ones sit where the bracket was
narrowest.

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
