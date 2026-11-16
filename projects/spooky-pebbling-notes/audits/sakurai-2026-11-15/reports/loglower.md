# LOGLOWER L3: explicit eventual H log H lower bound

Prior SUMAREA S3 STOP and work log1706 readback confirmed. Owner spooky_dp; no competing assignment for this arithmetic proof. Finite reservation600s wall, per call CPU30/wall60s/1GiB. All calls STOP.

## Verified theorem
`LogLower.paper_explicit_log_lower`: n=2^H-1>0; actual PaperRuns d q r; every initial vertex nonpebbled; final root pebbled and nonroots empty; actual work<=3n; union-space<=s; s>0; integer c>0; H*s<=c*n; and

    H >= 2^(2*(Nat.log2(16*c)+1))

imply

    H * Nat.log2 H <= 2*c*d.

Nat.log2 is floor base-two logarithm. This explicit uniform eventual inequality proves D=Omega(H log H) for each fixed c and s<=c*n/H, hence for s=Theta(n/H). Only the upper-space constant is needed; no lower Theta constant is assumed. No BigOmega library notation or real-analysis theorem is used. The entire eventual bound with explicit threshold and coefficient is kernel-checked. Choosing c depending on H does not yield a uniform fixed-c asymptotic statement.

`paper_log_lower` permits any k with16c<=2^k,H>=2^(2k). It selects ell=Nat.log2 H-k in SUMAREA's finite inequality. `scale_loss` proves at least n/2 surviving weighted vertices under16s*2^ell<=n. `transfer_scale` and `transfer_depth` cancel positive c and n without division or rounding assumptions. `log_scale` proves scale feasibility and logH<=2ell+1.

## Verification
Lean4.35.0 arm64 commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc. L1/L2 failures saved, not evidence of theorem falsity. L3 rc0 UTC2026-11-15T16:54:27.538581--16:54:27.890046, CPU0.343842s, peak675250176bytes. Final theorem dependencies only propext,Classical.choice,Quot.sound; no sorry/admit/native_decide. Failure logs printing sorryAx do not apply to successful final proof.

## Boundaries
This is the e=0 fixed work coefficient3 case, NOT a lower bound for arbitrary linear-work constants C>3. Lee's multi-stage upper constructions preclude that extrapolation. Prior-work novelty handled independently; no S-grade/newness claim. Independent prose-to-model audit remains separate from kernel theorem. No existing file overwrite in showa, Git publication/merge, new cost or expanded permission. Mikawa export remains explicitly blocked pending approval, not retried.
