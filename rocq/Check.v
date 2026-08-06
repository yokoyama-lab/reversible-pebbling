(** Trust-base report for the developments.  See README.md.

    The cover's 925 windows are all built the same way, so a sample is
    enough here: [check_axioms.sh] runs [Print Assumptions] over every
    one of them. *)
From RevPebblingRocq Require Import
  KappaStar RhoEnclose LedgerParam EnvelopeE RhoDeriv SlopeWindow LedgerA
  CoverGlue LedgerCover.

Print Assumptions kappa_upper.
Print Assumptions kappa_lower.
Print Assumptions c_bracket_of_kappa.
Print Assumptions rho_in.
Print Assumptions f_window_qstar.
Print Assumptions root_exists.
Print Assumptions beta_bracket.
Print Assumptions bracket_at_1_5.
Print Assumptions f_ge_global.
Print Assumptions E_ge_one.
Print Assumptions E_lower_ratio.
Print Assumptions rhoc_spec.
Print Assumptions rhoc_unique.
Print Assumptions rhoc_continuous.
Print Assumptions derive_g_q.
Print Assumptions derive_g_r_neg.
Print Assumptions topkis.
Print Assumptions slope_window.
Print Assumptions slope_in_24_26.
Print Assumptions ledger_pos.
Print Assumptions window_24.

(** the cover's scaffolding *)
Print Assumptions CoverGlue.slope_upper.
Print Assumptions CoverGlue.slope_lower.
Print Assumptions CoverGlue.slope_closed.
Print Assumptions CoverGlue.ledger_window.

(** one window from each end of the cover, and one at its tightest point *)
Print Assumptions LedgerCoverP00.window_0.
Print Assumptions LedgerCoverP18.window_750.
Print Assumptions LedgerCoverP23.window_924.
