/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import TuranBessel.Anomaly
import TuranBessel.CriticalConstant
import TuranBessel.GammaRatio
import TuranBessel.GramRep
import TuranBessel.NegativeOrder
import TuranBessel.ScalarH
import TuranBessel.SectorAverage

/-!
# Axiom regression guard

A build-time check that the development stays sorry-free and axiom-free.  Each
`#guard_msgs in #print axioms …` pins the axiom footprint of one result to
Lean's three standard axioms `[propext, Classical.choice, Quot.sound]` and
nothing else.  If a `sorry` or a stray `axiom` ever enters a dependency, the
reported footprint changes and `#guard_msgs` turns the mismatch into a build
error — so `lake build` fails rather than silently degrading the claims in
`README.md`.

The guard binds in both directions: a footprint that grows fails the build, and
so does one that shrinks, since the pinned string no longer matches either way.
So a result whose proof stops depending on something cannot pass silently — the
table has to be brought back into agreement with what the build reports.

The expected strings are copied from the build's own output.  `#print axioms`
sorts the list, and a project axiom would print unqualified inside
`namespace TuranBessel`, so it would appear inside the three standard names
rather than after them.

`Hypergeometric` reaches Mathlib through `Vendor.MathlibPR.PR42760`, whose
declarations are ordinary theorems carrying no axiom of their own; the results
downstream of it are pinned to the same three names as everything else, and a
`sorry` entering that vendored copy would break them here.

## Implementation notes

The guarded results are the "What is proven (unconditionally)" table of
`README.md`, one `#print axioms` per Lean name it lists.  They are the results
the paper claims, not the helpers those proofs consume — a helper is pinned
transitively, since a `sorry` anywhere beneath a guarded result changes that
result's footprint.  The groups follow the section order of
`shields-2026-turan-bessel.tex`, with a `/-! ### -/` header per group.

## References

* `shields-2026-turan-bessel.tex`, and `lean/README.md`, whose per-item status
  table this file pins.
-/

namespace TuranBessel

/-! ### Reciprocal-gamma formulation and positivity phase diagram (`sec:main`) -/

/-- info: 'TuranBessel.coefficientwise_positivity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms coefficientwise_positivity

/-- info: 'TuranBessel.MD_NmatKT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MD_NmatKT

/-- info: 'TuranBessel.DcoeffKT_affine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms DcoeffKT_affine

/-- info: 'TuranBessel.DcoeffKT_degree_one_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms DcoeffKT_degree_one_boundary

/-- info: 'TuranBessel.tauCw_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tauCw_lt_one

/-- info: 'TuranBessel.tauCw_antitone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tauCw_antitone

/-- info: 'TuranBessel.summable_zterm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms summable_zterm

/-- info: 'TuranBessel.Zfun_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Zfun_pos

/-- info: 'TuranBessel.Zfun_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Zfun_sq

/-- info: 'TuranBessel.bessel_schur_ineq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bessel_schur_ineq

/-- info: 'TuranBessel.bessel_schur_matrix_pd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bessel_schur_matrix_pd

/-- info: 'TuranBessel.besselHkappa_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms besselHkappa_eq

/-- info: 'TuranBessel.DcoeffKT_pos_of_gt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms DcoeffKT_pos_of_gt

/-- info: 'TuranBessel.DcoeffKT_nonneg_of_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms DcoeffKT_nonneg_of_ge

/-- info: 'TuranBessel.two_parameter_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms two_parameter_boundary

/-- info: 'TuranBessel.hasSum_turanDetKT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasSum_turanDetKT

/-- info: 'TuranBessel.DcoeffKT_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms DcoeffKT_zero

/-- info: 'TuranBessel.turanDetKT_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms turanDetKT_pos

/-- info: 'TuranBessel.DcoeffKT_pos_iff_of_one_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms DcoeffKT_pos_iff_of_one_le

/-- info: 'TuranBessel.DcoeffKT_nonneg_iff_of_one_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms DcoeffKT_nonneg_iff_of_one_le

/-- info: 'TuranBessel.besselDefectKT_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms besselDefectKT_eq

/-- info: 'TuranBessel.bessel_sharpness_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bessel_sharpness_pos

/-- info: 'TuranBessel.bessel_schur_matrix_KT_pd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bessel_schur_matrix_KT_pd

/-- info: 'TuranBessel.exists_bessel_defect_neg_of_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_bessel_defect_neg_of_lt_one

/-- info: 'TuranBessel.schurMatKT_arg_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms schurMatKT_arg_zero

/-- info: 'TuranBessel.schurMatKT_arg_zero_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms schurMatKT_arg_zero_det

/-- info: 'TuranBessel.schurMat_arg_zero_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms schurMat_arg_zero_rank_one

/-- info: 'TuranBessel.besselGfun_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms besselGfun_eq

/-- info: 'TuranBessel.besselGfun_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms besselGfun_pos

/-- info: 'TuranBessel.besselPfun_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms besselPfun_eq

/-- info: 'TuranBessel.besselHfun_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms besselHfun_eq

/-- info: 'TuranBessel.besselDet_eq_turanDet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms besselDet_eq_turanDet

/-! ### Classical scalar Bessel directions (`sec:scalar`) -/

/-- info: 'TuranBessel.Hratio_pos_iff_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hratio_pos_iff_ratio

/-- info: 'TuranBessel.Hratio_one_pos_iff_amos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hratio_one_pos_iff_amos

/-- info: 'TuranBessel.Hratio_eq_turan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hratio_eq_turan

/-- info: 'TuranBessel.Hratio_pos_of_one_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hratio_pos_of_one_le

/-- info: 'TuranBessel.besselHkappa_pos_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms besselHkappa_pos_iff

/-- info: 'TuranBessel.schur_boundary_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms schur_boundary_det

/-! ### Reciprocal-gamma convolution and the coefficient calculus (`sec:coefficients`) -/

/-- info: 'TuranBessel.gamma_convolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gamma_convolution

/-- info: 'TuranBessel.poch_vandermonde' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms poch_vandermonde

/-- info: 'TuranBessel.sred_eq_sweight_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sred_eq_sweight_mul

/-- info: 'TuranBessel.hasSum_turanDet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasSum_turanDet

/-- info: 'TuranBessel.hasSum_turanDetCoeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasSum_turanDetCoeff

/-! ### Microcanonical Bessel fibers and canonical averaging (`subsec:microcanonical`) -/

/-- info: 'TuranBessel.normalizedTuran_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms normalizedTuran_eq

/-- info: 'TuranBessel.covariance_ineq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms covariance_ineq

/-- info: 'TuranBessel.hasSum_pairPMF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasSum_pairPMF

/-- info: 'TuranBessel.sum_condPMF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sum_condPMF

/-- info: 'TuranBessel.NmatKT_eq_condExp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NmatKT_eq_condExp

/-- info: 'TuranBessel.NmatKT_eq_baseline_sub_cov' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NmatKT_eq_baseline_sub_cov

/-- info: 'TuranBessel.NmatKT_eq_ellUV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NmatKT_eq_ellUV

/-- info: 'TuranBessel.normalizedTuran_eq_pairExp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms normalizedTuran_eq_pairExp

/-! ### Four-copy determinant sectors (`subsec:four-copy`) -/

/-- info: 'TuranBessel.SymMat.MD_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SymMat.MD_nonneg

/-- info: 'TuranBessel.SymMat.MD_pos_of_psd_pd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SymMat.MD_pos_of_psd_pd

/-- info: 'TuranBessel.hasSum_fourPMF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasSum_fourPMF

/-- info: 'TuranBessel.DcoeffKT_eq_kExp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms DcoeffKT_eq_kExp

/-- info: 'TuranBessel.besselDefect_eq_sectorAverage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms besselDefect_eq_sectorAverage

/-- info: 'TuranBessel.besselDefectKT_eq_sectorAverage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms besselDefectKT_eq_sectorAverage

/-! ### Gram structure and the exceptional matrix (`subsec:gram`) -/

/-- info: 'TuranBessel.NmatS_eq_gram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NmatS_eq_gram

/-- info: 'TuranBessel.Mmat_eq_gram_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Mmat_eq_gram_smul

/-- info: 'TuranBessel.NmatS_pd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NmatS_pd

/-- info: 'TuranBessel.Nmat_pd_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Nmat_pd_two

/-- info: 'TuranBessel.Nmat_pd_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Nmat_pd_one

/-- info: 'TuranBessel.M1_inertia_trichotomy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms M1_inertia_trichotomy

/-- info: 'TuranBessel.Nmat_one_not_psd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Nmat_one_not_psd

/-- info: 'TuranBessel.Nmat_one_pd_of_fM1_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Nmat_one_pd_of_fM1_pos

/-- info: 'TuranBessel.trigamma_gt_inv_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms trigamma_gt_inv_sharp

/-- info: 'TuranBessel.trigamma_lt_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms trigamma_lt_upper

/-- info: 'TuranBessel.tsum_mul_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tsum_mul_sq_le

/-! ### The exceptional degree and endpoint sufficiency (`subsec:endpoint-sufficiency`) -/

/-- info: 'TuranBessel.MDkappa_uniform_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MDkappa_uniform_iff

/-- info: 'TuranBessel.MDkappa_neg_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MDkappa_neg_exists

/-- info: 'TuranBessel.MDkappa_ge_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MDkappa_ge_pos

/-- info: 'TuranBessel.Dcoeff_two_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Dcoeff_two_pos

/-! ### Canonical--microcanonical phase geometry (`sec:phase`) -/

/-- info: 'TuranBessel.trigamma_lt_cubic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms trigamma_lt_cubic

/-- info: 'TuranBessel.sq_mul_trigamma_gt_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sq_mul_trigamma_gt_one

/-- info: 'TuranBessel.cCrit_gt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cCrit_gt

/-! ### Critical wall fan and equivalence of ensembles (`sec:scaling`) -/

/-- info: 'TuranBessel.sweight_eq_gamma_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sweight_eq_gamma_ratio

/-- info: 'TuranBessel.cCrit_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cCrit_mem

/-- info: 'TuranBessel.cCrit_strictAnti_and_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cCrit_strictAnti_and_range

/-- info: 'TuranBessel.trigamma_sq_add_tetragamma_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms trigamma_sq_add_tetragamma_pos

/-- info: 'TuranBessel.hasDerivAt_trigamma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasDerivAt_trigamma

/-- info: 'TuranBessel.abs_sweight_div_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms abs_sweight_div_sub_le

/-- info: 'TuranBessel.hyperWeight_variance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hyperWeight_variance

/-- info: 'TuranBessel.hyperWeight_second_moment_scaled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hyperWeight_second_moment_scaled

/-! ### The exposed one-particle wall (`app:boundary-proof`) -/

/-- info: 'TuranBessel.det_N1_boundary_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms det_N1_boundary_eq

/-- info: 'TuranBessel.det_N1_boundary_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms det_N1_boundary_nonneg

/-- info: 'TuranBessel.sStar_add_c_two_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sStar_add_c_two_pos

/-- info: 'TuranBessel.P2boundary_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms P2boundary_pos

/-- info: 'TuranBessel.boundary_positivity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms boundary_positivity

/-! ### Beyond the positive-series domain (`app:continuation`) -/

/-- info: 'TuranBessel.Dcoeff_two_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Dcoeff_two_neg

end TuranBessel
