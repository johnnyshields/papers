/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.FTMinModulus.Propositions
import ForgacsTran.FTMinModulus.ClusterExpansion
import ForgacsTran.FTMinModulus.RoucheModel
import ForgacsTran.FTMinModulus.ScaleMatching
import ForgacsTran.FTMinModulus.UpperEndpoint

/-!
# Forgács--Tran minimum modulus and the endpoint characterization

Proved here, with `Forgacs2017RationalDenominator`'s own numbering attributed:

## Main statements

* `norm_eval_posRootPoly_le_of_norm_eq`, `..._lt_of_norm_eq` — on the circle
  `|t| = s` the modulus of a polynomial with positive real zeros is minimized at
  the positive real point, strictly at every other point.  This is the magnitude
  comparison `Forgacs2017RationalDenominator` Prop. 1 opens with, in its Eq. (28).
* `ftCritical_eval_neg` — `sP'(s) - rP(s) < 0` below the first positive critical
  point, which is that proof's "the derivative does not vanish on `(0,t_a)`".
* `strictMonoOn_negDivPow` — hence `-P(s)/s^r` is strictly increasing there, and
  `negDivPow_lt_of_mem_Ioo` is the consequence used to exclude real nonnegative
  zeros.
* `norm_zeta_eq_norm_div` — `Forgacs2017RationalDenominator` Prop. 2 is Prop. 1
  renormalized: `|ζ_k| = |t_k|/τ`, so `|ζ_k| > 1` and `|t_k| > τ` say the same
  thing.

* `exists_ftDen_root_near_model_root` and its `..._eventually` — Rouché against
  the model `q(x_1)(t-x_1)^ρ + z_0x_1^rδ^ρ`, with the count read off the model
  side, so each of the `ρ` directions carries a root of the pencil.
* `exists_cluster_member_expansion_family` — that root expands as
  `eq:lower-cluster-expansion` to `O(δ²)` *at its own direction*: the index is
  chosen by the Rouché step, and `clusterAlpha_sep` matches it to the one the
  ratio step produces.
* `exists_cluster_normalized_expansion_of_pencil` — dividing by the branch
  radius gives `hexp₀`'s
  `ζ_i(δ) = 1 + [(cos(π/ρ) - ω_i)/sin(π/ρ)]δ + O(δ²)`, with the members produced
  rather than taken as given.

* `eval_div_pow_eq_of_isRoot` — their Eq. (28).
* `prod_norm_sub_le_of_norm_le`, `norm_sub_le_of_prod_le` — the containment of a
  hypothetical zero in `C₁ ∩ C₂`.  Their text justifies it by "considering the
  magnitudes of both sides", which by itself gives only that *some* distance
  shrinks; what makes it the smallest zero is that the difference of squared
  distances is affine in the zero and nonpositive at the origin, so a violation
  at the smallest propagates to all of them and contradicts the product
  inequality.
* `sin_numerator_nonneg` — the numerator of the derivative of
  `sin θ / sin((r-1)θ)`, which their text says "vanishes when `θ = 0` and is
  nondecreasing"; it is nondecreasing because its own derivative is
  `r(r-2)(cos((r-2)θ) - cos(rθ))` and `cos` is antitone on `[0,π]`.

## Implementation notes

Also here is their Prop. 3, Case 2, at both multiplicities.  The `ρ = 1` half is
what `thm:FT-geometry` consumes at the lower endpoint when the smallest zero of
`P` is simple.  The `ρ > 1` half is the cluster, and it is assembled rather than
assumed:

Five inputs stay hypotheses *here*, none of them this module's object.  Four are
about the principal branch — that `t_p(δ)` is a root of the same pencil member,
its own `O(δ²)` expansion, `τ = ‖t_p‖`, and `τ ≥ x_1/2`.  The fifth is one scalar
identity, `q(x_1)α_1^ρ + z_0x_1^r = 0`, saying the cluster directions *are* the
model's own roots.  **All five are discharged in `FTClusterSupply`**, which sits
above `FTGeometryAssembly` where the branch objects live, so
`FTClusterSupply.cluster_normalized_expansion_at_branch` carries no hypothesis
about the branch at all.  `scripts/check_cluster_model_roots.py` measures the
model identity independently.

**Case 3 is not claimed**, and `hexp₁` still carries it.

Their Prop. 1's own three steps are here as well:

What remains of Prop. 1 is its closing step, where the argument of the
hypothetical zero is fed through their Eqs. (6)--(8) to a branch index `l`, and
`τ(θ*; l) ≤ τ ≤ τ(θ; l)` with monotonicity of `z(·; l)` forces `θ* = θ`.  That
step consumes their Lemmas 3--6 and Remark 4, which are another lane's; this
module claims none of it.

Sorry-free.

## References

Formalizes results of `Forgacs2017RationalDenominator` that
`../shields-2026-forgacs-tran-numerators.tex` consumes rather than proves —
`thm:FT-geometry` cites them as `[Props.~1--2]` and `subsec:FT-geometry` reads
the endpoints off `t^{r-1}(rQ(t) - tQ'(t))`.

## Tags

minimum modulus, endpoint characterization, Forgacs-Tran interval

## Implementation notes

This module is a re-export.  At 3,894 lines it sat well over Mathlib's 1,500-line
cap, so it is cut into five submodules by mathematical object and imported here in
the order the argument runs:

* `FTMinModulus.Propositions` — Props 1 and 2, and Lemma 6's image statement.
* `FTMinModulus.ClusterExpansion` — Prop. 3 Case 2 and the `ρ`-th-root localization.
* `FTMinModulus.RoucheModel` — the endpoint multiplicity and the Rouché model.
* `FTMinModulus.ScaleMatching` — domination on the small circle, and the two scales.
* `FTMinModulus.UpperEndpoint` — Prop. 3 Case 3 and the endpoint limits of `z`.

Importing `ForgacsTran.FTMinModulus` still brings in all of it, so nothing that
cited this module had to change.
-/
