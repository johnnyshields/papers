/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.MetricSpace.Bounded

/-!
# A rational function is bounded outside a disc containing its poles

Let `P, Q` be polynomials over a proper normed field with `Q` free of zeros on the closed exterior
`{z | r ≤ ‖z‖}`.  If `deg P ≤ deg Q` then `P/Q` is **bounded** on that exterior.

The exterior is closed but not compact, so continuity alone gives nothing; the content is that the
degree comparison controls the far field.  The two regimes are glued along a radius:

* Far field.  `Polynomial.isBigO_cobounded_of_degree_le` turns `deg P ≤ deg Q` into
  `‖P.eval z‖ ≤ c‖Q.eval z‖` outside a bounded set, and dividing by `‖Q.eval z‖ ≠ 0` bounds the
  ratio by `c` there.
* Near field.  What is left is a closed **annulus**, compact in a proper space
  (`isCompact_annulus`), on which the ratio is continuous.

The degree hypothesis is sharp rather than convenient: `deg Q < deg P` forces `‖P/Q‖` to be
unbounded on *every* exterior (`not_bddAbove_norm_eval_div_of_degree_lt`).  Equality of degrees is
included because the ratio then tends to the quotient of leading coefficients, which is bounded
without being small — so the hypothesis is `≤` and not `<`.

## Main results

* `Shields.isCompact_annulus` — the closed annulus `r ≤ ‖z‖ ≤ s` is compact in a proper space.
* `Shields.exists_bound_eval_div_of_degree_le` — `P/Q` is bounded on `{r ≤ ‖z‖}` when
  `deg P ≤ deg Q` and `Q` has no zero there.
* `Shields.not_bddAbove_norm_eval_div_of_degree_lt` — sharpness of the degree hypothesis.

## Implementation notes

`Filter.hasBasis_cobounded_norm` is what converts the `IsBigO`'s `∀ᶠ … in cobounded` into an
explicit radius, and it needs no properness; properness enters only for the compact annulus.

The sharpness statement is over a `NontriviallyNormedField`, which is what makes
`cobounded 𝕜` a `NeBot` filter and so supplies the witness.  Over a field carrying the trivial
absolute value there are no points of large norm and the claim would be vacuous.

## Tags

polynomial, rational function, bounded, degree, cobounded
-/

open Filter Bornology Metric

namespace Shields

variable {𝕜 : Type*} [NormedField 𝕜]

/-! ### The closed annulus -/

/-- The closed annulus `r ≤ ‖z‖ ≤ s` is compact in a proper space.  Unlike a closed ball or a
sphere it is not already named in the library, and it is what remains of a closed exterior once a
far-field radius has been chosen. -/
theorem isCompact_annulus [ProperSpace 𝕜] (r s : ℝ) :
    IsCompact {z : 𝕜 | r ≤ ‖z‖ ∧ ‖z‖ ≤ s} := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · exact (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  · refine (Metric.isBounded_closedBall (x := (0 : 𝕜)) (r := s)).subset fun z hz => ?_
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz.2

/-! ### The bound -/

/-- **A rational function is bounded outside a disc containing all of its poles.**  Two
hypotheses: `Q` has no zero on the exterior `{r ≤ ‖z‖}`, so the quotient is defined there, and the
numerator's degree does not exceed the denominator's, which is what controls the behavior at
infinity.

The conclusion carries `0 ≤ M` so that it can be consumed where a nonnegative constant is wanted
without a further `max`. -/
theorem exists_bound_eval_div_of_degree_le [ProperSpace 𝕜] {P Q : Polynomial 𝕜}
    (hdeg : P.degree ≤ Q.degree) {r : ℝ} (hQ : ∀ z : 𝕜, r ≤ ‖z‖ → Q.eval z ≠ 0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : 𝕜, r ≤ ‖z‖ → ‖P.eval z / Q.eval z‖ ≤ M := by
  -- Far field: the degree comparison, made explicit at a radius `R₂`.
  obtain ⟨c, hc⟩ := Asymptotics.isBigO_iff.mp
    (Polynomial.isBigO_cobounded_of_degree_le (P := P) (Q := Q) hdeg)
  obtain ⟨R₂, -, hfar⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.mp hc
  -- Near field: the annulus between `r` and the far-field radius.
  have hcont : ContinuousOn (fun z : 𝕜 => P.eval z / Q.eval z)
      {z : 𝕜 | r ≤ ‖z‖ ∧ ‖z‖ ≤ max r R₂} :=
    P.continuousOn.div Q.continuousOn fun z hz => hQ z hz.1
  obtain ⟨M₁, hM₁⟩ := (isCompact_annulus r (max r R₂)).exists_bound_of_continuousOn hcont
  refine ⟨max (max c M₁) 0, le_max_right _ _, fun z hz => ?_⟩
  rcases le_or_gt (max r R₂) ‖z‖ with hfarz | hnearz
  · have hQz : Q.eval z ≠ 0 := hQ z hz
    rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr hQz)]
    refine (hfar ((le_max_right r R₂).trans hfarz)).trans ?_
    exact mul_le_mul_of_nonneg_right ((le_max_left c M₁).trans (le_max_left _ _)) (norm_nonneg _)
  · exact (hM₁ z ⟨hz, hnearz.le⟩).trans ((le_max_right c M₁).trans (le_max_left _ _))

/-! ### Sharpness of the degree hypothesis -/

/-- The degree hypothesis of `exists_bound_eval_div_of_degree_le` cannot be weakened: once the
numerator outgrows the denominator, no exterior carries a bound.

The witness is produced from the filter rather than by hand — beyond the finitely many zeros of
`Q`, and far enough out, `‖Q.eval z‖ ≤ ε‖P.eval z‖` for `ε` as small as one pleases, so the ratio
exceeds `1/ε`.  All three conditions hold eventually along `cobounded 𝕜`, which is `NeBot`. -/
theorem not_bddAbove_norm_eval_div_of_degree_lt {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {P Q : Polynomial 𝕜} (hdeg : Q.degree < P.degree) (hQ0 : Q ≠ 0) (r : ℝ) :
    ¬ BddAbove ((fun z : 𝕜 => ‖P.eval z / Q.eval z‖) '' {z : 𝕜 | r ≤ ‖z‖}) := by
  rintro ⟨M, hM⟩
  have hM0 : (0 : ℝ) ≤ max M 0 := le_max_right M 0
  have hMpos : (0 : ℝ) < max M 0 + 1 := by linarith
  set ε : ℝ := 1 / (max M 0 + 1) with hε
  have hεpos : 0 < ε := by rw [hε]; exact div_pos one_pos hMpos
  have hsmall : ∀ᶠ z in cobounded 𝕜, ‖Q.eval z‖ ≤ ε * ‖P.eval z‖ :=
    Asymptotics.isLittleO_iff.mp
      (Polynomial.isLittleO_cobounded_of_degree_lt (P := Q) (Q := P) hdeg) hεpos
  have hroots : ∀ᶠ z in cobounded 𝕜, Q.eval z ≠ 0 :=
    Bornology.isBounded_def.mp (Polynomial.finite_setOfPred_isRoot hQ0).isBounded
  obtain ⟨z, ⟨hkey, hzQ⟩, hzr⟩ :=
    ((hsmall.and hroots).and (eventually_cobounded_le_norm (E := 𝕜) r)).exists
  have hbig : max M 0 + 1 ≤ ‖P.eval z / Q.eval z‖ := by
    rw [norm_div, le_div_iff₀ (norm_pos_iff.mpr hzQ)]
    calc (max M 0 + 1) * ‖Q.eval z‖
        ≤ (max M 0 + 1) * (ε * ‖P.eval z‖) := mul_le_mul_of_nonneg_left hkey hMpos.le
      _ = ‖P.eval z‖ := by rw [hε]; field_simp
  have hin : ‖P.eval z / Q.eval z‖ ≤ M := hM (Set.mem_image_of_mem _ hzr)
  have := le_max_left M 0
  linarith

/-! ### Axiom footprint -/

/-- info: 'Shields.exists_bound_eval_div_of_degree_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_bound_eval_div_of_degree_le

/-- info: 'Shields.not_bddAbove_norm_eval_div_of_degree_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms not_bddAbove_norm_eval_div_of_degree_lt

end Shields
