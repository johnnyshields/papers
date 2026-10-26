/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
import SkewMarkedFactor.FactorRecovery
import SkewMarkedFactor.MixedVanishing
import SkewMarkedFactor.MarkTransport
import SkewMarkedFactor.TwoRowRigidity

/-!
# Common-period comparison in an actual marked fiber

`thm:transport` and `cor:two-row` of
`shields-2026-skew-marked-factor.tex`.
The comparison starts from Schur-equal parent functions, not equal cell sets.
The period and the second proper chart are supplied.  The only standing
rigidity assumption concerns the connected Schur class of the ordinary inner.
-/

namespace SkewMarkedFactor
open Gluing Gluing.Plan

/-- The standing hypothesis in common-period comparison. -/
def ConnectedInnerRigid (E : Diagram) : Prop :=
  ∀ U : Diagram, IsConnectedSkew U → cellSchur U = cellSchur E →
    (∃ t, U = translate t E) ∨ ∃ t, U = translate t (rotate E)

/-- An ordinary inner with two actual rows supplies the rigidity hypothesis. -/
theorem connectedInnerRigid_of_two_rows {E : Diagram} (hE : IsConnectedSkew E)
    (hrows : numRows E = 2) : ConnectedInnerRigid E :=
  fun _ hU hs => two_row_inner_rigidity hE hrows hU hs

/-- Fixed-inner ordinary comparison uses the atlas and the antitranspose gauge. -/
private theorem fixed_inner_fiber_eq {η θ : MarkedInner}
    (hη : η.IsReadoutLegal) (hθ : θ.IsReadoutLegal)
    (hoη : η.IsOrdinary) (hoθ : θ.IsOrdinary)
    (hE : θ.E = η.E) (hp : θ.period = η.period) {Q R : Lambda}
    (hQ : (if θ.case = .b then schurInvolution R else R) =
      (if η.case = .b then schurInvolution Q else Q)) :
    fiberClass cellSchur θ R = fiberClass cellSchur η Q := by
  classical
  rcases hoη.cases with ha | hb <;> rcases hoθ.cases with ha' | hb'
  · have hm := ordinary_mark_unique hη hθ hE hp (ha'.trans ha.symm)
    have hr : R = Q := by simpa [ha, ha'] using hQ
    rw [hm, hr]
  · have hr : R = schurInvolution Q := by
      have hh := congrArg schurInvolution hQ
      exact (schurInvolution_involutive R).symm.trans (by simpa [ha, hb'] using hh)
    rw [hr]
    exact (fiberClass_gauge hE.symm ha hb'
      (ordinary_mark_displacement hη hθ hE hp ha hb') Q).symm
  · have hr : R = schurInvolution Q := by simpa [hb, ha'] using hQ
    have hv := ordinary_mark_displacement hθ hη hE.symm hp.symm ha' hb
    have hg := fiberClass_gauge hE ha' hb hv R
    rw [hr, schurInvolution_involutive] at hg
    rw [hr]
    exact hg
  · have hm := ordinary_mark_unique hη hθ hE hp (hb'.trans hb.symm)
    have hr : R = Q := by
      apply schurInvolution_involutive.injective
      simpa [hb, hb'] using hQ
    rw [hm, hr]

/-- A mixed chart is excluded by equality with the genuine nonzero ordinary derivative. -/
theorem ordinary_of_equal_parent_at_period {χ θ : Chart} (hχ : χ.IsProperOrdinary)
    (hθ : θ.IsProperReadoutLegal)
    (hP : cellSchur θ.parent = cellSchur χ.parent) (hp : θ.period = χ.period) :
    θ.IsProperOrdinary := by
  refine ⟨hθ, ?_⟩
  intro hm
  have hz := mixed_period_derivative_zero hθ.2.2.2 hm hθ.1 (k := 1) (by decide)
  simp only [one_mul] at hz
  change pDeriv θ.period.toNat (cellSchur θ.parent) = 0 at hz
  rw [hP, hp] at hz
  exact ordinary_parent_first_derivative_ne_zero hχ hz

set_option backward.isDefEq.respectTransparency false in
/-- Recovery and rigidity identify actual fiber classes, allowing different parent cell diagrams. -/
theorem common_period_fiber_eq {χ θ : Chart} (hχ : χ.IsProperOrdinary)
    (hrigid : ConnectedInnerRigid χ.ω.E) (hθ : θ.IsProperReadoutLegal)
    (hP : cellSchur θ.parent = cellSchur χ.parent) (hp : θ.period = χ.period) :
    fiberClass cellSchur θ.ω (cellSchur θ.D) =
      fiberClass cellSchur χ.ω (cellSchur χ.D) := by
  classical
  have hoθ := ordinary_of_equal_parent_at_period hχ hθ hP hp
  have hi : cellSchur θ.ω.E = cellSchur χ.ω.E := by
    rw [← factor_recovery_inner hoθ, ← factor_recovery_inner hχ, hP, hp]
  have houter : adjustedOuter θ = adjustedOuter χ := by
    rw [← factor_recovery_outer_primitive hoθ,
      ← factor_recovery_outer_primitive hχ, hP, hp]
  have hη := hχ.1.2.2.2
  have hθlegal := hθ.2.2.2
  have hθconn := MarkAtlas.inner_connected hθlegal
  rcases hrigid θ.ω.E hθconn hi with ⟨t, ht⟩ | ⟨t, ht⟩
  · have hf : fiberClass cellSchur θ.ω (cellSchur θ.D) =
        fiberClass cellSchur (χ.ω.translate t) (cellSchur χ.D) := by
      apply fixed_inner_fiber_eq (hη.translate t) hθlegal hχ.2 hoθ.2
      · exact ht
      · exact hp
      · simpa only [adjustedOuter, MarkedInner.translate_case] using houter
    rw [hf, fiberClass_cellSchur_translate_inner]
  · have hcase : χ.ω.rotate.case = χ.ω.case := by
      rcases hχ.2.cases with hc | hc <;>
        simp [MarkedInner.rotate, hc, AttachCase.rotate]
    have hf : fiberClass cellSchur θ.ω (cellSchur θ.D) =
        fiberClass cellSchur (χ.ω.rotate.translate t) (cellSchur χ.D) := by
      apply fixed_inner_fiber_eq (hη.rotate.translate t) hθlegal hχ.2.rotate hoθ.2
      · exact ht
      · exact hp
      · simpa only [adjustedOuter, MarkedInner.translate_case, hcase] using houter
    rw [hf, fiberClass_cellSchur_translate_inner, fiberClass_rotate]

/-- A supplied proper chart places its actual parent translation in its actual marked fiber. -/
theorem proper_chart_mem_fiber {χ : Chart} (hχ : χ.IsProperReadoutLegal)
    {F : Diagram} (hF : χ.IsChartOf F) :
    F ∈ fiberClass cellSchur χ.ω (cellSchur χ.D) := by
  obtain ⟨t, ht⟩ := hF
  exact ⟨χ.parent, ⟨χ.D, hχ.1, hχ.2.1, rfl, Or.inl rfl⟩, t, ht⟩

/-- `thm:transport`: Schur-equal parents with supplied common-period charts
belong to one real marked fiber, up to translation, transported rotation and ordinary gauge.
The mate's connectedness is not needed once its proper chart is supplied. -/
theorem common_period_transport {χ θ : Chart} {F H : Diagram}
    (hχ : χ.IsProperOrdinary) (hF : χ.IsChartOf F)
    (hrigid : ConnectedInnerRigid χ.ω.E)
    (hs : cellSchur H = cellSchur F) (hθ : θ.IsProperReadoutLegal)
    (hchart : θ.IsChartOf H) (hp : θ.period = χ.period) :
    F ∈ fiberClass cellSchur χ.ω (cellSchur χ.D) ∧
      H ∈ fiberClass cellSchur χ.ω (cellSchur χ.D) := by
  have hP : cellSchur θ.parent = cellSchur χ.parent := by
    obtain ⟨tF, htF⟩ := hF
    obtain ⟨tH, htH⟩ := hchart
    simpa only [htF, htH, cellSchur_translate] using hs
  have hf := common_period_fiber_eq hχ hrigid hθ hP hp
  refine ⟨proper_chart_mem_fiber hχ.1 hF, ?_⟩
  rw [← hf]
  exact proper_chart_mem_fiber hθ hchart

/-- `cor:two-row`: two actual inner rows discharge rigidity; the connected outer is unrestricted. -/
theorem two_row_common_period_transport {χ θ : Chart} {F H : Diagram}
    (hχ : χ.IsProperOrdinary) (hF : χ.IsChartOf F)
    (hrows : numRows χ.ω.E = 2)
    (hs : cellSchur H = cellSchur F) (hθ : θ.IsProperReadoutLegal)
    (hchart : θ.IsChartOf H) (hp : θ.period = χ.period) :
    F ∈ fiberClass cellSchur χ.ω (cellSchur χ.D) ∧
      H ∈ fiberClass cellSchur χ.ω (cellSchur χ.D) :=
  common_period_transport hχ hF
    (connectedInnerRigid_of_two_rows (MarkAtlas.inner_connected hχ.1.2.2.2) hrows)
    hs hθ hchart hp

/-- A Schur-equal ordinary chart cannot have a positive multiple of a mixed period. -/
theorem mixed_excludes_divisible_ordinary {χ θ : Chart} (hχ : χ.IsProperOrdinary)
    (hθ : θ.IsProperReadoutLegal) (hm : θ.ω.case.IsMixed)
    (hP : cellSchur θ.parent = cellSchur χ.parent) {k : ℕ} (hk : 0 < k)
    (hp : χ.period.toNat = k * θ.period.toNat) : False := by
  have hz := mixed_period_derivative_zero hθ.2.2.2 hm hθ.1 hk
  change pDeriv (k * θ.period.toNat) (cellSchur θ.parent) = 0 at hz
  rw [hP, ← hp] at hz
  exact ordinary_parent_first_derivative_ne_zero hχ hz

/-- Every nonempty skew outer in an ordinary legal composition has a nonzero
first period derivative. -/
theorem ordinary_nonempty_first_derivative_ne_zero {η : MarkedInner}
    (hη : η.IsReadoutLegal) (ho : η.IsOrdinary) {D : Diagram}
    (hD : IsSkew D) (hne : D.Nonempty) :
    pDeriv η.period.toNat (cellSchur (η.compose D)) ≠ 0 := by
  intro hz
  have hn := modified_normalization_nonempty hη ho hD hne
  have hk : pDeriv η.period.toNat (normalizationFactor η D) = 0 := by
    simpa only [one_mul] using normalization_killed hη D (m := 1) (by decide)
  have hfirst : deltaAt η.period.toNat 1 (modifiedValue η D) = 0 := by
    rw [deltaAt_succ, deltaAt_zero, hn, Derivation.leibniz, hk, hz]
    simp
  have hword := ordinary_diagram_word_action hη ho hD
    (ν := List.replicate D.card 1) (by
      intro m hm
      have he : m = 1 := List.eq_of_mem_replicate hm
      omega)
  rw [modified_terminal_word] at hword
  have hlast : deltaAt η.period.toNat D.card (modifiedValue η D) =
      xi η ^ D.card * MvPolynomial.C (standardTableauCount D : ℚ) := by
    simpa [deltaAt, List.map_replicate] using hword
  have hzero : deltaAt η.period.toNat D.card (modifiedValue η D) = 0 := by
    have hp : 0 < D.card := Finset.card_pos.mpr hne
    have he : D.card = 1 + (D.card - 1) := by omega
    rw [he]
    exact deltaAt_after_zero η.period.toNat 1 _ _ hfirst
  have hscalar : MvPolynomial.C (standardTableauCount D : ℚ) ≠ (0 : Lambda) := by
    apply MvPolynomial.C_ne_zero.mpr
    exact ne_of_gt (show (0 : ℚ) < standardTableauCount D by
      exact_mod_cast standardTableauCount_pos D)
  exact (mul_ne_zero (pow_ne_zero _ (xi_ne_zero hη ho)) hscalar) (hzero ▸ hlast).symm

/-- The mixed-period exclusion requires no properness or lower size bound on either factor. -/
theorem mixed_excludes_ordinary_multiple {η θ : MarkedInner}
    (hη : η.IsReadoutLegal) (ho : η.IsOrdinary) {D X : Diagram}
    (hD : IsSkew D) (hne : D.Nonempty) (hθ : θ.IsReadoutLegal)
    (hm : θ.case.IsMixed) (hX : IsConnectedSkew X)
    (hP : cellSchur (θ.compose X) = cellSchur (η.compose D))
    {k : ℕ} (hk : 0 < k) (hp : η.period.toNat = k * θ.period.toNat) : False := by
  have hz := mixed_period_derivative_zero hθ hm hX hk
  rw [hP, ← hp] at hz
  exact ordinary_nonempty_first_derivative_ne_zero hη ho hD hne hz

end SkewMarkedFactor
