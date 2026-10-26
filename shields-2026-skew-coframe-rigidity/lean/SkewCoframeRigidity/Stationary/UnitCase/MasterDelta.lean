/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Stationary.UnitCase.Setup
import SkewCoframeRigidity.Stationary.UnitCase.Masks


/-!
# The first `ε`-coefficient of the difference of two coframes

Formalizes the evaluation of `δ`, the coefficient of `ε` in `Ct - Gt`, in the final step of the unit
case of `sc:positive-power` in `shields-2026-skew-coframe-rigidity.tex`: at a unit position it is
a nonzero multiple of `[Ū g]_b`, and it satisfies the row equations of the core.  If it vanishes, the
two diagrams have the same unit positions.
-/

namespace SkewCoframeRigidity.UnitCase

open SkewCofactorIndependence SkewCoframeRigidity SkewCoframeRigidity.Coframe
  SkewCoframeRigidity.UnitRestoration Polynomial

private theorem theta_ne_zero : cohLetters 0 ≠ 0 := by
  unfold cohLetters
  refine (map_ne_zero_iff _ (IsFractionRing.injective CohRing CohField)).2 ?_
  exact MvPolynomial.X_ne_zero 0

/-- The coefficient of `AH * G'` at `k`, as the coefficient of `G'` plus `ε` times the
coefficient of `Ū G'`, written as a sum over the antidiagonal. -/
private theorem coeff_AH_mul (G' : Polynomial CohField[X]) (k : ℕ) :
    PowerSeries.coeff k (AH * (G' : PowerSeries CohField[X])) =
      G'.coeff k + Polynomial.X * ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k,
        Polynomial.C (PowerSeries.coeff p.1 Ubar) * G'.coeff p.2 := by
  unfold AH
  rw [add_mul, one_mul, mul_assoc, map_add, PowerSeries.coeff_C_mul, Polynomial.coeff_coe,
    PowerSeries.coeff_mul]
  simp [PowerSeries.coeff_map, Polynomial.coeff_coe]

/-- The first `ε`-coefficient of the row equation of a coframe numerator `liftK (β F) + ε a`. -/
private theorem coeff_AH_lift {β : CohField} (F : CohField[X]) (a : Polynomial CohField[X])
    (k : ℕ) :
    (PowerSeries.coeff k (AH * ((liftK (Polynomial.C β * F) + Polynomial.C Polynomial.X * a :
      Polynomial CohField[X]) : PowerSeries CohField[X]))).coeff 1 =
      (a.coeff k).coeff 0 + β * PowerSeries.coeff k (Ubar * (F : PowerSeries CohField)) := by
  rw [coeff_AH_mul]
  have hq : ∀ q, (liftK (Polynomial.C β * F) + Polynomial.C Polynomial.X * a :
      Polynomial CohField[X]).coeff q =
      Polynomial.C (β * F.coeff q) + Polynomial.X * a.coeff q := by
    intro q
    simp [liftK, Polynomial.coeff_map]
  simp_rw [hq]
  have hs : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k,
      Polynomial.C (PowerSeries.coeff p.1 Ubar) * Polynomial.C (β * F.coeff p.2) =
      Polynomial.C (β * PowerSeries.coeff k (Ubar * (F : PowerSeries CohField))) := by
    rw [PowerSeries.coeff_mul, Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [Polynomial.coeff_coe, map_mul]
    ring
  simp only [mul_add, Finset.sum_add_distrib, hs, Polynomial.coeff_add, Polynomial.coeff_C,
    Polynomial.coeff_X_mul]
  simp

/-- The positive normalized series is `ϑ⁻¹` times the unit-free series. -/
private theorem coeff_Ubar_mul (F : PowerSeries CohField) (k : ℕ) :
    PowerSeries.coeff k (Ubar * F) =
      (cohLetters 0)⁻¹ * PowerSeries.coeff k (unitFreeSeries * F) := by
  have h : Ubar = PowerSeries.C (cohLetters 0)⁻¹ * unitFreeSeries := by
    ext k
    simp only [Ubar, unitFreeSeries, PowerSeries.coeff_mk, PowerSeries.coeff_C_mul, normLetters]
    split_ifs <;> simp [div_eq_inv_mul]
  rw [h, mul_assoc, PowerSeries.coeff_C_mul]

/-- At a position carrying a row equation, the first `ε`-coefficient of a coframe numerator is
`-β [Ū g]_b`. -/
theorem coeff_one_of_row {β : CohField} (g : CohField[X]) (G' a : Polynomial CohField[X])
    (hG : G' = liftK (Polynomial.C β * g) + Polynomial.C Polynomial.X * a) (b₀ : ℕ)
    (hrow : PowerSeries.coeff b₀ (AH * (G' : PowerSeries CohField[X])) = 0) :
    (G'.coeff b₀).coeff 1 = -(β * PowerSeries.coeff b₀ (Ubar * (g : PowerSeries CohField))) := by
  subst hG
  have h1 := coeff_AH_lift (β := β) g a b₀
  rw [hrow] at h1
  have h2 : ((liftK (Polynomial.C β * g) + Polynomial.C Polynomial.X * a :
      Polynomial CohField[X]).coeff b₀).coeff 1 = (a.coeff b₀).coeff 0 := by
    simp [liftK, Polynomial.coeff_map]
  rw [h2]
  simp only [Polynomial.coeff_zero] at h1
  linear_combination -h1

/-- The first `ε`-coefficient `δ` of `Ct - Gt` satisfies the row equations of `Ū` at every position
where both `Gt` and `Ct` have no coefficient and both row equations hold. -/
theorem delta_row_zero {β : CohField} (g : CohField[X]) (G' C' a b : Polynomial CohField[X])
    (hG : G' = liftK (Polynomial.C β * g) + Polynomial.C Polynomial.X * a)
    (hC : C' = liftK (Polynomial.C β * g) + Polynomial.C Polynomial.X * b) (i : ℕ)
    (hGi : G'.coeff i = 0) (hCi : C'.coeff i = 0)
    (hrowG : PowerSeries.coeff i (AH * (G' : PowerSeries CohField[X])) = 0)
    (hrowC : PowerSeries.coeff i (AH * (C' : PowerSeries CohField[X])) = 0)
    (δ : CohField[X]) (hδ : ∀ s, δ.coeff s = ((C' - G').coeff s).coeff 1) :
    PowerSeries.coeff i (Ubar * (δ : PowerSeries CohField)) = 0 := by
  have hw : PowerSeries.coeff i (AH * ((C' - G' : Polynomial CohField[X]) :
      PowerSeries CohField[X])) = 0 := by
    rw [Polynomial.coe_sub, mul_sub, map_sub, hrowG, hrowC, sub_zero]
  rw [coeff_AH_mul, Polynomial.coeff_sub, hCi, hGi, sub_zero, zero_add] at hw
  have hS := (mul_eq_zero.mp hw).resolve_left Polynomial.X_ne_zero
  have h1 := congrArg (fun q => Polynomial.coeff q 1) hS
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_zero] at h1
  rw [PowerSeries.coeff_mul]
  simpa [hδ, Polynomial.coeff_coe] using h1

/-- A unit position of `D` is a column position of `E`, once the `ε`-coefficient of `Ct - Gt`
vanishes, the row equation of `Gt` holds at it and `Ct` is supported on the columns of `E`. -/
private theorem unit_mem_colSet {n : ℕ} {D E : BetaDiagram (n + 1)} {m : ℕ}
    {C : BetaDiagram (m + 1)} (PD : CoreData D C) (PE : CoreData E C) (hC : C.Connected)
    {β : CohField} (hβ : β ≠ 0) (Gt Ct a : Polynomial CohField[X])
    (hG : Gt = liftK (Polynomial.C β * coframe C) + Polynomial.C Polynomial.X * a)
    (hrowG : ∀ i ∈ rowSet D, PowerSeries.coeff i (AH * (Gt : PowerSeries CohField[X])) = 0)
    (hsuppC : ∀ s, s ≠ 0 → s ∉ colSet E → Ct.coeff s = 0)
    (hδ : ∀ s, ((Ct - Gt).coeff s).coeff 1 = 0) {x : ℕ} (hxr : x ∈ rowSet D)
    (hxc : x ∈ colSet D) : x ∈ colSet E ∧ x ∈ rowSet E := by
  have hcolC := colSet_core PD
  have hcolE := colSet_core PE
  have hrowE := rowSet_core PE
  have hrowD := rowSet_core PD
  have hxrC : x ∉ rowSet C := by
    rw [hrowD]; simp [hxc]
  have hxc' : x ∈ colSet E → x ∈ rowSet E := by
    intro h
    by_contra hr
    have : x ∈ colSet C := by rw [hcolE]; exact Finset.mem_sdiff.mpr ⟨h, hr⟩
    rw [hcolC] at this
    exact (Finset.mem_sdiff.mp this).2 hxr
  have hxE : x ∈ colSet E := by
    by_contra hE
    obtain ⟨i, hi⟩ := Finset.mem_image.mp hxr
    have hx0 : 0 < x := by rw [← hi.2]; exact rowPos_pos D i
    have hxs : x < span D := by rw [← hi.2]; exact rowPos_lt_span D i
    have hne := coeff_unitFree_ne_zero hC hx0 (by rw [span_core PD]; exact hxs) hxrC
    have h1 := coeff_one_of_row (β := β) (coframe C) Gt a hG x (hrowG x hxr)
    have h2 : Ct.coeff x = 0 := hsuppC x hx0.ne' hE
    have h3 := hδ x
    rw [Polynomial.coeff_sub, h2, zero_sub, Polynomial.coeff_neg, h1, neg_neg,
      coeff_Ubar_mul] at h3
    exact mul_ne_zero hβ (mul_ne_zero (inv_ne_zero theta_ne_zero) hne) h3
  exact ⟨hxE, hxc' hxE⟩

/-- If the first `ε`-coefficient of `Ct - Gt` vanishes, the two diagrams with a common presented
zero-free core have the same row and column positions. -/
theorem masks_eq_of_delta_zero {n : ℕ} {D E : BetaDiagram (n + 1)} {m : ℕ}
    {C : BetaDiagram (m + 1)} (PD : CoreData D C) (PE : CoreData E C) (hC : C.Connected)
    (hzf : ∀ i j, C.row i ≠ C.col j) (hs : span D = span E)
    {β : CohField} (hβ : β ≠ 0) (Gt Ct a b : Polynomial CohField[X])
    (hG : Gt = liftK (Polynomial.C β * coframe C) + Polynomial.C Polynomial.X * a)
    (hC' : Ct = liftK (Polynomial.C β * coframe C) + Polynomial.C Polynomial.X * b)
    (hrowG : ∀ i ∈ rowSet D, PowerSeries.coeff i (AH * (Gt : PowerSeries CohField[X])) = 0)
    (hrowC : ∀ i ∈ rowSet E, PowerSeries.coeff i (AH * (Ct : PowerSeries CohField[X])) = 0)
    (hsuppG : ∀ s, s ≠ 0 → s ∉ colSet D → Gt.coeff s = 0)
    (hsuppC : ∀ s, s ≠ 0 → s ∉ colSet E → Ct.coeff s = 0)
    (hδ : ∀ s, ((Ct - Gt).coeff s).coeff 1 = 0) :
    rowSet D = rowSet E ∧ colSet D = colSet E := by
  have hδ' : ∀ s, ((Gt - Ct).coeff s).coeff 1 = 0 := fun s => by
    rw [← neg_sub Ct Gt, Polynomial.coeff_neg, Polynomial.coeff_neg, hδ s, neg_zero]
  have hDE := fun (x : ℕ) hr hc =>
    unit_mem_colSet PD PE hC hβ Gt Ct a hG hrowG hsuppC hδ (x := x) hr hc
  have hED := fun (x : ℕ) hr hc =>
    unit_mem_colSet PE PD hC hβ Ct Gt b hC' hrowC hsuppG hδ' (x := x) hr hc
  have rD := rowSet_core PD
  have cD := colSet_core PD
  have rE := rowSet_core PE
  have cE := colSet_core PE
  have hrc : rowSet D \ colSet D = rowSet E \ colSet E := rD.symm.trans rE
  have hcr : colSet D \ rowSet D = colSet E \ rowSet E := cD.symm.trans cE
  constructor
  · ext x
    constructor
    · intro hx
      by_cases hc : x ∈ colSet D
      · exact (hDE x hx hc).2
      · exact (Finset.mem_sdiff.mp (hrc ▸ Finset.mem_sdiff.mpr ⟨hx, hc⟩)).1
    · intro hx
      by_cases hc : x ∈ colSet E
      · exact (hED x hx hc).2
      · exact (Finset.mem_sdiff.mp (hrc ▸ Finset.mem_sdiff.mpr ⟨hx, hc⟩ : x ∈ _)).1
  · ext x
    constructor
    · intro hx
      by_cases hr : x ∈ rowSet D
      · exact (hDE x hr hx).1
      · exact (Finset.mem_sdiff.mp (hcr ▸ Finset.mem_sdiff.mpr ⟨hx, hr⟩ : x ∈ _)).1
    · intro hx
      by_cases hr : x ∈ rowSet E
      · exact (hED x hr hx).1
      · exact (Finset.mem_sdiff.mp (hcr ▸ Finset.mem_sdiff.mpr ⟨hx, hr⟩ : x ∈ _)).1

end SkewCoframeRigidity.UnitCase
