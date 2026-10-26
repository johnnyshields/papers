/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/


import SkewCornerDescent.Matrix.OriginalOneActiveOrdinaryPower
import SkewCornerDescent.Matrix.OriginalVirtualClosureFactor
import SkewCornerDescent.SignedRationalRepresentation

/-!
# Complete supplied one-active rational series

Supports `shields-2026-skew-corner-descent.tex` (`eq:residue-match`,
`eq:original-defect`, `lem:original-transfer`). The actual ordinary closure and
exact transcendental rational matching identify the entire supplied series,
including the vertical Schur complement and its orientation sign. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing CyclicWindows
noncomputable local instance oneActiveRationalSeriesRatAlgebra (N : ℕ+) :
    Algebra ℚ (OtherField N) := OreLocalization.instAlgebra
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

private theorem rational_monomial_series {F : Type*} [Field F] [CharZero F] [Algebra ℚ F]
    (x : F) (hx : Transcendental ℚ x) (u : PowerSeries F)
    (hu : PowerSeries.constantCoeff u = x) (p q : Polynomial ℚ) (hq : q ≠ 0)
    (κ : ℤ) (α : ℚ) (d : ℕ)
    (hfactor : Polynomial.aeval x p / Polynomial.aeval x q =
      (κ : F) * (x - (α : F)) ^ d) :
    Polynomial.aeval u p * (Polynomial.aeval u q)⁻¹ =
      PowerSeries.C (κ : F) * (u - PowerSeries.C (α : F))^d := by
  have h := signedRational_series_transfer x hx u hu p q hq κ {α} (fun _ => (d : ℤ))
    (by simpa only [Finset.prod_singleton, zpow_natCast] using hfactor)
  simpa [signedNormalProduct] using h

/-- The supplied rational numerator and denominator give exactly the complete
ordinary one-active power series, with a produced orientation scalar.  Uniqueness
at the actual transcendental horizontal quotient and the whole vertical Schur
complement transport the residue identity at every normal order. -/
theorem originalOneActive_supplied_series_power {n m s t on : ℕ}
    (P : Profile n) (W : Profile s) (A : Profile m) (H : Profile t) (O : Profile on)
    (q : ℤ) (v u z w zO : ℤ × ℤ) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate z W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells)
    (hH : originalHorizontalClosure P = translate w H.cells)
    (hO : originalHorizontalClosure P = translate zO O.cells ∨
      originalVerticalClosure P = translate zO O.cells)
    (hcutq : diagLo P.cells q = diagHi P.cells q)
    (hcutLq : diagLo P.cells (P.xi 0 - q) = diagHi P.cells (P.xi 0 - q))
    (hC : 0 < originalSelectedCount (hD := hD) W)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (Λ : Lambda) (b a : ℕ) (hab : a < b)
    (hKU : (jtMatrix (fun j : Fin n => P.xi j.succ)
      (fun j => P.zeta j.castSucc)).det = Λ ^ b)
    (hKW : (jtMatrix (fun j : Fin s => W.xi j.succ)
      (fun j => W.zeta j.castSucc)).det = Λ ^ a)
    (p₀ p₁ : Polynomial ℚ) (hpq : IsCoprime p₀ p₁)
    (hdep : c.residueMap P.schur ^ a / c.residueMap W.schur ^ b =
      Polynomial.aeval (c.residueMap H.schur / c.residueMap P.schur ^ 2) p₀ /
        Polynomial.aeval (c.residueMap H.schur / c.residueMap P.schur ^ 2) p₁)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (active : c.OriginalResponseClass P)
    (hother : ∀ X, X ≠ active → c.originalResponseClassExponent P W a b X = 0)
    (hactive : let center : Fin (originalSelectedCount (hD := hD) O - 1) :=
        ⟨originalSelectedCount (hD := hD) P - 1, by
          rw [originalOrdinaryClosure_selected_count P O zO hO]
          have := NeZero.pos (originalSelectedCount (hD := hD) P)
          omega⟩
      c.originalInternalResidue O center = active.val) :
    ∃ κ : ℤ, (κ = 1 ∨ κ = -1) ∧
      c.originalRationalFunctionSeries P H p₀ p₁ =
        PowerSeries.C (κ : OtherField c.top) *
          (c.normalPolynomialSeries O.schur * (c.normalPolynomialSeries P.schur)⁻¹^2)^(b-a) ∧
      c.residueMap P.schur ^ a / c.residueMap W.schur ^ b =
        (κ : OtherField c.top) * (c.residueMap O.schur / c.residueMap P.schur^2)^(b-a) ∧
      PowerSeries.constantCoeff (c.originalRationalFunctionSeries P H p₀ p₁) ≠ 0 := by
  classical
  obtain ⟨κ, hκ, hpower⟩ := c.originalOneActive_ordinary_residue_power P W A H O q v u z w zO
    hv hwindow hW hA hH hO hcutq hcutLq hC hmax Λ b a hab hKU hKW p₀ p₁ hpq hdep
      active hother hactive
  have hB := NeZero.pos (originalSelectedCount (hD := hD) P)
  have hmaxW := originalWindow_component_span P W A q v u z hv hwindow hW hA
    (c.top : ℕ) hmax
  have hf0 := c.originalSchur_residue_ne_zero P hB hmax
  have hW0 := c.originalSchur_residue_ne_zero W hC hmaxW
  have hΓ : c.residueMap P.schur^a / c.residueMap W.schur^b ≠ 0 :=
    div_ne_zero (pow_ne_zero a hf0) (pow_ne_zero b hW0)
  have hden : p₁ ≠ 0 := by
    intro hz
    apply hΓ
    rw [hdep, hz, map_zero, div_zero]
  let f := c.normalPolynomialSeries P.schur
  let γ := c.normalPolynomialSeries H.schur * f⁻¹^2
  let x := c.residueMap H.schur / c.residueMap P.schur^2
  have hf : PowerSeries.constantCoeff f ≠ 0 := by
    simpa only [f, c.normalPolynomialSeries_constant] using hf0
  have hγ : PowerSeries.constantCoeff γ = x := by
    simp only [γ, f, x, map_mul, map_pow, PowerSeries.constantCoeff_inv,
      c.normalPolynomialSeries_constant, div_eq_mul_inv, inv_pow]
  have hx := c.originalHorizontalClosure_residue_transcendental P H w hH hB hmax
  have hHschur : cellSchur (originalHorizontalClosure P)
      (originalHorizontalClosure_connected P).1 = H.schur := by
    rw [cellSchur_congr hH _ (isSkew_translate w H.isSkew_cells),
      cellSchur_translate H.cells H.isSkew_cells w, cellSchur_cells H]
  have hseries : c.originalRationalFunctionSeries P H p₀ p₁ =
      PowerSeries.C (κ : OtherField c.top) *
        (c.normalPolynomialSeries O.schur * f⁻¹^2)^(b-a) := by
    rcases hO with hOH | hOV
    · have hOschur : O.schur = H.schur := by
        have ho : cellSchur (originalHorizontalClosure P)
            (originalHorizontalClosure_connected P).1 = O.schur := by
          rw [cellSchur_congr hOH _ (isSkew_translate zO O.isSkew_cells),
            cellSchur_translate O.cells O.isSkew_cells zO, cellSchur_cells O]
        exact ho.symm.trans hHschur
      have hfactor : Polynomial.aeval x p₀ / Polynomial.aeval x p₁ =
          (κ : OtherField c.top) * (x - (0 : OtherField c.top))^(b-a) := by
        simpa only [hOschur, sub_zero] using hdep.symm.trans hpower
      have ht := rational_monomial_series x hx γ hγ p₀ p₁ hden κ 0 (b-a)
        (by simpa only [Rat.cast_zero] using hfactor)
      simpa only [originalRationalFunctionSeries, γ, f, hOschur, Rat.cast_zero,
        map_zero, sub_zero] using ht
    · have ho := originalVertical_virtual_factor P O zO hOV
      rw [hHschur] at ho
      have hOschur : O.schur = P.schur^2 - H.schur := by linear_combination ho
      have hOres : c.residueMap O.schur / c.residueMap P.schur^2 = 1 - x := by
        rw [hOschur, map_sub, map_pow, sub_div, div_self (pow_ne_zero 2 hf0)]
      have hfactor : Polynomial.aeval x p₀ / Polynomial.aeval x p₁ =
          ((κ*(-1)^(b-a) : ℤ) : OtherField c.top) * (x - 1)^(b-a) := by
        have hh := hdep.symm.trans hpower
        rw [hOres] at hh
        have hsub : (1 : OtherField c.top) - x = -(x - 1) := by ring
        rw [hsub, neg_pow] at hh
        simpa only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, mul_assoc] using hh
      have ht := rational_monomial_series x hx γ hγ p₀ p₁ hden
        (κ*(-1)^(b-a)) 1 (b-a) (by simpa only [Rat.cast_one] using hfactor)
      have hOseries : c.normalPolynomialSeries O.schur =
          f^2 - c.normalPolynomialSeries H.schur := by
        simpa only [f, map_sub, map_pow] using congrArg c.normalPolynomialSeries hOschur
      have hcancel : f^2 * f⁻¹^2 = 1 := by
        rw [← mul_pow, PowerSeries.mul_inv_cancel f hf, one_pow]
      have hquot : c.normalPolynomialSeries O.schur * f⁻¹^2 = 1 - γ := by
        rw [hOseries, sub_mul, hcancel]
      have hrho : c.originalRationalFunctionSeries P H p₀ p₁ =
          PowerSeries.C (((κ*(-1)^(b-a) : ℤ) : OtherField c.top)) * (γ-1)^(b-a) := by
        simpa only [originalRationalFunctionSeries, γ, f, Rat.cast_one, map_one] using ht
      rw [hrho, hquot]
      have hsub : (1 : PowerSeries (OtherField c.top)) - γ = -(γ-1) := by ring
      have hsign : (-(γ-1))^(b-a) =
          (-1 : PowerSeries (OtherField c.top))^(b-a) * (γ-1)^(b-a) := by
        rw [neg_pow]
      rw [hsub, hsign]
      simp only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
        map_mul, map_pow, map_neg, map_one]
      ring
  have hres : PowerSeries.constantCoeff (c.originalRationalFunctionSeries P H p₀ p₁) =
      c.residueMap P.schur^a / c.residueMap W.schur^b := by
    rw [hseries]
    simp only [map_mul, PowerSeries.constantCoeff_C, map_pow,
      PowerSeries.constantCoeff_inv, f, c.normalPolynomialSeries_constant]
    simpa only [div_eq_mul_inv, inv_pow] using hpower.symm
  exact ⟨κ, hκ, hseries, hpower, fun hz => hΓ (hres.symm.trans hz)⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
