/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalRationalDefectTransfer
import SkewCornerDescent.Matrix.OriginalWindowRationalFactors
import SkewCornerDescent.SignedRationalRepresentation

/-!
# The actual rational classes in the original coefficient formula

Supports `shields-2026-skew-corner-descent.tex` (`lem:residue-classifier`,
`lem:original-transfer`). The classifier supplies the very orientation used by
the shifted closure responses, not an independently chosen sign. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows
open scoped BigOperators

noncomputable local instance rationalClassTransferRatAlgebra (N : ℕ+) :
    Algebra ℚ (OtherField N) := OreLocalization.instAlgebra

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The original supplied rational function evaluated on the complete normal
closure/source quotient, with its full polynomial denominator inverse. -/
noncomputable def originalRationalFunctionSeries {n m : ℕ} (P : Profile n) (Q : Profile m)
    (p q : Polynomial ℚ) : PowerSeries (OtherField c.top) :=
  let u := c.normalPolynomialSeries Q.schur * (c.normalPolynomialSeries P.schur)⁻¹ ^ 2
  Polynomial.aeval u p * (Polynomial.aeval u q)⁻¹

/-- The orientation equation returned by `originalWindow_rational_factorization`
identifies each virtual central response with that classifier's actual class value. -/
theorem originalVirtualCentralResponse_eq_oriented_cap {n m : ℕ}
    (P : Profile n) (Q : Profile m) (w : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate w Q.cells)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (δ : ℤ)
    (hcoord : let middle : Fin (originalSelectedCount (hD := hD) Q + 1) :=
        ⟨originalSelectedCount (hD := hD) P, by
          rw [originalHorizontalClosure_profile_selected_count P Q w hQ]; omega⟩
      c.regularResidue (c.originalHessenbergResponse Q middle middle) /
        c.originalTrueCapProduct P =
          (δ : OtherField c.top) * (c.residueMap Q.schur / c.residueMap P.schur ^ 2)) :
    let middle : Fin (originalSelectedCount (hD := hD) Q + 1) :=
      ⟨originalSelectedCount (hD := hD) P, by
        rw [originalHorizontalClosure_profile_selected_count P Q w hQ]; omega⟩
    ∀ α : ℚ, c.originalVirtualCentralResponse P Q middle α =
      c.regularResidue (c.originalHessenbergResponse Q middle middle) -
        (((δ : ℚ) * α : ℚ) : OtherField c.top) * c.originalTrueCapProduct P := by
  have hf := c.originalSchur_residue_ne_zero P hB hmax
  have hBQ : 0 < originalSelectedCount (hD := hD) Q := by
    rw [originalHorizontalClosure_profile_selected_count P Q w hQ]
    omega
  have hβ := c.originalSchur_residue_ne_zero Q hBQ
    (c.originalHorizontalClosure_profile_component_span P Q w hQ hmax)
  have hcap := c.originalTrueCapProduct_ne_zero P hB hmax
  dsimp only at hcoord ⊢
  rw [← mul_div_assoc] at hcoord
  have hrel := (div_eq_div_iff hcap (pow_ne_zero 2 hf)).mp hcoord
  intro α
  unfold originalVirtualCentralResponse
  rw [Rat.cast_mul, Rat.cast_intCast]
  field_simp [hβ]
  linear_combination -(α : OtherField c.top) * hrel

/-- Exact standing residue dependence supplies the original signed class packet
and identifies the complete supplied rational series, independently of gap periods
and protected coefficient orders. -/
theorem originalRationalClasses_representation {n m s t : ℕ}
    (P : Profile n) (W : Profile s) (A : Profile m) (Q : Profile t)
    (q : ℤ) (v u z w : ℤ × ℤ) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate z W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells)
    (hQ : originalHorizontalClosure P = translate w Q.cells)
    (hcutq : diagLo P.cells q = diagHi P.cells q)
    (hcutLq : diagLo P.cells (P.xi 0 - q) = diagHi P.cells (P.xi 0 - q))
    (hC : 0 < originalSelectedCount (hD := hD) W)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (Λ : Lambda) (b a : ℕ) (hab : a < b)
    (hKU : (jtMatrix (fun j : Fin n => P.xi j.succ)
      (fun j => P.zeta j.castSucc)).det = Λ ^ b)
    (hKW : (jtMatrix (fun j : Fin s => W.xi j.succ)
      (fun j => W.zeta j.castSucc)).det = Λ ^ a)
    (p₀ p₁ : Polynomial ℚ) (hcoprime : IsCoprime p₀ p₁)
    (hdep : c.residueMap P.schur ^ a / c.residueMap W.schur ^ b =
      Polynomial.aeval (c.residueMap Q.schur / c.residueMap P.schur ^ 2) p₀ /
        Polynomial.aeval (c.residueMap Q.schur / c.residueMap P.schur ^ 2) p₁) :
    let middle : Fin (originalSelectedCount (hD := hD) Q + 1) :=
      ⟨originalSelectedCount (hD := hD) P, by
        rw [originalHorizontalClosure_profile_selected_count P Q w hQ]; omega⟩
    ∃ ε δ : ℤ, ∃ classes : Finset ℚ, ∃ e : ℚ → ℤ,
      (δ = 1 ∨ δ = -1) ∧ (ε = 1 ∨ ε = -1) ∧
      (∀ α, α ∈ classes ↔ e α ≠ 0) ∧ (∑ α ∈ classes, e α) = ((b - a : ℕ) : ℤ) ∧
      (∀ α, e α =
        (a : ℤ) * (Finset.univ.filter fun i =>
          c.regularResidue (c.originalHessenbergResponse Q middle middle) -
              (((δ : ℚ) * α : ℚ) : OtherField c.top) * c.originalTrueCapProduct P =
            c.originalInternalResidue P i).card -
        (b : ℤ) * (Finset.univ.filter fun i =>
          c.regularResidue (c.originalHessenbergResponse Q middle middle) -
              (((δ : ℚ) * α : ℚ) : OtherField c.top) * c.originalTrueCapProduct P =
            c.originalInternalResidue W i).card) ∧
      (c.regularResidue (c.originalHessenbergResponse Q middle middle) /
        c.originalTrueCapProduct P =
          (δ : OtherField c.top) * (c.residueMap Q.schur / c.residueMap P.schur ^ 2)) ∧
      (c.residueMap P.schur ^ a / c.residueMap W.schur ^ b =
        (ε : OtherField c.top) * ∏ α ∈ classes,
          (c.residueMap Q.schur / c.residueMap P.schur ^ 2 - (α : OtherField c.top)) ^ e α) ∧
      c.originalRationalFunctionSeries P Q p₀ p₁ = c.originalRationalPrefactor P Q classes id e ε ∧
      PowerSeries.constantCoeff (c.originalRationalFunctionSeries P Q p₀ p₁) ≠ 0 := by
  have hcutq' : ∀ x ∈ diagramInterior P.cells, content x ≠ q :=
    fun _ hx => privateDiagonal_avoids_interior hcutq hx
  have hcutLq' : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0 - q :=
    fun _ hx => privateDiagonal_avoids_interior hcutLq hx
  obtain ⟨hB, _⟩ := c.originalWindow_true_cap_product P W q v z hwindow hW hcutq' hcutLq' hC
  have hmaxW := originalWindow_component_span P W A q v u z hv hwindow hW hA (c.top : ℕ) hmax
  obtain ⟨htrans, _, ε, δ, classes, e, hδ, hε, _, hdegree, hsupport, hcounts, hcoord, hfactor⟩ :=
    c.originalWindow_rational_factorization P W Q q v z w hwindow hW hQ hcutq' hcutLq'
      hC hmax hmaxW Λ b a (b - a) (by omega) hKU hKW p₀ p₁ hcoprime hdep
  have hf0 := c.originalSchur_residue_ne_zero P hB hmax
  have hW0 := c.originalSchur_residue_ne_zero W hC hmaxW
  have hden : p₁ ≠ 0 := by
    intro hz
    apply (div_ne_zero (pow_ne_zero a hf0) (pow_ne_zero b hW0))
    rw [hdep, hz, map_zero, div_zero]
  let γ := c.normalPolynomialSeries Q.schur * (c.normalPolynomialSeries P.schur)⁻¹ ^ 2
  have hγ : PowerSeries.constantCoeff γ = c.residueMap Q.schur / c.residueMap P.schur ^ 2 := by
    simp only [γ, map_mul, map_pow, PowerSeries.constantCoeff_inv,
      c.normalPolynomialSeries_constant, div_eq_mul_inv, inv_pow]
  have hrepresentation := signedRational_series_transfer
    (c.residueMap Q.schur / c.residueMap P.schur ^ 2) htrans γ hγ
    p₀ p₁ hden ε classes e (hdep.symm.trans hfactor)
  have hρ : c.originalRationalFunctionSeries P Q p₀ p₁ =
      c.originalRationalPrefactor P Q classes id e ε := by
    simpa only [originalRationalFunctionSeries, originalRationalPrefactor, γ, id_eq] using
      hrepresentation
  dsimp only at hcoord ⊢
  refine ⟨ε, δ, classes, e, hδ, hε, hsupport, hdegree, hcounts, hcoord, hfactor, hρ, ?_⟩
  rw [hρ]
  exact c.originalRationalPrefactor_constant_ne_zero P Q w hQ hB hmax classes id e ε hε

/-- Exact standing rational dependence supplies the actual class inventory in
the whole original defect's fresh coefficient. The window component bounds,
signed factors, raw residue match, and virtual-class orientation are all produced. -/
theorem originalRationalClasses_coefficient {n m s t : ℕ}
    (P : Profile n) (W : Profile s) (A : Profile m) (Q : Profile t)
    (q : ℤ) (v u z w : ℤ × ℤ)
    (hq : 0 ≤ q) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate z W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells)
    (hQ : originalHorizontalClosure P = translate w Q.cells)
    (hcutq : diagLo P.cells q = diagHi P.cells q)
    (hcutLq : diagLo P.cells (P.xi 0 - q) = diagHi P.cells (P.xi 0 - q))
    (hC : 0 < originalSelectedCount (hD := hD) W)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (Λ : Lambda) (b a r : ℕ) (hab : a < b) (hrpos : 0 < r)
    (hr : primeOrder (cellSchur D hD.1) Λ = r)
    (hKU : (jtMatrix (fun j : Fin n => P.xi j.succ)
      (fun j => P.zeta j.castSucc)).det = Λ ^ b)
    (hKW : (jtMatrix (fun j : Fin s => W.xi j.succ)
      (fun j => W.zeta j.castSucc)).det = Λ ^ a)
    [NeZero (originalSelectedCount (hD := hD) P)]
    [NeZero (originalSelectedCount (hD := hD) P - originalSelectedCount (hD := hD) W)]
    (k h : ℕ) (hh : 0 < h) (hhB : h < originalSelectedCount (hD := hD) P)
    (hlen : h + 1 = k * r)
    (hp : Function.Periodic
      (fun z => c.originalCompletedGap P ((ZMod.finEquiv _).symm z))
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (K : ℕ+) (hK : c.top < K)
    (hKeq : (K : ℤ) = (c.top : ℤ) + k • windowSum
      (fun z => c.originalCompletedGap P ((ZMod.finEquiv _).symm z)) 1 r 0)
    (p₀ p₁ : Polynomial ℚ) (hcoprime : IsCoprime p₀ p₁)
    (hdep : c.residueMap P.schur ^ a / c.residueMap W.schur ^ b =
      Polynomial.aeval (c.residueMap Q.schur / c.residueMap P.schur ^ 2) p₀ /
        Polynomial.aeval (c.residueMap Q.schur / c.residueMap P.schur ^ 2) p₁) :
    let f := c.normalPolynomialSeries P.schur
    let E := c.normalPolynomialSeries A.schur
    let cycle := finiteWordCycle (n := originalSelectedCount (hD := hD) P -
      originalSelectedCount (hD := hD) W) (c.originalInternalResidue P) (by omega)
    let middle : Fin (originalSelectedCount (hD := hD) Q + 1) :=
      ⟨originalSelectedCount (hD := hD) P, by
        rw [originalHorizontalClosure_profile_selected_count P Q w hQ]; omega⟩
    ∃ ε δ : ℤ, ∃ classes : Finset ℚ, ∃ e : ℚ → ℤ,
      (δ = 1 ∨ δ = -1) ∧ (ε = 1 ∨ ε = -1) ∧
      (∀ α, α ∈ classes ↔ e α ≠ 0) ∧ (∑ α ∈ classes, e α) = ((b - a : ℕ) : ℤ) ∧
      (∀ α, e α =
        (a : ℤ) * (Finset.univ.filter fun i =>
          c.regularResidue (c.originalHessenbergResponse Q middle middle) -
              (((δ : ℚ) * α : ℚ) : OtherField c.top) * c.originalTrueCapProduct P =
            c.originalInternalResidue P i).card -
        (b : ℤ) * (Finset.univ.filter fun i =>
          c.regularResidue (c.originalHessenbergResponse Q middle middle) -
              (((δ : ℚ) * α : ℚ) : OtherField c.top) * c.originalTrueCapProduct P =
            c.originalInternalResidue W i).card) ∧
      (c.regularResidue (c.originalHessenbergResponse Q middle middle) /
        c.originalTrueCapProduct P =
          (δ : OtherField c.top) * (c.residueMap Q.schur / c.residueMap P.schur ^ 2)) ∧
      (c.residueMap P.schur ^ a / c.residueMap W.schur ^ b =
        (ε : OtherField c.top) * ∏ α ∈ classes,
          (c.residueMap Q.schur / c.residueMap P.schur ^ 2 - (α : OtherField c.top)) ^ e α) ∧
      let ρ := c.originalRationalFunctionSeries P Q p₀ p₁
      ρ = c.originalRationalPrefactor P Q classes id e ε ∧
      PowerSeries.constantCoeff ρ ≠ 0 ∧
      (∀ l, l < h → residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
        (PowerSeries.coeff l (f ^ a * (E * f⁻¹ ^ 2) ^ b - ρ)) = 0) ∧
      residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
        (PowerSeries.coeff h (f ^ a * (E * f⁻¹ ^ 2) ^ b - ρ)) =
        PowerSeries.constantCoeff ρ *
          (((-1 : OtherField c.top) ^ h * (c.normalCoefficient)⁻¹ ^ h) *
            ((b : OtherField c.top) * inverseWindowSum cycle (h + 1) -
              ∑ α ∈ classes, (e α : OtherField c.top) * inverseWindowSum
                (completeResponseCycle (c.originalInternalResidue P)
                  (c.regularResidue (c.originalHessenbergResponse Q middle middle) -
                    (((δ : ℚ) * α : ℚ) : OtherField c.top) * c.originalTrueCapProduct P))
                (h + 1))) ∧
      jetsAffineOver (residueLowerField c.top K) (residueGenerator c.top ⟨K, ne_of_gt hK⟩)
        (f ^ a * (E * f⁻¹ ^ 2) ^ b - ρ) h := by
  classical
  have hB : 0 < originalSelectedCount (hD := hD) P := by omega
  obtain ⟨ε, δ, classes, e, hδ, hε, hsupport, hdegree, hcounts, hcoord, hfactor, hρ, hρ0⟩ :=
    c.originalRationalClasses_representation P W A Q q v u z w hv hwindow hW hA hQ
      hcutq hcutLq hC hmax Λ b a hab hKU hKW p₀ p₁ hcoprime hdep
  have hcoeff := c.originalRationalDefect_coefficient_of_residue_match P W A Q q v u z w
    hq hv hwindow hW hA hQ hcutq hcutLq hC hmax Λ b a r hab hrpos hr hKU hKW
    k h hh hhB hlen hp K hK hKeq classes id e ε hε hdegree hfactor
  have hshift := c.originalVirtualCentralResponse_eq_oriented_cap P Q w hQ hB hmax δ hcoord
  dsimp only at hcoeff hshift ⊢
  simp only [id_eq] at hcoeff
  simp_rw [hshift] at hcoeff
  refine ⟨ε, δ, classes, e, hδ, hε, hsupport, hdegree, hcounts, hcoord, hfactor, hρ, hρ0, ?_⟩
  rw [hρ]
  exact hcoeff

end SkewCornerDescent.Matrix.SelectedCoordinate
