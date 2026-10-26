/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalMaximalBin
import SkewCornerDescent.Matrix.OriginalFilteredComparison

/-!
# Complete original maximal-bin coefficient and dichotomy

Formalizes `shields-2026-skew-corner-descent.tex` (`lem:maximal-bin`). One
constructed maximum and one actual signed class packet give the displayed filtered
cyclic coefficient, strict-bin detection of the complete supplied rational defect,
and the equality branch's completed-gap period. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows
open scoped BigOperators

noncomputable local instance maximalBinFullRatAlgebra (N : ℕ+) :
    Algebra ℚ (OtherField N) := OreLocalization.instAlgebra

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The actual maximal-bin formula and its two branches share one constructed
maximum, protected generator, and literal signed class inventory. -/
theorem originalMaximalBin_full {n m s t : ℕ}
    (P : Profile n) (W : Profile s) (A : Profile m) (Q : Profile t)
    (q : ℤ) (v u z w : ℤ × ℤ) (hq : 0 ≤ q) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate z W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells)
    (hQ : originalHorizontalClosure P = translate w Q.cells)
    (hcutq : diagLo P.cells q = diagHi P.cells q)
    (hcutLq : diagLo P.cells (P.xi 0 - q) = diagHi P.cells (P.xi 0 - q))
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (Λ : Lambda) (b a r : ℕ) (ha : 0 < a) (hab : a + 2 ≤ b) (hrpos : 0 < r)
    (hcoprime : b.Coprime a) (hr : primeOrder (cellSchur D hD.1) Λ = r)
    (hKU : (jtMatrix (fun j : Fin n => P.xi j.succ)
      (fun j => P.zeta j.castSucc)).det = Λ ^ b)
    (hKW : (jtMatrix (fun j : Fin s => W.xi j.succ)
      (fun j => W.zeta j.castSucc)).det = Λ ^ a)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (Δ : ℤ) (hspan : P.xi 0 - P.zeta (Fin.last n) = (b : ℤ) * Δ)
    (hqspan : q = ((b - a : ℕ) : ℤ) * Δ)
    (p₀ p₁ : Polynomial ℚ) (hpq : IsCoprime p₀ p₁)
    (hdep : c.residueMap P.schur ^ a / c.residueMap W.schur ^ b =
      Polynomial.aeval (c.residueMap Q.schur / c.residueMap P.schur ^ 2) p₀ /
        Polynomial.aeval (c.residueMap Q.schur / c.residueMap P.schur ^ 2) p₁) :
    let j := (b - a) * r
    letI : NeZero j := ⟨by dsimp only [j]; exact ne_of_gt (Nat.mul_pos (by omega) hrpos)⟩
    let middle : Fin (originalSelectedCount (hD := hD) Q + 1) :=
      ⟨originalSelectedCount (hD := hD) P, by
        rw [originalHorizontalClosure_profile_selected_count P Q w hQ]; omega⟩
    ∃ M : ℤ, ∃ K : ℕ+, ∃ hK : c.top < K,
    ∃ hperiodSize : j ≤ originalSelectedCount (hD := hD) P - 1,
    ∃ ε δ : ℤ, ∃ classes : Finset ℚ, ∃ e : ℚ → ℤ,
      (K : ℤ) = (c.top : ℤ) + M ∧
      (∀ x : ZMod (originalSelectedCount (hD := hD) P),
        windowSum (fun a => c.originalCompletedGap P ((ZMod.finEquiv _).symm a)) 1 j x ≤ M) ∧
      (∃ x : ZMod (originalSelectedCount (hD := hD) P),
        windowSum (fun a => c.originalCompletedGap P ((ZMod.finEquiv _).symm a)) 1 j x = M) ∧
      q ≤ M ∧ (δ = 1 ∨ δ = -1) ∧ (ε = 1 ∨ ε = -1) ∧
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
      c.originalRationalFunctionSeries P Q p₀ p₁ = c.originalRationalPrefactor P Q classes id e ε ∧
      PowerSeries.constantCoeff (c.originalRationalFunctionSeries P Q p₀ p₁) ≠ 0 ∧
      let f := c.normalPolynomialSeries P.schur
      let E := c.normalPolynomialSeries A.schur
      let T := fun α : ℚ => c.normalPolynomialSeries Q.schur -
        PowerSeries.C (α : OtherField c.top) * f ^ 2
      let R := normalComparisonSeries classes E f T e b a
      (residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
        (PowerSeries.coeff (j - 1)
          (PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff R)⁻¹ * R))) =
        ((-1 : OtherField c.top) ^ (j - 1) * (c.normalCoefficient)⁻¹ ^ (j - 1)) *
          ((b : OtherField c.top) * filteredInverseWindowSum
            (finiteWordCycle (n := j) (c.originalInternalResidue P) hperiodSize)
            (finiteWordCycle (n := j) (c.originalCompletedGap P)
              (hperiodSize.trans (Nat.sub_le _ _))) j M -
            ∑ α ∈ classes, (e α : OtherField c.top) * filteredInverseWindowSum
              (completeResponseCycle (c.originalInternalResidue P)
                (c.regularResidue (c.originalHessenbergResponse Q middle middle) -
                  (((δ : ℚ) * α : ℚ) : OtherField c.top) * c.originalTrueCapProduct P))
              (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x)) j M)) ∧
      (q < M → residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
        (PowerSeries.coeff (j - 1) (c.originalDeterminantDefect P A Q a b p₀ p₁)) ≠ 0) ∧
      (M = q → Function.Periodic
        (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x))
        (r : ZMod (originalSelectedCount (hD := hD) P))) := by
  classical
  let j := (b - a) * r
  have hj : 2 ≤ j := by
    have hd : 2 ≤ b - a := by omega
    have hm := Nat.mul_le_mul_left (b - a) hrpos
    dsimp only [j]
    omega
  let : NeZero j := ⟨by omega⟩
  have hcountP : originalSelectedCount (hD := hD) P = b * r := by
    rw [originalSelectedCount_eq_primeOrder, hKU,
      primeOrder_pow (irreducible_cellSchur hD).prime, hr]
  have hcountW : originalSelectedCount (hD := hD) W = a * r := by
    rw [originalSelectedCount_eq_primeOrder, hKW,
      primeOrder_pow (irreducible_cellSchur hD).prime, hr]
  have hC : 0 < originalSelectedCount (hD := hD) W := by
    rw [hcountW]
    exact Nat.mul_pos ha hrpos
  have hB : 0 < originalSelectedCount (hD := hD) P := by
    rw [hcountP]
    exact Nat.mul_pos (by omega) hrpos
  have hjlen : j = originalSelectedCount (hD := hD) P - originalSelectedCount (hD := hD) W := by
    rw [hcountP, hcountW, ← Nat.sub_mul]
  have hperiodSize : j ≤ originalSelectedCount (hD := hD) P - 1 := by omega
  obtain ⟨M, K, hK, hKeq, hbound, hretain, hmean, hstrict, hperiod⟩ :=
    c.originalMaximalBin_alternative P W A Q q v u z w hq hv hwindow hW hA hQ hcutq
      hcutLq hmax Λ b a r ha hab hrpos hcoprime hr hKU hKW Δ hspan hqspan p₀ p₁ hpq hdep
  obtain ⟨ε, δ, classes, e, hδ, hε, hsupport, hdegree, hcounts, hcoord, _, hρ, hρ0⟩ :=
    c.originalRationalClasses_representation P W A Q q v u z w hv hwindow hW hA hQ
      hcutq hcutLq hC hmax Λ b a (by omega) hKU hKW p₀ p₁ hpq hdep
  have hcoef := c.originalComparison_normalized_log_filtered_bin P W A Q q v u z w
    hq hv hwindow hW hA hQ hcutq hcutLq hC hmax j hj hjlen M hmean hbound K hK hKeq
    classes e b a (by rw [hdegree]; omega)
  have hshift := c.originalVirtualCentralResponse_eq_oriented_cap P Q w hQ hB hmax δ hcoord
  dsimp only at hcoef hshift ⊢
  simp_rw [hshift] at hcoef
  refine ⟨M, K, hK, hperiodSize, ε, δ, classes, e, hKeq, hbound, hretain, hmean, hδ, hε,
    hsupport, hdegree, hcounts, hρ, hρ0, ?_, hstrict, hperiod⟩
  have halg : maximalBinFullRatAlgebra c.top = DivisionRing.toRatAlgebra :=
    Subsingleton.elim _ _
  have hlog (p : PowerSeries (OtherField c.top)) :
      @PowerSeries.logOf (OtherField c.top) _ (maximalBinFullRatAlgebra c.top) p =
        @PowerSeries.logOf (OtherField c.top) _ DivisionRing.toRatAlgebra p :=
    congrArg (fun A : Algebra ℚ (OtherField c.top) =>
      @PowerSeries.logOf (OtherField c.top) _ A p) halg
  rw [hlog]
  exact hcoef.2

end SkewCornerDescent.Matrix.SelectedCoordinate
