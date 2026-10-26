/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalTransferIndices

/-!
# Original transfer at every eligible paper index

Formalizes `shields-2026-skew-corner-descent.tex` (`lem:original-transfer`). One
actual finite rational-class inventory works simultaneously at every eligible
index. Protected generators, full rational-function identity, earlier lower jets,
exact fresh coefficients, and affine fresh dependence are constructed. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows
open scoped BigOperators

noncomputable local instance originalTransferRatAlgebra (N : ℕ+) :
    Algebra ℚ (OtherField N) := OreLocalization.instAlgebra

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The paper's whole original defect with its supplied rational numerator and
denominator. Every original normal germ and full denominator inverse is retained. -/
noncomputable def originalDeterminantDefect {n m t : ℕ}
    (P : Profile n) (A : Profile m) (Q : Profile t) (a b : ℕ) (p q : Polynomial ℚ) :
    PowerSeries (OtherField c.top) :=
  c.normalPolynomialSeries P.schur ^ a *
      (c.normalPolynomialSeries A.schur * (c.normalPolynomialSeries P.schur)⁻¹ ^ 2) ^ b -
    c.originalRationalFunctionSeries P Q p q

/-- The complete original transfer uses one produced actual class inventory at
every `2 ≤ j ≤ B` divisible by the selected multiplicity. No cutoff, raw matching,
class count, earlier vanishing, or affine premise is added. -/
theorem originalTransfer_all_eligible_indices {n m s t : ℕ}
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
    (hC : 0 < originalSelectedCount (hD := hD) W)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (Λ : Lambda) (b a r : ℕ) (hab : a < b) (hrpos : 0 < r)
    (hr : primeOrder (cellSchur D hD.1) Λ = r)
    (hKU : (jtMatrix (fun j : Fin n => P.xi j.succ)
      (fun j => P.zeta j.castSucc)).det = Λ ^ b)
    (hKW : (jtMatrix (fun j : Fin s => W.xi j.succ)
      (fun j => W.zeta j.castSucc)).det = Λ ^ a)
    (Δ : ℤ) (hspan : P.xi 0 - P.zeta (Fin.last n) = (b : ℤ) * Δ)
    [NeZero (originalSelectedCount (hD := hD) P)]
    [NeZero (originalSelectedCount (hD := hD) P - originalSelectedCount (hD := hD) W)]
    (hp : Function.Periodic
      (fun z => c.originalCompletedGap P ((ZMod.finEquiv _).symm z))
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (p₀ p₁ : Polynomial ℚ) (hcoprime : IsCoprime p₀ p₁)
    (hdep : c.residueMap P.schur ^ a / c.residueMap W.schur ^ b =
      Polynomial.aeval (c.residueMap Q.schur / c.residueMap P.schur ^ 2) p₀ /
        Polynomial.aeval (c.residueMap Q.schur / c.residueMap P.schur ^ 2) p₁) :
    let ρ := c.originalRationalFunctionSeries P Q p₀ p₁
    let Θ := c.originalDeterminantDefect P A Q a b p₀ p₁
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
      ρ = c.originalRationalPrefactor P Q classes id e ε ∧ PowerSeries.constantCoeff ρ ≠ 0 ∧
      ∀ j : ℕ, 2 ≤ j → j ≤ originalSelectedCount (hD := hD) P → r ∣ j →
        ∃ K : ℕ+, ∃ hK : c.top < K,
          (K : ℤ) = (c.top : ℤ) + (j / r) • Δ ∧
          (∀ l, l < j - 1 → residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
            (PowerSeries.coeff l Θ) = 0) ∧
          residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩ (PowerSeries.coeff (j - 1) Θ) =
            PowerSeries.constantCoeff ρ *
              (((-1 : OtherField c.top) ^ (j - 1) * (c.normalCoefficient)⁻¹ ^ (j - 1)) *
                ((b : OtherField c.top) * inverseWindowSum cycle j -
                  ∑ α ∈ classes, (e α : OtherField c.top) * inverseWindowSum
                    (completeResponseCycle (c.originalInternalResidue P)
                      (c.regularResidue (c.originalHessenbergResponse Q middle middle) -
                        (((δ : ℚ) * α : ℚ) : OtherField c.top) * c.originalTrueCapProduct P)) j)) ∧
          jetsAffineOver (residueLowerField c.top K) (residueGenerator c.top ⟨K, ne_of_gt hK⟩)
            Θ (j - 1) := by
  classical
  have hB : 0 < originalSelectedCount (hD := hD) P :=
    Nat.pos_of_ne_zero (NeZero.ne _)
  have hcountP : originalSelectedCount (hD := hD) P = b * r := by
    rw [originalSelectedCount_eq_primeOrder, hKU,
      primeOrder_pow (irreducible_cellSchur hD).prime, hr]
  have hcountW : originalSelectedCount (hD := hD) W = a * r := by
    rw [originalSelectedCount_eq_primeOrder, hKW,
      primeOrder_pow (irreducible_cellSchur hD).prime, hr]
  have ha : 0 < a := by
    by_contra hnot
    have hz : a = 0 := by omega
    rw [hcountW, hz, zero_mul] at hC
    omega
  have hb : 0 < b := by omega
  have hb2 : 2 ≤ b := by omega
  have hΔ : c.originalPeriodIncrement P r = Δ := by
    apply mul_left_cancel₀ (show (b : ℤ) ≠ 0 by exact_mod_cast Nat.ne_of_gt hb)
    exact (c.originalPeriodIncrement_span P hB r b hcountP hp).symm.trans hspan
  have hB2 : 2 ≤ originalSelectedCount (hD := hD) P := by
    have he := Nat.mul_le_mul hb2 (show 1 ≤ r by omega)
    rw [hcountP]
    simpa only [mul_one] using he
  let KB := c.originalCyclicTop P r b
  have hKB : c.top < KB := c.originalCyclicTop_gt P hB r b hrpos hb
  have hKBco : (KB : ℤ) = (c.top : ℤ) + b • windowSum
      (fun z => c.originalCompletedGap P ((ZMod.finEquiv _).symm z)) 1 r 0 :=
    c.originalCyclicTop_coe P hB r b
  obtain ⟨ε, δ, classes, e, hδ, hε, hsupport, hdegree, hcounts, hcoord, hfactor, hρ, hρ0, _⟩ :=
    c.originalRationalClasses_coefficient P W A Q q v u z w hq hv hwindow hW hA hQ
      hcutq hcutLq hC hmax Λ b a r hab hrpos hr hKU hKW
      b (originalSelectedCount (hD := hD) P - 1) (by omega) (by omega)
      (by omega) hp KB hKB hKBco p₀ p₁ hcoprime hdep
  have hshift := c.originalVirtualCentralResponse_eq_oriented_cap P Q w hQ hB hmax δ hcoord
  dsimp only at hshift ⊢
  refine ⟨ε, δ, classes, e, hδ, hε, hsupport, hdegree, hcounts, hρ, hρ0, ?_⟩
  intro j hj hjB hjr
  have hdiv : j / r * r = j := Nat.div_mul_cancel hjr
  have hk : 0 < (j / r : ℕ) := by
    apply Nat.pos_of_ne_zero
    intro hz
    have hj0 : j = 0 := by simpa only [hz, zero_mul] using hdiv.symm
    omega
  let K := c.originalCyclicTop P r (j / r)
  have hK : c.top < K := c.originalCyclicTop_gt P hB r (j / r) hrpos hk
  have hKeq : (K : ℤ) = (c.top : ℤ) + (j / r) • windowSum
      (fun z => c.originalCompletedGap P ((ZMod.finEquiv _).symm z)) 1 r 0 :=
    c.originalCyclicTop_coe P hB r (j / r)
  have hcoeff := c.originalRationalDefect_coefficient_of_residue_match P W A Q q v u z w
    hq hv hwindow hW hA hQ hcutq hcutLq hC hmax Λ b a r hab hrpos hr hKU hKW
    (j / r) (j - 1) (by omega) (by omega) (by omega) hp K hK hKeq
    classes id e ε hε hdegree hfactor
  dsimp only at hcoeff
  simp only [id_eq] at hcoeff
  simp_rw [hshift] at hcoeff
  have hjlen : j - 1 + 1 = j := by omega
  simp only [hjlen] at hcoeff
  refine ⟨K, hK, ?_, ?_⟩
  · rw [← hΔ]
    exact c.originalCyclicTop_coe P hB r (j / r)
  · rw [originalDeterminantDefect, hρ]
    exact hcoeff

end SkewCornerDescent.Matrix.SelectedCoordinate
