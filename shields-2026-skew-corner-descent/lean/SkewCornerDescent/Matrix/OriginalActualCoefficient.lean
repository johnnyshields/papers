/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalRationalClassSums
import SkewCornerDescent.Matrix.OriginalResponseCycleProjection
import SkewCornerDescent.Matrix.OriginalTransfer

/-!
# Original coefficients with actual response-class inventories

Formalizes `shields-2026-skew-corner-descent.tex` (`lem:original-transfer`).
The produced rational support is summed back over literal equality classes and
complete original closure cycles. No independent response coordinates, assumed
class packet, or nonzero detector is used to derive the coefficient identity.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows
open scoped BigOperators

noncomputable local instance actualCoefficientRatAlgebra (N : ℕ+) :
    Algebra ℚ (OtherField N) := OreLocalization.instAlgebra

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The full original defect has the exact prefactor times the literal response
class detector. The protected top and all class/closure identifications are
constructed from the original chart and the standing gap period. -/
theorem originalActual_coefficient {n m s t : ℕ}
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
    [NeZero (originalSelectedCount (hD := hD) P)]
    [NeZero (originalSelectedCount (hD := hD) P - originalSelectedCount (hD := hD) W)]
    (hp : Function.Periodic
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x))
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (j : ℕ) (hj : 2 ≤ j) (hjB : j ≤ originalSelectedCount (hD := hD) P) (hjr : r ∣ j)
    (p₀ p₁ : Polynomial ℚ) (hpq : IsCoprime p₀ p₁)
    (hdep : c.residueMap P.schur ^ a / c.residueMap W.schur ^ b =
      Polynomial.aeval (c.residueMap Q.schur / c.residueMap P.schur ^ 2) p₀ /
        Polynomial.aeval (c.residueMap Q.schur / c.residueMap P.schur ^ 2) p₁) :
    let cycle := finiteWordCycle (n := originalSelectedCount (hD := hD) P -
      originalSelectedCount (hD := hD) W) (c.originalInternalResidue P) (by omega)
    ∃ K : ℕ+, ∃ hK : c.top < K,
      (∀ l, l < j - 1 → residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
        (PowerSeries.coeff l (c.originalDeterminantDefect P A Q a b p₀ p₁)) = 0) ∧
      residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
        (PowerSeries.coeff (j - 1) (c.originalDeterminantDefect P A Q a b p₀ p₁)) =
        PowerSeries.constantCoeff (c.originalRationalFunctionSeries P Q p₀ p₁) *
          (((-1 : OtherField c.top) ^ (j - 1) * (c.normalCoefficient)⁻¹ ^ (j - 1)) *
            windowDefect cycle Subtype.val (c.originalResponseClassExponent P W a b)
              b (originalSelectedCount (hD := hD) P) j) ∧
      jetsAffineOver (residueLowerField c.top K) (residueGenerator c.top ⟨K, ne_of_gt hK⟩)
        (c.originalDeterminantDefect P A Q a b p₀ p₁) (j - 1) ∧
      (windowDefect cycle Subtype.val (c.originalResponseClassExponent P W a b)
        b (originalSelectedCount (hD := hD) P) j ≠ 0 →
        PowerSeries.coeff (j - 1) (c.originalDeterminantDefect P A Q a b p₀ p₁) ≠ 0) := by
  classical
  have hB : 0 < originalSelectedCount (hD := hD) P := Nat.pos_of_ne_zero (NeZero.ne _)
  have hcountP : originalSelectedCount (hD := hD) P = b * r := by
    rw [originalSelectedCount_eq_primeOrder, hKU,
      primeOrder_pow (irreducible_cellSchur hD).prime, hr]
  have hdiv : j / r * r = j := Nat.div_mul_cancel hjr
  have hk : 0 < (j / r : ℕ) := by
    apply Nat.pos_of_ne_zero
    intro hzero
    have hjzero : j = 0 := by simpa only [hzero, zero_mul] using hdiv.symm
    omega
  let K := c.originalCyclicTop P r (j / r)
  have hK : c.top < K := c.originalCyclicTop_gt P hB r (j / r) hrpos hk
  have hKeq := c.originalCyclicTop_coe P hB r (j / r)
  obtain ⟨ε, δ, support, e, hε, hδ, hs, hdegree, hfactor, hρ, hρ0, hsums, hL⟩ :=
    c.originalWindow_rational_class_sums P W A Q q v u z w hv hwindow hW hA hQ hcutq
      hcutLq hC hmax Λ b a hab hKU hKW p₀ p₁ hpq hdep
  have hcoeff := c.originalRationalDefect_coefficient_of_residue_match P W A Q q v u z w
    hq hv hwindow hW hA hQ hcutq hcutLq hC hmax Λ b a r hab hrpos hr hKU hKW
    (j / r) (j - 1) (by omega) (by omega) (by omega) hp K hK hKeq
    support id e ε hε hdegree hfactor
  have hlen : originalSelectedCount (hD := hD) P - originalSelectedCount (hD := hD) W =
      originalSelectedCount (hD := hD) P - originalSelectedCount (hD := hD) W := rfl
  obtain ⟨hperiod, hprojection⟩ := c.originalWindow_complete_cycle_projection P W q z v hv
    hW.symm hwindow hcutq hcutLq hC _ hlen
  have hsum := hsums (fun x => inverseWindowSum
    (completeResponseCycle (c.originalInternalResidue P) x) j)
  dsimp only at hcoeff hsum hprojection ⊢
  simp only [id_eq, show j - 1 + 1 = j by omega] at hcoeff
  rw [← hsum] at hcoeff
  simp_rw [hprojection] at hcoeff
  rw [← hρ] at hcoeff
  change (∀ l, l < j - 1 → residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
    (PowerSeries.coeff l (c.originalDeterminantDefect P A Q a b p₀ p₁)) = 0) ∧ _ at hcoeff
  refine ⟨K, hK, hcoeff.1, hcoeff.2.1, hcoeff.2.2, ?_⟩
  intro hdetector hz
  have hderiv : residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
      (PowerSeries.coeff (j - 1) (c.originalDeterminantDefect P A Q a b p₀ p₁)) ≠ 0 := by
    rw [originalDeterminantDefect, hcoeff.2.1]
    exact mul_ne_zero hρ0 (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num))
      (pow_ne_zero _ (inv_ne_zero c.normalCoefficient_ne_zero))) hdetector)
  exact hderiv (by rw [hz, map_zero])

end SkewCornerDescent.Matrix.SelectedCoordinate
