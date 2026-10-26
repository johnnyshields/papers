/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalPrimitiveClasses
import SkewCornerDescent.Matrix.OriginalManyActiveGeneral

/-!
# The primitive nonconstant original-order bound

Formalizes `shields-2026-skew-corner-descent.tex` (`thm:primitive-short`).
Actual primitive corner powers exclude balanced internal classes. A nonconstant
original word supplies the two active classes consumed by arbitrary-gap
many-active detection. Signed exponents and arbitrary bounded unit inventories
are retained. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

noncomputable local instance primitiveShortRatAlgebra (N : ℕ+) :
    Algebra ℚ (OtherField N) := OreLocalization.instAlgebra

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- At primitive selected multiplicity, every nonconstant actual response word
has a nonzero original coefficient by order `b-a-1`. The active-class premise and
all gap-period premises are discharged, not supplied. -/
theorem originalPrimitive_short {n m s t : ℕ}
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
    (Λ : Lambda) (b a : ℕ) (ha : 0 < a) (hab : a + 2 ≤ b)
    (hcoprime : b.Coprime a) (hr : primeOrder (cellSchur D hD.1) Λ = 1)
    (hKU : (jtMatrix (fun j : Fin n => P.xi j.succ)
      (fun j => P.zeta j.castSucc)).det = Λ ^ b)
    (hKW : (jtMatrix (fun j : Fin s => W.xi j.succ)
      (fun j => W.zeta j.castSucc)).det = Λ ^ a)
    (Δ : ℤ) (hspan : P.xi 0 - P.zeta (Fin.last n) = (b : ℤ) * Δ)
    (hqspan : q = ((b - a : ℕ) : ℤ) * Δ)
    (p₀ p₁ : Polynomial ℚ) (hpq : IsCoprime p₀ p₁)
    (hdep : c.residueMap P.schur ^ a / c.residueMap W.schur ^ b =
      Polynomial.aeval (c.residueMap Q.schur / c.residueMap P.schur ^ 2) p₀ /
        Polynomial.aeval (c.residueMap Q.schur / c.residueMap P.schur ^ 2) p₁)
    (hnonconstant : ∃ i j, c.originalInternalResidue P i ≠ c.originalInternalResidue P j) :
    ∃ h : ℕ, 0 < h ∧ h ≤ b - a - 1 ∧
      PowerSeries.coeff h (c.originalDeterminantDefect P A Q a b p₀ p₁) ≠ 0 := by
  have hcount : originalSelectedCount (hD := hD) P = b := by
    rw [originalSelectedCount_eq_primeOrder, hKU,
      primeOrder_pow (irreducible_cellSchur hD).prime, hr, mul_one]
  have htwo := c.originalPrimitive_nonconstant_active P W a b hcoprime hcount hnonconstant
  simpa only [one_mul] using c.originalManyActive_general P W A Q q v u z w
    hq hv hwindow hW hA hQ hcutq hcutLq hmax Λ b a 1 ha hab (by omega) hcoprime hr
    hKU hKW Δ hspan hqspan p₀ p₁ hpq hdep htwo

end SkewCornerDescent.Matrix.SelectedCoordinate
