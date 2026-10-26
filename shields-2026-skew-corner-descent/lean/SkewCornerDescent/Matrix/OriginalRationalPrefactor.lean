/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalClosureVirtualUnits
import SkewCornerDescent.Matrix.SignedNormalProducts

/-!
# The full actual rational prefactor and its nonzero residue

Supports `shields-2026-skew-corner-descent.tex` (`lem:original-transfer`).
The prefactor evaluates all signed rational factors at the full actual closure quotient.
Its residue is a unit because every rational virtual factor is nonzero on that chart.
No independent unit hypothesis is required. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing
open scoped BigOperators

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The original rational prefactor uses complete determinant germs and full inverses. -/
noncomputable def originalRationalPrefactor {n m : ℕ} {ι : Type*}
    (P : Profile n) (Q : Profile m) (s : Finset ι) (α : ι → ℚ) (e : ι → ℤ) (ε : ℤ) :
    PowerSeries (OtherField c.top) :=
  PowerSeries.C (ε : OtherField c.top) * signedNormalProduct s
    (fun i => c.normalPolynomialSeries Q.schur * (c.normalPolynomialSeries P.schur)⁻¹ ^ 2 -
      PowerSeries.C (α i : OtherField c.top)) e

/-- The exact residue-prefactor product is nonzero for arbitrary signed multiplicities. -/
theorem originalRationalPrefactor_residue_ne_zero {n m : ℕ} {ι : Type*}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (s : Finset ι) (α : ι → ℚ) (e : ι → ℤ) (ε : ℤ) (hε : ε = 1 ∨ ε = -1) :
    (ε : OtherField c.top) * ∏ i ∈ s,
      (c.residueMap Q.schur / c.residueMap P.schur ^ 2 - (α i : OtherField c.top)) ^ e i ≠ 0 := by
  classical
  apply mul_ne_zero
  · rcases hε with rfl | rfl <;> norm_num
  · apply Finset.prod_ne_zero_iff.mpr
    intro i _
    apply zpow_ne_zero
    have hf := c.originalSchur_residue_ne_zero P hB hmax
    have hT := c.originalVirtualClosure_residue_ne_zero P Q v hQ hB hmax (α i)
    intro hz
    have he := (div_eq_iff (pow_ne_zero 2 hf)).mp (sub_eq_zero.mp hz)
    exact hT (sub_eq_zero.mpr he)

/-- The full actual prefactor has the same nonzero residue, not a residue-only replacement. -/
theorem originalRationalPrefactor_constant_ne_zero {n m : ℕ} {ι : Type*}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (s : Finset ι) (α : ι → ℚ) (e : ι → ℤ) (ε : ℤ) (hε : ε = 1 ∨ ε = -1) :
    PowerSeries.constantCoeff (c.originalRationalPrefactor P Q s α e ε) ≠ 0 := by
  have he := c.originalRationalPrefactor_residue_ne_zero P Q v hQ hB hmax s α e ε hε
  simpa only [originalRationalPrefactor, map_mul, PowerSeries.constantCoeff_C,
    signedNormalProduct_constant, map_sub, map_pow, PowerSeries.constantCoeff_inv,
    c.normalPolynomialSeries_constant, div_eq_mul_inv, ← inv_pow] using he

end SkewCornerDescent.Matrix.SelectedCoordinate
