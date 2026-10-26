/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalCoreHessianProjection
import SkewCornerDescent.Matrix.OriginalCapCorePhase
import SkewCornerDescent.Matrix.OriginalClosureHalfCapProjection
import SkewCornerDescent.Matrix.OriginalPrivateUnitProjection

/-!
# Actual phase cores as normalized Hessian weights

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
Actual selected-occurrence polynomials supply all ordinary support and
normalization premises of the full inverse-projection comparison. Literal
closure copying supplies the reference weights. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The actual selected phase cores are ordinary Laurent weights normalized
at zero; neither support nor normalization is carried as an extra premise. -/
theorem originalSelectedCore_laurent_normalized {n : ℕ} (P : Profile n)
    (i j : Fin (originalSelectedCount (hD := hD) P)) :
    (∀ k, k < 0 → (c.originalSelectedCoreLeft P i).toLaurent.coeff k = 0) ∧
      (∀ k, k < 0 → (c.originalSelectedCoreRight P j).toLaurent.coeff k = 0) ∧
      (c.originalSelectedCoreLeft P i).toLaurent.coeff 0 = 1 ∧
      (c.originalSelectedCoreRight P j).toLaurent.coeff 0 = 1 := by
  have coeff0 (f : Polynomial (OtherField c.top)) : f.toLaurent.coeff 0 = f.coeff 0 := by
    change (Finsupp.mapDomain (fun k : ℕ => (k : ℤ)) f.toFinsupp.coeff) 0 = _
    exact Finsupp.mapDomain_apply_of_injective Nat.cast_injective _ 0
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k hk
    unfold originalSelectedCoreLeft
    rw [c.selected_core_left_toLaurent]
    exact endpointProfile_coeff_negative _ _
      (fun a => (c.selected_core_left_distances _
        (originalSelectedProfile_schur P (originalSelectedEnumeration P i)).symm a).1.le) k hk
  · intro k hk
    unfold originalSelectedCoreRight
    rw [c.selected_core_right_toLaurent]
    exact endpointProfile_coeff_negative _ _
      (fun a => (c.selected_core_right_distances _
        (originalSelectedProfile_schur P (originalSelectedEnumeration P j)).symm a).1.le) k hk
  · rw [coeff0]
    exact (c.originalSelectedCore_constants P i).1
  · rw [coeff0]
    exact (c.originalSelectedCore_constants P j).2

/-- Literal placement in either closure copy supplies both exact reference
proper-core polynomials from the actual selected source occurrence. -/
theorem originalSelectedCore_closure_copy {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (copy : Bool)
    (i : Fin (originalSelectedCount (hD := hD) P)) :
    let b := originalSelectedEnumeration (hD := hD) P i
    let d := originalHorizontalClosureSelectedCopy P Q v hQ copy b
    c.originalSelectedCoreLeft P i = c.selectedCoreLeftPolynomial
        (interiorBlockProfile Q d.val.val (originalBlockSelected_nonempty Q d.val d.property))
        (originalSelectedProfile_schur Q d).symm ∧
      c.originalSelectedCoreRight P i = c.selectedCoreRightPolynomial
        (interiorBlockProfile Q d.val.val (originalBlockSelected_nonempty Q d.val d.property))
        (originalSelectedProfile_schur Q d).symm := by
  exact c.original_selected_core_polynomials_of_translate P Q _ _
    (originalClosureBlockDisplacement P copy)
    (originalHorizontalClosure_selected_normalized_cells P Q v hQ copy _)

/-- An actual ordered source interval exposes its mixed Hessian directly as
its two full inverse contractions weighted by the actual phase polynomials. -/
theorem originalLocalResponse_phase_hessian {n : ℕ} (P : Profile n)
    (i j : Fin (originalSelectedCount (hD := hD) P)) (hij : i < j)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (p q : ℕ+) (hp : c.top < p) (hq : c.top < q)
    (hsum : (p : ℤ) + (q : ℤ) =
      P.xi (originalRowSplitEquiv (hD := hD) P
        (.inl (some (originalSelectedEnumeration (hD := hD) P i)))) -
      P.zeta (originalColSplitEquiv (hD := hD) P
        (.inl (some (originalSelectedEnumeration (hD := hD) P j))))) :
    let b := originalSelectedEnumeration (hD := hD) P i
    let d := originalSelectedEnumeration (hD := hD) P j
    let x := P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some b)))
    let A := (c.originalSelectedCoreLeft P i).toLaurent
    let T := (c.originalSelectedCoreRight P j).toLaurent
    residueGeneratorDeriv c.top ⟨p, ne_of_gt hp⟩
      (residueGeneratorDeriv c.top ⟨q, ne_of_gt hq⟩
        (c.regularResidue (c.originalLocalResponse P (some b) (some d)))) =
      -c.originalIntervalInverseProjection P (some b) (some d) A T (x - (q : ℤ)) -
        c.originalIntervalInverseProjection P (some b) (some d) A T (x - (p : ℤ)) := by
  exact c.originalLocalResponse_proper_core_hessian P _ _
    (originalSelectedEnumeration_label_strictMono P hij).le hmax p q hp hq hsum

end SkewCornerDescent.Matrix.SelectedCoordinate
