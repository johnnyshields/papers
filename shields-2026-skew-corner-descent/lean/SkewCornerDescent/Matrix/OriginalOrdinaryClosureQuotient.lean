/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalOrdinaryClosureScalars
import SkewCornerDescent.Matrix.OriginalOrdinaryRemovedBalance
import SkewCornerDescent.Matrix.OriginalClosureQuotient

/-!
# Signed original residue quotient for either ordinary closure

Formalizes `shields-2026-skew-corner-descent.tex`, `prop:normal-interface`.
The unchanged true caps, both full internal source products and the complete
removed determinant square identify the actual original closure/source
quotient with its actual central response divided by the source cap product.
The determinant orientation sign is produced and retained.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
open scoped BigOperators
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The complete residue quotient of either actual ordinary closure is its
actual central response divided by both source caps, up to the produced
orientation sign.  Full removed determinants and both original internal
inventories are supplied from the actual geometry. -/
theorem originalOrdinaryClosure_residue_quotient {n m : ℕ}
    (P : Profile n) (Q : Profile m) (z : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate z Q.cells ∨
      originalVerticalClosure P = translate z Q.cells)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ)) :
    let center : Fin (originalSelectedCount (hD := hD) Q - 1) :=
      ⟨originalSelectedCount (hD := hD) P - 1, by
        rw [originalOrdinaryClosure_selected_count P Q z hQ]
        omega⟩
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      c.residueMap Q.schur / c.residueMap P.schur^2 =
        (ε : OtherField c.top) * c.originalInternalResidue Q center /
          c.originalTrueCapProduct P := by
  classical
  obtain ⟨εP, hεP, hP⟩ := c.originalHessenberg_residue_signed_factorization P
  obtain ⟨εQ, hεQ, hQ'⟩ := c.originalHessenberg_residue_signed_factorization Q
  have hBQ : 0 < originalSelectedCount (hD := hD) Q := by
    rw [originalOrdinaryClosure_selected_count P Q z hQ]
    omega
  rw [c.originalHessenberg_residue_cap_product P hB] at hP
  rw [c.originalHessenberg_residue_cap_product Q hBQ,
    c.originalOrdinaryClosure_true_cap_product P Q z hQ hB,
    c.originalOrdinaryClosure_internal_residue_product P Q z hQ hB,
    originalOrdinaryClosure_removed_square P Q z hQ, map_pow] at hQ'
  have hs : (εP : OtherField c.top)^2 = 1 := by
    rcases hεP with h | h <;> simp only [h, Int.cast_one, Int.cast_neg, neg_one_sq, one_pow]
  have hd := (c.originalRemoved_residue_lower_scalar P hmax).2
  have hF := c.originalTrueCapProduct_ne_zero P hB hmax
  have hT : (∏ i, c.originalInternalResidue P i) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact c.originalHessenberg_residue_ne_zero P hB hmax ⟨i.val+1, by omega⟩
  refine ⟨εQ, hεQ, ?_⟩
  rw [hP, hQ', mul_pow, mul_pow, mul_pow, hs, one_mul]
  field_simp

end SkewCornerDescent.Matrix.SelectedCoordinate
