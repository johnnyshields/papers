/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalRowClassHessian
import SkewCornerDescent.Matrix.OriginalClosureRowHessian
import SkewCornerDescent.Matrix.OriginalCapProductHessian
import SkewCornerDescent.Matrix.ResidueAffineHessian

/-!
# Actual all-row affine plane labels have an integer origin

Supports `shields-2026-skew-corner-descent.tex` (`cor:row-pencil`).
The actual full closure supplies its integer mixed-jet origin. The actual
source response class supplies its own integer jet, and the same true-cap
product supplies the nonzero unit jet. Their rational affine equality recovers
the label as an integer difference. No jet or integer origin is assumed.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Actual all-row plane labels share one produced integer origin and a
three-value range, reduced to two at a coincident cap square. Class-top and
affine equalities are the inputs supplied by the actual residue classifier. -/
theorem original_row_plane_integer_origin {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (hrows : ∀ C ∈ edgeComponents (diagramInterior P.cells), (C.image Prod.fst).card = 1)
    (p q : ℕ+) (hp : c.top < p) (hq : c.top < q)
    (hpTop : originalHessenbergDistance (hD := hD) P 0 0 = (p : ℤ))
    (hqTop : originalHessenbergDistance (hD := hD) P (Fin.last _) (Fin.last _) = (q : ℤ)) :
    let middle : Fin (originalSelectedCount (hD := hD) Q + 1) :=
      ⟨originalSelectedCount (hD := hD) P, by
        rw [originalHorizontalClosure_profile_selected_count P Q v hQ]; omega⟩
    ∃ origin : ℕ, origin ≤ (if p = q then 1 else 2) ∧
      ∀ (X : c.OriginalResponseClass P) (a : ℚ),
        (p : ℤ) + (q : ℤ) = (c.originalResponseClassTop P hB X : ℤ) →
        X.val = c.regularResidue (c.originalHessenbergResponse Q middle middle) -
          (a : OtherField c.top) * c.originalTrueCapProduct P →
        ∃ k : ℕ, k ≤ (if p = q then 1 else 2) ∧ a = (k : ℚ) - (origin : ℚ) := by
  classical
  obtain ⟨origin, horigin, hbase⟩ := c.originalHorizontalClosure_row_hessian_bound P Q v hQ hB
    hmax hrows p q hp hq hpTop hqTop
  have hcap := c.original_diagonal_product_hessian P hB hmax 0 (Fin.last _) p q hp hq
    hpTop hqTop
  let w : OtherField c.top := if p = q then 2 else 1
  have hw : w ≠ 0 := by dsimp only [w]; split_ifs <;> norm_num
  have hcap' : residueGeneratorDeriv c.top ⟨p, ne_of_gt hp⟩
      (residueGeneratorDeriv c.top ⟨q, ne_of_gt hq⟩ (c.originalTrueCapProduct P)) = w := hcap
  dsimp only at hbase ⊢
  refine ⟨origin, horigin, ?_⟩
  intro X a htop haffine
  have hleft : originalHessenbergDistance (hD := hD) P 0 0 < (p : ℤ) + (q : ℤ) := by
    rw [hpTop]
    have hpos : (0 : ℤ) < (q : ℤ) := by exact_mod_cast q.pos
    omega
  have hright : originalHessenbergDistance (hD := hD) P (Fin.last _) (Fin.last _) <
      (p : ℤ) + (q : ℤ) := by
    rw [hqTop]
    have hpos : (0 : ℤ) < (p : ℤ) := by exact_mod_cast p.pos
    omega
  obtain ⟨k, hk, hjet⟩ := c.originalResponseClass_row_hessian_bound P hB hmax hrows X p q hp hq
    htop hleft hright
  refine ⟨k, hk, ?_⟩
  exact residue_affine_label_of_integer_mixed_jets c.top ⟨p, ne_of_gt hp⟩ ⟨q, ne_of_gt hq⟩
    a X.val _ (c.originalTrueCapProduct P) w hw origin k haffine hjet hbase hcap'

end SkewCornerDescent.Matrix.SelectedCoordinate
