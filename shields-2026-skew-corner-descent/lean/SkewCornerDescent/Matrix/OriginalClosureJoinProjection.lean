/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalClosureHalfCapProjection
import SkewCornerDescent.Matrix.OriginalPrivateCapLocalization
import SkewCornerDescent.Matrix.OriginalClosureResponses

/-!
# Complete inverse projections at the actual horizontal join

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
The literal horizontal closure has no cut unit. Its full selected-to-selected
join contraction is therefore the complete source upper cap below the join,
or the complete source lower cap above it. Ordinary endpoint support removes
only the opposite side, never entries inside retained components. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- At or below the literal horizontal join, its full contraction equals the
complete original upper cap at the lower-copy selected endpoint. -/
theorem originalHorizontalClosure_join_projection_lower {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells)
    (b d : OriginalSelectedBlocks (hD := hD) P)
    (A T : LaurentPolynomial (OtherField c.top)) (z : ℤ) (hz : z ≤ P.xi 0)
    (hA : ∀ j, j < 0 → A.coeff j = 0) (hT : ∀ j, j < 0 → T.coeff j = 0) :
    c.originalIntervalInverseProjection Q
        (some (originalHorizontalClosureSelectedCopy P Q v hQ true b))
        (some (originalHorizontalClosureSelectedCopy P Q v hQ false d)) A T z =
      c.originalCapInverseProjection P true d A T z := by
  have hj := originalHorizontalClosure_profile_join_private P Q v hQ
  have hb : P.xi 0 < Q.xi (originalRowSplitEquiv (hD := hD) Q
      (.inl (some (originalHorizontalClosureSelectedCopy P Q v hQ true b)))) := by
    have he := (originalHorizontalClosure_retained_endpoints P Q v hQ true b).1
    simp only [originalClosureBlockDisplacement, ↓reduceIte, sub_zero,
      originalRowSplitEquiv_selected] at he
    have hp := P.xi_pos b.val.val.succ
    rw [originalRowSplitEquiv_selected]
    omega
  have hno (i : OriginalResponseInterval (hD := hD) Q
      (some (originalHorizontalClosureSelectedCopy P Q v hQ true b))
      (some (originalHorizontalClosureSelectedCopy P Q v hQ false d))) :
      ¬ (originalResponseRows Q i.1.1 = P.xi 0 ∧ originalResponseCols Q i.1.1 = P.xi 0) :=
    fun h => originalHorizontalClosure_join_no_unit P Q v hQ i.1.1 h.2
  rw [c.originalInterval_private_lower_cap_without_unit Q _ _ (P.xi 0) hj.1 hj.2 hb
    hno A T z hz hA hT]
  have hcopy := c.originalHorizontalClosure_half_cap_projection P Q v hQ false true d A T z
  simpa only [Bool.false_eq_true, ↓reduceIte, zero_add, add_zero] using hcopy.symm

/-- Above the literal horizontal join, its full contraction equals the
complete original lower cap, shifted by the actual source span. -/
theorem originalHorizontalClosure_join_projection_upper {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells)
    (b d : OriginalSelectedBlocks (hD := hD) P)
    (A T : LaurentPolynomial (OtherField c.top)) (z : ℤ) (hz : P.xi 0 ≤ z)
    (hA : ∀ j, j < 0 → A.coeff j = 0) (hT : ∀ j, j < 0 → T.coeff j = 0) :
    c.originalIntervalInverseProjection Q
        (some (originalHorizontalClosureSelectedCopy P Q v hQ true b))
        (some (originalHorizontalClosureSelectedCopy P Q v hQ false d)) A T z =
      c.originalCapInverseProjection P false b A T (z - P.xi 0) := by
  have hj := originalHorizontalClosure_profile_join_private P Q v hQ
  have hd : Q.zeta (originalColSplitEquiv (hD := hD) Q
      (.inl (some (originalHorizontalClosureSelectedCopy P Q v hQ false d)))) < P.xi 0 := by
    have he := (originalHorizontalClosure_retained_endpoints P Q v hQ false d).2
    simp only [originalClosureBlockDisplacement, Bool.false_eq_true, ↓reduceIte,
      add_sub_cancel_right, originalColSplitEquiv_selected] at he
    have hp := c.originalFirstCapDistance_gt_top P d
    unfold originalFirstCapDistance at hp
    have ht := c.top.property
    rw [originalColSplitEquiv_selected]
    omega
  have hno (i : OriginalResponseInterval (hD := hD) Q
      (some (originalHorizontalClosureSelectedCopy P Q v hQ true b))
      (some (originalHorizontalClosureSelectedCopy P Q v hQ false d))) :
      ¬ (originalResponseRows Q i.1.1 = P.xi 0 ∧ originalResponseCols Q i.1.1 = P.xi 0) :=
    fun h => originalHorizontalClosure_join_no_unit P Q v hQ i.1.1 h.2
  rw [c.originalInterval_private_upper_cap_without_unit Q _ _ (P.xi 0) hj.1 hj.2 hd
    hno A T z hz hA hT]
  have htop : Q.xi 0 = 2 * P.xi 0 := by
    have ht := originalHorizontalClosure_xi_upper P Q v hQ 0
    change Q.xi 0 = P.xi 0 + P.xi 0 at ht
    omega
  rw [htop]
  have hcopy := c.originalHorizontalClosure_half_cap_projection P Q v hQ true false b
    A T (z - P.xi 0)
  simpa only [↓reduceIte, two_mul, sub_add_cancel] using hcopy.symm

end SkewCornerDescent.Matrix.SelectedCoordinate
