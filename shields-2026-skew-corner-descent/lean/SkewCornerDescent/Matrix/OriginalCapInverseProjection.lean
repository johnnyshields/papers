/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalClosureCapIntervals
import SkewCornerDescent.Matrix.OriginalHessianProjection
import SkewCornerDescent.Matrix.ProjectionTransport
import SkewCornerDescent.Matrix.OriginalLiteralWindowCaps
import SkewCornerDescent.Matrix.OriginalWindowProfileEndpoints
import SkewCornerDescent.Matrix.OriginalPrivateUnitVertex

/-!
# Complete actual cap inverse projections in literal closure copies

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
Literal whole-cap equivalences produce every affine endpoint and full inverse
entry. The original residue homomorphism is unchanged, and no nonrow inverse
entry is discarded. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The full weighted inverse contraction of one actual exterior-cap interval. -/
noncomputable def originalCapInverseProjection {n : ℕ} (P : Profile n) (upper : Bool)
    (b : OriginalSelectedBlocks (hD := hD) P)
    (A T : LaurentPolynomial (OtherField c.top)) (z : ℤ) : OtherField c.top :=
  letI := c.originalResponseResidueIntervalInverse P
    (originalClosureCapLeft upper b) (originalClosureCapRight upper b)
  let row := fun i : OriginalResponseInterval (hD := hD) P
    (originalClosureCapLeft upper b) (originalClosureCapRight upper b) =>
      originalResponseRows P i.1.1
  let col := fun i : OriginalResponseInterval (hD := hD) P
    (originalClosureCapLeft upper b) (originalClosureCapRight upper b) =>
      originalResponseCols P i.1.1
  profileInverseProjection row col (⅟(vertexBetaMatrix c.residueMap row col)) A T z

/-- Every complete actual exterior-cap projection equals its literal closure
copy's projection at the transported content position. The source supplies both
actual inverses and all endpoint correspondences. -/
theorem originalHorizontalClosure_cap_inverse_projection {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (upper : Bool)
    (b : OriginalSelectedBlocks (hD := hD) P)
    (A T : LaurentPolynomial (OtherField c.top)) (z : ℤ) :
    let q := originalHorizontalClosureSelectedCopy P Q v hQ upper b
    let w := originalClosureBlockDisplacement P upper
    c.originalCapInverseProjection P upper b A T z =
      c.originalCapInverseProjection Q upper q A T (z + (w.2 - w.1)) := by
  classical
  let q := originalHorizontalClosureSelectedCopy P Q v hQ upper b
  let e := originalClosureCapIntervalEquiv P Q v hQ upper b
  let w := originalClosureBlockDisplacement P upper
  let := c.originalResponseResidueIntervalInverse P
    (originalClosureCapLeft upper b) (originalClosureCapRight upper b)
  let := c.originalResponseResidueIntervalInverse Q
    (originalClosureCapLeft upper q) (originalClosureCapRight upper q)
  dsimp only [originalCapInverseProjection]
  apply profileInverseProjection_affine_beta_copy c.residueMap e _ _ _ _ A T z (w.2 - w.1)
  · intro i
    simpa only [add_sub_assoc] using
      (originalHorizontalClosure_cap_interval_endpoints P Q v hQ upper b i).1
  · intro i
    simpa only [add_sub_assoc] using
      (originalHorizontalClosure_cap_interval_endpoints P Q v hQ upper b i).2

/-- An intact complete cap in a literal whole window has the same full actual
inverse projection after content translation. Boundary exclusion and literal
component copying produce the complete retained-index equivalence. -/
theorem originalLiteralWindow_cap_inverse_projection {n m : ℕ}
    (P : Profile n) (Q : Profile m) (lo hi : ℤ) (v : ℤ × ℤ)
    (hwindow : Q.cells = translate v
      (P.cells.filter fun x => lo ≤ content x ∧ content x < hi))
    (hlo : ∀ x ∈ diagramInterior P.cells, content x ≠ lo)
    (hhi : ∀ x ∈ diagramInterior P.cells, content x ≠ hi)
    (upper : Bool) (b : OriginalSelectedBlocks (hD := hD) P)
    (b' : OriginalSelectedBlocks (hD := hD) Q)
    (hcontained : ∀ a, originalCapBlockSide upper b a → originalBlockInWindow P lo hi a)
    (he : translate v (interiorBlockCells P b.val.val) = interiorBlockCells Q b'.val.val)
    (A T : LaurentPolynomial (OtherField c.top)) (z : ℤ) :
    c.originalCapInverseProjection P upper b A T z =
      c.originalCapInverseProjection Q upper b' A T (z + content v) := by
  classical
  let q := content v
  have hbounds := originalLiteralWindow_profile_bounds P Q lo hi v hwindow hlo hhi
  have hfilter : Q.cells.filter (fun x => lo + q ≤ content x ∧ content x < hi + q) =
      Q.cells := Finset.filter_eq_self.mpr hbounds.1
  have hcontained' (a : OriginalBlocks Q) (_ : originalCapBlockSide upper b' a) :
      originalBlockInWindow Q (lo + q) (hi + q) a :=
    originalLiteralWindow_full_profile_blocks P Q lo hi v hwindow hlo hhi a
  obtain ⟨e, hend⟩ := originalLiteralWindow_cap_interval_equiv (hD := hD) P Q lo hi
    q v rfl (by rw [hfilter]; exact hwindow) hlo hbounds.2.1 hhi hbounds.2.2
    upper b b' hcontained hcontained' he
  let := c.originalResponseResidueIntervalInverse P
    (originalClosureCapLeft upper b) (originalClosureCapRight upper b)
  let := c.originalResponseResidueIntervalInverse Q
    (originalClosureCapLeft upper b') (originalClosureCapRight upper b')
  dsimp only [originalCapInverseProjection]
  apply profileInverseProjection_affine_beta_copy c.residueMap e _ _ _ _ A T z q
  · intro i
    exact (hend i).1
  · intro i
    exact (hend i).2

/-- A private lower-content end cut preserves its whole true right-cap
projection. The source supplies cap containment and both interior exclusions. -/
theorem originalWindow_lower_cap_inverse_projection {n m : ℕ}
    (P : Profile n) (Q : Profile m) (hi : ℤ) (v : ℤ × ℤ)
    (hwindow : Q.cells = translate v
      (P.cells.filter fun x => 0 ≤ content x ∧ content x < hi))
    (hprivate : diagLo P.cells hi = diagHi P.cells hi)
    (b : OriginalSelectedBlocks (hD := hD) P) (b' : OriginalSelectedBlocks (hD := hD) Q)
    (hb : originalBlockInWindow P 0 hi b.val)
    (he : translate v (interiorBlockCells P b.val.val) = interiorBlockCells Q b'.val.val)
    (A T : LaurentPolynomial (OtherField c.top)) (z : ℤ) :
    c.originalCapInverseProjection P false b A T z =
      c.originalCapInverseProjection Q false b' A T (z + content v) := by
  have hlo : ∀ x ∈ diagramInterior P.cells, content x ≠ 0 := by
    intro x hx
    have h := (interior_content_strict P.isConnectedSkew_cells hx).1
    rw [Profile.minContent_cells] at h
    exact ne_of_gt h
  have hcontained (a : OriginalBlocks P) (ha : originalCapBlockSide false b a) :
      originalBlockInWindow P 0 hi a :=
    originalBlockInWindow_after_selected P hi b a hb ha
  exact c.originalLiteralWindow_cap_inverse_projection P Q 0 hi v hwindow hlo
    (private_diagonal_no_interior hprivate) false b b' hcontained he A T z

/-- A private upper-content end cut preserves its whole true left-cap
projection, including every complete nonrow unit block and boundary unit. -/
theorem originalWindow_upper_cap_inverse_projection {n m : ℕ}
    (P : Profile n) (Q : Profile m) (lo : ℤ) (v : ℤ × ℤ)
    (hwindow : Q.cells = translate v
      (P.cells.filter fun x => lo ≤ content x ∧ content x < P.xi 0))
    (hprivate : diagLo P.cells lo = diagHi P.cells lo)
    (b : OriginalSelectedBlocks (hD := hD) P) (b' : OriginalSelectedBlocks (hD := hD) Q)
    (hb : originalBlockInWindow P lo (P.xi 0) b.val)
    (he : translate v (interiorBlockCells P b.val.val) = interiorBlockCells Q b'.val.val)
    (A T : LaurentPolynomial (OtherField c.top)) (z : ℤ) :
    c.originalCapInverseProjection P true b A T z =
      c.originalCapInverseProjection Q true b' A T (z + content v) := by
  have hhi : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0 := by
    intro x hx
    exact ne_of_lt (P.content_bounds_cells (Finset.mem_filter.mp hx).1).2
  have hcontained (a : OriginalBlocks P) (ha : originalCapBlockSide true b a) :
      originalBlockInWindow P lo (P.xi 0) a :=
    originalBlockInWindow_before_selected P lo b a hb ha
  exact c.originalLiteralWindow_cap_inverse_projection P Q lo (P.xi 0) v hwindow
    (private_diagonal_no_interior hprivate) hhi true b b' hcontained he A T z

end SkewCornerDescent.Matrix.SelectedCoordinate
