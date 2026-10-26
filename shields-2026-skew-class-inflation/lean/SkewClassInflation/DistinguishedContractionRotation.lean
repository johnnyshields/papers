/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.DistinguishedContractionBoundaries
import SkewClassInflation.ProfileRotationSets

/-!
# Total distinguished contraction commutes with actual global rotation

The orientation step in `lem:total-contraction-inverse` of
`shields-2026-skew-class-inflation.tex`.  Translated support cancellation
and reflection identify the actual full profiles, not merely their Schur
functions.  Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative SkewJacobiNegative.Staircase

/-- Rotation and distinguished contraction commute on the actual row-bounded domain. -/
theorem contractAllMinimum_rotate {n : ℕ} (P : Profile n) (v : ℕ+) (hP : Thick P)
    (hr : ∀ i, v.val < P.r i) :
    (contractAllMinimum P.rotate v : ConnectedProfile) =
      ConnectedProfile.rotate (contractAllMinimum P v : ConnectedProfile) := by
  let C := (contractAllMinimum P v).2
  let D := (contractAllMinimum P.rotate v).2
  have hPr : ∀ i, v.val < P.rotate.r i := fun i => hr i.rev
  have hC := contractAllMinimum_sets P v hP hr
  have hD := contractAllMinimum_sets P.rotate v (profile_rotate_thick P hP) hPr
  have hspan : C.xi 0 = P.xi 0 := contractAllMinimum_span P v
  change C.toBetaDiagram.rowSet = _ ∧ C.toBetaDiagram.colSet = _ at hC
  change D.toBetaDiagram.rowSet = _ ∧ D.toBetaDiagram.colSet = _ at hD
  apply profileSigma_eq_of_full_sets D C.rotate
  · rw [hD.1, profile_rotate_rowSet P, profile_rotate_colSet P,
      profile_rotate_rowSet C, hspan, hC.2,
      Finset.image_sdiff _ _ (fun _ _ h => sub_right_injective h),
      Finset.image_image, Finset.image_image]
    congr 1
    apply Finset.image_congr
    intro x _
    dsimp only [Function.comp_def]
    ring
  · rw [hD.2, profile_rotate_colSet P, profile_rotate_rowSet P,
      profile_rotate_colSet C, hspan, hC.1,
      Finset.image_sdiff _ _ (fun _ _ h => sub_right_injective h),
      Finset.image_image, Finset.image_image]
    congr 1
    apply Finset.image_congr
    intro x _
    dsimp only [Function.comp_def]
    ring

end SkewClassInflation
