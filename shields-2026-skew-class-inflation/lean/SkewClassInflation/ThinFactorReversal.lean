/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.RibbonFactorReversal
import SkewClassInflation.ThinFullClass

/-!
# Actual factor-reversal mates of the thin and subthreshold classes

The construction direction of the factor-reversal statement in the first class of
`thm:sharp-inflation` of `shields-2026-skew-class-inflation.tex`.
Every finite reversal construction is supplied by actual ordinary
composition factors and remains a mate throughout the strict
subthreshold interval.  Sorry-free.
-/

namespace SkewClassInflation.ThinParameters

open SkewJacobiNegative

variable (B : ThinParameters)

/-- Every actual outer factor-reversal construction supplies a genuine complete thin mate. -/
theorem factor_reversal_mate {M : ℕ} (α β : Composition M) (hM : 0 < M)
    (he : RibbonFactorReversal α β) :
    B.diagram β hM ∈ ConnectedProfile.schurClass (B.diagram α hM) := by
  have hr := (B.diagram_schur_eq_iff β α hM).mpr (factor_reversal_ribbon_eq he).symm
  change profileSchur (B.diagram β hM).2 = profileSchur (B.diagram α hM).2
  simpa only [profileSchur_eq_inherited, Gluing.Profile.toBetaDiagram_schur] using hr

/-- Every constructed mate survives actual whole-diagram inflation strictly below the threshold. -/
theorem factor_reversal_subthreshold_mate {M : ℕ} (α β : Composition M) (hM : 0 < M)
    (he : RibbonFactorReversal α β) (t : ℕ) (ht : t < B.boundary.p) :
    ConnectedProfile.inflate t (B.diagram β hM) ∈
      ConnectedProfile.schurClass (ConnectedProfile.inflate t (B.diagram α hM)) := by
  rw [B.subthreshold_full_class α hM t ht]
  exact ⟨B.diagram β hM, B.factor_reversal_mate α β hM he, rfl⟩

/-- Their entire globally rotated orientations are also genuine subthreshold mates. -/
theorem factor_reversal_rotated_subthreshold_mate {M : ℕ}
    (α β : Composition M) (hM : 0 < M) (he : RibbonFactorReversal α β)
    (t : ℕ) (ht : t < B.boundary.p) :
    ConnectedProfile.rotate (ConnectedProfile.inflate t (B.diagram β hM)) ∈
      ConnectedProfile.schurClass (ConnectedProfile.inflate t (B.diagram α hM)) := by
  have hh := B.factor_reversal_subthreshold_mate α β hM he t ht
  change ConnectedProfile.schur
      (ConnectedProfile.rotate (ConnectedProfile.inflate t (B.diagram β hM))) = _
  rw [ConnectedProfile.schur_rotate]
  exact hh

end SkewClassInflation.ThinParameters
