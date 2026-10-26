/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewGluing.GluingBridge
import GluingCore.OlsonHarris.Plan.EdgeCase.HatShapes

/-!
# Normalization factors in the composition substrate

Formalizes `shields-2026-skew-corner-descent.tex`, «Corner transport»
(`eq:homomorphism`).  The three geometric normalization factors agree with the
certified composition substrate, including the empty-mark convention.

Sorry-free.
-/

namespace SkewGluing.MarkedInner

variable {ω : MarkedInner}

/-- The lower mark function agrees in the two representations. -/
theorem IsLegal.normalA_eq_gluing (h : ω.IsLegal) :
    ω.normalA h = GluingCore.cellSchur ω.toGluing.W := by
  change ω.normalA h = GluingCore.cellSchur ω.W
  by_cases hW : ω.W.Nonempty
  · simpa only [normalA, dite_eq_left hW, markA] using
      cellSchur_eq_gluing ω.W (h.isSkew_mark hW)
  · have he := Finset.not_nonempty_iff_eq_empty.mp hW
    simp [normalA, he]

/-- The finite hatted mark has the same cells in both APIs. -/
theorem IsLegal.hatMarkFin_eq (h : ω.IsLegal) :
    GluingCore.Plan.hatMarkFin ω.toGluing = ω.hatMarkWindow := by
  rw [GluingCore.Plan.MarkedInner.hatMarkFin_eq_hatMarkWindow h.toGluing.1
    h.toGluing.2.2.1]
  rfl

/-- The hatted mark normalization agrees, including the empty mark. -/
theorem IsLegal.normalB_eq_gluing (h : ω.IsLegal) :
    ω.normalB h = GluingCore.cellSchur (GluingCore.Plan.hatMarkFin ω.toGluing) := by
  rw [h.hatMarkFin_eq]
  by_cases hW : ω.W.Nonempty
  · simpa only [normalB, dite_eq_left hW, hatMarkB] using
      cellSchur_eq_gluing ω.hatMarkWindow (h.isSkew_hatMarkWindow hW)
  · have he := Finset.not_nonempty_iff_eq_empty.mp hW
    simp [normalB, hatMarkWindow, he]

/-- The finite hatted middle is actual southeast erosion. -/
theorem hatMiddleFin_eq (ω : MarkedInner) :
    GluingCore.Plan.hatMiddleFin ω.toGluing = diagramInterior ω.middle := rfl

/-- The middle normalization agrees in every legal case. -/
theorem IsLegal.normalC_eq_gluing (h : ω.IsLegal) :
    ω.normalC h = GluingCore.cellSchur (GluingCore.Plan.hatMiddleFin ω.toGluing) := by
  rw [hatMiddleFin_eq]
  by_cases hW : ω.W.Nonempty
  · simpa only [normalC, dite_eq_left hW, middleCofactor] using
      cellSchur_eq_gluing (diagramInterior ω.middle) (h.middle_connected hW).1.interior
  · have he := Finset.not_nonempty_iff_eq_empty.mp hW
    have hm : ω.middle = ω.E := by simp [middle, upper, translate, he]
    rw [hm]
    simpa only [normalC, dite_eq_right hW] using
      cellSchur_eq_gluing (diagramInterior ω.E) h.1.1.1.interior

end SkewGluing.MarkedInner
