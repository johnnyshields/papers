/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.FactorGeneration
import SkewClassInflation.ThinCompositionCells

/-!
# The sharp inflation threshold, assembled

`thm:sharp-inflation` of `shields-2026-skew-class-inflation.tex` as one statement: the full
class formula across the threshold, both cardinalities, the literal subthreshold chart, and the
exhaustive generation clause.  Below the threshold the first class is exactly the set of
profiles obtained from the constructed presentation of `α` by finite ordinary-composition
factor reversals and global rotation.  Sorry-free.
-/

namespace SkewClassInflation.ThinParameters

open SkewJacobiNegative SkewGluing

variable (B : ThinParameters)

/-- Strictly below the threshold, the first class is exactly the factor-reversal and rotation
closure of the constructed presentation. -/
theorem inflation_class_generated {M : ℕ} (α : Composition M) (hM : 0 < M) (t : ℕ)
    (ht : t < B.boundary.p) :
    (ConnectedProfile.inflate t (B.diagram α hM)).schurClass =
      {H | ∃ β : Composition M, RibbonFactorReversal α β ∧
        (H = ConnectedProfile.inflate t (B.diagram β hM) ∨
          H = (ConnectedProfile.inflate t (B.diagram β hM)).rotate)} := by
  rw [B.subthreshold_full_class α hM t ht, B.thin_full_class α hM]
  ext H
  constructor
  · rintro ⟨G, hG | hG, rfl⟩
    · obtain ⟨β, hβ, rfl⟩ := hG
      exact ⟨β, (ribbonClass_eq_factorReversal α hM ▸ hβ : β ∈ {β | RibbonFactorReversal α β}),
        Or.inl rfl⟩
    · obtain ⟨β, hβ, rfl⟩ := hG
      exact ⟨β, (ribbonClass_eq_factorReversal α hM ▸ hβ : β ∈ {β | RibbonFactorReversal α β}),
        Or.inr (ConnectedProfile.inflate_rotate t _).symm⟩
  · rintro ⟨β, hβ, rfl | rfl⟩
    · exact ⟨_, Or.inl ⟨β, by rw [ribbonClass_eq_factorReversal α hM]; exact hβ, rfl⟩, rfl⟩
    · exact ⟨_, Or.inr ⟨β, by rw [ribbonClass_eq_factorReversal α hM]; exact hβ, rfl⟩,
        ConnectedProfile.inflate_rotate t _⟩

/-- `thm:sharp-inflation`: the full class formula, both cardinalities, the literal legal
subthreshold chart, and exhaustive generation by factor reversals and global rotation. -/
theorem sharp_inflation {M : ℕ} (α : Composition M) (hM : 0 < M) :
    (∀ t : ℕ, (ConnectedProfile.inflate t (B.diagram α hM)).schurClass =
      if t < B.boundary.p then
        ConnectedProfile.inflate t '' (B.diagram α hM).schurClass
      else {ConnectedProfile.inflate t (B.diagram α hM),
        (ConnectedProfile.inflate t (B.diagram α hM)).rotate}) ∧
    (∀ t : ℕ, (ConnectedProfile.inflate t (B.diagram α hM)).schurClass.ncard =
      if t < B.boundary.p then 2 * (ribbonClass α).ncard else 2) ∧
    (∀ t : ℕ, 0 < t → t < B.boundary.p →
      IsConnectedSkew (profileCells (outerRibbon α hM).2) ∧
      List.ofFn (outerRibbon α hM).2.r = α.blocks ∧
      (outerRibbon α hM).2.toBetaDiagram.schur = ribbonWord α.blocks ∧
      (B.inflationMark t).IsLegal ∧
      (attachmentCells (B.inflationMark t).W (B.inflationMark t).middle).card = 1 ∧
      (attachmentCells (B.inflationMark t).upper (B.inflationMark t).middle).card = 1 ∧
      (B.inflationMark t).compose (profileCells (outerRibbon α hM).2) =
        translate (1 - (M : ℤ), -(M : ℤ))
          (profileCells (Profile.inflate t (B.diagram α hM).2))) ∧
    (∀ t : ℕ, t < B.boundary.p →
      (ConnectedProfile.inflate t (B.diagram α hM)).schurClass =
        {H | ∃ β : Composition M, RibbonFactorReversal α β ∧
          (H = ConnectedProfile.inflate t (B.diagram β hM) ∨
            H = (ConnectedProfile.inflate t (B.diagram β hM)).rotate)}) :=
  ⟨fun t => B.inflation_full_class α hM t, fun t => B.inflation_full_class_card α hM t,
    fun t ht htp => B.subthreshold_literal_chart α hM t ht htp,
    fun t ht => B.inflation_class_generated α hM t ht⟩

end SkewClassInflation.ThinParameters
