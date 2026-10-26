/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.SubthresholdClass
import SkewClassInflation.ThinRibbonSubstitution

/-!
# The complete thin class and its exact cardinality

Formalizes `thm:two-row-thin-class` and the class and cardinality
clauses of `thm:sharp-inflation` in
`shields-2026-skew-class-inflation.tex`.  The arbitrary-mate inverse,
faithful ribbon substitution, literal parameter injectivity, and
disjoint orientations are assembled without extra proof-gap premises.
Sorry-free.
-/

namespace SkewClassInflation.ThinParameters

open SkewJacobiNegative

variable (B : ThinParameters)

/-- Every thin mate is given by the outer ribbon class and one global orientation. -/
theorem thin_full_class {M : ℕ} (α : Composition M) (hM : 0 < M) :
    (B.diagram α hM).schurClass =
      (fun β : Composition M => B.diagram β hM) '' ribbonClass α ∪
      (fun β : Composition M => (B.diagram β hM).rotate) '' ribbonClass α := by
  ext H
  constructor
  · intro hH
    obtain ⟨k, Q⟩ := H
    have he : Q.toBetaDiagram.schur = (B.diagram α hM).2.toBetaDiagram.schur := by
      change profileSchur Q = profileSchur (B.diagram α hM).2 at hH
      simpa only [profileSchur_eq_inherited, Gluing.Profile.toBetaDiagram_schur] using hH
    obtain ⟨β, hβ | hβ⟩ := B.arbitrary_mate_geometry α hM Q he
    · apply Set.mem_union_left
      refine ⟨β, ?_, hβ.symm⟩
      apply (B.diagram_schur_eq_iff β α hM).mp
      exact (congrArg (fun D : ConnectedProfile => D.2.toBetaDiagram.schur) hβ).symm.trans he
    · apply Set.mem_union_right
      refine ⟨β, ?_, hβ.symm⟩
      apply (B.diagram_schur_eq_iff β α hM).mp
      have hh : (B.diagram β hM).schur = (B.diagram α hM).schur := by
        rw [← ConnectedProfile.schur_rotate (B.diagram β hM), ← hβ]
        exact hH
      simpa only [ConnectedProfile.schur, profileSchur_eq_inherited,
        Gluing.Profile.toBetaDiagram_schur] using hh
  · rintro (⟨β, hβ, rfl⟩ | ⟨β, hβ, rfl⟩)
    · have he := (B.diagram_schur_eq_iff β α hM).mpr hβ
      change profileSchur (B.diagram β hM).2 = profileSchur (B.diagram α hM).2
      simpa only [profileSchur_eq_inherited, Gluing.Profile.toBetaDiagram_schur] using he
    · change (B.diagram β hM).rotate.schur = (B.diagram α hM).schur
      rw [ConnectedProfile.schur_rotate]
      have he := (B.diagram_schur_eq_iff β α hM).mpr hβ
      simpa only [ConnectedProfile.schur, profileSchur_eq_inherited,
        Gluing.Profile.toBetaDiagram_schur] using he

/-- The two entire parameter images are disjoint, not just distinct for a fixed outer word. -/
theorem thin_orientations_disjoint {M : ℕ} (α : Composition M) (hM : 0 < M) :
    Disjoint ((fun β : Composition M => B.diagram β hM) '' ribbonClass α)
      ((fun β : Composition M => (B.diagram β hM).rotate) '' ribbonClass α) := by
  apply Set.disjoint_left.mpr
  rintro H ⟨β, _, hβ⟩ ⟨γ, _, hγ⟩
  exact B.diagram_ne_rotated β γ hM (hβ.trans hγ.symm)

/-- Rotation on the full dependent profile space is an involution. -/
theorem rotated_diagram_injective {M : ℕ} (hM : 0 < M) :
    Function.Injective (fun β : Composition M => (B.diagram β hM).rotate) := by
  intro β γ he
  apply B.diagram_injective hM
  have hh := congrArg ConnectedProfile.rotate he
  simpa only [ConnectedProfile.rotate, Gluing.Profile.rotate_rotate] using hh

/-- Every complete thin class is finite on the unrestricted connected-profile domain. -/
theorem thin_full_class_finite {M : ℕ} (α : Composition M) (hM : 0 < M) :
    (ConnectedProfile.schurClass (B.diagram α hM)).Finite := by
  rw [B.thin_full_class α hM]
  exact ((Set.toFinite (ribbonClass α)).image _).union
    ((Set.toFinite (ribbonClass α)).image _)

/-- The two disjoint orientations give exactly twice the outer ribbon-class cardinality. -/
theorem thin_full_class_card {M : ℕ} (α : Composition M) (hM : 0 < M) :
    (ConnectedProfile.schurClass (B.diagram α hM)).ncard = 2 * (ribbonClass α).ncard := by
  rw [B.thin_full_class α hM,
    Set.ncard_union_eq (B.thin_orientations_disjoint α hM)
      ((Set.toFinite (ribbonClass α)).image _)
      ((Set.toFinite (ribbonClass α)).image _),
    Set.ncard_image_of_injective _ (B.diagram_injective hM),
    Set.ncard_image_of_injective _ (B.rotated_diagram_injective hM)]
  omega

/-- The complete sharp class formula, with the exact threshold and arbitrary connected mates. -/
theorem inflation_full_class {M : ℕ} (α : Composition M) (hM : 0 < M) (t : ℕ) :
    (ConnectedProfile.inflate t (B.diagram α hM)).schurClass =
      if t < B.boundary.p then
        ConnectedProfile.inflate t '' (B.diagram α hM).schurClass
      else {ConnectedProfile.inflate t (B.diagram α hM),
        (ConnectedProfile.inflate t (B.diagram α hM)).rotate} := by
  split_ifs with ht
  · exact B.subthreshold_full_class α hM t ht
  · exact B.superthreshold_full_class α hM t (by omega)

/-- Both numerical class counts hold across the exact threshold. -/
theorem inflation_full_class_card {M : ℕ} (α : Composition M) (hM : 0 < M) (t : ℕ) :
    (ConnectedProfile.schurClass (ConnectedProfile.inflate t (B.diagram α hM))).ncard =
      if t < B.boundary.p then 2 * (ribbonClass α).ncard else 2 := by
  split_ifs with ht
  · rw [B.subthreshold_full_class α hM t ht,
      Set.ncard_image_of_injective _ (ConnectedProfile.inflate_injective t)]
    exact B.thin_full_class_card α hM
  · exact B.superthreshold_class_card α hM t (by omega)

end SkewClassInflation.ThinParameters
