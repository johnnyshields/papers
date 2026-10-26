/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.ThinMateGeometry
import Mathlib.Data.Set.Card

/-!
# The complete class at and above the sharp boundary

Formalizes the superthreshold clause of `thm:sharp-inflation` and
`eq:inflation-class` in `shields-2026-skew-class-inflation.tex`.
An arbitrary connected inflated mate is first deflated, its entire
original geometry is reconstructed, and boundary injectivity fixes the
outer composition.  No restriction to a preselected family of mates is
assumed.  Sorry-free.
-/

namespace SkewClassInflation.ThinParameters

open SkewJacobiNegative

variable (B : ThinParameters)

/-- The entire connected Schur class above the boundary consists of exactly two rotations. -/
theorem superthreshold_full_class {M : ℕ} (α : Composition M) (hM : 0 < M)
    (t : ℕ) (ht : B.boundary.p ≤ t) :
    (ConnectedProfile.inflate t (B.diagram α hM)).schurClass =
      {ConnectedProfile.inflate t (B.diagram α hM),
        (ConnectedProfile.inflate t (B.diagram α hM)).rotate} := by
  ext H
  constructor
  · intro hH
    obtain ⟨E, hE, rfl⟩ := ConnectedProfile.inflation_no_escape (B.diagram α hM) t hH
    obtain ⟨k, Q⟩ := E
    change (ConnectedProfile.inflate t (⟨k, Q⟩ : ConnectedProfile)).schur =
      (ConnectedProfile.inflate t (B.diagram α hM)).schur at hH
    have he : Q.toBetaDiagram.schur = (B.diagram α hM).2.toBetaDiagram.schur := by
      change profileSchur Q = profileSchur (B.diagram α hM).2 at hE
      simpa only [profileSchur_eq_inherited, Gluing.Profile.toBetaDiagram_schur] using hE
    obtain ⟨β, hβ | hβ⟩ := B.arbitrary_mate_geometry α hM Q he
    · have hh : (ConnectedProfile.inflate t (B.diagram β hM)).schur =
          (ConnectedProfile.inflate t (B.diagram α hM)).schur := by
        simpa only [hβ] using hH
      have hβα := B.superthreshold_function_injective hM t ht hh
      subst β
      exact Set.mem_insert_iff.mpr (Or.inl (congrArg (ConnectedProfile.inflate t) hβ))
    · have hh : (ConnectedProfile.inflate t (B.diagram β hM)).schur =
          (ConnectedProfile.inflate t (B.diagram α hM)).schur := by
        simpa only [hβ, ← ConnectedProfile.inflate_rotate, ConnectedProfile.schur_rotate] using hH
      have hβα := B.superthreshold_function_injective hM t ht hh
      subst β
      apply Set.mem_insert_iff.mpr
      right
      apply Set.mem_singleton_iff.mpr
      exact (congrArg (ConnectedProfile.inflate t) hβ).trans
        (ConnectedProfile.inflate_rotate t (B.diagram α hM)).symm
  · intro hH
    rcases Set.mem_insert_iff.mp hH with rfl | hH
    · rfl
    · rw [Set.mem_singleton_iff] at hH
      subst H
      exact ConnectedProfile.schur_rotate _

/-- Inflation does not identify the two literal orientations. -/
theorem inflated_diagram_ne_rotated {M : ℕ} (α β : Composition M) (hM : 0 < M)
    (t : ℕ) : ConnectedProfile.inflate t (B.diagram α hM) ≠
      (ConnectedProfile.inflate t (B.diagram β hM)).rotate := by
  rw [ConnectedProfile.inflate_rotate]
  exact fun he => B.diagram_ne_rotated α β hM (ConnectedProfile.inflate_injective t he)

/-- The full class has cardinality two at the boundary and at every later inflation. -/
theorem superthreshold_class_card {M : ℕ} (α : Composition M) (hM : 0 < M)
    (t : ℕ) (ht : B.boundary.p ≤ t) :
    (ConnectedProfile.schurClass (ConnectedProfile.inflate t (B.diagram α hM))).ncard = 2 := by
  rw [B.superthreshold_full_class α hM t ht]
  exact Set.ncard_pair (B.inflated_diagram_ne_rotated α α hM t)

end SkewClassInflation.ThinParameters
