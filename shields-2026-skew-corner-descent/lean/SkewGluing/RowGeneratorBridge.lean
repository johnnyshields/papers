/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewGluing.NormalizationBridge
import SkewGluing.CompositionAlgebra

/-!
# Generator values of geometric composition

Formalizes `shields-2026-skew-corner-descent.tex`, «Corner transport»
(`eq:homomorphism`).  A certified shape-algebra map has exactly the prescribed
complete-generator values on actual positive horizontal rows.

Sorry-free.
-/

namespace SkewGluing

/-- The one-row profile in the certified composition substrate. -/
def gluingRowProfile (j : ℕ+) : GluingCore.Profile 0 where
  r := fun _ => j
  g := Fin.elim0
  r_pos := fun _ => j.pos
  g_lt_castSucc := fun i => Fin.elim0 i
  g_lt_succ := fun i => Fin.elim0 i

/-- Both constructions give the same normalized horizontal row. -/
theorem gluingRowProfile_cells (j : ℕ+) :
    (gluingRowProfile j).cells = horizontalRow j := by
  ext x
  rcases x with ⟨a, b⟩
  simp [GluingCore.Profile.mem_cells, mem_horizontalRow, gluingRowProfile,
    GluingCore.Profile.xi, GluingCore.Profile.zeta, eq_comm]

/-- The Schur function of an actual row is its complete generator. -/
theorem gluing_cellSchur_horizontalRow (j : ℕ+) :
    GluingCore.cellSchur (horizontalRow j) = MvPolynomial.X j := by
  rw [← gluingRowProfile_cells, GluingCore.cellSchur_cells]
  unfold GluingCore.Profile.schur
  rw [Matrix.det_fin_one]
  change GluingCore.hh ((gluingRowProfile j).xi 0 - (gluingRowProfile j).zeta 0) = _
  have hx : (gluingRowProfile j).xi 0 - (gluingRowProfile j).zeta 0 = (j : ℤ) := by
    simp [GluingCore.Profile.xi, gluingRowProfile]
  rw [hx, GluingCore.hh_pnat]

/-- The row statistics make the hatted and middle powers zero. -/
theorem gluing_horizontalRow_statistics (j : ℕ+) :
    (horizontalRow j).card = j ∧
      GluingCore.numRows (horizontalRow j) = 1 ∧
      GluingCore.numCols (horizontalRow j) = j ∧
      GluingCore.span (horizontalRow j) = j := by
  have hc : (horizontalRow j).card = (j : ℕ) := by
    unfold horizontalRow
    rw [Finset.card_image_of_injective _ (fun a b h => by simpa using h), Int.card_Ico]
    simp
  refine ⟨hc, ?_, ?_, span_horizontalRow j⟩
  · have hh := GluingCore.numRows_translate_cells (gluingRowProfile j) (0, 0)
    simpa only [show ((0, 0) : ℤ × ℤ) = 0 from rfl,
      GluingCore.translate_zero, gluingRowProfile_cells, Nat.zero_add] using hh
  · rw [GluingCore.numCols_eq_card_image_snd]
    simp [horizontalRow, Finset.image_image, Function.comp_def]

namespace MarkedInner
variable {ω : MarkedInner}

/-- The connected-row normalization is the prescribed generator image. -/
theorem IsLegal.componentT_horizontalRow (h : ω.IsLegal) (j : ℕ+) :
    GluingCore.Plan.componentT ω.toGluing (horizontalRow j) = ω.modifiedGenerator h j := by
  obtain ⟨hc, hr, hcol, hs⟩ := gluing_horizontalRow_statistics j
  unfold GluingCore.Plan.componentT modifiedGenerator rowSchur
  simp only [hc, hr, hcol, hs, Nat.sub_self, pow_zero, mul_one]
  rw [← h.normalA_eq_gluing, toGluing_compose,
    ← cellSchur_eq_gluing _ (h.isConnectedSkew_compose_horizontalRow_all j.pos).1]

/-- Geometric row values determine the algebra map uniquely. -/
theorem IsLegal.algHom_eq_modifiedCompositionMap (h : ω.IsLegal)
    (φ : Lambda →ₐ[ℚ] Lambda)
    (hrow : ∀ j : ℕ+, φ (GluingCore.cellSchur (horizontalRow j)) =
      GluingCore.Plan.componentT ω.toGluing (horizontalRow j)) :
    φ = ω.modifiedCompositionMap h := by
  apply MvPolynomial.algHom_ext
  intro j
  rw [modifiedCompositionMap, MvPolynomial.bind₁_X_right]
  exact (congrArg φ (gluing_cellSchur_horizontalRow j).symm).trans
    ((hrow j).trans (h.componentT_horizontalRow j))

end MarkedInner
end SkewGluing
