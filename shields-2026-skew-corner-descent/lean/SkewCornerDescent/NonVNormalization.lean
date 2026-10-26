/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.NonVLegality
import SkewGluing.RowNormalization

/-!
# Normalization of the ordinary non-V family

Formalizes `shields-2026-skew-corner-descent.tex`, «Cofactor transport under composition»
(`sec:transport`, `eq:non-v-factors`, `eq:row-cofactor`).

The mark, hatted window, and middle are the literal diagrams of the infinite family.
Their functions determine all four normalization factors and every row cofactor.

Sorry-free.
-/

namespace SkewCornerDescent
open SkewGluing SkewGluing.MarkedInner SkewGluing.Profile

/-- The two-cell column underlying the actual lower mark. -/
def nonVColumnProfile : Profile 1 where
  r := ![1, 1]
  g := ![0]
  r_pos := by decide
  g_lt_castSucc := by decide
  g_lt_succ := by decide

/-- The two-cell row underlying the actual hatted mark. -/
def nonVRowProfile : Profile 0 where
  r := ![2]
  g := Fin.elim0
  r_pos := by decide
  g_lt_castSucc := by decide
  g_lt_succ := by decide

/-- The column's complete-generator determinant. -/
theorem nonVColumnProfile_schur : nonVColumnProfile.schur = hh 1 ^ 2 - hh 2 := by
  have hx : nonVColumnProfile.xi = ![2, 1] := by decide
  have hz : nonVColumnProfile.zeta = ![1, 0] := by decide
  rw [Profile.schur, Matrix.det_fin_two]
  simp [hx, hz]
  ring

/-- The row's complete-generator determinant. -/
theorem nonVRowProfile_schur : nonVRowProfile.schur = hh 2 := by
  have hx : nonVRowProfile.xi 0 = 2 := by decide
  have hz : nonVRowProfile.zeta 0 = 0 := by decide
  rw [Profile.schur, Matrix.det_succ_row_zero]
  simp [hx, hz]

/-- The lower finite cap is the southwest interior cell. -/
theorem nonVMark_lowerCap (k : ℕ) (hk : 3 ≤ k) :
    (nonVMark k).lowerCap = {(-1, 0)} := by
  unfold MarkedInner.lowerCap
  change (diagramInterior (nonVDiagram k)).filter
    (fun x => content x < minContent (nonVDiagram k) + (nonVMark k).width) = _
  rw [nonVDiagram_interior k hk, nonVDiagram_minContent k hk, nonVMark_width]
  have hkZ : (3 : ℤ) ≤ k := by exact_mod_cast hk
  ext ⟨a, b⟩
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq,
    content, zero_add, Nat.cast_ofNat]
  omega

/-- The upper finite cap is the northeast interior cell. -/
theorem nonVMark_upperCap (k : ℕ) (hk : 3 ≤ k) :
    (nonVMark k).upperCap = {(-2, (k : ℤ) - 2)} := by
  unfold MarkedInner.upperCap
  change (diagramInterior (nonVDiagram k)).filter
    (fun x => minContent (nonVDiagram k) + (nonVMark k).period - 1 < content x) = _
  rw [nonVDiagram_interior k hk, nonVDiagram_minContent k hk, nonVMark_period]
  have hkZ : (3 : ℤ) ≤ k := by exact_mod_cast hk
  ext ⟨a, b⟩
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq,
    content, zero_add]
  omega

/-- The actual hatted window is the two-cell row stated in the manuscript. -/
theorem nonVMark_hatMarkWindow (k : ℕ) (hk : 3 ≤ k) :
    (nonVMark k).hatMarkWindow = {(-1, 0), (-1, -1)} := by
  rw [(nonVMark_isLegal k hk).hatMarkWindow_eq_caps
    (nonVMark_isNonemptyMark k hk).1, nonVMark_lowerCap k hk, nonVMark_upperCap k hk]
  simp [nonVMark, SkewGluing.translate, Prod.mk_add_mk]

/-- The middle's actual southeast interior is empty. -/
theorem nonVMark_middle_interior (k : ℕ) (hk : 3 ≤ k) :
    diagramInterior (nonVMark k).middle = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  rw [diagramInterior, Finset.mem_filter] at hx
  exact nonVMark_middle_noInterior k hk hx.1 hx.2

/-- The original lower mark has the two-cell column function, with no assumed factor. -/
theorem nonVMark_normalA (k : ℕ) (hk : 3 ≤ k) :
    (nonVMark k).normalA (nonVMark_isLegal k hk) = hh 1 ^ 2 - hh 2 := by
  rw [normalA, dite_eq_left (nonVMark_isNonemptyMark k hk).1]
  unfold markA
  have he : (nonVMark k).W = SkewGluing.translate (-1, -1) nonVColumnProfile.cells := by
    change {(-1, 0), (0, 0)} = SkewGluing.translate (-1, -1) nonVColumnProfile.cells
    decide
  rw [cellSchur_eq_profile (nonVMark_isNonemptyMark k hk).2.1
    nonVColumnProfile (-1, -1) he, nonVColumnProfile_schur]

/-- The actual periodic hatted mark has the two-cell row function. -/
theorem nonVMark_normalB (k : ℕ) (hk : 3 ≤ k) :
    (nonVMark k).normalB (nonVMark_isLegal k hk) = hh 2 := by
  rw [normalB, dite_eq_left (nonVMark_isNonemptyMark k hk).1]
  unfold hatMarkB
  have he : (nonVMark k).hatMarkWindow = translate (-1, -1) nonVRowProfile.cells := by
    rw [nonVMark_hatMarkWindow k hk]
    decide
  rw [cellSchur_congr he _ (isSkew_translate _ nonVRowProfile.isSkew_cells),
    cellSchur_translate _ nonVRowProfile.isSkew_cells, cellSchur_cells, nonVRowProfile_schur]

/-- The actual ribbon middle has unit cofactor. -/
theorem nonVMark_normalC (k : ℕ) (hk : 3 ≤ k) :
    (nonVMark k).normalC (nonVMark_isLegal k hk) = 1 := by
  rw [normalC, dite_eq_left (nonVMark_isNonemptyMark k hk).1]
  unfold middleCofactor
  exact (cellSchur_congr (nonVMark_middle_interior k hk) _ (by decide)).trans
    (cellSchur_empty _)

/-- The two literal caps produce the square of the first complete generator. -/
theorem nonVMark_normalTheta (k : ℕ) (hk : 3 ≤ k) :
    (nonVMark k).normalTheta (nonVMark_isLegal k hk) = hh 1 ^ 2 := by
  have h := (nonVMark_isLegal k hk).interiorSchur_single_normalization
  rw [nonVMark_normalC k hk, mul_one] at h
  exact h.symm.trans (nonVDiagram_interiorSchur k hk)

/-- Every actual composed row has the full non-V cofactor formula. -/
theorem nonVMark_row_cofactor (k : ℕ) (hk : 3 ≤ k) {m : ℕ} (hm : 1 ≤ m) :
    cellSchur (diagramInterior ((nonVMark k).compose (horizontalRow m)))
      ((nonVMark_isLegal k hk).isConnectedSkew_compose_horizontalRow_all hm).1.interior =
        hh 1 ^ 2 * hh 2 ^ (m - 1) := by
  rw [(nonVMark_isLegal k hk).interiorSchur_compose_row_normalization hm,
    nonVMark_normalTheta k hk, nonVMark_normalC k hk, nonVMark_normalB k hk]
  simp

end SkewCornerDescent
