/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
-- TODO-COPIED: skew-gluing/lean/SkewGluing/OlsonHarris/Plan/MurnaghanNakayama/Beta.lean
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.MurnaghanNakayama.Determinant
import SkewMarkedFactor.Gluing.CellSchurTableau
import SkewMarkedFactor.Gluing.DualEvaluation

/-!
# Jacobi–Trudi for skew Young diagrams, and β-numbers

Formalizes `shields-2026-skew-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `def:gluing-graph`): the dictionary between skew Young diagrams `λ / μ` and the
determinants `jtDet` used by the derivation form of the Murnaghan–Nakayama rule.

Sorry-free.
-/

namespace SkewMarkedFactor.Gluing

namespace Plan

namespace MN

open MvPolynomial

/-- **Jacobi–Trudi in `Λ` for every skew Young diagram**, connected or not: `s_{λ/μ}` is the
determinant of the entries `h_{λ_i - i - μ_j + j}`. -/
theorem cellSchur_skewDiagram_eq_jtDet {lam mu : YoungDiagram} (hmu : mu ≤ lam) {M : ℕ}
    (hrow : ∀ i, M ≤ i → lam.rowLen i = 0) :
    cellSchur (skewDiagram lam mu) =
      jtDet (fun i : Fin M => (lam.rowLen i : ℤ) - i)
        (fun j : Fin M => (mu.rowLen j : ℤ) - j) := by
  apply eq_of_evalComplete_eq
  intro a
  rw [evalComplete, aeval_cellSchur_skewDiagram_all hmu a (varAlphabet a)]
  rw [← Shields.jacobiTrudiDet_eq_skewSchur (b := a) (m := M) (varAlphabet a) lam mu hmu hrow]
  rw [jtDet, AlgHom.map_det, Shields.jacobiTrudiDet]
  congr 1
  refine Matrix.ext fun u v => ?_
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
  have h2 := evalComplete_hh a (varAlphabet a) ((lam.rowLen u : ℤ) - u - ((mu.rowLen v : ℤ) - v))
  unfold evalComplete at h2
  rw [h2]
  simp only [Shields.jtCoeff]
  split_ifs <;> first | omega | rfl | (congr 2; omega)

end MN

end Plan

end SkewMarkedFactor.Gluing
