/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.ResidueHigherPolynomial
import SkewCornerDescent.Matrix.ResiduePlanePullback
import SkewCornerDescent.TriangularPlanePolynomial

/-!
# Protected tops and rational labels in the actual residue polynomial algebra

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:residue-classifier`). A response divisor of a genuine cleared
rational plane numerator has the closure top and a rational label. All higher variables
are the surviving original generators, evaluated injectively in the actual residue field.

Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open MvPolynomial

noncomputable local instance classificationRatAlgebra (N : ℕ+) :
    Algebra ℚ (OtherField N) := OreLocalization.instAlgebra

/-- Strictly lower higher-coordinate polynomials evaluate into the complete lower field. -/
theorem residueHigherEval_mem_lower {N K : ℕ+} (hNK : N ≤ K)
    {p : ResidueHigherPolynomial N} (hp : ∀ j ∈ p.vars, j.val < K) :
    residueHigherEval N p ∈ residueLowerField N K := by
  have hs : p ∈ supported (residueLowerField N N) {j | j.val < K} :=
    mem_supported.mpr hp
  clear hp
  induction hs using Algebra.adjoin_induction with
  | mem p hp =>
    obtain ⟨j, hj, rfl⟩ := hp
    simp only [residueHigherEval, aeval_X]
    exact IntermediateField.subset_adjoin ℚ _ ⟨⟨j.val, ne_of_gt j.prop⟩, hj, rfl⟩
  | algebraMap c =>
    change residueHigherEval N (C c) ∈ residueLowerField N K
    simp only [residueHigherEval, aeval_C, Subfield.algebraMap_ofSubfield]
    exact SelectedCoordinate.residueLowerField_mono hNK c.prop
  | add p q _ _ hp hq =>
    rw [map_add]
    exact (residueLowerField N K).add_mem hp hq
  | mul p q _ _ hp hq =>
    rw [map_mul]
    exact (residueLowerField N K).mul_mem hp hq

/-- Polynomial divisibility, not field divisibility, forces the actual protected top and
rational label. The lower-field membership and response-root equation are produced here. -/
theorem actualResidue_plane_divisor_classification (N : ℕ+)
    {K J : ResidueHigherIndex N} {p : Polynomial ℚ} (hp : p.Monic)
    (hirr : Irreducible p) {A F B : ResidueHigherPolynomial N}
    (hA : ∀ j ∈ A.vars, j < K) (hF : ∀ j ∈ F.vars, j < K)
    (hB : ∀ j ∈ B.vars, j < J) (hF0 : residueHigherEval N F ≠ 0)
    (hd : X J + B ∣ triangularPlanePolynomial K
      (p.map (algebraMap ℚ (residueLowerField N N))) A F) :
    J = K ∧ p.natDegree = 1 ∧ ∃ c : ℚ, p.IsRoot c ∧
      residueHigherEval N B = residueHigherEval N A -
        (c : OtherField N) * residueHigherEval N F := by
  have htop := triangularPlanePolynomial_divisor_top (hp.map _) hA hF hB hd
  subst J
  have hroot := triangularPlanePolynomial_divisor_root (residueHigherEval N)
    (hp.map _) hA hF hB hd
  rw [clearedPlanePolynomial_eval _ _ _ _ hF0, neg_add_eq_sub] at hroot
  have hzroot := (mul_eq_zero.mp hroot).resolve_left (pow_ne_zero _ hF0)
  have heval : Polynomial.aeval
      ((residueHigherEval N A - residueHigherEval N B) / residueHigherEval N F)
      (p.map (algebraMap ℚ (residueLowerField N N))) =
      Polynomial.aeval
      ((residueHigherEval N A - residueHigherEval N B) / residueHigherEval N F) p := by
    simp only [Polynomial.aeval_def, Polynomial.eval₂_map,
      ← IsScalarTower.algebraMap_eq ℚ (residueLowerField N N) (OtherField N)]
  rw [heval] at hzroot
  have hlowA := residueHigherEval_mem_lower K.prop.le (fun j hj => hA j hj)
  have hlowB := residueHigherEval_mem_lower K.prop.le (fun j hj => hB j hj)
  have hlowF := residueHigherEval_mem_lower K.prop.le (fun j hj => hF j hj)
  have hz := (residueLowerField N K.val).div_mem
    ((residueLowerField N K.val).sub_mem hlowA hlowB) hlowF
  obtain ⟨hdeg, c, hc, hpc⟩ := residueLowerField_irreducible_root N K.val hz hirr hzroot
  refine ⟨rfl, hdeg, c, hpc, ?_⟩
  have hcF := (eq_div_iff hF0).mp hc
  rw [hcF]
  ring

end SkewCornerDescent.Matrix
