/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.ComponentPivot
import SkewCornerDescent.Matrix.LowerResponses

/-!
# Actual complementary intervals

Supports `shields-2026-skew-corner-descent.tex`, «Equal windows and the determinant defect»
(`sec:normal-chart`, `lem:actual-elimination`) and «From response functions to literal copies»
(`sec:one-active`, `lem:profile-derivative`). The complete complementary interval is
invertible from the connected profile's proved minor nonvanishing. Its endpoint
inequalities, ordinary profile realization and triangular correction are produced.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- The actual interval matrix agrees with the complete deleted complementary minor. -/
theorem componentInterval_eq_minor {n : ℕ} (P : Profile n) :
    intervalMatrix (fun i : Fin n => P.xi i.succ) (fun j => P.zeta j.castSucc) =
      deletedTopRightOriginalMatrix P := rfl

/-- The actual interval inverse is supplied, not an extra theorem hypothesis. -/
@[instance_reducible]
noncomputable def componentIntervalInverse {n : ℕ} (P : Profile n) :
    Invertible (intervalMatrix (fun i : Fin n => P.xi i.succ) (fun j => P.zeta j.castSucc)) :=
  Matrix.invertibleOfIsUnitDet _ (by
    rw [componentInterval_eq_minor, det_deletedTopRightOriginalMatrix]
    apply isUnit_iff_ne_zero.mpr
    simpa using P.minor_ne_zero)

/-- The complete complementary row and column endpoints lie strictly inside the retained ends. -/
theorem componentInterval_endpoint_bounds {n : ℕ} (P : Profile n) :
    (∀ i : Fin n, P.xi i.succ < P.xi 0) ∧
      (∀ i : Fin n, P.zeta (Fin.last n) < P.zeta i.castSucc) := by
  constructor
  · intro i; exact P.xi_strictAnti (by simp)
  · intro i; exact P.zeta_strictAnti (Fin.castSucc_lt_last i)

/-- Actual complete component responses are triangular at the geometric top, with
ordinary endpoint profiles and no omitted inverse entries. -/
theorem componentInterval_triangular {n : ℕ} (P : Profile n) :
    letI := componentIntervalInverse P
    ∃ A ∈ lowerGeneratorField P.topVar,
      intervalResponse (P.xi 0) (P.zeta (Fin.last n))
        (fun i : Fin n => P.xi i.succ) (fun j => P.zeta j.castSucc) =
          originalMap (MvPolynomial.X P.topVar) + A ∧
      generatorDeriv P.topVar
        (intervalResponse (P.xi 0) (P.zeta (Fin.last n))
          (fun i : Fin n => P.xi i.succ) (fun j => P.zeta j.castSucc)) = 1 := by
  let := componentIntervalInverse P
  obtain ⟨hr, hc⟩ := componentInterval_endpoint_bounds P
  apply intervalResponse_triangular _ _ _ _ _ _ hr hc
  rw [P.zeta_last, sub_zero]
  exact P.topVar_coe.symm

/-- The actual component scalar and complete interval response are the same object. -/
theorem componentResponse_eq_intervalResponse {n : ℕ} (P : Profile n) :
    letI := componentIntervalInverse P
    componentResponse P = intervalResponse (P.xi 0) (P.zeta (Fin.last n))
      (fun i : Fin n => P.xi i.succ) (fun j => P.zeta j.castSucc) := by
  let := componentIntervalInverse P
  simp only [componentResponse, intervalResponse, retainedResponse,
    Matrix.invOf_eq_nonsing_inv]
  have h11 : (componentSplit P).toBlocks₁₁ =
      (fun _ _ : Unit => originalMap (hh (P.xi 0 - P.zeta (Fin.last n)))) := by
    ext i j
    cases i; cases j
    rfl
  have h12 : (componentSplit P).toBlocks₁₂ =
      intervalIncoming (P.xi 0) (fun j : Fin n => P.zeta j.castSucc) := by
    ext i j
    cases i
    simp [componentSplit, splitOriginalMatrix, originalMatrix, Matrix.toBlocks₁₂,
      Matrix.submatrix, intervalIncoming, Fin.succAbove_last]
  have h21 : (componentSplit P).toBlocks₂₁ =
      intervalOutgoing (P.zeta (Fin.last n)) (fun i : Fin n => P.xi i.succ) := by
    ext i j
    cases j
    simp [componentSplit, splitOriginalMatrix, originalMatrix, Matrix.toBlocks₂₁,
      Matrix.submatrix, intervalOutgoing]
  rw [h11, h12, h21, componentSplit_removed, ← componentInterval_eq_minor]

/-- The actual removed complementary lists give ordinary, not merely Laurent, profiles. -/
theorem componentInterval_profiles_ordinary {n : ℕ} (P : Profile n) :
    letI := componentIntervalInverse P
    ∃ A B : Polynomial actualField,
      leftEndpointProfile (P.xi 0) (fun i : Fin n => P.xi i.succ)
        (fun j => P.zeta j.castSucc) = A.toLaurent ∧
      rightEndpointProfile (P.zeta (Fin.last n)) (fun i : Fin n => P.xi i.succ)
        (fun j => P.zeta j.castSucc) = B.toLaurent := by
  let := componentIntervalInverse P
  obtain ⟨hr, hc⟩ := componentInterval_endpoint_bounds P
  obtain ⟨hA, hB⟩ := interval_profiles_ordinary (P.xi 0) (P.zeta (Fin.last n))
    (fun i : Fin n => P.xi i.succ) (fun j => P.zeta j.castSucc) hr hc
  exact ⟨_, _, hA, hB⟩

end SkewCornerDescent.Matrix
