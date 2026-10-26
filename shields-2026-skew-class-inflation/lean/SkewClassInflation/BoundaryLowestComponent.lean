/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.BoundaryDeletionSign
import SkewClassInflation.BoundaryParentIdentification

/-!
# The exact lowest ordinary-degree component of the boundary parent

Formalizes `lem:boundary-core` and `eq:boundary-lowest-degree` in
`shields-2026-skew-class-inflation.tex`.  The actual parent is identified
with its sorted restoration, whose computed deletion sign is positive.
All lower components vanish, and the first surviving component is the
actual connected, zero-free Hessenberg core.  Sorry-free.
-/

namespace SkewClassInflation.ThinParameters

open SkewJacobiNegative

variable (B : ThinParameters)

/-- The actual first-boundary parent has the exact core function as its displayed component. -/
theorem boundary_lowest_component {M : ℕ} (α : Composition M) (hM : 0 < M) :
    MvPolynomial.homogeneousComponent (M + 1)
      (Profile.inflate B.boundary.p (B.diagram α hM).2).toBetaDiagram.schur =
        (compositionCore B.boundary hM α).schur := by
  rw [B.boundary_schur_eq_restored α hM,
    B.boundary.restoredParent_lowest_component M hM (suffixSet α) (suffixSet_subset α)]
  rfl

/-- Every actual lower ordinary component vanishes, not merely the selected parent coefficient. -/
theorem boundary_component_below {M : ℕ} (α : Composition M) (hM : 0 < M)
    (d : ℕ) (hd : d < M + 1) :
    MvPolynomial.homogeneousComponent d
      (Profile.inflate B.boundary.p (B.diagram α hM).2).toBetaDiagram.schur = 0 := by
  rw [B.boundary_schur_eq_restored α hM]
  exact B.boundary.restoredParent_component_below M hM (suffixSet α) (suffixSet_subset α) d hd

/-- The actual core order is precisely the least occupied ordinary degree of the full parent. -/
theorem boundary_least_ordinary_degree {M : ℕ} (α : Composition M) (hM : 0 < M) :
    IsLeast {d : ℕ | MvPolynomial.homogeneousComponent d
      (Profile.inflate B.boundary.p (B.diagram α hM).2).toBetaDiagram.schur ≠ 0} (M + 1) := by
  constructor
  · rw [Set.mem_ofPred_eq, B.boundary_lowest_component]
    exact (compositionCore B.boundary hM α).schur_ne_zero
  · intro d hd
    by_contra hn
    exact hd (B.boundary_component_below α hM d (by omega))

/-- The complete boundary-core conclusion, with all structural properties proved. -/
theorem boundary_core_lowest {M : ℕ} (α : Composition M) (hM : 0 < M) :
    let C := compositionCore B.boundary hM α
    MvPolynomial.homogeneousComponent (M + 1)
        (Profile.inflate B.boundary.p (B.diagram α hM).2).toBetaDiagram.schur = C.schur ∧
      IsLeast {d : ℕ | MvPolynomial.homogeneousComponent d
        (Profile.inflate B.boundary.p (B.diagram α hM).2).toBetaDiagram.schur ≠ 0} (M + 1) ∧
      C.Connected ∧ C.ZeroFree ∧ IsHessenberg C := by
  refine ⟨B.boundary_lowest_component α hM, B.boundary_least_ordinary_degree α hM,
    B.boundary.core_connected M hM (suffixSet α),
    B.boundary.core_zeroFree M hM (suffixSet α), ?_⟩
  exact B.boundary.core_hessenberg M hM (suffixSet α)

/-- The retained upper beta list is the literal ordered formula, not only a permutation class. -/
theorem boundary_core_rows {M : ℕ} (α : Composition M) (hM : 0 < M) :
    (compositionCore B.boundary hM α).row = B.boundary.upper M (suffixSet α) := rfl

/-- The retained lower beta list has the same fixed literal order for every outer composition. -/
theorem boundary_core_cols {M : ℕ} (α : Composition M) (hM : 0 < M) :
    (compositionCore B.boundary hM α).col = B.boundary.lower M := rfl

end SkewClassInflation.ThinParameters
