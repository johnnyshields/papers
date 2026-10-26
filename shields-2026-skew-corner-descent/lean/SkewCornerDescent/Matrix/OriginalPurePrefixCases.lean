/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/


import SkewCornerDescent.Matrix.OriginalPureVisibleUnits

/-!
# Actual visible pure incoming coefficients have two produced values

Supports `shields-2026-skew-corner-descent.tex` (`thm:pure-primitive-first`).
A nonzero higher visible coefficient supplies a genuine gap-zero unit
vertex. Its original row and column beta coordinates agree, so the full
inverse column equation recovers that coefficient from the strictly
earlier incoming prefix. The alternative value is zero. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- A visible higher pure coefficient is zero or its exact complete-prefix
recurrence value, with the actual unit vertex produced internally. -/
theorem originalPure_visible_left_coefficient_cases {n : ℕ} (P : Profile n) (k : ℕ)
    (hK : (jtMatrix (fun j : Fin n => P.xi j.succ) (fun j => P.zeta j.castSucc)).det =
      cellSchur D hD.1 ^ k) (i : Fin (originalSelectedCount (hD := hD) P - 1))
    (w : ℕ) (hN : (c.top : ℕ) < w)
    (hw : 2 * (w : ℤ) < originalHessenbergDistance (hD := hD) P
      (originalInternalStateIndex P i) (originalInternalStateIndex P i)) :
    ((c.originalInternalEndpointProfiles P i).1).coeff w = 0 ∨
      ((c.originalInternalEndpointProfiles P i).1).coeff w =
        completePrefixRecurrenceValue c.residueMap
          (c.originalInternalEndpointProfiles P i).1 w := by
  classical
  let A := (c.originalInternalEndpointProfiles P i).1
  change A.coeff w = 0 ∨ A.coeff w = completePrefixRecurrenceValue c.residueMap A w
  by_cases hzero : A.coeff w = 0
  · exact Or.inl hzero
  apply Or.inr
  obtain ⟨p, hempty, hp⟩ := c.originalPure_visible_nonzero_coefficient_unit P k hK i w hN hw hzero
  let ai : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val, by have := i.isLt; omega⟩
  let bi : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val+1, by have := i.isLt; omega⟩
  let E := originalSelectedEnumeration (hD := hD) P
  let ν := OriginalInternalInterval (hD := hD) P i
  let row := fun p : ν => originalResponseRows P p.val.val
  let col := fun p : ν => originalResponseCols P p.val.val
  let x := P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some (E ai))))
  let : Invertible (vertexBetaMatrix c.residueMap row col) :=
    c.originalResponseResidueIntervalInverse P (some (E ai)) (some (E bi))
  have hprofile : A = betaEndpointLeftPolynomial c.residueMap row col x := by
    change c.originalResidueLeftEndpointPolynomial P (some (E ai)) (some (E bi)) = _
    dsimp only [originalResidueLeftEndpointPolynomial, residueIntervalLeftPolynomial,
      betaEndpointLeftPolynomial]
    simp only [Matrix.invOf_eq_nonsing_inv]
    rfl
  have hends := originalEmptyBlock_remaining_endpoints P p.val.val.1 hempty p.val.val.2
  have hr : row p = P.xi p.val.val.1.val.succ := hends.1
  have hc : col p = P.zeta p.val.val.1.val.castSucc := hends.2
  have heq : row p = col p := hr.trans (hempty.trans hc.symm)
  change x-row p = (w : ℤ) at hp
  have hwcol : (w : ℤ) = x-col p := by rw [← heq]; exact hp.symm
  have hrow (j : ν) : row j ≤ x := by
    have hh := originalResponse_row_lt P (some (E ai)) j.val.val j.property
    exact hh.le
  have hg := betaEndpointLeftPolynomial_column_coefficient c.residueMap row col x hrow p w hwcol
  simpa only [← hprofile] using hg

end SkewCornerDescent.Matrix.SelectedCoordinate
