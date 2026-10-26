/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/


import SkewCornerDescent.Matrix.OriginalPureInventoryUnits
import SkewCornerDescent.Matrix.EndpointPrefixRecurrence
import SkewCornerDescent.Matrix.OriginalIntervalProfileBands
import SkewCornerDescent.Matrix.OriginalInternalSelfJet
import SkewCornerDescent.Matrix.OriginalInternalLiteralCopy

/-!
# Genuine visible unit vertices from a pure original incoming coefficient

Supports `shields-2026-skew-corner-descent.tex` (`thm:pure-primitive-first`).
A nonzero incoming coefficient supplies its actual source row. Strict
higher-than-core and half-height bounds exclude both selected endpoint
strips. Pure original corner factorization then identifies the entire
remaining block as a genuine gap-zero unit pivot. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- A visible nonzero higher incoming coefficient in a pure inventory
produces its actual gap-zero unit vertex at the original integer distance. -/
theorem originalPure_visible_nonzero_coefficient_unit {n : ℕ} (P : Profile n) (k : ℕ)
    (hK : (jtMatrix (fun j : Fin n => P.xi j.succ) (fun j => P.zeta j.castSucc)).det =
      cellSchur D hD.1 ^ k) (i : Fin (originalSelectedCount (hD := hD) P - 1))
    (w : ℕ) (hN : (c.top : ℕ) < w)
    (hw : 2 * (w : ℤ) < originalHessenbergDistance (hD := hD) P
      (originalInternalStateIndex P i) (originalInternalStateIndex P i))
    (hcoeff : ((c.originalInternalEndpointProfiles P i).1).coeff w ≠ 0) :
    let a := originalSelectedEnumeration (hD := hD) P ⟨i.val, by have := i.isLt; omega⟩
    let x := P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a)))
    ∃ p : OriginalInternalInterval P i,
      P.xi p.val.val.1.val.succ = P.zeta p.val.val.1.val.castSucc ∧
      x - originalResponseRows P p.val.val = (w : ℤ) := by
  classical
  let ai : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val, by have := i.isLt; omega⟩
  let bi : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val+1, by have := i.isLt; omega⟩
  let E := originalSelectedEnumeration (hD := hD) P
  let ν := OriginalInternalInterval (hD := hD) P i
  let row := fun p : ν => originalResponseRows P p.val.val
  let col := fun p : ν => originalResponseCols P p.val.val
  let x := P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some (E ai))))
  let A := (c.originalInternalEndpointProfiles P i).1
  let M := vertexBetaMatrix c.residueMap row col
  let incoming := fun p => (vertexOutgoing c.residueMap col x * M⁻¹) () p
  let : Invertible M := c.originalResponseResidueIntervalInverse P (some (E ai)) (some (E bi))
  have hprofile : A = ordinaryEndpointProfile (fun p : ν => (x-row p).toNat) incoming := by
    change c.originalResidueLeftEndpointPolynomial P (some (E ai)) (some (E bi)) = _
    dsimp only [originalResidueLeftEndpointPolynomial, residueIntervalLeftPolynomial]
    simp only [Matrix.invOf_eq_nonsing_inv]
    rfl
  have hwpos : 0 < w := lt_trans c.top.pos hN
  obtain ⟨p,hp⟩ := ordinary_profile_nonzero_coefficient_support
    (fun p : ν => (x-row p).toNat) incoming w hwpos (by rw [← hprofile]; exact hcoeff)
  have hpos : 0 < x-row p := by
    have h := originalResponse_row_lt P (some (E ai)) p.val.val p.property
    change row p < x at h
    omega
  have hpZ : x-row p = (w : ℤ) := by
    have he := congrArg (fun t : ℕ => (t : ℤ)) hp
    rw [Int.toNat_of_nonneg hpos.le] at he
    exact he
  have hheight : P.xi (originalRowSplitEquiv P (.inl (some (E ai)))) -
      P.zeta (originalColSplitEquiv P (.inl (some (E bi)))) =
      originalHessenbergDistance (hD := hD) P
        (originalInternalStateIndex P i) (originalInternalStateIndex P i) := by
    change _ = P.xi (originalRowSplitEquiv P (.inl (originalHessenbergRows P ai.succ))) -
      P.zeta (originalColSplitEquiv P (.inl (originalHessenbergCols P bi.castSucc)))
    rw [originalHessenbergRows_succ, originalHessenbergCols_castSucc]
  have hNInt : (c.top : ℤ) < w := by exact_mod_cast hN
  have hH : 2 * (c.top : ℤ) < P.xi (originalRowSplitEquiv P (.inl (some (E ai)))) -
      P.zeta (originalColSplitEquiv P (.inl (some (E bi)))) := by rw [hheight]; omega
  have hvisible : 2 * (x-row p) < P.xi (originalRowSplitEquiv P (.inl (some (E ai)))) -
      P.zeta (originalColSplitEquiv P (.inl (some (E bi)))) := by rw [hpZ, hheight]; exact hw
  rcases c.original_consecutive_visible_row_cases P ai bi rfl p hH hvisible with hs | hs
  · have hb := (c.original_selected_row_distance_band P (E ai) p.val.val hs).2
    change x-row p < (c.top : ℤ) at hb
    omega
  · exact ⟨p, originalPure_nonselected_empty P k hK p.val.val.1 hs, hpZ⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
