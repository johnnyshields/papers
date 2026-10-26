/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalNormalDerivative
import SkewCornerDescent.Matrix.LowerResponses
import SkewCornerDescent.Matrix.UnitVertexGeometry

/-!
# Complete protected coefficients at genuine unit boundaries

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`).
A terminal unit row exposes the protected incoming generator with a strict
lower-field remainder. Exact transpose duality supplies the outgoing form.
All original inverse entries are retained and their support is proved together.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
open scoped BigOperators
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- A genuine terminal unit row has a monic protected incoming coefficient.
All inverse entries are controlled in the strict lower field simultaneously. -/
theorem protected_unit_incoming {ν : Type*} [Fintype ν] [DecidableEq ν]
    (row col : ν → ℤ) (x m : ℤ) (k : ν)
    [Invertible (vertexBetaMatrix c.residueMap row col)]
    (hrowk : row k = m) (hcolk : col k = m) (hcolinj : Function.Injective col)
    (hrow : ∀ i, row i < x) (hcol : ∀ i, m ≤ col i)
    (J : ℕ+) (hJ : c.top < J) (hJe : (J : ℤ) = x - m) :
    ∃ R ∈ residueLowerField c.top J,
      (vertexOutgoing c.residueMap col x * (vertexBetaMatrix c.residueMap row col)⁻¹) () k =
        residueGenerator c.top ⟨J, ne_of_gt hJ⟩ + R := by
  classical
  let S := residueLowerField c.top J
  let M := vertexBetaMatrix c.residueMap row col
  have hcol_strict (i : ν) (hi : i ≠ k) : m < col i := by
    have hle := hcol i
    have hne : col i ≠ m := fun he => hi (hcolinj (he.trans hcolk.symm))
    omega
  have hM (i j : ν) : M i j ∈ S := by
    change c.residueMap (hh (row i - col j)) ∈ S
    apply c.residue_hh_mem_lower J hJ
    have hi := hrow i
    have hj := hcol j
    omega
  have hI (i j : ν) : M⁻¹ i j ∈ S := by
    simpa only [Matrix.invOf_eq_nonsing_inv] using inverse_entries_mem_subfield S M hM i j
  have hunitrow (i : ν) : M k i = if i = k then 1 else 0 := by
    by_cases hi : i = k
    · subst i
      change c.residueMap (hh (row k - col k)) = _
      rw [hrowk, hcolk, sub_self, hh_zero, map_one, ite_eq_left rfl]
    · rw [ite_eq_right hi]
      change c.residueMap (hh (row k - col i)) = 0
      rw [hrowk, hh_of_neg (by have := hcol_strict i hi; omega), map_zero]
  have hIkk : M⁻¹ k k = 1 := by
    have he := congrFun (congrFun (Matrix.mul_inv_of_invertible M) k) k
    have hsum : (∑ i : ν, if i = k then M⁻¹ i k else 0) = M⁻¹ k k := by
      rw [Finset.sum_eq_single k]
      · exact ite_eq_left rfl
      · intro j _ hj
        exact ite_eq_right hj
      · intro hn
        exact False.elim (hn (Finset.mem_univ k))
    simp only [Matrix.mul_apply, hunitrow, ite_mul, one_mul, zero_mul,
      Matrix.one_apply_eq] at he
    rwa [hsum] at he
  let XJ := residueGenerator c.top ⟨J, ne_of_gt hJ⟩
  let R := ∑ i : ν, (c.residueMap (hh (x - col i)) * M⁻¹ i k - if i = k then XJ else 0)
  have hR : R ∈ S := by
    apply S.sum_mem
    intro i _
    by_cases hi : i = k
    · subst i
      rw [hcolk, ← hJe, hh_pnat, c.residueMap_other J (ne_of_gt hJ), hIkk,
        mul_one, ite_eq_left rfl]
      change XJ - XJ ∈ S
      rw [sub_self]
      exact S.zero_mem
    · rw [ite_eq_right hi, sub_zero]
      apply S.mul_mem
      · apply c.residue_hh_mem_lower J hJ
        have h := hcol_strict i hi
        omega
      · exact hI i k
  refine ⟨R, hR, ?_⟩
  rw [Matrix.mul_apply]
  change (∑ i : ν, c.residueMap (hh (x - col i)) * M⁻¹ i k) = XJ + R
  have hindicator : (∑ i : ν, if i = k then XJ else 0) = XJ :=
    Fintype.sum_ite_eq' k (fun _ => XJ)
  dsimp only [R]
  rw [Finset.sum_sub_distrib, hindicator]
  ring

/-- The outgoing protected coordinate is the exact transpose dual. The
full original inverse and every lower correction remain in the formula. -/
theorem protected_unit_outgoing {ν : Type*} [Fintype ν] [DecidableEq ν]
    (row col : ν → ℤ) (m y : ℤ) (k : ν)
    [Invertible (vertexBetaMatrix c.residueMap row col)]
    (hrowk : row k = m) (hcolk : col k = m) (hrowinj : Function.Injective row)
    (hrow : ∀ i, row i ≤ m) (hcol : ∀ i, y < col i)
    (J : ℕ+) (hJ : c.top < J) (hJe : (J : ℤ) = m - y) :
    ∃ R ∈ residueLowerField c.top J,
      ((vertexBetaMatrix c.residueMap row col)⁻¹ * vertexIncoming c.residueMap row y) k () =
        residueGenerator c.top ⟨J, ne_of_gt hJ⟩ + R := by
  let row' := fun i => -col i
  let col' := fun i => -row i
  have hmat : vertexBetaMatrix c.residueMap row' col' =
      (vertexBetaMatrix c.residueMap row col).transpose := by
    ext i j
    change c.residueMap (hh (-col i - -row j)) = c.residueMap (hh (row j - col i))
    apply congrArg c.residueMap
    apply congrArg hh
    omega
  let : Invertible (vertexBetaMatrix c.residueMap row' col') := by
    rw [hmat]
    infer_instance
  obtain ⟨R, hR, hvalue⟩ := c.protected_unit_incoming row' col' (-y) (-m) k
    (by dsimp only [row']; rw [hcolk]) (by dsimp only [col']; rw [hrowk])
    (by intro i j h; exact hrowinj (neg_inj.mp h))
    (by intro i; have h := hcol i; dsimp only [row']; omega)
    (by intro i; have h := hrow i; dsimp only [col']; omega)
    J hJ (by omega)
  have hvec : vertexOutgoing c.residueMap col' (-y) =
      (vertexIncoming c.residueMap row y).transpose := by
    ext i j
    change c.residueMap (hh (-y - -row j)) = c.residueMap (hh (row j - y))
    apply congrArg c.residueMap
    apply congrArg hh
    omega
  rw [hmat, ← Matrix.transpose_nonsing_inv, hvec, ← Matrix.transpose_mul] at hvalue
  exact ⟨R, hR, hvalue⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
