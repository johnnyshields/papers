/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalResidueEndpointProfiles
import SkewCornerDescent.Matrix.ResidueLowerBounds
import SkewCornerDescent.Matrix.LowerResponses
import SkewCornerDescent.Matrix.OriginalNormalDerivative

/-!
# Support of complete original response profiles

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The full actual interval inverse, local response, and both endpoint profiles
stay in the lower generator field when their actual span is smaller than the
protected generator. No inverse entries are frozen. Sorry-free.
-/

namespace SkewCornerDescent.Matrix
open SkewGluing
open scoped BigOperators

private theorem ordinary_profile_coeff_mem_subfield {F ν : Type*} [Field F] [Fintype ν]
    (S : Subfield F) (distance : ν → ℕ) (v : ν → F) (hv : ∀ i, v i ∈ S) (k : ℕ) :
    (ordinaryEndpointProfile distance v).coeff k ∈ S := by
  classical
  rw [ordinaryEndpointProfile, Polynomial.coeff_sub, Polynomial.finsetSum_coeff]
  apply S.sub_mem
  · simp only [Polynomial.coeff_one]
    split_ifs
    · exact S.one_mem
    · exact S.zero_mem
  · apply S.sum_mem
    intro i _
    rw [Polynomial.coeff_monomial]
    split_ifs
    · exact hv i
    · exact S.zero_mem

namespace SelectedCoordinate
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The entire actual local response and every complete endpoint-profile
coefficient stay below a later generator. Full original inverse entries are
controlled together; no internal inverse entry is assumed nonzero. -/
theorem originalLocalResponse_profiles_mem_lower {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) (H : ℕ+) (hNH : c.top < H)
    (hspan : P.xi (originalRowSplitEquiv (hD := hD) P (.inl b)) -
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl d)) < (H : ℤ)) :
    c.regularResidue (c.originalLocalResponse P b d) ∈ residueLowerField c.top H ∧
      ∀ k, (c.originalResidueLeftEndpointPolynomial P b d).coeff k ∈
          residueLowerField c.top H ∧
        (c.originalResidueRightEndpointPolynomial P b d).coeff k ∈
          residueLowerField c.top H := by
  classical
  let := c.originalResponseResidueIntervalInverse P b d
  let ν := OriginalResponseInterval (hD := hD) P b d
  let row := fun i : ν => originalResponseRows P i.1.1
  let col := fun i : ν => originalResponseCols P i.1.1
  let x := P.xi (originalRowSplitEquiv (hD := hD) P (.inl b))
  let y := P.zeta (originalColSplitEquiv (hD := hD) P (.inl d))
  let M := vertexBetaMatrix c.residueMap row col
  let S := residueLowerField c.top H
  have hxy : x - y < (H : ℤ) := hspan
  have hr (i : ν) : row i < x := originalResponse_row_lt P b i.1.1 i.2
  have hc (i : ν) : y < col i := originalResponse_col_gt P d i.1.1 i.1.2
  have hM (i j : ν) : M i j ∈ S := by
    change c.residueMap (hh (row i - col j)) ∈ S
    apply c.residue_hh_mem_lower H hNH
    have hi := hr i
    have hj := hc j
    omega
  have hI (i j : ν) : (⅟M) i j ∈ S := inverse_entries_mem_subfield S M hM i j
  have ho (i : ν) : vertexOutgoing c.residueMap col x () i ∈ S := by
    change c.residueMap (hh (x - col i)) ∈ S
    apply c.residue_hh_mem_lower H hNH
    have hi := hc i
    omega
  have hi (i : ν) : vertexIncoming c.residueMap row y i () ∈ S := by
    change c.residueMap (hh (row i - y)) ∈ S
    apply c.residue_hh_mem_lower H hNH
    have hri := hr i
    omega
  have hleft (i : ν) : (vertexOutgoing c.residueMap col x * ⅟M) () i ∈ S := by
    rw [Matrix.mul_apply]
    apply S.sum_mem
    intro j _
    exact S.mul_mem (ho j) (hI j i)
  have hright (i : ν) : (⅟M * vertexIncoming c.residueMap row y) i () ∈ S := by
    rw [Matrix.mul_apply]
    apply S.sum_mem
    intro j _
    exact S.mul_mem (hI i j) (hi j)
  constructor
  · rw [c.originalLocalResponse_residue_pruned P b d]
    change c.residueMap (hh (x - y)) -
      (vertexOutgoing c.residueMap col x * ⅟M * vertexIncoming c.residueMap row y) () () ∈ S
    apply S.sub_mem (c.residue_hh_mem_lower H hNH (x - y) hxy)
    rw [Matrix.mul_apply]
    apply S.sum_mem
    intro i _
    exact S.mul_mem (hleft i) (hi i)
  · intro k
    constructor
    · change (ordinaryEndpointProfile (fun i : ν => (x - row i).toNat)
        (fun i => (vertexOutgoing c.residueMap col x * ⅟M) () i)).coeff k ∈ S
      exact ordinary_profile_coeff_mem_subfield S _ _ hleft k
    · change (ordinaryEndpointProfile (fun i : ν => (col i - y).toNat)
        (fun i => (⅟M * vertexIncoming c.residueMap row y) i ())).coeff k ∈ S
      exact ordinary_profile_coeff_mem_subfield S _ _ hright k

/-- Every complete actual endpoint-profile coefficient omits any later
surviving generator, including coefficients of the full unit inverse. -/
theorem original_endpoint_profile_coeff_high_zero {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) (H : ℕ+) (hNH : c.top < H)
    (hspan : P.xi (originalRowSplitEquiv (hD := hD) P (.inl b)) -
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl d)) < (H : ℤ)) (k : ℕ) :
    residueGeneratorDeriv c.top ⟨H, ne_of_gt hNH⟩
      ((c.originalResidueLeftEndpointPolynomial P b d).coeff k) = 0 ∧
    residueGeneratorDeriv c.top ⟨H, ne_of_gt hNH⟩
      ((c.originalResidueRightEndpointPolynomial P b d).coeff k) = 0 := by
  have hs := (c.originalLocalResponse_profiles_mem_lower P b d H hNH hspan).2 k
  exact ⟨residueGeneratorDeriv_lower _ _ hs.1, residueGeneratorDeriv_lower _ _ hs.2⟩

end SelectedCoordinate
end SkewCornerDescent.Matrix
