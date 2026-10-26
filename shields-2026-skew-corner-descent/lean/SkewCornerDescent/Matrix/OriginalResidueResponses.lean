/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.ResidueLowerBounds

/-!
# Protected original responses at the actual residue

Formalizes `shields-2026-skew-corner-descent.tex`, «Equal windows and the determinant defect»
(`sec:normal-chart`, `lem:actual-elimination`, `lem:residue-classifier`). Ordered locality
retains every intervening inverse entry, while normal substitution preserves the protected
original top. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

noncomputable local instance (N : ℕ+) : Algebra ℚ (OtherField N) := OreLocalization.instAlgebra

/-- A complete inverse contraction stays in a subfield containing every input entry. -/
theorem inverseContraction_mem_subfield {F ν : Type*} [Field F] [Fintype ν] [DecidableEq ν]
    (S : Subfield F) (r s : ν → F) (M : Matrix ν ν F) [Invertible M]
    (hr : ∀ i, r i ∈ S) (hs : ∀ i, s i ∈ S) (hM : ∀ i j, M i j ∈ S) :
    inverseContraction r s M ∈ S := by
  unfold inverseContraction
  apply S.sum_mem
  intro i _
  apply S.sum_mem
  intro j _
  apply S.mul_mem _ (hs j)
  apply S.mul_mem (hr i)
  rw [← Matrix.invOf_eq_nonsing_inv]
  exact inverse_entries_mem_subfield S M hM i j

namespace SelectedCoordinate

attribute [local instance] Classical.propDecidable

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The full original response specializes with its complete actual residue inverse. -/
theorem originalLocalResponse_residue_contraction {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) :
    c.regularResidue (c.originalLocalResponse P b d) =
      c.residueMap ((originalSplitMatrix (hD := hD) P) (.inl b) (.inl d)) -
      inverseContraction
        (fun j => c.residueMap ((originalSplitMatrix (hD := hD) P) (.inl b) (.inr j)))
        (fun j => c.residueMap ((originalSplitMatrix (hD := hD) P) (.inr j) (.inl d)))
        ((originalRemovedMatrix (hD := hD) P).map c.residueMap) := by
  let := c.originalRemovedLocalInverse P
  rw [c.originalLocalResponse_entry, map_sub, c.regularResidue_polynomial]
  have hm : ((originalRemovedMatrix (hD := hD) P).map
      (algebraMap Lambda c.RegularRing)).map c.regularResidue =
      (originalRemovedMatrix (hD := hD) P).map c.residueMap := by
    apply Matrix.ext
    intro i j
    exact c.regularResidue_polynomial _
  rw [map_inverseContraction, hm]
  have hr : (c.regularResidue ∘ fun j : OriginalRemainingIndices (hD := hD) P =>
      algebraMap Lambda c.RegularRing
        ((originalSplitMatrix (hD := hD) P) (.inl b) (.inr j))) =
      fun j => c.residueMap ((originalSplitMatrix (hD := hD) P) (.inl b) (.inr j)) := by
    funext j
    exact c.regularResidue_polynomial _
  have hs : (c.regularResidue ∘ fun j : OriginalRemainingIndices (hD := hD) P =>
      algebraMap Lambda c.RegularRing
        ((originalSplitMatrix (hD := hD) P) (.inr j) (.inl d))) =
      fun j => c.residueMap ((originalSplitMatrix (hD := hD) P) (.inr j) (.inl d)) := by
    funext j
    exact c.regularResidue_polynomial _
  rw [hr, hs]

/-- Every actual upper response preserves its literal protected top after normal substitution. -/
theorem originalLocalResponse_residue_triangular {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) (K : ℕ+) (hNK : c.top < K)
    (hK : P.xi (originalRowSplitEquiv (hD := hD) P (.inl b)) -
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl d)) = (K : ℤ)) :
    ∃ A ∈ residueLowerField c.top K,
      c.regularResidue (c.originalLocalResponse P b d) = c.residueMap (MvPolynomial.X K) + A := by
  let := c.originalRemovedResidueInverse P
  let M := (originalRemovedMatrix (hD := hD) P).map c.residueMap
  let r := fun j : OriginalRemainingIndices (hD := hD) P =>
    c.residueMap ((originalSplitMatrix (hD := hD) P) (.inl b) (.inr j))
  let s := fun j : OriginalRemainingIndices (hD := hD) P =>
    c.residueMap ((originalSplitMatrix (hD := hD) P) (.inr j) (.inl d))
  let label := fun j : OriginalRemainingIndices (hD := hD) P => (interiorBlock P j.1.val : ℤ)
  let lo := originalResponseLowerCut P b
  let hi := originalResponseUpperCut P d
  have hM : M.BlockTriangular label := by
    intro i j hij
    change (interiorBlock P j.1.val : ℤ) < (interiorBlock P i.1.val : ℤ) at hij
    exact (originalRemovedMatrix_blockTriangular (hD := hD) P).map c.residueMap
      (by exact_mod_cast hij)
  let := orderedIntervalInverse M label hM lo hi
  let MI := ((M.toBlock (fun i => label i < hi) (fun i => label i < hi)).toBlock
    (fun i => lo < label i.1) (fun i => lo < label i.1))
  have hr : ∀ j, ¬lo < label j → r j = 0 := by
    intro j hj
    change c.residueMap (hh (_ - P.zeta (originalColSplitEquiv (hD := hD) P (.inr j)))) = 0
    rw [originalColSplitEquiv_removed, hh_of_neg
      (by have := originalResponse_incoming_cutoff P b j hj; omega), map_zero]
  have hs : ∀ j, ¬label j < hi → s j = 0 := by
    intro j hj
    change c.residueMap (hh (P.xi (originalRowSplitEquiv (hD := hD) P (.inr j)) - _)) = 0
    rw [originalRowSplitEquiv_removed, hh_of_neg
      (by have := originalResponse_outgoing_cutoff P d j hj; omega), map_zero]
  have hentry (i j : OrderedIntervalIndex label lo hi) : MI i j ∈ residueLowerField c.top K := by
    apply c.residue_hh_mem_lower K hNK
    change P.xi (originalRemovedRow (hD := hD) P i.1.1.1 i.1.1.2).succ -
      P.zeta (originalRemovedCol (hD := hD) P j.1.1.1 j.1.1.2).castSucc < (K : ℤ)
    have hx := originalResponse_row_lt P b i.1.1 i.2
    have hy := originalResponse_col_gt P d j.1.1 j.1.2
    omega
  have hri (i : OrderedIntervalIndex label lo hi) : r i.1.1 ∈ residueLowerField c.top K := by
    change c.residueMap (hh (_ - P.zeta (originalColSplitEquiv (hD := hD) P (.inr i.1.1)))) ∈ _
    rw [originalColSplitEquiv_removed]
    apply c.residue_hh_mem_lower K hNK
    have hy := originalResponse_col_gt P d i.1.1 i.1.2
    omega
  have hsi (i : OrderedIntervalIndex label lo hi) : s i.1.1 ∈ residueLowerField c.top K := by
    change c.residueMap (hh (P.xi (originalRowSplitEquiv (hD := hD) P (.inr i.1.1)) - _)) ∈ _
    rw [originalRowSplitEquiv_removed]
    apply c.residue_hh_mem_lower K hNK
    have hx := originalResponse_row_lt P b i.1.1 i.2
    omega
  have hcorr : inverseContraction r s M ∈ residueLowerField c.top K := by
    rw [inverseContraction_interval r s M label hM lo hi hr hs]
    exact inverseContraction_mem_subfield _ _ _ MI hri hsi hentry
  refine ⟨-inverseContraction r s M, (residueLowerField c.top K).neg_mem hcorr, ?_⟩
  rw [c.originalLocalResponse_residue_contraction]
  change c.residueMap (hh (_ - _)) - inverseContraction r s M = _
  rw [hK, hh_pnat]
  ring

/-- The actual assembled protected response is transcendental, with no supplied lower correction. -/
theorem originalLocalResponse_residue_transcendental {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) (K : ℕ+) (hNK : c.top < K)
    (hK : P.xi (originalRowSplitEquiv (hD := hD) P (.inl b)) -
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl d)) = (K : ℤ)) :
    Transcendental (residueLowerField c.top K)
      (c.regularResidue (c.originalLocalResponse P b d)) := by
  obtain ⟨A, hA, he⟩ := c.originalLocalResponse_residue_triangular P b d K hNK hK
  rw [he, c.residueMap_other K (ne_of_gt hNK)]
  have ht := residue_triangular_quotient_transcendental c.top ⟨K, ne_of_gt hNK⟩ A 1
    hA (residueLowerField c.top K).one_mem one_ne_zero
  simpa only [div_one, residueGenerator] using ht

end SelectedCoordinate
end SkewCornerDescent.Matrix
