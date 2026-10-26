/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalUpperSupport

/-!
# Monicity of the full original upper responses

Formalizes `shields-2026-skew-corner-descent.tex`, «Equal windows and the determinant defect»
(`sec:normal-chart`, `lem:actual-elimination`). Original endpoint geometry supplies every
ordered support condition. The complete normal-dependent removed inverse is retained.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

attribute [local instance] Classical.propDecidable

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Literal original row coordinates of every surviving removed entry. -/
noncomputable def originalResponseRows {n : ℕ} (P : Profile n)
    (j : OriginalRemainingIndices (hD := hD) P) : ℤ :=
  P.xi (originalRemovedRow (hD := hD) P j.1 j.2).succ

/-- Literal original column coordinates of every surviving removed entry. -/
noncomputable def originalResponseCols {n : ℕ} (P : Profile n)
    (j : OriginalRemainingIndices (hD := hD) P) : ℤ :=
  P.zeta (originalRemovedCol (hD := hD) P j.1 j.2).castSucc

/-- The field inverse is produced from regularity of the actual full removed matrix. -/
@[instance_reducible]
noncomputable def originalRemovedFieldInverse {n : ℕ} (P : Profile n) :
    Invertible (intervalMatrix (originalResponseRows (hD := hD) P)
      (originalResponseCols (hD := hD) P)) :=
  c.regularEmbeddedMatrixInverse (originalRemovedMatrix (hD := hD) P)
    (not_dvd_originalRemovedMatrix (hD := hD) P)

/-- Embedding a full local response keeps the entire literal original-field interval. -/
theorem originalLocalResponse_embedding_interval {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) :
    letI := c.originalRemovedFieldInverse P
    c.regularEmbedding (c.originalLocalResponse P b d) =
      intervalResponse (P.xi (originalRowSplitEquiv (hD := hD) P (.inl b)))
        (P.zeta (originalColSplitEquiv (hD := hD) P (.inl d)))
        (originalResponseRows (hD := hD) P) (originalResponseCols (hD := hD) P) := by
  let := c.originalRemovedLocalInverse P
  let := c.originalRemovedFieldInverse P
  rw [c.originalLocalResponse_entry, map_sub, c.regularEmbedding_polynomial]
  have hm : ((originalRemovedMatrix (hD := hD) P).map
      (algebraMap Lambda c.RegularRing)).map c.regularEmbedding =
      intervalMatrix (originalResponseRows (hD := hD) P)
        (originalResponseCols (hD := hD) P) := by
    apply Matrix.ext
    intro i j
    exact c.regularEmbedding_polynomial _
  rw [map_inverseContraction, hm, intervalResponse_eq_sub_inverseContraction]
  have hr : (c.regularEmbedding ∘ fun j : OriginalRemainingIndices (hD := hD) P =>
      algebraMap Lambda c.RegularRing
        ((originalSplitMatrix (hD := hD) P) (.inl b) (.inr j))) =
      fun j => originalMap (hh (P.xi (originalRowSplitEquiv (hD := hD) P (.inl b)) -
        originalResponseCols (hD := hD) P j)) := by
    funext j
    calc
      _ = originalMap ((originalSplitMatrix (hD := hD) P) (.inl b) (.inr j)) :=
        c.regularEmbedding_polynomial _
      _ = _ := by
        change originalMap (hh (_ - P.zeta (originalColSplitEquiv (hD := hD) P (.inr j)))) = _
        rw [originalColSplitEquiv_removed]
        rfl
  have hc : (c.regularEmbedding ∘ fun j : OriginalRemainingIndices (hD := hD) P =>
      algebraMap Lambda c.RegularRing
        ((originalSplitMatrix (hD := hD) P) (.inr j) (.inl d))) =
      fun j => originalMap (hh (originalResponseRows (hD := hD) P j -
        P.zeta (originalColSplitEquiv (hD := hD) P (.inl d)))) := by
    funext j
    calc
      _ = originalMap ((originalSplitMatrix (hD := hD) P) (.inr j) (.inl d)) :=
        c.regularEmbedding_polynomial _
      _ = _ := by
        change originalMap (hh (P.xi (originalRowSplitEquiv (hD := hD) P (.inr j)) - _)) = _
        rw [originalRowSplitEquiv_removed]
        rfl
  rw [hr, hc]
  rfl

/-- Full original responses are monic in their literal positive endpoint distance.
No endpoint support or inverse regularity is assumed: both are produced from the source. -/
theorem originalLocalResponse_triangular {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) (K : ℕ+)
    (hK : P.xi (originalRowSplitEquiv (hD := hD) P (.inl b)) -
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl d)) = (K : ℤ)) :
    ∃ A ∈ lowerGeneratorField K,
      c.regularEmbedding (c.originalLocalResponse P b d) = originalMap (MvPolynomial.X K) + A ∧
      generatorDeriv K (c.regularEmbedding (c.originalLocalResponse P b d)) = 1 := by
  let := c.originalRemovedFieldInverse P
  rw [c.originalLocalResponse_embedding_interval]
  have hM : (intervalMatrix (originalResponseRows (hD := hD) P)
      (originalResponseCols (hD := hD) P)).BlockTriangular
      (fun j => (interiorBlock P j.1.val : ℤ)) := by
    intro i j hij
    change (interiorBlock P j.1.val : ℤ) < (interiorBlock P i.1.val : ℤ) at hij
    exact (originalRemovedMatrix_blockTriangular (hD := hD) P).map originalMap
      (by exact_mod_cast hij)
  apply ordered_intervalResponse_triangular _ _
    (originalResponseRows (hD := hD) P) (originalResponseCols (hD := hD) P)
    (fun j => (interiorBlock P j.1.val : ℤ)) hM
    (originalResponseLowerCut P b) (originalResponseUpperCut P d)
  · exact fun j hj => originalResponse_incoming_cutoff P b j hj
  · exact fun j hj => originalResponse_outgoing_cutoff P d j hj
  · exact fun j => originalResponse_row_lt P b j.1.1 j.2
  · exact fun j => originalResponse_col_gt P d j.1.1 j.1.2
  · exact hK

end SkewCornerDescent.Matrix.SelectedCoordinate
