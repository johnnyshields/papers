/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalUpperResponses

/-!
# Ordinary endpoint profiles of complete original retained intervals

Formalizes `shields-2026-skew-corner-descent.tex`, «From response functions to literal copies»
(`sec:one-active`, `lem:profile-derivative`). Actual endpoint support restricts the full removed
inverse. Its ordered interval has ordinary endpoint profiles and all three original and normal
coordinate derivative identities. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

attribute [local instance] Classical.propDecidable

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The block order of the genuine full original removed matrix. -/
theorem originalResponse_blockTriangular {n : ℕ} (P : Profile n) :
    (intervalMatrix (originalResponseRows (hD := hD) P)
      (originalResponseCols (hD := hD) P)).BlockTriangular
        (fun j => (interiorBlock P j.1.val : ℤ)) := by
  intro i j hij
  change (interiorBlock P j.1.val : ℤ) < (interiorBlock P i.1.val : ℤ) at hij
  exact (originalRemovedMatrix_blockTriangular (hD := hD) P).map originalMap
    (by exact_mod_cast hij)

/-- All removed entries strictly inside the retained endpoints' actual block cuts. -/
abbrev OriginalResponseInterval {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) :=
  OrderedIntervalIndex (fun j : OriginalRemainingIndices (hD := hD) P =>
    (interiorBlock P j.1.val : ℤ)) (originalResponseLowerCut P b) (originalResponseUpperCut P d)

/-- The pruned inverse is constructed from the proved full inverse and actual block order. -/
@[instance_reducible]
noncomputable def originalResponseIntervalInverse {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) :
    Invertible (intervalMatrix
      (fun i : OriginalResponseInterval (hD := hD) P b d => originalResponseRows P i.1.1)
      (fun i => originalResponseCols P i.1.1)) := by
  let := c.originalRemovedFieldInverse P
  exact orderedResponseInverse _ _ _ (originalResponse_blockTriangular P) _ _

/-- The complete local response equals the interval whose profiles are used for differentiation. -/
theorem originalLocalResponse_embedding_pruned {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) :
    letI := c.originalResponseIntervalInverse P b d
    c.regularEmbedding (c.originalLocalResponse P b d) =
      intervalResponse (P.xi (originalRowSplitEquiv (hD := hD) P (.inl b)))
        (P.zeta (originalColSplitEquiv (hD := hD) P (.inl d)))
        (fun i : OriginalResponseInterval (hD := hD) P b d => originalResponseRows P i.1.1)
        (fun i => originalResponseCols P i.1.1) := by
  let := c.originalRemovedFieldInverse P
  let := c.originalResponseIntervalInverse P b d
  rw [c.originalLocalResponse_embedding_interval]
  apply intervalResponse_ordered_restriction _ _ _ _ _ (originalResponse_blockTriangular P)
  · exact fun j hj => originalResponse_incoming_cutoff P b j hj
  · exact fun j hj => originalResponse_outgoing_cutoff P d j hj

/-- Ordinary full-inverse endpoint profiles and the three derivative formulas for the actual
retained response. The profile coefficients are never substituted by diagonal-only inverses. -/
theorem originalLocalResponse_profiles_derivatives {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) (j : ℕ+) :
    letI := c.originalResponseIntervalInverse P b d
    let row := fun i : OriginalResponseInterval (hD := hD) P b d => originalResponseRows P i.1.1
    let col := fun i : OriginalResponseInterval (hD := hD) P b d => originalResponseCols P i.1.1
    let x := P.xi (originalRowSplitEquiv (hD := hD) P (.inl b))
    let y := P.zeta (originalColSplitEquiv (hD := hD) P (.inl d))
    (∃ L R : Polynomial actualField,
      leftEndpointProfile x row col = L.toLaurent ∧
      rightEndpointProfile y row col = R.toLaurent) ∧
    generatorDeriv j (c.regularEmbedding (c.originalLocalResponse P b d)) =
      (leftEndpointProfile x row col * rightEndpointProfile y row col).coeff (x - y - (j : ℤ)) ∧
    originalMap c.coefficient * normalDeriv c.top c.coefficient
        (c.regularEmbedding (c.originalLocalResponse P b d)) =
      (leftEndpointProfile x row col * rightEndpointProfile y row col).coeff
        (x - y - (c.top : ℤ)) ∧
    generatorDeriv j (c.regularEmbedding (c.originalLocalResponse P b d)) =
      fixedNormalDeriv c.top j c.coefficient c.remainder
        (c.regularEmbedding (c.originalLocalResponse P b d)) +
      normalDeriv c.top c.coefficient (c.regularEmbedding (c.originalLocalResponse P b d)) *
        generatorDeriv j (originalMap (cellSchur D hD.1)) := by
  let := c.originalResponseIntervalInverse P b d
  dsimp only
  rw [c.originalLocalResponse_embedding_pruned]
  refine ⟨?_, c.interval_derivative_identities _ _ _ _ j⟩
  obtain ⟨hL, hR⟩ := interval_profiles_ordinary
    (P.xi (originalRowSplitEquiv (hD := hD) P (.inl b)))
    (P.zeta (originalColSplitEquiv (hD := hD) P (.inl d)))
    (fun i : OriginalResponseInterval (hD := hD) P b d => originalResponseRows P i.1.1)
    (fun i => originalResponseCols P i.1.1)
    (fun i => originalResponse_row_lt P b i.1.1 i.2)
    (fun i => originalResponse_col_gt P d i.1.1 i.1.2)
  exact ⟨_, _, hL, hR⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
