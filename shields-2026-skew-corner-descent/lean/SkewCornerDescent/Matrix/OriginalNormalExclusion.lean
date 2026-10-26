/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.NormalSeriesSupport

/-!
# Protected-generator exclusion in original normal jets

Supports `shields-2026-skew-corner-descent.tex` (`lem:original-transfer`).
A shorter literal retained interval omits every later protected generator at all
normal orders. Positive-order jets of a complete response also omit that response's
own leading generator. These are properties of the actual complete inverse, not
of a residue-only replacement.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing MvPolynomial

/-- Determinants preserve coefficient subfields via the actual coefficient-ring map. -/
theorem series_coeff_det_mem_subfield {F : Type*} [Field F] (S : Subfield F)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι (PowerSeries F))
    (hA : ∀ i j n, PowerSeries.coeff n (A i j) ∈ S) (n : ℕ) :
    PowerSeries.coeff n A.det ∈ S := by
  let B : Matrix ι ι (PowerSeries S.toSubring) :=
    fun i j => (A i j).toSubring S.toSubring (hA i j)
  have he : B.map (PowerSeries.map S.toSubring.subtype) = A := by
    apply Matrix.ext
    intro i j
    exact PowerSeries.map_toSubring (A i j) S.toSubring (hA i j)
  rw [← he]
  change PowerSeries.coeff n ((PowerSeries.map S.toSubring.subtype).mapMatrix B).det ∈ S
  rw [← RingHom.map_det, PowerSeries.coeff_map]
  exact (PowerSeries.coeff n B.det).property

namespace SelectedCoordinate

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Full inverse jets of a shorter actual interval cannot see a later protected generator. -/
theorem originalLocalResponse_normalSeries_coeff_below {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) (J K : ℕ+)
    (hNJ : c.top < J) (hJK : J < K)
    (hJ : P.xi (originalRowSplitEquiv (hD := hD) P (.inl b)) -
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl d)) = (J : ℤ))
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (m : ℕ) :
    PowerSeries.coeff m (c.normalSeries (c.originalLocalResponse P b d)) ∈
      residueLowerField c.top K := by
  obtain ⟨A, hA, he⟩ := c.originalLocalResponse_normalSeries_lower_jets P b d J hNJ hJ hmax
  rw [he, map_add]
  apply Subfield.add_mem
  · rw [PowerSeries.coeff_C]
    split_ifs
    · rw [← c.residueMap_other J (ne_of_gt hNJ)]
      exact c.residue_other_mem_lower K J (ne_of_gt hNJ) hJK
    · exact Subfield.zero_mem _
  · exact residueLowerField_mono hJK.le (hA m)

/-- Positive-order jets contain no occurrence of the actual response's own leading generator. -/
theorem originalLocalResponse_normalSeries_positive_coeff {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) (K : ℕ+) (hNK : c.top < K)
    (hK : P.xi (originalRowSplitEquiv (hD := hD) P (.inl b)) -
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl d)) = (K : ℤ))
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (m : ℕ) (hm : m ≠ 0) :
    PowerSeries.coeff m (c.normalSeries (c.originalLocalResponse P b d)) ∈
      residueLowerField c.top K := by
  obtain ⟨A, hA, he⟩ := c.originalLocalResponse_normalSeries_lower_jets P b d K hNK hK hmax
  simpa only [he, map_add, PowerSeries.coeff_C, ite_eq_right hm, zero_add] using hA m

end SelectedCoordinate
end SkewCornerDescent.Matrix
