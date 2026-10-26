/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalNormalAffine
import SkewCornerDescent.Matrix.NormalRationalAffineJets
import SkewCornerDescent.Matrix.OriginalSchurNormalTransfer

/-!
# Affine first-fresh coefficients of the whole original Schur germ

Supports `shields-2026-skew-corner-descent.tex` (`lem:original-transfer`). The
complete removed determinant and its orientation sign stay in the full normal
series. Actual interval geometry supplies lower earlier jets and an affine fresh
coefficient. No full inverse is replaced by a residue. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing MvPolynomial CyclicWindows

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Every full removed-factor jet is in the strict lower field. -/
theorem originalRemoved_normalSeries_coeff_mem_lower {n : ℕ} (P : Profile n)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (K : ℕ+) (hK : c.top < K) (l : ℕ) :
    PowerSeries.coeff l (c.normalPolynomialSeries (originalRemovedMatrix (hD := hD) P).det) ∈
      residueLowerField c.top K := by
  apply c.normalPolynomialSeries_coeff_mem_lower K hK
  apply mem_supported.mpr
  intro j hj
  have hs := originalRemovedMatrix_det_span_le (hD := hD) P (c.top : ℕ)
    (originalBlock_span_le_of_components P _ hmax)
  exact lt_of_le_of_lt ((Finset.le_sup hj).trans hs) hK

/-- The whole original Schur germ inherits its affine first-fresh jet from the
complete matrix. Its removed factor and orientation remain present. -/
theorem originalSchur_jets_affine_from_length_bound {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (K : ℕ+) (hK : c.top < K) (m : ℕ) (hm : 0 < m)
    (hmB : m ≤ originalSelectedCount (hD := hD) P)
    (hbound : ∀ i j : Fin (originalSelectedCount (hD := hD) P + 1), i ≤ j →
      j.val - i.val = m → originalHessenbergDistance (hD := hD) P i j ≤ (K : ℤ)) :
    jetsAffineOver (residueLowerField c.top K) (residueGenerator c.top ⟨K, ne_of_gt hK⟩)
      (c.normalPolynomialSeries P.schur) m := by
  obtain ⟨ε, _, he⟩ := c.originalSchur_normalSeries_signed_factorization P
  rw [he]
  apply jetsAffineOver_mul _ _ hm
  · apply jetsAffineOver_mul _ _ hm
    · simpa using jetsAffineOver_C (residueLowerField c.top K)
        (residueGenerator c.top ⟨K, ne_of_gt hK⟩) ((residueLowerField c.top K).intCast_mem ε) m
    · exact jetsAffineOver_of_coeff_mem _ _ _ m
        (c.originalRemoved_normalSeries_coeff_mem_lower P hmax K hK)
  · exact c.originalHessenberg_jets_affine_from_length_bound P hB hmax K hK m hm hmB hbound

/-- The standing completed-gap period produces every exact-cost bound needed
for affine first-fresh coefficients of the complete original source. -/
theorem originalSchur_jets_affine_periodic {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (r k m : ℕ) (hm : 0 < m) (hmB : m < originalSelectedCount (hD := hD) P)
    (hlen : m + 1 = k * r)
    (hp : Function.Periodic
      (fun z => c.originalCompletedGap P ((ZMod.finEquiv _).symm z))
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (K : ℕ+) (hK : c.top < K)
    (hKeq : (K : ℤ) = (c.top : ℤ) + k • windowSum
      (fun z => c.originalCompletedGap P ((ZMod.finEquiv _).symm z)) 1 r 0) :
    jetsAffineOver (residueLowerField c.top K) (residueGenerator c.top ⟨K, ne_of_gt hK⟩)
      (c.normalPolynomialSeries P.schur) m := by
  apply c.originalSchur_jets_affine_from_length_bound P hB hmax K hK m hm hmB.le
  intro i j hij hcost
  rw [hKeq]
  exact c.originalHessenbergDistance_bound_of_periodic_gaps P hB r k m hm hmB hlen hp i j hij hcost

end SkewCornerDescent.Matrix.SelectedCoordinate
