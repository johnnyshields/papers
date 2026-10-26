/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.ResidueActiveClasses
import SkewCornerDescent.Matrix.OriginalPolynomialFamilies

/-!
# Full source response class counts

Supports `shields-2026-skew-corner-descent.tex` (`lem:residue-classifier`).
Prime-association multiplicities equal counts of literal full response equality in the
unchanged residue field. Complete original matrix responses inherit this equality from
their produced monic representatives. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing MvPolynomial

/-- Association of full monic triangular responses is exactly equality of their source
field evaluations, not equality up to a discarded lower-coordinate unit. -/
theorem residueHigherResponse_associated_iff {N : ℕ+}
    {K H : ResidueHigherIndex N} {A E : ResidueHigherPolynomial N}
    (hA : ∀ j ∈ A.vars, j < K) (hE : ∀ j ∈ E.vars, j < H) :
    Associated (X K + A) (X H + E) ↔
      residueHigherEval N (X K + A) = residueHigherEval N (X H + E) := by
  constructor
  · intro ha
    obtain ⟨hKH, hAE⟩ := (monicTriangularPolynomial_associated_iff hA hE).mp ha
    rw [hKH, hAE]
  · intro he
    exact (residueHigherEval_injective N he) ▸ Associated.refl _

/-- Full source-field equality counts preserve every retained occurrence, including
repeated responses and coincident cap classes. -/
theorem triangularClassCount_eq_source_count (N : ℕ+) {ι : Type*}
    (s : Finset ι) (J : ι → ResidueHigherIndex N)
    (B : ι → ResidueHigherPolynomial N)
    (hB : ∀ i ∈ s, ∀ j ∈ (B i).vars, j < J i)
    (H : ResidueHigherIndex N) (E : ResidueHigherPolynomial N)
    (hE : ∀ j ∈ E.vars, j < H) :
    triangularClassCount s J B (X H + E) =
      (s.filter fun i => residueHigherEval N (X H + E) =
        residueHigherEval N (X (J i) + B i)).card := by
  classical
  unfold triangularClassCount
  congr 1
  apply Finset.filter_congr
  intro i hi
  exact residueHigherResponse_associated_iff hE (hB i hi)

namespace SelectedCoordinate

variable {D : SkewGluing.Diagram} {hD : SkewGluing.IsConnectedSkew D}
    (c : SelectedCoordinate D hD)

/-- The complete original response family has representatives whose prime class counts
are exactly its original source-field equality counts. No class-count correspondence is
assumed of the matrix presentation. -/
theorem originalHessenberg_class_counts {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ SkewGluing.edgeComponents (SkewGluing.diagramInterior P.cells),
      SkewGluing.span C ≤ (c.top : ℕ)) :
    ∃ J : Fin (originalSelectedCount (hD := hD) P + 1) → ResidueHigherIndex c.top,
      ∃ B : Fin (originalSelectedCount (hD := hD) P + 1) → ResidueHigherPolynomial c.top,
        (∀ i, (∀ j ∈ (B i).vars, j < J i) ∧
          residueHigherEval c.top (X (J i) + B i) =
            c.regularResidue (c.originalHessenbergResponse P i i) ∧
          ((J i).val : ℤ) = originalHessenbergDistance (hD := hD) P i i) ∧
        ∀ (s : Finset (Fin (originalSelectedCount (hD := hD) P + 1)))
          (H : ResidueHigherIndex c.top) (E : ResidueHigherPolynomial c.top),
          (∀ j ∈ E.vars, j < H) →
          triangularClassCount s J B (X H + E) =
            (s.filter fun i => residueHigherEval c.top (X H + E) =
              c.regularResidue (c.originalHessenbergResponse P i i)).card := by
  obtain ⟨J, B, h⟩ := c.originalHessenberg_polynomial_family P hB hmax
  refine ⟨J, B, h, ?_⟩
  intro s H E hE
  rw [triangularClassCount_eq_source_count c.top s J B (fun i _ => (h i).1) H E hE]
  simp_rw [fun i => (h i).2.1]

end SelectedCoordinate
end SkewCornerDescent.Matrix
