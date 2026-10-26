/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.EffectiveIncomingCoordinates

/-!
# Complete effective outgoing coordinates before a known original suffix

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`). Negating
and exchanging the literal beta lists transposes the complete original matrix.
Thus the full outgoing correction uses the certified incoming recovery mechanism,
with all suffix couplings retained. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing
open scoped BigOperators

/-- Negating and exchanging beta lists transposes the full matrix, with no
symmetric-function conjugation or change of coefficient generators. -/
theorem vertexBetaMatrix_neg_transpose {ν F : Type*} [CommRing F]
    (ι : Lambda →+* F) (row col : ν → ℤ) :
    vertexBetaMatrix ι (fun i => -col i) (fun i => -row i) =
      Matrix.transpose (vertexBetaMatrix ι row col) := by
  ext i j
  change ι (hh (-col i - -row j)) = ι (hh (row j - col i))
  congr 2
  ring

namespace SelectedCoordinate

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The reflected inverse is produced by transposing the actual full inverse. -/
@[instance_reducible]
noncomputable def reflectedResidueBetaInverse {ν : Type*} [Fintype ν] [DecidableEq ν]
    (row col : ν → ℤ) [Invertible (vertexBetaMatrix c.residueMap row col)] :
    Invertible (vertexBetaMatrix c.residueMap (fun i => -col i) (fun i => -row i)) := by
  rw [vertexBetaMatrix_neg_transpose]
  exact Matrix.invertibleTranspose _

/-- The complete effective outgoing coordinate at the original row `y + J`. -/
noncomputable def effectiveOutgoingCoordinate {ν : Type*} [Fintype ν] [DecidableEq ν]
    (row col : ν → ℤ) (y : ℤ) [Invertible (vertexBetaMatrix c.residueMap row col)]
    (J : ResidueHigherIndex c.top) : OtherField c.top :=
  residueGenerator c.top ⟨J.val, ne_of_gt J.prop⟩ -
    inverseContraction (fun i => c.residueMap (hh (y + (J.val : ℤ) - col i)))
      (fun i => c.residueMap (hh (row i - y))) (vertexBetaMatrix c.residueMap row col)

/-- Reflection relates the same full rational contraction, not just its signs
or its values at a single specialization. -/
theorem effective_outgoing_reflected {ν : Type*} [Fintype ν] [DecidableEq ν]
    (row col : ν → ℤ) (y : ℤ) [Invertible (vertexBetaMatrix c.residueMap row col)]
    (J : ResidueHigherIndex c.top) :
    letI := c.reflectedResidueBetaInverse row col
    c.effectiveOutgoingCoordinate row col y J =
      c.effectiveIncomingCoordinate (fun i => -col i) (fun i => -row i) (-y) J := by
  let := c.reflectedResidueBetaInverse row col
  rw [effectiveOutgoingCoordinate, effectiveIncomingCoordinate, vertexBetaMatrix_neg_transpose]
  apply congrArg (fun z : OtherField c.top => residueGenerator c.top ⟨J.val, ne_of_gt J.prop⟩ - z)
  rw [inverseContraction_transpose]
  have hr : (fun i => c.residueMap (hh (-y - -row i))) =
      fun i => c.residueMap (hh (row i - y)) := by
    funext i
    congr 2
    ring
  have hs : (fun i => c.residueMap (hh (-col i - (-y - (J.val : ℤ))))) =
      fun i => c.residueMap (hh (y + (J.val : ℤ) - col i)) := by
    funext i
    congr 2
    ring
  rw [hr, hs]

/-- The complete suffix correction is strictly below the candidate's own row
generator throughout the valid finite original candidate domain. -/
theorem effective_outgoing_triangular {ν : Type*} [Fintype ν] [DecidableEq ν]
    (row col : ν → ℤ) (y : ℤ) [Invertible (vertexBetaMatrix c.residueMap row col)]
    (hcol : ∀ i, y < col i) (J : ResidueHigherIndex c.top)
    (hrow : ∀ i, row i - y < (J.val : ℤ)) :
    ∃ R ∈ residueLowerField c.top J.val,
      c.effectiveOutgoingCoordinate row col y J =
        residueGenerator c.top ⟨J.val, ne_of_gt J.prop⟩ + R := by
  let := c.reflectedResidueBetaInverse row col
  have h := c.effective_incoming_triangular (fun i => -col i) (fun i => -row i) (-y)
    (fun i => neg_lt_neg (hcol i)) J (fun i => by have := hrow i; omega)
  rw [← c.effective_outgoing_reflected row col y J] at h
  exact h

/-- An effective outgoing coordinate is the literal original row response. -/
theorem effective_outgoing_original_coordinate {ν : Type*}
    [Fintype ν] [DecidableEq ν] (row col : ν → ℤ) (y R : ℤ)
    [Invertible (vertexBetaMatrix c.residueMap row col)]
    (J : ResidueHigherIndex c.top) (hJ : R - y = (J.val : ℤ)) :
    c.residueMap (hh (R - y)) -
      inverseContraction (fun i => c.residueMap (hh (R - col i)))
        (fun i => c.residueMap (hh (row i - y))) (vertexBetaMatrix c.residueMap row col) =
      c.effectiveOutgoingCoordinate row col y J := by
  have hR : R = y + (J.val : ℤ) := by omega
  have hj : y + (J.val : ℤ) - y = (J.val : ℤ) := by ring
  rw [hR, effectiveOutgoingCoordinate, hj, hh_pnat,
    c.residueMap_other J.val (ne_of_gt J.prop)]
  rfl

/-- Equal complete effective outgoing inventories recover their finite original
row-index sets, even in the presence of arbitrary full nonrow suffix units. -/
theorem effective_outgoing_support_eq {ν ι κ : Type*}
    [Fintype ν] [DecidableEq ν] [Fintype ι] [Fintype κ]
    (row col : ν → ℤ) (y : ℤ) [Invertible (vertexBetaMatrix c.residueMap row col)]
    (hcol : ∀ i, y < col i)
    (left : ι → ResidueHigherIndex c.top) (right : κ → ResidueHigherIndex c.top)
    (hleft : Function.Injective left) (hright : Function.Injective right)
    (hrowsLeft : ∀ i j, row j - y < ((left i).val : ℤ))
    (hrowsRight : ∀ i j, row j - y < ((right i).val : ℤ))
    (a : ι → residueLowerField c.top c.top) (b : κ → residueLowerField c.top c.top)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ j, b j ≠ 0)
    (hvalue : (∑ i, (a i : OtherField c.top) * c.effectiveOutgoingCoordinate row col y (left i)) =
      ∑ j, (b j : OtherField c.top) * c.effectiveOutgoingCoordinate row col y (right j)) :
    Finset.univ.image left = Finset.univ.image right := by
  apply c.triangular_higher_linear_support_eq (c.effectiveOutgoingCoordinate row col y)
    left right ?_ hleft hright a b ha hb hvalue
  intro J hJ
  rcases Finset.mem_union.mp hJ with hJ | hJ
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hJ
    exact c.effective_outgoing_triangular row col y hcol (left i) (hrowsLeft i)
  · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hJ
    exact c.effective_outgoing_triangular row col y hcol (right j) (hrowsRight j)

end SelectedCoordinate
end SkewCornerDescent.Matrix
