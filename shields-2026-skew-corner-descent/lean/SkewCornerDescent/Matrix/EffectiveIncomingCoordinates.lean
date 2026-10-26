/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.TriangularHigherRecovery
import SkewCornerDescent.Matrix.OrderedComponentProfileTops
import SkewCornerDescent.Matrix.OriginalResidueResponses

/-!
# Complete effective incoming coordinates after a known original prefix

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`). A
candidate original column retains the full earlier inverse contraction. Its
monic protected top is proved only on the actual finite candidate domain;
there is no artificial extension or replacement outside that domain.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing
open scoped BigOperators

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The original effective incoming coordinate at column `x - J`, with every
earlier block coupling included. -/
noncomputable def effectiveIncomingCoordinate {ν : Type*} [Fintype ν] [DecidableEq ν]
    (row col : ν → ℤ) (x : ℤ) [Invertible (vertexBetaMatrix c.residueMap row col)]
    (J : ResidueHigherIndex c.top) : OtherField c.top :=
  residueGenerator c.top ⟨J.val, ne_of_gt J.prop⟩ -
    inverseContraction (fun i => c.residueMap (hh (x - col i)))
      (fun i => c.residueMap (hh (row i - (x - (J.val : ℤ)))))
      (vertexBetaMatrix c.residueMap row col)

/-- The complete original prefix correction is strictly below the candidate's
own high generator, not merely below the largest candidate generator. -/
theorem effective_incoming_triangular {ν : Type*} [Fintype ν] [DecidableEq ν]
    (row col : ν → ℤ) (x : ℤ) [Invertible (vertexBetaMatrix c.residueMap row col)]
    (hrow : ∀ i, row i < x) (J : ResidueHigherIndex c.top)
    (hcol : ∀ i, x - col i < (J.val : ℤ)) :
    ∃ R ∈ residueLowerField c.top J.val,
      c.effectiveIncomingCoordinate row col x J =
        residueGenerator c.top ⟨J.val, ne_of_gt J.prop⟩ + R := by
  let M := vertexBetaMatrix c.residueMap row col
  let r := fun i => c.residueMap (hh (x - col i))
  let s := fun i => c.residueMap (hh (row i - (x - (J.val : ℤ))))
  have hr (i) : r i ∈ residueLowerField c.top J.val :=
    c.residue_hh_mem_lower J.val J.prop _ (hcol i)
  have hs (i) : s i ∈ residueLowerField c.top J.val := by
    apply c.residue_hh_mem_lower J.val J.prop
    have h := hrow i
    omega
  have hM (i j) : M i j ∈ residueLowerField c.top J.val := by
    apply c.residue_hh_mem_lower J.val J.prop
    have hi := hrow i
    have hj := hcol j
    omega
  have hcorr := inverseContraction_mem_subfield (residueLowerField c.top J.val) r s M hr hs hM
  refine ⟨-inverseContraction r s M, (residueLowerField c.top J.val).neg_mem hcorr, ?_⟩
  change _ - inverseContraction r s M = _ + -inverseContraction r s M
  exact sub_eq_add_neg _ _

/-- The effective coordinate is formed from its literal original column. -/
theorem effective_incoming_original_coordinate {ν : Type*}
    [Fintype ν] [DecidableEq ν] (row col : ν → ℤ) (x C : ℤ)
    [Invertible (vertexBetaMatrix c.residueMap row col)]
    (J : ResidueHigherIndex c.top) (hJ : x - C = (J.val : ℤ)) :
    c.residueMap (hh (x - C)) -
      inverseContraction (fun i => c.residueMap (hh (x - col i)))
        (fun i => c.residueMap (hh (row i - C))) (vertexBetaMatrix c.residueMap row col) =
      c.effectiveIncomingCoordinate row col x J := by
  have hC : C = x - (J.val : ℤ) := by omega
  rw [hC, effectiveIncomingCoordinate, sub_sub_cancel, hh_pnat,
    c.residueMap_other J.val (ne_of_gt J.prop)]
  rfl

/-- Equal complete effective-coordinate inventories recover their finite
original column-index sets. The prefix may contain arbitrary full nonrow units. -/
theorem effective_incoming_support_eq {ν ι κ : Type*}
    [Fintype ν] [DecidableEq ν] [Fintype ι] [Fintype κ]
    (row col : ν → ℤ) (x : ℤ) [Invertible (vertexBetaMatrix c.residueMap row col)]
    (hrow : ∀ i, row i < x)
    (left : ι → ResidueHigherIndex c.top) (right : κ → ResidueHigherIndex c.top)
    (hleft : Function.Injective left) (hright : Function.Injective right)
    (hcolsLeft : ∀ i j, x - col j < ((left i).val : ℤ))
    (hcolsRight : ∀ i j, x - col j < ((right i).val : ℤ))
    (a : ι → residueLowerField c.top c.top) (b : κ → residueLowerField c.top c.top)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ j, b j ≠ 0)
    (hvalue : (∑ i, (a i : OtherField c.top) * c.effectiveIncomingCoordinate row col x (left i)) =
      ∑ j, (b j : OtherField c.top) * c.effectiveIncomingCoordinate row col x (right j)) :
    Finset.univ.image left = Finset.univ.image right := by
  apply c.triangular_higher_linear_support_eq (c.effectiveIncomingCoordinate row col x)
    left right ?_ hleft hright a b ha hb hvalue
  intro J hJ
  rcases Finset.mem_union.mp hJ with hJ | hJ
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hJ
    exact c.effective_incoming_triangular row col x hrow (left i) (hcolsLeft i)
  · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hJ
    exact c.effective_incoming_triangular row col x hrow (right j) (hcolsRight j)

end SkewCornerDescent.Matrix.SelectedCoordinate
