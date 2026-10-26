/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalVisibleUnitExtremeValues
import SkewCornerDescent.Matrix.EndpointInverseTransport
import SkewCornerDescent.Matrix.OrderedComponentColumnRecovery
import SkewCornerDescent.Matrix.OriginalIntervalIncomingLocality
import SkewCornerDescent.Matrix.OriginalUnitNormalizedLists

/-!
# Original unit-component prefix recovery

Formalizes `shields-2026-skew-corner-descent.tex`, `lem:early-recovery`.
A paired prefix and the actual extreme incoming value recover the opposite
column list.  The prefix remains an explicit ordered-induction input.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- A reconstructed paired prefix and the source-produced extreme incoming
value recover every original column of the current full unit component.
The extreme value is supplied by `original_visible_unit_incoming_extreme`;
the prefix copy is the geometric input of the ordered reconstruction step. -/
theorem original_unit_columns_of_prefix_copy {n m : ℕ} (P : Profile n) (Q : Profile m)
    (a b : OriginalSelectedBlocks (hD := hD) P)
    (a' b' : OriginalSelectedBlocks (hD := hD) Q)
    (u : OriginalBlocks P) (v : OriginalBlocks Q)
    (hu : ¬ originalBlockSelected (hD := hD) P u)
    (hv : ¬ originalBlockSelected (hD := hD) Q v)
    (hune : P.zeta u.val.castSucc < P.xi u.val.succ)
    (hvne : Q.zeta v.val.castSucc < Q.xi v.val.succ)
    (huint : originalResponseLowerCut P (some a) < (interiorBlock P u.val : ℤ) ∧
      (interiorBlock P u.val : ℤ) < originalResponseUpperCut P (some b))
    (hvint : originalResponseLowerCut Q (some a') < (interiorBlock Q v.val : ℤ) ∧
      (interiorBlock Q v.val : ℤ) < originalResponseUpperCut Q (some b'))
    (hmaxP : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (hmaxQ : ∀ C ∈ edgeComponents (diagramInterior Q.cells), span C ≤ (c.top : ℕ))
    (hheight : P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a))) -
        P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some b))) =
      Q.xi (originalRowSplitEquiv (hD := hD) Q (.inl (some a'))) -
        Q.zeta (originalColSplitEquiv (hD := hD) Q (.inl (some b'))))
    (e : OriginalIntervalUnitPrefix (hD := hD) P (some a) (some b) u ≃
      OriginalIntervalUnitPrefix (hD := hD) Q (some a') (some b') v)
    (hr : ∀ k, originalResponseRows Q (e k).1.1.1 = originalResponseRows P k.1.1.1 +
      (Q.xi (originalRowSplitEquiv (hD := hD) Q (.inl (some a'))) -
        P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a)))))
    (hc : ∀ k, originalResponseCols Q (e k).1.1.1 = originalResponseCols P k.1.1.1 +
      (Q.xi (originalRowSplitEquiv (hD := hD) Q (.inl (some a'))) -
        P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a)))))
    (hvalue :
      let rowP := fun k : OriginalResponseInterval (hD := hD) P (some a) (some b) =>
        originalResponseRows P k.1.1
      let colP := fun k : OriginalResponseInterval (hD := hD) P (some a) (some b) =>
        originalResponseCols P k.1.1
      let rowQ := fun k : OriginalResponseInterval (hD := hD) Q (some a') (some b') =>
        originalResponseRows Q k.1.1
      let colQ := fun k : OriginalResponseInterval (hD := hD) Q (some a') (some b') =>
        originalResponseCols Q k.1.1
      (vertexOutgoing c.residueMap colP
          (P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a)))) *
        (vertexBetaMatrix c.residueMap rowP colP)⁻¹)
          () (originalIntervalUnitIndex P (some a) (some b) u hu huint 0) =
      (vertexOutgoing c.residueMap colQ
          (Q.xi (originalRowSplitEquiv (hD := hD) Q (.inl (some a')))) *
        (vertexBetaMatrix c.residueMap rowQ colQ)⁻¹)
          () (originalIntervalUnitIndex Q (some a') (some b') v hv hvint 0)) :
    originalUnitColDistances P b u = originalUnitColDistances Q b' v := by
  classical
  let U := interiorBlockProfile P u.val hune
  let V := interiorBlockProfile Q v.val hvne
  let ν := OriginalIntervalUnitPrefix (hD := hD) P (some a) (some b) u
  let μ := OriginalIntervalUnitPrefix (hD := hD) Q (some a') (some b') v
  let row := fun k : ν => originalResponseRows P k.1.1.1
  let col := fun k : ν => originalResponseCols P k.1.1.1
  let row' := fun k : μ => originalResponseRows Q k.1.1.1
  let col' := fun k : μ => originalResponseCols Q k.1.1.1
  let x := P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a)))
  let x' := Q.xi (originalRowSplitEquiv (hD := hD) Q (.inl (some a')))
  let y := P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some b)))
  let y' := Q.zeta (originalColSplitEquiv (hD := hD) Q (.inl (some b')))
  let shift := x' - x
  let τ := originalComponentTau P u
  let υ := originalComponentTau Q v - shift
  let := c.originalIntervalUnitPrefixInverse P (some a) (some b) u
  have hUP := original_unit_component_schur_ne P u hu hune
  have hVQ := original_unit_component_schur_ne Q v hv hvne
  have hspanP := c.original_unit_component_top_le P u hu hune hmaxP
  have hspanQ := c.original_unit_component_top_le Q v hv hvne hmaxQ
  have hrow (k : ν) : row k < x := originalResponse_row_lt P (some a) k.1.1.1 k.1.2
  have hsepP (i : Fin (interiorBlockLength P u.val + 1)) (k : ν) : U.xi i + τ < col k :=
    original_interval_unit_prefix_separation P (some a) (some b) u hu hune i k
  have hsepQ (i : Fin (interiorBlockLength Q v.val + 1)) (k : ν) : V.xi i + υ < col k := by
    have hs := original_interval_unit_prefix_separation Q (some a') (some b') v hv hvne i (e k)
    have hc' : col' (e k) = col k + shift := hc k
    change V.xi i + originalComponentTau Q v < col' (e k) at hs
    dsimp only [υ]
    omega
  have hhighP (i : Fin (interiorBlockLength P u.val + 1)) :
      (c.top : ℤ) < x - (U.zeta i + τ) := by
    have hh := c.original_interval_nonselected_row_high P a (some b)
      (originalIntervalUnitIndex P (some a) (some b) u hu huint i) hu
    change (c.top : ℤ) < x - P.xi (originalRemovedRow P u (originalUnitIndex P u hu i)).succ at hh
    rw [(original_unit_component_beta P u hu hune i).1] at hh
    change (c.top : ℤ) < x - (U.xi i + τ) at hh
    have hp := U.r_pos i
    have he := U.xi_sub_zeta i
    omega
  have hhighQ (i : Fin (interiorBlockLength Q v.val + 1)) :
      (c.top : ℤ) < x - (V.zeta i + υ) := by
    have hh := c.original_interval_nonselected_row_high Q a' (some b')
      (originalIntervalUnitIndex Q (some a') (some b') v hv hvint i) hv
    change (c.top : ℤ) < x' - Q.xi (originalRemovedRow Q v (originalUnitIndex Q v hv i)).succ at hh
    rw [(original_unit_component_beta Q v hv hvne i).1] at hh
    change (c.top : ℤ) < x' - (V.xi i + originalComponentTau Q v) at hh
    have hp := V.r_pos i
    have he := V.xi_sub_zeta i
    dsimp only [υ, shift]
    omega
  let E := Equiv.sumCongr e (Equiv.refl (Fin (interiorBlockLength Q v.val + 1)))
  let row0 := Sum.elim row (fun i => V.xi i + υ)
  let col0 := Sum.elim col (fun i => V.zeta i + υ)
  let row1 := Sum.elim row' (fun i => V.xi i + originalComponentTau Q v)
  let col1 := Sum.elim col' (fun i => V.zeta i + originalComponentTau Q v)
  have hrE (s) : row1 (E s) = row0 s + shift := by
    cases s with
    | inl k => exact hr k
    | inr i => change V.xi i + _ = (V.xi i + υ) + shift; dsimp only [υ]; omega
  have hcE (s) : col1 (E s) = col0 s + shift := by
    cases s with
    | inl k => exact hc k
    | inr i => change V.zeta i + _ = (V.zeta i + υ) + shift; dsimp only [υ]; omega
  have htransport := vertex_outgoing_inverse_affine_copy c.residueMap E row0 col0 row1 col1
    x shift hrE hcE (.inr 0)
  have hx : x + shift = x' := by dsimp only [shift]; omega
  rw [hx] at htransport
  change (vertexOutgoing c.residueMap col1 x' * (vertexBetaMatrix c.residueMap row1 col1)⁻¹)
      () (.inr 0) =
    (vertexOutgoing c.residueMap col0 x * (vertexBetaMatrix c.residueMap row0 col0)⁻¹)
      () (.inr 0) at htransport
  have hval := hvalue
  dsimp only at hval
  rw [c.original_interval_incoming_prefix_value P (some a) (some b) u hu hune huint x 0,
    c.original_interval_incoming_prefix_value Q (some a') (some b') v hv hvne hvint x' 0] at hval
  change (vertexOutgoing c.residueMap (Sum.elim col (fun i => U.zeta i + τ)) x *
      (vertexBetaMatrix c.residueMap (Sum.elim row (fun i => U.xi i + τ))
        (Sum.elim col (fun i => U.zeta i + τ)))⁻¹) () (.inr 0) =
    (vertexOutgoing c.residueMap col1 x' * (vertexBetaMatrix c.residueMap row1 col1)⁻¹)
      () (.inr 0) at hval
  rw [htransport] at hval
  have hcols := c.ordered_component_extreme_incoming_columns_eq U V hUP hVQ hspanP hspanQ
    row col x τ υ hrow hsepP hsepQ hhighP hhighQ (by
      simpa only [Matrix.invOf_eq_nonsing_inv] using hval)
  have hci := congrArg (Finset.image (fun z : ℤ => z - y)) hcols
  simp only [Finset.image_image, Function.comp_def] at hci
  have hcframe (i) : V.zeta i + υ - y = V.zeta i + originalComponentTau Q v - y' := by
    change x - y = x' - y' at hheight
    dsimp only [υ, shift]
    omega
  rw [original_unit_col_distances_normalized P b u hu hune,
    original_unit_col_distances_normalized Q b' v hv hvne]
  change Finset.univ.image (fun i => U.zeta i + τ - y) =
    Finset.univ.image (fun i => V.zeta i + originalComponentTau Q v - y')
  simpa only [hcframe] using hci

end SkewCornerDescent.Matrix.SelectedCoordinate
