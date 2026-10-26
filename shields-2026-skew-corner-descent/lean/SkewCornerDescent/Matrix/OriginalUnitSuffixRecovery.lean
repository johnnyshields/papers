/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalVisibleUnitExtremeValues
import SkewCornerDescent.Matrix.EndpointInverseTransport
import SkewCornerDescent.Matrix.OrderedComponentRowRecovery
import SkewCornerDescent.Matrix.OriginalIntervalOutgoingLocality
import SkewCornerDescent.Matrix.OriginalUnitNormalizedLists

/-!
# Original unit-component suffix recovery

Formalizes `shields-2026-skew-corner-descent.tex`, `lem:early-recovery`.
A paired suffix and the actual extreme outgoing value recover the opposite
row list.  The suffix remains an explicit ordered-induction input.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- A reconstructed paired suffix and the source-produced extreme outgoing
value recover every original row of the current full unit component.
The suffix copy is the geometric input of the ordered reconstruction step. -/
theorem original_unit_rows_of_suffix_copy {n m : ℕ} (P : Profile n) (Q : Profile m)
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
    (e : OriginalIntervalUnitSuffix (hD := hD) P (some a) (some b) u ≃
      OriginalIntervalUnitSuffix (hD := hD) Q (some a') (some b') v)
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
      ((vertexBetaMatrix c.residueMap rowP colP)⁻¹ * vertexIncoming c.residueMap rowP
        (P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some b)))))
          (originalIntervalUnitIndex P (some a) (some b) u hu huint (Fin.last _)) () =
      ((vertexBetaMatrix c.residueMap rowQ colQ)⁻¹ * vertexIncoming c.residueMap rowQ
        (Q.zeta (originalColSplitEquiv (hD := hD) Q (.inl (some b')))))
          (originalIntervalUnitIndex Q (some a') (some b') v hv hvint (Fin.last _)) ()) :
    originalUnitRowDistances P a u = originalUnitRowDistances Q a' v := by
  classical
  let U := interiorBlockProfile P u.val hune
  let V := interiorBlockProfile Q v.val hvne
  let ν := OriginalIntervalUnitSuffix (hD := hD) P (some a) (some b) u
  let μ := OriginalIntervalUnitSuffix (hD := hD) Q (some a') (some b') v
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
  let := c.originalIntervalUnitSuffixInverse P (some a) (some b) u
  have hUP := original_unit_component_schur_ne P u hu hune
  have hVQ := original_unit_component_schur_ne Q v hv hvne
  have hspanP := c.original_unit_component_top_le P u hu hune hmaxP
  have hspanQ := c.original_unit_component_top_le Q v hv hvne hmaxQ
  have hcol (k : ν) : y < col k := originalResponse_col_gt P (some b) k.1.1.1 k.1.1.2
  have hsepP (k : ν) (i : Fin (interiorBlockLength P u.val + 1)) : row k < U.zeta i + τ :=
    original_interval_unit_suffix_separation P (some a) (some b) u hu hune i k
  have hsepQ (k : ν) (i : Fin (interiorBlockLength Q v.val + 1)) : row k < V.zeta i + υ := by
    have hs := original_interval_unit_suffix_separation Q (some a') (some b') v hv hvne i (e k)
    have hr' : row' (e k) = row k + shift := hr k
    change row' (e k) < V.zeta i + originalComponentTau Q v at hs
    dsimp only [υ]
    omega
  have hhighP (i : Fin (interiorBlockLength P u.val + 1)) :
      (c.top : ℤ) < U.xi i + τ - y := by
    have hh := c.original_interval_nonselected_col_high P (some a) b
      (originalIntervalUnitIndex P (some a) (some b) u hu huint i) hu
    change (c.top : ℤ) <
      P.zeta (originalRemovedCol P u (originalUnitIndex P u hu i)).castSucc - y at hh
    rw [(original_unit_component_beta P u hu hune i).2] at hh
    change (c.top : ℤ) < U.zeta i + τ - y at hh
    have hp := U.r_pos i
    have he := U.xi_sub_zeta i
    omega
  have hhighQ (i : Fin (interiorBlockLength Q v.val + 1)) :
      (c.top : ℤ) < V.xi i + υ - y := by
    have hh := c.original_interval_nonselected_col_high Q (some a') b'
      (originalIntervalUnitIndex Q (some a') (some b') v hv hvint i) hv
    change (c.top : ℤ) <
      Q.zeta (originalRemovedCol Q v (originalUnitIndex Q v hv i)).castSucc - y' at hh
    rw [(original_unit_component_beta Q v hv hvne i).2] at hh
    change (c.top : ℤ) < V.zeta i + originalComponentTau Q v - y' at hh
    have hp := V.r_pos i
    have he := V.xi_sub_zeta i
    change x - y = x' - y' at hheight
    dsimp only [υ, shift]
    omega
  let E := Equiv.sumCongr (Equiv.refl (Fin (interiorBlockLength Q v.val + 1))) e
  let row0 := Sum.elim (fun i => V.xi i + υ) row
  let col0 := Sum.elim (fun i => V.zeta i + υ) col
  let row1 := Sum.elim (fun i => V.xi i + originalComponentTau Q v) row'
  let col1 := Sum.elim (fun i => V.zeta i + originalComponentTau Q v) col'
  have hrE (s) : row1 (E s) = row0 s + shift := by
    cases s with
    | inl i => change V.xi i + _ = (V.xi i + υ) + shift; dsimp only [υ]; omega
    | inr k => exact hr k
  have hcE (s) : col1 (E s) = col0 s + shift := by
    cases s with
    | inl i => change V.zeta i + _ = (V.zeta i + υ) + shift; dsimp only [υ]; omega
    | inr k => exact hc k
  have htransport := vertex_incoming_inverse_affine_copy c.residueMap E row0 col0 row1 col1
    y shift hrE hcE (.inl (Fin.last _))
  have hy : y + shift = y' := by change x - y = x' - y' at hheight; dsimp only [shift]; omega
  rw [hy] at htransport
  change ((vertexBetaMatrix c.residueMap row1 col1)⁻¹ * vertexIncoming c.residueMap row1 y')
      (.inl (Fin.last _)) () =
    ((vertexBetaMatrix c.residueMap row0 col0)⁻¹ * vertexIncoming c.residueMap row0 y)
      (.inl (Fin.last _)) () at htransport
  have hval := hvalue
  dsimp only at hval
  rw [c.original_interval_outgoing_suffix_value P (some a) (some b) u hu hune huint y
      (Fin.last _),
    c.original_interval_outgoing_suffix_value Q (some a') (some b') v hv hvne hvint y'
      (Fin.last _)] at hval
  change ((vertexBetaMatrix c.residueMap (Sum.elim (fun i => U.xi i + τ) row)
      (Sum.elim (fun i => U.zeta i + τ) col))⁻¹ *
      vertexIncoming c.residueMap (Sum.elim (fun i => U.xi i + τ) row) y)
        (.inl (Fin.last _)) () =
    ((vertexBetaMatrix c.residueMap row1 col1)⁻¹ * vertexIncoming c.residueMap row1 y')
      (.inl (Fin.last _)) () at hval
  rw [htransport] at hval
  have hrows := c.ordered_component_extreme_outgoing_rows_eq U V hUP hVQ hspanP hspanQ
    row col y τ υ hcol hsepP hsepQ hhighP hhighQ (by
      simpa only [Matrix.invOf_eq_nonsing_inv] using hval)
  have hri := congrArg (Finset.image (fun z : ℤ => x - z)) hrows
  simp only [Finset.image_image, Function.comp_def] at hri
  have hrframe (i) : x - (V.xi i + υ) = x' - (V.xi i + originalComponentTau Q v) := by
    dsimp only [υ, shift]
    omega
  rw [original_unit_row_distances_normalized P a u hu hune,
    original_unit_row_distances_normalized Q a' v hv hvne]
  change Finset.univ.image (fun i => x - (U.xi i + τ)) =
    Finset.univ.image (fun i => x' - (V.xi i + originalComponentTau Q v))
  simpa only [hrframe] using hri

end SkewCornerDescent.Matrix.SelectedCoordinate
