/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalInverseProjectionSpan
import SkewCornerDescent.Matrix.OriginalCoreProductJets

/-!
# Actual inverse projections have their source proper-core weights

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
The complete inverse's geometric entry-span bound limits contributing profile
offsets to the source-selected proper-core jets. The full inverse is retained;
only endpoint weights are replaced, through their proved original bridges.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

private theorem coeff_toLaurent_nat {F : Type*} [CommRing F] (P : Polynomial F) (k : ℕ) :
    P.toLaurent.coeff (k : ℤ) = P.coeff k := by
  change (Finsupp.mapDomain (fun x : ℕ => (x : ℤ)) P.toFinsupp.coeff) (k : ℤ) = _
  exact Finsupp.mapDomain_apply_of_injective Nat.cast_injective _ k

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Complete original interval projections have the proper cores of their own
selected endpoint components as weights. All inverse entries and nonrow unit
blocks remain. The source produces every low-jet and entry-span premise. -/
theorem original_interval_projection_proper_cores {n : ℕ} (P : Profile n)
    (b d : OriginalSelectedBlocks (hD := hD) P)
    (horder : interiorBlock P b.val.val ≤ interiorBlock P d.val.val)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ)) (z : ℤ) :
    letI := c.originalResponseResidueIntervalInverse P (some b) (some d)
    let row := fun i : OriginalResponseInterval (hD := hD) P (some b) (some d) =>
      originalResponseRows P i.1.1
    let col := fun i : OriginalResponseInterval (hD := hD) P (some b) (some d) =>
      originalResponseCols P i.1.1
    let x := P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some b)))
    let y := P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some d)))
    let I := ⅟(vertexBetaMatrix c.residueMap row col)
    let B := vertexOutgoing c.residueMap col x
    let C := vertexIncoming c.residueMap row y
    let A := endpointProfile (fun i => x - row i) (fun i => (B * I) () i)
    let T := endpointProfile (fun i => col i - y) (fun i => (I * C) i ())
    let Qb := interiorBlockProfile P b.val.val (originalBlockSelected_nonempty P b.val b.property)
    let Qd := interiorBlockProfile P d.val.val (originalBlockSelected_nonempty P d.val d.property)
    profileInverseProjection row col I A T z = profileInverseProjection row col I
      (c.selectedCoreLeftPolynomial Qb (originalSelectedProfile_schur P b).symm).toLaurent
      (c.selectedCoreRightPolynomial Qd (originalSelectedProfile_schur P d).symm).toLaurent z := by
  let := c.originalResponseResidueIntervalInverse P (some b) (some d)
  let row := fun i : OriginalResponseInterval (hD := hD) P (some b) (some d) =>
    originalResponseRows P i.1.1
  let col := fun i : OriginalResponseInterval (hD := hD) P (some b) (some d) =>
    originalResponseCols P i.1.1
  let x := P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some b)))
  let y := P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some d)))
  let I := ⅟(vertexBetaMatrix c.residueMap row col)
  let A := endpointProfile (fun i => x - row i)
    (fun i => (vertexOutgoing c.residueMap col x * I) () i)
  let T := endpointProfile (fun i => col i - y)
    (fun i => (I * vertexIncoming c.residueMap row y) i ())
  let Qb := interiorBlockProfile P b.val.val (originalBlockSelected_nonempty P b.val b.property)
  let Qd := interiorBlockProfile P d.val.val (originalBlockSelected_nonempty P d.val d.property)
  have hb : cellSchur D hD.1 = Qb.schur := (originalSelectedProfile_schur P b).symm
  have hd : cellSchur D hD.1 = Qd.schur := (originalSelectedProfile_schur P d).symm
  have hr (i) : 0 ≤ x - row i := by
    have h := originalResponse_row_lt P (some b) i.1.1 i.2
    change row i < x at h
    exact sub_nonneg.mpr h.le
  have hc (i) : 0 ≤ col i - y := by
    have h := originalResponse_col_gt P (some d) i.1.1 i.1.2
    change y < col i at h
    exact sub_nonneg.mpr h.le
  have hAf : (c.originalResidueLeftEndpointPolynomial P (some b) (some d)).toLaurent = A :=
    (endpointProfile_eq_toLaurent_of_nonneg _ _ hr).symm
  have hTf : (c.originalResidueRightEndpointPolynomial P (some b) (some d)).toLaurent = T :=
    (endpointProfile_eq_toLaurent_of_nonneg _ _ hc).symm
  have hupper : (interiorBlock P b.val.val : ℤ) < originalResponseUpperCut P (some d) := by
    change (interiorBlock P b.val.val : ℤ) < (interiorBlock P d.val.val : ℤ) + 1
    omega
  have hlower : originalResponseLowerCut P (some b) < (interiorBlock P d.val.val : ℤ) := by
    change (interiorBlock P b.val.val : ℤ) - 1 < (interiorBlock P d.val.val : ℤ)
    omega
  dsimp only
  apply profile_inverse_projection_low_jets row col I (c.top : ℤ)
    (c.original_interval_inverse_entry_span P (some b) (some d) (c.top : ℕ) hmax)
  · intro k hk
    exact endpointProfile_coeff_negative _ _ hr k hk
  · intro k hk
    exact endpointProfile_coeff_negative _ _ hc k hk
  · intro k hk
    rw [c.selected_core_left_toLaurent Qb hb]
    exact endpointProfile_coeff_negative _ _
      (fun i => (c.selected_core_left_distances Qb hb i).1.le) k hk
  · intro k hk
    rw [c.selected_core_right_toLaurent Qd hd]
    exact endpointProfile_coeff_negative _ _
      (fun i => (c.selected_core_right_distances Qd hd i).1.le) k hk
  · intro k hk hkN
    let m := k.toNat
    have hm : (m : ℤ) = k := Int.toNat_of_nonneg hk
    have hmN : m ≤ (c.top : ℕ) := by omega
    change A.coeff k = (c.selectedCoreLeftPolynomial Qb hb).toLaurent.coeff k
    rw [← hAf, ← hm, coeff_toLaurent_nat, coeff_toLaurent_nat]
    exact c.original_left_profile_low_core P b (some d) hupper m hmN
  · intro k hk hkN
    let m := k.toNat
    have hm : (m : ℤ) = k := Int.toNat_of_nonneg hk
    have hmN : m ≤ (c.top : ℕ) := by omega
    change T.coeff k = (c.selectedCoreRightPolynomial Qd hd).toLaurent.coeff k
    rw [← hTf, ← hm, coeff_toLaurent_nat, coeff_toLaurent_nat]
    exact c.original_right_profile_low_core P (some b) d hlower m hmN

end SkewCornerDescent.Matrix.SelectedCoordinate
