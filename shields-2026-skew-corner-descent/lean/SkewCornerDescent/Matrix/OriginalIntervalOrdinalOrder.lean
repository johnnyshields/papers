/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/


import SkewCornerDescent.Matrix.OriginalIntervalRowOrdinals

/-!
# Physical row-rank rigidity of complete paired original intervals

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The complete original row beta list is strictly decreasing in its exact
two-pivot row ordinals. A paired beta copy therefore gives a monotone
ordinal equivalence. Equal full row frames force this equivalence to be
the identity by finite linear-order rigidity. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D}

/-- Identical extents and pivot gaps identify the actual two-pivot ordered frames. -/
def twoPivotRowOrderCast {L L' g g' : ℕ} (hL : L = L') (hg : g = g') :
    {k : Fin L // k.val ≠ 0 ∧ k.val ≠ g} ≃o {k : Fin L' // k.val ≠ 0 ∧ k.val ≠ g'} := by
  subst L'
  subst g'
  exact OrderIso.refl _

/-- Frame identification preserves the numerical local row rank. -/
theorem twoPivotRowOrderCast_val {L L' g g' : ℕ} (hL : L = L') (hg : g = g')
    (k : {k : Fin L // k.val ≠ 0 ∧ k.val ≠ g}) :
    (twoPivotRowOrderCast hL hg k).val.val = k.val.val := by
  subst L'
  subst g'
  rfl

/-- The inverse frame identification preserves the numerical local row rank. -/
theorem twoPivotRowOrderCast_symm_val {L L' g g' : ℕ} (hL : L = L') (hg : g = g')
    (k : {k : Fin L' // k.val ≠ 0 ∧ k.val ≠ g'}) :
    ((twoPivotRowOrderCast hL hg).symm k).val.val = k.val.val := by
  subst L'
  subst g'
  rfl

/-- Retained ordinal order is precisely physical original row order. -/
theorem originalInternalRowOrdinal_lt_iff {n : ℕ} (P : Profile n)
    (i : Fin (originalSelectedCount (hD := hD) P - 1)) (r s : OriginalInternalInterval P i) :
    originalInternalRowOrdinal P i r < originalInternalRowOrdinal P i s ↔
      originalRemovedRow P r.val.val.1 r.val.val.2 <
        originalRemovedRow P s.val.val.1 s.val.val.2 := by
  change (originalRemovedRow P r.val.val.1 r.val.val.2).val - originalInternalRowStart P i <
      (originalRemovedRow P s.val.val.1 s.val.val.2).val - originalInternalRowStart P i ↔
    (originalRemovedRow P r.val.val.1 r.val.val.2).val <
      (originalRemovedRow P s.val.val.1 s.val.val.2).val
  have hr := originalInternal_interval_row_bounds P i r
  have hs := originalInternal_interval_row_bounds P i s
  omega

/-- The actual beta coordinate at a local retained row ordinal. -/
noncomputable def originalInternalRowOrdinalBeta {n : ℕ} (P : Profile n)
    (i : Fin (originalSelectedCount (hD := hD) P - 1))
    (k : OriginalInternalRowOrdinal P i) : ℤ :=
  originalResponseRows P ((originalInternalRowOrdinalEquiv P i).symm k).val.val

/-- Original row beta coordinates decrease strictly with the full retained row ordinal. -/
theorem originalInternalRowOrdinalBeta_strictAnti {n : ℕ} (P : Profile n)
    (i : Fin (originalSelectedCount (hD := hD) P - 1)) :
    StrictAnti (originalInternalRowOrdinalBeta (hD := hD) P i) := by
  intro r s hrs
  let E := originalInternalRowOrdinalEquiv (hD := hD) P i
  have hr : originalInternalRowOrdinal P i (E.symm r) = r := E.apply_symm_apply r
  have hs : originalInternalRowOrdinal P i (E.symm s) = s := E.apply_symm_apply s
  have hrow := (originalInternalRowOrdinal_lt_iff P i (E.symm r) (E.symm s)).mp
    (by rw [hr, hs]; exact hrs)
  apply P.xi_strictAnti
  change (originalRemovedRow P (E.symm r).val.val.1 (E.symm r).val.val.2).val + 1 <
    (originalRemovedRow P (E.symm s).val.val.1 (E.symm s).val.val.2).val + 1
  change (originalRemovedRow P (E.symm r).val.val.1 (E.symm r).val.val.2).val <
    (originalRemovedRow P (E.symm s).val.val.1 (E.symm s).val.val.2).val at hrow
  omega

/-- A full original row-beta copy preserves exact local row order. -/
theorem originalInterval_copy_ordinal_strictMono {n m : ℕ} (P : Profile n) (Q : Profile m)
    (i : Fin (originalSelectedCount (hD := hD) P - 1))
    (j : Fin (originalSelectedCount (hD := hD) Q - 1))
    (e : OriginalInternalInterval P i ≃ OriginalInternalInterval Q j) (shift : ℤ)
    (he : ∀ r, originalResponseRows Q (e r).val.val = originalResponseRows P r.val.val + shift) :
    StrictMono (fun k : OriginalInternalRowOrdinal P i =>
      originalInternalRowOrdinalEquiv Q j (e ((originalInternalRowOrdinalEquiv P i).symm k))) := by
  let E := originalInternalRowOrdinalEquiv (hD := hD) P i
  let F := originalInternalRowOrdinalEquiv (hD := hD) Q j
  let f := fun k => F (e (E.symm k))
  have hbeta (k : OriginalInternalRowOrdinal P i) :
      originalInternalRowOrdinalBeta Q j (f k) = originalInternalRowOrdinalBeta P i k + shift := by
    change originalResponseRows Q (F.symm (F (e (E.symm k)))).val.val = _
    rw [Equiv.symm_apply_apply]
    exact he (E.symm k)
  intro a b hab
  have hp := originalInternalRowOrdinalBeta_strictAnti P i hab
  have ha := hbeta a
  have hb := hbeta b
  apply (originalInternalRowOrdinalBeta_strictAnti Q j).lt_iff_gt.mp
  change originalInternalRowOrdinalBeta Q j (f b) < originalInternalRowOrdinalBeta Q j (f a)
  omega

/-- Complete paired row-beta copies on equal frames preserve every physical relative row rank. -/
theorem originalInterval_copy_relative_row_rank {n m : ℕ} (P : Profile n) (Q : Profile m)
    (i : Fin (originalSelectedCount (hD := hD) P - 1))
    (j : Fin (originalSelectedCount (hD := hD) Q - 1))
    (e : OriginalInternalInterval P i ≃ OriginalInternalInterval Q j) (shift : ℤ)
    (he : ∀ r, originalResponseRows Q (e r).val.val = originalResponseRows P r.val.val + shift)
    (hL : originalInternalRowLast P i + 1 - originalInternalRowStart P i =
      originalInternalRowLast Q j + 1 - originalInternalRowStart Q j)
    (hg : originalInternalRowEnd P i - originalInternalRowStart P i =
      originalInternalRowEnd Q j - originalInternalRowStart Q j)
    (r : OriginalInternalInterval P i) :
    (originalRemovedRow Q (e r).val.val.1 (e r).val.val.2).val - originalInternalRowStart Q j =
      (originalRemovedRow P r.val.val.1 r.val.val.2).val - originalInternalRowStart P i := by
  let E := originalInternalRowOrdinalEquiv (hD := hD) P i
  let F := originalInternalRowOrdinalEquiv (hD := hD) Q j
  let T := twoPivotRowOrderCast hL hg
  let f : OriginalInternalRowOrdinal P i → OriginalInternalRowOrdinal P i :=
    fun k => T.symm (F (e (E.symm k)))
  have hf : StrictMono f := T.symm.strictMono.comp
    (originalInterval_copy_ordinal_strictMono P Q i j e shift he)
  have hid := congrFun hf.eq_id (E r)
  have hv := congrArg (fun k => k.val.val) hid
  change (T.symm (F (e (E.symm (E r))))).val.val = (E r).val.val at hv
  rw [Equiv.symm_apply_apply] at hv
  rw [twoPivotRowOrderCast_symm_val] at hv
  exact hv

end SkewCornerDescent.Matrix.SelectedCoordinate
