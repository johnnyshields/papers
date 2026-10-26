/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalRemainingOrder
import SkewCornerDescent.Matrix.OriginalIntervalProfileBands

/-!
# Original block order inside selected-end intervals

Formalizes `shields-2026-skew-corner-descent.tex`, `lem:early-recovery`.
Actual interval cuts put each full unit strictly between the selected endpoints
and retain every initial proper-strip point.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D}

/-- A nonselected component in an actual selected-end interval lies strictly
between its selected endpoints in the original source order. -/
theorem original_interval_unit_between {n : ℕ} (P : Profile n)
    (a b : OriginalSelectedBlocks (hD := hD) P) (u : OriginalBlocks P)
    (hu : ¬ originalBlockSelected (hD := hD) P u)
    (hint : originalResponseLowerCut P (some a) < (interiorBlock P u.val : ℤ) ∧
      (interiorBlock P u.val : ℤ) < originalResponseUpperCut P (some b)) :
    a.val < u ∧ u < b.val := by
  have ha : interiorBlock P a.val.val ≠ interiorBlock P u.val := by
    intro h
    have he := (originalBlocks_label_strictMono P).injective h
    exact hu (he ▸ a.property)
  have hb : interiorBlock P u.val ≠ interiorBlock P b.val.val := by
    intro h
    have he := (originalBlocks_label_strictMono P).injective h
    exact hu (he.symm ▸ b.property)
  change (interiorBlock P a.val.val : ℤ) - 1 < (interiorBlock P u.val : ℤ) ∧
    (interiorBlock P u.val : ℤ) < (interiorBlock P b.val.val : ℤ) + 1 at hint
  constructor
  · exact (originalBlocks_label_strictMono P).lt_iff_lt.mp (by omega)
  · exact (originalBlocks_label_strictMono P).lt_iff_lt.mp (by omega)

/-- Every retained initial proper-strip point is a genuine index of the
selected-end interval; no full-matrix pivot is reinserted. -/
def originalSelectedStartIntervalIndex {n : ℕ} (P : Profile n)
    (a b : OriginalSelectedBlocks (hD := hD) P)
    (hab : interiorBlock P a.val.val ≤ interiorBlock P b.val.val)
    (k : Fin (originalRemovedSize (hD := hD) P a.val)) :
    OriginalResponseInterval (hD := hD) P (some a) (some b) := by
  refine ⟨⟨⟨a.val, k⟩, ?_⟩, ?_⟩
  · change (interiorBlock P a.val.val : ℤ) < (interiorBlock P b.val.val : ℤ) + 1
    omega
  · change (interiorBlock P a.val.val : ℤ) - 1 < (interiorBlock P a.val.val : ℤ)
    omega

/-- Every retained terminal proper-strip point is a genuine interval index. -/
def originalSelectedEndIntervalIndex {n : ℕ} (P : Profile n)
    (a b : OriginalSelectedBlocks (hD := hD) P)
    (hab : interiorBlock P a.val.val ≤ interiorBlock P b.val.val)
    (k : Fin (originalRemovedSize (hD := hD) P b.val)) :
    OriginalResponseInterval (hD := hD) P (some a) (some b) := by
  refine ⟨⟨⟨b.val, k⟩, ?_⟩, ?_⟩
  · change (interiorBlock P b.val.val : ℤ) < (interiorBlock P b.val.val : ℤ) + 1
    omega
  · change (interiorBlock P a.val.val : ℤ) - 1 < (interiorBlock P b.val.val : ℤ)
    omega

/-- Consecutive selected enumeration gives the exact source-label order used
by the component and proper-strip reconstruction steps. -/
theorem original_consecutive_endpoint_label_le {n : ℕ} (P : Profile n)
    (i t : Fin (originalSelectedCount (hD := hD) P)) (ht : t.val = i.val + 1) :
    interiorBlock P (originalSelectedEnumeration (hD := hD) P i).val.val ≤
      interiorBlock P (originalSelectedEnumeration (hD := hD) P t).val.val := by
  exact (originalSelectedEnumeration_label_strictMono P (show i < t by omega)).le

end SkewCornerDescent.Matrix.SelectedCoordinate
