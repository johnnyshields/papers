/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalRationalClassTransfer

/-!
# Constructing the paper's protected original indices

Supports `shields-2026-skew-corner-descent.tex` (`lem:original-transfer`). Actual
positive completed gaps produce the protected top and its strict separation from
the selected generator. No numerical cutoff assumption is introduced. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The original period increment, retaining each actual cyclic position. -/
noncomputable def originalPeriodIncrement {n : ℕ} (P : Profile n)
    [NeZero (originalSelectedCount (hD := hD) P)] (r : ℕ) : ℤ :=
  windowSum (fun z => c.originalCompletedGap P ((ZMod.finEquiv _).symm z)) 1 r 0

/-- Nonnegative period sums are produced from the actual positive gap geometry. -/
theorem originalPeriodIncrement_nonneg {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    [NeZero (originalSelectedCount (hD := hD) P)] (r : ℕ) :
    0 ≤ c.originalPeriodIncrement P r := by
  unfold originalPeriodIncrement windowSum
  apply Finset.sum_nonneg
  intro i _
  exact (c.originalCompletedGap_pos P hB _).le

/-- A nonempty period has strictly positive actual increment. -/
theorem originalPeriodIncrement_pos {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    [NeZero (originalSelectedCount (hD := hD) P)] (r : ℕ) (hr : 0 < r) :
    0 < c.originalPeriodIncrement P r := by
  unfold originalPeriodIncrement windowSum
  apply Finset.sum_pos
  · intro i _
    exact c.originalCompletedGap_pos P hB _
  · exact ⟨0, Finset.mem_range.mpr hr⟩

/-- The actual source width equals its number of periods times the produced
increment. This identifies the increment used in the paper's protected indices. -/
theorem originalPeriodIncrement_span {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    [NeZero (originalSelectedCount (hD := hD) P)] (r b : ℕ)
    (hcount : originalSelectedCount (hD := hD) P = b * r)
    (hp : Function.Periodic
      (fun z => c.originalCompletedGap P ((ZMod.finEquiv _).symm z))
      (r : ZMod (originalSelectedCount (hD := hD) P))) :
    P.xi 0 - P.zeta (Fin.last n) = (b : ℤ) * c.originalPeriodIncrement P r := by
  let f := fun z => c.originalCompletedGap P ((ZMod.finEquiv _).symm z)
  have he := (ZMod.finEquiv (originalSelectedCount (hD := hD) P)).toEquiv.sum_comp f
  change (∑ i, c.originalCompletedGap P
    ((ZMod.finEquiv _).symm ((ZMod.finEquiv _) i))) = ∑ z, f z at he
  simp only [RingEquiv.symm_apply_apply] at he
  have hsum : ∑ z, f z = P.xi 0 - P.zeta (Fin.last n) := by
    rw [← he]
    exact c.originalCompletedGap_sum P hB
  have hw := zmod_windowSum_cycle f 0
  have hn := congrArg (fun length => windowSum f 1 length 0) hcount
  rw [hn, windowSum_of_zmod_period_multiple f r hp b 0, hsum, nsmul_eq_mul] at hw
  exact hw.symm

/-- A genuine original protected top, constructed from the actual period sum. -/
noncomputable def originalCyclicTop {n : ℕ} (P : Profile n)
    [NeZero (originalSelectedCount (hD := hD) P)] (r k : ℕ) : ℕ+ :=
  ⟨(c.top : ℕ) + k * (c.originalPeriodIncrement P r).toNat, by have := c.top.pos; omega⟩

/-- The constructed index has the exact integer formula in the paper. -/
theorem originalCyclicTop_coe {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    [NeZero (originalSelectedCount (hD := hD) P)] (r k : ℕ) :
    (c.originalCyclicTop P r k : ℤ) = (c.top : ℤ) + k • c.originalPeriodIncrement P r := by
  have hδ := c.originalPeriodIncrement_nonneg P hB r
  change (((c.top : ℕ) + k * (c.originalPeriodIncrement P r).toNat : ℕ) : ℤ) =
    (c.top : ℤ) + k • c.originalPeriodIncrement P r
  rw [Nat.cast_add, Nat.cast_mul, Int.toNat_of_nonneg hδ, nsmul_eq_mul]

/-- Positive multiples give an original surviving generator strictly above the
selected top. The inequality is supplied, not carried as a separate hypothesis. -/
theorem originalCyclicTop_gt {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    [NeZero (originalSelectedCount (hD := hD) P)] (r k : ℕ) (hr : 0 < r) (hk : 0 < k) :
    c.top < c.originalCyclicTop P r k := by
  have hδ := c.originalPeriodIncrement_pos P hB r hr
  have hco := c.originalCyclicTop_coe P hB r k
  have hk' : 0 < (k : ℤ) := by exact_mod_cast hk
  have hp := mul_pos hk' hδ
  simp only [nsmul_eq_mul] at hco
  exact_mod_cast (show (c.top : ℤ) < (c.originalCyclicTop P r k : ℤ) by omega)

end SkewCornerDescent.Matrix.SelectedCoordinate
