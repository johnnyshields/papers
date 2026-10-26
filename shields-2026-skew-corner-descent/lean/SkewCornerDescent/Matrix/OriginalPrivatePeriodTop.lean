/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalAmalgamationGapPeriod

/-!
# The actual private-period interval has the true cap-splice top

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
Completed gap periodicity identifies a period-boundary internal gap with the
actual final cap splice. Both true cap tops remain, including their coincident
case. No interval-top equality is assumed. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The actual diagonal at the original period boundary has top equal to the
sum of the two true exterior cap tops. Counts and the complete gap period are
the standing periodic source data, not an assumed response or cap match. -/
theorem originalPrivatePeriod_top_eq_cap_sum {n : ℕ} (P : Profile n)
    [NeZero (originalSelectedCount (hD := hD) P)] (a b r : ℕ) [NeZero r]
    (ha : 0 < a) (hab : a < b)
    (hcount : originalSelectedCount (hD := hD) P = r * b)
    (hgap : Function.Periodic
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x))
      (r : ZMod (originalSelectedCount (hD := hD) P))) :
    let i : Fin (originalSelectedCount (hD := hD) P) :=
      ⟨r * (b - a) - 1, by
        have hlt := Nat.mul_lt_mul_of_pos_left (show b - a < b by omega) (NeZero.pos r)
        omega⟩
    originalHessenbergDistance (hD := hD) P i.succ i.succ =
      originalHessenbergDistance (hD := hD) P 0 0 +
        originalHessenbergDistance (hD := hD) P (Fin.last _) (Fin.last _) := by
  have hrpos := NeZero.pos r
  have hbpos : 0 < b := by omega
  have hcutpos : 0 < r * (b - a) := Nat.mul_pos hrpos (by omega)
  have htotalpos : 0 < r * b := Nat.mul_pos hrpos hbpos
  have hcutlt : r * (b - a) < r * b :=
    Nat.mul_lt_mul_of_pos_left (by omega) hrpos
  have hrle : r ≤ originalSelectedCount (hD := hD) P := by
    rw [hcount]
    exact Nat.le_mul_of_pos_right r hbpos
  let i : Fin (originalSelectedCount (hD := hD) P) := ⟨r * (b - a) - 1, by omega⟩
  let last : Fin (originalSelectedCount (hD := hD) P) :=
    ⟨originalSelectedCount (hD := hD) P - 1, by omega⟩
  have hcast : (i.val : ZMod r) = (last.val : ZMod r) := by
    change ((r * (b - a) - 1 : ℕ) : ZMod r) =
      ((originalSelectedCount (hD := hD) P - 1 : ℕ) : ZMod r)
    rw [hcount, Nat.cast_sub (by omega), Nat.cast_sub (by omega),
      Nat.cast_mul, Nat.cast_mul, ZMod.natCast_self, zero_mul, zero_mul]
  have hsame : c.originalCompletedGap P i = c.originalCompletedGap P last := by
    rw [c.originalCompletedGap_period_cycle P r hrle hgap i,
      c.originalCompletedGap_period_cycle P r hrle hgap last, hcast]
  have hiinternal : i.val + 1 ≠ originalSelectedCount (hD := hD) P := by
    dsimp only [i]
    omega
  have hlast : last.val + 1 = originalSelectedCount (hD := hD) P := by
    dsimp only [last]
    omega
  dsimp only
  unfold originalCompletedGap at hsame
  rw [ite_eq_right hiinternal, ite_eq_left hlast] at hsame
  change originalHessenbergDistance (hD := hD) P i.succ i.succ = _
  omega

end SkewCornerDescent.Matrix.SelectedCoordinate
