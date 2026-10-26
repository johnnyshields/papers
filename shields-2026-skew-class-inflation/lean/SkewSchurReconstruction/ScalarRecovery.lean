/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
-- TODO-COPIED: skew-boundary-reconstruction/lean/SkewSchurReconstruction/ScalarRecovery.lean

import SkewSchurReconstruction.Diagrams

/-!
# Geometric exchange moments and scalar recovery

Formalizes the geometric exchange and scalar algebra of `prop:stable-cofactor`
and `eq:scalar-recovery` in "Reconstruction from two boundary observations"
(`sec:reconstruction`).  These are moments of the increasing coordinate matchings;
this module does not identify them with determinant degrees or valuations.
Their full profiles recover ordered row lengths and overlaps, hence translation
classes of connected diagrams.  Sorry-free.
-/

namespace SkewSchurReconstruction
namespace Diagram

open scoped BigOperators

variable {n : ℕ}

/-- Subscript of the increasing matching after deleting cap column `j`. -/
def peelIndex (X : Diagram n) (j : Fin (n + 1)) (i : Fin n) : ℤ :=
  X.capShift (j.succAbove i) - X.rowParam i

/-- First geometric moment of the increasing matching. -/
def peelDegree (X : Diagram n) (j : Fin (n + 1)) : ℤ := ∑ i, X.peelIndex j i

/-- Second geometric moment of the increasing matching. -/
def peelSquare (X : Diagram n) (j : Fin (n + 1)) : ℤ := ∑ i, (X.peelIndex j i) ^ 2

/-- The row-length subscript removed by the adjacent exchange. -/
def exchangeRow (X : Diagram n) (j : Fin n) : ℤ := X.capShift j.succ - X.rowParam j

/-- The subscript inserted by the adjacent exchange. -/
def exchangeZero (X : Diagram n) (j : Fin n) : ℤ := X.capShift j.castSucc - X.rowParam j

/-- Degree drop between adjacent geometric matching profiles. -/
def degreeDrop (X : Diagram n) (j : Fin n) : ℤ :=
  X.peelDegree j.castSucc - X.peelDegree j.succ

/-- Square-moment drop between adjacent geometric matching profiles. -/
def squareDrop (X : Diagram n) (j : Fin n) : ℤ :=
  X.peelSquare j.castSucc - X.peelSquare j.succ

theorem peelIndex_adjacent_eq (X : Diagram n) (j i : Fin n) (hij : i ≠ j) :
    X.peelIndex j.castSucc i = X.peelIndex j.succ i := by
  rcases lt_or_gt_of_ne hij with h | h
  · simp [peelIndex, Fin.succAbove_castSucc_of_lt _ _ h,
      Fin.succAbove_succ_of_le _ _ h.le]
  · simp [peelIndex, Fin.succAbove_castSucc_of_le _ _ h.le,
      Fin.succAbove_succ_of_lt _ _ h]

@[simp] theorem peelIndex_castSucc_self (X : Diagram n) (j : Fin n) :
    X.peelIndex j.castSucc j = X.exchangeRow j := by
  simp [peelIndex, exchangeRow]

@[simp] theorem peelIndex_succ_self (X : Diagram n) (j : Fin n) :
    X.peelIndex j.succ j = X.exchangeZero j := by
  simp [peelIndex, exchangeZero]

/-- Adjacent omission matchings exchange exactly one subscript. -/
theorem peel_sum_exchange (X : Diagram n) (j : Fin n) (F : ℤ → ℤ) :
    (∑ i, F (X.peelIndex j.castSucc i)) - (∑ i, F (X.peelIndex j.succ i)) =
      F (X.exchangeRow j) - F (X.exchangeZero j) := by
  classical
  rw [← Finset.sum_sub_distrib]
  have he : ∀ i : Fin n,
      F (X.peelIndex j.castSucc i) - F (X.peelIndex j.succ i) =
        if i = j then F (X.exchangeRow j) - F (X.exchangeZero j) else 0 := by
    intro i
    by_cases hi : i = j
    · subst i
      simp
    · simp [hi, X.peelIndex_adjacent_eq j i hi]
  simp_rw [he]
  simp

theorem degreeDrop_eq_exchange (X : Diagram n) (j : Fin n) :
    X.degreeDrop j = X.exchangeRow j - X.exchangeZero j :=
  X.peel_sum_exchange j id

theorem squareDrop_eq_exchange (X : Diagram n) (j : Fin n) :
    X.squareDrop j = (X.exchangeRow j) ^ 2 - (X.exchangeZero j) ^ 2 :=
  X.peel_sum_exchange j (fun a => a ^ 2)

theorem degreeDrop_eq_grid (X : Diagram n) (j : Fin n) :
    X.degreeDrop j = X.capShift j.succ - X.capShift j.castSucc := by
  rw [degreeDrop_eq_exchange]
  unfold exchangeRow exchangeZero
  ring

theorem degreeDrop_pos (X : Diagram n) (j : Fin n) : 0 < X.degreeDrop j := by
  have h := X.capShift_strictMono (show j.castSucc < j.succ by
    change j.val < j.val + 1
    omega)
  rw [degreeDrop_eq_grid]
  omega

theorem squareDrop_factor (X : Diagram n) (j : Fin n) :
    X.squareDrop j = X.degreeDrop j * (X.exchangeRow j + X.exchangeZero j) := by
  rw [squareDrop_eq_exchange, degreeDrop_eq_exchange]
  ring

theorem degreeDrop_dvd_squareDrop (X : Diagram n) (j : Fin n) :
    X.degreeDrop j ∣ X.squareDrop j :=
  ⟨X.exchangeRow j + X.exchangeZero j, X.squareDrop_factor j⟩

/-- The rational denominator in scalar recovery is nonzero by strict grid order. -/
theorem degreeDrop_rat_ne_zero (X : Diagram n) (j : Fin n) :
    (X.degreeDrop j : ℚ) ≠ 0 := by
  have h := X.degreeDrop_pos j
  exact_mod_cast ne_of_gt h

theorem squareDrop_div_degreeDrop (X : Diagram n) (j : Fin n) :
    (X.squareDrop j : ℚ) / (X.degreeDrop j : ℚ) =
      (X.exchangeRow j : ℚ) + (X.exchangeZero j : ℚ) := by
  apply (div_eq_iff (X.degreeDrop_rat_ne_zero j)).mpr
  have h := X.squareDrop_factor j
  have hc : (X.squareDrop j : ℚ) =
      (X.degreeDrop j : ℚ) * ((X.exchangeRow j : ℚ) + (X.exchangeZero j : ℚ)) := by
    exact_mod_cast h
  simpa [mul_comm] using hc

/-- First scalar-recovery formula in `eq:scalar-recovery`. -/
theorem exchangeRow_scalar_recovery (X : Diagram n) (j : Fin n) :
    (X.exchangeRow j : ℚ) =
      ((X.squareDrop j : ℚ) / (X.degreeDrop j : ℚ) + (X.degreeDrop j : ℚ)) / 2 := by
  rw [squareDrop_div_degreeDrop]
  have h : (X.degreeDrop j : ℚ) =
      (X.exchangeRow j : ℚ) - (X.exchangeZero j : ℚ) := by
    exact_mod_cast X.degreeDrop_eq_exchange j
  rw [h]
  ring

/-- Second scalar-recovery formula in `eq:scalar-recovery`. -/
theorem exchangeZero_scalar_recovery (X : Diagram n) (j : Fin n) :
    (X.exchangeZero j : ℚ) =
      ((X.squareDrop j : ℚ) / (X.degreeDrop j : ℚ) - (X.degreeDrop j : ℚ)) / 2 := by
  rw [squareDrop_div_degreeDrop]
  have h : (X.degreeDrop j : ℚ) =
      (X.exchangeRow j : ℚ) - (X.exchangeZero j : ℚ) := by
    exact_mod_cast X.degreeDrop_eq_exchange j
  rw [h]
  ring

theorem exchangeRow_eq_rowLength (X : Diagram n) (j : Fin n) :
    X.exchangeRow j = (X.rowLength j : ℤ) :=
  (X.rowLength_eq_coordinates j).symm

theorem exchangeZero_zero (X : Diagram n) (hn : 0 < n) :
    X.exchangeZero ⟨0, hn⟩ = 0 := by
  simp [exchangeZero, capShift, rowParam, top_of_pos X hn]

theorem exchangeZero_next_eq_overlap (X : Diagram n) (i : Fin n)
    (hi : i.val + 1 < n) :
    X.exchangeZero ⟨i.val + 1, hi⟩ + 1 = X.overlap i hi := by
  have he : (⟨i.val + 1, hi⟩ : Fin n).castSucc = i.succ := by
    apply Fin.ext
    rfl
  have h := X.overlap_eq_coordinates i hi
  unfold exchangeZero
  rw [he]
  omega

/-- Equal drops recover both exchanged integers, not merely their unordered pair. -/
theorem exchange_eq_of_drops (X Y : Diagram n) (j : Fin n)
    (hd : X.degreeDrop j = Y.degreeDrop j)
    (hs : X.squareDrop j = Y.squareDrop j) :
    X.exchangeRow j = Y.exchangeRow j ∧ X.exchangeZero j = Y.exchangeZero j := by
  have hprod : X.degreeDrop j * (X.exchangeRow j + X.exchangeZero j) =
      X.degreeDrop j * (Y.exchangeRow j + Y.exchangeZero j) := by
    rw [← X.squareDrop_factor j, hs, Y.squareDrop_factor j, ← hd]
  have hsum := mul_left_cancel₀ (ne_of_gt (X.degreeDrop_pos j)) hprod
  have hx := X.degreeDrop_eq_exchange j
  have hy := Y.degreeDrop_eq_exchange j
  constructor <;> omega

/-- Full geometric degree and square profiles recover the ordered geometric data. -/
theorem rowLength_overlap_eq_of_profiles (X Y : Diagram n)
    (hd : ∀ j, X.peelDegree j = Y.peelDegree j)
    (hs : ∀ j, X.peelSquare j = Y.peelSquare j) :
    (∀ i, X.rowLength i = Y.rowLength i) ∧
      (∀ (i : Fin n) (hi : i.val + 1 < n), X.overlap i hi = Y.overlap i hi) := by
  have he : ∀ j : Fin n,
      X.exchangeRow j = Y.exchangeRow j ∧ X.exchangeZero j = Y.exchangeZero j := by
    intro j
    apply exchange_eq_of_drops
    · simp only [degreeDrop, hd]
    · simp only [squareDrop, hs]
  constructor
  · intro i
    have h := (he i).1
    rw [exchangeRow_eq_rowLength, exchangeRow_eq_rowLength] at h
    exact_mod_cast h
  · intro i hi
    rw [← X.exchangeZero_next_eq_overlap i hi, ← Y.exchangeZero_next_eq_overlap i hi,
      (he ⟨i.val + 1, hi⟩).2]

/-- Equal geometric moment profiles identify connected diagrams up to translation.
In fact the signed-overlap recovery remains valid without connectedness. -/
theorem translationEquivalent_of_profiles (X Y : Diagram n)
    (hd : ∀ j, X.peelDegree j = Y.peelDegree j)
    (hs : ∀ j, X.peelSquare j = Y.peelSquare j) : TranslationEquivalent X Y := by
  obtain ⟨hlen, hover⟩ := rowLength_overlap_eq_of_profiles X Y hd hs
  exact translationEquivalent_of_rowLength_overlap X Y hlen hover

end Diagram
end SkewSchurReconstruction
