/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.EmptyBorderCore
import SkewCornerDescent.Matrix.CommonCoreReindex
import SkewCornerDescent.Matrix.CommonCoreDuality
import Mathlib.Data.Fintype.Option

/-!
# Integral common-core divisibility with arbitrary imbalanced borders

Supports `shields-2026-skew-corner-descent.tex` (`lem:shared-core`).
Complete column expansion removes left-border states while preserving all
right-border couplings. Exact duality discharges the remaining right border.
The divisor is the full core determinant over every commutative ring.

Sorry-free.
-/

namespace SkewCornerDescent.Matrix

universe u

variable {α : Type u} {β γ F : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ] [CommRing F]

/-- Integral divisibility propagates from an empty left border to every finite
left border, with the same complete core and right-hand data. -/
theorem commonCoreDifference_left_induction
    (C : Matrix (Unit ⊕ β) (Unit ⊕ β) F)
    (S : Matrix (Unit ⊕ β) (Unit ⊕ γ) F) (B : Matrix γ (Unit ⊕ γ) F)
    (r s : (Unit ⊕ β) → F) (q : (Unit ⊕ γ) → F) (z : F)
    (hEmpty : ∀ [DecidableEq PEmpty.{u + 1}]
      (A₀ : Matrix (PEmpty.{u + 1} ⊕ Unit) PEmpty.{u + 1} F)
      (R₀ : Matrix (PEmpty.{u + 1} ⊕ Unit) (Unit ⊕ β) F)
      (T₀ : Matrix (PEmpty.{u + 1} ⊕ Unit) (Unit ⊕ γ) F)
      (t₀ : (PEmpty.{u + 1} ⊕ Unit) → F),
      C.det ∣ commonCoreDifference A₀ R₀ T₀ C S B r s t₀ q z)
    (A : Matrix (α ⊕ Unit) α F) (R : Matrix (α ⊕ Unit) (Unit ⊕ β) F)
    (T : Matrix (α ⊕ Unit) (Unit ⊕ γ) F) (t : (α ⊕ Unit) → F) :
    C.det ∣ commonCoreDifference A R T C S B r s t q z := by
  classical
  let P := fun (δ : Type u) [Fintype δ] => ∀ [DecidableEq δ]
    (A' : Matrix (δ ⊕ Unit) δ F) (R' : Matrix (δ ⊕ Unit) (Unit ⊕ β) F)
    (T' : Matrix (δ ⊕ Unit) (Unit ⊕ γ) F) (t' : (δ ⊕ Unit) → F),
    C.det ∣ commonCoreDifference A' R' T' C S B r s t' q z
  have hp : P α := by
    refine Fintype.induction_empty_option (P := P) ?_ ?_ ?_ α
    · intro δ ε _ e ih
      let : Fintype δ := Fintype.ofEquiv ε e.symm
      intro _ A' R' T' t'
      rw [← commonCoreDifference_left_equiv e A' R' T' C S B r s t' q z]
      exact ih _ _ _ _
    · intro _ A₀ R₀ T₀ t₀
      exact hEmpty A₀ R₀ T₀ t₀
    · intro δ _ ih dOption A' R' T' t'
      have hd : dOption = @Option.instDecidableEq δ (inferInstance : DecidableEq δ) :=
        Subsingleton.elim _ _
      cases hd
      apply commonCoreDifference_left_option_dvd A' R' T' C S B r s t' q z
      intro A₀ R₀ T₀ t₀
      exact ih A₀ R₀ T₀ t₀
  exact hp A R T t

/-- Empty right borders are discharged by the complete integral left expansion. -/
theorem commonCoreDifference_right_empty_dvd [IsEmpty γ]
    (A : Matrix (α ⊕ Unit) α F) (R : Matrix (α ⊕ Unit) (Unit ⊕ β) F)
    (T : Matrix (α ⊕ Unit) (Unit ⊕ γ) F) (C : Matrix (Unit ⊕ β) (Unit ⊕ β) F)
    (S : Matrix (Unit ⊕ β) (Unit ⊕ γ) F) (B : Matrix γ (Unit ⊕ γ) F)
    (r s : (Unit ⊕ β) → F) (t : (α ⊕ Unit) → F) (q : (Unit ⊕ γ) → F) (z : F) :
    C.det ∣ commonCoreDifference A R T C S B r s t q z := by
  apply commonCoreDifference_left_induction C S B r s q z _ A R T t
  intro _ A₀ R₀ T₀ t₀
  exact commonCoreDifference_empty_dvd A₀ R₀ T₀ C S B r s t₀ q z

/-- Every compatible imbalanced border retains divisibility by the entire
central determinant, including every multiplicity after specialization.

**Differs from the paper's route.** Complete border expansion and integral
condensation replace the generic singular-locus argument. -/
theorem commonCoreDifference_dvd
    (A : Matrix (α ⊕ Unit) α F) (R : Matrix (α ⊕ Unit) (Unit ⊕ β) F)
    (T : Matrix (α ⊕ Unit) (Unit ⊕ γ) F) (C : Matrix (Unit ⊕ β) (Unit ⊕ β) F)
    (S : Matrix (Unit ⊕ β) (Unit ⊕ γ) F) (B : Matrix γ (Unit ⊕ γ) F)
    (r s : (Unit ⊕ β) → F) (t : (α ⊕ Unit) → F) (q : (Unit ⊕ γ) → F) (z : F) :
    C.det ∣ commonCoreDifference A R T C S B r s t q z := by
  apply commonCoreDifference_left_induction C S B r s q z _ A R T t
  intro _ A₀ R₀ T₀ t₀
  rw [← commonCoreDifference_dual A₀ R₀ T₀ C S B r s t₀ q z]
  rw [← Matrix.det_transpose C]
  exact commonCoreDifference_right_empty_dvd _ _ _ _ _ _ _ _ _ _ _

end SkewCornerDescent.Matrix
