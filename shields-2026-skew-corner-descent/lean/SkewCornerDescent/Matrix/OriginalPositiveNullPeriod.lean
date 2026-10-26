/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.FieldPositiveNullPeriod
import SkewCornerDescent.Matrix.OriginalPositiveClassWitness

/-!
# Actual one-active response-period nullspace

Supports `shields-2026-skew-corner-descent.tex` (`lem:positive-support`). The
complete actual class family produces positive regular separating assignments.
Literal one-active counts and a zero full-period detector force its completed
response values periodic in the unchanged original field. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing MvPolynomial
open CyclicWindows

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- One-active nullity forces a literal completed actual response word periodic;
all positivity, regularity and separation inputs are produced from the same
complete original source class family. -/
theorem original_one_active_null_period {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    {r d s k : ℕ} [NeZero (r * d)] [NeZero (k * (r * d) + r * s)]
    (hr : 0 < r) (hs : 0 < s)
    (word : ZMod (r * d) → c.OriginalResponseClass P) (active : c.OriginalResponseClass P)
    (hsingle : ∀ a, classDefect word 1 d s (r * s - 1) 0 a =
      if a = active then (d : ℤ) else 0)
    (hzero : windowDefect (Subtype.val ∘ word) Subtype.val
      (classDefect word 1 d s (r * s - 1) 0) (k * d + s)
      (k * (r * d) + r * s) (r * d) = 0) :
    Function.Periodic (closureWord (Subtype.val ∘ word) active.val
      (k * (r * d) + r * s)) (r * d : ℕ) := by
  apply field_one_active_null_period
    (algebraMap (OtherPolynomial c.top) (OtherField c.top))
    (IsFractionRing.injective _ _) Subtype.val ?_ hr hs word active hsingle hzero
  intro a b hne
  have hab : a ≠ b := fun h => hne (congrArg Subtype.val h)
  obtain ⟨num, den, x, hrep, hnF, _, hnφ, _, hpos, hdistinct⟩ :=
    c.originalResponseClasses_positive_separated P hB hmax a b hab
  exact ⟨num, den, (MvPolynomial.eval x).comp (realResiduePolynomial c.top),
    hrep, hnF, hnφ, hpos, hdistinct⟩

/-- Coprime literal source counts reduce the completed actual response period
to the selected multiplicity, without substituting independent letter values. -/
theorem original_one_active_null_primitive {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    {r d s k : ℕ} [NeZero (r * d)] [NeZero (k * (r * d) + r * s)]
    (hr : 0 < r) (hs : 0 < s) (hcoprime : Nat.Coprime (k * d + s) d)
    (word : ZMod (r * d) → c.OriginalResponseClass P) (active : c.OriginalResponseClass P)
    (hsingle : ∀ a, classDefect word 1 d s (r * s - 1) 0 a =
      if a = active then (d : ℤ) else 0)
    (hzero : windowDefect (Subtype.val ∘ word) Subtype.val
      (classDefect word 1 d s (r * s - 1) 0) (k * d + s)
      (k * (r * d) + r * s) (r * d) = 0) :
    Function.Periodic (closureWord (Subtype.val ∘ word) active.val
      (k * (r * d) + r * s)) (r : ZMod (k * (r * d) + r * s)) := by
  have hp := c.original_one_active_null_period P hB hmax hr hs word active hsingle hzero
  have hg := zmod_periodic_gcd _ hp
  have hB : k * (r * d) + r * s = r * (k * d + s) := by ring
  have hgc : Nat.gcd (r * d) (k * (r * d) + r * s) = r := by
    rw [hB, Nat.gcd_mul_left, hcoprime.symm.gcd_eq_one, Nat.mul_one]
  rwa [hgc] at hg

/-- The actual one-active nullspace needs only uniqueness of the nonzero
literal class exponent. Its value `d` is produced by the complete count sum,
rather than supplied as an additional numeric hypothesis. -/
theorem original_one_active_null_of_unique {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    {r d s k : ℕ} [NeZero (r * d)] [NeZero (k * (r * d) + r * s)]
    (hr : 0 < r) (hs : 0 < s) (hcoprime : Nat.Coprime (k * d + s) d)
    (word : ZMod (r * d) → c.OriginalResponseClass P) (active : c.OriginalResponseClass P)
    (hunique : ∀ a, a ≠ active → classDefect word 1 d s (r * s - 1) 0 a = 0)
    (hzero : windowDefect (Subtype.val ∘ word) Subtype.val
      (classDefect word 1 d s (r * s - 1) 0) (k * d + s)
      (k * (r * d) + r * s) (r * d) = 0) :
    Function.Periodic (closureWord (Subtype.val ∘ word) active.val
      (k * (r * d) + r * s)) (r : ZMod (k * (r * d) + r * s)) := by
  have hsum := sum_reduced_classDefect hr hs word
  have hactive : classDefect word 1 d s (r * s - 1) 0 active = (d : ℤ) := by
    rw [Finset.sum_eq_single active] at hsum
    · exact hsum
    · intro a _ ha
      exact hunique a ha
    · intro h
      exact (h (Finset.mem_univ active)).elim
  have hsingle (a) : classDefect word 1 d s (r * s - 1) 0 a =
      if a = active then (d : ℤ) else 0 := by
    by_cases ha : a = active
    · rw [ha, ite_eq_left rfl, hactive]
    · rw [ite_eq_right ha, hunique a ha]
  exact c.original_one_active_null_primitive P hB hmax hr hs hcoprime word active hsingle hzero

end SkewCornerDescent.Matrix.SelectedCoordinate
