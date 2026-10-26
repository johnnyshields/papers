/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.CompleteAlgebra

/-!
# Strict positive matrix entries

The auxiliary convention in `sec:restoration` of
`shields-2026-skew-cofactor-independence.tex` suppresses the value at equality.
This differs from the genuine Jacobi--Trudi unit.  Sorry-free.
-/

namespace SkewJacobiNegative.StrictTriangularPaths

variable {R : Type*} [CommRing R]

/-- The manuscript's auxiliary positive-entry convention. -/
noncomputable def positiveGap (h : ℤ → R) (a b : ℤ) : R :=
  if b < a then h (a - b) else 0

@[simp]
theorem positiveGap_self (h : ℤ → R) (a : ℤ) : positiveGap h a a = 0 := by
  simp [positiveGap]

theorem positiveGap_of_lt (h : ℤ → R) {a b : ℤ} (hab : b < a) :
    positiveGap h a b = h (a - b) := by
  simp [positiveGap, hab]

theorem positiveGap_of_le (h : ℤ → R) {a b : ℤ} (hab : a ≤ b) :
    positiveGap h a b = 0 := by
  simp [positiveGap, not_lt.mpr hab]

/-- `H(U,V)`, with the value at equality suppressed. -/
noncomputable def positiveMatrix {α β : Type*} (h : ℤ → R)
    (U : α → ℤ) (V : β → ℤ) : Matrix α β R :=
  Matrix.of fun i j => positiveGap h (U i) (V j)

/-- Coefficient extension preserves the positive-entry convention. -/
theorem positiveGap_map {S : Type*} [CommRing S] (f : R →+* S)
    (h : ℤ → R) (a b : ℤ) :
    positiveGap (fun d => f (h d)) a b = f (positiveGap h a b) := by
  by_cases hab : b < a <;> simp [positiveGap, hab]

theorem positiveMatrix_map {S α β : Type*} [CommRing S] (f : R →+* S)
    (h : ℤ → R) (U : α → ℤ) (V : β → ℤ) :
    positiveMatrix (fun d => f (h d)) U V = (positiveMatrix h U V).map f := by
  ext i j
  exact positiveGap_map f h (U i) (V j)
end SkewJacobiNegative.StrictTriangularPaths
