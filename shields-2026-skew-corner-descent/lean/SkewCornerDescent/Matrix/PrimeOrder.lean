/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.PeriodTests
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

/-!
# Finite prime orders of nonzero symmetric-function polynomials

Supports `shields-2026-skew-corner-descent.tex`, «Period comparison and polynomial
obstructions» (`sec:periods`, `lem:alpha-row-candidate`).
Zero has extended order infinity; the natural-valued order is used only for
explicitly nonzero polynomial factors.

Sorry-free.
-/

namespace SkewCornerDescent.Matrix
open SkewGluing

/-- Natural-valued order, used below only when the polynomial is nonzero. -/
noncomputable def primeOrder (f g : Lambda) : ℕ := (emultiplicity f g).toNat

/-- Prime orders add on nonzero products. -/
theorem primeOrder_mul {f a b : Lambda} (hf : Prime f) (ha : a ≠ 0) (hb : b ≠ 0) :
    primeOrder f (a * b) = primeOrder f a + primeOrder f b := by
  unfold primeOrder
  rw [emultiplicity_mul hf, ENat.toNat_add]
  · exact finiteMultiplicity_iff_emultiplicity_ne_top.mp (FiniteMultiplicity.of_prime_left hf ha)
  · exact finiteMultiplicity_iff_emultiplicity_ne_top.mp (FiniteMultiplicity.of_prime_left hf hb)

/-- Orders of powers are multiplied by their natural exponent. -/
theorem primeOrder_pow {f a : Lambda} (hf : Prime f) (n : ℕ) :
    primeOrder f (a ^ n) = n * primeOrder f a := by
  unfold primeOrder
  rw [emultiplicity_pow hf, ENat.toNat_mul, ENat.toNat_natCast]

/-- A prime excluded from a polynomial has order zero. -/
theorem primeOrder_eq_zero_of_not_dvd {f a : Lambda} (hn : ¬ f ∣ a) :
    primeOrder f a = 0 := by
  unfold primeOrder
  rw [emultiplicity_eq_zero.mpr hn, ENat.toNat_zero]

/-- For a nonzero polynomial, order zero is exactly absence of the prime. -/
theorem primeOrder_eq_zero_iff {f a : Lambda} (hf : Prime f) (ha : a ≠ 0) :
    primeOrder f a = 0 ↔ ¬ f ∣ a := by
  unfold primeOrder
  have he := (FiniteMultiplicity.of_prime_left hf ha).emultiplicity_eq_multiplicity
  rw [he, ENat.toNat_natCast]
  exact multiplicity_eq_zero (FiniteMultiplicity.of_prime_left hf ha)

/-- A prime has order one in itself. -/
theorem primeOrder_self {f : Lambda} (hf : Prime f) : primeOrder f f = 1 := by
  simpa only [primeOrder, pow_one, ENat.toNat_natCast] using
    congrArg ENat.toNat (emultiplicity_pow_self_of_prime hf 1)

end SkewCornerDescent.Matrix
