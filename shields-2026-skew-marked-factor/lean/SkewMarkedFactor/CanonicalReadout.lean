/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
import SkewMarkedFactor.TerminalOrder
import SkewMarkedFactor.ReducedNumerator
import SkewMarkedFactor.CharacterExpansion
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Canonical readouts from the parent and the supplied period

«Recovering the factors» (`sec:extraction`, `eq:inner-recovery`,
`eq:outer-recovery`) of `shields-2026-skew-marked-factor.tex`.
All definitions take only the parent polynomial and the period.  Scalar
reading uses a genuine nonzero denominator coefficient; its equality with a
fraction-field quotient is proved whenever that quotient is rational.
-/

namespace SkewMarkedFactor
open Gluing Gluing.Plan MvPolynomial
open scoped BigOperators

/-- Read a numerator coefficient against a canonically selected denominator coefficient. -/
noncomputable def scalarReading (U T : Lambda) : ℚ :=
  U.coeff (leastMonomial T.support) / T.coeff (leastMonomial T.support)

/-- Nonzero denominators have a proved nonzero selected coefficient. -/
theorem selected_coefficient_ne_zero {T : Lambda} (hT : T ≠ 0) :
    T.coeff (leastMonomial T.support) ≠ 0 :=
  mem_support_iff.mp (least_monomial_spec (support_nonempty.mpr hT)).1

/-- A rational polynomial quotient is read exactly, with no zero-denominator convention. -/
theorem scalarReading_eq {U T : Lambda} {q : ℚ} (hT : T ≠ 0)
    (hU : U = C q * T) : scalarReading U T = q := by
  rw [scalarReading, hU, coeff_C_mul]
  exact mul_div_cancel_right₀ q (selected_coefficient_ne_zero hT)

/-- The actual fraction field of the complete-generator polynomial ring. -/
abbrev ReadoutField := FractionRing Lambda

/-- The mathematical quotient, separately from its rational scalar reading. -/
noncomputable def actualRatio (U T : Lambda) : ReadoutField :=
  algebraMap Lambda ReadoutField U / algebraMap Lambda ReadoutField T

/-- Polynomial scalar equality implies equality of the genuine fraction-field quotient. -/
theorem actualRatio_eq_scalar {U T : Lambda} {q : ℚ} (hT : T ≠ 0)
    (hU : U = C q * T) : actualRatio U T = algebraMap ℚ ReadoutField q := by
  have ht : algebraMap Lambda ReadoutField T ≠ 0 :=
    fun h => hT ((IsFractionRing.injective Lambda ReadoutField) (by simpa using h))
  rw [actualRatio, hU, map_mul]
  have hc : algebraMap Lambda ReadoutField (C q) = algebraMap ℚ ReadoutField q := by
    rw [← MvPolynomial.algebraMap_eq]
    exact (IsScalarTower.algebraMap_apply ℚ Lambda ReadoutField q).symm
  rw [hc]
  exact mul_div_cancel_right₀ _ ht

/-- A partition's actual adjoint indices multiplied by the supplied period. -/
noncomputable def periodWord (p : ℕ) (d : powerExponent) : List ℕ :=
  (exponentWord d).map (fun k => k * p)

/-- The actual derivative indexed by a period-scaled partition. -/
noncomputable def characterDerivative (P : Lambda) (p : ℕ) (d : powerExponent) : Lambda :=
  pDerivWord (periodWord p d) P

/-- Canonical gcd-reduced-numerator inner readout, with no normalization exponents as inputs. -/
noncomputable def innerReadout (P : Lambda) (p : ℕ) : Lambda :=
  primitive (reducedNumerator (penultimateDerivative P p) (terminalDerivative P p))

/-- The rational polynomial recovered from all character-index scalar readings. -/
noncomputable def outerReadout (P : Lambda) (p : ℕ) : Lambda :=
  ∑ d ∈ partitionExponents (terminalOrder P p),
    C (scalarReading (characterDerivative P p d) (terminalDerivative P p) / powerZ d) *
      pProd (exponentWord d)

end SkewMarkedFactor
