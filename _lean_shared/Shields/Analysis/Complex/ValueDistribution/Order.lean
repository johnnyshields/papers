/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Analysis.Complex.ValueDistribution.CharacteristicFunction
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The order of growth of a meromorphic function

The order of a meromorphic function `f` is the infimum of the exponents `p` for which the
Nevanlinna characteristic `T(r, f)` is `O(r ^ p)` as `r → ∞`.  For an entire function this agrees
with the classical order defined through the maximum modulus, and the infimum of the empty set is
`⊤`, the order of a function of infinite order.

## Main results

* `Shields.order` — the order of growth of `f`.
* `Shields.order_le_of_isBigO` — the order is at most any exponent controlling the characteristic.
* `Shields.isBigO_rpow_of_order_lt` — the converse direction: any exponent strictly above the order
  controls the characteristic.

## Tags

order of growth, Nevanlinna characteristic, value distribution
-/

open Asymptotics Filter Real ValueDistribution
open scoped ENNReal NNReal

namespace Shields

/--
The order of growth of a meromorphic function `f`: the infimum of the nonnegative exponents `p`
for which the Nevanlinna characteristic `T(r, f)` is `O(r ^ p)`.  The infimum of the empty set is
`⊤`.
-/
noncomputable def order (f : ℂ → ℂ) : ℝ≥0∞ :=
  ⨅ p ∈ {p : NNReal | characteristic f ⊤ =O[atTop] fun r : ℝ ↦ r ^ (p : ℝ)}, (p : ℝ≥0∞)

/--
The order is at most any exponent `p` for which the characteristic is `O(r ^ p)`.
-/
theorem order_le_of_isBigO {f : ℂ → ℂ} {p : NNReal}
    (h : characteristic f ⊤ =O[atTop] fun r : ℝ ↦ r ^ (p : ℝ)) :
    order f ≤ p :=
  iInf₂_le p h

/--
A function whose characteristic is `O(r ^ p)` for every positive `p` has order zero.
-/
theorem order_eq_zero_of_forall_pos {f : ℂ → ℂ}
    (h : ∀ p : NNReal, 0 < p → characteristic f ⊤ =O[atTop] fun r : ℝ ↦ r ^ (p : ℝ)) :
    order f = 0 :=
  le_antisymm
    (ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ by
      simpa using order_le_of_isBigO (h ε hε))
    bot_le

/--
A power of `r` dominates a smaller power, as `r → ∞`.
-/
theorem isBigO_rpow_rpow {p q : ℝ} (hpq : p ≤ q) :
    (fun r : ℝ ↦ r ^ p) =O[atTop] fun r : ℝ ↦ r ^ q := by
  rw [isBigO_iff]
  refine ⟨1, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
  rw [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _),
    Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)]
  exact Real.rpow_le_rpow_of_exponent_le hr hpq

/--
The characteristic is `O(r ^ p)` for every exponent `p` strictly above the order.  This is the
converse half of `Shields.order_le_of_isBigO`: the infimum is attained in the limit, not at the
order itself.
-/
theorem isBigO_rpow_of_order_lt {f : ℂ → ℂ} {p : NNReal} (h : order f < p) :
    characteristic f ⊤ =O[atTop] fun r : ℝ ↦ r ^ (p : ℝ) := by
  rw [order, iInf_lt_iff] at h
  obtain ⟨q, hq⟩ := h
  rw [iInf_lt_iff] at hq
  obtain ⟨hqmem, hqlt⟩ := hq
  simp only [Set.mem_ofPred_eq] at hqmem
  have hqp : (q : ℝ) ≤ (p : ℝ) := by
    have : q ≤ p := by exact_mod_cast hqlt.le
    exact_mod_cast this
  exact hqmem.trans (isBigO_rpow_rpow hqp)

end Shields
