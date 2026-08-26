/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Polynomial.Vieta

/-!
# Newton's identities for a multiset, and Vieta in the normalized form

Mathlib carries Newton's identities only for `MvPolynomial σ R` over a `Fintype σ`
(`MvPolynomial.psum_eq_mul_esymm_sub_sum`), and carries `Multiset.esymm` but no multiset power
sum.  It also states Vieta for `∏(X + C a)`, where the `k`-th coefficient is `esymm (card s - k)`.

Both gaps matter for a *normalized* product `∏(1 + a X)`, which is the shape a power series
factors into when its constant term is `1`: there the `k`-th coefficient is `esymm k` on the nose,
with no reference to the number of factors, so the statement survives the passage to an infinite
product where `card s` does not.  This file supplies the multiset power sum, that form of Vieta,
and Newton's identities transported to a multiset.

The transport is by evaluation: a multiset of cardinality `n` is `Finset.univ.val.map f` for the
enumeration `f : Fin n → R` of its underlying list, and `MvPolynomial.aeval f` carries `esymm` and
`psum` to their multiset counterparts.

## Main results

* `Shields.psum` --- the `n`-th power sum of a multiset
* `Shields.coeff_prod_one_add_C_mul_X` --- `(∏(1 + a X)).coeff k = s.esymm k`, for every `k`
* `Shields.psum_eq_mul_esymm_sub_sum` --- **Newton's identities for a multiset**
* `Shields.psum_eq_mul_coeff_sub_sum` --- the same recursion read off the coefficients of the
  normalized product, which is the form a symbol's Taylor coefficients present

## Papers depending on this file

* `edrei-spectral-classification` --- `EdreiClass/LaguerreOrigin.lean`, where the `k`-th power sum
  of the Edrei parameters is the `k`-th rung of the bound on `∑‖xᵢ‖⁻ᵏ` over a symbol's zeros

## Tags

Newton's identities, power sum, elementary symmetric function, Vieta, multiset
-/

open Finset Polynomial

namespace Shields

variable {R : Type*} [CommRing R]

/-! ### The power sum of a multiset -/

/-- **The `n`-th power sum of a multiset**, `∑ x ∈ s, x ^ n`.  The companion of
`Multiset.esymm`, which Mathlib has and this does not. -/
def psum (s : Multiset R) (n : ℕ) : R := (s.map (· ^ n)).sum

@[simp] theorem psum_zero_multiset (n : ℕ) : psum (0 : Multiset R) n = 0 := by simp [psum]

@[simp] theorem psum_cons (a : R) (s : Multiset R) (n : ℕ) :
    psum (a ::ₘ s) n = a ^ n + psum s n := by simp [psum]

theorem psum_one (s : Multiset R) : psum s 1 = s.sum := by simp [psum]

/-! ### Vieta for the normalized product -/

/-- The elementary symmetric functions of a multiset obey Pascal's recursion. -/
theorem esymm_cons (a : R) (s : Multiset R) (k : ℕ) :
    (a ::ₘ s).esymm (k + 1) = s.esymm (k + 1) + a * s.esymm k := by
  simp only [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_add, Multiset.sum_add,
    Multiset.map_map, Function.comp_def, Multiset.prod_cons]
  rw [← Multiset.sum_map_mul_left]

/-- **Vieta in the normalized form.**  For `s` a multiset of scalars, the `k`-th coefficient of
`∏_{a ∈ s} (1 + a X)` is the `k`-th elementary symmetric function of `s`, for every `k` --- with no
hypothesis relating `k` to the number of factors, both sides vanishing past it.

Mathlib's `Multiset.prod_X_add_C_coeff` is the reversed statement, `(∏(X + C a)).coeff k =
esymm (card s - k)`, which does refer to the number of factors. -/
theorem coeff_prod_one_add_C_mul_X (s : Multiset R) (k : ℕ) :
    ((s.map fun a => 1 + C a * X).prod).coeff k = s.esymm k := by
  induction s using Multiset.induction generalizing k with
  | empty =>
      cases k with
      | zero => simp [Multiset.esymm]
      | succ k => simp [Multiset.esymm, Multiset.powersetCard_zero_right, Polynomial.coeff_one]
  | cons a s ih =>
      rw [Multiset.map_cons, Multiset.prod_cons]
      set Q := (s.map fun a => 1 + C a * X).prod with hQ
      cases k with
      | zero =>
          rw [add_mul, one_mul, coeff_add, mul_assoc, coeff_C_mul]
          simp [ih 0, Multiset.esymm]
      | succ k =>
          rw [add_mul, one_mul, coeff_add, mul_assoc, coeff_C_mul, coeff_X_mul,
            ih (k + 1), ih k, esymm_cons]

/-! ### Newton's identities on a multiset

The transport from `MvPolynomial σ R` runs through an enumeration of the multiset.  Nothing here
is specific to the enumeration chosen: `aeval` of the `MvPolynomial` identity is an identity in
`R` about `Finset.univ.val.map f`, and every multiset is of that form. -/

private theorem aeval_psum {n : ℕ} (f : Fin n → R) (k : ℕ) :
    MvPolynomial.aeval f (MvPolynomial.psum (Fin n) R k) = psum (univ.val.map f) k := by
  rw [MvPolynomial.psum, map_sum]
  simp only [MvPolynomial.aeval_X, map_pow]
  rw [psum, Multiset.map_map]
  rfl

private theorem exists_enumeration {R : Type*} (s : Multiset R) :
    ∃ (n : ℕ) (f : Fin n → R), univ.val.map f = s := by
  refine ⟨s.toList.length, fun i => s.toList.get i, ?_⟩
  rw [Fin.univ_val_map, List.ofFn_get, Multiset.coe_toList]

/-- **Newton's identities for a multiset.**  For every `k > 0`,

`p_k = (-1)^{k+1} k e_k - ∑_{0 < i < k} (-1)^i e_i p_{k-i}`,

with `e` the elementary symmetric functions of `s` and `p` its power sums. -/
theorem psum_eq_mul_esymm_sub_sum (s : Multiset R) (k : ℕ) (hk : 0 < k) :
    psum s k = (-1) ^ (k + 1) * k * s.esymm k
      - ∑ a ∈ {a ∈ antidiagonal k | a.1 ∈ Set.Ioo 0 k},
          (-1) ^ a.1 * s.esymm a.1 * psum s a.2 := by
  obtain ⟨n, f, rfl⟩ := exists_enumeration s
  have h := congrArg (MvPolynomial.aeval f) (MvPolynomial.psum_eq_mul_esymm_sub_sum (Fin n) R k hk)
  rw [aeval_psum] at h
  rw [h]
  simp only [map_sub, map_mul, map_pow, map_neg, map_one, map_natCast, map_sum]
  rw [MvPolynomial.aeval_esymm_eq_multiset_esymm]
  refine congrArg (fun t => _ - t) (Finset.sum_congr rfl fun a _ => ?_)
  rw [MvPolynomial.aeval_esymm_eq_multiset_esymm, aeval_psum]

/-- **Newton's identities read off the coefficients of the normalized product.**  Writing
`P = ∏_{a ∈ s}(1 + a X)`, whose `k`-th coefficient is `e_k`, the power sums of `s` obey the
recursion in the coefficients of `P` alone.

This is the form in which the identity is used on a power series: the coefficients are given and
the parameters are not. -/
theorem psum_eq_mul_coeff_sub_sum (s : Multiset R) (k : ℕ) (hk : 0 < k) :
    psum s k = (-1) ^ (k + 1) * k * ((s.map fun a => 1 + C a * X).prod).coeff k
      - ∑ a ∈ {a ∈ antidiagonal k | a.1 ∈ Set.Ioo 0 k},
          (-1) ^ a.1 * ((s.map fun a => 1 + C a * X).prod).coeff a.1 * psum s a.2 := by
  simp only [coeff_prod_one_add_C_mul_X]
  exact psum_eq_mul_esymm_sub_sum s k hk

end Shields
