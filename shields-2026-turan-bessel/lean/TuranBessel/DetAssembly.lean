/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import TuranBessel.Degree
import TuranBessel.Zseries
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# The Cauchy product of the coefficient sequences is the mixed-determinant sum

The purely algebraic half of `eq:Delta-n-MD` in `shields-2026-turan-bessel.tex`,
«Reciprocal-gamma convolution and canonical--microcanonical structure»
(`sec:coefficients`, `eq:matrix-series`, `eq:Tkt`) and «Four-copy determinant
sectors» (`subsec:four-copy`, `eq:Delta-n-MD`).

Once the three coefficient identifications `eq:alpha`, `eq:beta` and the `γ`
identity are known — that `A`, `B`, `C` have `λᵐ` coefficients `S_mα_m`, `S_mβ_m`
and `S_m(1+gc_m)` — the passage from `Δ = AC - gB²` to the mixed-determinant sum
`Δ_n = ½∑S_kS_{n-k}MD(M_k,M_{n-k})` involves no analysis at all.  It is one
Cauchy product and one symmetrization, and that is what is proved here:
```
  ∑_k (S_kα_k)(S_{n-k}(1+gc_{n-k})) - g∑_k (S_kβ_k)(S_{n-k}β_{n-k})
      = ψ₁(a)/(2Γ(a)⁴) · Dcoeff a n.
```
The right-hand factor is `Bridge.turanCoeffFactor`, written out inline so that
this module does not depend on `Bridge`.

Two facts do the work.  Under the square-root-free normalization
`N_m = diag(1,g^{-1/2}) M_m diag(1,g^{-1/2})` of `subsec:gram` the mixed determinant scales
by the determinant of the congruence, `MD(M_k,M_l) = g·MD(N_k,N_l)`, which is what
turns the `g^{-1}` in `Nmat`'s lower-right entry into the `1` of `eq:matrix-series`;
and `sred a m = S_m Γ(a)²` (`Zseries.sred_eq_sweight_mul`) converts the weights.
The asymmetry between the two sides — the left names `α_k` and `c_{n-k}`, the right
names both orderings — is removed by reflecting `k ↦ n-k`, under which the weight
`S_kS_{n-k}` is invariant.

Sorry-free.
-/

open Finset

namespace TuranBessel

variable {a : ℝ}

/-- The Cauchy product of two absolutely convergent power series in `λ`.  Stated
separately from the coefficient algebra because it is the only analytic input the
assembly needs: given the three coefficient identifications, `Δ = AC - gB²` is a
product of series and nothing more. -/
theorem tsum_cauchy_lam {f g : ℕ → ℝ} (lam : ℝ)
    (hf : Summable fun m => ‖f m * lam ^ m‖) (hg : Summable fun m => ‖g m * lam ^ m‖) :
    (∑' m : ℕ, f m * lam ^ m) * (∑' m : ℕ, g m * lam ^ m)
      = ∑' n : ℕ, (∑ k ∈ range (n + 1), f k * g (n - k)) * lam ^ n := by
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg]
  refine tsum_congr fun n => ?_
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hpow : lam ^ k * lam ^ (n - k) = lam ^ n := by
    rw [← pow_add, Nat.add_sub_cancel' hkn]
  calc f k * lam ^ k * (g (n - k) * lam ^ (n - k))
      = f k * g (n - k) * (lam ^ k * lam ^ (n - k)) := by ring
    _ = f k * g (n - k) * lam ^ n := by rw [hpow]

/-- **The algebraic half of `eq:Delta-n-MD`.**  The Cauchy product of the `A`,`C`
coefficient sequences less `g` times that of `B` with itself is the
mixed-determinant sum `Dcoeff`, up to `ψ₁(a)/(2Γ(a)⁴)`.  Stated in terms of the
coefficient sequences alone, so it composes with `eq:alpha`, `eq:beta` and the `γ`
identity without re-entering the analysis. -/
theorem cauchy_eq_factor_mul_Dcoeff (ha : 0 < a) (n : ℕ) :
    (∑ k ∈ range (n + 1),
        (sweight a k * αcoef a k) * (sweight a (n - k) * (1 + trigamma a * ccoef a (n - k))))
      - trigamma a * ∑ k ∈ range (n + 1),
        (sweight a k * βcoef a k) * (sweight a (n - k) * βcoef a (n - k))
      = trigamma a / (2 * Real.Gamma a ^ 4) * Dcoeff a n := by
  have hG : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  have hg : trigamma a ≠ 0 := (trigamma_pos ha).ne'
  have hR : trigamma a / (2 * Real.Gamma a ^ 4) * Dcoeff a n
      = ∑ k ∈ range (n + 1), (trigamma a / 2) *
          (sweight a k * sweight a (n - k) * SymMat.MD (Nmat a k) (Nmat a (n - k))) := by
    rw [Dcoeff, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [sred_eq_sweight_mul ha k, sred_eq_sweight_mul ha (n - k)]
    field_simp
  rw [hR, Finset.mul_sum, ← Finset.sum_sub_distrib, ← sub_eq_zero, ← Finset.sum_sub_distrib]
  have hterm : ∀ k ∈ range (n + 1),
      ((sweight a k * αcoef a k) * (sweight a (n - k) * (1 + trigamma a * ccoef a (n - k)))
        - trigamma a * ((sweight a k * βcoef a k) * (sweight a (n - k) * βcoef a (n - k))))
      - (trigamma a / 2) *
          (sweight a k * sweight a (n - k) * SymMat.MD (Nmat a k) (Nmat a (n - k)))
      = (1 / 2) * ((fun j => sweight a j * sweight a (n - j) * αcoef a j
              * (1 + trigamma a * ccoef a (n - j))) k
          - (fun j => sweight a j * sweight a (n - j) * αcoef a j
              * (1 + trigamma a * ccoef a (n - j))) (n - k)) := by
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have h1 : n - (n - k) = k := Nat.sub_sub_self hkn
    simp only [SymMat.MD, Nmat_a11, Nmat_a12, Nmat_a22, h1]
    field
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, Finset.sum_sub_distrib]
  have hrefl : ∑ k ∈ range (n + 1),
      (fun j => sweight a j * sweight a (n - j) * αcoef a j
          * (1 + trigamma a * ccoef a (n - j))) (n - k)
      = ∑ k ∈ range (n + 1),
      (fun j => sweight a j * sweight a (n - j) * αcoef a j
          * (1 + trigamma a * ccoef a (n - j))) k := by
    simpa using Finset.sum_range_reflect
      (fun j => sweight a j * sweight a (n - j) * αcoef a j
          * (1 + trigamma a * ccoef a (n - j))) (n + 1)
  rw [hrefl, sub_self, mul_zero]

end TuranBessel
