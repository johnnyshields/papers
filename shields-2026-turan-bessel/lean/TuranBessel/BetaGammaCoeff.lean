/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import TuranBessel.ParameterCalculus
import TuranBessel.Phase

/-!
# The `B` and `C` coefficients: `eq:beta` and `eq:gamma-kappa`

The second and third columns of `shields-2026-turan-bessel.tex`, «Reciprocal-gamma convolution and
canonical--microcanonical structure»
(`sec:coefficients`, `thm:coefficients`, `eq:ABC-expansions`):
```
  B          = Z² + ZZ_{aΘ} - Z_aZ_Θ            = ∑_m S_m β_m λ^m ,
  C_{κ,τ}    = τZ² + g(κZZ_Θ - ZZ_{ΘΘ} + Z_Θ²)  = ∑_m S_m(τ + g c_m^{(κ)}) λ^m ,
```
with `Θ = λ∂_λ`, `β_0 = 1`, `β_m = (2a+m-2)/(2(a+m-1))` (`eq:beta`) and `c_m^{(κ)}`
of `eq:cm-kappa`, `eq:cm-kappa-general`.  The `A` column (`eq:alpha`) is not here.

* `pairWeight`, `sum_pairWeight`, `sum_sub_mul_pairWeight`,
  `sum_mul_sub_mul_pairWeight` — the three moments of the diagonal convolution
  weight `w_i = u_iu_{m-i}`.  Only the third needs `lem:convolution` again, at
  `a+1` and `m-2` after the factors `i(m-i)` cancel; the first moment is free from
  the reflection `i ↦ m-i`, which fixes `w`.
* `sum_score_pairWeight` — **the score identity** `∑_i(m-i)Ξ_iw_i = -mS_m/(2(a+m-1))`,
  `Ξ = ψ(a+i)-ψ(a+m-i)`, the `E(DΞ)` of `eq:EDXi`.  This is the one analytic step:
  the digamma weights are the `δ`-derivative of the *antidiagonal* deformation
  `(α,β) = (a+δ, a+1-δ)` of `lem:convolution`.  Because the two centers move
  oppositely, `α+β` is constant and the Pochhammer numerator does not depend on
  `δ`, so the whole `δ`-dependence of the closed form is the pair
  `Γ(a+m-1+δ)Γ(a+m-δ)`, whose score at `δ=0` is `ψ(a+m)-ψ(a+m-1) = 1/(a+m-1)`.
  Differentiating a *finite* sum needs no domination, which is why this route is
  taken rather than differentiating `Z` in the parameter.
* `bcoeffSum_eq`, `ccoeffSum_eq` — `eq:beta` and `eq:gamma-kappa` as coefficient
  identities.  `ccoeffSum_eq` is proved for every real `g`, `κ`, `τ`, the paper's
  case being `g = ψ₁(a)`; `ckappa` is the `c_m^{(κ)}` already carried by `Phase`, and
  `ckappa_one_eq_ccoef` is its endpoint `κ=1` against the `ccoef` of `Coefficients`, and
  `ccoeffSum_endpoint` the `(κ,τ)=(1,1)` corner.
  `C` needs no digamma at all: after `(m-i)² = m(m-i) - i(m-i)` it is the three
  moments and the ratio `sweight_shift`.
* `summable_pow_mul_pow_div_factorial`, `summable_norm_weighted_zterm`,
  `tsum_weighted_mul` — the analytic layer.  Any coefficient family bounded by
  `C(k+1)^j` leaves `∑_k c_kz_k` absolutely convergent, and the Cauchy product of
  two such series has `m`-th coefficient the finite convolution `convCoeff`,
  because `z_i(λ)z_{m-i}(λ) = λ^mw_i` carries the whole `λ`-dependence.
* `hasDerivAt_weightedZ`, `ZEulerSeries_eq_euler_deriv` and its two companions —
  `Θ` and `∂_a` really are the operators.  `∂_λ` passes under the sum on
  `(-(|λ|+1), |λ|+1)`, multiplying by `λ` puts the index back in the numerator,
  and `ZParamSeries_eq_deriv` reads `∂_a` off `deriv_Zfun_param`.
* `tsum_beta_eq_B`, `tsum_gamma_eq_C` — the two expansions written in the paper's
  own operators, with no series definition of ours left in the statement.

Sorry-free, and axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

open Filter Topology Set
open scoped BigOperators
open Finset

namespace TuranBessel

variable {a : ℝ}

/-! ### The convolution pair weight -/

/-- `w_i = u_i u_{m-i}` with `u_k = 1/(k!Γ(a+k))`: the summand of `lem:convolution`
on the diagonal `α = β = a`. -/
noncomputable def pairWeight (a : ℝ) (m i : ℕ) : ℝ :=
  1 / ((Nat.factorial i : ℝ) * (Nat.factorial (m - i) : ℝ)
        * Real.Gamma (a + (i : ℝ)) * Real.Gamma (a + ((m - i : ℕ) : ℝ)))

/-- `∑_i w_i = S_m`: the diagonal case of `lem:convolution`. -/
theorem sum_pairWeight (ha : 0 < a) (m : ℕ) :
    ∑ i ∈ range (m + 1), pairWeight a m i = sweight a m := by
  rw [sweight]
  exact gamma_convolution_diag ha m

/-- `w` is symmetric under `i ↦ m - i`. -/
theorem pairWeight_symm {m i : ℕ} (him : i ≤ m) :
    pairWeight a m (m - i) = pairWeight a m i := by
  rw [pairWeight, pairWeight, Nat.sub_sub_self him]
  ring


/-- Reflection `i ↦ m - i` on `range (m+1)`. -/
theorem sum_range_reflect_succ (f : ℕ → ℝ) (m : ℕ) :
    ∑ i ∈ range (m + 1), f (m - i) = ∑ i ∈ range (m + 1), f i := by
  simpa using Finset.sum_range_reflect f (m + 1)

/-! ### The two moments of the pair weight -/

/-- `∑_i (m-i) w_i = (m/2) S_m`.  The reflection `i ↦ m-i` fixes `w`, so the two
first moments agree and their sum is `m S_m`. -/
theorem sum_sub_mul_pairWeight (ha : 0 < a) (m : ℕ) :
    ∑ i ∈ range (m + 1), ((m - i : ℕ) : ℝ) * pairWeight a m i
      = (m : ℝ) / 2 * sweight a m := by
  have hswap : ∑ i ∈ range (m + 1), ((m - i : ℕ) : ℝ) * pairWeight a m i
      = ∑ i ∈ range (m + 1), (i : ℝ) * pairWeight a m i := by
    rw [← sum_range_reflect_succ (fun i => (i : ℝ) * pairWeight a m i) m]
    refine Finset.sum_congr rfl fun i hi => ?_
    have him : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [pairWeight_symm him]
  have htotal : ∑ i ∈ range (m + 1),
      (((m - i : ℕ) : ℝ) * pairWeight a m i + (i : ℝ) * pairWeight a m i)
      = (m : ℝ) * sweight a m := by
    rw [← sum_pairWeight ha m, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have him : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hcast : ((m - i : ℕ) : ℝ) = (m : ℝ) - (i : ℝ) := Nat.cast_sub him
    rw [hcast]; ring
  rw [Finset.sum_add_distrib, hswap] at htotal
  linarith

/-- `∑_i i(m-i) w_i = S_{m-2}(a+1)`, for `m ≥ 2`: canceling the factors `i` and
`m-i` and shifting `j = i-1` is the diagonal convolution at `a+1`. -/
theorem sum_mul_sub_mul_pairWeight (ha : 0 < a) (m : ℕ) :
    ∑ i ∈ range (m + 3), (i : ℝ) * ((m + 2 - i : ℕ) : ℝ) * pairWeight a (m + 2) i
      = sweight (a + 1) m := by
  have ha1 : 0 < a + 1 := by linarith
  rw [← sum_pairWeight ha1 m]
  set f : ℕ → ℝ := fun i => (i : ℝ) * ((m + 2 - i : ℕ) : ℝ) * pairWeight a (m + 2) i with hf
  have hpeel : ∑ i ∈ range (m + 3), f i = ∑ i ∈ range (m + 1), f (i + 1) := by
    rw [Finset.sum_range_succ' f (m + 2), Finset.sum_range_succ (fun i => f (i + 1)) (m + 1)]
    have h0 : f 0 = 0 := by simp [hf]
    have htop : f (m + 1 + 1) = 0 := by simp [hf]
    rw [h0, htop]; ring
  rw [hpeel]
  refine Finset.sum_congr rfl fun i hi => ?_
  have him : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hs1 : m + 2 - (i + 1) = (m - i) + 1 := by omega
  have hfi : (0 : ℝ) < (Nat.factorial i : ℝ) := by exact_mod_cast Nat.factorial_pos i
  have hfmi : (0 : ℝ) < (Nat.factorial (m - i) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (m - i)
  have hGl : Real.Gamma (a + 1 + (i : ℝ)) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by have := Nat.cast_nonneg (α := ℝ) i; linarith)).ne'
  have hGr : Real.Gamma (a + 1 + ((m - i : ℕ) : ℝ)) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by have := Nat.cast_nonneg (α := ℝ) (m - i); linarith)).ne'
  simp only [hf, pairWeight, hs1]
  rw [Nat.factorial_succ, Nat.factorial_succ]
  have e1 : a + ((i + 1 : ℕ) : ℝ) = a + 1 + (i : ℝ) := by push_cast; ring
  have e2 : a + (((m - i) + 1 : ℕ) : ℝ) = a + 1 + ((m - i : ℕ) : ℝ) := by push_cast; ring
  rw [e1, e2]
  push_cast
  field_simp


/-! ### The shift `S_{m-2}(a+1)` against `S_m(a)` -/

/-- `2(2a+2m+1) S_m(a+1) = (m+2)(m+1)(a+m+1) S_{m+2}(a)`.  Both weights carry the
same Pochhammer base `(2a+m+1)_\bullet`, so the ratio is the two extra factors of
that base against the factorial and the Gamma shift. -/
theorem sweight_shift (ha : 0 < a) (m : ℕ) :
    2 * (2 * a + 2 * (m : ℝ) + 1) * sweight (a + 1) m
      = ((m : ℝ) + 2) * ((m : ℝ) + 1) * (a + (m : ℝ) + 1) * sweight a (m + 2) := by
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have ham : 0 < a + (m : ℝ) + 1 := by linarith
  have hG1 : 0 < Real.Gamma (a + (m : ℝ) + 1) := Real.Gamma_pos_of_pos ham
  have hbase : 2 * (a + 1) + (m : ℝ) - 1 = 2 * a + (m : ℝ) + 1 := by ring
  have hbase2 : 2 * a + ((m + 2 : ℕ) : ℝ) - 1 = 2 * a + (m : ℝ) + 1 := by push_cast; ring
  have hpoch : poch (2 * a + (m : ℝ) + 1) (m + 2)
      = poch (2 * a + (m : ℝ) + 1) m
        * (2 * a + 2 * (m : ℝ) + 1) * (2 * a + 2 * (m : ℝ) + 2) := by
    rw [show m + 2 = (m + 1) + 1 from rfl, poch_succ, poch_succ]
    push_cast; ring
  have hGam : Real.Gamma (a + ((m + 2 : ℕ) : ℝ))
      = Real.Gamma (a + (m : ℝ) + 1) * (a + (m : ℝ) + 1) := by
    have h : a + ((m + 2 : ℕ) : ℝ) = (a + (m : ℝ) + 1) + 1 := by push_cast; ring
    rw [h, Real.Gamma_add_one ham.ne']
    ring
  have hGl : Real.Gamma (a + 1 + (m : ℝ)) = Real.Gamma (a + (m : ℝ) + 1) := by
    rw [show a + 1 + (m : ℝ) = a + (m : ℝ) + 1 by ring]
  have hfac : (Nat.factorial (m + 2) : ℝ)
      = (Nat.factorial m : ℝ) * ((m : ℝ) + 1) * ((m : ℝ) + 2) := by
    rw [show m + 2 = (m + 1) + 1 from rfl, Nat.factorial_succ, Nat.factorial_succ]
    push_cast; ring
  have hfm : (0 : ℝ) < (Nat.factorial m : ℝ) := by exact_mod_cast Nat.factorial_pos m
  rw [sweight, sweight, hbase, hbase2, hpoch, hGam, hGl, hfac]
  field_simp

/-! ### `eq:gamma-kappa`: the `C_{κ,τ}` coefficient -/

/-- At the endpoint `κ = 1`, the `c_m^{(κ)}` of `Phase` is the `c_m` of
`Coefficients`. -/
theorem ckappa_one_eq_ccoef (ha : 0 < a) (m : ℕ) : ckappa a 1 m = ccoef a m := by
  have h := ckappa_sub_ccoef ha 1 m
  simp only [sub_self, zero_mul, zero_div] at h
  linarith

/-- `[λ^m] C_{κ,τ}`: the Cauchy product of `eq:Ckt-def`, with `Θ` acting on a power
series as multiplication by the index. -/
noncomputable def ccoeffSum (a g κ τ : ℝ) (m : ℕ) : ℝ :=
  ∑ i ∈ range (m + 1),
    (τ + g * (κ * ((m - i : ℕ) : ℝ) - ((m - i : ℕ) : ℝ) ^ 2
        + (i : ℝ) * ((m - i : ℕ) : ℝ))) * pairWeight a m i

/-- The three moments of `pairWeight` that `ccoeffSum` is built from. -/
theorem ccoeffSum_eq_moments (ha : 0 < a) (g κ τ : ℝ) (m : ℕ) :
    ccoeffSum a g κ τ m
      = τ * sweight a m + g * ((κ - (m : ℝ)) * ((m : ℝ) / 2 * sweight a m)
          + 2 * ∑ i ∈ range (m + 1), (i : ℝ) * ((m - i : ℕ) : ℝ) * pairWeight a m i) := by
  have hsplit : ∀ i ∈ range (m + 1),
      (τ + g * (κ * ((m - i : ℕ) : ℝ) - ((m - i : ℕ) : ℝ) ^ 2
          + (i : ℝ) * ((m - i : ℕ) : ℝ))) * pairWeight a m i
        = τ * pairWeight a m i
          + (g * κ - g * (m : ℝ)) * (((m - i : ℕ) : ℝ) * pairWeight a m i)
          + (2 * g) * ((i : ℝ) * ((m - i : ℕ) : ℝ) * pairWeight a m i) := by
    intro i hi
    have him : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hcast : ((m - i : ℕ) : ℝ) = (m : ℝ) - (i : ℝ) := Nat.cast_sub him
    rw [hcast]; ring
  rw [ccoeffSum, Finset.sum_congr rfl hsplit]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum, sum_pairWeight ha m, sum_sub_mul_pairWeight ha m]
  ring

/-- **`eq:gamma-kappa`.**  `[λ^m] C_{κ,τ} = S_m (τ + g c_m^{(κ)})`, for every real
`g`, `κ`, `τ`; the paper's case is `g = ψ₁(a)`. -/
theorem ccoeffSum_eq (ha : 0 < a) (g κ τ : ℝ) (m : ℕ) :
    ccoeffSum a g κ τ m = sweight a m * (τ + g * ckappa a κ m) := by
  rw [ccoeffSum_eq_moments ha]
  match m with
  | 0 =>
      simp [ckappa, mul_comm]
  | 1 =>
      have h : ∑ i ∈ range 2, (i : ℝ) * ((1 - i : ℕ) : ℝ) * pairWeight a 1 i = 0 := by
        simp [Finset.sum_range_succ]
      rw [h, ckappa_one]
      push_cast
      ring
  | (n + 2) =>
      have hP := sum_mul_sub_mul_pairWeight ha n
      have hS := sweight_shift ha n
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have hden : 2 * a + 2 * ((n : ℝ) + 2) - 3 ≠ 0 := by nlinarith
      have hck : ckappa a κ (n + 2)
          = κ * ((n : ℝ) + 2) / 2
            - ((n : ℝ) + 2) * (2 * a + (n : ℝ)) / (2 * (2 * a + 2 * (n : ℝ) + 1)) := by
        unfold ckappa
        rw [if_neg (by omega), if_neg (by omega)]
        push_cast
        rw [show 2 * a + ((n : ℝ) + 2) - 2 = 2 * a + (n : ℝ) by ring,
          show 2 * a + 2 * ((n : ℝ) + 2) - 3 = 2 * a + 2 * (n : ℝ) + 1 by ring]
      rw [hck]
      have hPval : ∑ i ∈ range (n + 3), (i : ℝ) * ((n + 2 - i : ℕ) : ℝ) * pairWeight a (n + 2) i
          = sweight (a + 1) n := hP
      push_cast
      push_cast at hPval hS
      rw [hPval]
      have hd : 2 * a + 2 * (n : ℝ) + 1 ≠ 0 := by nlinarith
      field_simp
      linear_combination (2 * g) * hS


/-- The endpoint `(κ,τ) = (1,1)` of `eq:gamma-kappa`: `[λ^m]C = S_m(1 + g c_m)`
with `g = ψ₁(a)` and `c_m` the `ccoef` of `Coefficients`. -/
theorem ccoeffSum_endpoint (ha : 0 < a) (m : ℕ) :
    ccoeffSum a (trigamma a) 1 1 m = sweight a m * (1 + trigamma a * ccoef a m) := by
  rw [ccoeffSum_eq ha, ckappa_one_eq_ccoef ha]

/-! ### The `δ`-deformation with two centers -/

/-- `δ ↦ [Γ(y+δ)Γ(z-δ)]⁻¹`.  The antidiagonal deformation of a reciprocal-gamma
pair: the two centers move oppositely, so their sum `y+z` — and with it the
Pochhammer factor of `lem:convolution` — is held fixed. -/
noncomputable def gammaSplitInv (y z d : ℝ) : ℝ := (Real.Gamma (y + d) * Real.Gamma (z - d))⁻¹

theorem hasDerivAt_gammaSplitInv {y z d : ℝ} (h₁ : 0 < y + d) (h₂ : 0 < z - d) :
    HasDerivAt (gammaSplitInv y z)
      ((-realDigamma (y + d) + realDigamma (z - d)) * gammaSplitInv y z d) d := by
  have hG1 : Real.Gamma (y + d) ≠ 0 := (Real.Gamma_pos_of_pos h₁).ne'
  have hG2 : Real.Gamma (z - d) ≠ 0 := (Real.Gamma_pos_of_pos h₂).ne'
  have hu : HasDerivAt (fun e : ℝ => (Real.Gamma (y + e))⁻¹)
      (-realDigamma (y + d) / Real.Gamma (y + d)) d := by
    simpa using (hasDerivAt_inv_Gamma h₁).comp d ((hasDerivAt_id d).const_add y)
  have hv : HasDerivAt (fun e : ℝ => (Real.Gamma (z - e))⁻¹)
      (realDigamma (z - d) / Real.Gamma (z - d)) d := by
    have hcomp := (hasDerivAt_inv_Gamma h₂).comp d ((hasDerivAt_id d).const_sub z)
    simp only [Function.comp_def] at hcomp
    refine hcomp.congr_deriv ?_
    field_simp
  have hmul := hu.mul hv
  have hfun : gammaSplitInv y z
      =ᶠ[𝓝 d] ((fun e : ℝ => (Real.Gamma (y + e))⁻¹) * fun e : ℝ => (Real.Gamma (z - e))⁻¹) := by
    filter_upwards with e
    simp [gammaSplitInv, Pi.mul_apply, mul_comm]
  refine (hmul.congr_of_eventuallyEq hfun).congr_deriv ?_
  rw [gammaSplitInv]
  field_simp

/-- The pair weight `w_i` with the antidiagonal deformation `a ↦ (a+δ, a-δ)`
carried on its two Gamma factors. -/
noncomputable def pairWeightD (a : ℝ) (m i : ℕ) (d : ℝ) : ℝ :=
  1 / ((Nat.factorial i : ℝ) * (Nat.factorial (m - i) : ℝ))
    * gammaSplitInv (a + (i : ℝ)) (a + ((m - i : ℕ) : ℝ)) d

@[simp] theorem pairWeightD_zero (a : ℝ) (m i : ℕ) : pairWeightD a m i 0 = pairWeight a m i := by
  rw [pairWeightD, gammaSplitInv, pairWeight]
  simp only [add_zero, sub_zero]
  field_simp

/-- `∂_δ w_i(δ)|_δ = (-ψ(a+i+δ) + ψ(a+m-i-δ)) w_i(δ)`: the score of the deformed
weight, `eq:Fdelta`. -/
theorem hasDerivAt_pairWeightD {m i : ℕ} {d : ℝ}
    (h₁ : 0 < a + (i : ℝ) + d) (h₂ : 0 < a + ((m - i : ℕ) : ℝ) - d) :
    HasDerivAt (pairWeightD a m i)
      ((-realDigamma (a + (i : ℝ) + d) + realDigamma (a + ((m - i : ℕ) : ℝ) - d))
        * pairWeightD a m i d) d := by
  have h := (hasDerivAt_gammaSplitInv h₁ h₂).const_mul
    (1 / ((Nat.factorial i : ℝ) * (Nat.factorial (m - i) : ℝ)))
  refine h.congr_deriv ?_
  rw [pairWeightD]; ring

/-- `f_m(δ) = ∑_i (m-i) w_i(δ)`, the first moment of the deformed weight. -/
noncomputable def momentD (a : ℝ) (m : ℕ) (d : ℝ) : ℝ :=
  ∑ i ∈ range (m + 1), ((m - i : ℕ) : ℝ) * pairWeightD a m i d

theorem momentD_zero (ha : 0 < a) (m : ℕ) :
    momentD a m 0 = (m : ℝ) / 2 * sweight a m := by
  rw [momentD]
  simp only [pairWeightD_zero]
  exact sum_sub_mul_pairWeight ha m

/-- `f_m'(δ)` termwise: the score-weighted first moment. -/
theorem hasDerivAt_momentD (a : ℝ) (m : ℕ) {d : ℝ}
    (hd₁ : -a < d) (hd₂ : d < a) :
    HasDerivAt (momentD a m)
      (∑ i ∈ range (m + 1), ((m - i : ℕ) : ℝ)
        * ((-realDigamma (a + (i : ℝ) + d) + realDigamma (a + ((m - i : ℕ) : ℝ) - d))
            * pairWeightD a m i d)) d := by
  have hfun : momentD a m
      = fun e : ℝ => ∑ i ∈ range (m + 1), ((m - i : ℕ) : ℝ) * pairWeightD a m i e := rfl
  rw [hfun]
  refine HasDerivAt.fun_sum fun i _ => ?_
  have hi : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
  have hmi : (0 : ℝ) ≤ ((m - i : ℕ) : ℝ) := Nat.cast_nonneg (m - i)
  exact (hasDerivAt_pairWeightD (by linarith) (by linarith)).const_mul _


/-- **The closed form of `f_m` on `|δ| < a`.**  `lem:convolution` at
`(α,β) = (a+δ, a+1-δ)` and `m-1`: the two centers move oppositely, so
`α+β = 2a+1` is constant and the Pochhammer numerator does not depend on `δ`. -/
theorem momentD_eq (a : ℝ) (n : ℕ) {d : ℝ} (hd₁ : -a < d) (hd₂ : d < a) :
    momentD a (n + 1) d
      = poch (2 * a + (n : ℝ)) n / (Nat.factorial n : ℝ)
          * gammaSplitInv (a + (n : ℝ)) (a + (n : ℝ) + 1) d := by
  have hα : 0 < a + d := by linarith
  have hβ : 0 < a + 1 - d := by linarith
  have hconv := gamma_convolution hα hβ n
  rw [show a + d + (a + 1 - d) + (n : ℝ) - 1 = 2 * a + (n : ℝ) by ring] at hconv
  rw [momentD, Finset.sum_range_succ]
  have htop : ((n + 1 - (n + 1) : ℕ) : ℝ) * pairWeightD a (n + 1) (n + 1) d = 0 := by simp
  rw [htop, add_zero]
  have hterm : ∀ i ∈ range (n + 1),
      ((n + 1 - i : ℕ) : ℝ) * pairWeightD a (n + 1) i d
        = 1 / ((Nat.factorial i : ℝ) * (Nat.factorial (n - i) : ℝ)
              * Real.Gamma (a + d + (i : ℝ)) * Real.Gamma (a + 1 - d + ((n - i : ℕ) : ℝ))) := by
    intro i hi
    have him : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hs : n + 1 - i = (n - i) + 1 := by omega
    have hfi : (0 : ℝ) < (Nat.factorial i : ℝ) := by exact_mod_cast Nat.factorial_pos i
    have hfni : (0 : ℝ) < (Nat.factorial (n - i) : ℝ) := by
      exact_mod_cast Nat.factorial_pos (n - i)
    have hni : (0 : ℝ) ≤ ((n - i : ℕ) : ℝ) := Nat.cast_nonneg (n - i)
    have hG1 : 0 < Real.Gamma (a + d + (i : ℝ)) :=
      Real.Gamma_pos_of_pos (by have := Nat.cast_nonneg (α := ℝ) i; linarith)
    have hG2 : 0 < Real.Gamma (a + 1 - d + ((n - i : ℕ) : ℝ)) :=
      Real.Gamma_pos_of_pos (by linarith)
    rw [pairWeightD, gammaSplitInv, hs, Nat.factorial_succ]
    rw [show a + (i : ℝ) + d = a + d + (i : ℝ) by ring,
      show a + (((n - i) + 1 : ℕ) : ℝ) - d = a + 1 - d + ((n - i : ℕ) : ℝ) by push_cast; ring]
    push_cast
    field_simp
  rw [Finset.sum_congr rfl hterm, hconv, gammaSplitInv]
  rw [show a + (n : ℝ) + d = a + d + (n : ℝ) by ring,
    show a + (n : ℝ) + 1 - d = a + 1 - d + (n : ℝ) by ring]
  field_simp

/-- `f_m'(0) = f_m(0)/(a+m-1)`: the closed form's only `δ`-dependence is the pair
`Γ(a+m-1+δ)Γ(a+m-δ)`, whose score at `δ=0` is `ψ(a+m)-ψ(a+m-1) = 1/(a+m-1)`. -/
theorem hasDerivAt_momentD_closed (ha : 0 < a) (n : ℕ) :
    HasDerivAt (momentD a (n + 1)) (momentD a (n + 1) 0 / (a + (n : ℝ))) 0 := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have han : 0 < a + (n : ℝ) := by linarith
  set c : ℝ := poch (2 * a + (n : ℝ)) n / (Nat.factorial n : ℝ) with hc
  have hsplit : HasDerivAt (gammaSplitInv (a + (n : ℝ)) (a + (n : ℝ) + 1))
      ((-realDigamma (a + (n : ℝ) + 0) + realDigamma (a + (n : ℝ) + 1 - 0))
        * gammaSplitInv (a + (n : ℝ)) (a + (n : ℝ) + 1) 0) 0 :=
    hasDerivAt_gammaSplitInv (by linarith) (by linarith)
  have hrec : realDigamma (a + (n : ℝ) + 1) = realDigamma (a + (n : ℝ)) + 1 / (a + (n : ℝ)) :=
    realDigamma_add_one han
  have hG := hsplit.const_mul c
  have hval : c * ((-realDigamma (a + (n : ℝ) + 0) + realDigamma (a + (n : ℝ) + 1 - 0))
      * gammaSplitInv (a + (n : ℝ)) (a + (n : ℝ) + 1) 0)
      = momentD a (n + 1) 0 / (a + (n : ℝ)) := by
    rw [momentD_eq a n (by linarith) ha]
    simp only [add_zero, sub_zero]
    rw [hrec, ← hc]
    field
  rw [hval] at hG
  refine hG.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds (show -a < (0 : ℝ) by linarith) ha] with e he
  rw [hc]
  exact momentD_eq a n he.1 he.2

/-! ### `eq:beta`: the score identity and the `B` coefficient -/

/-- **The score identity** of the `thm:coefficients` proof.  With
`Ξ = ψ(a+i) - ψ(a+m-i)`,
```
  ∑_i (m-i) Ξ_i w_i = -m S_m / (2(a+m-1)) ,       m ≥ 1 .
```
Equivalently `E(J Ξ) = ½ E(D Ξ) = m/(2(a+m-1))` after normalization by `S_m`
(`eq:EDXi`). -/
theorem sum_score_pairWeight (ha : 0 < a) (n : ℕ) :
    ∑ i ∈ range (n + 2), ((n + 1 - i : ℕ) : ℝ)
        * ((realDigamma (a + (i : ℝ)) - realDigamma (a + ((n + 1 - i : ℕ) : ℝ)))
            * pairWeight a (n + 1) i)
      = -(((n : ℝ) + 1) / 2 * sweight a (n + 1)) / (a + (n : ℝ)) := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have han : 0 < a + (n : ℝ) := by linarith
  have h1 := hasDerivAt_momentD a (n + 1) (d := 0) (by linarith) ha
  have h2 := hasDerivAt_momentD_closed ha n
  have heq := h1.unique h2
  rw [momentD_zero ha] at heq
  have hcast : (((n + 1 : ℕ)) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [hcast] at heq
  have hneg : ∑ i ∈ range (n + 2), ((n + 1 - i : ℕ) : ℝ)
        * ((realDigamma (a + (i : ℝ)) - realDigamma (a + ((n + 1 - i : ℕ) : ℝ)))
            * pairWeight a (n + 1) i)
      = -∑ i ∈ range (n + 2), ((n + 1 - i : ℕ) : ℝ)
          * ((-realDigamma (a + (i : ℝ) + 0)
                + realDigamma (a + ((n + 1 - i : ℕ) : ℝ) - 0)) * pairWeightD a (n + 1) i 0) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [pairWeightD_zero, add_zero, sub_zero]
    ring
  rw [hneg, heq]
  ring

/-- `[λ^m] B`: the Cauchy product of `eq:Bdef`, `B = Z² + ZZ_{aΘ} - Z_aZ_Θ`.
`Θ` multiplies by the index and `∂_a` brings down `-ψ(a+k)`, so the two
Euler-parameter terms leave the score `ψ(a+i) - ψ(a+m-i)` weighted by `m-i`. -/
noncomputable def bcoeffSum (a : ℝ) (m : ℕ) : ℝ :=
  ∑ i ∈ range (m + 1),
    (1 + ((m - i : ℕ) : ℝ)
        * (realDigamma (a + (i : ℝ)) - realDigamma (a + ((m - i : ℕ) : ℝ)))) * pairWeight a m i

/-- **`eq:beta`.**  `[λ^m]B = S_m β_m`, with `β_0 = 1` and
`β_m = (2a+m-2)/(2(a+m-1))`. -/
theorem bcoeffSum_eq (ha : 0 < a) (m : ℕ) :
    bcoeffSum a m = sweight a m * βcoef a m := by
  have hsplit : bcoeffSum a m
      = (∑ i ∈ range (m + 1), pairWeight a m i)
        + ∑ i ∈ range (m + 1), ((m - i : ℕ) : ℝ)
            * ((realDigamma (a + (i : ℝ)) - realDigamma (a + ((m - i : ℕ) : ℝ)))
                * pairWeight a m i) := by
    rw [bcoeffSum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hsplit, sum_pairWeight ha]
  match m with
  | 0 => simp [βcoef]
  | (n + 1) =>
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have han : 0 < a + (n : ℝ) := by linarith
      rw [sum_score_pairWeight ha n]
      unfold βcoef
      rw [if_neg (by omega)]
      push_cast
      rw [show 2 * a + ((n : ℝ) + 1) - 2 = 2 * a + (n : ℝ) - 1 by ring,
        show 2 * (a + ((n : ℝ) + 1) - 1) = 2 * (a + (n : ℝ)) by ring]
      field


/-! ### Absolute summability of the weighted series -/

/-- `∑_k (k+1)^j |x|^k/k!` converges for every `j`: shifting the index by one costs
a factor `(k+2)^{j+1}/(k+1) ≤ 2^{j+1}(k+1)^j`, which is the induction step. -/
theorem summable_pow_mul_pow_div_factorial (j : ℕ) (x : ℝ) :
    Summable (fun k : ℕ => ((k : ℝ) + 1) ^ j * (|x| ^ k / (Nat.factorial k : ℝ))) := by
  induction j with
  | zero => simpa using Real.summable_pow_div_factorial |x|
  | succ j ih =>
      rw [← summable_nat_add_iff 1]
      refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
        (ih.mul_left (2 ^ (j + 1) * |x|))
      have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have hfk : (0 : ℝ) < (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos k
      have hfac : (Nat.factorial (k + 1) : ℝ) = ((k : ℝ) + 1) * (Nat.factorial k : ℝ) := by
        rw [Nat.factorial_succ]; push_cast; ring
      have hstep : ((k : ℝ) + 2) ^ (j + 1) ≤ 2 ^ (j + 1) * ((k : ℝ) + 1) ^ (j + 1) := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (by positivity) (by linarith) _
      have hxk : (0 : ℝ) ≤ |x| ^ k := by positivity
      rw [show (((k + 1 : ℕ) : ℝ) + 1) = ((k : ℝ) + 2) by push_cast; ring, hfac,
        show |x| ^ (k + 1) = |x| * |x| ^ k by rw [pow_succ]; ring]
      rw [show ((k : ℝ) + 2) ^ (j + 1) * (|x| * |x| ^ k / (((k : ℝ) + 1) * (Nat.factorial k : ℝ)))
          = (((k : ℝ) + 2) ^ (j + 1) / ((k : ℝ) + 1)) * (|x| * (|x| ^ k / (Nat.factorial k : ℝ)))
          by field_simp,
        show 2 ^ (j + 1) * |x| * (((k : ℝ) + 1) ^ j * (|x| ^ k / (Nat.factorial k : ℝ)))
          = (2 ^ (j + 1) * ((k : ℝ) + 1) ^ j) * (|x| * (|x| ^ k / (Nat.factorial k : ℝ)))
          by ring]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      rw [div_le_iff₀ hk1]
      calc ((k : ℝ) + 2) ^ (j + 1) ≤ 2 ^ (j + 1) * ((k : ℝ) + 1) ^ (j + 1) := hstep
        _ = 2 ^ (j + 1) * ((k : ℝ) + 1) ^ j * ((k : ℝ) + 1) := by rw [pow_succ]; ring

/-- A weight bounded by `C(k+1)²` leaves the `Z`-series absolutely summable.  Every
coefficient family the `B` and `C` expansions need — `1`, `k`, `k²`, `-ψ(a+k)` and
`-kψ(a+k)` — clears this bar, the digamma ones through
`abs_realDigamma_add_nat_le`. -/
theorem summable_norm_weighted_zterm (ha : 0 < a) (lam : ℝ) {c : ℕ → ℝ} {C : ℝ}
    (j : ℕ) (hc : ∀ k, |c k| ≤ C * ((k : ℝ) + 1) ^ j) :
    Summable (fun k => ‖c k * zterm a lam k‖) := by
  have hC : 0 ≤ C := by have := (abs_nonneg (c 0)).trans (hc 0); simpa using this
  have hGa : 0 < Real.Gamma a := Real.Gamma_pos_of_pos ha
  have hmin : 0 < min a 1 := lt_min ha one_pos
  have hD : 0 < Real.Gamma a * min a 1 := mul_pos hGa hmin
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
    (((summable_pow_mul_pow_div_factorial j lam).mul_left (C / (Real.Gamma a * min a 1))))
  have hGk : 0 < Real.Gamma (a + (k : ℝ)) :=
    Real.Gamma_pos_of_pos (by have := Nat.cast_nonneg (α := ℝ) k; linarith)
  have hfk : (0 : ℝ) < (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hnorm : ‖zterm a lam k‖
      = |lam| ^ k / ((Nat.factorial k : ℝ) * Real.Gamma (a + (k : ℝ))) := by
    rw [zterm, Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos (mul_pos hfk hGk)]
  have hlow : Real.Gamma a * min a 1 ≤ Real.Gamma (a + (k : ℝ)) :=
    Gamma_mul_min_le_Gamma_add ha k
  have hinv : 1 / Real.Gamma (a + (k : ℝ)) ≤ 1 / (Real.Gamma a * min a 1) :=
    one_div_le_one_div_of_le hD hlow
  have habs : (0 : ℝ) ≤ |lam| ^ k / (Nat.factorial k : ℝ) := by positivity
  have hz : ‖zterm a lam k‖
      ≤ (1 / (Real.Gamma a * min a 1)) * (|lam| ^ k / (Nat.factorial k : ℝ)) := by
    rw [hnorm]
    calc |lam| ^ k / ((Nat.factorial k : ℝ) * Real.Gamma (a + (k : ℝ)))
        = (|lam| ^ k / (Nat.factorial k : ℝ)) * (1 / Real.Gamma (a + (k : ℝ))) := by field_simp
      _ ≤ (|lam| ^ k / (Nat.factorial k : ℝ)) * (1 / (Real.Gamma a * min a 1)) :=
          mul_le_mul_of_nonneg_left hinv habs
      _ = (1 / (Real.Gamma a * min a 1)) * (|lam| ^ k / (Nat.factorial k : ℝ)) := by ring
  rw [norm_mul, Real.norm_eq_abs]
  calc |c k| * ‖zterm a lam k‖
      ≤ (C * ((k : ℝ) + 1) ^ j)
          * ((1 / (Real.Gamma a * min a 1)) * (|lam| ^ k / (Nat.factorial k : ℝ))) := by
        exact mul_le_mul (hc k) hz (norm_nonneg _) (by positivity)
    _ = C / (Real.Gamma a * min a 1)
          * (((k : ℝ) + 1) ^ j * (|lam| ^ k / (Nat.factorial k : ℝ))) := by ring

/-- `|ψ(a+k)| ≤ (2|ψ(a)| + 1/a)(k+1)`, the linear bound the domination runs on. -/
theorem abs_realDigamma_add_nat_le_linear (ha : 0 < a) (k : ℕ) :
    |realDigamma (a + (k : ℝ))| ≤ (2 * |realDigamma a| + 1 / a) * ((k : ℝ) + 1) := by
  have h := abs_realDigamma_add_nat_le ha (a := a) ⟨le_refl a, le_refl a⟩ k
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have habs : (0 : ℝ) ≤ |realDigamma a| := abs_nonneg _
  have hka : (k : ℝ) / a ≤ (1 / a) * ((k : ℝ) + 1) := by
    rw [div_le_iff₀ ha]
    have : (1 / a) * ((k : ℝ) + 1) * a = (k : ℝ) + 1 := by field_simp
    rw [this]; linarith
  nlinarith [h, hka]

/-! ### The Cauchy product of two weighted copies of `Z` -/

/-- `z_i(λ) z_{m-i}(λ) = λ^m w_i`: the `λ`-dependence of a pair of terms is the
single power `λ^m`, which is what turns each product into a coefficient identity. -/
theorem zterm_mul_zterm (a lam : ℝ) {m i : ℕ} (him : i ≤ m) :
    zterm a lam i * zterm a lam (m - i) = lam ^ m * pairWeight a m i := by
  have hpow : lam ^ i * lam ^ (m - i) = lam ^ m := by
    rw [← pow_add, Nat.add_sub_cancel' him]
  simp only [zterm, pairWeight]
  rw [div_mul_div_comm, hpow]
  ring

/-- The `m`-th coefficient of the Cauchy product of two index-weighted copies of `Z`. -/
noncomputable def convCoeff (a : ℝ) (p q : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ i ∈ range (m + 1), p i * q (m - i) * pairWeight a m i

theorem summable_convCoeff {a lam : ℝ} {p q : ℕ → ℝ}
    (hp : Summable fun k => ‖p k * zterm a lam k‖)
    (hq : Summable fun k => ‖q k * zterm a lam k‖) :
    Summable (fun m : ℕ => convCoeff a p q m * lam ^ m) := by
  have h := (summable_norm_sum_mul_antidiagonal_of_summable_norm hp hq).of_norm
  refine h.congr fun m => ?_
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, convCoeff, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  have him : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [show p i * zterm a lam i * (q (m - i) * zterm a lam (m - i))
      = p i * q (m - i) * (zterm a lam i * zterm a lam (m - i)) by ring,
    zterm_mul_zterm a lam him]
  ring

/-- **The Cauchy product.**  Two index-weighted copies of `Z` multiply to the power
series whose `m`-th coefficient is the finite convolution `convCoeff` against
`pairWeight`. -/
theorem tsum_weighted_mul {a lam : ℝ} {p q : ℕ → ℝ}
    (hp : Summable fun k => ‖p k * zterm a lam k‖)
    (hq : Summable fun k => ‖q k * zterm a lam k‖) :
    (∑' k, p k * zterm a lam k) * (∑' k, q k * zterm a lam k)
      = ∑' m : ℕ, convCoeff a p q m * lam ^ m := by
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hp hq]
  refine tsum_congr fun m => ?_
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, convCoeff, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  have him : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [show p i * zterm a lam i * (q (m - i) * zterm a lam (m - i))
      = p i * q (m - i) * (zterm a lam i * zterm a lam (m - i)) by ring,
    zterm_mul_zterm a lam him]
  ring


/-! ### The four weighted series -/

/-- `Z` itself, written with the constant weight so the Cauchy product applies. -/
theorem Zfun_eq_weighted (a lam : ℝ) : Zfun a lam = ∑' k : ℕ, (1 : ℝ) * zterm a lam k := by
  rw [Zfun]; exact tsum_congr fun k => (one_mul _).symm

/-- `Z_Θ = ΘZ`, `Θ = λ∂_λ`, as a series: `Θ` multiplies the `k`-th coefficient by `k`. -/
noncomputable def ZEulerSeries (a lam : ℝ) : ℝ := ∑' k : ℕ, (k : ℝ) * zterm a lam k

/-- `Z_{ΘΘ} = Θ²Z`: the index weight squared. -/
noncomputable def ZEuler2Series (a lam : ℝ) : ℝ := ∑' k : ℕ, ((k : ℝ)) ^ 2 * zterm a lam k

/-- `Z_a = ∂_aZ`: the parameter derivative brings down `-ψ(a+k)`
(`hasDerivAt_zterm`). -/
noncomputable def ZParamSeries (a lam : ℝ) : ℝ :=
  ∑' k : ℕ, (-realDigamma (a + (k : ℝ))) * zterm a lam k

/-- `Z_{aΘ} = ∂_aΘZ`: the two weights multiply. -/
noncomputable def ZParamEulerSeries (a lam : ℝ) : ℝ :=
  ∑' k : ℕ, (-realDigamma (a + (k : ℝ)) * (k : ℝ)) * zterm a lam k

/-- `Z_a` is the `a`-derivative of `Z`, from `deriv_Zfun_param`. -/
theorem ZParamSeries_eq_deriv (ha : 0 < a) (lam : ℝ) :
    ZParamSeries a lam = deriv (fun x : ℝ => Zfun x lam) a :=
  (deriv_Zfun_param ha lam).symm

theorem summable_norm_one_zterm (ha : 0 < a) (lam : ℝ) :
    Summable (fun k : ℕ => ‖(1 : ℝ) * zterm a lam k‖) :=
  summable_norm_weighted_zterm ha lam (C := 1) 2 (fun k => by
    have : (1 : ℝ) ≤ ((k : ℝ) + 1) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
    simpa using this)

theorem summable_norm_idx_zterm (ha : 0 < a) (lam : ℝ) :
    Summable (fun k : ℕ => ‖(k : ℝ) * zterm a lam k‖) :=
  summable_norm_weighted_zterm ha lam (C := 1) 2 (fun k => by
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    rw [abs_of_nonneg hk]; nlinarith)

theorem summable_norm_sq_zterm (ha : 0 < a) (lam : ℝ) :
    Summable (fun k : ℕ => ‖((k : ℝ)) ^ 2 * zterm a lam k‖) :=
  summable_norm_weighted_zterm ha lam (C := 1) 2 (fun k => by
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    rw [abs_of_nonneg (by positivity)]; nlinarith)

theorem summable_norm_psi_zterm (ha : 0 < a) (lam : ℝ) :
    Summable (fun k : ℕ => ‖(-realDigamma (a + (k : ℝ))) * zterm a lam k‖) :=
  summable_norm_weighted_zterm ha lam (C := 2 * |realDigamma a| + 1 / a) 2 (fun k => by
    have h := abs_realDigamma_add_nat_le_linear ha k
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hC : 0 ≤ 2 * |realDigamma a| + 1 / a := by positivity
    have hstep : (2 * |realDigamma a| + 1 / a) * ((k : ℝ) + 1)
        ≤ (2 * |realDigamma a| + 1 / a) * ((k : ℝ) + 1) ^ 2 :=
      mul_le_mul_of_nonneg_left (by nlinarith) hC
    rw [abs_neg]
    linarith [h, hstep])

theorem summable_norm_psi_idx_zterm (ha : 0 < a) (lam : ℝ) :
    Summable (fun k : ℕ => ‖(-realDigamma (a + (k : ℝ)) * (k : ℝ)) * zterm a lam k‖) :=
  summable_norm_weighted_zterm ha lam (C := 2 * |realDigamma a| + 1 / a) 2 (fun k => by
    have h := abs_realDigamma_add_nat_le_linear ha k
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hC : 0 ≤ 2 * |realDigamma a| + 1 / a := by positivity
    rw [abs_mul, abs_neg, abs_of_nonneg hk]
    have hstep : |realDigamma (a + (k : ℝ))| * (k : ℝ)
        ≤ (2 * |realDigamma a| + 1 / a) * ((k : ℝ) + 1) * (k : ℝ) :=
      mul_le_mul_of_nonneg_right h hk
    nlinarith [hstep, hC])

/-! ### Linear combinations of power series -/

private theorem tsum_lin3 {f₀ f₁ f₂ : ℕ → ℝ} (h₀ : Summable f₀) (h₁ : Summable f₁)
    (h₂ : Summable f₂) (t₀ t₁ t₂ : ℝ) :
    t₀ * (∑' m, f₀ m) + t₁ * (∑' m, f₁ m) + t₂ * (∑' m, f₂ m)
      = ∑' m, (t₀ * f₀ m + t₁ * f₁ m + t₂ * f₂ m) := by
  rw [← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left,
    ← Summable.tsum_add (h₀.mul_left t₀) (h₁.mul_left t₁),
    ← Summable.tsum_add ((h₀.mul_left t₀).add (h₁.mul_left t₁)) (h₂.mul_left t₂)]

private theorem tsum_lin4 {f₀ f₁ f₂ f₃ : ℕ → ℝ} (h₀ : Summable f₀) (h₁ : Summable f₁)
    (h₂ : Summable f₂) (h₃ : Summable f₃) (t₀ t₁ t₂ t₃ : ℝ) :
    t₀ * (∑' m, f₀ m) + t₁ * (∑' m, f₁ m) + t₂ * (∑' m, f₂ m) + t₃ * (∑' m, f₃ m)
      = ∑' m, (t₀ * f₀ m + t₁ * f₁ m + t₂ * f₂ m + t₃ * f₃ m) := by
  rw [← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left,
    ← Summable.tsum_add (h₀.mul_left t₀) (h₁.mul_left t₁),
    ← Summable.tsum_add ((h₀.mul_left t₀).add (h₁.mul_left t₁)) (h₂.mul_left t₂),
    ← Summable.tsum_add (((h₀.mul_left t₀).add (h₁.mul_left t₁)).add (h₂.mul_left t₂))
        (h₃.mul_left t₃)]

/-! ### `eq:ABC-expansions` for `B` and `C` -/

/-- `B = Z² + ZZ_{aΘ} - Z_aZ_Θ` (`eq:Bdef`), assembled from the four series. -/
noncomputable def Bseries (a lam : ℝ) : ℝ :=
  Zfun a lam * Zfun a lam + Zfun a lam * ZParamEulerSeries a lam
    - ZParamSeries a lam * ZEulerSeries a lam

/-- `C_{κ,τ} = τZ² + g(κZZ_Θ - ZZ_{ΘΘ} + Z_Θ²)` (`eq:Ckt-def`). -/
noncomputable def Cseries (a g κ τ lam : ℝ) : ℝ :=
  τ * (Zfun a lam * Zfun a lam)
    + g * (κ * (Zfun a lam * ZEulerSeries a lam) - Zfun a lam * ZEuler2Series a lam
        + ZEulerSeries a lam * ZEulerSeries a lam)

/-- **`eq:ABC-expansions` for `B`, with `eq:beta`.**
`B = ∑_m S_m β_m λ^m`. -/
theorem Bseries_eq_tsum (ha : 0 < a) (lam : ℝ) :
    Bseries a lam = ∑' m : ℕ, sweight a m * βcoef a m * lam ^ m := by
  have h1 := summable_norm_one_zterm ha lam
  have hk := summable_norm_idx_zterm ha lam
  have hp := summable_norm_psi_zterm ha lam
  have hpk := summable_norm_psi_idx_zterm ha lam
  have e0 := tsum_weighted_mul h1 h1
  have e1 := tsum_weighted_mul h1 hpk
  have e2 := tsum_weighted_mul hp hk
  rw [Bseries, Zfun_eq_weighted, ZParamEulerSeries, ZParamSeries, ZEulerSeries, e0, e1, e2,
    show ∀ x y z : ℝ, x + y - z = 1 * x + 1 * y + (-1) * z from fun x y z => by ring,
    tsum_lin3 (summable_convCoeff h1 h1) (summable_convCoeff h1 hpk)
      (summable_convCoeff hp hk)]
  refine tsum_congr fun m => ?_
  have hc : convCoeff a (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) m
      + convCoeff a (fun _ => (1 : ℝ)) (fun k => -realDigamma (a + (k : ℝ)) * (k : ℝ)) m
      - convCoeff a (fun k => -realDigamma (a + (k : ℝ))) (fun k => (k : ℝ)) m
      = bcoeffSum a m := by
    simp only [convCoeff, bcoeffSum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [show (1 : ℝ) * (convCoeff a (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) m * lam ^ m)
        + 1 * (convCoeff a (fun _ => (1 : ℝ))
            (fun k => -realDigamma (a + (k : ℝ)) * (k : ℝ)) m * lam ^ m)
        + (-1) * (convCoeff a (fun k => -realDigamma (a + (k : ℝ)))
            (fun k => (k : ℝ)) m * lam ^ m)
      = (convCoeff a (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) m
          + convCoeff a (fun _ => (1 : ℝ))
              (fun k => -realDigamma (a + (k : ℝ)) * (k : ℝ)) m
          - convCoeff a (fun k => -realDigamma (a + (k : ℝ))) (fun k => (k : ℝ)) m) * lam ^ m
      by ring, hc, bcoeffSum_eq ha]

/-- **`eq:ABC-expansions` for `C`, with `eq:gamma-kappa`.**
`C_{κ,τ} = ∑_m S_m (τ + g c_m^{(κ)}) λ^m`. -/
theorem Cseries_eq_tsum (ha : 0 < a) (g κ τ lam : ℝ) :
    Cseries a g κ τ lam = ∑' m : ℕ, sweight a m * (τ + g * ckappa a κ m) * lam ^ m := by
  have h1 := summable_norm_one_zterm ha lam
  have hk := summable_norm_idx_zterm ha lam
  have hk2 := summable_norm_sq_zterm ha lam
  have e0 := tsum_weighted_mul h1 h1
  have e1 := tsum_weighted_mul h1 hk
  have e2 := tsum_weighted_mul h1 hk2
  have e3 := tsum_weighted_mul hk hk
  rw [Cseries, Zfun_eq_weighted, ZEulerSeries, ZEuler2Series, e0, e1, e2, e3,
    show ∀ x y z w : ℝ, τ * x + g * (κ * y - z + w)
        = τ * x + (g * κ) * y + (-g) * z + g * w from fun x y z w => by ring,
    tsum_lin4 (summable_convCoeff h1 h1) (summable_convCoeff h1 hk)
      (summable_convCoeff h1 hk2) (summable_convCoeff hk hk)]
  refine tsum_congr fun m => ?_
  have hc : τ * convCoeff a (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) m
      + (g * κ) * convCoeff a (fun _ => (1 : ℝ)) (fun k => (k : ℝ)) m
      + (-g) * convCoeff a (fun _ => (1 : ℝ)) (fun k => ((k : ℝ)) ^ 2) m
      + g * convCoeff a (fun k => (k : ℝ)) (fun k => (k : ℝ)) m
      = ccoeffSum a g κ τ m := by
    simp only [convCoeff, ccoeffSum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [show τ * (convCoeff a (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) m * lam ^ m)
        + (g * κ) * (convCoeff a (fun _ => (1 : ℝ)) (fun k => (k : ℝ)) m * lam ^ m)
        + (-g) * (convCoeff a (fun _ => (1 : ℝ)) (fun k => ((k : ℝ)) ^ 2) m * lam ^ m)
        + g * (convCoeff a (fun k => (k : ℝ)) (fun k => (k : ℝ)) m * lam ^ m)
      = (τ * convCoeff a (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) m
          + (g * κ) * convCoeff a (fun _ => (1 : ℝ)) (fun k => (k : ℝ)) m
          + (-g) * convCoeff a (fun _ => (1 : ℝ)) (fun k => ((k : ℝ)) ^ 2) m
          + g * convCoeff a (fun k => (k : ℝ)) (fun k => (k : ℝ)) m) * lam ^ m
      by ring, hc, ccoeffSum_eq ha]


/-! ### The Euler derivative `Θ = λ∂_λ` -/

/-- The `λ`-derivative of the `k`-th term of `Z`. -/
theorem hasDerivAt_zterm_lam (a : ℝ) (k : ℕ) (y : ℝ) :
    HasDerivAt (fun x : ℝ => zterm a x k)
      ((k : ℝ) * y ^ (k - 1) / ((Nat.factorial k : ℝ) * Real.Gamma (a + (k : ℝ)))) y := by
  simpa [zterm] using
    (hasDerivAt_pow k y).div_const ((Nat.factorial k : ℝ) * Real.Gamma (a + (k : ℝ)))

/-- A summable majorant for the termwise `λ`-derivative of a weighted `Z`-series,
uniform on `(-(|λ|+1), |λ|+1)`. -/
private theorem exists_lam_deriv_bound (ha : 0 < a) {c : ℕ → ℝ} {C : ℝ} (j : ℕ)
    (hc : ∀ k, |c k| ≤ C * ((k : ℝ) + 1) ^ j) (lam : ℝ) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ (k : ℕ) (y : ℝ), y ∈ Ioo (-(|lam| + 1)) (|lam| + 1) →
      ‖c k * ((k : ℝ) * y ^ (k - 1)
          / ((Nat.factorial k : ℝ) * Real.Gamma (a + (k : ℝ))))‖ ≤ u k := by
  have hC : 0 ≤ C := by have := (abs_nonneg (c 0)).trans (hc 0); simpa using this
  have hGa : 0 < Real.Gamma a := Real.Gamma_pos_of_pos ha
  have hmin : 0 < min a 1 := lt_min ha one_pos
  set D : ℝ := 1 / (Real.Gamma a * min a 1) with hD
  have hD0 : 0 < D := by rw [hD]; positivity
  set R : ℝ := |lam| + 2 with hR
  have hR1 : (1 : ℝ) ≤ R := by rw [hR]; linarith [abs_nonneg lam]
  refine ⟨fun k => C * D * (((k : ℝ) + 1) ^ (j + 1) * (|R| ^ k / (Nat.factorial k : ℝ))),
    (summable_pow_mul_pow_div_factorial (j + 1) R).mul_left (C * D), fun k y hy => ?_⟩
  have habsR : |R| = R := abs_of_pos (by linarith)
  have hyR : |y| ≤ R := by
    have hlt : |y| < |lam| + 1 := abs_lt.mpr ⟨hy.1, hy.2⟩
    rw [hR]; linarith
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hfk : (0 : ℝ) < (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hGk : 0 < Real.Gamma (a + (k : ℝ)) := Real.Gamma_pos_of_pos (by linarith)
  have hnorm : ‖c k * ((k : ℝ) * y ^ (k - 1)
        / ((Nat.factorial k : ℝ) * Real.Gamma (a + (k : ℝ))))‖
      = (|c k| * ((k : ℝ) * |y| ^ (k - 1))) * (1 / Real.Gamma (a + (k : ℝ)))
        * (1 / (Nat.factorial k : ℝ)) := by
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_mul, abs_pow,
      abs_of_nonneg hk, abs_of_pos (mul_pos hfk hGk)]
    field_simp
  have hpow : (k : ℝ) * |y| ^ (k - 1) ≤ ((k : ℝ) + 1) * R ^ k := by
    have h1 : |y| ^ (k - 1) ≤ R ^ (k - 1) := pow_le_pow_left₀ (abs_nonneg y) hyR _
    have h2 : R ^ (k - 1) ≤ R ^ k := pow_le_pow_right₀ hR1 (Nat.sub_le k 1)
    have h3 : (0 : ℝ) ≤ R ^ k := by positivity
    nlinarith [h1, h2, abs_nonneg y, pow_nonneg (abs_nonneg y) (k - 1)]
  have hGinv : 1 / Real.Gamma (a + (k : ℝ)) ≤ D := by
    rw [hD]
    exact one_div_le_one_div_of_le (by positivity) (Gamma_mul_min_le_Gamma_add ha k)
  have hcb : |c k| * ((k : ℝ) * |y| ^ (k - 1))
      ≤ (C * ((k : ℝ) + 1) ^ j) * (((k : ℝ) + 1) * R ^ k) := by
    refine mul_le_mul (hc k) hpow (by positivity) (by positivity)
  rw [hnorm, habsR]
  calc (|c k| * ((k : ℝ) * |y| ^ (k - 1))) * (1 / Real.Gamma (a + (k : ℝ)))
        * (1 / (Nat.factorial k : ℝ))
      ≤ ((C * ((k : ℝ) + 1) ^ j) * (((k : ℝ) + 1) * R ^ k)) * D
          * (1 / (Nat.factorial k : ℝ)) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul hcb hGinv (by positivity) (by positivity))
          (by positivity)
    _ = C * D * (((k : ℝ) + 1) ^ (j + 1) * (R ^ k / (Nat.factorial k : ℝ))) := by
        rw [pow_succ]; ring

/-- **The `λ`-derivative under the summation sign.**  A weight bounded by
`C(k+1)^j` lets `∂_λ` pass through the `Z`-series, uniformly on
`(-(|λ|+1), |λ|+1)`. -/
theorem hasDerivAt_weightedZ (ha : 0 < a) {c : ℕ → ℝ} {C : ℝ} (j : ℕ)
    (hc : ∀ k, |c k| ≤ C * ((k : ℝ) + 1) ^ j) (lam : ℝ) :
    HasDerivAt (fun x : ℝ => ∑' k : ℕ, c k * zterm a x k)
      (∑' k : ℕ, c k * ((k : ℝ) * lam ^ (k - 1)
          / ((Nat.factorial k : ℝ) * Real.Gamma (a + (k : ℝ))))) lam := by
  have hmem : lam ∈ Ioo (-(|lam| + 1)) (|lam| + 1) :=
    ⟨by linarith [neg_abs_le lam], by linarith [le_abs_self lam]⟩
  obtain ⟨u, hu, hbound⟩ := exists_lam_deriv_bound ha j hc lam
  have hsummable : Summable (fun k : ℕ => c k * zterm a lam k) :=
    (summable_norm_weighted_zterm ha lam j hc).of_norm
  exact hasDerivAt_tsum_of_isPreconnected (u := u) (g := fun k x => c k * zterm a x k)
    (g' := fun k x => c k * ((k : ℝ) * x ^ (k - 1)
        / ((Nat.factorial k : ℝ) * Real.Gamma (a + (k : ℝ)))))
    (t := Ioo (-(|lam| + 1)) (|lam| + 1)) (y₀ := lam) (y := lam) hu isOpen_Ioo
    (convex_Ioo _ _).isPreconnected
    (fun k x _ => (hasDerivAt_zterm_lam a k x).const_mul (c k)) hbound hmem hsummable hmem

/-- Multiplying the termwise `λ`-derivative by `λ` puts the index back in the
numerator: this is `Θ = λ∂_λ` acting coefficientwise. -/
theorem lam_mul_tsum_deriv (a : ℝ) (c : ℕ → ℝ) (lam : ℝ) :
    lam * (∑' k : ℕ, c k * ((k : ℝ) * lam ^ (k - 1)
        / ((Nat.factorial k : ℝ) * Real.Gamma (a + (k : ℝ)))))
      = ∑' k : ℕ, (c k * (k : ℝ)) * zterm a lam k := by
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  match k with
  | 0 => simp [zterm]
  | (n + 1) =>
      rw [zterm, Nat.add_sub_cancel]
      rw [show lam * (c (n + 1) * (((n + 1 : ℕ) : ℝ) * lam ^ n
            / ((Nat.factorial (n + 1) : ℝ) * Real.Gamma (a + ((n + 1 : ℕ) : ℝ)))))
          = c (n + 1) * ((n + 1 : ℕ) : ℝ) * (lam * lam ^ n)
            / ((Nat.factorial (n + 1) : ℝ) * Real.Gamma (a + ((n + 1 : ℕ) : ℝ))) by ring,
        ← pow_succ']
      ring


private theorem bound_one (k : ℕ) : |(1 : ℝ)| ≤ 1 * ((k : ℝ) + 1) ^ 2 := by
  have : (1 : ℝ) ≤ ((k : ℝ) + 1) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
  simpa using this

private theorem bound_idx (k : ℕ) : |(k : ℝ)| ≤ 1 * ((k : ℝ) + 1) ^ 1 := by
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  rw [abs_of_nonneg hk]; nlinarith

private theorem bound_psi (ha : 0 < a) (k : ℕ) :
    |(-realDigamma (a + (k : ℝ)))| ≤ (2 * |realDigamma a| + 1 / a) * ((k : ℝ) + 1) ^ 1 := by
  rw [abs_neg, pow_one]
  exact abs_realDigamma_add_nat_le_linear ha k

/-- **`Z_Θ = λ∂_λ Z`.**  The series `ZEulerSeries` is the Euler derivative of `Z`. -/
theorem ZEulerSeries_eq_euler_deriv (ha : 0 < a) (lam : ℝ) :
    ZEulerSeries a lam = lam * deriv (fun x : ℝ => Zfun a x) lam := by
  have hfun : (fun x : ℝ => Zfun a x) = fun x : ℝ => ∑' k : ℕ, (1 : ℝ) * zterm a x k := by
    funext x; exact Zfun_eq_weighted a x
  rw [hfun, (hasDerivAt_weightedZ (a := a) ha (c := fun _ => (1 : ℝ)) (C := 1) 2
    (fun k => bound_one k) lam).deriv, lam_mul_tsum_deriv a (fun _ => (1 : ℝ)) lam,
    ZEulerSeries]
  exact tsum_congr fun k => by ring

/-- **`Z_{ΘΘ} = Θ²Z`.** -/
theorem ZEuler2Series_eq_euler_deriv (ha : 0 < a) (lam : ℝ) :
    ZEuler2Series a lam = lam * deriv (fun x : ℝ => ZEulerSeries a x) lam := by
  have hfun : (fun x : ℝ => ZEulerSeries a x)
      = fun x : ℝ => ∑' k : ℕ, (k : ℝ) * zterm a x k := rfl
  rw [hfun, (hasDerivAt_weightedZ (a := a) ha (c := fun k : ℕ => (k : ℝ)) (C := 1) 1
    (fun k => bound_idx k) lam).deriv, lam_mul_tsum_deriv a (fun k : ℕ => (k : ℝ)) lam,
    ZEuler2Series]
  exact tsum_congr fun k => by ring

/-- **`Z_{aΘ} = Θ∂_aZ`.**  The Euler derivative of the parameter derivative. -/
theorem ZParamEulerSeries_eq_euler_deriv (ha : 0 < a) (lam : ℝ) :
    ZParamEulerSeries a lam = lam * deriv (fun x : ℝ => ZParamSeries a x) lam := by
  have hfun : (fun x : ℝ => ZParamSeries a x)
      = fun x : ℝ => ∑' k : ℕ, (-realDigamma (a + (k : ℝ))) * zterm a x k := rfl
  rw [hfun, (hasDerivAt_weightedZ (a := a) ha (c := fun k : ℕ => -realDigamma (a + (k : ℝ)))
    (C := 2 * |realDigamma a| + 1 / a) 1 (fun k => bound_psi ha k) lam).deriv,
    lam_mul_tsum_deriv a (fun k : ℕ => -realDigamma (a + (k : ℝ))) lam, ZParamEulerSeries]

/-! ### `eq:Bdef` and `eq:Ckt-def` in the paper's own operators -/

/-- **`eq:Bdef` with `eq:beta`.**  `B = Z² + ZZ_{aΘ} - Z_aZ_Θ = ∑_m S_m β_m λ^m`,
with every derivative the honest one: `∂_a` in the parameter and `Θ = λ∂_λ` in
`λ`. -/
theorem tsum_beta_eq_B (ha : 0 < a) (lam : ℝ) :
    Zfun a lam * Zfun a lam
        + Zfun a lam * (lam * deriv (fun x : ℝ => deriv (fun y : ℝ => Zfun y x) a) lam)
        - deriv (fun y : ℝ => Zfun y lam) a * (lam * deriv (fun x : ℝ => Zfun a x) lam)
      = ∑' m : ℕ, sweight a m * βcoef a m * lam ^ m := by
  have hpar : (fun x : ℝ => deriv (fun y : ℝ => Zfun y x) a) = fun x : ℝ => ZParamSeries a x := by
    funext x; exact (ZParamSeries_eq_deriv ha x).symm
  rw [hpar, ← ZParamEulerSeries_eq_euler_deriv ha, ← ZEulerSeries_eq_euler_deriv ha,
    ← ZParamSeries_eq_deriv ha, ← Bseries]
  exact Bseries_eq_tsum ha lam

/-- **`eq:Ckt-def` with `eq:gamma-kappa`.**
`C_{κ,τ} = τZ² + g(κZZ_Θ - ZZ_{ΘΘ} + Z_Θ²) = ∑_m S_m(τ + g c_m^{(κ)})λ^m`, with
`Θ = λ∂_λ` applied twice for the `Z_{ΘΘ}` term. -/
theorem tsum_gamma_eq_C (ha : 0 < a) (g κ τ lam : ℝ) :
    τ * (Zfun a lam * Zfun a lam)
        + g * (κ * (Zfun a lam * (lam * deriv (fun x : ℝ => Zfun a x) lam))
            - Zfun a lam
                * (lam * deriv (fun x : ℝ => x * deriv (fun y : ℝ => Zfun a y) x) lam)
            + (lam * deriv (fun x : ℝ => Zfun a x) lam)
                * (lam * deriv (fun x : ℝ => Zfun a x) lam))
      = ∑' m : ℕ, sweight a m * (τ + g * ckappa a κ m) * lam ^ m := by
  have heuler : (fun x : ℝ => x * deriv (fun y : ℝ => Zfun a y) x)
      = fun x : ℝ => ZEulerSeries a x := by
    funext x; exact (ZEulerSeries_eq_euler_deriv ha x).symm
  rw [heuler, ← ZEuler2Series_eq_euler_deriv ha, ← ZEulerSeries_eq_euler_deriv ha, ← Cseries]
  exact Cseries_eq_tsum ha g κ τ lam

end TuranBessel
