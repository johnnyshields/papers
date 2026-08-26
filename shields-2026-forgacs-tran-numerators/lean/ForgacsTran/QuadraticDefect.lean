/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.QuasiOrthogonalZeros
import ForgacsTran.QuadraticCase
import ForgacsTran.LaurentReduction

/-!
# The quadratic pencil's reduced defect

`QuasiOrthogonalZeros` proves the count against an abstract weight; this module
supplies the weight and discharges every hypothesis for the pencil.

## Main statements

* `quadWeight` and `quadFavard_orthogonal` — the `p_m` of `QuadraticCase` are
  orthogonal on `closure(I_{Q,1})` against `√((z_+ - z)(z - z_-))`.  Proved
  through `x = -q₁ + 2√(q₀q₂)cos θ`, where the weight is `2√(q₀q₂) sin θ` and
  `p_m` becomes `sin((m+1)θ)`.
* `ftCoeffPoly_linearCombination` — `eq:P-linear-combination` for the
  coefficient polynomials of `AttractorPole`.

## Implementation notes

Sorry-free.

## References

Formalizes `rem:quadratic-case` of `../shields-2026-forgacs-tran-numerators.tex`,
the half that rests on the cited third-party count: at `deg Q = 2`, `r = 1` the
reduced coefficient polynomial `F_M` is a fixed combination of consecutive
members of a Chebyshev system, so Shohat's theorem bounds its reduced defect by
`deg B + 2` at every index.

## Tags

quadratic pencil, reduced defect, weight polynomial
-/

namespace ForgacsTran

open Polynomial Real

/-! ### `∫₀^π sin((m+1)θ) sin((k+1)θ) dθ = 0` -/

private theorem integral_cos_mul_eq_zero {c : ℝ} (hc : c ≠ 0) (hcpi : Real.sin (c * π) = 0) :
    (∫ θ in (0:ℝ)..π, Real.cos (c * θ)) = 0 := by
  have hd : ∀ θ ∈ Set.uIcc (0:ℝ) π,
      HasDerivAt (fun t : ℝ => Real.sin (c * t) / c) (Real.cos (c * θ)) θ := by
    intro θ _
    have h1 : HasDerivAt (fun t : ℝ => c * t) c θ := by
      simpa using (hasDerivAt_id θ).const_mul c
    have h2 : HasDerivAt (fun t : ℝ => Real.sin (c * t)) (Real.cos (c * θ) * c) θ :=
      (Real.hasDerivAt_sin (c * θ)).comp θ h1
    have h3 := h2.div_const c
    rwa [mul_div_assoc, div_self hc, mul_one] at h3
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((Continuous.continuousOn (by fun_prop)).intervalIntegrable)]
  simp [hcpi]

private theorem integral_sin_mul_sin_eq_zero {m k : ℕ} (hmk : m ≠ k) :
    (∫ θ in (0:ℝ)..π, Real.sin (((m : ℝ) + 1) * θ) * Real.sin (((k : ℝ) + 1) * θ)) = 0 := by
  have key : ∀ θ : ℝ, Real.sin (((m : ℝ) + 1) * θ) * Real.sin (((k : ℝ) + 1) * θ)
      = (Real.cos (((m : ℝ) - k) * θ) - Real.cos (((m : ℝ) + k + 2) * θ)) / 2 := by
    intro θ
    have e1 : ((m : ℝ) - k) * θ = ((m : ℝ) + 1) * θ - ((k : ℝ) + 1) * θ := by ring
    have e2 : ((m : ℝ) + k + 2) * θ = ((m : ℝ) + 1) * θ + ((k : ℝ) + 1) * θ := by ring
    rw [e1, e2, Real.cos_sub, Real.cos_add]
    ring
  have hdiff : ((m : ℝ) - k) ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hmk)
  have hsum : ((m : ℝ) + k + 2) ≠ 0 := by positivity
  have hdiffpi : Real.sin (((m : ℝ) - k) * π) = 0 := by
    have : ((m : ℝ) - k) = (((m : ℤ) - (k : ℤ) : ℤ) : ℝ) := by push_cast; ring
    rw [this]; exact Real.sin_int_mul_pi _
  have hsumpi : Real.sin (((m : ℝ) + k + 2) * π) = 0 := by
    have : ((m : ℝ) + k + 2) = ((m + k + 2 : ℕ) : ℝ) := by push_cast; ring
    rw [this]; exact Real.sin_nat_mul_pi _
  rw [intervalIntegral.integral_congr (g := fun θ =>
      (Real.cos (((m : ℝ) - k) * θ) - Real.cos (((m : ℝ) + k + 2) * θ)) / 2)
      fun θ _ => key θ,
    intervalIntegral.integral_div,
    intervalIntegral.integral_sub ((Continuous.continuousOn (by fun_prop)).intervalIntegrable)
      ((Continuous.continuousOn (by fun_prop)).intervalIntegrable),
    integral_cos_mul_eq_zero hdiff hdiffpi, integral_cos_mul_eq_zero hsum hsumpi]
  norm_num

/-! ### The weight, and orthogonality of the Favard branch -/

/-- `rem:quadratic-case` — the lower endpoint of `I_{Q,1}`. -/
noncomputable def quadLow (q0 q1 q2 : ℝ) : ℝ := -q1 - 2 * Real.sqrt (q0 * q2)

/-- `rem:quadratic-case` — the upper endpoint of `I_{Q,1}`. -/
noncomputable def quadHigh (q0 q1 q2 : ℝ) : ℝ := -q1 + 2 * Real.sqrt (q0 * q2)

/-- The weight the Favard branch `p_m` is orthogonal against on
`closure(I_{Q,1})`: the Chebyshev weight of the second kind, pulled back through
`rem:quadratic-case`'s `z(θ)`. -/
noncomputable def quadWeight (q0 q1 q2 : ℝ) (x : ℝ) : ℝ :=
  Real.sqrt ((quadHigh q0 q1 q2 - x) * (x - quadLow q0 q1 q2))

theorem continuous_quadWeight (q0 q1 q2 : ℝ) : Continuous (quadWeight q0 q1 q2) := by
  unfold quadWeight quadHigh quadLow
  fun_prop

theorem quadLow_lt_quadHigh {q0 q2 : ℝ} (hq0 : 0 < q0) (hq2 : 0 < q2) (q1 : ℝ) :
    quadLow q0 q1 q2 < quadHigh q0 q1 q2 := by
  have hs : 0 < Real.sqrt (q0 * q2) := Real.sqrt_pos.mpr (by positivity)
  unfold quadLow quadHigh
  linarith

theorem quadWeight_pos {q0 q1 q2 x : ℝ}
    (hx : x ∈ Set.Ioo (quadLow q0 q1 q2) (quadHigh q0 q1 q2)) : 0 < quadWeight q0 q1 q2 x :=
  Real.sqrt_pos.2 (mul_pos (by linarith [hx.2]) (by linarith [hx.1]))

private theorem integral_subst_cos (c s : ℝ) {G : ℝ → ℝ} (hG : Continuous G) :
    (∫ x in (c - 2 * s)..(c + 2 * s), G x)
      = ∫ θ in π..(0 : ℝ), G (c + 2 * s * Real.cos θ) * (-(2 * s * Real.sin θ)) := by
  have hf : ∀ θ ∈ Set.uIcc π (0 : ℝ),
      HasDerivAt (fun t : ℝ => c + 2 * s * Real.cos t) (-(2 * s * Real.sin θ)) θ := by
    intro θ _
    have h := (Real.hasDerivAt_cos θ).const_mul (2 * s)
    rw [show 2 * s * -Real.sin θ = -(2 * s * Real.sin θ) by ring] at h
    exact h.const_add c
  have hcont : ContinuousOn (fun θ : ℝ => -(2 * s * Real.sin θ)) (Set.uIcc π (0 : ℝ)) := by
    fun_prop
  have hsub := intervalIntegral.integral_comp_mul_deriv hf hcont hG
  simp only [Function.comp_apply] at hsub
  rw [show c - 2 * s = c + 2 * s * Real.cos π by rw [Real.cos_pi]; ring,
    show c + 2 * s = c + 2 * s * Real.cos 0 by rw [Real.cos_zero]; ring, ← hsub]

/-- **`rem:quadratic-case`, `Q4` completed.**  The Favard branch of the
quadratic pencil is an orthogonal system on `closure(I_{Q,1})` against
`quadWeight`.  This is the hypothesis `QuasiOrthogonalZeros` needs and the one
`rem:quadratic-case` leaves implicit in the phrase "the classical
quasi-orthogonal case".

**Differs from the paper's route.**  The paper names the case classical and
takes the orthogonality of the Chebyshev system as known.  Mathlib carries the
first-kind orthogonality only, so the second-kind relation is proved here
through `x = -q₁ + 2√(q₀q₂)cos θ`, under which the weight becomes
`2√(q₀q₂) sin θ` and `p_m` becomes `√(q₀q₂)^m sin((m+1)θ)/sin θ`; the two sines
cancel the two weights and what is left is
`∫₀^π sin((m+1)θ)sin((k+1)θ)dθ`. -/
theorem quadFavard_orthogonal {q0 q2 : ℝ} (hq0 : 0 < q0) (hq2 : 0 < q2) (q1 : ℝ)
    {m k : ℕ} (hmk : m ≠ k) :
    (∫ x in (quadLow q0 q1 q2)..(quadHigh q0 q1 q2),
        (quadFavard q0 q1 q2 m).eval x * (quadFavard q0 q1 q2 k).eval x * quadWeight q0 q1 q2 x)
      = 0 := by
  set s := Real.sqrt (q0 * q2) with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hG : Continuous fun x : ℝ =>
      (quadFavard q0 q1 q2 m).eval x * (quadFavard q0 q1 q2 k).eval x * quadWeight q0 q1 q2 x :=
    ((quadFavard q0 q1 q2 m).continuous.mul (quadFavard q0 q1 q2 k).continuous).mul
      (continuous_quadWeight q0 q1 q2)
  have hlo : quadLow q0 q1 q2 = -q1 - 2 * s := rfl
  have hhi : quadHigh q0 q1 q2 = -q1 + 2 * s := rfl
  rw [hlo, hhi, integral_subst_cos (-q1) s hG]
  have hkey : ∀ θ ∈ Set.uIcc π (0 : ℝ),
      ((quadFavard q0 q1 q2 m).eval (-q1 + 2 * s * Real.cos θ)
          * (quadFavard q0 q1 q2 k).eval (-q1 + 2 * s * Real.cos θ)
          * quadWeight q0 q1 q2 (-q1 + 2 * s * Real.cos θ))
            * (-(2 * s * Real.sin θ))
        = -(4 * s ^ (m + k + 2))
            * (Real.sin (((m : ℝ) + 1) * θ) * Real.sin (((k : ℝ) + 1) * θ)) := by
    intro θ hθ
    rw [Set.uIcc_of_ge pi_pos.le] at hθ
    have hsin : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2
    have hcos : ((-q1 + 2 * s * Real.cos θ) + q1) / (2 * s) = Real.cos θ := by
      field
    have hpm := quadFavard_eval_eq_chebyshev hq0 hq2 q1 m (-q1 + 2 * s * Real.cos θ)
    have hpk := quadFavard_eval_eq_chebyshev hq0 hq2 q1 k (-q1 + 2 * s * Real.cos θ)
    rw [← hs, hcos] at hpm hpk
    have hw : quadWeight q0 q1 q2 (-q1 + 2 * s * Real.cos θ) = 2 * s * Real.sin θ := by
      change Real.sqrt ((-q1 + 2 * s - (-q1 + 2 * s * Real.cos θ))
          * ((-q1 + 2 * s * Real.cos θ) - (-q1 - 2 * s))) = 2 * s * Real.sin θ
      have hpy : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by
        have h := Real.sin_sq_add_cos_sq θ; linarith
      have hsq : (-q1 + 2 * s - (-q1 + 2 * s * Real.cos θ))
          * ((-q1 + 2 * s * Real.cos θ) - (-q1 - 2 * s)) = (2 * s * Real.sin θ) ^ 2 := by
        calc (-q1 + 2 * s - (-q1 + 2 * s * Real.cos θ))
              * ((-q1 + 2 * s * Real.cos θ) - (-q1 - 2 * s))
            = 4 * s ^ 2 * (1 - Real.cos θ ^ 2) := by ring
          _ = 4 * s ^ 2 * Real.sin θ ^ 2 := by rw [← hpy]
          _ = (2 * s * Real.sin θ) ^ 2 := by ring
      rw [hsq, Real.sqrt_sq (by positivity)]
    rw [hpm, hpk, hw]
    have hUm := Polynomial.Chebyshev.U_real_cos (θ := θ) (n := (m : ℤ))
    have hUk := Polynomial.Chebyshev.U_real_cos (θ := θ) (n := (k : ℤ))
    push_cast at hUm hUk
    calc s ^ m * (Polynomial.Chebyshev.U ℝ (m : ℤ)).eval (Real.cos θ)
            * (s ^ k * (Polynomial.Chebyshev.U ℝ (k : ℤ)).eval (Real.cos θ))
            * (2 * s * Real.sin θ) * (-(2 * s * Real.sin θ))
        = -(4 * s ^ (m + k + 2))
            * (((Polynomial.Chebyshev.U ℝ (m : ℤ)).eval (Real.cos θ) * Real.sin θ)
              * ((Polynomial.Chebyshev.U ℝ (k : ℤ)).eval (Real.cos θ) * Real.sin θ)) := by
          rw [pow_add, pow_add]; ring
      _ = -(4 * s ^ (m + k + 2))
            * (Real.sin (((m : ℝ) + 1) * θ) * Real.sin (((k : ℝ) + 1) * θ)) := by
          rw [hUm, hUk]
  rw [intervalIntegral.integral_congr hkey, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_symm, integral_sin_mul_sin_eq_zero hmk]
  ring

/-! ### The count, and the reduced defect -/

/-- `rem:quadratic-case`'s `F_M`, cleared of the nonzero scalar
`1/(q₀(-q₀)^M)`: the fixed combination `∑_j b_j(-q₀)^j p_{M-j}` of
`eq:P-linear-combination`.  `quadReduced_eval_eq_ftCoeffPoly` identifies it with
the coefficient polynomial. -/
noncomputable def quadReduced (q0 q1 q2 : ℝ) (B : Polynomial ℝ) (M : ℕ) : Polynomial ℝ :=
  ∑ j ∈ Finset.range (M + 1), C (B.coeff j * (-q0) ^ j) * quadFavard q0 q1 q2 (M - j)

private theorem quadFavard_natDegree (q0 q1 q2 : ℝ) (m : ℕ) :
    (quadFavard q0 q1 q2 m).natDegree = m := (quadFavard_monic_natDegree q0 q1 q2 m).2

private theorem quadFavard_ne_zero (q0 q1 q2 : ℝ) (m : ℕ) : quadFavard q0 q1 q2 m ≠ 0 :=
  (quadFavard_monic_natDegree q0 q1 q2 m).1.ne_zero

theorem quadReduced_eq_range_natDegree {q0 q1 q2 : ℝ} (B : Polynomial ℝ) {M : ℕ}
    (hM : B.natDegree ≤ M) :
    quadReduced q0 q1 q2 B M
      = ∑ j ∈ Finset.range (B.natDegree + 1),
          C (B.coeff j * (-q0) ^ j) * quadFavard q0 q1 q2 (M - j) := by
  have hsubset : Finset.range (B.natDegree + 1) ⊆ Finset.range (M + 1) := by
    intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  refine (Finset.sum_subset hsubset fun j hj hj' => ?_).symm
  have hjd : B.natDegree < j := by
    by_contra hcon
    exact hj' (Finset.mem_range.2 (by omega))
  rw [coeff_eq_zero_of_natDegree_lt hjd, zero_mul, map_zero, zero_mul]

theorem quadReduced_coeff_top {q0 q1 q2 : ℝ} (B : Polynomial ℝ) (M : ℕ) :
    (quadReduced q0 q1 q2 B M).coeff M = B.coeff 0 := by
  rw [quadReduced, finsetSum_coeff]
  refine (Finset.sum_eq_single 0 (fun j hj hj0 => ?_) (fun h => ?_)).trans ?_
  · have hjM : j < M + 1 := Finset.mem_range.1 hj
    have hz : (quadFavard q0 q1 q2 (M - j)).coeff M = 0 :=
      coeff_eq_zero_of_natDegree_lt (by rw [quadFavard_natDegree]; omega)
    rw [coeff_C_mul, hz, mul_zero]
  · exact absurd (Finset.mem_range.2 (Nat.succ_pos M)) h
  · rw [coeff_C_mul, Nat.sub_zero, pow_zero, mul_one]
    have := (quadFavard_monic_natDegree q0 q1 q2 M).1
    rw [Monic, leadingCoeff, quadFavard_natDegree] at this
    rw [this, mul_one]

theorem quadReduced_natDegree {q0 q1 q2 : ℝ} {B : Polynomial ℝ} (hB : B.coeff 0 ≠ 0) (M : ℕ) :
    (quadReduced q0 q1 q2 B M).natDegree = M := by
  refine le_antisymm ?_ (le_natDegree_of_ne_zero (by rw [quadReduced_coeff_top]; exact hB))
  refine natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [quadFavard_natDegree]
  omega

/-- **`rem:quadratic-case`, the cited count, instantiated.**  For `M ≥ deg B`
and `B(0) ≠ 0`, the reduced coefficient polynomial vanishes to odd order at at
least `M - deg B` points of `I_{Q,1}`.

**Differs from the paper's route.**  The paper reads the count off
`Duran2026LinearCombinations` in the closed interval and concedes two endpoints
to reach the open one, so it states `M - deg B - 2`.  `card_oddOrderRoots_ge`
locates the zeros in the open interval directly — its sign argument never needs
an endpoint — so the concession is not made here and the count is two better.
`quadReduced_card_interior_ge` still records the paper's own `M - deg B - 2`,
through the concession, so both statements stand in the tree.

The concession is not idle bookkeeping: a weight can be chosen so that the
reduced coefficient polynomial vanishes exactly at an endpoint of `I_{Q,1}`, and
`scripts/check_shohat_open_interval.py` constructs one at every index it tests.
What the count above does with such a zero is charge it against `deg B` rather
than against a separate allowance of two.

The cited lemma's `γ_K ≠ 0` costs nothing here.  `K` is `B.natDegree`, so the
coefficient in question is `B.leadingCoeff · (-q₀)^K`, nonzero for every `B` the
hypothesis `B.coeff 0 ≠ 0` already rules in. -/
theorem quadReduced_card_oddOrderRoots_ge {q0 q2 : ℝ} (hq0 : 0 < q0) (hq2 : 0 < q2) (q1 : ℝ)
    {B : Polynomial ℝ} (hB : B.coeff 0 ≠ 0) {M : ℕ} (hM : B.natDegree ≤ M) :
    M - B.natDegree
      ≤ (oddOrderRoots (quadReduced q0 q1 q2 B M)
          (quadLow q0 q1 q2) (quadHigh q0 q1 q2)).card := by
  refine card_oddOrderRoots_linearCombination_ge (quadLow_lt_quadHigh hq0 hq2 q1)
    (continuous_quadWeight q0 q1 q2).continuousOn (fun x hx => quadWeight_pos hx)
    (quadFavard_natDegree q0 q1 q2) (quadFavard_ne_zero q0 q1 q2)
    (fun m k hmk => quadFavard_orthogonal hq0 hq2 q1 hmk) hM
    (γ := fun j => B.coeff j * (-q0) ^ j) ?_ (quadReduced_eq_range_natDegree B hM)
  simpa using hB

/-- **`rem:quadratic-case`, the defect bound.**  At most `deg B` zeros of the
reduced coefficient polynomial lie outside `I_{Q,1}`, counted with multiplicity
— the paper's `deg B + 2` with the two endpoints it conceded restored. -/
theorem quadReduced_card_outside_le {q0 q2 : ℝ} (hq0 : 0 < q0) (hq2 : 0 < q2) (q1 : ℝ)
    {B : Polynomial ℝ} (hB : B.coeff 0 ≠ 0) {M : ℕ} (hM : B.natDegree ≤ M) :
    M - ((quadReduced q0 q1 q2 B M).roots.filter
          (fun x => x ∈ Set.Ioo (quadLow q0 q1 q2) (quadHigh q0 q1 q2))).card
      ≤ B.natDegree := by
  classical
  have hPne : quadReduced q0 q1 q2 B M ≠ 0 := fun h => hB (by
    have hc := quadReduced_coeff_top (q0 := q0) (q1 := q1) (q2 := q2) B M
    rw [h, coeff_zero] at hc
    exact hc.symm)
  have hcount := quadReduced_card_oddOrderRoots_ge hq0 hq2 q1 hB hM
  have hsub : oddOrderRoots (quadReduced q0 q1 q2 B M) (quadLow q0 q1 q2) (quadHigh q0 q1 q2)
      ⊆ ((quadReduced q0 q1 q2 B M).roots.filter
          (fun x => x ∈ Set.Ioo (quadLow q0 q1 q2) (quadHigh q0 q1 q2))).toFinset := by
    intro ξ hξ
    obtain ⟨hmem, hodd⟩ := (mem_oddOrderRoots hPne).1 hξ
    simp only [Multiset.mem_toFinset, Multiset.mem_filter, mem_roots hPne]
    exact ⟨(rootMultiplicity_pos hPne).1 hodd.pos, hmem⟩
  have hle : (oddOrderRoots (quadReduced q0 q1 q2 B M)
        (quadLow q0 q1 q2) (quadHigh q0 q1 q2)).card
      ≤ ((quadReduced q0 q1 q2 B M).roots.filter
          (fun x => x ∈ Set.Ioo (quadLow q0 q1 q2) (quadHigh q0 q1 q2))).card :=
    (Finset.card_le_card hsub).trans (Multiset.toFinset_card_le _)
  omega

/-! ### `eq:P-linear-combination` for the coefficient polynomials -/

/-- The coefficient polynomials of `prop:isolated-dominant-cancellation` satisfy
the denominator recurrence of `eq:H-generating` with right-hand side `b_M`. -/
theorem denomConv_ftCoeffPoly (Q B : ℂ[X]) {r : ℕ} (hr : 1 ≤ r) (hQ0 : Q.coeff 0 ≠ 0) (M : ℕ) :
    denomConv (ftDenom Q r) (ftCoeffPoly Q B r) M = C (B.coeff M) := by
  have hS : ∑ i ∈ Finset.range M, ftDenom Q r (i + 1) * ftCoeffPoly Q B r (M - (i + 1))
      = ∑ i ∈ Finset.range M, ftDenCoeff Q r (M - i) * ftCoeffPoly Q B r i := by
    rw [← Finset.sum_range_reflect (fun i => ftDenCoeff Q r (M - i) * ftCoeffPoly Q B r i) M]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjM : j < M := Finset.mem_range.1 hj
    rw [show M - 1 - j = M - (j + 1) by omega, show M - (M - (j + 1)) = j + 1 by omega]
    rfl
  have hCC : (C (Q.coeff 0) : ℂ[X]) * C (Q.coeff 0)⁻¹ = 1 := by
    rw [← C_mul, mul_inv_cancel₀ hQ0, C_1]
  rw [denomConv, Finset.sum_range_succ', hS, ftDenom_zero Q hr, Nat.sub_zero,
    ftCoeffPoly_eq Q B r M, ← mul_assoc, hCC, one_mul]
  ring

/-- **Paper `eq:P-linear-combination`, for `ftCoeffPoly`.**  Writing
`B = ∑_j b_j t^j`, the coefficient polynomial of the weight `B` is the fixed
finite combination `F_M = ∑_j b_j H_{M-j}` of the denominator-only sequence
`H = ftCoeffPoly Q 1 r`. -/
theorem ftCoeffPoly_linearCombination (Q B : ℂ[X]) {r : ℕ} (hr : 1 ≤ r) (hQ0 : Q.coeff 0 ≠ 0)
    (M : ℕ) :
    ftCoeffPoly Q B r M
      = ∑ j ∈ Finset.range (M + 1), C (B.coeff j) * ftCoeffPoly Q 1 r (M - j) := by
  refine reduced_tail_linear_combination Q hr hQ0 B (ftCoeffPoly Q 1 r) (ftCoeffPoly Q B r)
    (fun N => ?_) (fun N => denomConv_ftCoeffPoly Q B hr hQ0 N) M
  rw [denomConv_ftCoeffPoly Q 1 hr hQ0 N, Polynomial.coeff_one]
  split <;> simp

/-! ### The identification with `F_M`, and the paper's statement -/

/-- **`rem:quadratic-case`, `Q5`.**  `quadReduced` is the reduced coefficient
polynomial `F_M` of the pencil, cleared of the scalar `1/(q₀(-q₀)^M)` — this is
`eq:P-linear-combination` written in the Favard normalization. -/
theorem quadReduced_eval_eq_ftCoeffPoly {q0 : ℝ} (hq0 : 0 < q0) (q1 q2 : ℝ)
    (B : Polynomial ℝ) (M : ℕ) (z : ℝ) :
    (((quadReduced q0 q1 q2 B M).eval z : ℝ) : ℂ)
      = ((q0 : ℝ) : ℂ) * (-((q0 : ℝ) : ℂ)) ^ M
        * (ftCoeffPoly (quadPoly q0 q1 q2) (B.map (algebraMap ℝ ℂ)) 1 M).eval ((z : ℝ) : ℂ) := by
  have hQ0 : (quadPoly q0 q1 q2).coeff 0 ≠ 0 := by
    have : (quadPoly q0 q1 q2).coeff 0 = ((q0 : ℝ) : ℂ) := by
      simp [quadPoly]
    rw [this]
    simpa using hq0.ne'
  rw [ftCoeffPoly_linearCombination _ _ le_rfl hQ0 M, quadReduced]
  push_cast [eval_finsetSum, eval_mul, eval_C]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjM : j < M + 1 := Finset.mem_range.1 hj
  have hpj := quadFavard_eval_eq_coeffPoly (q0 := q0) (q1 := q1) (q2 := q2) hq0 (M - j) z
  rw [coeff_map]
  rw [hpj]
  have hpow : (-((q0 : ℝ) : ℂ)) ^ j * (-((q0 : ℝ) : ℂ)) ^ (M - j) = (-((q0 : ℝ) : ℂ)) ^ M := by
    rw [← pow_add, show j + (M - j) = M by omega]
  calc ((B.coeff j : ℝ) : ℂ) * (-((q0 : ℝ) : ℂ)) ^ j
        * (((q0 : ℝ) : ℂ) * (-((q0 : ℝ) : ℂ)) ^ (M - j)
          * (ftCoeffPoly (quadPoly q0 q1 q2) 1 1 (M - j)).eval ((z : ℝ) : ℂ))
      = ((q0 : ℝ) : ℂ) * ((-((q0 : ℝ) : ℂ)) ^ j * (-((q0 : ℝ) : ℂ)) ^ (M - j))
        * (((B.coeff j : ℝ) : ℂ)
          * (ftCoeffPoly (quadPoly q0 q1 q2) 1 1 (M - j)).eval ((z : ℝ) : ℂ)) := by ring
    _ = ((q0 : ℝ) : ℂ) * (-((q0 : ℝ) : ℂ)) ^ M
        * (((B.coeff j : ℝ) : ℂ)
          * (ftCoeffPoly (quadPoly q0 q1 q2) 1 1 (M - j)).eval ((z : ℝ) : ℂ)) := by rw [hpow]

/-- **`rem:quadratic-case`, the count as the paper states it.**  For `M ≥ deg B`
and `B(0) ≠ 0`, the reduced coefficient polynomial of the quadratic pencil has
at least `M - deg B` distinct real zeros in `I_{Q,1}`.  The paper claims
`M - deg B - 2` distinct zeros there, which this implies. -/
theorem ftCoeffPoly_quadratic_card_interior_ge {q0 q2 : ℝ} (hq0 : 0 < q0) (hq2 : 0 < q2) (q1 : ℝ)
    {B : Polynomial ℝ} (hB : B.coeff 0 ≠ 0) {M : ℕ} (hM : B.natDegree ≤ M) :
    ∃ S : Finset ℝ, M - B.natDegree ≤ S.card
      ∧ (∀ x ∈ S, x ∈ Set.Ioo (quadLow q0 q1 q2) (quadHigh q0 q1 q2))
      ∧ ∀ x ∈ S,
          (ftCoeffPoly (quadPoly q0 q1 q2) (B.map (algebraMap ℝ ℂ)) 1 M).eval ((x : ℝ) : ℂ)
            = 0 := by
  have hPne : quadReduced q0 q1 q2 B M ≠ 0 := fun h => hB (by
    have hc := quadReduced_coeff_top (q0 := q0) (q1 := q1) (q2 := q2) B M
    rw [h, coeff_zero] at hc
    exact hc.symm)
  refine ⟨oddOrderRoots (quadReduced q0 q1 q2 B M) (quadLow q0 q1 q2) (quadHigh q0 q1 q2),
    quadReduced_card_oddOrderRoots_ge hq0 hq2 q1 hB hM,
    fun x hx => ((mem_oddOrderRoots hPne).1 hx).1, fun x hx => ?_⟩
  have hroot : (quadReduced q0 q1 q2 B M).eval x = 0 :=
    (rootMultiplicity_pos hPne).1 ((mem_oddOrderRoots hPne).1 hx).2.pos
  have hbridge := quadReduced_eval_eq_ftCoeffPoly hq0 q1 q2 B M x
  rw [hroot] at hbridge
  have hq0c : ((q0 : ℝ) : ℂ) ≠ 0 := by simpa using hq0.ne'
  have hne : ((q0 : ℝ) : ℂ) * (-((q0 : ℝ) : ℂ)) ^ M ≠ 0 :=
    mul_ne_zero hq0c (pow_ne_zero _ (neg_ne_zero.2 hq0c))
  simpa [hne] using (mul_eq_zero.1 (by simpa using hbridge.symm)).resolve_left hne

/-- **`rem:quadratic-case` as the remark writes it.**  The remark's own sentence
— at least `M - deg B - 2` distinct zeros in `I_{Q,1}` — obtained by feeding the
count into `card_Ioo_ge_of_card_Icc`, the endpoint concession.  It is weaker than
`quadReduced_card_oddOrderRoots_ge` by exactly the two endpoints the concession
gives away, and is recorded so that the paper's literal claim, and the step
`card_Ioo_ge_of_card_Icc` exists for, are both discharged in the tree. -/
theorem quadReduced_card_interior_ge {q0 q2 : ℝ} (hq0 : 0 < q0) (hq2 : 0 < q2) (q1 : ℝ)
    {B : Polynomial ℝ} (hB : B.coeff 0 ≠ 0) {M : ℕ} (hM : B.natDegree ≤ M) :
    M - B.natDegree - 2
      ≤ ((oddOrderRoots (quadReduced q0 q1 q2 B M) (quadLow q0 q1 q2) (quadHigh q0 q1 q2)).filter
          (fun x => quadLow q0 q1 q2 < x ∧ x < quadHigh q0 q1 q2)).card := by
  have hPne : quadReduced q0 q1 q2 B M ≠ 0 := fun h => hB (by
    have hc := quadReduced_coeff_top (q0 := q0) (q1 := q1) (q2 := q2) B M
    rw [h, coeff_zero] at hc
    exact hc.symm)
  exact card_Ioo_ge_of_card_Icc (quadReduced_card_oddOrderRoots_ge hq0 hq2 q1 hB hM)
    fun x hx => Set.Ioo_subset_Icc_self ((mem_oddOrderRoots hPne).1 hx).1

end ForgacsTran
