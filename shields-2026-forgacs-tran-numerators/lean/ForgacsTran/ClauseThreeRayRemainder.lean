/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.ClauseThreeQuadraticRay
import ForgacsTran.DominanceFT
import ForgacsTran.ClauseThreeComposition
import ForgacsTran.ClauseThreeWitness

/-!
# No remainder on the `r = 2` branch

`D(t,z) = q_0 + q_1t + (q_2+z)t^2` is quadratic in `t`, so the principal pair exhausts it and
the decomposition is exact — `R_M ≡ 0`, hence `eq:dominance-bound` holds on the whole arc
with no deleted window.  That is the same conclusion `QuadraticWitness.quad_ftRemainder_eq_zero`
reaches for the Favard pencil, but there the modulus is constant; here `τ(θ)` varies and
vanishes at the upper endpoint, and the cancellation still goes through because both sides carry
the same power of `τ`.

This module is separated from `ClauseThreeQuadraticRay` because `ftRemainder` and `ftPrincipal`
live in `DominanceFT`; everything algebraic about the branch is proved there, on `sec:reduction`
and `AttractorPole` alone.

## Implementation notes

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, `eq:principal-decomposition` for the
`r > 1` pencil of `ClauseThreeQuadraticRay`.

## Tags

remainder estimate, denominator pencil, defect
-/

namespace ForgacsTran

open Polynomial

/-- `\operatorname{Re}(ia/c · e^{iy}) = -asin y/c`. -/
private theorem ray_I_mul_div_exp_re {a c y : ℝ} (hc : c ≠ 0) :
    (Complex.I * ((a : ℝ) : ℂ) / ((c : ℝ) : ℂ)
        * Complex.exp (((y : ℝ) : ℂ) * Complex.I)).re
      = -(a * Real.sin y) / c := by
  have hcne : ((c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc
  have hval : Complex.I * ((a : ℝ) : ℂ) / ((c : ℝ) : ℂ)
      * Complex.exp (((y : ℝ) : ℂ) * Complex.I)
      = ((((-(a * Real.sin y) / c : ℝ))) : ℂ)
        + ((((a * Real.cos y / c : ℝ))) : ℂ) * Complex.I := by
    rw [Complex.ofReal_div, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_mul,
      Complex.ofReal_mul, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    field_simp
    linear_combination (((a : ℝ) : ℂ) * ((Real.sin y : ℝ) : ℂ)) * Complex.I_sq
  rw [hval]
  simp [Complex.sin_ofReal_re]

/-- **`eq:principal-decomposition` is exact on the `r = 2` branch.**  The pair exhausts a
quadratic denominator whatever the modulus does, so `R_M ≡ 0` — and therefore
`eq:dominance-bound` holds on the whole arc, with no deleted window and no threshold in `M`.

The two sides meet at `τsin((M+1)θ)/(q_0sinθ)`: the coefficient side by
`ray_coeffPoly_on_arc`, the principal side because `τ^{M+1}/t_+^{M+1} = e^{-i(M+1)θ}`
cancels the varying modulus exactly. -/
theorem ray_ftRemainder_eq_zero {q0 q1 q2 : ℝ} (hq0 : 0 < q0) (hq1 : q1 < 0) {θ : ℝ}
    (hcos : 0 < Real.cos θ) (hsin : 0 < Real.sin θ) (M : ℕ) :
    ftRemainder (quadPoly q0 q1 q2) 1 2 (rayZ q0 q1 q2) (rayTau q0 q1) M θ = 0 := by
  have hτ : 0 < rayTau q0 q1 θ := rayTau_pos hq0 hq1 hcos
  have hτc : ((rayTau q0 q1 θ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hτ.ne'
  have hsc : ((Real.sin θ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsin.ne'
  have hqc : ((q0 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hq0.ne'
  have hq0r : q0 ≠ 0 := hq0.ne'
  have hsr : Real.sin θ ≠ 0 := hsin.ne'
  have hden : (2 * q0 * Real.sin θ) ≠ 0 := by positivity
  have hE : Complex.exp ((θ : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  set φ : ℝ := ((M + 1 : ℕ) : ℝ) * θ with hφ
  -- the principal quotient loses the modulus entirely
  have hquot : ((rayTau q0 q1 θ : ℝ) : ℂ) ^ (M + 1)
      / (((rayTau q0 q1 θ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ^ (M + 1)
      = Complex.exp (((-φ : ℝ) : ℂ) * Complex.I) := by
    rw [mul_pow, div_mul_eq_div_div, div_self (pow_ne_zero _ hτc), one_div,
      ← Complex.exp_nat_mul, ← Complex.exp_neg]
    congr 1
    rw [hφ]
    push_cast
    ring
  -- the coefficient side
  have harc := ray_coeffPoly_on_arc (q2 := q2) hq0 hq1 hcos M
  have hterm1 : ((rayTau q0 q1 θ : ℝ) : ℂ) ^ (M + 1)
      * (ftCoeffPoly (quadPoly q0 q1 q2) 1 2 M).eval (((rayZ q0 q1 q2 θ : ℝ)) : ℂ)
      = ((rayTau q0 q1 θ * Real.sin φ / (q0 * Real.sin θ) : ℝ) : ℂ) := by
    have hM : ((rayTau q0 q1 θ : ℝ) : ℂ) ^ (M + 1)
        = ((rayTau q0 q1 θ : ℝ) : ℂ) ^ M * ((rayTau q0 q1 θ : ℝ) : ℂ) := by ring
    rw [hM, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_mul]
    field_simp
    linear_combination harc
  rw [ftRemainder,
    show ftPrincipal (rayTau q0 q1) θ
      = ((rayTau q0 q1 θ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) from rfl,
    ray_ftAmp hq0 hq1 hcos hsin, hterm1]
  -- the principal side
  have hre : (((rayTau q0 q1 θ : ℝ) : ℂ) ^ (M + 1)
      * (Complex.I * ((rayTau q0 q1 θ : ℝ) : ℂ)
          / (2 * ((q0 : ℝ) : ℂ) * ((Real.sin θ : ℝ) : ℂ))
        / (((rayTau q0 q1 θ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ^ (M + 1))).re
      = rayTau q0 q1 θ * Real.sin φ / (2 * q0 * Real.sin θ) := by
    rw [show ((rayTau q0 q1 θ : ℝ) : ℂ) ^ (M + 1)
        * (Complex.I * ((rayTau q0 q1 θ : ℝ) : ℂ)
            / (2 * ((q0 : ℝ) : ℂ) * ((Real.sin θ : ℝ) : ℂ))
          / (((rayTau q0 q1 θ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ^ (M + 1))
        = (Complex.I * ((rayTau q0 q1 θ : ℝ) : ℂ)
            / (2 * ((q0 : ℝ) : ℂ) * ((Real.sin θ : ℝ) : ℂ)))
          * (((rayTau q0 q1 θ : ℝ) : ℂ) ^ (M + 1)
            / (((rayTau q0 q1 θ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ^ (M + 1)) by
      ring]
    rw [hquot, show (2 * ((q0 : ℝ) : ℂ) * ((Real.sin θ : ℝ) : ℂ))
        = ((2 * q0 * Real.sin θ : ℝ) : ℂ) by push_cast; ring]
    rw [ray_I_mul_div_exp_re hden, Real.sin_neg]
    ring
  rw [hre, ← Complex.ofReal_sub,
    show rayTau q0 q1 θ * Real.sin φ / (q0 * Real.sin θ)
        - 2 * (rayTau q0 q1 θ * Real.sin φ / (2 * q0 * Real.sin θ)) = 0 by
      field_simp; ring]
  simp


/-! ### The branch in `ftPrincipal` form

`ClauseThreeQuadraticRay` writes the principal branch as `τ e^{iθ}` so that it can stay
off `DominanceFT`.  `FTChainGeom` asks for it as `ftPrincipal`, and the two are the same term;
these restate the branch facts in the form the geometry bundle consumes. -/

theorem ray_ftPrincipal_eq (q0 q1 : ℝ) (θ : ℝ) :
    ftPrincipal (rayTau q0 q1) θ
      = ((rayTau q0 q1 θ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := rfl

theorem ray_ftAmp_ne_zero {q0 q1 q2 : ℝ} (hq0 : 0 < q0) (hq1 : q1 < 0) {θ : ℝ}
    (hcos : 0 < Real.cos θ) (hsin : 0 < Real.sin θ) :
    ftAmp (quadPoly q0 q1 q2) 1 2 (((rayZ q0 q1 q2 θ : ℝ)) : ℂ)
      (ftPrincipal (rayTau q0 q1) θ) ≠ 0 := by
  have hden : (0 : ℝ) < 2 * q0 * Real.sin θ := by positivity
  have hτ : 0 < rayTau q0 q1 θ := rayTau_pos hq0 hq1 hcos
  rw [ray_ftPrincipal_eq, ray_ftAmp hq0 hq1 hcos hsin]
  refine div_ne_zero (mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hτ.ne')) ?_
  rw [show (2 * ((q0 : ℝ) : ℂ) * ((Real.sin θ : ℝ) : ℂ))
      = ((2 * q0 * Real.sin θ : ℝ) : ℂ) by push_cast; ring]
  exact_mod_cast hden.ne'

/-- `|W(θ)| = τ(θ)/(2q_0sinθ)`, in the `ftPrincipalAmp` spelling. -/
theorem ray_ftPrincipalAmp {q0 q1 q2 : ℝ} (hq0 : 0 < q0) (hq1 : q1 < 0) {θ : ℝ}
    (hcos : 0 < Real.cos θ) (hsin : 0 < Real.sin θ) :
    ftPrincipalAmp (quadPoly q0 q1 q2) 1 2 (rayZ q0 q1 q2) (rayTau q0 q1) θ
      = rayTau q0 q1 θ / (2 * q0 * Real.sin θ) := by
  rw [ftPrincipalAmp, ray_ftPrincipal_eq, ray_norm_ftAmp hq0 hq1 hcos hsin]

/-- **The polar form `FTChainGeom` consumes**, with the constant branch `ψ ≡ π/2`. -/
theorem ray_polar_ftPrincipal {q0 q1 q2 : ℝ} (hq0 : 0 < q0) (hq1 : q1 < 0) {θ : ℝ}
    (hcos : 0 < Real.cos θ) (hsin : 0 < Real.sin θ) :
    ftAmp (quadPoly q0 q1 q2) 1 2 (((rayZ q0 q1 q2 θ : ℝ)) : ℂ)
        (ftPrincipal (rayTau q0 q1) θ)
      = ((ftPrincipalAmp (quadPoly q0 q1 q2) 1 2 (rayZ q0 q1 q2) (rayTau q0 q1) θ : ℝ) : ℂ)
        * Complex.exp (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) := by
  rw [ftPrincipalAmp, ray_ftPrincipal_eq]
  exact ray_polar hq0 hq1 hcos hsin



/-! ### The branch geometry at `r = 2`

`FTChainGeom` for the ray pencil.  The joint constraint is `2 ≤ M`: the retained arc
`[1/M, π/2 - 1/M]` of `eq:retained-range` is **empty** at `M = 1`, where `1/M = 1` already
exceeds `π/2 - 1/M`.  Every field would then hold vacuously except `∀ i, w_i ∈ A`,
which forces `A` nonempty — so the bundle is unsatisfiable there rather than trivially true.
That is a constraint of the composition, not of any one field. -/

/-- The retained arc of `eq:retained-range` at `h = 1`, for `r = 2`. -/
noncomputable def rayArc (M : ℕ) : Set ℝ :=
  Set.Icc (1 / (M : ℝ)) (Real.pi / 2 - 1 / (M : ℝ))

/-- The monotone chain for the single component. -/
noncomputable def rayChain (M : ℕ) : ℕ → ℝ :=
  fun i => if i = 0 then 1 / (M : ℝ) else Real.pi / 2 - 1 / (M : ℝ)

private theorem rayArc_le {M : ℕ} (hM : 2 ≤ M) :
    1 / (M : ℝ) ≤ Real.pi / 2 - 1 / (M : ℝ) := by
  have hMR : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have h1 : 1 / (M : ℝ) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) hMR
  have := Real.pi_gt_three
  linarith

private theorem rayArc_pos {M : ℕ} (hM : 2 ≤ M) : (0 : ℝ) < 1 / (M : ℝ) := by
  have hMR : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  positivity

private theorem rayArc_cos {M : ℕ} (hM : 2 ≤ M) {θ : ℝ} (hθ : θ ∈ rayArc M) :
    0 < Real.cos θ :=
  rayCos_pos (rayArc_pos hM).le (by linarith [rayArc_pos hM]) hθ

private theorem rayArc_sin {M : ℕ} (hM : 2 ≤ M) {θ : ℝ} (hθ : θ ∈ rayArc M) :
    0 < Real.sin θ := by
  have hp := rayArc_pos hM
  refine Real.sin_pos_of_pos_of_lt_pi (lt_of_lt_of_le hp hθ.1) ?_
  have := Real.pi_gt_three
  linarith [hθ.2]

/-- **`FTChainGeom` at `r = 2`.**  The branch geometry of `thm:FT-geometry` on the retained arc,
with `τ` non-constant and vanishing at the upper endpoint, `z` strictly increasing into the
ray, and the amplitude's argument the constant `π/2` — so `eq:phase-derivative-bound` holds at
`κ = 0` and `eq:linear-phase-variation` at `κ_0 = κ_1 = 0`, exactly as on the
`r = 1` Favard pencil. -/
theorem witness_ftChainGeom_ray {q0 q1 q2 : ℝ} (hq0 : 0 < q0) (hq1 : q1 < 0) {M : ℕ}
    (hM : 2 ≤ M) :
    FTChainGeom (quadPoly q0 q1 q2) 1 2 (rayZ q0 q1 q2) (rayTau q0 q1)
      (fun _ => Real.pi / 2) M (1 : Polynomial ℂ).natDegree 1 0 0 0 1 (Real.pi / 2)
      (fun _ => (∅ : Set ℝ)) (Set.Ioi (q1 ^ 2 / (4 * q0) - q2)) := by
  have hab : 1 / (M : ℝ) ≤ Real.pi / 2 - 1 / (M : ℝ) := rayArc_le hM
  have hpos : (0 : ℝ) < 1 / (M : ℝ) := rayArc_pos hM
  have hMR : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  refine ⟨rayArc M, rayChain M, 1, fun _ => 0, 0, Set.ordConnected_Icc, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun θ hθ => ⟨hθ.1, hθ.2, by simp⟩
  · intro i j hij
    change (if i = 0 then 1 / (M : ℝ) else Real.pi / 2 - 1 / (M : ℝ))
      ≤ (if j = 0 then 1 / (M : ℝ) else Real.pi / 2 - 1 / (M : ℝ))
    split_ifs with h1 h2 h2
    · exact le_rfl
    · exact hab
    · exact absurd hij (by omega)
    · exact le_rfl
  · intro i
    change (if i = 0 then 1 / (M : ℝ) else Real.pi / 2 - 1 / (M : ℝ))
      ∈ Set.Icc (1 / (M : ℝ)) (Real.pi / 2 - 1 / (M : ℝ))
    split_ifs
    · exact ⟨le_rfl, hab⟩
    · exact ⟨hab, le_rfl⟩
  · intro i hi; omega
  · exact rayZ_strictMonoOn hq0 hq1 hpos.le (by linarith)
  · exact fun θ hθ => rayZ_mem_Ioi hq0 hq1 hpos (by linarith) hθ
  · exact fun θ hθ => rayTau_pos hq0 hq1 (rayArc_cos hM hθ)
  · exact fun θ hθ => ray_ftAmp_ne_zero hq0 hq1 (rayArc_cos hM hθ) (rayArc_sin hM hθ)
  · exact fun θ hθ => ray_polar_ftPrincipal hq0 hq1 (rayArc_cos hM hθ) (rayArc_sin hM hθ)
  · exact fun θ _ => hasDerivAt_const θ (Real.pi / 2)
  · exact fun θ _ => by simp
  · positivity
  · simp
  · rw [Finset.sum_range_one]
    change Real.pi / ((2 : ℕ) : ℝ) - 2 * 1 / (M : ℝ) - 0
      ≤ (Real.pi / 2 - 1 / (M : ℝ)) - 1 / (M : ℝ)
    have h2 : 2 * (1 : ℝ) / (M : ℝ) = 1 / (M : ℝ) + 1 / (M : ℝ) := by ring
    rw [h2]
    norm_num
  · simp
  · have hconst : eVariationOn (fun _ : ℝ => Real.pi / 2) (rayArc M) = 0 := by
      refine eVariationOn.constant_on ?_
      rintro x ⟨a, -, rfl⟩ y ⟨b, -, rfl⟩
      rfl
    rw [hconst]
    simp



/-- **`eq:dominance-bound` on the retained range at `r = 2`**, in the shape
`DominanceFT.weighted_dominance_of_branch` concludes and `phaseSupply_of_ftChainGeom` consumes.
The remainder vanishes identically, so the bound holds with no deleted window and the only
threshold is the `2 ≤ M` the arc itself needs. -/
theorem witness_dominance_ray {q0 q1 q2 : ℝ} (hq0 : 0 < q0) (hq1 : q1 < 0) :
    ∀ M : ℕ, 2 ≤ M → ∀ θ : ℝ, 1 / (M : ℝ) ≤ θ → θ ≤ Real.pi / 2 - 1 / (M : ℝ) →
      θ ∉ (∅ : Set ℝ) →
      ftRemainder (quadPoly q0 q1 q2) 1 2 (rayZ q0 q1 q2) (rayTau q0 q1) M θ
        ≤ ftPrincipalAmp (quadPoly q0 q1 q2) 1 2 (rayZ q0 q1 q2) (rayTau q0 q1) θ / 2 := by
  intro M hM θ h1 h2 _
  have hθ : θ ∈ rayArc M := ⟨h1, h2⟩
  have hzero := ray_ftRemainder_eq_zero (q2 := q2) hq0 hq1 (rayArc_cos hM hθ)
    (rayArc_sin hM hθ) M
  have hamp : (0 : ℝ)
      ≤ ftPrincipalAmp (quadPoly q0 q1 q2) 1 2 (rayZ q0 q1 q2) (rayTau q0 q1) θ :=
    norm_nonneg _
  rw [hzero]
  linarith



/-! ### The phase supply at `r > 1` -/

/-- **`PhaseSupply` for the `r = 2` ray pencil.**  `phaseSupply_of_ftChainGeom` run on the
branch geometry and `eq:dominance-bound` above.  The coefficient sequence is real by
`exists_real_ftCoeffPoly`, so it is produced rather than assumed.

`hwin = 1`, `κ_0 = κ_1 = 0` are literals here, exactly as in the `r = 1` witness — the
constants of `prop:angular-discrepancy` do not move when the pencil's modulus stops being
constant. -/
theorem witness_phaseSupply_ray {q0 q1 q2 : ℝ} (hq0 : 0 < q0) (hq1 : q1 < 0) {M : ℕ}
    (hM : 2 ≤ M) :
    ∃ P : Polynomial ℝ,
      P.map (algebraMap ℝ ℂ) = ftCoeffPoly (quadPoly q0 q1 q2) 1 2 M ∧
      PhaseSupply P (fun _ => Real.pi / 2) (rayZ q0 q1 q2) M
        (1 : Polynomial ℂ).natDegree 2 1 0 0 0
        (Set.Ioi (q1 ^ 2 / (4 * q0) - q2)) := by
  obtain ⟨P, hP⟩ := exists_real_ftCoeffPoly q0 q1 q2 M
  refine ⟨P, hP, ?_⟩
  exact phaseSupply_of_ftChainGeom hP Set.ordConnected_Ioi (by simp) hM
    (witness_dominance_ray hq0 hq1) (witness_ftChainGeom_ray hq0 hq1 hM)

/-- **The count clause 3 delivers at `r > 1`.**  At every index `M ≥ 2` the coefficient
polynomial has at least `M/2 - 4` distinct zeros inside the Forgács--Tran **ray**.

The defect is `⌈ defectC_0\ 1\ 0 + defectC_1\ 0 · 0⌉ = 4`, the same constant the
`r = 1` witness produces — which is the point: `τ` varying and vanishing at the endpoint
changes the geometry, not the discrepancy constants. -/
theorem witness_clauseThree_ray {q0 q1 q2 : ℝ} (hq0 : 0 < q0) (hq1 : q1 < 0) {M : ℕ}
    (hM : 2 ≤ M) :
    ∃ (P : Polynomial ℝ) (Z : Finset ℂ),
      P.map (algebraMap ℝ ℂ) = ftCoeffPoly (quadPoly q0 q1 q2) 1 2 M ∧
      M / 2 - 4 ≤ Z.card ∧
      (∀ w ∈ Z, (P.map (algebraMap ℝ ℂ)).IsRoot w) ∧
      (∀ w ∈ Z, w ∈ Complex.ofReal '' Set.Ioi (q1 ^ 2 / (4 * q0) - q2)) := by
  obtain ⟨P, hP, hsup⟩ := witness_phaseSupply_ray hq0 hq1 hM
  obtain ⟨Z, hcard, hroot, hmem⟩ :=
    exists_interiorZeros_of_phaseSupply P (by omega) (by norm_num) zero_le_one hsup
  refine ⟨P, Z, hP, ?_, hroot, hmem⟩
  have h3 := Real.pi_gt_three
  have h4 := Real.pi_lt_four
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hceil : ⌈defectC₀ 1 0 + defectC₁ 0 * (((1 : Polynomial ℂ).natDegree : ℕ) : ℝ)⌉₊ = 4 := by
    rw [Polynomial.natDegree_one]
    have hval : defectC₀ 1 0 + defectC₁ 0 * ((0 : ℕ) : ℝ) = 5 / Real.pi + 2 := by
      rw [defectC₀, defectC₁]; push_cast; ring
    rw [hval]
    refine (Nat.ceil_eq_iff (by norm_num)).2 ⟨?_, ?_⟩
    · have : (1 : ℝ) < 5 / Real.pi := by rw [lt_div_iff₀ hπ]; linarith
      push_cast; linarith
    · have : (5 : ℝ) / Real.pi ≤ 2 := by rw [div_le_iff₀ hπ]; linarith
      push_cast; linarith
  rwa [hceil] at hcard



/-! ### The weight `t^k` at `r = 2`: `deg B` varies on the ray too -/

theorem ray_polar_pow_ftPrincipal (k : ℕ) {q0 q1 q2 : ℝ} (hq0 : 0 < q0) (hq1 : q1 < 0) {θ : ℝ}
    (hcos : 0 < Real.cos θ) (hsin : 0 < Real.sin θ) :
    ftAmp (quadPoly q0 q1 q2) (X ^ k) 2 (((rayZ q0 q1 q2 θ : ℝ)) : ℂ)
        (ftPrincipal (rayTau q0 q1) θ)
      = ((ftPrincipalAmp (quadPoly q0 q1 q2) (X ^ k) 2 (rayZ q0 q1 q2) (rayTau q0 q1) θ
          : ℝ) : ℂ)
        * Complex.exp (((rayPsi k θ : ℝ) : ℂ) * Complex.I) := by
  rw [ftPrincipalAmp, ray_ftPrincipal_eq]
  exact ray_polar_pow k hq0 hq1 hcos hsin

/-- **No remainder at the weight `t^k`.**  `ftRemainder_X_pow_of_pos` carries the vanishing
across the shift, and the factor it introduces is `τ^k` — which is exactly why that lemma
had to be general in the modulus: the `τ ≡ 1` form covers the Favard pencil alone. -/
theorem ray_ftRemainder_pow_eq_zero (k : ℕ) {q0 q1 q2 : ℝ} (hq0 : 0 < q0) (hq1 : q1 < 0)
    {θ : ℝ} (hcos : 0 < Real.cos θ) (hsin : 0 < Real.sin θ) {M : ℕ} (hkM : k ≤ M) :
    ftRemainder (quadPoly q0 q1 q2) (X ^ k) 2 (rayZ q0 q1 q2) (rayTau q0 q1) M θ = 0 := by
  rw [ftRemainder_X_pow_of_pos (rayTau_pos hq0 hq1 hcos) hkM,
    ray_ftRemainder_eq_zero hq0 hq1 hcos hsin (M - k), mul_zero]

theorem witness_dominance_ray_pow (k : ℕ) {q0 q1 q2 : ℝ} (hq0 : 0 < q0) (hq1 : q1 < 0) :
    ∀ M : ℕ, max 2 k ≤ M → ∀ θ : ℝ, 1 / (M : ℝ) ≤ θ → θ ≤ Real.pi / 2 - 1 / (M : ℝ) →
      θ ∉ (∅ : Set ℝ) →
      ftRemainder (quadPoly q0 q1 q2) (X ^ k) 2 (rayZ q0 q1 q2) (rayTau q0 q1) M θ
        ≤ ftPrincipalAmp (quadPoly q0 q1 q2) (X ^ k) 2 (rayZ q0 q1 q2) (rayTau q0 q1) θ / 2 := by
  intro M hM θ h1 h2 _
  have hM2 : 2 ≤ M := le_trans (le_max_left _ _) hM
  have hkM : k ≤ M := le_trans (le_max_right _ _) hM
  have hθ : θ ∈ rayArc M := ⟨h1, h2⟩
  have hzero := ray_ftRemainder_pow_eq_zero (q2 := q2) k hq0 hq1 (rayArc_cos hM2 hθ)
    (rayArc_sin hM2 hθ) hkM
  have hamp : (0 : ℝ)
      ≤ ftPrincipalAmp (quadPoly q0 q1 q2) (X ^ k) 2 (rayZ q0 q1 q2) (rayTau q0 q1) θ :=
    norm_nonneg _
  rw [hzero]
  linarith

/-- **`FTChainGeom` at `r = 2`, weight `t^k`.**  `hwin = 1`, `κ_0 = 0` and
`κ_1 = π/2` are literals not mentioning `k`; what moves with the weight is
`K = deg(t^k) = k`, the branch `ψ_k`, and the phase-derivative constant `κ = k`.
`κ_1 = π/2` rather than `π` because the arc is `(0, π/r)` and `r = 2`. -/
theorem witness_ftChainGeom_ray_pow (k : ℕ) {q0 q1 q2 : ℝ} (hq0 : 0 < q0) (hq1 : q1 < 0)
    {M : ℕ} (hM : 2 ≤ M) (hkM : k ≤ M) :
    FTChainGeom (quadPoly q0 q1 q2) (X ^ k) 2 (rayZ q0 q1 q2) (rayTau q0 q1)
      (rayPsi k) M ((X ^ k : Polynomial ℂ).natDegree) 1 0 0 (Real.pi / 2) 1 (Real.pi / 2)
      (fun _ => (∅ : Set ℝ)) (Set.Ioi (q1 ^ 2 / (4 * q0) - q2)) := by
  have hab : 1 / (M : ℝ) ≤ Real.pi / 2 - 1 / (M : ℝ) := rayArc_le hM
  have hpos : (0 : ℝ) < 1 / (M : ℝ) := rayArc_pos hM
  have hkR : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hkMR : (k : ℝ) ≤ (M : ℝ) := by exact_mod_cast hkM
  refine ⟨rayArc M, rayChain M, 1, fun _ => (k : ℝ), (k : ℝ), Set.ordConnected_Icc, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun θ hθ => ⟨hθ.1, hθ.2, by simp⟩
  · intro i j hij
    change (if i = 0 then 1 / (M : ℝ) else Real.pi / 2 - 1 / (M : ℝ))
      ≤ (if j = 0 then 1 / (M : ℝ) else Real.pi / 2 - 1 / (M : ℝ))
    split_ifs with h1 h2 h2
    · exact le_rfl
    · exact hab
    · exact absurd hij (by omega)
    · exact le_rfl
  · intro i
    change (if i = 0 then 1 / (M : ℝ) else Real.pi / 2 - 1 / (M : ℝ))
      ∈ Set.Icc (1 / (M : ℝ)) (Real.pi / 2 - 1 / (M : ℝ))
    split_ifs
    · exact ⟨le_rfl, hab⟩
    · exact ⟨hab, le_rfl⟩
  · intro i hi; omega
  · exact rayZ_strictMonoOn hq0 hq1 hpos.le (by linarith)
  · exact fun θ hθ => rayZ_mem_Ioi hq0 hq1 hpos (by linarith) hθ
  · exact fun θ hθ => rayTau_pos hq0 hq1 (rayArc_cos hM hθ)
  · intro θ hθ
    rw [ray_ftPrincipal_eq]
    exact ray_ftAmp_pow_ne_zero k hq0 hq1 (rayArc_cos hM hθ) (rayArc_sin hM hθ)
  · exact fun θ hθ => ray_polar_pow_ftPrincipal k hq0 hq1 (rayArc_cos hM hθ)
      (rayArc_sin hM hθ)
  · intro θ _
    change HasDerivAt (fun x : ℝ => (k : ℝ) * x + Real.pi / 2) ((k : ℝ)) θ
    simpa using ((hasDerivAt_id θ).const_mul (k : ℝ)).add_const (Real.pi / 2)
  · exact fun θ _ => by simp
  · linarith
  · rw [Polynomial.natDegree_X_pow]; omega
  · rw [Finset.sum_range_one]
    change Real.pi / ((2 : ℕ) : ℝ) - 2 * 1 / (M : ℝ) - 0
      ≤ (Real.pi / 2 - 1 / (M : ℝ)) - 1 / (M : ℝ)
    have h2 : 2 * (1 : ℝ) / (M : ℝ) = 1 / (M : ℝ) + 1 / (M : ℝ) := by ring
    rw [h2]
    norm_num
  · simp
  · have hmono : MonotoneOn (rayPsi k) (rayArc M) := by
      intro x _ y _ hxy
      simp only [rayPsi]
      nlinarith
    have hma : (1 / (M : ℝ)) ∈ rayArc M := ⟨le_rfl, hab⟩
    have hmb : (Real.pi / 2 - 1 / (M : ℝ)) ∈ rayArc M := ⟨hab, le_rfl⟩
    have heq := hmono.eVariationOn_eq hma hmb
    rw [rayArc, Set.inter_self] at heq
    rw [rayArc, heq, Polynomial.natDegree_X_pow]
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [rayPsi]
    nlinarith [mul_nonneg hkR hpos.le]



theorem exists_real_ftCoeffPoly_pow (q0 q1 q2 : ℝ) {k M : ℕ} (hkM : k ≤ M) :
    ∃ P : Polynomial ℝ,
      P.map (algebraMap ℝ ℂ) = ftCoeffPoly (quadPoly q0 q1 q2) (X ^ k) 2 M := by
  obtain ⟨P, hP⟩ := exists_real_ftCoeffPoly q0 q1 q2 (M - k)
  exact ⟨P, by rw [hP, ftCoeffPoly_X_pow, if_neg (by omega)]⟩

/-- **`PhaseSupply` at `r = 2` over weights of every degree.**  `hwin = 1`, `κ_0 = 0` and
`κ_1 = π/2` are literals in the conclusion and do not mention `k`, while
`K = deg(t^k) = k` and the branch `ψ_k` do.  So the clause-3 constants stand still as the
weight degree moves, on a pencil whose principal modulus is not constant either. -/
theorem witness_phaseSupply_ray_pow (k : ℕ) {q0 q1 q2 : ℝ} (hq0 : 0 < q0) (hq1 : q1 < 0)
    {M : ℕ} (hM : 2 ≤ M) (hkM : k ≤ M) :
    ∃ P : Polynomial ℝ,
      P.map (algebraMap ℝ ℂ) = ftCoeffPoly (quadPoly q0 q1 q2) (X ^ k) 2 M ∧
      PhaseSupply P (rayPsi k) (rayZ q0 q1 q2) M ((X ^ k : Polynomial ℂ).natDegree) 2
        1 0 0 (Real.pi / 2) (Set.Ioi (q1 ^ 2 / (4 * q0) - q2)) := by
  obtain ⟨P, hP⟩ := exists_real_ftCoeffPoly_pow q0 q1 q2 hkM
  refine ⟨P, hP, ?_⟩
  refine phaseSupply_of_ftChainGeom hP Set.ordConnected_Ioi ?_ (max_le hM hkM)
    (witness_dominance_ray_pow k hq0 hq1) (witness_ftChainGeom_ray_pow k hq0 hq1 hM hkM)
  rw [Polynomial.natDegree_X_pow]
  have := Real.pi_pos
  positivity

/-- **The count at `r > 1`, over weights of every degree.**  At every index `M ≥ max(2,k)`
the coefficient polynomial has at least `M/2 - (4 + 3k)` distinct zeros in the Forgács--Tran
ray.  The defect grows linearly in `deg B` with intercept `4` and slope `3`, **neither
depending on `k`** — the same shape, and the same intercept, as the `r = 1` witness. -/
theorem witness_clauseThree_ray_pow (k : ℕ) {q0 q1 q2 : ℝ} (hq0 : 0 < q0) (hq1 : q1 < 0)
    {M : ℕ} (hM : 2 ≤ M) (hkM : k ≤ M) :
    ∃ (P : Polynomial ℝ) (Z : Finset ℂ),
      P.map (algebraMap ℝ ℂ) = ftCoeffPoly (quadPoly q0 q1 q2) (X ^ k) 2 M ∧
      M / 2 - (4 + 3 * k) ≤ Z.card ∧
      (∀ w ∈ Z, (P.map (algebraMap ℝ ℂ)).IsRoot w) ∧
      (∀ w ∈ Z, w ∈ Complex.ofReal '' Set.Ioi (q1 ^ 2 / (4 * q0) - q2)) := by
  obtain ⟨P, hP, hsup⟩ := witness_phaseSupply_ray_pow k hq0 hq1 hM hkM
  obtain ⟨Z, hcard, hroot, hmem⟩ :=
    exists_interiorZeros_of_phaseSupply P (by omega) (by norm_num) zero_le_one hsup
  refine ⟨P, Z, hP, ?_, hroot, hmem⟩
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have h3 := Real.pi_gt_three
  have h4 := Real.pi_lt_four
  have hbound : ⌈defectC₀ 1 0
      + defectC₁ (Real.pi / 2) * (((X ^ k : Polynomial ℂ).natDegree : ℕ) : ℝ)⌉₊
      ≤ 4 + 3 * k := by
    rw [Polynomial.natDegree_X_pow]
    refine le_trans (Nat.ceil_add_le _ _) (Nat.add_le_add ?_ ?_)
    · refine Nat.ceil_le.2 ?_
      rw [defectC₀]
      have : (5 : ℝ) / Real.pi ≤ 2 := by rw [div_le_iff₀ hπ]; linarith
      push_cast
      have h5 : 4 * (1 : ℝ) / Real.pi + 1 / Real.pi + 0 / Real.pi = 5 / Real.pi := by
        field_simp; ring
      linarith [h5.symm.le, h5.le]
    · refine Nat.ceil_le.2 ?_
      rw [defectC₁]
      have hhalf : Real.pi / 2 / Real.pi = 1 / 2 := by field_simp
      rw [hhalf]
      push_cast
      have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
  omega


/-- **The count is unbounded on the ray too.**  `witness_clauseThree_ray_pow` bounds the count
below by `M/2 - (4 + 3k)`, empty in `ℕ` for every `M ≤ 2(4 + 3k) + 1` -- the `+ 1` because
`M/2 ≤ c` admits the odd `M = 2c + 1`, so at `k = 0` the bound is empty through `M = 9` and
not merely through `M = 8`.  At every weight degree the
witness produces arbitrarily many distinct zeros in the Forgács--Tran ray, so the conclusion is
non-trivial rather than merely non-empty — and the degree of the coefficient polynomial grows
with them. -/
theorem witness_clauseThree_ray_unbounded (k n : ℕ) {q0 q1 q2 : ℝ} (hq0 : 0 < q0)
    (hq1 : q1 < 0) :
    ∃ (M : ℕ) (P : Polynomial ℝ) (Z : Finset ℂ),
      P.map (algebraMap ℝ ℂ) = ftCoeffPoly (quadPoly q0 q1 q2) (X ^ k) 2 M ∧
      n ≤ Z.card ∧
      (∀ w ∈ Z, (P.map (algebraMap ℝ ℂ)).IsRoot w) ∧
      (∀ w ∈ Z, w ∈ Complex.ofReal '' Set.Ioi (q1 ^ 2 / (4 * q0) - q2)) := by
  obtain ⟨P, Z, hP, hcard, hroot, hmem⟩ :=
    witness_clauseThree_ray_pow k hq0 hq1 (M := 2 * (n + 4 + 3 * k)) (by omega) (by omega)
  exact ⟨2 * (n + 4 + 3 * k), P, Z, hP, by omega, hroot, hmem⟩

end ForgacsTran
