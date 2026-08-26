/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.UpperClusterWitness

/-!
# Both clusters at once: Q = (1-t)³, r = 3

Every witness in this tree has had one cluster empty.  `CubicWitness` takes
`Q = (1-t)³` with `r = 1`: `ρ = 3` gives `n₀ = 1`, but `r = 1` leaves the upper
cluster empty.  `UpperClusterWitness` takes `Q = 1 - t` with `r = 3` and has the
mirror defect.  Here the triple zero gives `ρ = 3` and `n₀ = ρ - 2 = 1`, and
`r = 3` gives `n₁ = r - 2 = 1`, so **both** cluster binder families of
`weighted_dominance_of_branch` are instantiated non-vacuously at one pencil.

**The branch needs no root-finding.**  `z = -((1-t)/t)³` is real exactly when
`arg((1-t)/t)` is a multiple of `π/3`, so the realness locus is a *ray* in
`w = (1-t)/t` rather than a curve cut out by an equation.  Along `w = ρe^{-iπ/3}`
the parameter is `z = -w³ = ρ³`, with nothing to solve.  Eliminating `ρ` in
favour of the angle removes every square root and every arctangent:

`ρ(θ) = sin θ / cos(θ + π/6)`, `τ(θ) = (2/√3)cos(θ + π/6)`,
`t₃(θ) = cos(θ + π/6)/(√3 cos(θ + π/3))`, `t₃/τ = 1/(2cos(θ + π/3))`.

**The factorization is the sum of cubes.**  `A³ + B³ = (A+B)(A+ηB)(A+η²B)` at
`A = 1 - t`, `B = ρt`, so the three zeros are `1/(1 - cρ)` over the cube roots
of unity — no symmetric-function computation and no discriminant.

**One degeneracy, at `ρ = 1`.**  `(1-t)³ + zt³ = 1 - 3t + 3t² + (z-1)t³` has
leading coefficient `z - 1`, so at `ρ = 1` the degree drops to `2` and the third
zero escapes.  What is left there is *exactly the principal pair*, so both
cluster counts are `0` rather than `1` — a sharper statement than the degree
dropping.  That point is `θ = π/6`, the midpoint of the arc, hence interior; both
binder windows avoid it whenever `e₀ < π/6` and `e₁ < π/6`, which they must be
anyway to stay disjoint.  Every result below that names `t₃` carries
`cos(θ + π/3) ≠ 0`, which is that exclusion.

**The involution.**  `ρ ↦ 1/ρ` maps the arc to itself by `θ ↦ π/3 - θ`, fixes
exactly `ρ = 1`, and sends the normalized nonprincipal member to *minus* itself.
In closed form that is `|ratio(π/3 - δ)| = ratio(δ)`, so one scalar function
carries both endpoints.  It does **not** make the two binders the same shape:
the sign it introduces is exactly why `hexp₀` bounds a complex difference and
`hexp₁` bounds a difference of moduli.

`scripts/check_joint_witness.py` checks the counts, the degeneracy and the
involution at the real objects.

## Implementation notes

Sorry-free.

## Tags

witness, cubic pencil, both clusters, non-vacuity
-/

namespace ForgacsTran

open Polynomial Complex

/-- The witness pencil's numerator: `Q(t) = (1 - t)³`, a triple zero at `t = 1`,
so `ρ = 3`. -/
noncomputable def jointQ : Polynomial ℂ := (1 - Polynomial.X) ^ 3

theorem jointQ_eval (t : ℂ) : jointQ.eval t = (1 - t) ^ 3 := by simp [jointQ]

theorem jointQ_eval_zero : jointQ.eval 0 = 1 := by simp [jointQ]

/-! ### The cube root of unity, and the sum of cubes -/

/-- `η = e^{2πi/3}`. -/
noncomputable def jointEta : ℂ := ⟨-(1 / 2), Real.sqrt 3 / 2⟩

theorem jointEta_sq_add : jointEta ^ 2 + jointEta + 1 = 0 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  apply Complex.ext <;>
    simp [jointEta, pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.add_im, Complex.one_re, Complex.one_im] <;> nlinarith [h3]

/-- `A³ + B³ = (A+B)(A+ηB)(A+η²B)`.  The whole factorization of the pencil is
this identity at `A = 1 - t`, `B = ρt`. -/
theorem sum_cubes_factor (A B : ℂ) :
    A ^ 3 + B ^ 3 = (A + B) * (A + jointEta * B) * (A + jointEta ^ 2 * B) := by
  linear_combination (B ^ 3 - A ^ 2 * B - jointEta * A * B ^ 2 - jointEta * B ^ 3)
    * jointEta_sq_add

/-! ### The branch, in closed form -/

/-- The branch radius of the joint pencil, in closed form: `ρ(θ) = sin θ / cos(θ + π/6)`.
The reality condition at `Q(t) = (1-t)³`, `r = 3` solves in closed form, which is why this
pencil rather than a general one carries both clusters. -/
noncomputable def jointRho (θ : ℝ) : ℝ := Real.sin θ / Real.cos (θ + Real.pi / 6)

/-- The spectral parameter along the joint branch, `z(θ) = ρ(θ)³`.  The cube is `r = 3`. -/
noncomputable def jointZ (θ : ℝ) : ℝ := jointRho θ ^ 3

/-- The modulus of the principal pair, `τ(θ) = 2cos(θ + π/6)/√3`.  Positive exactly on the
viewing arc `(0, π/3)`, which is where every statement about it is asked. -/
noncomputable def jointTau (θ : ℝ) : ℝ := 2 * Real.cos (θ + Real.pi / 6) / Real.sqrt 3

/-- The third denominator zero, the one member of the nonprincipal cluster.  Vieta puts it on
the real axis because the three zeros of `(1-t)³ + zt³` have product fixed. -/
noncomputable def jointThird (θ : ℝ) : ℝ :=
  Real.cos (θ + Real.pi / 6) / (Real.sqrt 3 * Real.cos (θ + Real.pi / 3))

/-- `t₃/τ`, and it is the one scalar both endpoints expand. -/
noncomputable def jointRatio (δ : ℝ) : ℝ := 1 / (2 * Real.cos (δ + Real.pi / 3))

/-- The principal denominator zero `τ(θ)e^{iθ}`; its conjugate is the other member of the pair. -/
noncomputable def jointPrincipal (θ : ℝ) : ℂ :=
  ((jointTau θ : ℝ) : ℂ) * Complex.exp (((θ : ℝ) : ℂ) * Complex.I)

/-- `2cos(θ + π/6) + sin θ = √3 cos θ`.  This and its companion below are the
only trigonometry the factorization needs. -/
theorem two_cos_add_sin (θ : ℝ) :
    2 * Real.cos (θ + Real.pi / 6) + Real.sin θ = Real.sqrt 3 * Real.cos θ := by
  rw [Real.cos_add, Real.cos_pi_div_six, Real.sin_pi_div_six]
  ring

/-- `cos(θ + π/6) - sin θ = √3 cos(θ + π/3)`. -/
theorem cos_sub_sin_eq (θ : ℝ) :
    Real.cos (θ + Real.pi / 6) - Real.sin θ
      = Real.sqrt 3 * Real.cos (θ + Real.pi / 3) := by
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  rw [Real.cos_add, Real.cos_add, Real.cos_pi_div_six, Real.sin_pi_div_six,
    Real.cos_pi_div_three, Real.sin_pi_div_three]
  linear_combination (Real.sin θ / 2) * h3

theorem cos_add_pi_div_six_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 3)) :
    0 < Real.cos (θ + Real.pi / 6) := by
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> [linarith [Real.pi_pos, hθ.1]; linarith [hθ.2]]

theorem jointTau_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 3)) : 0 < jointTau θ := by
  have := cos_add_pi_div_six_pos hθ
  rw [jointTau]
  positivity

theorem jointEta_sq_eq_conj : jointEta ^ 2 = (starRingEnd ℂ) jointEta := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  apply Complex.ext <;>
    simp [jointEta, pow_two, Complex.mul_re, Complex.mul_im] <;> nlinarith [h3]

/-! ### The three zeros -/

/-- `1 - ηρ = (√3/2cos(θ+π/6))e^{-iθ}`, which is the whole content of the
principal zero: inverting it gives `τe^{iθ}`. -/
theorem one_sub_eta_rho {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 3)) :
    1 - jointEta * ((jointRho θ : ℝ) : ℂ)
      = ((Real.sqrt 3 / (2 * Real.cos (θ + Real.pi / 6)) : ℝ) : ℂ)
        * Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) := by
  have hc : 0 < Real.cos (θ + Real.pi / 6) := cos_add_pi_div_six_pos hθ
  have hi := two_cos_add_sin θ
  refine Complex.ext ?_ ?_
  · simp only [jointEta, jointRho, Complex.sub_re, Complex.one_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Real.cos_neg,
      Real.sin_neg]
    set c := Real.cos (θ + Real.pi / 6) with hcd
    field_simp [hc.ne']
    linear_combination hi
  · simp only [jointEta, jointRho, Complex.sub_im, Complex.one_im,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Real.cos_neg,
      Real.sin_neg]
    set c := Real.cos (θ + Real.pi / 6) with hcd
    field_simp [hc.ne']
    ring

/-- The principal zero solves the `η` factor: `t₊(1 - ηρ) = 1`. -/
theorem jointPrincipal_mul {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 3)) :
    jointPrincipal θ * (1 - jointEta * ((jointRho θ : ℝ) : ℂ)) = 1 := by
  have hc : 0 < Real.cos (θ + Real.pi / 6) := cos_add_pi_div_six_pos hθ
  have hs3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  rw [one_sub_eta_rho hθ, jointPrincipal, jointTau]
  rw [show ((2 * Real.cos (θ + Real.pi / 6) / Real.sqrt 3 : ℝ) : ℂ)
        * Complex.exp (((θ : ℝ) : ℂ) * Complex.I)
      * (((Real.sqrt 3 / (2 * Real.cos (θ + Real.pi / 6)) : ℝ) : ℂ)
        * Complex.exp (((-θ : ℝ) : ℂ) * Complex.I))
      = (((2 * Real.cos (θ + Real.pi / 6) / Real.sqrt 3
            * (Real.sqrt 3 / (2 * Real.cos (θ + Real.pi / 6)))) : ℝ) : ℂ)
        * (Complex.exp (((θ : ℝ) : ℂ) * Complex.I)
            * Complex.exp (((-θ : ℝ) : ℂ) * Complex.I)) by push_cast; ring]
  rw [← Complex.exp_add,
    show ((θ : ℝ) : ℂ) * Complex.I + ((-θ : ℝ) : ℂ) * Complex.I = 0 by push_cast; ring,
    Complex.exp_zero, mul_one]
  rw [show (2 * Real.cos (θ + Real.pi / 6) / Real.sqrt 3
      * (Real.sqrt 3 / (2 * Real.cos (θ + Real.pi / 6))) : ℝ) = 1 by
    set c := Real.cos (θ + Real.pi / 6)
    field_simp]
  norm_num

/-- The third zero solves the trivial factor: `t₃(1 - ρ) = 1`. -/
theorem jointThird_mul {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 3))
    (hne : Real.cos (θ + Real.pi / 3) ≠ 0) :
    jointThird θ * (1 - jointRho θ) = 1 := by
  have hc : 0 < Real.cos (θ + Real.pi / 6) := cos_add_pi_div_six_pos hθ
  have hs3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hiii := cos_sub_sin_eq θ
  set c := Real.cos (θ + Real.pi / 6) with hcd
  set s := Real.sin θ with hsd
  set d := Real.cos (θ + Real.pi / 3) with hdd
  rw [jointThird, jointRho, ← hcd, ← hsd, ← hdd]
  field_simp
  linear_combination hiii

/-- The conjugate zero solves the `η²` factor, by conjugating the first. -/
theorem jointPrincipal_conj_mul {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 3)) :
    (starRingEnd ℂ) (jointPrincipal θ)
        * (1 - jointEta ^ 2 * ((jointRho θ : ℝ) : ℂ)) = 1 := by
  have h := congrArg (starRingEnd ℂ) (jointPrincipal_mul hθ)
  rw [map_mul, map_one, map_sub, map_one, map_mul, Complex.conj_ofReal,
    ← jointEta_sq_eq_conj] at h
  exact h

/-! ### The factorization -/

/-- **The pencil is a sum of cubes.**  `A = 1 - t`, `B = ρt`. -/
theorem jointDen_eval (θ : ℝ) (t : ℂ) :
    (ftDen jointQ 3 ((jointZ θ : ℝ) : ℂ)).eval t
      = (1 - t + ((jointRho θ : ℝ) : ℂ) * t)
        * (1 - t + jointEta * ((jointRho θ : ℝ) : ℂ) * t)
        * (1 - t + jointEta ^ 2 * ((jointRho θ : ℝ) : ℂ) * t) := by
  have hz : ((jointZ θ : ℝ) : ℂ) = ((jointRho θ : ℝ) : ℂ) ^ 3 := by
    rw [jointZ]; push_cast; ring
  have h := sum_cubes_factor (1 - t) (((jointRho θ : ℝ) : ℂ) * t)
  rw [ftDen_eval, jointQ_eval, hz]
  linear_combination h

theorem jointDen_eval_principal {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 3)) :
    (ftDen jointQ 3 ((jointZ θ : ℝ) : ℂ)).eval (jointPrincipal θ) = 0 := by
  rw [jointDen_eval]
  have h := jointPrincipal_mul hθ
  have : 1 - jointPrincipal θ + jointEta * ((jointRho θ : ℝ) : ℂ) * jointPrincipal θ = 0 := by
    linear_combination -h
  rw [this]; ring

theorem jointDen_eval_conj {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 3)) :
    (ftDen jointQ 3 ((jointZ θ : ℝ) : ℂ)).eval ((starRingEnd ℂ) (jointPrincipal θ)) = 0 := by
  rw [jointDen_eval]
  have h := jointPrincipal_conj_mul hθ
  have : 1 - (starRingEnd ℂ) (jointPrincipal θ)
      + jointEta ^ 2 * ((jointRho θ : ℝ) : ℂ) * (starRingEnd ℂ) (jointPrincipal θ) = 0 := by
    linear_combination -h
  rw [this]; ring

theorem jointDen_eval_third {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 3))
    (hne : Real.cos (θ + Real.pi / 3) ≠ 0) :
    (ftDen jointQ 3 ((jointZ θ : ℝ) : ℂ)).eval ((jointThird θ : ℝ) : ℂ) = 0 := by
  rw [jointDen_eval]
  have h : ((jointThird θ : ℝ) : ℂ) * (1 - ((jointRho θ : ℝ) : ℂ)) = 1 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_mul,
      jointThird_mul hθ hne]
  have : 1 - ((jointThird θ : ℝ) : ℂ)
      + ((jointRho θ : ℝ) : ℂ) * ((jointThird θ : ℝ) : ℂ) = 0 := by
    linear_combination -h
  rw [this]; ring

/-! ### The retained set -/

theorem jointPrincipal_im {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 3)) :
    0 < (jointPrincipal θ).im := by
  have hs : (0 : ℝ) < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [Real.pi_pos, hθ.2])
  have hτ := jointTau_pos hθ
  rw [jointPrincipal, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_im, Complex.exp_ofReal_mul_I_re]
  have : jointTau θ * Real.sin θ + 0 * Real.cos θ = jointTau θ * Real.sin θ := by ring
  rw [this]
  positivity

/-- The conjugate member in the binder's own form, `τe^{-iθ}`. -/
theorem conj_jointPrincipal (θ : ℝ) :
    (starRingEnd ℂ) (jointPrincipal θ)
      = ((jointTau θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * Complex.I) := by
  rw [jointPrincipal, map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 1
  simp

/-- The retained set: the principal pair and the third zero. -/
noncomputable def jointRootSet (θ : ℝ) : Finset ℂ :=
  {jointPrincipal θ, (starRingEnd ℂ) (jointPrincipal θ), ((jointThird θ : ℝ) : ℂ)}

theorem card_jointRootSet {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 3)) :
    (jointRootSet θ).card = 3 := by
  classical
  have him := jointPrincipal_im hθ
  have hne1 : jointPrincipal θ ≠ (starRingEnd ℂ) (jointPrincipal θ) := by
    intro h
    have : (jointPrincipal θ).im = -(jointPrincipal θ).im := by
      conv_lhs => rw [h]
      simp
    linarith
  have hne2 : jointPrincipal θ ≠ ((jointThird θ : ℝ) : ℂ) := by
    intro h
    have : (jointPrincipal θ).im = 0 := by rw [h]; simp
    linarith
  have hne3 : (starRingEnd ℂ) (jointPrincipal θ) ≠ ((jointThird θ : ℝ) : ℂ) := by
    intro h
    have : (-(jointPrincipal θ).im) = 0 := by
      have := congrArg Complex.im h
      simpa using this
    linarith
  rw [jointRootSet, Finset.card_insert_of_notMem (by simp [hne1, hne2]),
    Finset.card_insert_of_notMem (by simp [hne3]), Finset.card_singleton]

/-- Erasing the principal pair leaves the third zero alone.  This is `n₀ = 1` at
the lower endpoint and `n₁ = 1` at the upper, from one `card` clause — which is
the point of this pencil. -/
theorem jointRootSet_erase_pair {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 3)) :
    ((jointRootSet θ).erase (jointPrincipal θ)).erase
        ((starRingEnd ℂ) (jointPrincipal θ))
      = {((jointThird θ : ℝ) : ℂ)} := by
  classical
  have him := jointPrincipal_im hθ
  have hne2 : ((jointThird θ : ℝ) : ℂ) ≠ jointPrincipal θ := by
    intro h
    have : (jointPrincipal θ).im = 0 := by rw [← h]; simp
    linarith
  have hne3 : ((jointThird θ : ℝ) : ℂ) ≠ (starRingEnd ℂ) (jointPrincipal θ) := by
    intro h
    have : (-(jointPrincipal θ).im) = 0 := by
      have := congrArg Complex.im h.symm
      simpa using this
    linarith
  ext w
  simp only [Finset.mem_erase, jointRootSet, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hc, hp, h | h | h⟩
    · exact absurd h hp
    · exact absurd h hc
    · exact h
  · rintro rfl
    exact ⟨hne3, hne2, by tauto⟩

/-- **`hroot` and `huniq` together.**  The zeros of the pencil are exactly the
retained set, with no modulus bound needed: each factor of the sum-of-cubes
form vanishes at exactly one point. -/
theorem jointDen_eval_eq_zero_iff {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 3))
    (hne : Real.cos (θ + Real.pi / 3) ≠ 0) (t : ℂ) :
    (ftDen jointQ 3 ((jointZ θ : ℝ) : ℂ)).eval t = 0 ↔ t ∈ jointRootSet θ := by
  classical
  constructor
  · intro h
    rw [jointDen_eval, mul_eq_zero, mul_eq_zero] at h
    have hthird : ((jointThird θ : ℝ) : ℂ) * (1 - ((jointRho θ : ℝ) : ℂ)) = 1 := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_mul,
        jointThird_mul hθ hne]
    rw [jointRootSet]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases h with (h | h) | h
    · refine Or.inr (Or.inr ?_)
      have hu : (1 - ((jointRho θ : ℝ) : ℂ)) ≠ 0 := by
        intro h0; rw [h0, mul_zero] at hthird; exact one_ne_zero hthird.symm
      have ht : t * (1 - ((jointRho θ : ℝ) : ℂ)) = 1 := by linear_combination -h
      exact mul_right_cancel₀ hu (ht.trans hthird.symm)
    · refine Or.inl ?_
      have hp := jointPrincipal_mul hθ
      have hu : (1 - jointEta * ((jointRho θ : ℝ) : ℂ)) ≠ 0 := by
        intro h0; rw [h0, mul_zero] at hp; exact one_ne_zero hp.symm
      have ht : t * (1 - jointEta * ((jointRho θ : ℝ) : ℂ)) = 1 := by linear_combination -h
      exact mul_right_cancel₀ hu (ht.trans hp.symm)
    · refine Or.inr (Or.inl ?_)
      have hp := jointPrincipal_conj_mul hθ
      have hu : (1 - jointEta ^ 2 * ((jointRho θ : ℝ) : ℂ)) ≠ 0 := by
        intro h0; rw [h0, mul_zero] at hp; exact one_ne_zero hp.symm
      have ht : t * (1 - jointEta ^ 2 * ((jointRho θ : ℝ) : ℂ)) = 1 := by
        linear_combination -h
      exact mul_right_cancel₀ hu (ht.trans hp.symm)
  · intro h
    rw [jointRootSet] at h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl | rfl
    · exact jointDen_eval_principal hθ
    · exact jointDen_eval_conj hθ
    · exact jointDen_eval_third hθ hne

/-! ### The minimum-modulus condition is the arc condition -/

theorem abs_cos_add_pi_div_three_lt_half {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 3)) :
    |Real.cos (θ + Real.pi / 3)| < 1 / 2 := by
  have hpi := Real.pi_pos
  have hup : Real.cos (θ + Real.pi / 3) < 1 / 2 := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi (x := Real.pi / 3) (y := θ + Real.pi / 3)
      (by positivity) (by linarith [hθ.2]) (by linarith [hθ.1])
    rwa [Real.cos_pi_div_three] at h
  have hlo : -(1 / 2) < Real.cos (θ + Real.pi / 3) := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi (x := θ + Real.pi / 3)
      (y := 2 * Real.pi / 3) (by linarith [hθ.1]) (by linarith) (by linarith [hθ.2])
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub,
      Real.cos_pi_div_three] at h
    linarith
  rw [abs_lt]; exact ⟨hlo, hup⟩

/-- `τ` is the minimum modulus of the retained set, and the inequality is
*equivalent* to `θ` lying in the open arc — no separate hypothesis. -/
theorem jointTau_lt_norm_third {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 3))
    (hne : Real.cos (θ + Real.pi / 3) ≠ 0) :
    jointTau θ < ‖((jointThird θ : ℝ) : ℂ)‖ := by
  have hc : 0 < Real.cos (θ + Real.pi / 6) := cos_add_pi_div_six_pos hθ
  have hs3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hd : 0 < |Real.cos (θ + Real.pi / 3)| := abs_pos.mpr hne
  have hhalf := abs_cos_add_pi_div_three_lt_half hθ
  rw [Complex.norm_real, Real.norm_eq_abs, jointThird, jointTau, abs_div,
    abs_of_pos hc, abs_mul, abs_of_pos hs3]
  rw [div_lt_div_iff₀ hs3 (mul_pos hs3 hd)]
  nlinarith [mul_lt_mul_of_pos_left hhalf (mul_pos (mul_pos two_pos hc) hs3), hc, hs3, hd]

/-! ### The scalar both endpoints expand -/

theorem jointThird_div_jointTau {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 3))
    (hne : Real.cos (θ + Real.pi / 3) ≠ 0) :
    jointThird θ / jointTau θ = jointRatio θ := by
  have hc : 0 < Real.cos (θ + Real.pi / 6) := cos_add_pi_div_six_pos hθ
  have hs3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  rw [jointThird, jointTau, jointRatio]
  set c := Real.cos (θ + Real.pi / 6)
  set d := Real.cos (θ + Real.pi / 3)
  field_simp

/-- **The involution, in closed form.**  `ρ ↦ 1/ρ` is `θ ↦ π/3 - θ` on the arc,
and it sends the normalized nonprincipal member to minus itself.  One scalar
therefore carries both endpoints — and the sign it introduces is exactly why the
two expansion binders do not share a shape. -/
theorem jointRatio_reflect (δ : ℝ) : jointRatio (Real.pi / 3 - δ) = -jointRatio δ := by
  rw [jointRatio, jointRatio,
    show Real.pi / 3 - δ + Real.pi / 3 = Real.pi - (δ + Real.pi / 3) by ring,
    Real.cos_pi_sub]
  field_simp

/-- The derivative of `jointRatio`, written out rather than produced by `deriv`, so that the
expansion's mean-value step has a closed form to bound. -/
noncomputable def jointRatioDeriv (δ : ℝ) : ℝ :=
  Real.sin (δ + Real.pi / 3)
    / (2 * (Real.cos (δ + Real.pi / 3) * Real.cos (δ + Real.pi / 3)))

/-- The second derivative of `jointRatio`, in closed form.  A bound on this on the window is
what turns the first-order expansion into the `O(δ²)` the cluster binders ask for. -/
noncomputable def jointRatioDeriv2 (δ : ℝ) : ℝ :=
  (1 + Real.sin (δ + Real.pi / 3) * Real.sin (δ + Real.pi / 3))
    / (2 * (Real.cos (δ + Real.pi / 3) * Real.cos (δ + Real.pi / 3)
        * Real.cos (δ + Real.pi / 3)))

theorem hasDerivAt_jointShift (δ : ℝ) :
    HasDerivAt (fun x : ℝ => x + Real.pi / 3) 1 δ := (hasDerivAt_id δ).add_const _

theorem hasDerivAt_jointRatio {δ : ℝ} (h : Real.cos (δ + Real.pi / 3) ≠ 0) :
    HasDerivAt jointRatio (jointRatioDeriv δ) δ := by
  have h1 := (hasDerivAt_jointShift δ).cos
  have hne2 : (2 : ℝ) * Real.cos (δ + Real.pi / 3) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, not_or]; exact ⟨two_ne_zero, h⟩
  change HasDerivAt (fun x : ℝ => 1 / (2 * Real.cos (x + Real.pi / 3))) _ δ
  exact ((hasDerivAt_const δ (1 : ℝ)).div (h1.const_mul 2) hne2).congr_deriv (by
    rw [jointRatioDeriv]; field_simp; ring)

theorem hasDerivAt_jointRatioDeriv {δ : ℝ} (h : Real.cos (δ + Real.pi / 3) ≠ 0) :
    HasDerivAt jointRatioDeriv (jointRatioDeriv2 δ) δ := by
  have hpy := Real.sin_sq_add_cos_sq (δ + Real.pi / 3)
  have h1 := (hasDerivAt_jointShift δ).cos
  have h2 := (hasDerivAt_jointShift δ).sin
  have hne2 : (2 : ℝ) * (Real.cos (δ + Real.pi / 3) * Real.cos (δ + Real.pi / 3)) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, not_or]; exact ⟨two_ne_zero, h, h⟩
  change HasDerivAt (fun x : ℝ => Real.sin (x + Real.pi / 3)
    / (2 * (Real.cos (x + Real.pi / 3) * Real.cos (x + Real.pi / 3)))) _ δ
  exact (h2.div ((h1.mul h1).const_mul 2) hne2).congr_deriv (by
    simp only [Pi.mul_apply]
    rw [jointRatioDeriv2]
    set u := δ + Real.pi / 3 with hu
    field_simp
    linear_combination hpy)

/-! ### The expansion, proved once and used at both endpoints -/

theorem sqrt_three_le : Real.sqrt 3 ≤ 7 / 4 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), Real.sqrt_nonneg 3]

/-- `cos(δ + π/3) ≥ 2/5` on `[0, 1/10]`, which is the one numeric input the
second-derivative bound needs. -/
theorem cos_add_pi_div_three_ge {δ : ℝ} (hδ : δ ∈ Set.Icc (0 : ℝ) (1 / 10)) :
    2 / 5 ≤ Real.cos (δ + Real.pi / 3) := by
  have hs : Real.sin δ ≤ δ := Real.sin_le hδ.1
  have hs0 : 0 ≤ Real.sin δ := Real.sin_nonneg_of_nonneg_of_le_pi hδ.1
    (by linarith [Real.pi_gt_three, hδ.2])
  have hcq : 1 - δ ^ 2 / 2 ≤ Real.cos δ := Real.one_sub_sq_div_two_le_cos
  have h3 := sqrt_three_le
  have h3' : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  rw [Real.cos_add, Real.cos_pi_div_three, Real.sin_pi_div_three]
  nlinarith [hδ.1, hδ.2, hs, hs0, hcq, h3, h3']

theorem cos_add_pi_div_three_ne {δ : ℝ} (hδ : δ ∈ Set.Icc (0 : ℝ) (1 / 10)) :
    Real.cos (δ + Real.pi / 3) ≠ 0 := by
  have := cos_add_pi_div_three_ge hδ
  intro h; rw [h] at this; linarith

/-- `|f''| ≤ 16` on `[0, 1/10]`.  `f'' = (1 + sin²)/(2cos³)` and `cos ≥ 2/5`
there, so the crude numerator bound `1 + sin² ≤ 2` already gives `125/8`. -/
theorem abs_jointRatioDeriv2_le {δ : ℝ} (hδ : δ ∈ Set.Icc (0 : ℝ) (1 / 10)) :
    |jointRatioDeriv2 δ| ≤ 16 := by
  have hc := cos_add_pi_div_three_ge hδ
  have hs := Real.sin_sq_add_cos_sq (δ + Real.pi / 3)
  have hden : (0 : ℝ) < 2 * (Real.cos (δ + Real.pi / 3) * Real.cos (δ + Real.pi / 3)
      * Real.cos (δ + Real.pi / 3)) := by nlinarith [hc]
  rw [jointRatioDeriv2, abs_div, abs_of_pos hden,
    abs_of_nonneg (by nlinarith [hs] : (0:ℝ) ≤ 1 + Real.sin (δ + Real.pi / 3)
      * Real.sin (δ + Real.pi / 3)), div_le_iff₀ hden]
  nlinarith [hc, hs, hden]

theorem jointRatio_zero : jointRatio 0 = 1 := by
  rw [jointRatio, zero_add, Real.cos_pi_div_three]; norm_num

theorem jointRatioDeriv_zero : jointRatioDeriv 0 = Real.sqrt 3 := by
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  rw [jointRatioDeriv, zero_add, Real.cos_pi_div_three, Real.sin_pi_div_three]
  rw [div_eq_iff (by norm_num)]
  linarith [h3]

/-- The second-order bound, from `phase_taylor_bound` — the mean value theorem
twice, the same lemma both other witnesses run on. -/
theorem jointCluster_taylor {δ : ℝ} (hδ : 0 < δ) (hδe : δ ≤ 1 / 10) :
    |jointRatio δ - 1 - Real.sqrt 3 * δ| ≤ 16 * δ ^ 2 := by
  have h := phase_taylor_bound (ψ := jointRatio) (dψ := jointRatioDeriv)
    (ddψ := jointRatioDeriv2) (a := 0) (b := 1 / 10) (κ₂ := 16)
    (fun x hx => hasDerivAt_jointRatio (cos_add_pi_div_three_ne hx))
    (fun x hx => hasDerivAt_jointRatioDeriv (cos_add_pi_div_three_ne hx))
    (fun x hx => abs_jointRatioDeriv2_le hx)
    ⟨le_rfl, by norm_num⟩ ⟨hδ.le, hδe⟩ hδ.le
  rw [jointRatio_zero, jointRatioDeriv_zero] at h
  simpa using h

/-- The binder's coefficient at `ρ = r = 3`, in the complex form `hexp₀` uses. -/
theorem clusterOmega_three_two_coeff :
    (((Real.cos (Real.pi / ((3 : ℕ) : ℝ)) : ℝ) : ℂ) - clusterOmega 3 2)
        / ((Real.sin (Real.pi / ((3 : ℕ) : ℝ)) : ℝ) : ℂ) = ((Real.sqrt 3 : ℝ) : ℂ) := by
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hs : Real.sin (Real.pi / ((3 : ℕ) : ℝ)) = Real.sqrt 3 / 2 := by
    rw [show ((3 : ℕ) : ℝ) = 3 by norm_num, Real.sin_pi_div_three]
  have hc : Real.cos (Real.pi / ((3 : ℕ) : ℝ)) = 1 / 2 := by
    rw [show ((3 : ℕ) : ℝ) = 3 by norm_num, Real.cos_pi_div_three]
  have hne : ((Real.sqrt 3 : ℝ) : ℂ) ≠ 0 := by
    simp
  have hsq : ((Real.sqrt 3 : ℝ) : ℂ) * ((Real.sqrt 3 : ℝ) : ℂ) = 3 := by
    rw [← Complex.ofReal_mul, h3]; norm_num
  rw [clusterOmega_three_two, hs, hc]
  push_cast
  field_simp
  linear_combination -hsq

/-! ### The nonprincipal member, and the two endpoint expansions -/

/-- The nonprincipal cluster as the one-element family `weighted_dominance_of_branch`'s binders
take: a singleton, because erasing the principal pair from three zeros leaves one. -/
noncomputable def jointNonprincipal (θ : ℝ) : Fin 1 → ℂ :=
  fun _ => ((jointThird θ : ℝ) : ℂ)

theorem jointNonprincipal_div {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 3))
    (hne : Real.cos (θ + Real.pi / 3) ≠ 0) (i : Fin 1) :
    jointNonprincipal θ i / ((jointTau θ : ℝ) : ℂ) = ((jointRatio θ : ℝ) : ℂ) := by
  rw [jointNonprincipal, ← Complex.ofReal_div, jointThird_div_jointTau hθ hne]

theorem mem_arc_lower {δ : ℝ} (hδ : 0 < δ) (hδe : δ ≤ 1 / 10) :
    δ ∈ Set.Ioo 0 (Real.pi / 3) := ⟨hδ, by linarith [Real.pi_gt_three]⟩

theorem mem_arc_upper {δ : ℝ} (hδ : 0 < δ) (hδe : δ ≤ 1 / 10) :
    Real.pi / 3 - δ ∈ Set.Ioo 0 (Real.pi / 3) :=
  ⟨by linarith [Real.pi_gt_three], by linarith⟩

theorem cos_upper_ne {δ : ℝ} (hδ : 0 < δ) (hδe : δ ≤ 1 / 10) :
    Real.cos (Real.pi / 3 - δ + Real.pi / 3) ≠ 0 := by
  have h := cos_add_pi_div_three_ge ⟨hδ.le, hδe⟩
  rw [show Real.pi / 3 - δ + Real.pi / 3 = Real.pi - (δ + Real.pi / 3) by ring,
    Real.cos_pi_sub]
  intro h0
  rw [neg_eq_zero] at h0
  rw [h0] at h
  linarith

/-- **`hexp₀` at the lower endpoint**, in the binder's complex shape.  The
normalized member is real and positive there, so the complex difference is the
real one. -/
theorem jointCluster_hexp_lower (i : Fin 1) {δ : ℝ} (hδ : 0 < δ) (hδe : δ ≤ 1 / 10) :
    ‖jointNonprincipal δ i / ((jointTau δ : ℝ) : ℂ)
        - (1 + ((((Real.cos (Real.pi / ((3 : ℕ) : ℝ)) : ℝ) : ℂ) - clusterOmega 3 2)
            / ((Real.sin (Real.pi / ((3 : ℕ) : ℝ)) : ℝ) : ℂ)) * ((δ : ℝ) : ℂ))‖
      ≤ 16 * δ ^ 2 := by
  rw [jointNonprincipal_div (mem_arc_lower hδ hδe) (cos_add_pi_div_three_ne ⟨hδ.le, hδe⟩) i,
    clusterOmega_three_two_coeff]
  rw [show ((jointRatio δ : ℝ) : ℂ)
        - (1 + ((Real.sqrt 3 : ℝ) : ℂ) * ((δ : ℝ) : ℂ))
      = (((jointRatio δ - 1 - Real.sqrt 3 * δ : ℝ)) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs]
  exact jointCluster_taylor hδ hδe

/-- **`hexp₁` at the upper endpoint**, in the binder's modulus shape.  The same
scalar, through `jointRatio_reflect` — and the sign that identity carries is
exactly why this binder takes the modulus first. -/
theorem jointCluster_hexp_upper (i : Fin 1) {δ : ℝ} (hδ : 0 < δ) (hδe : δ ≤ 1 / 10) :
    |‖jointNonprincipal (Real.pi / 3 - δ) i / ((jointTau (Real.pi / 3 - δ) : ℝ) : ℂ)‖
        - (1 + ((Real.cos (Real.pi / ((3 : ℕ) : ℝ)) - (clusterOmega 3 2).re)
            / Real.sin (Real.pi / ((3 : ℕ) : ℝ))) * δ)| ≤ 16 * δ ^ 2 := by
  have hpos : 0 < jointRatio δ := by
    rw [jointRatio]
    have := cos_add_pi_div_three_ge ⟨hδ.le, hδe⟩
    positivity
  have hcoeff : (Real.cos (Real.pi / ((3 : ℕ) : ℝ)) - (clusterOmega 3 2).re)
      / Real.sin (Real.pi / ((3 : ℕ) : ℝ)) = Real.sqrt 3 := by
    have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
    rw [clusterOmega_three_two, show ((3 : ℕ) : ℝ) = 3 by norm_num,
      Real.cos_pi_div_three, Real.sin_pi_div_three]
    simp only [Complex.neg_re, Complex.one_re]
    rw [div_eq_iff (by positivity)]
    linarith [h3]
  rw [jointNonprincipal_div (mem_arc_upper hδ hδe) (cos_upper_ne hδ hδe) i,
    Complex.norm_real, Real.norm_eq_abs, jointRatio_reflect, abs_neg,
    abs_of_pos hpos, hcoeff]
  have h := jointCluster_taylor hδ hδe
  rw [show jointRatio δ - (1 + Real.sqrt 3 * δ)
      = jointRatio δ - 1 - Real.sqrt 3 * δ by ring]
  exact h

/-! ### Both cluster blocks, at one pencil -/

/-- **`thm:weighted-dominance`'s cluster binders at both endpoints of one
pencil.**  Six at the lower endpoint and six at the upper, on two windows of a
single branch — `jointTau`, `jointZ` and `jointRootSet` are the same functions
on both halves, which is what no earlier witness could say.

The `e < π/6` clauses are load-bearing twice over.  They keep the two windows
disjoint, and they exclude `θ = π/6`, where the leading coefficient `z - 1`
vanishes, the third zero escapes, and *both* cluster counts collapse to `0`. -/
theorem jointWitness_both_clusters_block :
    ∃ e₀ e₁ Cexp : ℝ, 0 < e₀ ∧ e₀ < Real.pi / 6 ∧ 0 < e₁ ∧ e₁ < Real.pi / 6 ∧
      0 ≤ Cexp ∧
      -- the lower endpoint, `θ = δ`
      (∀ _i : Fin 1, clusterOmega 3 2
        ≠ Complex.exp (((Real.pi / ((3 : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I)) ∧
      (∀ _i : Fin 1, clusterOmega 3 2
        ≠ Complex.exp (((-(Real.pi / ((3 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I)) ∧
      (∀ δ : ℝ, 0 < δ → δ ≤ e₀ → Function.Injective (jointNonprincipal δ)) ∧
      (∀ δ : ℝ, 0 < δ → δ ≤ e₀ → ∀ i : Fin 1, jointNonprincipal δ i ∈
        ((jointRootSet δ).erase (ftPrincipal jointTau δ)).erase
          (((jointTau δ : ℝ) : ℂ) * Complex.exp (-((δ : ℝ) : ℂ) * Complex.I))) ∧
      (∀ δ : ℝ, 0 < δ → δ ≤ e₀ →
        (((jointRootSet δ).erase (ftPrincipal jointTau δ)).erase
          (((jointTau δ : ℝ) : ℂ)
            * Complex.exp (-((δ : ℝ) : ℂ) * Complex.I))).card = 1) ∧
      (∀ i : Fin 1, ∀ δ : ℝ, 0 < δ → δ ≤ e₀ →
        ‖jointNonprincipal δ i / ((jointTau δ : ℝ) : ℂ)
            - (1 + ((((Real.cos (Real.pi / ((3 : ℕ) : ℝ)) : ℝ) : ℂ) - clusterOmega 3 2)
                / ((Real.sin (Real.pi / ((3 : ℕ) : ℝ)) : ℝ) : ℂ)) * ((δ : ℝ) : ℂ))‖
          ≤ Cexp * δ ^ 2) ∧
      -- the upper endpoint, `θ = π/3 - δ`, on the same branch
      (∀ δ : ℝ, 0 < δ → δ ≤ e₁ →
        Function.Injective (jointNonprincipal (Real.pi / 3 - δ))) ∧
      (∀ δ : ℝ, 0 < δ → δ ≤ e₁ → ∀ i : Fin 1,
        jointNonprincipal (Real.pi / 3 - δ) i ∈
          ((jointRootSet (Real.pi / 3 - δ)).erase
              (ftPrincipal jointTau (Real.pi / 3 - δ))).erase
            (((jointTau (Real.pi / 3 - δ) : ℝ) : ℂ)
              * Complex.exp (-((Real.pi / 3 - δ : ℝ) : ℂ) * Complex.I))) ∧
      (∀ δ : ℝ, 0 < δ → δ ≤ e₁ →
        (((jointRootSet (Real.pi / 3 - δ)).erase
            (ftPrincipal jointTau (Real.pi / 3 - δ))).erase
          (((jointTau (Real.pi / 3 - δ) : ℝ) : ℂ)
            * Complex.exp (-((Real.pi / 3 - δ : ℝ) : ℂ) * Complex.I))).card = 1) ∧
      (∀ i : Fin 1, ∀ δ : ℝ, 0 < δ → δ ≤ e₁ →
        |‖jointNonprincipal (Real.pi / 3 - δ) i
              / ((jointTau (Real.pi / 3 - δ) : ℝ) : ℂ)‖
            - (1 + ((Real.cos (Real.pi / ((3 : ℕ) : ℝ)) - (clusterOmega 3 2).re)
                / Real.sin (Real.pi / ((3 : ℕ) : ℝ))) * δ)| ≤ Cexp * δ ^ 2) := by
  have hpi := Real.pi_gt_three
  have he : (1 : ℝ) / 10 < Real.pi / 6 := by linarith
  refine ⟨1 / 10, 1 / 10, 16, by norm_num, he, by norm_num, he, by norm_num,
    fun _ => clusterOmega_three_two_ne_principal,
    fun _ => clusterOmega_three_two_ne_principal_conj,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro δ _ _ a b _; exact Subsingleton.elim a b
  · intro δ hδ hδe i
    rw [show ftPrincipal jointTau δ = jointPrincipal δ from rfl,
      ← conj_jointPrincipal δ,
      jointRootSet_erase_pair (mem_arc_lower hδ hδe), Finset.mem_singleton]
    rfl
  · intro δ hδ hδe
    rw [show ftPrincipal jointTau δ = jointPrincipal δ from rfl,
      ← conj_jointPrincipal δ,
      jointRootSet_erase_pair (mem_arc_lower hδ hδe), Finset.card_singleton]
  · intro i δ hδ hδe; exact jointCluster_hexp_lower i hδ hδe
  · intro δ _ _ a b _; exact Subsingleton.elim a b
  · intro δ hδ hδe i
    rw [show ftPrincipal jointTau (Real.pi / 3 - δ) = jointPrincipal (Real.pi / 3 - δ) from rfl,
      ← conj_jointPrincipal (Real.pi / 3 - δ),
      jointRootSet_erase_pair (mem_arc_upper hδ hδe), Finset.mem_singleton]
    rfl
  · intro δ hδ hδe
    rw [show ftPrincipal jointTau (Real.pi / 3 - δ) = jointPrincipal (Real.pi / 3 - δ) from rfl,
      ← conj_jointPrincipal (Real.pi / 3 - δ),
      jointRootSet_erase_pair (mem_arc_upper hδ hδe), Finset.card_singleton]
  · intro i δ hδ hδe; exact jointCluster_hexp_upper i hδ hδe

/-! ### The remaining retained-set binders

`hroot` and `huniq` are `jointDen_eval_eq_zero_iff`; `hτpos` is `jointTau_pos`.
What is left is `hsimple`, `haR` and `hne`. -/

theorem jointZ_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 3)) : 0 < jointZ θ := by
  have hc := cos_add_pi_div_six_pos hθ
  have hs : (0 : ℝ) < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [Real.pi_pos, hθ.2])
  rw [jointZ, jointRho]
  positivity

/-- **`hsimple`**, and it needs no case split over the three zeros.

That is a property of the pencil rather than of the route here.  A common zero of
`D` and `D'` forces `za² = 0` directly — one `linear_combination` — and `z > 0`
on the arc while `D(0) = 1`, so no root of `D` is a root of `D'` whatever the
three roots happen to be.  The sibling witness at `Q = 1 - t` has no such
shortcut and argues per root, the real zero by sign and the pair by imaginary
part; the asymmetry is in the pencils, not in how hard each was tried. -/
theorem jointDen_deriv_ne_zero {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 3))
    {a : ℂ} (ha : (ftDen jointQ 3 ((jointZ θ : ℝ) : ℂ)).eval a = 0) :
    (derivative (ftDen jointQ 3 ((jointZ θ : ℝ) : ℂ))).eval a ≠ 0 := by
  have hz : ((jointZ θ : ℝ) : ℂ) ≠ 0 := by
    have := jointZ_pos hθ
    simpa using this.ne'
  rw [ftDen, jointQ] at ha ⊢
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_C,
    Polynomial.derivative_pow, Polynomial.derivative_sub, Polynomial.derivative_one,
    Polynomial.derivative_X, Polynomial.eval_zero, zero_mul, zero_add, mul_one,
    Nat.cast_ofNat] at ha ⊢
  intro hd
  norm_num at hd
  -- `za² = 0` from the two, then `a = 0` and `D(0) = 1`
  have hkey : ((jointZ θ : ℝ) : ℂ) * a ^ 2 = 0 := by
    linear_combination ha + ((1 - a) / 3) * hd
  rcases mul_eq_zero.mp hkey with h | h
  · exact hz h
  · have ha0 : a = 0 := by
      simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
    rw [ha0] at ha
    norm_num at ha

/-- **`haR`**: radius `2` holds the retained set wherever the arc is kept away
from `θ = π/6`.

**The gap hypothesis is necessary, not a convenience.**  No radius holds the
retained set across the whole arc: `‖t₃‖ = cos(θ+π/6)/(√3|cos(θ+π/3)|)` runs to
infinity as `θ → π/6`.  So this is a third consequence of the degeneracy, and
not the same one as the clusters emptying — that one is repaired by excluding a
neighbourhood of `π/6` from a window, this one by refusing to state the bound on
the bare arc at all.  Both binder windows do supply `|cos(θ+π/3)| ≥ 2/5`, but a
reader must not take that as evidence the arc version is true. -/
theorem norm_lt_two_of_mem_jointRootSet {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 3))
    (hgap : 2 / 5 ≤ |Real.cos (θ + Real.pi / 3)|) {a : ℂ} (ha : a ∈ jointRootSet θ) :
    ‖a‖ < 2 := by
  have hc := cos_add_pi_div_six_pos hθ
  have hc1 : Real.cos (θ + Real.pi / 6) ≤ 1 := Real.cos_le_one _
  have hs3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hs32 : (3 : ℝ) / 2 < Real.sqrt 3 := by nlinarith [h3, hs3]
  have hτ : jointTau θ < 2 := by
    rw [jointTau, div_lt_iff₀ hs3]; nlinarith [hc1, hs32]
  have hnp : ‖jointPrincipal θ‖ = jointTau θ := by
    rw [jointPrincipal, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (jointTau_pos hθ), Complex.norm_exp_ofReal_mul_I, mul_one]
  rw [jointRootSet] at ha
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl
  · rw [hnp]; exact hτ
  · rw [RCLike.norm_conj, hnp]; exact hτ
  · rw [Complex.norm_real, Real.norm_eq_abs, jointThird, abs_div, abs_of_pos hc,
      abs_mul, abs_of_pos hs3, div_lt_iff₀ (by positivity)]
    nlinarith [hc1, hs32, hgap, hs3]

/-- **`hne`**: the principal point is not its own conjugate. -/
theorem jointPrincipal_ne_conj {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 3)) :
    ftPrincipal jointTau θ
      ≠ ((jointTau θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * Complex.I) := by
  rw [show ftPrincipal jointTau θ = jointPrincipal θ from rfl, ← conj_jointPrincipal]
  intro h
  have him := jointPrincipal_im hθ
  have : (jointPrincipal θ).im = -(jointPrincipal θ).im := by
    conv_lhs => rw [h]
    simp
  linarith

/-! ### Why the repaired chart is right rather than merely workable

The endpoint binders were re-routed to the *punctured* window `0 < δ ≤ e₁`, and
the striking thing is not that the proofs became possible — it is that they
became **arithmetic**.  Excluding the endpoint puts every quantity at the far end
of its range rather than at a singularity:

* `hCbd₁` is a triangle inequality, because `z` is *large* on the window
  (`z ≥ 64`) rather than small — no root structure and no compactness enter the
  denominator at all.
* `hamp₁` is a closed-form rate, because `τ` is *linear* on the window
  (`τ = (2/√3)sin η`) rather than merely tending to zero.
* `hτle₁`, `haR₁` and `hDsph₁` are numeric comparisons for the same reason.

Both are consequences of excluding the endpoint, which is the thing the old chart
could not do — and it is the best available evidence that the new chart is the
right one and not just a way around the refutations. -/

/-! ### The two endpoint data groups are not alike, and the upper one is refuted

`weighted_dominance_of_branch` carries, at each endpoint, a datum `te` with
`hte : te ≠ 0` pinned to the branch by `hγ0 : ftPrincipal τ (endpoint) = te`.
Together those say `τ` does not vanish at the endpoint.

At the lower endpoint that holds here: `τ(0) = (2/√3)cos(π/6) = 1`.

**At the upper endpoint it is false, and false at exactly the pencils whose upper
cluster is non-empty.**  `b = π/r` is what `hexp₁`'s coefficient encodes — it is
written `(cos(π/r) - Re ω)/sin(π/r)` over `clusterOmega r`, which is the
`θ → π/r` asymptotics — and `τ(π/3) = (2/√3)cos(π/2) = 0`.  So `hγ0₁` forces
`te₁ = 0` and `hte₁` refutes it.

The same holds at `Q = 1 - t`, `r = 3`: `upperTau(π/3) = (4cos²(π/3) - 1)/(2cos(π/3)) = 0`.
It does *not* hold at `r = 1`, where the arc ends at `π` and `cubicTau(π) = 1/2`.
The mechanism is the one `hn₁r` already names from the other side: the upper
cluster is empty unless `r ≥ 2`, and at `r ≥ 2` the whole retained set collapses
to the origin as `θ → π/r`, taking `τ` with it.  So the upper *endpoint* group
and the upper *cluster* group are satisfiable at disjoint sets of pencils, at
least among the three carried here. -/

theorem jointTau_upper_endpoint : jointTau (Real.pi / 3) = 0 := by
  rw [jointTau, show Real.pi / 3 + Real.pi / 6 = Real.pi / 2 by ring,
    Real.cos_pi_div_two]
  norm_num

theorem ftPrincipal_jointTau_upper : ftPrincipal jointTau (Real.pi / 3) = 0 := by
  rw [show ftPrincipal jointTau (Real.pi / 3) = jointPrincipal (Real.pi / 3) from rfl,
    jointPrincipal, jointTau_upper_endpoint]
  simp

/-- **`hte₁` and `hγ0₁` cannot both hold at this pencil's upper endpoint.** -/
theorem no_upper_endpoint_datum :
    ¬ ∃ te₁ : ℂ, te₁ ≠ 0 ∧ ftPrincipal jointTau (Real.pi / 3 - 0) = te₁ := by
  rintro ⟨te₁, hne, h⟩
  rw [sub_zero, ftPrincipal_jointTau_upper] at h
  exact hne h.symm

/-! ### The lower endpoint group, which is satisfiable -/

theorem jointTau_zero : jointTau 0 = 1 := by
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hs3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  rw [jointTau, zero_add, Real.cos_pi_div_six, div_eq_iff hs3.ne']
  linarith [h3]

/-- `te₀ = 1`, so `hte₀` holds. -/
theorem ftPrincipal_jointTau_zero : ftPrincipal jointTau 0 = 1 := by
  rw [show ftPrincipal jointTau 0 = jointPrincipal 0 from rfl, jointPrincipal,
    jointTau_zero]
  simp

theorem jointRho_zero : jointRho 0 = 0 := by rw [jointRho, Real.sin_zero]; simp

theorem jointZ_zero : jointZ 0 = 0 := by rw [jointZ, jointRho_zero]; norm_num

/-- **`hk₀`**: the branch starts at the triple zero of `Q`, so the multiplicity
is `ρ = 3`, comfortably above the `1` the binder asks for. -/
theorem one_le_rootMultiplicity_jointDen_zero :
    1 ≤ (ftDen jointQ 3 ((jointZ 0 : ℝ) : ℂ)).rootMultiplicity
      (ftPrincipal jointTau 0) := by
  rw [ftPrincipal_jointTau_zero, jointZ_zero]
  have hden : ftDen jointQ 3 ((0 : ℝ) : ℂ) = jointQ := by
    rw [ftDen]; norm_num
  rw [hden, jointQ]
  have hne : ((1 : ℂ[X]) - Polynomial.X) ^ 3 ≠ 0 := by
    apply pow_ne_zero
    intro h
    have := congrArg (Polynomial.eval (0 : ℂ)) h
    simp at this
  rw [Polynomial.le_rootMultiplicity_iff hne]
  exact ⟨-(1 - Polynomial.X) ^ 2, by rw [Polynomial.C_1]; ring⟩

/-- **`hrootev₀`**: the principal point is a zero of the pencil throughout a
right neighbourhood of `0`, not merely eventually. -/
theorem eventually_jointDen_eval_principal :
    ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (ftDen jointQ 3 ((jointZ δ : ℝ) : ℂ)).eval (ftPrincipal jointTau δ) = 0 := by
  have hpi := Real.pi_pos
  have hmem : Set.Ioo (0 : ℝ) (Real.pi / 3) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
    rw [← Set.Ioi_inter_Iio]
    exact inter_mem_nhdsWithin _ (Iio_mem_nhds (by positivity))
  filter_upwards [hmem] with δ hδ
  rw [show ftPrincipal jointTau δ = jointPrincipal δ from rfl]
  exact jointDen_eval_principal hδ

/-- **`hn₁r`**: free at `r = 3`. -/
theorem joint_hn₁r : 0 < 1 → 2 ≤ 3 := fun _ => by norm_num

/-! ### `hL₁`, and what the upper amplitude ratio's limit is

`hratio₁` sends the amplitude ratio to `L₁ i`, and `hL₁` asks `‖L₁ i‖ = 1`.  At
this pencil the limit is the cluster direction over the principal direction,
`ω₂/e^{iπ/3}`, and that is `e^{2πi/3}` — which is `jointEta`, the very cube root
of unity the sum-of-cubes factorization runs on.  The numerator plays no part:
`B(0) ≠ 0`, so `B` does not vanish on this cluster and cancels from the ratio.
`scripts/check_joint_witness.py` measures it at three numerators. -/

/-- `e^{iπ/3}` in components.  Stated with `rw` rather than reached by `simp`,
because normalizing the cast to `↑π/3` stops `Complex.exp_ofReal_mul_I_re` from
matching. -/
theorem exp_pi_div_three :
    Complex.exp (((Real.pi / 3 : ℝ) : ℂ) * Complex.I)
      = ⟨1 / 2, Real.sqrt 3 / 2⟩ := by
  apply Complex.ext
  · rw [Complex.exp_ofReal_mul_I_re, Real.cos_pi_div_three]
  · rw [Complex.exp_ofReal_mul_I_im, Real.sin_pi_div_three]

theorem jointEta_mul_principal_dir :
    jointEta * Complex.exp (((Real.pi / 3 : ℝ) : ℂ) * Complex.I) = clusterOmega 3 2 := by
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  rw [clusterOmega_three_two, exp_pi_div_three]
  apply Complex.ext <;>
    simp [jointEta, Complex.mul_re, Complex.mul_im] <;> nlinarith [h3]

/-- **`hL₁`**: the limit is unimodular. -/
theorem norm_jointEta : ‖jointEta‖ = 1 := by
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  rw [Complex.norm_def, Complex.normSq_apply]
  simp only [jointEta]
  rw [show -(1 / 2 : ℝ) * -(1 / 2) + Real.sqrt 3 / 2 * (Real.sqrt 3 / 2) = 1 by
    nlinarith [h3]]
  exact Real.sqrt_one

/-! ### `hratio₁`: the amplitude ratio is a ratio of normalized roots

`ftAmp_eq_ftCritical` writes the amplitude as `-tB(t)/E(t)` with
`E = tQ' - rQ`, which does not involve `z`.  At this pencil `E` collapses:

`E(t) = t·(-3(1-t)²) - 3(1-t)³ = -3(1-t)²[t + (1-t)] = -3(1-t)²`

so `𝒲(t) = tB(t)/(3(1-t)²)` and the ratio of two amplitudes is

`𝒲(g)/𝒲(t₊) = (g/t₊) · (B(g)/B(t₊)) · ((1-t₊)/(1-g))²`.

Both zeros go to the origin at the upper endpoint, so the last two factors go to
`1` — the second because `B(0) ≠ 0`, which is `hQ0`'s companion — and the limit
is `g/t₊ = ζ₃/ζ₊`, a ratio of *normalized* roots with the `τ` cancelled.

**Nothing here involves the amplitude's order at the endpoint.**  The `τ` cancels
between one numerator and one denominator, so no exponent survives; the ratio is
insensitive to how the principal amplitude is bounded below. -/

theorem jointCritical_eval (t : ℂ) :
    (ftCritical jointQ 3).eval t = -3 * (1 - t) ^ 2 := by
  rw [ftCritical, jointQ]
  simp [Polynomial.derivative_pow, Polynomial.derivative_sub]
  ring

/-- `𝒲(t) = tB(t)/(3(1-t)²)` at this pencil, for any zero of the pencil other
than `1` — and `1` is never a zero, since `jointQ.eval 1 = 0` forces `z = 0`. -/
theorem jointAmp_eval {B : Polynomial ℂ} {z t : ℂ} (ht : t ≠ 0) (ht1 : t ≠ 1)
    (hroot : (ftDen jointQ 3 z).eval t = 0) :
    ftAmp jointQ B 3 z t = t * B.eval t / (3 * (1 - t) ^ 2) := by
  rw [ftAmp_eq_ftCritical (by norm_num) ht hroot, jointCritical_eval]
  have h1 : (1 : ℂ) - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht1)
  field_simp

/-- **The ratio, in closed form.**  Every factor but `g/t₊` tends to `1`, and no
exponent from the endpoint order appears. -/
theorem jointAmp_ratio {B : Polynomial ℂ} {z g tp : ℂ}
    (hg : g ≠ 0) (hg1 : g ≠ 1) (htp : tp ≠ 0) (htp1 : tp ≠ 1)
    (hBg : B.eval g ≠ 0) (hBp : B.eval tp ≠ 0)
    (hrg : (ftDen jointQ 3 z).eval g = 0) (hrp : (ftDen jointQ 3 z).eval tp = 0) :
    ftAmp jointQ B 3 z g / ftAmp jointQ B 3 z tp
      = (g / tp) * (B.eval g / B.eval tp) * ((1 - tp) / (1 - g)) ^ 2 := by
  have h1g : (1 : ℂ) - g ≠ 0 := sub_ne_zero.mpr (Ne.symm hg1)
  have h1p : (1 : ℂ) - tp ≠ 0 := sub_ne_zero.mpr (Ne.symm htp1)
  rw [jointAmp_eval hg hg1 hrg, jointAmp_eval htp htp1 hrp]
  field_simp

/-! ### Two normalizer traps in the derivative and limit plumbing

Both cost a rewritten block, and in both the thing a reader tries first does not
work.

**`HasDerivAt.mul` on lambdas leaves `((fun s => …) * fun s => …) δ`** rather
than a product of values, so `ring` cannot see it.  `simp only [Pi.mul_apply]`
before `ring` fixes it, and that is why the `congr_deriv` blocks below carry it.

**`Filter.Tendsto.div` leaves `Pi.div` rather than a pointwise quotient, and
`simp` cannot reach it** — it sits inside the *function argument* of a `Tendsto`,
where simp does not rewrite.  **Adding `Pi.div_apply` to the simp set does
nothing**, which is the natural thing to try and the reason this note exists.
What works is `have h := …; rw […] at h; exact h`, relying on `f / g` and
`fun x => f x / g x` being definitionally equal.  **The `.mul` fix does not
transfer**, and assuming it does is what cost the rewrite.

A third of the same kind: `(Complex.continuous_ofReal.tendsto _).comp f` yields
`ofReal ∘ f` where the goal wants `fun δ => ↑(f δ)`.  There `Function.comp_def`
in the `simpa` is enough, because the mismatch is in the term rather than under
a binder simp will not enter. -/

/-! ### The three convergences

`jointAmp_ratio` leaves three factors.  Two go to `1` because both zeros go to
the origin; the third is the whole limit.

**`B` dropping out is not an accident of the numerators tested.**  Both zeros
reach the origin and `B(0) ≠ 0`, so `B` does not vanish on the upper cluster at
all — which is exactly what the paper says at this endpoint, and exactly why the
correct endpoint lemma gives its exponent unconditionally.  The algebra here, the
paper's sentence and that exponent are three independent arrivals at one fact. -/

theorem continuousAt_jointRatio {δ : ℝ} (h : Real.cos (δ + Real.pi / 3) ≠ 0) :
    ContinuousAt jointRatio δ := (hasDerivAt_jointRatio h).continuousAt

theorem cos_pi_div_three_ne : Real.cos ((0 : ℝ) + Real.pi / 3) ≠ 0 := by
  rw [zero_add, Real.cos_pi_div_three]; norm_num

/-- `ζ₃(π/3 - δ) → -1`: the normalized nonprincipal member reaches the cube root
of `-1` that is not principal. -/
theorem tendsto_jointRatio_upper :
    Filter.Tendsto (fun δ : ℝ => jointRatio (Real.pi / 3 - δ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (-1)) := by
  have h1 : Filter.Tendsto jointRatio (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 1) := by
    have hc := (continuousAt_jointRatio cos_pi_div_three_ne).continuousWithinAt
      (s := Set.Ioi (0 : ℝ))
    rwa [ContinuousWithinAt, jointRatio_zero] at hc
  simp only [jointRatio_reflect]
  simpa using h1.neg

theorem jointEta_eq_neg_exp :
    jointEta = (-1 : ℂ) * Complex.exp (-((Real.pi / 3 : ℝ) : ℂ) * Complex.I) := by
  have h := jointEta_mul_principal_dir
  rw [clusterOmega_three_two] at h
  refine mul_right_cancel₀ (Complex.exp_ne_zero (((Real.pi / 3 : ℝ) : ℂ) * Complex.I)) ?_
  rw [h, mul_assoc, ← Complex.exp_add,
    show -((Real.pi / 3 : ℝ) : ℂ) * Complex.I + ((Real.pi / 3 : ℝ) : ℂ) * Complex.I = 0 by ring,
    Complex.exp_zero, mul_one]

/-- **The limit of `g/t₊`**, which is `jointAmp_ratio`'s only surviving factor:
`ζ₃/ζ₊ → -1/e^{iπ/3} = e^{2πi/3} = jointEta`.  The `τ` has already cancelled, so
no exponent from the endpoint order can appear here. -/
theorem tendsto_joint_normalized_quotient :
    Filter.Tendsto
      (fun δ : ℝ => ((jointRatio (Real.pi / 3 - δ) : ℝ) : ℂ)
        * Complex.exp (-((Real.pi / 3 - δ : ℝ) : ℂ) * Complex.I))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds jointEta) := by
  have hr : Filter.Tendsto (fun δ : ℝ => ((jointRatio (Real.pi / 3 - δ) : ℝ) : ℂ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds ((-1 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp tendsto_jointRatio_upper
  have hs : Filter.Tendsto (fun δ : ℝ => -((Real.pi / 3 - δ : ℝ) : ℂ) * Complex.I)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (-((Real.pi / 3 : ℝ) : ℂ) * Complex.I)) := by
    apply Filter.Tendsto.mul_const
    apply Filter.Tendsto.neg
    exact (Complex.continuous_ofReal.tendsto _).comp
      (((continuous_const.sub continuous_id).tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
        |>.congr' (by filter_upwards with x using rfl) |>.congr (by intro x; rfl)
        |>.mono_right (by simp))
  have he : Filter.Tendsto (fun δ : ℝ => Complex.exp (-((Real.pi / 3 - δ : ℝ) : ℂ) * Complex.I))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (Complex.exp (-((Real.pi / 3 : ℝ) : ℂ) * Complex.I))) :=
    (Complex.continuous_exp.tendsto _).comp hs
  rw [jointEta_eq_neg_exp]
  simpa using hr.mul he

/-! ### The other two factors, which go to `1` because both zeros reach the origin

**`B` dropping out is not an accident of the numerators tested.**  Both zeros
reach the origin and `B(0) ≠ 0`, so `B` does not vanish on the upper cluster at
all — no `ν_B`, no `ρ-1`.  That is what the paper says at this endpoint and what
makes the correct endpoint lemma's exponent unconditional. -/

theorem jointThird_upper_endpoint : jointThird (Real.pi / 3) = 0 := by
  rw [jointThird, show Real.pi / 3 + Real.pi / 6 = Real.pi / 2 by ring,
    Real.cos_pi_div_two]
  simp

theorem cos_two_pi_div_three_ne : Real.cos (Real.pi / 3 + Real.pi / 3) ≠ 0 := by
  rw [show Real.pi / 3 + Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub,
    Real.cos_pi_div_three]
  norm_num

theorem tendsto_jointTau_upper :
    Filter.Tendsto (fun δ : ℝ => jointTau (Real.pi / 3 - δ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hc : Continuous (fun δ : ℝ => jointTau (Real.pi / 3 - δ)) := by
    unfold jointTau; fun_prop
  have h := hc.tendsto 0
  rw [sub_zero, jointTau_upper_endpoint] at h
  exact h.mono_left nhdsWithin_le_nhds

theorem tendsto_jointThird_upper :
    Filter.Tendsto (fun δ : ℝ => jointThird (Real.pi / 3 - δ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hs3 : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hc : ContinuousAt (fun δ : ℝ => jointThird (Real.pi / 3 - δ)) 0 := by
    unfold jointThird
    refine ContinuousAt.div (by fun_prop) (by fun_prop) ?_
    simpa using mul_ne_zero hs3 cos_two_pi_div_three_ne
  have h := hc.tendsto
  rw [sub_zero, jointThird_upper_endpoint] at h
  exact h.mono_left nhdsWithin_le_nhds

theorem tendsto_jointThird_upper_complex :
    Filter.Tendsto (fun δ : ℝ => ((jointThird (Real.pi / 3 - δ) : ℝ) : ℂ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  simpa [Function.comp_def] using
    (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp tendsto_jointThird_upper

theorem tendsto_jointPrincipal_upper :
    Filter.Tendsto (fun δ : ℝ => jointPrincipal (Real.pi / 3 - δ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hτ : Filter.Tendsto (fun δ : ℝ => ((jointTau (Real.pi / 3 - δ) : ℝ) : ℂ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    simpa [Function.comp_def] using
      (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp tendsto_jointTau_upper
  have he : Filter.Tendsto
      (fun δ : ℝ => Complex.exp (((Real.pi / 3 - δ : ℝ) : ℂ) * Complex.I))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (Complex.exp (((Real.pi / 3 : ℝ) : ℂ) * Complex.I))) := by
    have hc : Continuous
        (fun δ : ℝ => Complex.exp (((Real.pi / 3 - δ : ℝ) : ℂ) * Complex.I)) := by fun_prop
    have h := hc.tendsto 0
    rw [sub_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  simpa [jointPrincipal] using hτ.mul he

/-- **The numerator factor**, and it cancels entirely. -/
theorem tendsto_jointB_ratio {B : Polynomial ℂ} (hB : B.eval 0 ≠ 0) :
    Filter.Tendsto
      (fun δ : ℝ => B.eval ((jointThird (Real.pi / 3 - δ) : ℝ) : ℂ)
        / B.eval (jointPrincipal (Real.pi / 3 - δ)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 1) := by
  have hg : Filter.Tendsto (fun δ : ℝ => B.eval ((jointThird (Real.pi / 3 - δ) : ℝ) : ℂ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (B.eval 0)) := by
    simpa [Function.comp_def] using
      (B.continuous.tendsto (0 : ℂ)).comp tendsto_jointThird_upper_complex
  have hp : Filter.Tendsto (fun δ : ℝ => B.eval (jointPrincipal (Real.pi / 3 - δ)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (B.eval 0)) := by
    simpa [Function.comp_def] using
      (B.continuous.tendsto (0 : ℂ)).comp tendsto_jointPrincipal_upper
  have h := hg.div hp hB
  rw [div_self hB] at h
  exact h

/-- **The `(1-t)` factor.** -/
theorem tendsto_joint_one_sub_ratio :
    Filter.Tendsto
      (fun δ : ℝ => ((1 - jointPrincipal (Real.pi / 3 - δ))
        / (1 - ((jointThird (Real.pi / 3 - δ) : ℝ) : ℂ))) ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 1) := by
  have hg : Filter.Tendsto (fun δ : ℝ => 1 - ((jointThird (Real.pi / 3 - δ) : ℝ) : ℂ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 1) := by
    simpa using tendsto_const_nhds.sub tendsto_jointThird_upper_complex
  have hp : Filter.Tendsto (fun δ : ℝ => 1 - jointPrincipal (Real.pi / 3 - δ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 1) := by
    simpa using tendsto_const_nhds.sub tendsto_jointPrincipal_upper
  simpa using (hp.div hg one_ne_zero).pow 2

/-! ### `hzc₁` is refuted too, and by the same collapse

`hte₁` is not the only upper-endpoint binder the collapse defeats.  `hzc₁` asks
for `ContinuousOn (fun δ => z(b - δ)) (Icc 0 e₁)` — on a *closed* interval
containing the endpoint.  But the endpoint is where the branch runs out:

`ρ(π/3 - δ) = sin(π/3 - δ)/cos(π/2 - δ) = sin(π/3 - δ)/sin δ`

so `z = ρ³` grows like `δ^{-3}`.  A continuous function on a compact set is
bounded, and this one is not bounded on any `Icc 0 e`, so the binder cannot
hold.  Two binders of that group are therefore refuted rather than one, which
says the repair is to the *group's chart* rather than to `hte₁` alone. -/

theorem jointRho_upper_eq (δ : ℝ) :
    jointRho (Real.pi / 3 - δ) = Real.sin (Real.pi / 3 - δ) / Real.sin δ := by
  rw [jointRho, show Real.pi / 3 - δ + Real.pi / 6 = Real.pi / 2 - δ by ring,
    Real.cos_pi_div_two_sub]

/-- The spectral parameter is unbounded on every right neighbourhood of the
upper endpoint. -/
theorem jointZ_upper_unbounded {e : ℝ} (he : 0 < e) (hee : e < Real.pi / 3) (C : ℝ) :
    ∃ δ ∈ Set.Icc (0 : ℝ) e, C < ‖((jointZ (Real.pi / 3 - δ) : ℝ) : ℂ)‖ := by
  have hpi := Real.pi_pos
  have hs : 0 < Real.sin (Real.pi / 3 - e) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  set M := max 1 C with hM
  have hM1 : (1 : ℝ) ≤ M := le_max_left _ _
  have hMC : C ≤ M := le_max_right _ _
  set δ := min e (Real.sin (Real.pi / 3 - e) / (M + 1)) with hδdef
  have hδ0 : 0 < δ := by
    rw [hδdef]; positivity
  have hδe : δ ≤ e := min_le_left _ _
  have hδs : δ ≤ Real.sin (Real.pi / 3 - e) / (M + 1) := min_le_right _ _
  have hsin_le : Real.sin δ ≤ δ := Real.sin_le hδ0.le
  have hsin_pos : 0 < Real.sin δ :=
    Real.sin_pos_of_pos_of_lt_pi hδ0 (by linarith)
  have hnum : Real.sin (Real.pi / 3 - e) ≤ Real.sin (Real.pi / 3 - δ) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith)
  have hρ : M + 1 ≤ jointRho (Real.pi / 3 - δ) := by
    rw [jointRho_upper_eq, le_div_iff₀ hsin_pos]
    calc (M + 1) * Real.sin δ ≤ (M + 1) * δ := by nlinarith [hsin_le, hM1]
      _ ≤ Real.sin (Real.pi / 3 - e) := by
          rw [← le_div_iff₀' (by linarith : (0:ℝ) < M + 1)]; exact hδs
      _ ≤ Real.sin (Real.pi / 3 - δ) := hnum
  have hρ1 : (1 : ℝ) ≤ jointRho (Real.pi / 3 - δ) := by linarith
  refine ⟨δ, ⟨hδ0.le, hδe⟩, ?_⟩
  rw [Complex.norm_real, Real.norm_eq_abs, jointZ,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ jointRho (Real.pi / 3 - δ) ^ 3)]
  have hcube : jointRho (Real.pi / 3 - δ) ≤ jointRho (Real.pi / 3 - δ) ^ 3 := by
    have h0 : (0 : ℝ) ≤ jointRho (Real.pi / 3 - δ) := by linarith
    nlinarith [hρ1, h0, mul_nonneg h0 (by linarith : (0:ℝ) ≤ jointRho (Real.pi / 3 - δ) - 1)]
  linarith

/-- **`hzc₁` cannot hold at this pencil.** -/
theorem no_upper_z_continuity {e : ℝ} (he : 0 < e) (hee : e < Real.pi / 3) :
    ¬ ContinuousOn (fun δ : ℝ => ((jointZ (Real.pi / 3 - δ) : ℝ) : ℂ))
      (Set.Icc 0 e) := by
  intro hc
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0:ℝ)) (b := e)).exists_bound_of_continuousOn hc
  obtain ⟨δ, hδ, hlt⟩ := jointZ_upper_unbounded he hee C
  exact absurd (hC δ hδ) (not_le.mpr hlt)

/-! ### The upper-endpoint binders the collapse does *not* defeat

`hte₁` and `hzc₁` are refuted because they evaluate at the endpoint.  The rest of
that group is stated on `0 < δ ≤ e₁`, never at `δ = 0`, and those are all
satisfiable here.  `τ` has a closed form on the upper window that makes them
arithmetic:

`τ(π/3 - δ) = (2/√3)cos(π/2 - δ) = (2/√3)sin δ`

so `τ → 0` linearly, and the whole retained set is inside a fixed small disc. -/

theorem jointTau_upper_eq (δ : ℝ) :
    jointTau (Real.pi / 3 - δ) = 2 * Real.sin δ / Real.sqrt 3 := by
  rw [jointTau, show Real.pi / 3 - δ + Real.pi / 6 = Real.pi / 2 - δ by ring,
    Real.cos_pi_div_two_sub]

/-- **`hτle₁`** at `e₁ = 1/10`, with `τmax₁ = 1/8`. -/
theorem jointTau_upper_le {δ : ℝ} (hδ : 0 < δ) (hδe : δ ≤ 1 / 10) :
    jointTau (Real.pi / 3 - δ) ≤ 1 / 8 := by
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hs3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have h32 : (3 : ℝ) / 2 < Real.sqrt 3 := by nlinarith [h3, hs3]
  have hsin : Real.sin δ ≤ δ := Real.sin_le hδ.le
  have hsin0 : 0 ≤ Real.sin δ := Real.sin_nonneg_of_nonneg_of_le_pi hδ.le
    (by linarith [Real.pi_gt_three])
  rw [jointTau_upper_eq, div_le_iff₀ hs3]
  nlinarith [hsin, hsin0, h32, hδe]

/-- Every retained zero sits well inside the half-disc on the upper window. -/
theorem norm_lt_half_of_mem_jointRootSet_upper {δ : ℝ} (hδ : 0 < δ) (hδe : δ ≤ 1 / 10)
    {a : ℂ} (ha : a ∈ jointRootSet (Real.pi / 3 - δ)) : ‖a‖ < 1 / 2 := by
  have hθ := mem_arc_upper hδ hδe
  have hτ0 := jointTau_pos hθ
  have hτ := jointTau_upper_le hδ hδe
  have hcos := cos_add_pi_div_three_ge ⟨hδ.le, hδe⟩
  have hratio : jointRatio δ ≤ 5 / 4 := by
    rw [jointRatio, div_le_iff₀ (by linarith)]
    linarith
  have hratio0 : 0 < jointRatio δ := by rw [jointRatio]; positivity
  have hnp : ‖jointPrincipal (Real.pi / 3 - δ)‖ = jointTau (Real.pi / 3 - δ) := by
    rw [jointPrincipal, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hτ0, Complex.norm_exp_ofReal_mul_I, mul_one]
  rw [jointRootSet] at ha
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl
  · rw [hnp]; linarith
  · rw [RCLike.norm_conj, hnp]; linarith
  · rw [Complex.norm_real, Real.norm_eq_abs,
      show jointThird (Real.pi / 3 - δ)
          = jointRatio (Real.pi / 3 - δ) * jointTau (Real.pi / 3 - δ) by
        rw [← jointThird_div_jointTau hθ (cos_upper_ne hδ hδe)]
        exact (div_mul_cancel₀ _ hτ0.ne').symm,
      jointRatio_reflect, abs_mul, abs_neg, abs_of_pos hratio0, abs_of_pos hτ0]
    nlinarith [hratio, hτ, hτ0, hratio0]

/-- **`hDsph₁`** at `R₁ = 1/2`: the pencil has no zero on that circle anywhere on
the closed window.

**It holds at `δ = 0` for a reason unrelated to what it was written to test, and
that is worth knowing before reading it as evidence.**  There `z` takes Lean's
division-by-zero value, so the pencil is `Q` itself, whose only zero is at `1`,
and `‖1‖ ≠ 1/2`.  The binder is therefore discharged *without probing the
endpoint at all* — where the branch actually runs out and `z` is unbounded.

This is the inverse of the situation in `no_upper_z_continuity`, where the same
junk value is what *creates* the discontinuity that refutes `hzc₁`.  Both are
facts about `δ = 0` and neither is evidence about the other: a binder that holds
for a reason unrelated to its purpose looks exactly like a binder that holds. -/
theorem jointDen_ne_zero_on_sphere_upper {δ : ℝ} (hδ : δ ∈ Set.Icc (0 : ℝ) (1 / 10))
    {t : ℂ} (ht : ‖t‖ = 1 / 2) :
    (ftDen jointQ 3 ((jointZ (Real.pi / 3 - δ) : ℝ) : ℂ)).eval t ≠ 0 := by
  rcases eq_or_lt_of_le hδ.1 with h | h
  · -- `δ = 0`: `z` is the junk value `0`, so the pencil is `Q = (1 - X)³`
    have hz : jointZ (Real.pi / 3 - δ) = 0 := by
      rw [← h, sub_zero, jointZ, jointRho,
        show Real.pi / 3 + Real.pi / 6 = Real.pi / 2 by ring, Real.cos_pi_div_two]
      norm_num
    rw [hz]
    have hden : ftDen jointQ 3 ((0 : ℝ) : ℂ) = jointQ := by rw [ftDen]; norm_num
    rw [hden, jointQ]
    simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_one,
      Polynomial.eval_X]
    intro hc
    have h1 : t = 1 := by
      have := pow_eq_zero_iff (n := 3) (by norm_num) |>.mp hc
      linear_combination -this
    rw [h1] at ht
    norm_num at ht
  · intro hc
    have hmem := (jointDen_eval_eq_zero_iff (mem_arc_upper h hδ.2)
      (cos_upper_ne h hδ.2) t).mp hc
    have := norm_lt_half_of_mem_jointRootSet_upper h hδ.2 hmem
    rw [ht] at this
    exact lt_irrefl _ this

/-! ### `hCbd₁`, the punctured contour bound

The repaired binder asks only for `0 < δ ≤ e₁`, so the endpoint — where `z` is
unbounded and the old closed-window binders failed — is outside it.  That makes
the bound elementary rather than compact: on `‖t‖ = 1/2` the triangle inequality
gives `‖D‖ ≥ z/8 - 27/8`, and `z` is *large* on the window rather than small.

`z = ρ³` with `ρ = sin(π/3 - δ)/sin δ ≥ (2/5)/(1/10) = 4`, so `z ≥ 64` and
`‖D‖ ≥ 37/8 ≥ 4`.  Only the numerator then needs compactness. -/

theorem sin_upper_ge {δ : ℝ} (hδ : 0 < δ) (hδe : δ ≤ 1 / 10) :
    2 / 5 ≤ Real.sin (Real.pi / 3 - δ) := by
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hs3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have h32 : (3 : ℝ) / 2 ≤ Real.sqrt 3 := by nlinarith [h3, hs3]
  have hc : 1 - δ ^ 2 / 2 ≤ Real.cos δ := Real.one_sub_sq_div_two_le_cos
  have hs : Real.sin δ ≤ δ := Real.sin_le hδ.le
  rw [Real.sin_sub, Real.sin_pi_div_three, Real.cos_pi_div_three]
  nlinarith [hc, hs, h32, hδ, hδe]

theorem jointZ_upper_ge {δ : ℝ} (hδ : 0 < δ) (hδe : δ ≤ 1 / 10) :
    64 ≤ jointZ (Real.pi / 3 - δ) := by
  have hsin_pos : 0 < Real.sin δ :=
    Real.sin_pos_of_pos_of_lt_pi hδ (by linarith [Real.pi_gt_three])
  have hsin_le : Real.sin δ ≤ 1 / 10 := le_trans (Real.sin_le hδ.le) hδe
  have hnum := sin_upper_ge hδ hδe
  have hρ : 4 ≤ jointRho (Real.pi / 3 - δ) := by
    rw [jointRho_upper_eq, le_div_iff₀ hsin_pos]
    nlinarith [hsin_le, hnum]
  rw [jointZ]
  calc (64 : ℝ) = 4 ^ 3 := by norm_num
    _ ≤ jointRho (Real.pi / 3 - δ) ^ 3 := by
        exact pow_le_pow_left₀ (by norm_num) hρ 3

/-- The pencil is bounded below on the contour, uniformly over the window. -/
theorem norm_jointDen_sphere_ge {δ : ℝ} (hδ : 0 < δ) (hδe : δ ≤ 1 / 10)
    {t : ℂ} (ht : ‖t‖ = 1 / 2) :
    4 ≤ ‖(ftDen jointQ 3 ((jointZ (Real.pi / 3 - δ) : ℝ) : ℂ)).eval t‖ := by
  have hz := jointZ_upper_ge hδ hδe
  have hzc : ‖((jointZ (Real.pi / 3 - δ) : ℝ) : ℂ)‖ = jointZ (Real.pi / 3 - δ) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have h1 : ‖(1 : ℂ) - t‖ ≤ 3 / 2 := by
    calc ‖(1 : ℂ) - t‖ ≤ ‖(1 : ℂ)‖ + ‖t‖ := norm_sub_le _ _
      _ = 3 / 2 := by rw [norm_one, ht]; norm_num
  have hcube : ‖((1 : ℂ) - t) ^ 3‖ ≤ 27 / 8 := by
    rw [norm_pow]
    calc ‖(1 : ℂ) - t‖ ^ 3 ≤ (3 / 2 : ℝ) ^ 3 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 3
      _ = 27 / 8 := by norm_num
  have hzt : ‖((jointZ (Real.pi / 3 - δ) : ℝ) : ℂ) * t ^ 3‖
      = jointZ (Real.pi / 3 - δ) / 8 := by
    rw [norm_mul, hzc, norm_pow, ht]; ring
  rw [ftDen_eval, jointQ_eval]
  calc (4 : ℝ) ≤ jointZ (Real.pi / 3 - δ) / 8 - 27 / 8 := by linarith
    _ ≤ ‖((jointZ (Real.pi / 3 - δ) : ℝ) : ℂ) * t ^ 3‖ - ‖((1 : ℂ) - t) ^ 3‖ := by
        rw [hzt]; linarith
    _ ≤ ‖((1 : ℂ) - t) ^ 3 + ((jointZ (Real.pi / 3 - δ) : ℝ) : ℂ) * t ^ 3‖ := by
        have := norm_sub_norm_le (((jointZ (Real.pi / 3 - δ) : ℝ) : ℂ) * t ^ 3)
          (-(((1 : ℂ) - t) ^ 3))
        simpa [sub_neg_eq_add, add_comm] using this

/-- **`hCbd₁`** at `R₁ = 1/2`, `e₁ = 1/10`, for any numerator. -/
theorem exists_jointCbd (B : Polynomial ℂ) :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 10 →
      ∀ t ∈ Metric.sphere (0 : ℂ) (1 / 2),
        ‖B.eval t / (ftDen jointQ 3 ((jointZ (Real.pi / 3 - δ) : ℝ) : ℂ)).eval t‖ ≤ C₁ := by
  obtain ⟨M, hM⟩ := (isCompact_sphere (0 : ℂ) (1 / 2)).exists_bound_of_continuousOn
    (B.continuous.continuousOn (s := Metric.sphere (0 : ℂ) (1 / 2)))
  refine ⟨max 0 M / 4, by positivity, fun δ hδ hδe t ht => ?_⟩
  have hts : ‖t‖ = 1 / 2 := by simpa using ht
  have hlow := norm_jointDen_sphere_ge hδ hδe hts
  have hnum : ‖B.eval t‖ ≤ max 0 M := le_trans (hM t ht) (le_max_right _ _)
  rw [norm_div, div_le_div_iff₀ (by linarith) (by norm_num)]
  nlinarith [hnum, hlow, norm_nonneg (B.eval t), le_max_left (0:ℝ) M]

/-! ### `hamp₁`, the amplitude floor, through the origin route

`amplitude_lower_bound_of_origin_form` wants the principal point in the form
`γ(η) = η·T(η)` with `T` continuous at `0` and `T(0) ≠ 0`.  **The fact that
refuted `hte₁` is what supplies it**: `γ(0) = 0` is not an obstruction here, it
is the hypothesis the route consumes, and the collapse being *linear* rather
than merely tending to zero is what makes `T(0)` nonzero.

`τ(π/3 - η) = (2/√3)sin η` gives both at once, with `Real.sinc` carrying the
removable singularity:

`T(η) = (2/√3)·sinc(η)·e^{i(π/3 - η)}`,  `T(0) = (2/√3)e^{iπ/3} ≠ 0`.

**`hT0` is the binder that would refuse a pencil**, and it is where the
non-vacuity sits: `T(0)` is the collapse *rate*, so a pencil whose principal
point reached the origin faster than linearly would have `T(0) = 0` and no floor
of this shape.  Here the rate is `2/√3` in closed form. -/

theorem mul_sinc (x : ℝ) : x * Real.sinc x = Real.sin x := by
  rw [Real.sinc]
  split_ifs with h
  · rw [h]; simp
  · field_simp

noncomputable def jointT (η : ℝ) : ℂ :=
  ((2 / Real.sqrt 3 : ℝ) : ℂ) * ((Real.sinc η : ℝ) : ℂ)
    * Complex.exp (((Real.pi / 3 - η : ℝ) : ℂ) * Complex.I)

theorem continuousWithinAt_jointT : ContinuousWithinAt jointT (Set.Ici (0 : ℝ)) 0 := by
  have : Continuous jointT := by
    unfold jointT
    exact ((continuous_const.mul
      (Complex.continuous_ofReal.comp Real.continuous_sinc)).mul (by fun_prop))
  exact this.continuousWithinAt

/-- `T(0) = (2/√3)e^{iπ/3}`, the collapse rate, and it is nonzero. -/
theorem jointT_zero_ne : jointT 0 ≠ 0 := by
  have hs3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  rw [jointT, Real.sinc]
  simp only [if_pos rfl]
  refine mul_ne_zero (mul_ne_zero ?_ ?_) (Complex.exp_ne_zero _)
  · simpa using (by positivity : (0:ℝ) < 2 / Real.sqrt 3).ne'
  · norm_num

/-- **`hγ`**: the principal point at the upper endpoint is `η·T(η)` exactly. -/
theorem jointPrincipal_upper_eq (η : ℝ) :
    ftPrincipal jointTau (Real.pi / 3 - η) = ((η : ℝ) : ℂ) * jointT η := by
  have hms := mul_sinc η
  rw [show ftPrincipal jointTau (Real.pi / 3 - η)
      = jointPrincipal (Real.pi / 3 - η) from rfl, jointPrincipal,
    jointTau_upper_eq, jointT]
  rw [show ((η : ℝ) : ℂ) * (((2 / Real.sqrt 3 : ℝ) : ℂ) * ((Real.sinc η : ℝ) : ℂ)
        * Complex.exp (((Real.pi / 3 - η : ℝ) : ℂ) * Complex.I))
      = ((η * (2 / Real.sqrt 3) * Real.sinc η : ℝ) : ℂ)
        * Complex.exp (((Real.pi / 3 - η : ℝ) : ℂ) * Complex.I) by push_cast; ring]
  congr 2
  field_simp
  linear_combination -hms

theorem eventually_jointDen_upper_root :
    ∀ᶠ η in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (ftDen jointQ 3 ((jointZ (Real.pi / 3 - η) : ℝ) : ℂ)).eval
        (ftPrincipal jointTau (Real.pi / 3 - η)) = 0 := by
  have hmem : Set.Ioo (0 : ℝ) (1 / 10) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
    rw [← Set.Ioi_inter_Iio]
    exact inter_mem_nhdsWithin _ (Iio_mem_nhds (by norm_num))
  filter_upwards [hmem] with η hη
  rw [show ftPrincipal jointTau (Real.pi / 3 - η)
      = jointPrincipal (Real.pi / 3 - η) from rfl]
  exact jointDen_eval_principal (mem_arc_upper hη.1 hη.2.le)

/-- **`hamp₁` with `p₁ = 1`**, for any numerator not vanishing at the origin. -/
theorem exists_jointAmp_floor {B : Polynomial ℂ} (hB0 : B.eval 0 ≠ 0) :
    ∃ A > (0 : ℝ), ∃ e > (0 : ℝ), ∀ η : ℝ, 0 < η → η ≤ e →
      A * η ≤ ftPrincipalAmp jointQ B 3
        (fun θ => jointZ θ) jointTau (Real.pi / 3 - η) :=
  amplitude_lower_bound_of_origin_form (by norm_num) hB0
    (by rw [jointQ_eval_zero]; norm_num)
    continuousWithinAt_jointT jointT_zero_ne jointPrincipal_upper_eq
    eventually_jointDen_upper_root

end ForgacsTran
