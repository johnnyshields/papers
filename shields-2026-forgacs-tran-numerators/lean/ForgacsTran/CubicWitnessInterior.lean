/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.CubicWitness
import ForgacsTran.DominanceFT

/-!
# `hinterior` at the cubic pencil: the amplitude and window groups

Completes the instantiation of `weighted_dominance_of_branch`'s last binder at
the pencil of `CubicWitness`, `Q(t) = (1-t)^3` with `r = 1`, by supplying a
numerator `B` and a family of deleted windows.

The geometry group is `cubicWitness_interior_geometry`.  What is left is the
amplitude divisor `lem:amplitude-divisor` -- which angles carry a vanishing
residue amplitude -- the branch's own regularity, and the window inequality of
`subsec:proof`.

## The numerator

`B(t) = 3t^2 + 1` is chosen so that `B` vanishes on the branch and does so at an
*interior* angle.  Its zeros are `±i/√3`, of modulus `1/√3`, and
`τ(π/2) = 1/√3` with `γ(π/2) = (1/√3)i`, so `B(γ(θ)) = 0` exactly at `θ = π/2`.
That is the point of the choice: an amplitude divisor that is empty on the arc
would satisfy every clause about `S` by emptying it, and would certify nothing
about the windows -- the clause `∀ θj ∈ S, …` and the window inequality are both
quantified over `S`.

The identification of the zero angle needs no argument of `γ` at all.  From
`3γ² + 1 = 0`, moduli give `τ(θ)² = 1/3`, hence `τ(θ) = τ(π/2)`, and
`cubicTau_strictAntiOn` is injective on `[0,π]`.  The route through
`Re γ² = Im γ² = 0` is available and is worse: it ends at `cos θ sin θ = 0`,
which then has to be turned back into an angle.

**Differs from the paper's route.**  `lem:amplitude-divisor` reads the divisor
off `B`'s zeros through the injectivity of the branch; here the branch is
injective for a stronger reason -- `τ` is strictly monotone, so even the modulus
separates angles -- and that is what the proof uses.  Nothing is assumed about
`B` beyond what is computed.

## The windows are forced to be `M`-independent, and that is a finding

`Θ` is a parameter of `weighted_dominance_of_branch`, bound *before*
`hinterior`'s `∀ e`, while the window inequality's constant `σi` is produced
*inside* that quantifier and depends on `e`.  At this pencil `σi` is pinned from
below: `τmi ≥ τ(e)` and the separating radius obeys `Ri < 1/τ(e)²`, because the
third denominator zero sits at `1/τ(e)²` and is real while the principal pair is
not, so `σi ≥ τmi/Ri > τ(e)³`.  As `e → 0`, `τ(e) → τ(0) = 1`, so
`exp(-(-log σi)M/2) = σi^{M/2} → 1` for every fixed `M`.

So a `Θ` serving every `e` at once must delete a *fixed* interval about `π/2`,
of half-width `1`, at every `M`: the shrinking windows of `subsec:proof` cannot
be recovered from this binder, at this pencil or any other where `τ` reaches `1`
at the endpoint.  `cubicTheta` is that fixed family, `cubicWitness_hinterior`
proves it admissible, and `cubicTheta_leaves_room` checks the deleted set does
not swallow the arc -- without which the whole instantiation would be a
certificate that the conclusion is empty.

## Tags

witness, cubic pencil, principal amplitude, interior window
-/

namespace ForgacsTran

open Polynomial Complex

/-! ### The witness numerator -/

/-- The witness numerator `B(t) = 3t² + 1`, whose zeros `±i/√3` meet the
principal branch at `θ = π/2`. -/
noncomputable def witB : Polynomial ℂ := C 3 * X ^ 2 + 1

@[simp] theorem witB_eval (t : ℂ) : witB.eval t = 3 * t ^ 2 + 1 := by
  simp [witB]

theorem witB_ne_zero : witB ≠ 0 := by
  intro h
  have h0 := witB_eval 0
  rw [h] at h0
  simp at h0

theorem hasRealCoeffs_witB : HasRealCoeffs witB := by
  have hmap : witB = ((C 3 * X ^ 2 + 1 : Polynomial ℝ)).map (algebraMap ℝ ℂ) := by
    rw [witB, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_one, Polynomial.map_C]
    norm_num
  intro k
  rw [hmap, coeff_map]
  simp

/-! ### The branch, its modulus and its conjugate -/

/-- `‖γ(θ)‖ = τ(θ)`: the branch's modulus is the branch function. -/
theorem norm_ftPrincipal_cubicTau (θ : ℝ) : ‖ftPrincipal cubicTau θ‖ = cubicTau θ := by
  rw [ftPrincipal, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (cubicTau_pos θ)]

theorem ftPrincipal_cubicTau_pi_div_two :
    ftPrincipal cubicTau (Real.pi / 2) = ((1 / Real.sqrt 3 : ℝ) : ℂ) * I := by
  rw [ftPrincipal, cubicTau_pi_div_two]
  congr 1
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

/-! ### The amplitude divisor -/

/-- **`lem:amplitude-divisor` at the witness.**  `B` vanishes on the branch at
exactly one interior angle.  Through moduli: `3γ² = -1` forces `τ(θ)² = 1/3`,
so `τ(θ) = τ(π/2)`, and `cubicTau_strictAntiOn` is injective. -/
theorem witB_eval_ftPrincipal_eq_zero_iff {θ : ℝ} (hθ : θ ∈ Set.Icc 0 Real.pi) :
    witB.eval (ftPrincipal cubicTau θ) = 0 ↔ θ = Real.pi / 2 := by
  have hpi := Real.pi_pos
  have hhalf : Real.pi / 2 ∈ Set.Icc (0 : ℝ) Real.pi := ⟨by linarith, by linarith⟩
  have hs3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hval : ((1 / Real.sqrt 3 : ℝ) : ℂ) ^ 2 = -(-(1 / 3) : ℂ) := by
    rw [← Complex.ofReal_pow]
    have : (1 / Real.sqrt 3 : ℝ) ^ 2 = 1 / 3 := by
      rw [div_pow, one_pow, h3]
    rw [this]
    norm_num
  constructor
  · intro h
    rw [witB_eval] at h
    have hsq : ftPrincipal cubicTau θ ^ 2 = (-(1 / 3) : ℂ) := by linear_combination h / 3
    have hn : ‖ftPrincipal cubicTau θ‖ ^ 2 = 1 / 3 := by
      rw [← norm_pow, hsq]
      rw [norm_neg]
      norm_num
    rw [norm_ftPrincipal_cubicTau] at hn
    have heq : cubicTau θ = cubicTau (Real.pi / 2) := by
      rw [cubicTau_pi_div_two, ← sq_eq_sq₀ (cubicTau_pos θ).le (by positivity)]
      rw [hn, div_pow, one_pow, h3]
    exact cubicTau_strictAntiOn.injOn hθ hhalf heq
  · rintro rfl
    rw [ftPrincipal_cubicTau_pi_div_two, witB_eval, mul_pow, hval, Complex.I_sq]
    ring

/-! ### The branch is regular on the interior

`τ` is differentiable there because `cubicTau_closed_form` makes it
`1/(2cos((π-θ)/3))` on `[0,π]`, and `[0,π]` is a neighborhood of every interior
angle.  The derivative of the branch is then `(τ' + iτ)e^{iθ}`, which cannot
vanish: its imaginary factor is `τ > 0`. -/

/-- The closed form's own derivative, wherever its cosine does not vanish.  Kept
separate from `hasDerivAt_cubicTau` because the endpoints need it too, and there
`cubicTau` matches it only on one side. -/
theorem hasDerivAt_cubicTauCF {θ : ℝ} (hcne : Real.cos ((Real.pi - θ) / 3) ≠ 0) :
    HasDerivAt (fun t : ℝ => 1 / (2 * Real.cos ((Real.pi - t) / 3)))
      (-Real.sin ((Real.pi - θ) / 3) / (6 * Real.cos ((Real.pi - θ) / 3) ^ 2)) θ := by
  have h0 : HasDerivAt (fun t : ℝ => Real.pi - t) (-1 : ℝ) θ := by
    simpa using (hasDerivAt_id θ).const_sub Real.pi
  have hu : HasDerivAt (fun t : ℝ => (Real.pi - t) / 3) (-1 / 3 : ℝ) θ := h0.div_const 3
  have hc : HasDerivAt (fun t : ℝ => Real.cos ((Real.pi - t) / 3))
      (-Real.sin ((Real.pi - θ) / 3) * (-1 / 3)) θ := hu.cos
  have hne : 2 * Real.cos ((Real.pi - θ) / 3) ≠ 0 := by simpa using hcne
  have h2 : HasDerivAt (fun t : ℝ => 2 * Real.cos ((Real.pi - t) / 3))
      (2 * (-Real.sin ((Real.pi - θ) / 3) * (-1 / 3))) θ := hc.const_mul 2
  have h3 := (hasDerivAt_const θ (1 : ℝ)).div h2 hne
  have heq : (0 * (2 * Real.cos ((Real.pi - θ) / 3))
        - 1 * (2 * (-Real.sin ((Real.pi - θ) / 3) * (-1 / 3))))
        / (2 * Real.cos ((Real.pi - θ) / 3)) ^ 2
      = -Real.sin ((Real.pi - θ) / 3) / (6 * Real.cos ((Real.pi - θ) / 3) ^ 2) := by
    field
  exact heq ▸ h3

/-- The closed form's cosine is positive on the closed arc, endpoints included. -/
theorem cos_third_pos {θ : ℝ} (hθ : θ ∈ Set.Icc 0 Real.pi) :
    0 < Real.cos ((Real.pi - θ) / 3) := by
  have hpi := Real.pi_pos
  exact Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.2], by linarith [hθ.1]⟩

/-- The branch function is differentiable on the open arc, with the derivative
its closed form gives. -/
theorem hasDerivAt_cubicTau {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    HasDerivAt cubicTau
      (-Real.sin ((Real.pi - θ) / 3) / (6 * Real.cos ((Real.pi - θ) / 3) ^ 2)) θ := by
  refine (hasDerivAt_cubicTauCF (cos_third_pos ⟨hθ.1.le, hθ.2.le⟩).ne').congr_of_eventuallyEq ?_
  filter_upwards [Icc_mem_nhds hθ.1 hθ.2] with t ht
  exact cubicTau_closed_form ht

/-- **`hγd` at the witness.**  The branch has a nonvanishing derivative at every
interior angle. -/
theorem exists_hasDerivAt_ftPrincipal_cubicTau {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    ∃ γ' : ℂ, γ' ≠ 0 ∧ HasDerivAt (ftPrincipal cubicTau) γ' θ := by
  set d : ℝ := -Real.sin ((Real.pi - θ) / 3) / (6 * Real.cos ((Real.pi - θ) / 3) ^ 2) with hddef
  refine ⟨Complex.exp (((θ : ℝ) : ℂ) * I) * ((d : ℂ) + ((cubicTau θ : ℝ) : ℂ) * I), ?_, ?_⟩
  · refine mul_ne_zero (Complex.exp_ne_zero _) ?_
    intro h
    have him := congrArg Complex.im h
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_I_im,
      Complex.ofReal_re, zero_add, Complex.zero_im] at him
    exact absurd him (cubicTau_pos θ).ne'
  · have hτ : HasDerivAt (fun t : ℝ => ((cubicTau t : ℝ) : ℂ)) ((d : ℂ)) θ :=
      (hasDerivAt_cubicTau hθ).ofReal_comp
    have hE : HasDerivAt (fun t : ℝ => Complex.exp (((t : ℝ) : ℂ) * I))
        (Complex.exp (((θ : ℝ) : ℂ) * I) * I) θ := by
      have : HasDerivAt (fun w : ℂ => Complex.exp (w * I))
          (Complex.exp (((θ : ℝ) : ℂ) * I) * I) (((θ : ℝ) : ℂ)) := by
        simpa using ((hasDerivAt_id (((θ : ℝ) : ℂ))).mul_const I).cexp
      exact this.comp_ofReal
    have hmul := hτ.mul hE
    have hfun : ftPrincipal cubicTau
        = fun t : ℝ => ((cubicTau t : ℝ) : ℂ) * Complex.exp (((t : ℝ) : ℂ) * I) := rfl
    have hval : ((d : ℝ) : ℂ) * Complex.exp (((θ : ℝ) : ℂ) * I)
          + ((cubicTau θ : ℝ) : ℂ) * (Complex.exp (((θ : ℝ) : ℂ) * I) * I)
        = Complex.exp (((θ : ℝ) : ℂ) * I) * (((d : ℝ) : ℂ) + ((cubicTau θ : ℝ) : ℂ) * I) := by
      ring
    rw [hfun, ← hval]
    exact hmul

/-! ### The amplitude along the branch -/

/-- The principal branch is a denominator zero, in the form `hinterior` writes. -/
theorem ftDen_cubicQ_eval_ftPrincipal (θ : ℝ) :
    (ftDen cubicQ 1 ((cubicZ (cubicTau θ) θ : ℝ) : ℂ)).eval (ftPrincipal cubicTau θ) = 0 :=
  ftDen_cubicQ_eval_cubicTau θ

/-- It is a simple zero. -/
theorem derivative_ftDen_cubicQ_ftPrincipal_ne_zero {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    (derivative (ftDen cubicQ 1 ((cubicZ (cubicTau θ) θ : ℝ) : ℂ))).eval
      (ftPrincipal cubicTau θ) ≠ 0 := by
  refine derivative_ftDen_cubicQ_ne_zero hθ ?_
  simp [cubicRootSet, ftPrincipal]

/-- **`lem:amplitude-divisor` at the witness, on the arc.**  The residue
amplitude vanishes at exactly one interior angle. -/
theorem ftAmp_witB_eq_zero_iff {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    ftAmp cubicQ witB 1 ((cubicZ (cubicTau θ) θ : ℝ) : ℂ) (ftPrincipal cubicTau θ) = 0
      ↔ θ = Real.pi / 2 := by
  rw [ftAmp_eq_zero_iff (ftDen_cubicQ_eval_ftPrincipal θ)
    (derivative_ftDen_cubicQ_ftPrincipal_ne_zero hθ)]
  exact witB_eval_ftPrincipal_eq_zero_iff ⟨hθ.1.le, hθ.2.le⟩

/-! ### The deleted windows -/

/-- The deleted windows at the witness: a fixed interval about the amplitude's
zero angle, the same at every `M`.  See the module header for why `M`-dependence
is not available under this binder. -/
def cubicTheta : ℕ → Set ℝ := fun _ => {θ : ℝ | |θ - Real.pi / 2| < 1}

theorem mem_cubicTheta {M : ℕ} {θ : ℝ} : θ ∈ cubicTheta M ↔ |θ - Real.pi / 2| < 1 := Iff.rfl

/-- The deleted set never swallows the arc: for every large `M` there is an
angle the conclusion of `weighted_dominance_of_branch` actually speaks about.
Without this the instantiation would certify an empty statement. -/
theorem cubicTheta_leaves_room {h : ℝ} (hh : 0 < h) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∃ θ : ℝ,
      h / M ≤ θ ∧ θ ≤ Real.pi - h / M ∧ θ ∉ cubicTheta M := by
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hw : (0 : ℝ) < Real.pi / 2 - 1 := by linarith
  obtain ⟨M₀, hM₀⟩ := exists_nat_gt (h / (Real.pi / 2 - 1))
  refine ⟨M₀, fun M hM => ?_⟩
  have hM0 : (0 : ℝ) < M := by
    have h0 : (0 : ℝ) < M₀ := lt_of_le_of_lt (by positivity) hM₀
    exact lt_of_lt_of_le h0 (by exact_mod_cast hM)
  have hbound : h / M ≤ Real.pi / 2 - 1 := by
    have hlt : h / (Real.pi / 2 - 1) < M := lt_of_lt_of_le hM₀ (by exact_mod_cast hM)
    rw [div_lt_iff₀ hw] at hlt
    rw [div_le_iff₀ hM0]
    nlinarith
  refine ⟨Real.pi / 2 - 1, hbound, by linarith, ?_⟩
  have habs : |Real.pi / 2 - 1 - Real.pi / 2| = 1 := by
    rw [show Real.pi / 2 - 1 - Real.pi / 2 = (-1 : ℝ) by ring, abs_neg, abs_one]
  rw [mem_cubicTheta, habs]
  exact lt_irrefl 1

/-! ### The binder

Both branches of the case split are real.  For `e ≤ π/2` the arc
`[e, π-e]` meets `π/2` and `S = {π/2}`; for `e > π/2` the arc is empty, and the
data is supplied so that the binder's `∀ e > 0` is met rather than met only
where it has content. -/

/-- **`hinterior` at the witness.**  The geometry group is
`cubicWitness_interior_geometry`; what is added here is the amplitude divisor,
the branch's regularity, and the window inequality against `cubicTheta`. -/
theorem cubicWitness_hinterior :
    ∀ e : ℝ, 0 < e →
      ∃ (Ri τmi σi : ℝ) (S : Finset ℝ),
        0 < Ri ∧ τmi / Ri ≤ σi ∧ 0 < σi ∧ σi < 1 ∧
        (∀ θ : ℝ, e ≤ θ → θ ≤ Real.pi - e → 0 < cubicTau θ) ∧
        (∀ θ : ℝ, e ≤ θ → θ ≤ Real.pi - e → cubicTau θ ≤ τmi) ∧
        (∀ θ : ℝ, e ≤ θ → θ ≤ Real.pi - e → cubicTau θ < Ri) ∧
        (∀ θ : ℝ, e ≤ θ → θ ≤ Real.pi - e →
          (ftDen cubicQ 1 ((cubicZ (cubicTau θ) θ : ℝ) : ℂ)).eval
            (ftPrincipal cubicTau θ) = 0) ∧
        (∀ θ : ℝ, e ≤ θ → θ ≤ Real.pi - e →
          (derivative (ftDen cubicQ 1 ((cubicZ (cubicTau θ) θ : ℝ) : ℂ))).eval
            (ftPrincipal cubicTau θ) ≠ 0) ∧
        (∀ θ : ℝ, e ≤ θ → θ ≤ Real.pi - e →
          (derivative (ftDen cubicQ 1 ((cubicZ (cubicTau θ) θ : ℝ) : ℂ))).eval
            (((cubicTau θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * I)) ≠ 0) ∧
        (∀ θ : ℝ, e ≤ θ → θ ≤ Real.pi - e →
          ftPrincipal cubicTau θ
            ≠ ((cubicTau θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * I)) ∧
        (∀ θ : ℝ, e ≤ θ → θ ≤ Real.pi - e → ∀ t : ℂ, ‖t‖ ≤ Ri →
          (ftDen cubicQ 1 ((cubicZ (cubicTau θ) θ : ℝ) : ℂ)).eval t = 0 →
          t = ftPrincipal cubicTau θ
            ∨ t = ((cubicTau θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * I)) ∧
        (↑S ⊆ Set.Icc e (Real.pi - e)) ∧
        (∀ θj ∈ S, ftAmp cubicQ witB 1 ((cubicZ (cubicTau θj) θj : ℝ) : ℂ)
          (ftPrincipal cubicTau θj) = 0) ∧
        (∀ θ ∈ Set.Icc e (Real.pi - e),
          ftAmp cubicQ witB 1 ((cubicZ (cubicTau θ) θ : ℝ) : ℂ)
            (ftPrincipal cubicTau θ) = 0 → θ ∈ S) ∧
        (∀ θ ∈ Set.Icc e (Real.pi - e),
          ∃ γ' : ℂ, γ' ≠ 0 ∧ HasDerivAt (ftPrincipal cubicTau) γ' θ) ∧
        (∀ θ ∈ Set.Icc e (Real.pi - e),
          ContinuousAt (fun θ' => ((cubicZ (cubicTau θ') θ' : ℝ) : ℂ)) θ) ∧
        (∀ (M : ℕ) (θ : ℝ), θ ∉ cubicTheta M → ∀ θj ∈ S,
          Real.exp (-((-Real.log σi) / (2 * S.card) * M
            / (witB.rootMultiplicity (ftPrincipal cubicTau θj)))) ≤ |θ - θj|) := by
  classical
  intro e he
  have hpi := Real.pi_pos
  -- the window clause needs only that the exponent is nonpositive
  have hwin : ∀ (σi : ℝ), 0 < σi → σi < 1 → ∀ (S : Finset ℝ),
      (∀ θj ∈ S, θj = Real.pi / 2) →
      ∀ (M : ℕ) (θ : ℝ), θ ∉ cubicTheta M → ∀ θj ∈ S,
        Real.exp (-((-Real.log σi) / (2 * S.card) * M
          / (witB.rootMultiplicity (ftPrincipal cubicTau θj)))) ≤ |θ - θj| := by
    intro σi hσi0 hσi1 S hSval M θ hθ θj hθj
    have hlog : 0 ≤ -Real.log σi := by
      have := Real.log_neg hσi0 hσi1
      linarith
    have hnn : 0 ≤ (-Real.log σi) / (2 * S.card) * M
        / (witB.rootMultiplicity (ftPrincipal cubicTau θj)) :=
      div_nonneg (mul_nonneg (div_nonneg hlog (by positivity)) (by positivity)) (by positivity)
    have h1 : Real.exp (-((-Real.log σi) / (2 * S.card) * M
        / (witB.rootMultiplicity (ftPrincipal cubicTau θj)))) ≤ 1 :=
      Real.exp_le_one_iff.2 (by linarith)
    have h2 : (1 : ℝ) ≤ |θ - θj| := by
      rw [hSval θj hθj]
      simpa only [mem_cubicTheta, not_lt] using hθ
    linarith
  rcases le_or_gt e (Real.pi / 2) with hle | hgt
  · -- the arc meets `π/2`, and `S = {π/2}`
    have heπ : e < Real.pi := by linarith
    have hsub : ∀ θ : ℝ, e ≤ θ → θ ≤ Real.pi - e → θ ∈ Set.Ioo 0 Real.pi :=
      fun θ h1 h2 => ⟨lt_of_lt_of_le he h1, lt_of_le_of_lt h2 (by linarith)⟩
    have hτe0 : 0 < cubicTau e := cubicTau_pos e
    have hτe1 : cubicTau e < 1 := cubicTau_lt_one ⟨he, heπ⟩
    have hmax : ∀ θ : ℝ, e ≤ θ → θ ≤ Real.pi - e → cubicTau θ ≤ cubicTau e := by
      intro θ h1 h2
      rcases eq_or_lt_of_le h1 with h | h
      · exact le_of_eq (by rw [h])
      · exact (cubicTau_strictAntiOn ⟨he.le, heπ.le⟩
          ⟨le_trans he.le h1, (hsub θ h1 h2).2.le⟩ h).le
    have hhalfmem : Real.pi / 2 ∈ Set.Icc e (Real.pi - e) := ⟨hle, by linarith⟩
    have hhalfIoo : Real.pi / 2 ∈ Set.Ioo 0 Real.pi := ⟨by linarith, by linarith⟩
    refine ⟨1, cubicTau e, cubicTau e, {Real.pi / 2}, one_pos, by rw [div_one], hτe0, hτe1,
      fun θ _ _ => cubicTau_pos θ, hmax,
      fun θ h1 h2 => cubicTau_lt_one (hsub θ h1 h2),
      fun θ _ _ => ftDen_cubicQ_eval_ftPrincipal θ,
      fun θ h1 h2 => derivative_ftDen_cubicQ_ftPrincipal_ne_zero (hsub θ h1 h2),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- the conjugate zero is simple too
      intro θ h1 h2
      rw [← conj_ftPrincipal cubicTau θ]
      refine derivative_ftDen_cubicQ_ne_zero (hsub θ h1 h2) ?_
      simp [cubicRootSet, ftPrincipal]
    · -- the principal pair is genuinely a pair
      intro θ h1 h2
      rw [← conj_ftPrincipal cubicTau θ]
      exact cubic_pair_ne (hsub θ h1 h2)
    · -- exactly two zeros inside `‖t‖ ≤ 1`
      intro θ h1 h2 t hnorm hrt
      have hθ := hsub θ h1 h2
      have hmem := (mem_cubicRootSet_iff hθ).2 hrt
      simp only [cubicRootSet, Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h | h | h
      · exact Or.inl h
      · exact Or.inr (h.trans (conj_ftPrincipal cubicTau θ))
      · exfalso
        have h3 : cubicThird θ ≤ 1 := by
          rw [h, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (lt_trans (cubicTau_pos θ) (cubicTau_lt_cubicThird hθ))] at hnorm
          exact hnorm
        have hlt : cubicTau θ < 1 := cubicTau_lt_one hθ
        have hp : 0 < cubicTau θ := cubicTau_pos θ
        rw [cubicThird, div_le_one (by positivity)] at h3
        nlinarith
    · -- `S` sits in the arc
      intro x hx
      simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hx
      rw [hx]; exact hhalfmem
    · -- the amplitude vanishes at `π/2`
      intro θj hθj
      rw [Finset.mem_singleton] at hθj
      subst hθj
      exact (ftAmp_witB_eq_zero_iff hhalfIoo).2 rfl
    · -- and nowhere else on the arc
      intro θ hθ hz
      rw [Finset.mem_singleton]
      exact (ftAmp_witB_eq_zero_iff (hsub θ hθ.1 hθ.2)).1 hz
    · exact fun θ hθ => exists_hasDerivAt_ftPrincipal_cubicTau (hsub θ hθ.1 hθ.2)
    · exact fun θ _ => (Complex.continuous_ofReal.comp continuous_cubicZ_branch).continuousAt
    · refine hwin _ hτe0 hτe1 _ ?_
      intro θj hθj
      rwa [Finset.mem_singleton] at hθj
  · -- the arc is empty: `π - e < π/2 < e`
    have hempty : ∀ θ : ℝ, e ≤ θ → θ ≤ Real.pi - e → False := fun θ h1 h2 => by linarith
    refine ⟨1, 1 / 4, 1 / 2, ∅, one_pos, by norm_num, by norm_num, by norm_num,
      fun θ h1 h2 => (hempty θ h1 h2).elim, fun θ h1 h2 => (hempty θ h1 h2).elim,
      fun θ h1 h2 => (hempty θ h1 h2).elim, fun θ h1 h2 => (hempty θ h1 h2).elim,
      fun θ h1 h2 => (hempty θ h1 h2).elim, fun θ h1 h2 => (hempty θ h1 h2).elim,
      fun θ h1 h2 => (hempty θ h1 h2).elim, fun θ h1 h2 => (hempty θ h1 h2).elim,
      by simp, by simp, ?_, ?_, ?_, ?_⟩
    · exact fun θ hθ _ => (hempty θ hθ.1 hθ.2).elim
    · exact fun θ hθ => (hempty θ hθ.1 hθ.2).elim
    · exact fun θ hθ => (hempty θ hθ.1 hθ.2).elim
    · exact hwin _ (by norm_num) (by norm_num) ∅ (by simp)

/-! ### The windows are forced to be `M`-independent

`cubicTheta` is not a lazy choice.  Every `Θ` meeting this binder at this pencil
contains the same fixed interval about `π/2`, at every `M`, so no admissible
family shrinks -- the `exp(-cM)` windows of `subsec:proof` are not expressible
under this quantifier order.

The chain is short and every step is a clause of the binder.  The third
denominator zero `1/τ(e)²` is real while the principal pair is not, so the
separating radius obeys `Ri < 1/τ(e)²`; the arc's own left endpoint gives
`τ(e) ≤ τmi`; so `σi ≥ τmi/Ri > τ(e)³`.  The amplitude divisor is the single
angle `π/2` with `B`-multiplicity `1`, so the window inequality reads
`σi^{M/2} ≤ |θ - π/2|`.  Letting `e → 0` and using `τ(0) = 1` sends the left
side to `1`.

**This is a property of the compatibility wrapper, not of the theorem.**
`subsec:proof` chooses the interior parameter and the windows together, after
`M`, and the `_at` forms do exactly that: `weighted_dominance_of_branch_at` and
`weighted_dominance_of_branch_any_multiplicity_at` conclude
`∃ ε > 0, ∀ Θ : ℕ → Set ℝ, …`, so `σ` is one fixed number by the time `Θ` is
chosen and nothing above applies to them.  What is measured here is
`weighted_dominance_of_branch`, which keeps `Θ` in its binder list deliberately,
so that the seventeen files consuming it did not have to be restated.

So this is neither a gap in `thm:weighted-dominance` nor a defect in the paper.
Without that distinction the theorem below reads as a limitation of the
dominance theorem itself, which it is not. -/

theorem eval_derivative_witB (t : ℂ) : (derivative witB).eval t = 6 * t := by
  rw [witB, derivative_add, derivative_C_mul, derivative_X_pow, derivative_one]
  simp
  ring

theorem witB_rootMultiplicity_pi_div_two :
    witB.rootMultiplicity (ftPrincipal cubicTau (Real.pi / 2)) = 1 := by
  have hpi := Real.pi_pos
  have hroot : witB.IsRoot (ftPrincipal cubicTau (Real.pi / 2)) :=
    (witB_eval_ftPrincipal_eq_zero_iff ⟨by linarith, by linarith⟩).2 rfl
  have hs3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hd : ¬ (derivative witB).IsRoot (ftPrincipal cubicTau (Real.pi / 2)) := by
    rw [Polynomial.IsRoot, eval_derivative_witB, ftPrincipal_cubicTau_pi_div_two]
    refine mul_ne_zero (by norm_num) (mul_ne_zero ?_ Complex.I_ne_zero)
    simp
  have h0 : 0 < witB.rootMultiplicity (ftPrincipal cubicTau (Real.pi / 2)) :=
    (rootMultiplicity_pos witB_ne_zero).2 hroot
  have h1 : ¬ 1 < witB.rootMultiplicity (ftPrincipal cubicTau (Real.pi / 2)) := by
    rw [one_lt_rootMultiplicity_iff_isRoot witB_ne_zero]
    exact fun h => hd h.2
  omega

/-- **Under the wrapper's binder order, the deleted windows cannot shrink.**
The `_at` forms bind `Θ` after `ε` and are not subject to this; see the note
above `eval_derivative_witB`.  The hypothesis is seven of
`hinterior`'s clauses -- the three on `σi`, the bound `τ ≤ τmi`, the
exactly-two-zeros clause, the two that pin the amplitude divisor, and the window
inequality itself.  `cubicTheta_forced_of_hinterior` checks that this list really
is a sublist by deriving it from `cubicWitness_hinterior`. -/
theorem cubicWitness_window_forced {Θ : ℕ → Set ℝ}
    (hint : ∀ e : ℝ, 0 < e →
      ∃ (Ri τmi σi : ℝ) (S : Finset ℝ),
        0 < Ri ∧ τmi / Ri ≤ σi ∧ 0 < σi ∧ σi < 1 ∧
        (∀ θ : ℝ, e ≤ θ → θ ≤ Real.pi - e → cubicTau θ ≤ τmi) ∧
        (∀ θ : ℝ, e ≤ θ → θ ≤ Real.pi - e → ∀ t : ℂ, ‖t‖ ≤ Ri →
          (ftDen cubicQ 1 ((cubicZ (cubicTau θ) θ : ℝ) : ℂ)).eval t = 0 →
          t = ftPrincipal cubicTau θ
            ∨ t = ((cubicTau θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * I)) ∧
        (↑S ⊆ Set.Icc e (Real.pi - e)) ∧
        (∀ θj ∈ S, ftAmp cubicQ witB 1 ((cubicZ (cubicTau θj) θj : ℝ) : ℂ)
          (ftPrincipal cubicTau θj) = 0) ∧
        (∀ θ ∈ Set.Icc e (Real.pi - e),
          ftAmp cubicQ witB 1 ((cubicZ (cubicTau θ) θ : ℝ) : ℂ)
            (ftPrincipal cubicTau θ) = 0 → θ ∈ S) ∧
        (∀ (M : ℕ) (θ : ℝ), θ ∉ Θ M → ∀ θj ∈ S,
          Real.exp (-((-Real.log σi) / (2 * S.card) * M
            / (witB.rootMultiplicity (ftPrincipal cubicTau θj)))) ≤ |θ - θj|)) :
    ∀ (M : ℕ) (θ : ℝ), |θ - Real.pi / 2| < 1 → θ ∈ Θ M := by
  intro M θ hθ
  by_contra hnot
  have hpi := Real.pi_pos
  -- one bound per interior parameter, and it degenerates as `e → 0`
  have key : ∀ e : ℝ, 0 < e → e < Real.pi / 2 →
      Real.exp (3 * M / 2 * Real.log (cubicTau e)) ≤ |θ - Real.pi / 2| := by
    intro e he hlt
    obtain ⟨Ri, τmi, σi, S, hRi, hσi, hσi0, hσi1, hτle, hpairOnly, hSsub, hSzero, hSconv,
      hwin⟩ := hint e he
    have heπ : e < Real.pi := by linarith
    have hsub : ∀ x : ℝ, e ≤ x → x ≤ Real.pi - e → x ∈ Set.Ioo 0 Real.pi :=
      fun x h1 h2 => ⟨lt_of_lt_of_le he h1, lt_of_le_of_lt h2 (by linarith)⟩
    have heIoo : e ∈ Set.Ioo 0 Real.pi := ⟨he, heπ⟩
    have hτe0 : 0 < cubicTau e := cubicTau_pos e
    have hhalfmem : Real.pi / 2 ∈ Set.Icc e (Real.pi - e) := ⟨hlt.le, by linarith⟩
    have hhalfIoo : Real.pi / 2 ∈ Set.Ioo 0 Real.pi := ⟨by linarith, by linarith⟩
    -- the divisor is the single angle `π/2`
    have hSeq : S = {Real.pi / 2} := by
      refine Finset.eq_singleton_iff_unique_mem.2
        ⟨hSconv _ hhalfmem ((ftAmp_witB_eq_zero_iff hhalfIoo).2 rfl), fun x hx => ?_⟩
      have hxmem : x ∈ Set.Icc e (Real.pi - e) := hSsub hx
      exact (ftAmp_witB_eq_zero_iff (hsub x hxmem.1 hxmem.2)).1 (hSzero x hx)
    -- the separating radius is under the third zero, which is real
    have hthird : 0 < cubicThird e := lt_trans hτe0 (cubicTau_lt_cubicThird heIoo)
    have hRilt : Ri < cubicThird e := by
      by_contra hcon
      push Not at hcon
      have hnorm : ‖((cubicThird e : ℝ) : ℂ)‖ ≤ Ri := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hthird]
        exact hcon
      have hse : 0 < Real.sin e := Real.sin_pos_of_pos_of_lt_pi he heπ
      rcases hpairOnly e le_rfl (by linarith) _ hnorm (ftDen_cubicQ_eval_cubicThird e) with h | h
      · have him := congrArg Complex.im h
        rw [ftPrincipal] at him
        simp only [Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
          Complex.exp_ofReal_mul_I_im, Complex.exp_ofReal_mul_I_re, zero_mul, add_zero] at him
        nlinarith
      · have him := congrArg Complex.im h
        rw [show -((e : ℝ) : ℂ) * I = (((-e : ℝ) : ℝ) : ℂ) * I by push_cast; ring] at him
        simp only [Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
          Complex.exp_ofReal_mul_I_im, Complex.exp_ofReal_mul_I_re, zero_mul, add_zero,
          Real.sin_neg] at him
        nlinarith
    -- so `σi` is pinned above `τ(e)³`
    have hσlb : cubicTau e ^ 3 < σi := by
      have h1 : cubicTau e ≤ τmi := hτle e le_rfl (by linarith)
      have h2 : cubicTau e / cubicThird e < cubicTau e / Ri :=
        div_lt_div_of_pos_left hτe0 hRi hRilt
      have h3 : cubicTau e / Ri ≤ τmi / Ri := by
        gcongr
      have h4 : cubicTau e / cubicThird e = cubicTau e ^ 3 := by
        rw [cubicThird]
        field_simp
      linarith [h4 ▸ h2]
    have hlogb : 3 * Real.log (cubicTau e) < Real.log σi := by
      have := Real.log_lt_log (by positivity) hσlb
      rwa [Real.log_pow] at this
    -- the window inequality, with `card S = 1` and multiplicity `1`
    have hw := hwin M θ hnot (Real.pi / 2) (by rw [hSeq]; exact Finset.mem_singleton_self _)
    rw [hSeq, witB_rootMultiplicity_pi_div_two, Finset.card_singleton] at hw
    have hshape : -((-Real.log σi) / (2 * ((1 : ℕ) : ℝ)) * M / ((1 : ℕ) : ℝ))
        = Real.log σi * M / 2 := by
      push_cast
      ring
    rw [hshape] at hw
    refine le_trans (Real.exp_le_exp.2 ?_) hw
    have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    nlinarith
  -- and the bound degenerates
  have hlim : Filter.Tendsto (fun e : ℝ => Real.exp (3 * M / 2 * Real.log (cubicTau e)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    have h1 : Filter.Tendsto cubicTau (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 1) := by
      have hc := continuous_cubicTau.continuousAt (x := (0 : ℝ))
      rw [ContinuousAt, cubicTau_zero] at hc
      exact hc.mono_left nhdsWithin_le_nhds
    have h2 := (Real.continuousAt_log (one_ne_zero)).tendsto.comp h1
    rw [Real.log_one] at h2
    have h3 : Filter.Tendsto (fun e : ℝ => 3 * (M : ℝ) / 2 * Real.log (cubicTau e))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      simpa using h2.const_mul (3 * (M : ℝ) / 2)
    have h4 := (Real.continuous_exp.tendsto 0).comp h3
    simpa [Function.comp_def] using h4
  have hev : ∀ᶠ e in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      Real.exp (3 * M / 2 * Real.log (cubicTau e)) ≤ |θ - Real.pi / 2| := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by linarith : (0 : ℝ) < Real.pi / 2)).filter_mono
        nhdsWithin_le_nhds] with e he1 he2
    exact key e he1 he2
  have hone := le_of_tendsto hlim hev
  linarith

/-- The clause list of `cubicWitness_window_forced` is genuinely a sublist of
`hinterior`'s: this derives it from the proven instance. -/
theorem cubicTheta_forced_of_hinterior :
    ∀ (M : ℕ) (θ : ℝ), |θ - Real.pi / 2| < 1 → θ ∈ cubicTheta M := by
  refine cubicWitness_window_forced (fun e he => ?_)
  obtain ⟨Ri, τmi, σi, S, hRi, hσi, hσi0, hσi1, _, hτle, _, _, _, _, _, hpairOnly,
    hSsub, hSzero, hSconv, _, _, hwin⟩ := cubicWitness_hinterior e he
  exact ⟨Ri, τmi, σi, S, hRi, hσi, hσi0, hσi1, hτle, hpairOnly, hSsub, hSzero, hSconv, hwin⟩


/-! ### The clause list is the binder's

`cubicWitness_hinterior` is written out rather than derived, so nothing but the
type checker can say it matches `hinterior`.  This feeds its twenty-two
components, in order, to `hdata_entry_of_interior` -- the consumer
`weighted_dominance_of_branch` hands them to -- so a clause that drifted in
transcription fails to compile rather than certifying the wrong statement. -/

example (e : ℝ) (he : 0 < e) : True := by
  obtain ⟨Ri, τmi, σi, S, hRi, hσi, hσi0, hσi1, hτpos, hτle, hτR, hrp, hsp, hsm, hnee, hpair,
    hSsub, hSzero, hzeros, hγd, hzc, hwin⟩ := cubicWitness_hinterior e he
  have _hd := hdata_entry_of_interior hasRealCoeffs_cubicQ hasRealCoeffs_witB (le_refl 1)
    cubicQ_eval_zero_ne witB_ne_zero hRi hσi hσi0 hσi1 hτpos hτle hτR hrp hsp hsm hnee hpair
    hSsub hSzero hzeros hγd hzc hwin
  trivial

end ForgacsTran
