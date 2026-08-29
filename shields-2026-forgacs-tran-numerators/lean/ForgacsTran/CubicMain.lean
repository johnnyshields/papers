/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.CubicPhaseDerivative
import ForgacsTran.QuadraticDefect
import ForgacsTran.Main

/-!
# The cubic pencil against the headline theorem

`Main.main_bound` runs on a `Bridge.FTInputs`.  This module asks what the cubic
witness can put into one, and answers precisely: everything except the rate at
which the deleted window shrinks.

## What is unconditional

`natDegree_ftCoeffPoly_cubic` computes `deg F_M = M`, so the pencil's own
coefficient sequence is what `coeffPoly` would be and its degree grows -- the
comparison `Bridge.ftInputsWitness`, with `coeffPoly = 1`, cannot make.
`cubic_interior_zero_count` then produces, past one threshold and with no
analytic hypothesis, at least `M/4` distinct real zeros of `F_M` inside
`I_{Q,1} = (0, 27/4)`.

## Why that is not `bulk_zero_count`, and what closes it

`Bridge.FTInputs.bulk_zero_count` asks for `deg P_m - C ≤ #interior` with `C` a
**constant**, and `M - C ≤ 0.363 M` fails for large `M`.  The shortfall is a
*factor*, and all of it is the deleted window: `cubicTheta` deletes
`|θ - π/2| < 1` at every `M`, so the two retained components carry only
`(π-2)/π` of the arc however large `M` is.

That fixed width was never the mathematics.  `weighted_dominance_of_branch` asks
for its window inequality inside `hinterior`'s `∀ e` while using it at one `e`,
and as `e → 0` the interior contraction ratio tends to `1`, so the half-width
`eq:amplitude-deletion` forces tends to a fixed positive number.
`DominanceFTSupply.dominance_shrinking_of_fixed_window` repairs it, by fixing the
interior parameter first -- which is what `subsec:proof` does, choosing `ε` with
every amplitude zero inside `(ε, π/r - ε)` before `M` is quantified.

`cubic_shrinkingWindow` is that repair at this pencil, and it discharges
`CubicShrinkingWindow`.  So `thm:main`'s three clauses hold here with **no
analytic hypothesis**, at a pencil with a genuine amplitude divisor -- which is
what separates it from `QuadraticWitness`, where `B = 1` and no window arises.

`scripts/check_cubic_main_route.py` measures the pieces: `deg F_M = M`, that all
`M` zeros are in fact real and in `I_{Q,1}` (so `M/4` is far from tight), and
that the shrinking-window dominance holds at `h = 1` for `M` up to `80` --
measured before it was proved.

## Main statements

* `natDegree_ftCoeffPoly_cubic` — `deg F_M = M`, the non-degeneracy of the data.
* `cubicZ_mem_Ioo`, `ofReal_cubicZ_image_subset` — `eq:ab-def` at this pencil,
  `I_{Q,1} = (0, 27/4)`.
* `cubic_interior_zero_count` — unconditional: at least `M/4` real zeros of `F_M`
  in `I_{Q,1}`.
* `CubicShrinkingWindow` — `eq:dominance-bound` off windows of half-width `h/M`;
  `cubic_shrinkingWindow` proves it.
* `cubic_bulk_count`, `cubic_ftInputs`, `cubic_main_bound`,
  `cubic_main_bound_interval` — `thm:main`'s three clauses at this pencil,
  unconditionally.

## Tags

cubic pencil, main theorem, interior zero count, retained range
-/

namespace ForgacsTran

open Polynomial Set

/-! ### The coefficient sequence has degree exactly `M` -/

theorem cubicQ_coeff_zero : cubicQ.coeff 0 = 1 := by
  rw [Polynomial.coeff_zero_eq_eval_zero, cubicQ_eval]
  norm_num

theorem cubicQ_coeff_zero_ne : cubicQ.coeff 0 ≠ 0 := by
  rw [cubicQ_coeff_zero]; norm_num

/-- The degree bound of `lem:eventual-degree` at this pencil, `deg F_M ≤ M` at
`r = 1`, read off the recurrence rather than assumed. -/
theorem natDegree_ftCoeffPoly_cubic_le (M : ℕ) :
    (ftCoeffPoly cubicQ witB 1 M).natDegree ≤ M := by
  have h := eventual_natDegree_le cubicQ (le_refl 1) cubicQ_coeff_zero_ne
    (fun M => witB.coeff M) (ftCoeffPoly cubicQ witB 1)
    (fun M => denomConv_ftCoeffPoly cubicQ witB (le_refl 1) cubicQ_coeff_zero_ne M) M
  simpa using h

/-- The leading coefficient: `[z^M] F_M = (-1)^M`.  Only the resonant index
`i = r = 1` of the recurrence contributes at the top, and it contributes the
factor `X` once per step. -/
theorem coeff_ftCoeffPoly_cubic (M : ℕ) :
    (ftCoeffPoly cubicQ witB 1 M).coeff M = (-1) ^ M := by
  induction M using Nat.strong_induction_on with
  | _ M ih =>
    rcases M with _ | M'
    · rw [ftCoeffPoly_eq]
      simp [cubicQ_coeff_zero, witB]
    · set M := M' + 1 with hM
      rw [ftCoeffPoly_eq, cubicQ_coeff_zero, inv_one, map_one, one_mul, Polynomial.coeff_sub,
        Polynomial.finsetSum_coeff]
      have hC : (Polynomial.C (witB.coeff M)).coeff M = 0 := by
        rw [Polynomial.coeff_C]
        simp [hM]
      have hsum : ∑ i ∈ Finset.range M,
          (ftDenCoeff cubicQ 1 (M - i) * ftCoeffPoly cubicQ witB 1 i).coeff M
          = (-1 : ℂ) ^ M' := by
        rw [Finset.sum_eq_single M']
        · rw [show M - M' = 1 by omega, ftDenCoeff]
          simp only [if_true, Polynomial.coeff_add, Polynomial.coeff_C_mul, add_mul,
            Polynomial.coeff_add]
          have h1 : (ftCoeffPoly cubicQ witB 1 M').coeff M = 0 :=
            Polynomial.coeff_eq_zero_of_natDegree_lt
              (lt_of_le_of_lt (natDegree_ftCoeffPoly_cubic_le M') (by omega))
          have h2 : (X * ftCoeffPoly cubicQ witB 1 M').coeff M = (-1 : ℂ) ^ M' := by
            rw [hM, Polynomial.coeff_X_mul, ih M' (by omega)]
          rw [h1, h2]
          ring
        · intro i hi hne
          have hiM : i < M := Finset.mem_range.1 hi
          have hgap : 2 ≤ M - i := by omega
          have hne1 : M - i ≠ 1 := by omega
          rw [ftDenCoeff]
          simp only [if_neg hne1, add_zero, Polynomial.coeff_C_mul]
          rw [Polynomial.coeff_eq_zero_of_natDegree_lt
            (lt_of_le_of_lt (natDegree_ftCoeffPoly_cubic_le i) hiM), mul_zero]
        · intro h
          exact absurd (Finset.mem_range.2 (by omega)) h
      rw [hC, hsum, hM]
      ring

/-- **The coefficient sequence is honest and its degree grows.**  `deg F_M = M`
at this pencil, so a count of interior zeros linear in `M` is a count against a
degree that is linear in `M` -- which is what `Bridge.ftInputsWitness`, whose
`coeffPoly` is the constant `1`, does not have. -/
theorem natDegree_ftCoeffPoly_cubic (M : ℕ) :
    (ftCoeffPoly cubicQ witB 1 M).natDegree = M :=
  Polynomial.natDegree_eq_of_le_of_coeff_ne_zero (natDegree_ftCoeffPoly_cubic_le M)
    (by rw [coeff_ftCoeffPoly_cubic]; exact pow_ne_zero _ (by norm_num))


/-! ### The spectral interval at this pencil

`eq:ab-def` gives `I_{Q,1} = (0, 27/4)`: the branch runs from `τ(0) = 1` to
`τ(π) = 1/2`, and `z = 3 - τ² - 2cos θ/τ` runs from `0` to `27/4` with it.  The
left endpoint is `0`, which `ftInterval_subset_posRay` admits -- `ρ = 3`, so the
smallest zero of `Q` is repeated, exactly the case that docstring names. -/

theorem cubicZ_at_zero : cubicZ (cubicTau 0) 0 = 0 := by
  rw [cubicZ, cubicTau_zero]
  norm_num

theorem cubicZ_at_pi : cubicZ (cubicTau Real.pi) Real.pi = 27 / 4 := by
  rw [cubicZ, cubicTau_pi, Real.cos_pi]
  norm_num

/-- The branch's spectral parameter lands strictly inside `I_{Q,1}`. -/
theorem cubicZ_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    cubicZ (cubicTau θ) θ ∈ Set.Ioo 0 (27 / 4) := by
  have hπ := Real.pi_pos
  have h0 : (0 : ℝ) ∈ Set.Icc 0 Real.pi := ⟨le_rfl, hπ.le⟩
  have hπm : Real.pi ∈ Set.Icc (0 : ℝ) Real.pi := ⟨hπ.le, le_rfl⟩
  have hθm : θ ∈ Set.Icc (0 : ℝ) Real.pi := ⟨hθ.1.le, hθ.2.le⟩
  constructor
  · have h := cubicZ_strictMonoOn h0 hθm hθ.1
    simp only at h
    rwa [cubicZ_at_zero] at h
  · have h := cubicZ_strictMonoOn hθm hπm hθ.2
    simp only at h
    rwa [cubicZ_at_pi] at h

/-- The image of a subarc of the open arc sits inside `I_{Q,1}`. -/
theorem ofReal_cubicZ_image_subset {u v : ℝ} (huv : u ≤ v)
    (hsub : Set.Icc u v ⊆ Set.Ioo 0 Real.pi) :
    Complex.ofReal '' (Set.Icc (cubicZ (cubicTau u) u) (cubicZ (cubicTau v) v))
      ⊆ ftInterval 0 (27 / 4) := by
  rintro w ⟨x, hx, rfl⟩
  have hu := cubicZ_mem_Ioo (hsub ⟨le_rfl, huv⟩)
  have hv := cubicZ_mem_Ioo (hsub ⟨huv, le_rfl⟩)
  exact ⟨x, ⟨lt_of_lt_of_le hu.1 hx.1, lt_of_le_of_lt hx.2 hv.2⟩, rfl⟩


/-- **Zeros in two ordered spectral intervals cannot coincide.**  The counts over the
two components of the retained range add rather than overlap, and this is the whole
reason: `z` carries the two components to intervals that do not meet, so a zero
produced by one cannot be produced by the other.

Stated over bare endpoints, because that is all it uses — no branch, no pencil, and no
monotonicity beyond the single inequality `d₁ < c₂` the caller supplies from
`cubicZ_strictMonoOn`. -/
theorem disjoint_of_ofReal_image_lt {Z₁ Z₂ : Finset ℂ} {c₁ d₁ c₂ d₂ : ℝ}
    (h₁ : ∀ w ∈ Z₁, w ∈ Complex.ofReal '' Set.Icc c₁ d₁)
    (h₂ : ∀ w ∈ Z₂, w ∈ Complex.ofReal '' Set.Icc c₂ d₂)
    (hlt : d₁ < c₂) : Disjoint Z₁ Z₂ := by
  refine Finset.disjoint_left.2 fun w hw1 hw2 => ?_
  obtain ⟨x, hx, rfl⟩ := h₁ w hw1
  obtain ⟨y, hy, hxy⟩ := h₂ _ hw2
  have hyx : y = x := by exact_mod_cast hxy
  subst hyx
  linarith [hx.2, hy.1]


/-! ### The count over the retained range

`cubicTheta` deletes `|θ - π/2| < 1` at every `M`, so the retained range has
exactly two components and their total length is `π - 2 - 2h/M` rather than
`π - 2h/M`.  Summing `cubic_exists_phaseZeros` over the two gives a count of

`((M - 1/2)(π - 2 - 2h/M))/π - 4`,

which is linear in `M` with slope `(π-2)/π ≈ 0.363`.  `M/4` is a round number
below it, stated so the count is directly comparable with
`natDegree_ftCoeffPoly_cubic`: **at least `M/4` of the `M` zeros are real and lie
in `I_{Q,1}`.**

**The slope is not `1`, and that is the finding.**  `Bridge.FTInputs`'s
`bulk_zero_count` asks for `deg P_m - C ≤ #interior` with `C` a *constant*, and
`M - C ≤ 0.363M` fails for large `M`.  The gap is not this module's arithmetic:
it is the fixed deleted window, which the `Θ`-before-`∀e` quantifier order of
`weighted_dominance_of_branch` forces at this pencil (recorded in
`CubicWitnessInterior`'s header).  A window shrinking like `1/(M+1)` -- what
`eq:retained-range` and `eq:amplitude-window-negligible` actually give -- would
send the two components' total length to `π` and the slope to `1`, and the
constant defect would follow.  See the closing note. -/

/-- **The unconditional interior-zero count at the cubic pencil.**  Past one
threshold, every weight's coefficient polynomial has at least `M/4` distinct
real zeros inside `I_{Q,1} = (0, 27/4)`, with no analytic hypothesis assumed.
Against `natDegree_ftCoeffPoly_cubic`'s `deg = M` this is a fixed positive
fraction of the degree, so the count grows with the degree. -/
theorem cubic_interior_zero_count :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      ∀ P : Polynomial ℝ, P.map (algebraMap ℝ ℂ) = ftCoeffPoly cubicQ witB 1 M →
        ∃ Z : Finset ℂ, (M : ℝ) / 4 ≤ (Z.card : ℝ) ∧
          (∀ w ∈ Z, (P.map (algebraMap ℝ ℂ)).IsRoot w) ∧
          (∀ w ∈ Z, w ∈ ftInterval 0 (27 / 4)) := by
  classical
  obtain ⟨h, hh, M₁, hcount⟩ := cubic_exists_phaseZeros
  obtain ⟨N, hN⟩ := exists_nat_gt (10 * h)
  refine ⟨max (max M₁ N) 100, fun M hM P hP => ?_⟩
  have hM₁ : M₁ ≤ M := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hM
  have hMN : N ≤ M := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hM
  have hM100 : 100 ≤ M := le_trans (le_max_right _ _) hM
  have hMR : (100 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM100
  have hMpos : (0 : ℝ) < (M : ℝ) := by linarith
  have hπ1 : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hπ2 : Real.pi < 3.15 := Real.pi_lt_d2
  have hh0 : 0 < h / (M : ℝ) := div_pos hh hMpos
  have hhM : h / (M : ℝ) ≤ 1 / 10 := by
    rw [div_le_div_iff₀ hMpos (by norm_num)]
    have hNR : (N : ℝ) ≤ (M : ℝ) := by exact_mod_cast hMN
    nlinarith [hN]
  -- the two components of the retained range
  have harc1 : Set.Icc (h / (M : ℝ)) (Real.pi / 2 - 1) ⊆ Set.Ioo 0 Real.pi :=
    fun θ hθ => ⟨lt_of_lt_of_le hh0 hθ.1, by linarith [hθ.2]⟩
  have harc2 : Set.Icc (Real.pi / 2 + 1) (Real.pi - h / (M : ℝ)) ⊆ Set.Ioo 0 Real.pi :=
    fun θ hθ => ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  have hwin1 : ∀ θ ∈ Set.Icc (h / (M : ℝ)) (Real.pi / 2 - 1), θ ∉ cubicTheta M := by
    intro θ hθ hc
    rw [mem_cubicTheta, abs_lt] at hc
    linarith [hθ.2, hc.1]
  have hwin2 : ∀ θ ∈ Set.Icc (Real.pi / 2 + 1) (Real.pi - h / (M : ℝ)), θ ∉ cubicTheta M := by
    intro θ hθ hc
    rw [mem_cubicTheta, abs_lt] at hc
    linarith [hθ.1, hc.2]
  obtain ⟨ψ1, Z1, -, -, hr1, hm1, hn1⟩ :=
    hcount M hM₁ (h / (M : ℝ)) (Real.pi / 2 - 1) (by linarith) harc1 le_rfl (by linarith)
      hwin1 P hP
  obtain ⟨ψ2, Z2, -, -, hr2, hm2, hn2⟩ :=
    hcount M hM₁ (Real.pi / 2 + 1) (Real.pi - h / (M : ℝ)) (by linarith) harc2 (by linarith)
      le_rfl hwin2 P hP
  -- the two spectral windows are disjoint, so the counts add
  have hmid : cubicZ (cubicTau (Real.pi / 2 - 1)) (Real.pi / 2 - 1)
      < cubicZ (cubicTau (Real.pi / 2 + 1)) (Real.pi / 2 + 1) := by
    have h := cubicZ_strictMonoOn (a := Real.pi / 2 - 1) (b := Real.pi / 2 + 1)
      ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith)
    simpa using h
  have hdisj : Disjoint Z1 Z2 := disjoint_of_ofReal_image_lt hm1 hm2 hmid
  refine ⟨Z1 ∪ Z2, ?_, ?_, ?_⟩
  · -- the arithmetic: two components of length `π/2 - 1 - h/M` each
    rw [Finset.card_union_of_disjoint hdisj]
    push_cast
    set L : ℝ := Real.pi / 2 - 1 - h / (M : ℝ) with hL
    have hLge : (47 : ℝ) / 100 ≤ L := by rw [hL]; linarith
    have hA0 : (0 : ℝ) ≤ ((M : ℝ) - 1 / 2) * L := by nlinarith
    have hAge : ((M : ℝ) - 1 / 2) * (47 / 100) ≤ ((M : ℝ) - 1 / 2) * L := by nlinarith
    have hdiv : ((M : ℝ) - 1 / 2) * L * (20 / 63) ≤ ((M : ℝ) - 1 / 2) * L / Real.pi := by
      rw [le_div_iff₀ Real.pi_pos]
      nlinarith
    have he1 : ((M : ℝ) - 1 / 2) * (Real.pi / 2 - 1 - h / (M : ℝ)) / Real.pi - 2
        ≤ (Z1.card : ℝ) := hn1
    have he2 : ((M : ℝ) - 1 / 2) * (Real.pi - h / (M : ℝ) - (Real.pi / 2 + 1)) / Real.pi - 2
        ≤ (Z2.card : ℝ) := hn2
    have hrw : Real.pi - h / (M : ℝ) - (Real.pi / 2 + 1) = L := by rw [hL]; ring
    rw [hrw] at he2
    rw [← hL] at he1
    nlinarith
  · intro w hw
    rcases Finset.mem_union.1 hw with hw | hw
    · exact hr1 w hw
    · exact hr2 w hw
  · intro w hw
    rcases Finset.mem_union.1 hw with hw | hw
    · exact ofReal_cubicZ_image_subset (by linarith) harc1 (hm1 w hw)
    · exact ofReal_cubicZ_image_subset (by linarith) harc2 (hm2 w hw)


/-! ### What a shrinking window would buy

The count above is short of `bulk_zero_count` by a *factor*, not a constant, and
the whole of that shortfall is the fixed deleted window.  This section makes that
precise by taking the shrinking window as a hypothesis and deriving everything
downstream from it: with the deleted windows of half-width `h/M` -- the rate
`eq:retained-range` and `eq:amplitude-window-negligible` give -- the two
components' lengths sum to `π - 4h/M`, the defect becomes the constant
`4.5 + 4h/3`, and `thm:main` follows at this pencil with no further hypothesis.

So the residual gap at the cubic pencil is exactly `hdom` below.  It is not a
statement about the phase, the amplitude divisor, the branch, the degree, or the
count -- all of those are proved -- but about the *rate at which the deleted
window may shrink*, which is where `weighted_dominance_of_branch`'s quantifier
order loses information the paper's `thm:weighted-dominance` has. -/

/-- **`eq:dominance-bound` off shrinking windows.**  `eq:dominance-bound`
on the retained range of `eq:retained-range`, with *all* deleted windows -- the
two endpoint windows and the amplitude window of
`eq:amplitude-window-negligible` -- of half-width `h/M`.

`cubic_weighted_dominance` proves this statement with the amplitude window at a
fixed half-width `1` instead, which is what
`weighted_dominance_of_branch`'s `Θ`-before-`∀e` quantifier order forces at this
pencil.  The rate is the whole difference: a fixed window costs a constant
*fraction* of the count, a shrinking one costs a constant.
`cubic_shrinkingWindow` proves it. -/
def CubicShrinkingWindow : Prop :=
  ∃ h > (0 : ℝ), ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ θ : ℝ,
    h / M ≤ θ → θ ≤ Real.pi - h / M → h / M ≤ |θ - Real.pi / 2| →
    ftRemainder cubicQ witB 1 (fun θ' => cubicZ (cubicTau θ') θ') cubicTau M θ
      ≤ ftPrincipalAmp cubicQ witB 1 (fun θ' => cubicZ (cubicTau θ') θ') cubicTau θ / 2

/-- **The bulk count, given dominance off a shrinking window.**  The defect is a
constant, which is what `Bridge.FTInputs.bulk_zero_count` asks for and what the
fixed window of `cubicTheta` cannot deliver. -/
theorem cubic_bulk_count_of_shrinkingWindow (hdom : CubicShrinkingWindow) :
    ∃ C M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      ∃ Z : Finset ℂ, ((M : ℝ) - C ≤ (Z.card : ℝ)) ∧
        (∀ w ∈ Z, (ftCoeffPoly cubicQ witB 1 M).IsRoot w) ∧
        (∀ w ∈ Z, w ∈ ftInterval 0 (27 / 4)) := by
  classical
  obtain ⟨h, hh, M₁, hdomAll⟩ := hdom
  obtain ⟨N, hN⟩ := exists_nat_gt (10 * h)
  obtain ⟨C, hC⟩ := exists_nat_gt (9 / 2 + 4 * h / 3)
  refine ⟨C, max (max M₁ N) 100, fun M hM => ?_⟩
  have hM₁ : M₁ ≤ M := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hM
  have hMN : N ≤ M := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hM
  have hM100 : 100 ≤ M := le_trans (le_max_right _ _) hM
  have hM1 : 1 ≤ M := le_trans (by norm_num) hM100
  have hMR : (100 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM100
  have hMpos : (0 : ℝ) < (M : ℝ) := by linarith
  have hπ1 : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hπ2 : Real.pi < 3.15 := Real.pi_lt_d2
  have hh0 : 0 < h / (M : ℝ) := div_pos hh hMpos
  have hhM : h / (M : ℝ) ≤ 1 / 10 := by
    rw [div_le_div_iff₀ hMpos (by norm_num)]
    have hNR : (N : ℝ) ≤ (M : ℝ) := by exact_mod_cast hMN
    nlinarith [hN]
  have hhMM : (M : ℝ) * (h / (M : ℝ)) = h := by field_simp
  obtain ⟨P, hP⟩ :=
    exists_real_ftCoeffPoly_of_real hasRealCoeffs_cubicQ hasRealCoeffs_witB 1 M
  -- the two components, now separated only by the shrinking window
  have hsub1 : Set.Icc (h / (M : ℝ)) (Real.pi / 2 - h / (M : ℝ)) ⊆ cubicRetained :=
    fun θ hθ => ⟨⟨lt_of_lt_of_le hh0 hθ.1, by linarith [hθ.2]⟩, by
      intro hc; rw [hc] at hθ; linarith [hθ.2]⟩
  have hsub2 : Set.Icc (Real.pi / 2 + h / (M : ℝ)) (Real.pi - h / (M : ℝ)) ⊆ cubicRetained :=
    fun θ hθ => ⟨⟨by linarith [hθ.1], by linarith [hθ.2]⟩, by
      intro hc; rw [hc] at hθ; linarith [hθ.1]⟩
  have hd1 : ∀ θ ∈ Set.Icc (h / (M : ℝ)) (Real.pi / 2 - h / (M : ℝ)),
      ftRemainder cubicQ witB 1 (fun θ' => cubicZ (cubicTau θ') θ') cubicTau M θ
        ≤ ftPrincipalAmp cubicQ witB 1 (fun θ' => cubicZ (cubicTau θ') θ') cubicTau θ / 2 := by
    intro θ hθ
    refine hdomAll M hM₁ θ hθ.1 (by linarith [hθ.2]) ?_
    rw [abs_of_nonpos (by linarith [hθ.2])]
    linarith [hθ.2]
  have hd2 : ∀ θ ∈ Set.Icc (Real.pi / 2 + h / (M : ℝ)) (Real.pi - h / (M : ℝ)),
      ftRemainder cubicQ witB 1 (fun θ' => cubicZ (cubicTau θ') θ') cubicTau M θ
        ≤ ftPrincipalAmp cubicQ witB 1 (fun θ' => cubicZ (cubicTau θ') θ') cubicTau θ / 2 := by
    intro θ hθ
    refine hdomAll M hM₁ θ (by linarith [hθ.1]) hθ.2 ?_
    rw [abs_of_nonneg (by linarith [hθ.1])]
    linarith [hθ.1]
  obtain ⟨ψ1, Z1, -, -, hr1, hm1, hn1⟩ :=
    cubic_phaseZeros_of_dominance (by linarith) hsub1 hM1 hd1 P hP
  obtain ⟨ψ2, Z2, -, -, hr2, hm2, hn2⟩ :=
    cubic_phaseZeros_of_dominance (by linarith) hsub2 hM1 hd2 P hP
  have hmid : cubicZ (cubicTau (Real.pi / 2 - h / (M : ℝ))) (Real.pi / 2 - h / (M : ℝ))
      < cubicZ (cubicTau (Real.pi / 2 + h / (M : ℝ))) (Real.pi / 2 + h / (M : ℝ)) := by
    have hx := cubicZ_strictMonoOn (a := Real.pi / 2 - h / (M : ℝ))
      (b := Real.pi / 2 + h / (M : ℝ)) ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
      (by linarith)
    simpa using hx
  have hdisj : Disjoint Z1 Z2 := disjoint_of_ofReal_image_lt hm1 hm2 hmid
  refine ⟨Z1 ∪ Z2, ?_, ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint hdisj]
    push_cast
    set e : ℝ := h / (M : ℝ) with he
    have hexp : ((M : ℝ) - 1 / 2) * (Real.pi / 2 - 2 * e)
        = ((M : ℝ) - 1 / 2) * Real.pi / 2 - 2 * h + e := by
      rw [he]; field
    have hdiv : (((M : ℝ) - 1 / 2) - 4 * h / 3) / 2
        ≤ ((M : ℝ) - 1 / 2) * (Real.pi / 2 - 2 * e) / Real.pi := by
      rw [le_div_iff₀ Real.pi_pos, hexp]
      nlinarith [mul_lt_mul_of_pos_left hπ1 hh, hh0, hh]
    have hrw1 : Real.pi / 2 - e - e = Real.pi / 2 - 2 * e := by ring
    have hrw2 : Real.pi - e - (Real.pi / 2 + e) = Real.pi / 2 - 2 * e := by ring
    rw [hrw1] at hn1
    rw [hrw2] at hn2
    linarith [hC, hn1, hn2, hdiv]
  · intro w hw
    rw [← hP]
    rcases Finset.mem_union.1 hw with hw | hw
    · exact hr1 w hw
    · exact hr2 w hw
  · intro w hw
    rcases Finset.mem_union.1 hw with hw | hw
    · exact ofReal_cubicZ_image_subset (by linarith)
        (fun θ hθ => (hsub1 hθ).1) (hm1 w hw)
    · exact ofReal_cubicZ_image_subset (by linarith)
        (fun θ hθ => (hsub2 hθ).1) (hm2 w hw)


/-! ### `thm:main` at the cubic pencil, modulo the window

With `CubicShrinkingWindow` in hand every field of `Bridge.FTInputs` is the
pencil's own data and nothing further is assumed. -/

theorem ftCoeffPoly_cubic_ne_zero (M : ℕ) : ftCoeffPoly cubicQ witB 1 M ≠ 0 := by
  intro hc
  have h := coeff_ftCoeffPoly_cubic M
  rw [hc, Polynomial.coeff_zero] at h
  exact pow_ne_zero M (by norm_num : (-1 : ℂ) ≠ 0) h.symm

/-- **`Bridge.FTInputs` at the cubic pencil, given the window.**  `coeffPoly` is
the pencil's own coefficient sequence -- not a convenient function -- and its
degree is `M` by `natDegree_ftCoeffPoly_cubic`, so the bundle is non-degenerate
in the sense `Bridge.ftInputsWitness` is not. -/
theorem cubic_ftInputs_of_shrinkingWindow (hdom : CubicShrinkingWindow) :
    ∃ H : FTInputs, H.coeffPoly = ftCoeffPoly cubicQ witB 1
      ∧ H.ftSet = ftInterval 0 (27 / 4) := by
  classical
  obtain ⟨C, M₀, hcount⟩ := cubic_bulk_count_of_shrinkingWindow hdom
  have hall : ∀ M : ℕ, ∃ Z : Finset ℂ,
      (M₀ ≤ M → ((M : ℝ) - C ≤ (Z.card : ℝ))) ∧
      (∀ w ∈ Z, (ftCoeffPoly cubicQ witB 1 M).IsRoot w) ∧
      (∀ w ∈ Z, w ∈ ftInterval 0 (27 / 4)) := by
    intro M
    by_cases hM : M₀ ≤ M
    · obtain ⟨Z, h1, h2, h3⟩ := hcount M hM
      exact ⟨Z, fun _ => h1, h2, h3⟩
    · exact ⟨∅, fun hc => absurd hc hM, by simp, by simp⟩
  choose Z hZ1 hZ2 hZ3 using hall
  refine ⟨{ coeffPoly := ftCoeffPoly cubicQ witB 1
            ftSet := ftInterval 0 (27 / 4)
            ftSet_subset := ftInterval_subset_posRay le_rfl
            interiorZeros := Z
            Cbulk := C
            interiorZeros_root := hZ2
            interiorZeros_mem := hZ3
            bulk_zero_count := ⟨M₀, fun M hM => ?_⟩ }, rfl, rfl⟩
  rw [natDegree_ftCoeffPoly_cubic]
  rcases le_or_gt M C with hle | hgt
  · simp [Nat.sub_eq_zero_of_le hle]
  · have hR : ((M - C : ℕ) : ℝ) ≤ ((Z M).card : ℝ) := by
      rw [Nat.cast_sub hgt.le]
      linarith [hZ1 M hM]
    exact_mod_cast hR

/-- **`thm:main` clause 3 at the cubic pencil, given the window.**  One constant
bounds the zeros of every `F_M` off the positive ray. -/
theorem cubic_main_bound_of_shrinkingWindow (hdom : CubicShrinkingWindow) :
    ∃ C : ℕ, ∀ M : ℕ,
      (exceptionalRoots (ftCoeffPoly cubicQ witB 1 M) posRay).card ≤ C := by
  obtain ⟨H, hcoeff, -⟩ := cubic_ftInputs_of_shrinkingWindow hdom
  obtain ⟨C, hC⟩ := main_bound H
  refine ⟨C, fun M => ?_⟩
  have h := hC M (by rw [hcoeff]; exact ftCoeffPoly_cubic_ne_zero M)
  rwa [hcoeff] at h

/-- **`thm:main` clause 2 at the cubic pencil, given the window.**  Past one
threshold, at most `Cbulk` zeros of `F_M` lie outside `I_{Q,1}`. -/
theorem cubic_main_bound_interval_of_shrinkingWindow (hdom : CubicShrinkingWindow) :
    ∃ (C : ℕ) (M₀ : ℕ), ∀ M : ℕ, M₀ ≤ M →
      (exceptionalRoots (ftCoeffPoly cubicQ witB 1 M) (ftInterval 0 (27 / 4))).card ≤ C := by
  obtain ⟨H, hcoeff, hset⟩ := cubic_ftInputs_of_shrinkingWindow hdom
  obtain ⟨M₀, hM₀⟩ := main_bound_interval H
  refine ⟨H.Cbulk, M₀, fun M hM => ?_⟩
  have h := hM₀ M hM (by rw [hcoeff]; exact ftCoeffPoly_cubic_ne_zero M)
  rwa [hcoeff, hset] at h


/-! ### The window discharged

`cubic_weighted_dominance` already gives `eq:dominance-bound` where
`|θ - π/2| ≥ 1`.  What is missing is the band `h/M ≤ |θ - π/2| < 1`, and on that
band the estimate is elementary, because the band sits in a **fixed** compact
subinterval of the open arc:

* `interior_data_of_geometry` at the fixed `e = π/2 - 1` gives one `σ < 1` and
  `|R_M(θ)| ≤ C σ^M` on `[π/2 - 1, π/2 + 1]`, and the amplitude floor
  `A|θ - π/2|^ν` of `lem:amplitude-divisor` there;
* on the band `|θ - π/2| ≥ h/M`, that floor is at least `A(h/M)^ν`, which is
  polynomial in `1/M` while the remainder is exponential in `M`.

So the whole content of the missing band is that an exponential beats a
polynomial.  The fixed window of `cubicTheta` was never the mathematics: it was
`weighted_dominance_of_branch` asking for the window inequality at *every*
interior parameter `e` while using it at only one, and as `e → 0` the `σ` of
`[e, π-e]` tends to `1` and the window it forces tends to a fixed width.  Fixing
`e` first -- which is what `subsec:proof` does, choosing `ε` with all the
amplitude zeros inside `(ε, π/r - ε)` before `M` is quantified -- removes it.

**Differs from the paper's route.**  `thm:weighted-dominance` proves the whole
retained range in one pass with the windows of `eq:amplitude-deletion`, whose
half-width `e^{-cM/ν_j}` is exponentially small.  Here the arc is covered twice:
`cubic_weighted_dominance` off a fixed window, and this band inside it.  The
half-width obtained is `h/M`, not `e^{-cM/ν}` -- weaker than the paper's, and
all that `eq:retained-range` needs. -/

/-- **`CubicShrinkingWindow` holds.**  The one analytic input `CubicMain` was
owed is discharged, so everything it gated is unconditional. -/
theorem cubic_shrinkingWindow : CubicShrinkingWindow := by
  classical
  have hπ3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  set e : ℝ := Real.pi / 2 - 1 with he
  have hepos : 0 < e := by rw [he]; linarith
  obtain ⟨Ri, τmi, σi, S, hRi, hσiR, hσi0, hσi1, hτpos, hτle, hτR, hrp, hsp, hsm,
    hnee, hpair, hSsub, hSzero, hzeros, hγd, hzc, -⟩ := cubicWitness_hinterior e hepos
  obtain ⟨CI, σI, AI, hσI0, hσI1, hAI, hrem, hfloor, -, -⟩ :=
    interior_data_of_geometry (z := fun θ' => cubicZ (cubicTau θ') θ') (τ := cubicTau)
      hasRealCoeffs_cubicQ hasRealCoeffs_witB (le_refl 1) cubicQ_eval_zero_ne
      witB_ne_zero hRi hσiR hσi0 hσi1 hτpos hτle hτR hrp hsp hsm hnee hpair hSsub
      hSzero hzeros hγd hzc
  -- the amplitude's zero set on this window is the single angle `π/2`
  have hmemIoo : ∀ θ ∈ Set.Icc e (Real.pi - e), θ ∈ Set.Ioo 0 Real.pi :=
    fun θ hθ => ⟨lt_of_lt_of_le hepos hθ.1, lt_of_le_of_lt hθ.2 (by linarith)⟩
  have hhalfmem : Real.pi / 2 ∈ Set.Icc e (Real.pi - e) := by
    constructor <;> rw [he] <;> linarith
  have hSeq : S = {Real.pi / 2} := by
    refine Finset.eq_singleton_iff_unique_mem.2 ⟨?_, fun x hx => ?_⟩
    · exact hzeros _ hhalfmem ((ftAmp_witB_eq_zero_iff (hmemIoo _ hhalfmem)).2 rfl)
    · exact (ftAmp_witB_eq_zero_iff (hmemIoo x (hSsub hx))).1 (hSzero x hx)
  have hCI0 : 0 ≤ CI := by
    have h := hrem 0 (Real.pi / 2) hhalfmem.1 hhalfmem.2
    simpa using le_trans (abs_nonneg _) h
  have hmain := dominance_shrinking_of_fixed_window
    (Rrem := ftRemainder cubicQ witB 1 (fun θ' => cubicZ (cubicTau θ') θ') cubicTau)
    (Wamp := ftPrincipalAmp cubicQ witB 1 (fun θ' => cubicZ (cubicTau θ') θ') cubicTau)
    (Θ := cubicTheta) (S := S)
    (ν := fun θj => witB.rootMultiplicity (ftPrincipal cubicTau θj))
    (b := Real.pi) (e := e) hσI0 hσI1 hAI hCI0 (fun _ _ => norm_nonneg _)
    cubic_weighted_dominance
    (fun M θ hθ => by
      rw [mem_cubicTheta]
      exact not_lt.2 (hθ _ (by rw [hSeq]; exact Finset.mem_singleton_self _)))
    (fun θ θj hθj hlt => by
      rw [hSeq, Finset.mem_singleton] at hθj
      subst hθj
      have hb := abs_lt.1 hlt
      exact ⟨by rw [he]; linarith [hb.1], by rw [he]; linarith [hb.2]⟩)
    (fun M θ h1 h2 => by
      have h := hrem M θ h1 h2
      rwa [abs_of_nonneg (show (0:ℝ) ≤ ftRemainder cubicQ witB 1
        (fun θ' => cubicZ (cubicTau θ') θ') cubicTau M θ from norm_nonneg _)] at h)
    hfloor
  obtain ⟨h, hh, M₀, hbound⟩ := hmain
  refine ⟨h, hh, M₀, fun M hM θ h1 h2 h3 => hbound M hM θ h1 h2 ?_⟩
  intro θj hθj
  rw [hSeq, Finset.mem_singleton] at hθj
  subst hθj
  exact h3

/-! ### `thm:main` at the cubic pencil, unconditionally

Nothing below carries a hypothesis.  The pencil has a genuine amplitude divisor
-- `B(t) = 3t^2 + 1` vanishes on the branch at `θ = π/2` -- which is what
separates it from `QuadraticWitness`, where `B = 1` and no window arises at all. -/

/-- **`prop:angular-discrepancy` at the cubic pencil, defect constant.**  At
least `deg F_M - C` distinct real zeros of `F_M` in `I_{Q,1}`, past one
threshold. -/
theorem cubic_bulk_count :
    ∃ C M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      ∃ Z : Finset ℂ, ((M : ℝ) - C ≤ (Z.card : ℝ)) ∧
        (∀ w ∈ Z, (ftCoeffPoly cubicQ witB 1 M).IsRoot w) ∧
        (∀ w ∈ Z, w ∈ ftInterval 0 (27 / 4)) :=
  cubic_bulk_count_of_shrinkingWindow cubic_shrinkingWindow

/-- **`Bridge.FTInputs` at the cubic pencil, with no analytic hypothesis.**  The
bundle `thm:main` runs on, built from the pencil's own data: `coeffPoly` is
`ftCoeffPoly cubicQ witB 1`, whose degree is `M`. -/
theorem cubic_ftInputs :
    ∃ H : FTInputs, H.coeffPoly = ftCoeffPoly cubicQ witB 1
      ∧ H.ftSet = ftInterval 0 (27 / 4) :=
  cubic_ftInputs_of_shrinkingWindow cubic_shrinkingWindow

/-- **`thm:main` clause 3 at the cubic pencil, unconditionally.**  One constant
bounds the zeros of every `F_M` off the positive ray. -/
theorem cubic_main_bound :
    ∃ C : ℕ, ∀ M : ℕ,
      (exceptionalRoots (ftCoeffPoly cubicQ witB 1 M) posRay).card ≤ C :=
  cubic_main_bound_of_shrinkingWindow cubic_shrinkingWindow

/-- **`thm:main` clause 2 at the cubic pencil, unconditionally.**  Past one
threshold, at most `C` zeros of `F_M` lie outside `I_{Q,1}`. -/
theorem cubic_main_bound_interval :
    ∃ (C : ℕ) (M₀ : ℕ), ∀ M : ℕ, M₀ ≤ M →
      (exceptionalRoots (ftCoeffPoly cubicQ witB 1 M) (ftInterval 0 (27 / 4))).card ≤ C :=
  cubic_main_bound_interval_of_shrinkingWindow cubic_shrinkingWindow

end ForgacsTran
