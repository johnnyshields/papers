/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.MeasureTheory.Integral.TorusIntegral
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# The integral Andréief identity on a polycircle

The `k`-fold contour integral over the polycircle `|t_a| = ρ`, and the identity that turns a
`k × k` determinant of Laurent coefficients into one such integral.

Writing `B m` for the `m`th Laurent coefficient of a continuous function `G` on the circle
`|t| = ρ`, the staircase determinant `det [B (n - i + j)]_{i,j}` equals
\[
  \frac{(-1)^{k(k-1)/2}}{k!\,(2\pi i)^k}
  \int\cdots\int \Delta(t)^2 \prod_{a=1}^k G(t_a)\,t_a^{-n-k}\,dt_a,
  \qquad \Delta(t) = \prod_{a<b}(t_b - t_a),
\]
each variable running over `|t_a| = ρ`.  This is Andréief's identity in its integral form, the
continuous counterpart of the Cauchy--Binet expansion.

## Main definitions

* `Shields.polyCircle`: the product of `k` circles of radius `ρ` in `Fin k → ℂ`.
* `Shields.circleIntegralPow`: the `k`-fold contour integral, normalized as `k` copies of
  `circleIntegral`.
* `Shields.CircleIntegrablePow`: integrability of the angular integrand.
* `Shields.vandermondeProd`: the Vandermonde product `∆(t) = ∏_{a<b}(t_b - t_a)`.

## Main results

* `Shields.det_staircase_eq_circleIntegralPow`: **the integral Andréief identity**.
* `Shields.circleIntegralPow_eq_torusIntegral`: the `k`-fold integral is `torusIntegral` at
  center `0` and constant radius.
* `Shields.circleIntegralPow_prod`: a product integrand factors into `k` one-variable integrals.
* `Shields.circleIntegralPow_comp_perm`: the integral is invariant under permuting the variables.
* `Shields.sum_sign_prod_pow`, `Shields.sum_sign_prod_zpow_neg`: the two alternants, in ascending
  and in descending powers, as Vandermonde products.

## Implementation notes

`circleIntegralPow` is defined against the **product** measure `Measure.pi`, not against the box
`torusIntegral` integrates over.  That is what makes `circleIntegralPow_prod` hypothesis-free and
`circleIntegralPow_comp_perm` a consequence of the symmetry of `Measure.pi`; upstream's
`torusIntegral` carries neither lemma.  `circleIntegralPow_eq_torusIntegral` is the bridge, so
results proved upstream transfer.

## References

* C. Andréief, *Note sur une relation entre les intégrales définies des produits des fonctions*,
  Mém. Soc. Sci. Phys. Nat. Bordeaux (3) **2** (1886), 1--14.
* P. J. Forrester, *Meet Andréief, Bordeaux 1886, and Andreev, Kharkov 1882--83*,
  Random Matrices Theory Appl. **8** (2019), 1930001.

## Tags

Andreief, Andreev, contour integral, torus integral, Vandermonde, determinant, Cauchy-Binet
-/

open scoped Real BigOperators
open MeasureTheory Complex Set

namespace Shields

/-! ### The polycircle and its measure -/

/-- The polycircle `{t : |t_a| = |ρ| for every a}`, the set traced by the `k`
contours. -/
def polyCircle (k : ℕ) (ρ : ℝ) : Set (Fin k → ℂ) :=
  Set.univ.pi fun _ => Metric.sphere (0 : ℂ) |ρ|

theorem mem_polyCircle {k : ℕ} {ρ : ℝ} {t : Fin k → ℂ} :
    t ∈ polyCircle k ρ ↔ ∀ a, ‖t a‖ = |ρ| := by
  simp [polyCircle]

theorem circleMap_mem_polyCircle (k : ℕ) (ρ : ℝ) (θ : Fin k → ℝ) :
    (fun a => circleMap 0 ρ (θ a)) ∈ polyCircle k ρ := fun a _ =>
  circleMap_mem_sphere' 0 ρ (θ a)

theorem ne_zero_of_mem_polyCircle {k : ℕ} {ρ : ℝ} (hρ : ρ ≠ 0) {t : Fin k → ℂ}
    (ht : t ∈ polyCircle k ρ) (a : Fin k) : t a ≠ 0 := by
  intro h
  have := mem_polyCircle.mp ht a
  rw [h, norm_zero] at this
  exact hρ (abs_eq_zero.mp this.symm)

/-- The angular measure of the `k` contour parameters: `k` copies of Lebesgue
measure on one period, as a product measure, so that permuting the variables
preserves it. -/
noncomputable def angleMeasure (k : ℕ) : Measure (Fin k → ℝ) :=
  Measure.pi fun _ : Fin k => (volume : Measure ℝ).restrict (Set.Ioc 0 (2 * π))

/-! ### The `k`-fold contour integral -/

/-- The `k`-fold contour integral `∫⋯∫ F(t) dt_1⋯dt_k` over the polycircle
`|t_a| = ρ`.  Each variable is parametrized by `circleMap 0 ρ` exactly as
`circleIntegral` parametrizes a single contour, and the Jacobian is the product
of the `k` one-variable Jacobians. -/
noncomputable def circleIntegralPow (k : ℕ) (ρ : ℝ) (F : (Fin k → ℂ) → ℂ) : ℂ :=
  ∫ θ : Fin k → ℝ,
      (∏ a, circleMap 0 ρ (θ a) * I) * F fun a => circleMap 0 ρ (θ a) ∂angleMeasure k

/-- Integrability of `F` for the `k`-fold contour integral over `|t_a| = ρ`. -/
def CircleIntegrablePow (k : ℕ) (ρ : ℝ) (F : (Fin k → ℂ) → ℂ) : Prop :=
  Integrable (fun θ : Fin k → ℝ =>
    (∏ a, circleMap 0 ρ (θ a) * I) * F fun a => circleMap 0 ρ (θ a)) (angleMeasure k)

/-! ### Relation to Mathlib's torus integral

`circleIntegralPow k ρ` is Mathlib's `torusIntegral` at center `0` and constant
radius `ρ`, as `circleIntegralPow_eq_torusIntegral` records.  The definition is
kept in this presentation because `angleMeasure` is a **product** measure
(`Measure.pi`), which is what makes `circleIntegralPow_prod` hypothesis-free and
`circleIntegralPow_comp_perm` a consequence of `Measure.pi` symmetry;
`torusIntegral` integrates over a box and upstream carries neither a Fubini nor a
permutation lemma to inherit.  Results that *are* upstream transfer through the
bridge below. -/

/-- The angular measure is Lebesgue measure restricted to the torus box.  `Ioc`
and `Icc` differ by a null set, which is the only gap between the two forms. -/
theorem angleMeasure_eq_box (k : ℕ) : angleMeasure k
    = (volume : Measure (Fin k → ℝ)).restrict (Set.Icc (0 : Fin k → ℝ) fun _ => 2 * π) := by
  have h1 : angleMeasure k
      = (volume : Measure (Fin k → ℝ)).restrict (Set.univ.pi fun _ => Set.Ioc 0 (2 * π)) := by
    rw [MeasureTheory.volume_pi, Measure.restrict_pi_pi]; rfl
  rw [h1, ← Set.pi_univ_Icc]
  exact Measure.restrict_congr_set (Measure.ae_eq_set_pi fun _ _ => MeasureTheory.Ioc_ae_eq_Icc)

/-- **The `k`-fold contour integral is Mathlib's torus integral** at center `0`
and constant radius `ρ`. -/
theorem circleIntegralPow_eq_torusIntegral (k : ℕ) (ρ : ℝ) (F : (Fin k → ℂ) → ℂ) :
    circleIntegralPow k ρ F = torusIntegral F 0 (fun _ => ρ) := by
  have hmap : ∀ θ : Fin k → ℝ,
      torusMap (0 : Fin k → ℂ) (fun _ => ρ) θ = fun a => circleMap 0 ρ (θ a) := by
    intro θ; funext a; simp [torusMap, circleMap]
  rw [circleIntegralPow, angleMeasure_eq_box, torusIntegral]
  refine setIntegral_congr_fun measurableSet_Icc fun θ _ => ?_
  rw [hmap θ, smul_eq_mul]
  simp [circleMap]

/-- Two integrands agreeing on the polycircle have the same `k`-fold contour
integral. -/
theorem circleIntegralPow_congr {k : ℕ} {ρ : ℝ} {F₁ F₂ : (Fin k → ℂ) → ℂ}
    (h : ∀ t ∈ polyCircle k ρ, F₁ t = F₂ t) :
    circleIntegralPow k ρ F₁ = circleIntegralPow k ρ F₂ := by
  unfold circleIntegralPow
  congr 1
  funext θ
  rw [h _ (circleMap_mem_polyCircle k ρ θ)]

theorem circleIntegralPow_const_mul {k : ℕ} {ρ : ℝ} (c : ℂ) (F : (Fin k → ℂ) → ℂ) :
    circleIntegralPow k ρ (fun t => c * F t) = c * circleIntegralPow k ρ F := by
  unfold circleIntegralPow
  rw [← MeasureTheory.integral_const_mul]
  congr 1
  funext θ
  ring

theorem circleIntegralPow_finset_sum {k : ℕ} {ρ : ℝ} {ι : Type*} (s : Finset ι)
    (F : ι → (Fin k → ℂ) → ℂ) (h : ∀ i ∈ s, CircleIntegrablePow k ρ (F i)) :
    circleIntegralPow k ρ (fun t => ∑ i ∈ s, F i t) = ∑ i ∈ s, circleIntegralPow k ρ (F i) := by
  unfold circleIntegralPow
  rw [← MeasureTheory.integral_finsetSum s h]
  congr 1
  funext θ
  rw [Finset.mul_sum]

/-! ### Subtraction and the contour bound -/

/-- The `k`-fold contour integral is additive on differences of integrable integrands. -/
theorem circleIntegralPow_sub {k : ℕ} {ρ : ℝ} {F G : (Fin k → ℂ) → ℂ}
    (hF : CircleIntegrablePow k ρ F) (hG : CircleIntegrablePow k ρ G) :
    circleIntegralPow k ρ (fun t => F t - G t)
      = circleIntegralPow k ρ F - circleIntegralPow k ρ G := by
  unfold circleIntegralPow
  unfold CircleIntegrablePow at hF hG
  rw [← MeasureTheory.integral_sub hF hG]
  congr 1
  funext θ
  ring

/-- **The contour bound for the `k`-fold integral.**  Circumference to the `k`-th power times a
supremum on the polycircle: `‖∫⋯∫ F‖ ≤ (2π|ρ|)^k \sup_{polyCircle} ‖F‖`.  This is the `k`-fold
analogue of `circleIntegral.norm_integral_le_of_norm_le_const`, obtained from
`circleIntegralPow_eq_torusIntegral` and upstream's `norm_torusIntegral_le_of_norm_le_const`. -/
theorem norm_circleIntegralPow_le {k : ℕ} {ρ M : ℝ} {F : (Fin k → ℂ) → ℂ}
    (hF : ∀ t ∈ polyCircle k ρ, ‖F t‖ ≤ M) :
    ‖circleIntegralPow k ρ F‖ ≤ ((2 * π) ^ k * |ρ| ^ k) * M := by
  rw [circleIntegralPow_eq_torusIntegral]
  have hmap : ∀ θ : Fin k → ℝ,
      torusMap (0 : Fin k → ℂ) (fun _ => ρ) θ = fun a => circleMap 0 ρ (θ a) := by
    intro θ
    funext a
    simp [torusMap, circleMap]
  have hbd : ∀ θ : Fin k → ℝ, ‖F (torusMap (0 : Fin k → ℂ) (fun _ => ρ) θ)‖ ≤ M := by
    intro θ
    rw [hmap θ]
    exact hF _ (circleMap_mem_polyCircle k ρ θ)
  have := norm_torusIntegral_le_of_norm_le_const (f := F) (c := (0 : Fin k → ℂ))
    (R := fun _ : Fin k => ρ) hbd
  simpa [Finset.prod_const] using this

/-! ### Fubini: a product integrand factors -/

/-- **Fubini for the polycircle.**  A product of one-variable functions
integrates to the product of the one-variable contour integrals.  This is the
step by which `k` separate coefficient integrals become one `k`-fold integral. -/
theorem circleIntegralPow_prod {k : ℕ} (ρ : ℝ) (f : Fin k → ℂ → ℂ) :
    circleIntegralPow k ρ (fun t => ∏ a, f a (t a)) = ∏ a, ∮ z in C(0, ρ), f a z := by
  have hfub := MeasureTheory.integral_fintype_prod_eq_prod (ι := Fin k) (𝕜 := ℂ)
    (E := fun _ : Fin k => ℝ)
    (μ := fun _ : Fin k => (volume : Measure ℝ).restrict (Set.Ioc 0 (2 * π)))
    (fun (a : Fin k) (x : ℝ) => circleMap 0 ρ x * I * f a (circleMap 0 ρ x))
  unfold circleIntegralPow angleMeasure
  calc (∫ θ : Fin k → ℝ, (∏ a, circleMap 0 ρ (θ a) * I) * ∏ a, f a (circleMap 0 ρ (θ a))
          ∂Measure.pi fun _ : Fin k => (volume : Measure ℝ).restrict (Set.Ioc 0 (2 * π)))
      = ∫ θ : Fin k → ℝ, ∏ a, circleMap 0 ρ (θ a) * I * f a (circleMap 0 ρ (θ a))
          ∂Measure.pi fun _ : Fin k => (volume : Measure ℝ).restrict (Set.Ioc 0 (2 * π)) := by
        congr 1
        funext θ
        rw [← Finset.prod_mul_distrib]
    _ = ∏ a, ∫ x : ℝ, circleMap 0 ρ x * I * f a (circleMap 0 ρ x)
          ∂(volume : Measure ℝ).restrict (Set.Ioc 0 (2 * π)) := hfub
    _ = ∏ a, ∮ z in C(0, ρ), f a z := by
        refine Finset.prod_congr rfl fun a _ => ?_
        rw [circleIntegral, intervalIntegral.integral_of_le Real.two_pi_pos.le]
        simp [deriv_circleMap, smul_eq_mul]

/-! ### Permutation invariance -/

private theorem measurePreserving_comp_perm (k : ℕ) (σ : Equiv.Perm (Fin k)) :
    MeasurePreserving
      (MeasurableEquiv.piCongrLeft (fun _ : Fin k => ℝ) σ.symm)
      (angleMeasure k) (angleMeasure k) :=
  measurePreserving_piCongrLeft
    (fun _ : Fin k => (volume : Measure ℝ).restrict (Set.Ioc 0 (2 * π))) σ.symm

private theorem coe_piCongrLeft_perm (k : ℕ) (σ : Equiv.Perm (Fin k)) (θ : Fin k → ℝ) :
    (MeasurableEquiv.piCongrLeft (fun _ : Fin k => ℝ) σ.symm) θ = θ ∘ σ := by
  funext a
  rw [MeasurableEquiv.coe_piCongrLeft]
  have := Equiv.piCongrLeft_apply_apply (fun _ : Fin k => ℝ) σ.symm θ (σ a)
  simpa using this

private theorem integrand_comp_perm {k : ℕ} (ρ : ℝ) (F : (Fin k → ℂ) → ℂ)
    (σ : Equiv.Perm (Fin k)) (θ : Fin k → ℝ) :
    (∏ a, circleMap 0 ρ (θ a) * I) * (fun t => F (t ∘ σ)) (fun a => circleMap 0 ρ (θ a))
      = (∏ a, circleMap 0 ρ ((θ ∘ σ) a) * I) * F fun a => circleMap 0 ρ ((θ ∘ σ) a) := by
  have h1 : (∏ a, circleMap 0 ρ ((θ ∘ σ) a) * I) = ∏ a, circleMap 0 ρ (θ a) * I :=
    Equiv.prod_comp σ fun a => circleMap 0 ρ (θ a) * I
  rw [h1]
  rfl

/-- Permuting the `k` variables leaves the `k`-fold contour integral unchanged:
the polycircle measure is a product of equal factors. -/
theorem circleIntegralPow_comp_perm {k : ℕ} (ρ : ℝ) (F : (Fin k → ℂ) → ℂ)
    (σ : Equiv.Perm (Fin k)) :
    circleIntegralPow k ρ (fun t => F (t ∘ σ)) = circleIntegralPow k ρ F := by
  unfold circleIntegralPow
  rw [← (measurePreserving_comp_perm k σ).integral_comp'
        (fun θ : Fin k → ℝ =>
          (∏ a, circleMap 0 ρ (θ a) * I) * F fun a => circleMap 0 ρ (θ a))]
  congr 1
  funext θ
  rw [coe_piCongrLeft_perm k σ θ]
  exact integrand_comp_perm ρ F σ θ

theorem CircleIntegrablePow.comp_perm {k : ℕ} {ρ : ℝ} {F : (Fin k → ℂ) → ℂ}
    (h : CircleIntegrablePow k ρ F) (σ : Equiv.Perm (Fin k)) :
    CircleIntegrablePow k ρ (fun t => F (t ∘ σ)) := by
  unfold CircleIntegrablePow at h ⊢
  have hmp := measurePreserving_comp_perm k σ
  have hcomp := (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 h
  refine hcomp.congr ?_
  filter_upwards with θ
  rw [Function.comp_apply, coe_piCongrLeft_perm k σ θ]
  exact (integrand_comp_perm ρ F σ θ).symm

/-! ### Integrability from continuity on the polycircle -/

private theorem integrable_of_continuous {k : ℕ} {g : (Fin k → ℝ) → ℂ} (hg : Continuous g) :
    Integrable g (angleMeasure k) := by
  have hmeas : angleMeasure k
      = (volume : Measure (Fin k → ℝ)).restrict (Set.univ.pi fun _ => Set.Ioc 0 (2 * π)) := by
    rw [MeasureTheory.volume_pi, Measure.restrict_pi_pi]
    rfl
  have hK : IsCompact (Set.univ.pi fun _ : Fin k => Set.Icc (0 : ℝ) (2 * π)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hsub : (Set.univ.pi fun _ : Fin k => Set.Ioc (0 : ℝ) (2 * π))
      ⊆ Set.univ.pi fun _ : Fin k => Set.Icc (0 : ℝ) (2 * π) :=
    Set.pi_mono fun _ _ => Set.Ioc_subset_Icc_self
  rw [hmeas]
  exact (hg.continuousOn.integrableOn_compact hK).mono_set hsub

/-- A function continuous on the polycircle is integrable for the `k`-fold
contour integral. -/
theorem CircleIntegrablePow.of_continuousOn {k : ℕ} {ρ : ℝ} {F : (Fin k → ℂ) → ℂ}
    (hF : ContinuousOn F (polyCircle k ρ)) : CircleIntegrablePow k ρ F := by
  refine integrable_of_continuous ?_
  refine Continuous.mul (continuous_finsetProd _ fun a _ => ?_) ?_
  · exact ((continuous_circleMap 0 ρ).comp (continuous_apply a)).mul continuous_const
  · refine hF.comp_continuous ?_ ?_
    · exact continuous_pi fun a => (continuous_circleMap 0 ρ).comp (continuous_apply a)
    · exact fun θ => circleMap_mem_polyCircle k ρ θ

/-! ### The two Vandermonde sums -/

/-- The Vandermonde product `Δ(t) = ∏_{a<b} (t_b - t_a)`. -/
noncomputable def vandermondeProd {k : ℕ} (t : Fin k → ℂ) : ℂ :=
  ∏ a, ∏ b ∈ Finset.Ioi a, (t b - t a)

theorem vandermondeProd_eq_det {k : ℕ} (t : Fin k → ℂ) :
    vandermondeProd t = (Matrix.vandermonde t).det := (Matrix.det_vandermonde t).symm

theorem vandermondeProd_comp_perm {k : ℕ} (t : Fin k → ℂ) (σ : Equiv.Perm (Fin k)) :
    vandermondeProd (t ∘ σ) = (Equiv.Perm.sign σ : ℤ) * vandermondeProd t :=
  σ.prod_Ioi_comp_eq_sign_mul_prod (f := fun i j => t j - t i) fun _ _ => by ring

/-- Ascending powers: the Leibniz sum of `∏_j t_j^{σ(j)}` is `Δ(t)`. -/
theorem sum_sign_prod_pow {k : ℕ} (t : Fin k → ℂ) :
    (∑ σ : Equiv.Perm (Fin k), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ j, t j ^ ((σ j : ℕ)))
      = vandermondeProd t := by
  rw [vandermondeProd_eq_det, ← Matrix.det_transpose (Matrix.vandermonde t),
    Matrix.det_apply']
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp

/-- **Gauss' count of the Vandermonde factors.**  The product
`Δ(t) = ∏_a ∏_{b > a}(t_b - t_a)` has `∑_a |Ioi a| = k(k-1)/2` factors, which is
both the exponent in a bound on `Δ` and the power of `-1` picked up by reversing
the points. -/
theorem sum_card_Ioi (k : ℕ) : (∑ i : Fin k, (Finset.Ioi i).card) = k * (k - 1) / 2 := by
  have h1 : ∀ i : Fin k, (Finset.Ioi i).card = k - 1 - i.val := fun i => Fin.card_Ioi i
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => h1 i]
  rw [Fin.sum_univ_eq_sum_range fun m => k - 1 - m]
  rw [Finset.sum_range_reflect (fun m => m) k]
  exact Finset.sum_range_id k

/-- The sign of the reversal permutation of `Fin k`. -/
theorem sign_finRevPerm (k : ℕ) :
    ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin k)) : ℤ)) = (-1) ^ (k * (k - 1) / 2) := by
  set v : Fin k → ℤ := fun i => (i.val : ℤ) with hv
  have hinj : Function.Injective v := by
    intro i j h
    exact Fin.val_injective (Nat.cast_injective h)
  have hne : (Matrix.vandermonde v).det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr hinj
  have hcard := sum_card_Ioi k
  -- Reversing the points negates every Vandermonde factor.
  have hstep : ∀ i j : Fin k, v (Fin.rev j) - v (Fin.rev i) = -(v j - v i) := by
    intro i j
    have hi : (Fin.rev i).val = k - 1 - i.val := by
      rw [Fin.val_rev]; omega
    have hj : (Fin.rev j).val = k - 1 - j.val := by
      rw [Fin.val_rev]; omega
    have hik : i.val < k := i.isLt
    have hjk : j.val < k := j.isLt
    simp only [hv, hi, hj]
    have ci : ((k - 1 - i.val : ℕ) : ℤ) = (k : ℤ) - 1 - i.val := by omega
    have cj : ((k - 1 - j.val : ℕ) : ℤ) = (k : ℤ) - 1 - j.val := by omega
    rw [ci, cj]; ring
  have hleft : (Matrix.vandermonde (v ∘ Fin.rev)).det
      = (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin k)) : ℤ) * (Matrix.vandermonde v).det := by
    rw [show Matrix.vandermonde (v ∘ Fin.rev)
          = (Matrix.vandermonde v).submatrix (Fin.revPerm : Equiv.Perm (Fin k)) id from
        Matrix.ext fun _ _ => rfl, Matrix.det_permute]
    simp
  have hright : (Matrix.vandermonde (v ∘ Fin.rev)).det
      = (-1) ^ (k * (k - 1) / 2) * (Matrix.vandermonde v).det := by
    rw [Matrix.det_vandermonde, Matrix.det_vandermonde, ← hcard]
    rw [show (∏ i : Fin k, ∏ j ∈ Finset.Ioi i, ((v ∘ Fin.rev) j - (v ∘ Fin.rev) i))
        = ∏ i : Fin k, ∏ j ∈ Finset.Ioi i, (-1 : ℤ) * (v j - v i) from
      Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => by
        simpa using hstep i j]
    rw [show (∏ i : Fin k, ∏ j ∈ Finset.Ioi i, (-1 : ℤ) * (v j - v i))
        = ∏ i : Fin k, ((-1 : ℤ) ^ (Finset.Ioi i).card * ∏ j ∈ Finset.Ioi i, (v j - v i)) from
      Finset.prod_congr rfl fun i _ => by
        rw [Finset.prod_mul_distrib, Finset.prod_const]]
    rw [Finset.prod_mul_distrib, ← Finset.prod_pow_eq_pow_sum]
  exact mul_right_cancel₀ hne (hleft.symm.trans hright)

/-- Descending powers: the Leibniz sum of `∏_j t_{τ(j)}^{-j}` is `Δ(t)` again,
up to the sign of the reversal permutation and a common power of `∏_a t_a`. -/
theorem sum_sign_prod_zpow_neg {k : ℕ} (t : Fin k → ℂ) (ht : ∀ a, t a ≠ 0) :
    (∑ τ : Equiv.Perm (Fin k), ((Equiv.Perm.sign τ : ℤ) : ℂ) * ∏ j, t (τ j) ^ (-(j.val : ℤ)))
      = (-1) ^ (k * (k - 1) / 2) * (∏ a, t a ^ (-((k : ℤ) - 1))) * vandermondeProd t := by
  set A : Matrix (Fin k) (Fin k) ℂ := Matrix.of fun i j => t i ^ (-(j.val : ℤ)) with hA
  have hdet : A.det
      = ∑ τ : Equiv.Perm (Fin k),
          ((Equiv.Perm.sign τ : ℤ) : ℂ) * ∏ j, t (τ j) ^ (-(j.val : ℤ)) := by
    rw [Matrix.det_apply']
    refine Finset.sum_congr rfl fun τ _ => ?_
    simp [hA]
  have hsplit : A = Matrix.of fun i j =>
      t i ^ (-((k : ℤ) - 1)) * (Matrix.vandermonde t).submatrix id Fin.rev i j := by
    refine Matrix.ext fun i j => ?_
    have hjk : j.val < k := j.isLt
    have hrev : (Fin.rev j).val = k - 1 - j.val := by rw [Fin.val_rev]; omega
    have hexp : -((k : ℤ) - 1) + (((Fin.rev j).val : ℕ) : ℤ) = -(j.val : ℤ) := by
      rw [hrev]; omega
    simp only [hA, Matrix.of_apply, Matrix.submatrix_apply, id_eq, Matrix.vandermonde_apply]
    rw [← zpow_natCast (t i) ((Fin.rev j).val), ← zpow_add₀ (ht i), hexp]
  have h1 : A.det
      = (∏ a, t a ^ (-((k : ℤ) - 1))) * ((Matrix.vandermonde t).submatrix id Fin.rev).det := by
    rw [hsplit]; exact Matrix.det_mul_column _ _
  have h2 : ((Matrix.vandermonde t).submatrix id Fin.rev).det
      = (((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin k)) : ℤ)) : ℂ)
        * (Matrix.vandermonde t).det := by
    rw [show (Matrix.vandermonde t).submatrix id Fin.rev
          = (Matrix.vandermonde t).submatrix id (Fin.revPerm : Equiv.Perm (Fin k)) from rfl,
      Matrix.det_permute']
  rw [← hdet, h1, h2, ← vandermondeProd_eq_det, sign_finRevPerm k]
  push_cast
  ring


/-! ### The integral Andréief identity -/

section Andreief

variable {k : ℕ} {ρ : ℝ} {G : ℂ → ℂ}

theorem CircleIntegrablePow.const_mul {F : (Fin k → ℂ) → ℂ}
    (h : CircleIntegrablePow k ρ F) (c : ℂ) :
    CircleIntegrablePow k ρ (fun t => c * F t) := by
  unfold CircleIntegrablePow at h ⊢
  exact (h.const_mul c).congr (Filter.Eventually.of_forall fun θ => by ring)

theorem mapsTo_polyCircle (hρ : 0 < ρ) (a : Fin k) :
    Set.MapsTo (fun t : Fin k → ℂ => t a) (polyCircle k ρ) (Metric.sphere 0 ρ) := by
  intro t ht
  rw [mem_sphere_zero_iff_norm, mem_polyCircle.mp ht a, abs_of_pos hρ]

/-- On the polycircle `|t_a| = ρ` a product `∏_a G(t_a)t_a^{e_a}` is continuous:
each variable stays on the circle, where `G` is continuous and the integer power
is regular because `ρ > 0` keeps it off the origin. -/
theorem continuousOn_polyCircle_prod (hρ : 0 < ρ)
    (hG : ContinuousOn G (Metric.sphere 0 ρ)) (e : Fin k → ℤ) :
    ContinuousOn (fun t : Fin k → ℂ => ∏ a, G (t a) * t a ^ e a) (polyCircle k ρ) := by
  refine continuousOn_finsetProd _ fun a _ => ContinuousOn.mul ?_ ?_
  · exact hG.comp (continuous_apply a).continuousOn (mapsTo_polyCircle hρ a)
  · exact (continuous_apply a).continuousOn.zpow₀ _ fun t ht =>
      Or.inl (ne_zero_of_mem_polyCircle hρ.ne' ht a)

theorem continuous_vandermondeProd :
    Continuous (fun t : Fin k → ℂ => vandermondeProd t) := by
  refine continuous_finsetProd _ fun a _ => continuous_finsetProd _ fun b _ => ?_
  exact (continuous_apply b).sub (continuous_apply a)

/-- **The integral Andréief identity.**  If
`B m` is the `m`th coefficient integral of `G` over the circle `|t| = ρ`, then
the `k × k` staircase minor `det [B (n-i+j)]` is the `k`-fold contour integral
\[
  \frac{(-1)^{k(k-1)/2}}{k!\,(2\pi i)^k}
  \int\cdots\int\Delta(t)^2\prod_{a=1}^k G(t_a)\,t_a^{-n-k}\,dt_a .
\]
Indices are zero-based here, so the entry in row `i` and column `j` is
`B (n - i + j)` for `i j : Fin k`; the one-based
`\det[B_{n-i+j}]_{i,j=1}^k` is the same matrix.  The order `n` is an arbitrary
integer: nothing forces `B m` to vanish for negative `m`. -/
theorem det_staircase_eq_circleIntegralPow (n : ℤ) (hρ : 0 < ρ)
    (hG : ContinuousOn G (Metric.sphere 0 ρ)) {B : ℤ → ℂ}
    (hB : ∀ m : ℤ, B m = (2 * π * I)⁻¹ * ∮ z in C(0, ρ), G z * z ^ (-m - 1)) :
    (Matrix.of fun i j : Fin k => B (n - (i.val : ℤ) + (j.val : ℤ))).det
      = (-1) ^ (k * (k - 1) / 2) / ((Nat.factorial k : ℂ) * (2 * π * I) ^ k)
        * circleIntegralPow k ρ
            (fun t => vandermondeProd t ^ 2 * ∏ a, G (t a) * t a ^ (-n - (k : ℤ))) := by
  have hπ : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have hfac : (Nat.factorial k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  -- Integrability of every integrand met below.
  have hint : ∀ e : Fin k → ℤ,
      CircleIntegrablePow k ρ (fun t => ∏ a, G (t a) * t a ^ e a) := fun e =>
    CircleIntegrablePow.of_continuousOn (continuousOn_polyCircle_prod hρ hG e)
  have hsumint : ∀ F : Equiv.Perm (Fin k) → (Fin k → ℂ) → ℂ,
      (∀ σ, CircleIntegrablePow k ρ (F σ)) →
      (∑ σ : Equiv.Perm (Fin k), circleIntegralPow k ρ (F σ))
        = circleIntegralPow k ρ (fun t => ∑ σ : Equiv.Perm (Fin k), F σ t) :=
    fun F hF => (circleIntegralPow_finset_sum Finset.univ F fun σ _ => hF σ).symm
  have hintV : ∀ e : Fin k → ℤ,
      CircleIntegrablePow k ρ (fun t => vandermondeProd t * ∏ a, G (t a) * t a ^ e a) :=
    fun e => CircleIntegrablePow.of_continuousOn
      (continuous_vandermondeProd.continuousOn.mul (continuousOn_polyCircle_prod hρ hG e))
  -- Fubini on the Leibniz term attached to a permutation.
  have hfub : ∀ σ : Equiv.Perm (Fin k),
      circleIntegralPow k ρ
          (fun t => ∏ j, G (t j) * t j ^ (((σ j).val : ℤ) - (j.val : ℤ) - n - 1))
        = ∏ j : Fin k, ∮ z in C(0, ρ), G z * z ^ (((σ j).val : ℤ) - (j.val : ℤ) - n - 1) :=
    fun σ => circleIntegralPow_prod ρ
      fun j z => G z * z ^ (((σ j).val : ℤ) - (j.val : ℤ) - n - 1)
  have hBprod : ∀ σ : Equiv.Perm (Fin k),
      (∏ j, B (n - ((σ j).val : ℤ) + (j.val : ℤ)))
        = ((2 * π * I : ℂ)⁻¹) ^ k * circleIntegralPow k ρ
            (fun t => ∏ j, G (t j) * t j ^ (((σ j).val : ℤ) - (j.val : ℤ) - n - 1)) := by
    intro σ
    have hpow : ((2 * π * I : ℂ)⁻¹) ^ k = ∏ _j : Fin k, (2 * π * I : ℂ)⁻¹ := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [hfub σ, hpow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    have hexp : -(n - ((σ j).val : ℤ) + (j.val : ℤ)) - 1
        = ((σ j).val : ℤ) - (j.val : ℤ) - n - 1 := by ring
    rw [hB, hexp]
  -- Step 1: expand the determinant and merge the `k` coefficient integrals.
  have step1 : (Matrix.of fun i j : Fin k => B (n - (i.val : ℤ) + (j.val : ℤ))).det
      = ((2 * π * I : ℂ)⁻¹) ^ k * circleIntegralPow k ρ
          (fun t => vandermondeProd t * ∏ j, G (t j) * t j ^ (-(j.val : ℤ) - n - 1)) := by
    rw [Matrix.det_apply']
    calc (∑ σ : Equiv.Perm (Fin k), ((Equiv.Perm.sign σ : ℤ) : ℂ)
            * ∏ i, (Matrix.of fun i j : Fin k => B (n - (i.val : ℤ) + (j.val : ℤ))) (σ i) i)
        = ∑ σ : Equiv.Perm (Fin k), ((2 * π * I : ℂ)⁻¹) ^ k * circleIntegralPow k ρ
            (fun t => ((Equiv.Perm.sign σ : ℤ) : ℂ)
              * ∏ j, G (t j) * t j ^ (((σ j).val : ℤ) - (j.val : ℤ) - n - 1)) :=
          Finset.sum_congr rfl fun σ _ => by
            rw [circleIntegralPow_const_mul,
              show (∏ i, (Matrix.of fun i j : Fin k =>
                  B (n - (i.val : ℤ) + (j.val : ℤ))) (σ i) i)
                = ∏ j, B (n - ((σ j).val : ℤ) + (j.val : ℤ)) from rfl, hBprod σ]
            ring
      _ = ((2 * π * I : ℂ)⁻¹) ^ k * ∑ σ : Equiv.Perm (Fin k), circleIntegralPow k ρ
            (fun t => ((Equiv.Perm.sign σ : ℤ) : ℂ)
              * ∏ j, G (t j) * t j ^ (((σ j).val : ℤ) - (j.val : ℤ) - n - 1)) :=
          (Finset.mul_sum _ _ _).symm
      _ = ((2 * π * I : ℂ)⁻¹) ^ k * circleIntegralPow k ρ
            (fun t => ∑ σ : Equiv.Perm (Fin k), ((Equiv.Perm.sign σ : ℤ) : ℂ)
              * ∏ j, G (t j) * t j ^ (((σ j).val : ℤ) - (j.val : ℤ) - n - 1)) :=
          congrArg (fun x => ((2 * π * I : ℂ)⁻¹) ^ k * x)
            (hsumint (fun σ t => ((Equiv.Perm.sign σ : ℤ) : ℂ)
                * ∏ j, G (t j) * t j ^ (((σ j).val : ℤ) - (j.val : ℤ) - n - 1))
              fun σ => (hint fun j => ((σ j).val : ℤ) - (j.val : ℤ) - n - 1).const_mul _)
      _ = ((2 * π * I : ℂ)⁻¹) ^ k * circleIntegralPow k ρ
            (fun t => vandermondeProd t * ∏ j, G (t j) * t j ^ (-(j.val : ℤ) - n - 1)) := by
          refine congrArg _ (circleIntegralPow_congr fun t ht => ?_)
          have hne : ∀ a, t a ≠ 0 := fun a => ne_zero_of_mem_polyCircle hρ.ne' ht a
          calc (∑ σ : Equiv.Perm (Fin k), ((Equiv.Perm.sign σ : ℤ) : ℂ)
                  * ∏ j, G (t j) * t j ^ (((σ j).val : ℤ) - (j.val : ℤ) - n - 1))
              = ∑ σ : Equiv.Perm (Fin k),
                  (((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ j, t j ^ ((σ j).val : ℕ))
                    * ∏ j, G (t j) * t j ^ (-(j.val : ℤ) - n - 1) :=
                Finset.sum_congr rfl fun σ _ => by
                  rw [mul_assoc, ← Finset.prod_mul_distrib]
                  refine congrArg _ (Finset.prod_congr rfl fun j _ => ?_)
                  rw [← zpow_natCast (t j) ((σ j).val),
                    show (((σ j).val : ℤ) - (j.val : ℤ) - n - 1)
                      = ((σ j).val : ℤ) + (-(j.val : ℤ) - n - 1) by ring,
                    zpow_add₀ (hne j)]
                  ring
            _ = (∑ σ : Equiv.Perm (Fin k), ((Equiv.Perm.sign σ : ℤ) : ℂ)
                    * ∏ j, t j ^ ((σ j).val : ℕ))
                  * ∏ j, G (t j) * t j ^ (-(j.val : ℤ) - n - 1) := (Finset.sum_mul _ _ _).symm
            _ = vandermondeProd t * ∏ j, G (t j) * t j ^ (-(j.val : ℤ) - n - 1) := by
                rw [sum_sign_prod_pow t]
  -- Step 2: symmetrize the `k` variables.
  have step2 : (Nat.factorial k : ℂ) * circleIntegralPow k ρ
        (fun t => vandermondeProd t * ∏ j, G (t j) * t j ^ (-(j.val : ℤ) - n - 1))
      = (-1) ^ (k * (k - 1) / 2) * circleIntegralPow k ρ
          (fun t => vandermondeProd t ^ 2 * ∏ a, G (t a) * t a ^ (-n - (k : ℤ))) := by
    have hcard : ((Finset.univ : Finset (Equiv.Perm (Fin k))).card : ℂ)
        = (Nat.factorial k : ℂ) := by
      rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
    calc (Nat.factorial k : ℂ) * circleIntegralPow k ρ
          (fun t => vandermondeProd t * ∏ j, G (t j) * t j ^ (-(j.val : ℤ) - n - 1))
        = ∑ _τ : Equiv.Perm (Fin k), circleIntegralPow k ρ
            (fun t => vandermondeProd t * ∏ j, G (t j) * t j ^ (-(j.val : ℤ) - n - 1)) := by
          rw [Finset.sum_const, nsmul_eq_mul, hcard]
      _ = ∑ τ : Equiv.Perm (Fin k), circleIntegralPow k ρ
            (fun t => (fun s : Fin k → ℂ => vandermondeProd s
                * ∏ j, G (s j) * s j ^ (-(j.val : ℤ) - n - 1)) (t ∘ τ)) :=
          Finset.sum_congr rfl fun τ _ =>
            (circleIntegralPow_comp_perm ρ _ τ).symm
      _ = circleIntegralPow k ρ (fun t => ∑ τ : Equiv.Perm (Fin k),
            (fun s : Fin k → ℂ => vandermondeProd s
              * ∏ j, G (s j) * s j ^ (-(j.val : ℤ) - n - 1)) (t ∘ τ)) :=
          hsumint (fun τ t => (fun s : Fin k → ℂ => vandermondeProd s
              * ∏ j, G (s j) * s j ^ (-(j.val : ℤ) - n - 1)) (t ∘ τ))
            fun τ => (hintV fun j => -(j.val : ℤ) - n - 1).comp_perm τ
      _ = (-1) ^ (k * (k - 1) / 2) * circleIntegralPow k ρ
            (fun t => vandermondeProd t ^ 2 * ∏ a, G (t a) * t a ^ (-n - (k : ℤ))) := by
          rw [← circleIntegralPow_const_mul]
          refine circleIntegralPow_congr fun t ht => ?_
          have hne : ∀ a, t a ≠ 0 := fun a => ne_zero_of_mem_polyCircle hρ.ne' ht a
          have hmerge : (∏ a, t a ^ (-((k : ℤ) - 1))) * ∏ a, G (t a) * t a ^ (-n - 1)
              = ∏ a, G (t a) * t a ^ (-n - (k : ℤ)) := by
            rw [← Finset.prod_mul_distrib]
            refine Finset.prod_congr rfl fun a _ => ?_
            rw [show (-n - (k : ℤ)) = (-((k : ℤ) - 1)) + (-n - 1) by ring, zpow_add₀ (hne a)]
            ring
          calc (∑ τ : Equiv.Perm (Fin k), vandermondeProd (t ∘ τ)
                  * ∏ j, G ((t ∘ τ) j) * (t ∘ τ) j ^ (-(j.val : ℤ) - n - 1))
              = ∑ τ : Equiv.Perm (Fin k),
                  (((Equiv.Perm.sign τ : ℤ) : ℂ) * ∏ j, t (τ j) ^ (-(j.val : ℤ)))
                    * (vandermondeProd t * ∏ a, G (t a) * t a ^ (-n - 1)) :=
                Finset.sum_congr rfl fun τ _ => by
                  rw [vandermondeProd_comp_perm t τ,
                    show (∏ j, G ((t ∘ τ) j) * (t ∘ τ) j ^ (-(j.val : ℤ) - n - 1))
                      = ∏ j, t (τ j) ^ (-(j.val : ℤ)) * (G (t (τ j)) * t (τ j) ^ (-n - 1)) from
                      Finset.prod_congr rfl fun j _ => by
                        simp only [Function.comp_apply]
                        rw [show (-(j.val : ℤ) - n - 1) = -(j.val : ℤ) + (-n - 1) by ring,
                          zpow_add₀ (hne (τ j))]
                        ring,
                    Finset.prod_mul_distrib,
                    Equiv.prod_comp τ fun a => G (t a) * t a ^ (-n - 1)]
                  ring
            _ = (∑ τ : Equiv.Perm (Fin k),
                    ((Equiv.Perm.sign τ : ℤ) : ℂ) * ∏ j, t (τ j) ^ (-(j.val : ℤ)))
                  * (vandermondeProd t * ∏ a, G (t a) * t a ^ (-n - 1)) :=
                (Finset.sum_mul _ _ _).symm
            _ = (-1) ^ (k * (k - 1) / 2)
                  * (vandermondeProd t ^ 2 * ∏ a, G (t a) * t a ^ (-n - (k : ℤ))) := by
                rw [sum_sign_prod_zpow_neg t hne, ← hmerge]
                ring
  rw [step1, show circleIntegralPow k ρ
        (fun t => vandermondeProd t * ∏ j, G (t j) * t j ^ (-(j.val : ℤ) - n - 1))
      = (Nat.factorial k : ℂ)⁻¹ * ((-1) ^ (k * (k - 1) / 2) * circleIntegralPow k ρ
          (fun t => vandermondeProd t ^ 2 * ∏ a, G (t a) * t a ^ (-n - (k : ℤ)))) by
    rw [← step2, ← mul_assoc, inv_mul_cancel₀ hfac, one_mul]]
  rw [inv_pow, div_eq_mul_inv, mul_inv]
  ring

end Andreief

end Shields
