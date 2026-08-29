/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import Shields.Analysis.Complex.ArgumentPrinciple.Polynomial
import ForgacsTran.FTBranchPencil
import ForgacsTran.AttractorPole

/-!
# The separating circle at the lower endpoint

`thm:weighted-dominance` carries a radius `R_0` around which the retained cluster
is read: every retained zero lies strictly inside it, every zero of the pencil
inside it is retained, and `B/D` is bounded on it.  Those are the `haR₀`,
`huniq₀` and `hCbd₀` binders of
`DominanceFTBranch.weighted_dominance_of_branch_any_multiplicity_at`,
and none of them is available until a radius has been named.

The radius is fixed by the spectrum of `Q` alone.  With `Q = c∏(a_k - X)`, every
`a_k > 0` and `x_1 = min a_k` carried `ρ` times, the separating quantity is the
**ratio** `m/x_1`, where `m` is the smallest zero above `x_1`; any `R_0` strictly
between them separates the collapsing cluster from the rest of the spectrum, and
`ftSepRadius` takes the midpoint.  Nothing here is a numeral: every bound below
scales with `x_1`.

On `‖t‖ = R_0` the modulus of `Q` is bounded below without any compactness
argument, since `|a_k - t| ≥ ||t| - a_k| = |R_0 - a_k|` and each `a_k` is either
`x_1` or at least `m`.  That elementary floor `|c|d^n`, with `d` the clearance the
midpoint leaves on both sides, is what makes the circle zero-free for the whole
pencil at small spectral parameter, what produces the contour constant, and — being
strictly above `‖z‖‖t‖^r` over the window — Rouché's hypothesis verbatim.  So the
zero count in the disk is `Q`'s own, which is the multiplicity of `x_1`.

## Main statements

* `ftSepRadius`, `ftSepGap`, `ftSepFloor` — the radius, the gap it leaves on both
  sides, and the floor the gap forces on `|Q|`.
* `ftSepFloor_le_norm_eval` — the floor, on the circle.
* `norm_eval_ftDen_ge` — the pencil's own floor, half of `Q`'s, for
  `|z| ≤ ftSepWindow`.
* `eval_ftDen_ne_zero_on_sphere` — the circle is zero-free.
* `exists_endpoint_contour_bound` — `‖B/D‖ ≤ C_0` on the circle, uniformly in the
  spectral parameter over the window: the `hCbd₀` binder.
* `norm_lt_ftSepRadius_of_le_x1` — a point of modulus at most `x_1` is strictly
  inside, whatever the pencil is doing.
* `ftSepRatio_lt_one` — the geometric rate `x_1/R_0` of `hσ₀`.
* `diskRoots`, `mem_diskRoots` — the retained set, defined as the zeros of the
  pencil in the closed disk rather than supplied.
* `eval_eq_zero_of_mem_diskRoots`, `mem_diskRoots_of_eval_eq_zero`,
  `norm_lt_of_mem_diskRoots` — the `hroot₀`, `huniq₀` and `haR₀` binders at that
  set.  The first two are true by construction; the third is the circle's
  zero-freeness, since the disk is closed.
* `card_rootsIn_ftRootPoly`, `card_rootsIn_ftDen` — `Q` has `ρ` zeros in the disk
  and so does the whole pencil over the window, by Rouché against the floor.
* `simple_and_complete_of_count` — `N` distinct zeros in a disk carrying `N` are
  therefore each simple and are all of them.  Stated at an arbitrary polynomial,
  radius and count, because both endpoints consume it; `simple_and_complete_of_card`
  is it at the lower endpoint's own circle.  This is the single obligation behind
  `hsimple₀`, `hginj₀`, `hgmem₀` and `hgcard₀`, and behind their `₁` mirrors.
* `ftUpperRadius`, `ftUpperCeil`, `ftUpperWindow`, `norm_eval_ftRootPoly_le`,
  `norm_eval_ftDen_ge_upper`, `eval_ftDen_ne_zero_on_upper_sphere`,
  `ftDen_ne_zero_of_upper_window`, `card_rootsIn_ftDen_upper` — **the upper
  endpoint's own circle**, inside the smallest zero rather than outside it, with
  `z X^r` dominant rather than negligible and a count of `r` rather than `ρ`.
* `eval_derivative_ftDen_mul`, `eval_derivative_ftDen_ne_zero_of_ftCritical`,
  `eval_ftCritical_zero_ne_zero`, `exists_simple_radius` — **simplicity near the
  origin without a count**: `E` is parameter-free, so the pencil's multiple zeros
  are the zeros of one fixed polynomial, and `E(0) = -rQ(0) ≠ 0`.
* `norm_lt_of_mem_diskRoots_of_sphere`, `card_diskRoots_eq_card_rootsIn` — the
  retained set at an arbitrary circle, and when its cardinality is the count.

## Implementation notes

**Differs from the paper's route.**  The manuscript takes the separating circle
as given, describing it as a contour on which the retained zeros are inside and
the rest outside.  Here the radius is *constructed* from the spectrum and the
zero-freeness is proved by the triangle inequality rather than assumed, because a
binder asserting a zero-free circle is exactly the kind that can be met vacuously
or not at all, and the pencil's degree jumps from `n` to `r` once `r > n` — the
`r - n` zeros that enter from infinity as `z → 0` leave the disk rather than
threaten it, and the estimate below says so with no case split.

**Containment.**  The separating results — `norm_eval_ftDen_ge`,
`eval_ftDen_ne_zero_on_sphere`, `exists_endpoint_contour_bound` and
`card_rootsIn_ftDen` — bound or count `ftDen (ftRootPoly c a) r z` on the sphere
of radius `ftSepRadius` from hypotheses constraining only the spectrum `a`, the
scalar `c`, the window `z` lies in and the modulus of the point.

Three statements below do carry a binder naming the pencil and the radius
together, and each is a step rather than a result.  `eval_eq_zero_of_mem_diskRoots`
and `norm_lt_of_mem_diskRoots` read `t ∈ diskRoots (ftDen (ftRootPoly c a) r z)
(ftSepRadius a x₁)`, membership in a `Finset` this module *defines* as the zeros
in the disk: the first is that definition's projection, while the second is not,
since turning `‖t‖ ≤ R_0` into `‖t‖ < R_0` is exactly
`eval_ftDen_ne_zero_on_sphere`.  `simple_and_complete_of_card` takes a candidate
set `T` of zeros strictly inside the circle and returns their simplicity and
completeness, which come from the Rouché count `card_rootsIn_ftDen` rather than
from `T`.

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Principal-pair
dominance and the fixed-numerator theorem» (`sec:dominance`,
`thm:weighted-dominance`, `eq:contour-remainder-bound`).

`scripts/check_endpoint_separating_radius.py` exhibits the floor, the window and
the zero count at five pencils.

## Tags

separating circle, contour bound, retained cluster, endpoint
-/

namespace ForgacsTran

open Polynomial Complex

/-- The smallest zero of `Q` strictly above `x_1`, or `x_1 + 1` when `x_1` is the
only one.  The separating data is a function of the ratio of this to `x_1`. -/
noncomputable def ftNextRoot {n : ℕ} (a : Fin n → ℝ) (x₁ : ℝ) : ℝ :=
  if h : ((Finset.univ.filter fun k => a k ≠ x₁).image a).Nonempty then
    ((Finset.univ.filter fun k => a k ≠ x₁).image a).min' h
  else x₁ + 1

/-- Every zero of `Q` other than `x_1` is at least `ftNextRoot`. -/
theorem ftNextRoot_le {n : ℕ} {a : Fin n → ℝ} {x₁ : ℝ} {k : Fin n} (hk : a k ≠ x₁) :
    ftNextRoot a x₁ ≤ a k := by
  have hmem : a k ∈ (Finset.univ.filter fun k => a k ≠ x₁).image a :=
    Finset.mem_image.2 ⟨k, Finset.mem_filter.2 ⟨Finset.mem_univ k, hk⟩, rfl⟩
  have hne : ((Finset.univ.filter fun k => a k ≠ x₁).image a).Nonempty := ⟨a k, hmem⟩
  rw [ftNextRoot, dif_pos hne]
  exact Finset.min'_le _ _ hmem

/-- `x_1` sits strictly below the next zero.  This is where `hmin` is spent: the
smallest zero is `x_1`, so anything different from it is larger. -/
theorem lt_ftNextRoot {n : ℕ} {a : Fin n → ℝ} {x₁ : ℝ} (hmin : ∀ k, x₁ ≤ a k) :
    x₁ < ftNextRoot a x₁ := by
  by_cases hne : ((Finset.univ.filter fun k => a k ≠ x₁).image a).Nonempty
  · rw [ftNextRoot, dif_pos hne]
    obtain ⟨k, hk, hka⟩ := Finset.mem_image.1 (Finset.min'_mem _ hne)
    have h1 : a k ≠ x₁ := (Finset.mem_filter.1 hk).2
    have h2 : x₁ ≤ a k := hmin k
    rw [← hka]
    exact lt_of_le_of_ne h2 (Ne.symm h1)
  · rw [ftNextRoot, dif_neg hne]; linarith

/-- The separating radius: the midpoint of `x_1` and the next zero. -/
noncomputable def ftSepRadius {n : ℕ} (a : Fin n → ℝ) (x₁ : ℝ) : ℝ :=
  (x₁ + ftNextRoot a x₁) / 2

/-- The clearance the radius leaves on either side.  Both sides are the same
number, which is why no `min` appears: `R_0 - x_1 = m - R_0`. -/
noncomputable def ftSepGap {n : ℕ} (a : Fin n → ℝ) (x₁ : ℝ) : ℝ :=
  (ftNextRoot a x₁ - x₁) / 2

theorem ftSepGap_pos {n : ℕ} {a : Fin n → ℝ} {x₁ : ℝ} (hmin : ∀ k, x₁ ≤ a k) :
    0 < ftSepGap a x₁ := by
  rw [ftSepGap]; linarith [lt_ftNextRoot hmin]

theorem lt_ftSepRadius {n : ℕ} {a : Fin n → ℝ} {x₁ : ℝ} (hmin : ∀ k, x₁ ≤ a k) :
    x₁ < ftSepRadius a x₁ := by
  rw [ftSepRadius]; linarith [lt_ftNextRoot hmin]

theorem ftSepRadius_pos {n : ℕ} {a : Fin n → ℝ} {x₁ : ℝ} (hx₁ : 0 < x₁)
    (hmin : ∀ k, x₁ ≤ a k) : 0 < ftSepRadius a x₁ :=
  lt_trans hx₁ (lt_ftSepRadius hmin)

theorem ftSepRadius_sub {n : ℕ} (a : Fin n → ℝ) (x₁ : ℝ) :
    ftSepRadius a x₁ - x₁ = ftSepGap a x₁ := by
  rw [ftSepRadius, ftSepGap]; ring

/-- A point of modulus at most `x_1` lies strictly inside the circle.  Every
retained zero at the lower endpoint does — the cluster collapses to `x_1` and the
branch radius is bounded by it — so this is the half of `haR₀` that is settled by
the radius alone, before the cluster is enumerated. -/
theorem norm_lt_ftSepRadius_of_le_x1 {n : ℕ} {a : Fin n → ℝ} {x₁ : ℝ}
    (hmin : ∀ k, x₁ ≤ a k) {t : ℂ} (ht : ‖t‖ ≤ x₁) : ‖t‖ < ftSepRadius a x₁ :=
  lt_of_le_of_lt ht (lt_ftSepRadius hmin)

/-- **Every zero of `Q` is off the circle, by the gap.**  A zero equal to `x_1`
is `R_0 - x_1 = d` inside it; one different from `x_1` is at least `m - R_0 = d`
outside.  The two cases give the same number, which is the point of taking the
midpoint. -/
theorem ftSepGap_le_dist {n : ℕ} {a : Fin n → ℝ} {x₁ : ℝ} (ha : ∀ k, 0 < a k)
    (hmin : ∀ k, x₁ ≤ a k) (k : Fin n) {t : ℂ} (ht : ‖t‖ = ftSepRadius a x₁) :
    ftSepGap a x₁ ≤ ‖((a k : ℝ) : ℂ) - t‖ := by
  have hR : x₁ < ftSepRadius a x₁ := lt_ftSepRadius hmin
  have h1 : ‖((a k : ℝ) : ℂ)‖ = a k := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (ha k)]
  by_cases hk : a k = x₁
  · have h2 : ‖t‖ - ‖((a k : ℝ) : ℂ)‖ ≤ ‖((a k : ℝ) : ℂ) - t‖ := by
      rw [← norm_neg (((a k : ℝ) : ℂ) - t), neg_sub]
      exact norm_sub_norm_le _ _
    rw [ht, h1] at h2
    have h3 := ftSepRadius_sub a x₁
    linarith
  · have hak : ftNextRoot a x₁ ≤ a k := ftNextRoot_le hk
    have h2 : ‖((a k : ℝ) : ℂ)‖ - ‖t‖ ≤ ‖((a k : ℝ) : ℂ) - t‖ := norm_sub_norm_le _ _
    rw [ht, h1] at h2
    have h3 : ftSepGap a x₁ ≤ a k - ftSepRadius a x₁ := by
      rw [ftSepGap, ftSepRadius]; linarith
    linarith

/-- The floor the gap forces on `|Q|` over the circle. -/
noncomputable def ftSepFloor {n : ℕ} (c : ℝ) (a : Fin n → ℝ) (x₁ : ℝ) : ℝ :=
  |c| * ftSepGap a x₁ ^ n

theorem ftSepFloor_pos {n : ℕ} {c : ℝ} {a : Fin n → ℝ} {x₁ : ℝ} (hc : c ≠ 0)
    (hmin : ∀ k, x₁ ≤ a k) : 0 < ftSepFloor c a x₁ :=
  mul_pos (abs_pos.2 hc) (pow_pos (ftSepGap_pos hmin) n)

/-- **The floor, on the circle.**  `|Q(t)| = |c|∏|a_k - t|` and each factor is at
least the gap, so no compactness argument is needed and the bound is explicit in
the spectrum. -/
theorem ftSepFloor_le_norm_eval {n : ℕ} {c : ℝ} {a : Fin n → ℝ} {x₁ : ℝ}
    (ha : ∀ k, 0 < a k) (hmin : ∀ k, x₁ ≤ a k) {t : ℂ} (ht : ‖t‖ = ftSepRadius a x₁) :
    ftSepFloor c a x₁ ≤ ‖(ftRootPoly c a).eval t‖ := by
  rw [eval_ftRootPoly, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_prod, ftSepFloor]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg c)
  calc ftSepGap a x₁ ^ n
      = ∏ _k : Fin n, ftSepGap a x₁ := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ ∏ k : Fin n, ‖((a k : ℝ) : ℂ) - t‖ :=
        Finset.prod_le_prod (fun k _ => (ftSepGap_pos hmin).le)
          (fun k _ => ftSepGap_le_dist ha hmin k ht)

/-- The window on the spectral parameter over which the circle stays clear: half
the floor, divided by `R_0^r`. -/
noncomputable def ftSepWindow {n : ℕ} (c : ℝ) (a : Fin n → ℝ) (x₁ : ℝ) (r : ℕ) : ℝ :=
  ftSepFloor c a x₁ / (2 * ftSepRadius a x₁ ^ r)

theorem ftSepWindow_pos {n : ℕ} {c : ℝ} {a : Fin n → ℝ} {x₁ : ℝ} {r : ℕ} (hc : c ≠ 0)
    (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k) : 0 < ftSepWindow c a x₁ r :=
  div_pos (ftSepFloor_pos hc hmin) (by
    have h := ftSepRadius_pos hx₁ hmin
    positivity)

/-- **The pencil's own floor on the circle.**  `‖D‖ ≥ ‖Q‖ - ‖z‖‖t‖^r`, and the
window is exactly what leaves half the floor standing.  The `r > n` case needs no
separate treatment: the extra zeros the degree jump produces have modulus of order
`|z|^{-1/(r-n)}`, so they leave the disk rather than enter it, and the inequality
below never sees them. -/
theorem norm_eval_ftDen_ge {n : ℕ} {c : ℝ} {a : Fin n → ℝ} {x₁ : ℝ} {r : ℕ}
    (ha : ∀ k, 0 < a k) (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    {z : ℂ} (hz : ‖z‖ ≤ ftSepWindow c a x₁ r)
    {t : ℂ} (ht : ‖t‖ = ftSepRadius a x₁) :
    ftSepFloor c a x₁ / 2 ≤ ‖(ftDen (ftRootPoly c a) r z).eval t‖ := by
  have hR : 0 < ftSepRadius a x₁ := ftSepRadius_pos hx₁ hmin
  have hQ := ftSepFloor_le_norm_eval (c := c) ha hmin ht
  have hzt : ‖z * t ^ r‖ ≤ ftSepFloor c a x₁ / 2 := by
    rw [norm_mul, norm_pow, ht]
    calc ‖z‖ * ftSepRadius a x₁ ^ r
        ≤ ftSepWindow c a x₁ r * ftSepRadius a x₁ ^ r :=
          mul_le_mul_of_nonneg_right hz (by positivity)
      _ = ftSepFloor c a x₁ / 2 := by
          rw [ftSepWindow]
          field_simp
  rw [ftDen_eval]
  have hsplit := norm_sub_norm_le ((ftRootPoly c a).eval t) (-(z * t ^ r))
  rw [sub_neg_eq_add, norm_neg] at hsplit
  linarith

/-- **The circle is zero-free.**  Immediate from the floor, and it is what makes
`huniq₀`'s closed disk a legitimate place to count zeros and `hCbd₀`'s quotient
defined. -/
theorem eval_ftDen_ne_zero_on_sphere {n : ℕ} {c : ℝ} {a : Fin n → ℝ} {x₁ : ℝ} {r : ℕ}
    (hc : c ≠ 0) (ha : ∀ k, 0 < a k) (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    {z : ℂ} (hz : ‖z‖ ≤ ftSepWindow c a x₁ r)
    {t : ℂ} (ht : ‖t‖ = ftSepRadius a x₁) :
    (ftDen (ftRootPoly c a) r z).eval t ≠ 0 := by
  intro h0
  have hb := norm_eval_ftDen_ge ha hx₁ hmin hz ht
  rw [h0, norm_zero] at hb
  exact absurd hb (not_le.2 (by linarith [ftSepFloor_pos (a := a) (x₁ := x₁) hc hmin]))

/-- **`hCbd₀`: the contour constant, uniform in the spectral parameter.**  `B` is
bounded on the circle by compactness and `D` is bounded below on it by the floor,
so the quotient is bounded by one constant for every `z` in the window — which is
the uniformity `eq:contour-remainder-bound` asserts and the manuscript states in
prose.

The constant depends on `B`; the radius and the window do not, which is why they
are definitions above and this is an existential. -/
theorem exists_endpoint_contour_bound {n : ℕ} {c : ℝ} {a : Fin n → ℝ} {x₁ : ℝ} {r : ℕ}
    (hc : c ≠ 0) (ha : ∀ k, 0 < a k) (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    (B : Polynomial ℂ) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ z : ℂ, ‖z‖ ≤ ftSepWindow c a x₁ r →
      ∀ t ∈ Metric.sphere (0 : ℂ) (ftSepRadius a x₁),
        ‖B.eval t / (ftDen (ftRootPoly c a) r z).eval t‖ ≤ C₀ := by
  obtain ⟨K, hK⟩ := (isCompact_sphere (0 : ℂ) (ftSepRadius a x₁)).exists_bound_of_continuousOn
    (f := fun t : ℂ => B.eval t) (by fun_prop)
  have hfl : 0 < ftSepFloor c a x₁ := ftSepFloor_pos hc hmin
  refine ⟨max K 0 / (ftSepFloor c a x₁ / 2),
    div_nonneg (le_max_right K 0) (by linarith), fun z hz t htmem => ?_⟩
  have ht : ‖t‖ = ftSepRadius a x₁ := by
    simpa [Complex.dist_eq, sub_zero] using Metric.mem_sphere.1 htmem
  have hD := norm_eval_ftDen_ge ha hx₁ hmin hz ht
  have hDpos : 0 < ‖(ftDen (ftRootPoly c a) r z).eval t‖ := lt_of_lt_of_le (by linarith) hD
  rw [norm_div, div_le_div_iff₀ hDpos (by linarith)]
  nlinarith [hK t htmem, hD, norm_nonneg (B.eval t), le_max_left K 0, le_max_right K 0]

/-! ### The retained set, as the zeros inside the circle -/

open scoped Classical in
/-- The zeros of `P` in the closed disk of radius `R`, as a finite set. -/
noncomputable def diskRoots (P : Polynomial ℂ) (R : ℝ) : Finset ℂ :=
  P.roots.toFinset.filter fun t => ‖t‖ ≤ R

theorem mem_diskRoots {P : Polynomial ℂ} (hP : P ≠ 0) {R : ℝ} {t : ℂ} :
    t ∈ diskRoots P R ↔ P.eval t = 0 ∧ ‖t‖ ≤ R := by
  classical
  simp only [diskRoots, Finset.mem_filter, Multiset.mem_toFinset, Polynomial.mem_roots',
    Polynomial.IsRoot.def]
  exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨hP, h.1⟩, h.2⟩⟩

/-- The pencil is not the zero polynomial anywhere in the window: it is nonzero at
the real point of the circle. -/
theorem ftDen_ne_zero_of_window {n : ℕ} {c : ℝ} {a : Fin n → ℝ} {x₁ : ℝ} {r : ℕ}
    (hc : c ≠ 0) (ha : ∀ k, 0 < a k) (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    {z : ℂ} (hz : ‖z‖ ≤ ftSepWindow c a x₁ r) :
    ftDen (ftRootPoly c a) r z ≠ 0 := by
  intro h0
  have hR : 0 < ftSepRadius a x₁ := ftSepRadius_pos hx₁ hmin
  have ht : ‖((ftSepRadius a x₁ : ℝ) : ℂ)‖ = ftSepRadius a x₁ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  exact eval_ftDen_ne_zero_on_sphere hc ha hx₁ hmin hz ht (by rw [h0]; simp)

/-- **`hroot₀`: every retained point is a zero.**  True by construction, once the
retained set is *defined* as the zeros in the disk rather than supplied. -/
theorem eval_eq_zero_of_mem_diskRoots {n : ℕ} {c : ℝ} {a : Fin n → ℝ} {x₁ : ℝ} {r : ℕ}
    (hc : c ≠ 0) (ha : ∀ k, 0 < a k) (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    {z : ℂ} (hz : ‖z‖ ≤ ftSepWindow c a x₁ r)
    {t : ℂ} (ht : t ∈ diskRoots (ftDen (ftRootPoly c a) r z) (ftSepRadius a x₁)) :
    (ftDen (ftRootPoly c a) r z).eval t = 0 :=
  ((mem_diskRoots (ftDen_ne_zero_of_window hc ha hx₁ hmin hz)).1 ht).1

/-- **`huniq₀`: nothing in the disk is left out.**  Also true by construction — the
content of the binder is that the disk is the *right* disk, which is what
`eval_ftDen_ne_zero_on_sphere` settles. -/
theorem mem_diskRoots_of_eval_eq_zero {n : ℕ} {c : ℝ} {a : Fin n → ℝ} {x₁ : ℝ} {r : ℕ}
    (hc : c ≠ 0) (ha : ∀ k, 0 < a k) (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    {z : ℂ} (hz : ‖z‖ ≤ ftSepWindow c a x₁ r)
    {t : ℂ} (htR : ‖t‖ ≤ ftSepRadius a x₁)
    (ht0 : (ftDen (ftRootPoly c a) r z).eval t = 0) :
    t ∈ diskRoots (ftDen (ftRootPoly c a) r z) (ftSepRadius a x₁) :=
  (mem_diskRoots (ftDen_ne_zero_of_window hc ha hx₁ hmin hz)).2 ⟨ht0, htR⟩

/-- **`haR₀`: every retained point is *strictly* inside.**  The disk is closed, so
strictness is exactly the statement that the circle carries no zero, and that is
`eval_ftDen_ne_zero_on_sphere`.  Nothing about the cluster's position is used:
this holds for every zero in the disk, wherever it came from. -/
theorem norm_lt_of_mem_diskRoots {n : ℕ} {c : ℝ} {a : Fin n → ℝ} {x₁ : ℝ} {r : ℕ}
    (hc : c ≠ 0) (ha : ∀ k, 0 < a k) (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    {z : ℂ} (hz : ‖z‖ ≤ ftSepWindow c a x₁ r)
    {t : ℂ} (ht : t ∈ diskRoots (ftDen (ftRootPoly c a) r z) (ftSepRadius a x₁)) :
    ‖t‖ < ftSepRadius a x₁ := by
  obtain ⟨ht0, htR⟩ := (mem_diskRoots (ftDen_ne_zero_of_window hc ha hx₁ hmin hz)).1 ht
  refine lt_of_le_of_ne htR fun hEq => ?_
  exact eval_ftDen_ne_zero_on_sphere hc ha hx₁ hmin hz hEq ht0

/-- **`hσ₀`: the branch radius sits below the circle by a fixed factor.**  At the
lower endpoint the branch radius is bounded by `x_1`, so the geometric rate the
contour remainder decays at may be taken to be `x_1 / R_0`, and it is below `1` by
the same gap that separates the spectrum.  The ratio is the separating quantity
again: `x_1/R_0 = 2x_1/(x_1 + m)`, a function of `m/x_1` alone. -/
theorem ftSepRatio_lt_one {n : ℕ} {a : Fin n → ℝ} {x₁ : ℝ} (hx₁ : 0 < x₁)
    (hmin : ∀ k, x₁ ≤ a k) : x₁ / ftSepRadius a x₁ < 1 :=
  (div_lt_one (ftSepRadius_pos hx₁ hmin)).2 (lt_ftSepRadius hmin)

/-! ### The count inside the circle -/

/-- The radius stays below the next zero, which is what puts every zero of `Q`
other than `x_1` outside the disk. -/
theorem ftSepRadius_lt_ftNextRoot {n : ℕ} {a : Fin n → ℝ} {x₁ : ℝ} (hmin : ∀ k, x₁ ≤ a k) :
    ftSepRadius a x₁ < ftNextRoot a x₁ := by
  rw [ftSepRadius]; linarith [lt_ftNextRoot hmin]

/-- `Q` is not the zero polynomial: `Q(0) = c∏a_k ≠ 0`. -/
theorem ftRootPoly_ne_zero' {n : ℕ} {c : ℝ} {a : Fin n → ℝ} (hc : c ≠ 0) (ha : ∀ k, 0 < a k) :
    ftRootPoly c a ≠ 0 := by
  intro h
  have h0 : (ftRootPoly c a).eval 0 = ((c * ∏ k, a k : ℝ) : ℂ) := by
    rw [eval_ftRootPoly]; push_cast; simp
  rw [h] at h0
  simp only [Polynomial.eval_zero] at h0
  exact (mul_ne_zero hc (ne_of_gt (Finset.prod_pos fun k _ => ha k)))
    (by exact_mod_cast h0.symm)

/-- Every zero of `Q` is one of the `a_k`. -/
theorem exists_eq_of_eval_ftRootPoly_eq_zero {n : ℕ} {c : ℝ} {a : Fin n → ℝ} (hc : c ≠ 0)
    {t : ℂ} (h : (ftRootPoly c a).eval t = 0) : ∃ k, ((a k : ℝ) : ℂ) = t := by
  rw [eval_ftRootPoly, mul_eq_zero] at h
  rcases h with h | h
  · exact absurd (by exact_mod_cast h : (c : ℝ) = 0) hc
  · obtain ⟨k, _, hk⟩ := Finset.prod_eq_zero_iff.1 h
    exact ⟨k, sub_eq_zero.1 hk⟩

/-- **`Q` has exactly `ρ` zeros in the disk, all at `x_1`.**  The count is the
multiplicity, because the radius separates `x_1` from every other zero. -/
theorem card_rootsIn_ftRootPoly {n : ℕ} {c : ℝ} {a : Fin n → ℝ} {x₁ : ℝ} {ρ : ℕ}
    (hc : c ≠ 0) (ha : ∀ k, 0 < a k) (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    (hmult : (ftRootPoly c a).rootMultiplicity ((x₁ : ℝ) : ℂ) = ρ) :
    Multiset.card (Shields.rootsIn (ftRootPoly c a) 0 (ftSepRadius a x₁)) = ρ := by
  classical
  have hP := ftRootPoly_ne_zero' hc ha
  have hR : x₁ < ftSepRadius a x₁ := lt_ftSepRadius hmin
  set M := Shields.rootsIn (ftRootPoly c a) 0 (ftSepRadius a x₁) with hM
  have hall : ∀ w ∈ M, w = ((x₁ : ℝ) : ℂ) := by
    intro w hw
    rw [hM, Shields.mem_rootsIn] at hw
    obtain ⟨hwr, hwb⟩ := hw
    have hz : (ftRootPoly c a).eval w = 0 := (Polynomial.mem_roots'.1 hwr).2
    obtain ⟨k, hk⟩ := exists_eq_of_eval_ftRootPoly_eq_zero hc hz
    have hnorm : ‖w‖ < ftSepRadius a x₁ := by
      simpa [Complex.dist_eq, sub_zero] using Metric.mem_ball.1 hwb
    rw [← hk, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (ha k)] at hnorm
    by_cases hkx : a k = x₁
    · rw [← hk, hkx]
    · exact absurd (lt_of_lt_of_le (lt_of_lt_of_le hnorm
        (ftSepRadius_lt_ftNextRoot hmin).le) (ftNextRoot_le hkx)) (lt_irrefl _)
  have hrep : M = Multiset.replicate (Multiset.card M) ((x₁ : ℝ) : ℂ) :=
    Multiset.eq_replicate_card.2 hall
  have hcount : Multiset.count ((x₁ : ℝ) : ℂ) M = Multiset.card M := by
    conv_lhs => rw [hrep]
    rw [Multiset.count_replicate_self]
  have hfil : Multiset.count ((x₁ : ℝ) : ℂ) M
      = Multiset.count ((x₁ : ℝ) : ℂ) (ftRootPoly c a).roots := by
    rw [hM, Shields.rootsIn, Multiset.count_filter, if_pos]
    simpa [Complex.dist_eq, sub_zero, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hx₁] using hR
  rw [← hcount, hfil, Polynomial.count_roots, hmult]

/-- **The pencil has exactly `ρ` zeros in the disk, for every parameter of the
window.**  Rouché at the circle, whose hypothesis is the floor of
`ftSepFloor_le_norm_eval` against the window's `‖z‖‖t‖^r`. -/
theorem card_rootsIn_ftDen {n : ℕ} {c : ℝ} {a : Fin n → ℝ} {x₁ : ℝ} {r ρ : ℕ}
    (hc : c ≠ 0) (ha : ∀ k, 0 < a k) (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    (hmult : (ftRootPoly c a).rootMultiplicity ((x₁ : ℝ) : ℂ) = ρ)
    {z : ℂ} (hz : ‖z‖ ≤ ftSepWindow c a x₁ r) :
    Multiset.card
        (Shields.rootsIn (ftDen (ftRootPoly c a) r z) 0 (ftSepRadius a x₁)) = ρ := by
  have hR : 0 < ftSepRadius a x₁ := ftSepRadius_pos hx₁ hmin
  have hfl : 0 < ftSepFloor c a x₁ := ftSepFloor_pos hc hmin
  have hlt : ∀ t ∈ Metric.sphere (0 : ℂ) (ftSepRadius a x₁),
      ‖(Polynomial.C z * Polynomial.X ^ r).eval t‖ < ‖(ftRootPoly c a).eval t‖ := by
    intro t htmem
    have ht : ‖t‖ = ftSepRadius a x₁ := by
      simpa [Complex.dist_eq, sub_zero] using Metric.mem_sphere.1 htmem
    have hQ := ftSepFloor_le_norm_eval (c := c) ha hmin ht
    have hzt : ‖(Polynomial.C z * Polynomial.X ^ r).eval t‖ ≤ ftSepFloor c a x₁ / 2 := by
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
        norm_mul, norm_pow, ht]
      calc ‖z‖ * ftSepRadius a x₁ ^ r
          ≤ ftSepWindow c a x₁ r * ftSepRadius a x₁ ^ r :=
            mul_le_mul_of_nonneg_right hz (by positivity)
        _ = ftSepFloor c a x₁ / 2 := by rw [ftSepWindow]; field_simp
    linarith
  have := Shields.card_rootsIn_add_eq (P := ftRootPoly c a)
    (Q := Polynomial.C z * Polynomial.X ^ r) (c := 0) hR hlt
  rw [ftDen, ← this]
  exact card_rootsIn_ftRootPoly hc ha hx₁ hmin hmult

/-- **`hsimple` and the completeness of a retained set, from the count.**  The
multiplicities of a polynomial's zeros in a disk sum to `N`; `N` distinct zeros
therefore each carry multiplicity exactly `1`, which is simplicity, and leave no
room for an `N+1`-st.

Stated at an arbitrary polynomial, radius and count, because **both endpoints
consume it and their disks are nothing alike**: below, the cluster collapses to
`x_1` and the circle separates it from the rest of the spectrum; above, the
cluster collapses to the *origin* and the circle sits inside the smallest zero of
`Q`, with the pencil's own term dominant rather than negligible.  What they share
is only this counting argument.

This is the only place an argument-principle count is needed: `PrincipalSimple`
settles simplicity off the real axis unconditionally, but a cluster of odd
multiplicity carries a real member, and there the count is the argument. -/
theorem simple_and_complete_of_count {P : Polynomial ℂ} (hP : P ≠ 0) {R : ℝ} {N : ℕ}
    (hcount : Multiset.card (Shields.rootsIn P 0 R) = N)
    (hsphere : ∀ t : ℂ, ‖t‖ = R → P.eval t ≠ 0)
    {T : Finset ℂ} (hTcard : T.card = N)
    (hT : ∀ w ∈ T, P.eval w = 0 ∧ ‖w‖ < R) :
    (∀ w ∈ T, (Polynomial.derivative P).eval w ≠ 0)
      ∧ (∀ w : ℂ, ‖w‖ ≤ R → P.eval w = 0 → w ∈ T) := by
  classical
  set M := Shields.rootsIn P 0 R with hMdef
  have hMcard : Multiset.card M = N := hcount
  -- membership in the multiset, for a zero strictly inside
  have hmem : ∀ w : ℂ, P.eval w = 0 → ‖w‖ < R → w ∈ M.toFinset := by
    intro w hw0 hwR
    rw [Multiset.mem_toFinset, hMdef, Shields.mem_rootsIn]
    exact ⟨Polynomial.mem_roots'.2 ⟨hP, hw0⟩, by
      simpa [Complex.dist_eq, sub_zero] using hwR⟩
  have hsub : T ⊆ M.toFinset := fun w hw => hmem w (hT w hw).1 (hT w hw).2
  have hpos : ∀ w ∈ M.toFinset, 1 ≤ Multiset.count w M := fun w hw =>
    Multiset.one_le_count_iff_mem.2 (Multiset.mem_toFinset.1 hw)
  have htotal : ∑ w ∈ M.toFinset, Multiset.count w M = N := by
    rw [Multiset.toFinset_sum_count_eq, hMcard]
  have hTsum : ∑ w ∈ T, Multiset.count w M ≤ N := by
    rw [← htotal]; exact Finset.sum_le_sum_of_subset hsub
  have hTge : ∑ w ∈ T, 1 ≤ ∑ w ∈ T, Multiset.count w M :=
    Finset.sum_le_sum fun w hw => hpos w (hsub hw)
  have hTone : ∀ w ∈ T, Multiset.count w M = 1 := by
    have heq : ∑ w ∈ T, (1 : ℕ) = ∑ w ∈ T, Multiset.count w M := by
      have h1 : ∑ w ∈ T, (1 : ℕ) = N := by
        rw [Finset.sum_const, smul_eq_mul, mul_one, hTcard]
      omega
    intro w hw
    exact ((Finset.sum_eq_sum_iff_of_le fun i hi => hpos i (hsub hi)).1 heq w hw).symm
  -- multiplicity one is simplicity
  refine ⟨fun w hw hderiv => ?_, fun w hwR hw0 => ?_⟩
  · have hcnt : Multiset.count w P.roots = 1 := by
      have hfil : Multiset.count w M = Multiset.count w P.roots := by
        rw [hMdef, Shields.rootsIn, Multiset.count_filter, if_pos]
        simpa [Complex.dist_eq, sub_zero] using (hT w hw).2
      rw [← hfil]; exact hTone w hw
    rw [Polynomial.count_roots] at hcnt
    have hgt : 1 < P.rootMultiplicity w :=
      (Polynomial.one_lt_rootMultiplicity_iff_isRoot hP).2 ⟨(hT w hw).1, hderiv⟩
    omega
  · -- no room for another zero
    by_contra hnot
    have hwlt : ‖w‖ < R := by
      refine lt_of_le_of_ne hwR fun hEq => ?_
      exact hsphere w hEq hw0
    have hins : insert w T ⊆ M.toFinset := by
      intro v hv
      rcases Finset.mem_insert.1 hv with rfl | hv
      · exact hmem v hw0 hwlt
      · exact hsub hv
    have hbig : ∑ v ∈ insert w T, Multiset.count v M ≤ N := by
      rw [← htotal]; exact Finset.sum_le_sum_of_subset hins
    rw [Finset.sum_insert hnot] at hbig
    have hTsumeq : ∑ v ∈ T, Multiset.count v M = N := by
      have := Finset.sum_congr rfl hTone
      rw [this, Finset.sum_const, smul_eq_mul, mul_one, hTcard]
    have hw1 : 1 ≤ Multiset.count w M := hpos w (hmem w hw0 hwlt)
    omega


/-- `simple_and_complete_of_count` at the lower endpoint's own circle and count. -/
theorem simple_and_complete_of_card {n : ℕ} {c : ℝ} {a : Fin n → ℝ} {x₁ : ℝ} {r ρ : ℕ}
    (hc : c ≠ 0) (ha : ∀ k, 0 < a k) (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    (hmult : (ftRootPoly c a).rootMultiplicity ((x₁ : ℝ) : ℂ) = ρ)
    {z : ℂ} (hz : ‖z‖ ≤ ftSepWindow c a x₁ r)
    {T : Finset ℂ} (hTcard : T.card = ρ)
    (hT : ∀ w ∈ T, (ftDen (ftRootPoly c a) r z).eval w = 0 ∧ ‖w‖ < ftSepRadius a x₁) :
    (∀ w ∈ T, (Polynomial.derivative (ftDen (ftRootPoly c a) r z)).eval w ≠ 0)
      ∧ (∀ w : ℂ, ‖w‖ ≤ ftSepRadius a x₁ →
          (ftDen (ftRootPoly c a) r z).eval w = 0 → w ∈ T) :=
  simple_and_complete_of_count (ftDen_ne_zero_of_window hc ha hx₁ hmin hz)
    (card_rootsIn_ftDen hc ha hx₁ hmin hmult hz)
    (fun _ ht => eval_ftDen_ne_zero_on_sphere hc ha hx₁ hmin hz ht) hTcard hT

/-! ### The upper endpoint: the same counting, the opposite circle

At the upper endpoint the cluster does not collapse to a zero of `Q`.  The branch
radius tends to `0` for `r ≥ 2` and the normalized roots tend to the `r`th roots of
`-1`, so the cluster collapses to the **origin**, and the spectral parameter runs
to infinity rather than to `0`.

So the separating circle is inside the smallest zero rather than outside it, and
the domination on it runs the other way: `z t^r` is the large term and `Q` the
small one.  Nothing above is reusable — `ftSepRadius` is built from the spectrum
around `x_1` and `ftSepFloor` bounds `|Q|` from **below** — and what the two
endpoints share is only `simple_and_complete_of_count`.

**Scope: this is the `r ≥ 2` picture, and at `r = 1` its hypothesis cannot be
met.**  Every statement below is conditioned on `ftUpperWindow ≤ ‖z‖`, and at
`r = 1` the upper endpoint is *finite*: the branch radius tends to a positive
limit and the spectral parameter to a finite one, so `‖z‖` is bounded and no
threshold is ever cleared.  A caller at `r = 1` cannot discharge the hypothesis,
which is the honest outcome — the alternative, a construction stated for all `r`
and usable at none of `r = 1`, would build green and be vacuous there.

At `r = 1` the upper endpoint is a different object again: `b = π`, and the
principal point `τe^{iθ}` and the arc point `τe^{-iθ}` *collide* on the negative
real axis as `θ ↑ π`.  There is no cluster to count — the manuscript's `n_1 = r-2`
is `0` — and what a circle is needed for is the pair alone.  That construction is
not here.  `scripts/check_upper_endpoint_regimes.py` measures the half the
hypothesis rests on — `|z|` clearing every threshold at `r ≥ 2` and bounded at
`r = 1` — and `scripts/check_upper_endpoint_r_one.py` the radius half.
-/

/-- The upper separating radius: half the smallest zero, so the circle sits inside
the whole spectrum. -/
noncomputable def ftUpperRadius (x₁ : ℝ) : ℝ := x₁ / 2

theorem ftUpperRadius_pos {x₁ : ℝ} (hx₁ : 0 < x₁) : 0 < ftUpperRadius x₁ := by
  rw [ftUpperRadius]; linarith

/-- The ceiling `|Q|` obeys on that circle: `|a_k - t| ≤ a_k + R_1`. -/
noncomputable def ftUpperCeil {n : ℕ} (c : ℝ) (a : Fin n → ℝ) (x₁ : ℝ) : ℝ :=
  |c| * ∏ k, (a k + ftUpperRadius x₁)

theorem ftUpperCeil_pos {n : ℕ} {c : ℝ} {a : Fin n → ℝ} {x₁ : ℝ} (hc : c ≠ 0)
    (ha : ∀ k, 0 < a k) (hx₁ : 0 < x₁) : 0 < ftUpperCeil c a x₁ :=
  mul_pos (abs_pos.2 hc)
    (Finset.prod_pos fun k _ => by
      have := ftUpperRadius_pos hx₁
      have := ha k
      linarith)

/-- **The ceiling, on the circle.**  As explicit as the lower endpoint's floor, and
by the same triangle inequality read the other way. -/
theorem norm_eval_ftRootPoly_le {n : ℕ} {c : ℝ} {a : Fin n → ℝ} {x₁ : ℝ}
    (ha : ∀ k, 0 < a k) {t : ℂ} (ht : ‖t‖ = ftUpperRadius x₁) :
    ‖(ftRootPoly c a).eval t‖ ≤ ftUpperCeil c a x₁ := by
  rw [eval_ftRootPoly, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_prod, ftUpperCeil]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg c)
  refine Finset.prod_le_prod (fun k _ => norm_nonneg _) fun k _ => ?_
  calc ‖((a k : ℝ) : ℂ) - t‖ ≤ ‖((a k : ℝ) : ℂ)‖ + ‖t‖ := norm_sub_le _ _
    _ = a k + ftUpperRadius x₁ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (ha k), ht]

/-- The window on the spectral parameter beyond which the pencil's own term
dominates: twice the ceiling, divided by `R_1^r`. -/
noncomputable def ftUpperWindow {n : ℕ} (c : ℝ) (a : Fin n → ℝ) (x₁ : ℝ) (r : ℕ) : ℝ :=
  2 * ftUpperCeil c a x₁ / ftUpperRadius x₁ ^ r

/-- **The pencil's floor on the upper circle**, from the domination the other way:
`‖D‖ ≥ ‖z t^r‖ - ‖Q‖ ≥ 2C - C`. -/
theorem ftUpperWindow_pos {n : ℕ} {c : ℝ} {a : Fin n → ℝ} {x₁ : ℝ} {r : ℕ} (hc : c ≠ 0)
    (ha : ∀ k, 0 < a k) (hx₁ : 0 < x₁) : 0 < ftUpperWindow c a x₁ r := by
  refine div_pos (by linarith [ftUpperCeil_pos hc ha hx₁]) ?_
  have := ftUpperRadius_pos hx₁
  positivity

theorem norm_eval_ftDen_ge_upper {n : ℕ} {c : ℝ} {a : Fin n → ℝ} {x₁ : ℝ} {r : ℕ}
    (ha : ∀ k, 0 < a k) (hx₁ : 0 < x₁) {z : ℂ} (hz : ftUpperWindow c a x₁ r ≤ ‖z‖)
    {t : ℂ} (ht : ‖t‖ = ftUpperRadius x₁) :
    ftUpperCeil c a x₁ ≤ ‖(ftDen (ftRootPoly c a) r z).eval t‖ := by
  have hR : 0 < ftUpperRadius x₁ := ftUpperRadius_pos hx₁
  have hQ := norm_eval_ftRootPoly_le (c := c) ha ht
  have hzt : 2 * ftUpperCeil c a x₁ ≤ ‖z * t ^ r‖ := by
    rw [norm_mul, norm_pow, ht]
    calc 2 * ftUpperCeil c a x₁
        = ftUpperWindow c a x₁ r * ftUpperRadius x₁ ^ r := by
          rw [ftUpperWindow]; field_simp
      _ ≤ ‖z‖ * ftUpperRadius x₁ ^ r :=
          mul_le_mul_of_nonneg_right hz (by positivity)
  rw [ftDen_eval]
  have hsplit := norm_sub_norm_le (z * t ^ r) (-(ftRootPoly c a).eval t)
  rw [sub_neg_eq_add, norm_neg] at hsplit
  rw [add_comm]
  linarith

theorem eval_ftDen_ne_zero_on_upper_sphere {n : ℕ} {c : ℝ} {a : Fin n → ℝ} {x₁ : ℝ} {r : ℕ}
    (hc : c ≠ 0) (ha : ∀ k, 0 < a k) (hx₁ : 0 < x₁)
    {z : ℂ} (hz : ftUpperWindow c a x₁ r ≤ ‖z‖)
    {t : ℂ} (ht : ‖t‖ = ftUpperRadius x₁) :
    (ftDen (ftRootPoly c a) r z).eval t ≠ 0 := by
  intro h0
  have hb := norm_eval_ftDen_ge_upper ha hx₁ hz ht
  rw [h0, norm_zero] at hb
  exact absurd hb (not_le.2 (ftUpperCeil_pos hc ha hx₁))

theorem ftDen_ne_zero_of_upper_window {n : ℕ} {c : ℝ} {a : Fin n → ℝ} {x₁ : ℝ} {r : ℕ}
    (hc : c ≠ 0) (ha : ∀ k, 0 < a k) (hx₁ : 0 < x₁)
    {z : ℂ} (hz : ftUpperWindow c a x₁ r ≤ ‖z‖) :
    ftDen (ftRootPoly c a) r z ≠ 0 := by
  intro h0
  have ht : ‖((ftUpperRadius x₁ : ℝ) : ℂ)‖ = ftUpperRadius x₁ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (ftUpperRadius_pos hx₁)]
  exact eval_ftDen_ne_zero_on_upper_sphere hc ha hx₁ hz ht (by rw [h0]; simp)

/-- **The pencil has exactly `r` zeros inside the upper circle.**  Rouché against
`z X^r`, whose `r` zeros all sit at the origin — the mirror of
`card_rootsIn_ftDen`, with the roles of the two terms exchanged. -/
theorem card_rootsIn_ftDen_upper {n : ℕ} {c : ℝ} {a : Fin n → ℝ} {x₁ : ℝ} {r : ℕ}
    (hr : 1 ≤ r) (hc : c ≠ 0) (ha : ∀ k, 0 < a k) (hx₁ : 0 < x₁)
    {z : ℂ} (hz : ftUpperWindow c a x₁ r ≤ ‖z‖) (hzne : z ≠ 0) :
    Multiset.card
        (Shields.rootsIn (ftDen (ftRootPoly c a) r z) 0 (ftUpperRadius x₁)) = r := by
  classical
  have hR : 0 < ftUpperRadius x₁ := ftUpperRadius_pos hx₁
  have hlt : ∀ t ∈ Metric.sphere (0 : ℂ) (ftUpperRadius x₁),
      ‖(ftRootPoly c a).eval t‖ < ‖(Polynomial.C z * Polynomial.X ^ r).eval t‖ := by
    intro t htmem
    have ht : ‖t‖ = ftUpperRadius x₁ := by
      simpa [Complex.dist_eq, sub_zero] using Metric.mem_sphere.1 htmem
    have hQ := norm_eval_ftRootPoly_le (c := c) ha ht
    have hzt : 2 * ftUpperCeil c a x₁
        ≤ ‖(Polynomial.C z * Polynomial.X ^ r).eval t‖ := by
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
        Polynomial.eval_X, norm_mul, norm_pow, ht]
      calc 2 * ftUpperCeil c a x₁
          = ftUpperWindow c a x₁ r * ftUpperRadius x₁ ^ r := by
            rw [ftUpperWindow]; field_simp
        _ ≤ ‖z‖ * ftUpperRadius x₁ ^ r :=
            mul_le_mul_of_nonneg_right hz (by positivity)
    have hCpos : 0 < ftUpperCeil c a x₁ := ftUpperCeil_pos hc ha hx₁
    linarith
  have hrou := Shields.card_rootsIn_add_eq (P := Polynomial.C z * Polynomial.X ^ r)
    (Q := ftRootPoly c a) (c := 0) hR hlt
  have hsame : Polynomial.C z * Polynomial.X ^ r + ftRootPoly c a
      = ftDen (ftRootPoly c a) r z := by rw [ftDen]; ring
  rw [hsame] at hrou
  rw [← hrou]
  -- the roots of `z X^r` are `r` copies of the origin, all inside
  have hmem0 : ∀ w ∈ (Polynomial.C z * Polynomial.X ^ r).roots, w = 0 := by
    intro w hw
    have h2 := (Polynomial.mem_roots'.1 hw).2
    simp only [Polynomial.IsRoot.def, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, mul_eq_zero,
      pow_eq_zero_iff (by omega : r ≠ 0)] at h2
    rcases h2 with h | h
    · exact absurd h hzne
    · exact h
  rw [Shields.rootsIn,
    Multiset.filter_eq_self.2 (fun w hw => by rw [hmem0 w hw]; simpa using hR),
    Polynomial.roots_C_mul _ hzne, Polynomial.roots_pow, Polynomial.roots_X,
    Multiset.card_nsmul, Multiset.card_singleton, mul_one]

/-! ### Simplicity at the upper endpoint, without a count

The lower endpoint needed an argument-principle count to know its zeros were
simple, because a cluster of odd multiplicity carries a real member and
`PrincipalSimple` reaches only the ones off the axis.  The upper endpoint does
not, and the reason is the pencil's own invariant.

`ftCritical_ftDen` says `E = XD' - rD` does not depend on the spectral parameter:
`E(·, z) = XQ' - rQ` for every `z`.  At a zero `t_0 ≠ 0` of `D` this reads
`t_0 D'(t_0) = E(t_0)`, so **the multiple zeros of the whole pencil, at every
parameter at once, are the zeros of one fixed polynomial**.  And `E(0) = -rQ(0)`
is nonzero, so a disk about the origin small enough to miss the zeros of `E`
carries only simple zeros of `D` — uniformly in `z`, with nothing counted and no
chart built.

The upper cluster collapses to the origin, which is exactly where this applies.

**Why the lower endpoint cannot use it, and where it could.**  There the cluster
collapses to `x_1`, and `E(x_1) = x_1Q'(x_1) - rQ(x_1)`.  At multiplicity `ρ ≥ 2`
both `Q` and `Q'` vanish at `x_1`, so `E(x_1) = 0` and no disk about `x_1` is
`E`-free — the collapse point is itself a multiple zero of the pencil at the limit
parameter, which is what the count is for.  At `ρ = 1` the same expression is
`x_1Q'(x_1) ≠ 0`, so the argument does apply there; that is the case
`EndpointBranch`'s chart route was built for, and it is cheaper by this one.
-/

/-- **The pencil's multiple zeros are the zeros of `E`, at every parameter.**
`ftCritical_ftDen` makes `E` parameter-free, so this one identity governs
simplicity across the whole pencil. -/
theorem eval_derivative_ftDen_mul {Q : Polynomial ℂ} {r : ℕ} (hr : 1 ≤ r) {z t : ℂ}
    (ht : (ftDen Q r z).eval t = 0) :
    t * (Polynomial.derivative (ftDen Q r z)).eval t = (ftCritical Q r).eval t := by
  have h : (ftCritical (ftDen Q r z) r).eval t = (ftCritical Q r).eval t := by
    rw [ftCritical_ftDen Q hr z]
  rw [eval_ftCritical (ftDen Q r z) r t, ht, mul_zero, sub_zero] at h
  exact h

/-- **A zero of the pencil off the zeros of `E` is simple.**  Uniform in the
spectral parameter, because `E` is.  No hypothesis `t ≠ 0` is needed: the identity
gives `E(0) = 0` at a vanishing derivative there, and `E(0) = -rQ(0)`. -/
theorem eval_derivative_ftDen_ne_zero_of_ftCritical {Q : Polynomial ℂ} {r : ℕ}
    (hr : 1 ≤ r) {z t : ℂ} (ht : (ftDen Q r z).eval t = 0)
    (hE : (ftCritical Q r).eval t ≠ 0) :
    (Polynomial.derivative (ftDen Q r z)).eval t ≠ 0 := by
  intro h0
  rw [← eval_derivative_ftDen_mul hr ht, h0, mul_zero] at hE
  exact hE rfl

/-- `E(0) = -rQ(0)`, which is nonzero once `r ≥ 1` and `0` is not a zero of `Q`.
This is what puts the origin — where the upper cluster collapses — strictly
inside the region where every zero of the pencil is simple. -/
theorem eval_ftCritical_zero_ne_zero {Q : Polynomial ℂ} {r : ℕ} (hr : 1 ≤ r)
    (hQ0 : Q.eval 0 ≠ 0) : (ftCritical Q r).eval 0 ≠ 0 := by
  rw [eval_ftCritical, zero_mul, zero_sub, neg_ne_zero]
  exact mul_ne_zero (by exact_mod_cast (by omega : r ≠ 0)) hQ0

/-- **A radius about the origin on which the whole pencil has only simple zeros.**
`E` is continuous and nonzero at `0`, so it is nonzero on a closed disk; every
zero of `D(·,z)` in that disk is then simple for every `z`, and the origin itself
is not a zero because `D(0,z) = Q(0)`. -/
theorem exists_simple_radius {Q : Polynomial ℂ} {r : ℕ} (hr : 1 ≤ r)
    (hQ0 : Q.eval 0 ≠ 0) :
    ∃ R > (0 : ℝ), ∀ z t : ℂ, ‖t‖ ≤ R → (ftDen Q r z).eval t = 0 →
      (Polynomial.derivative (ftDen Q r z)).eval t ≠ 0 := by
  have hE0 : (ftCritical Q r).eval 0 ≠ 0 := eval_ftCritical_zero_ne_zero hr hQ0
  have hcont : ContinuousAt (fun t : ℂ => (ftCritical Q r).eval t) 0 :=
    (ftCritical Q r).continuous_aeval.continuousAt
  obtain ⟨u, hu, hball⟩ := Metric.eventually_nhds_iff.mp (hcont.eventually_ne hE0)
  refine ⟨u / 2, by linarith, fun z t htR ht0 => ?_⟩
  refine eval_derivative_ftDen_ne_zero_of_ftCritical hr ht0 (hball ?_)
  rw [Complex.dist_eq, sub_zero]
  linarith

/-! ### The retained set at an arbitrary circle

`diskRoots` is a Finset of *points* while `Shields.rootsIn` is a multiset carrying
multiplicity, so their cardinalities agree exactly when every zero in the disk is
simple.  At the upper endpoint that is `exists_simple_radius`, so the count `r`
transfers to the set without a chart; at the lower endpoint simplicity is itself
the count's output, so the transfer runs the other way.
-/

/-- `haR`, at any circle the pencil does not meet. -/
theorem norm_lt_of_mem_diskRoots_of_sphere {P : Polynomial ℂ} (hP : P ≠ 0) {R : ℝ}
    (hsphere : ∀ t : ℂ, ‖t‖ = R → P.eval t ≠ 0) {t : ℂ} (ht : t ∈ diskRoots P R) :
    ‖t‖ < R := by
  obtain ⟨ht0, htR⟩ := (mem_diskRoots hP).1 ht
  exact lt_of_le_of_ne htR fun hEq => hsphere t hEq ht0

/-- **The set and the multiset agree when the zeros are simple.**  Each zero is
listed once, so the number of *points* in the disk is the number of zeros counted
with multiplicity. -/
theorem card_diskRoots_eq_card_rootsIn {P : Polynomial ℂ} (hP : P ≠ 0) {R : ℝ}
    (hsphere : ∀ t : ℂ, ‖t‖ = R → P.eval t ≠ 0)
    (hsimple : ∀ t : ℂ, ‖t‖ ≤ R → P.eval t = 0 →
      (Polynomial.derivative P).eval t ≠ 0) :
    (diskRoots P R).card = Multiset.card (Shields.rootsIn P 0 R) := by
  classical
  set M := Shields.rootsIn P 0 R with hMdef
  have hmemM : ∀ w : ℂ, w ∈ M ↔ P.eval w = 0 ∧ ‖w‖ < R := by
    intro w
    rw [hMdef, Shields.mem_rootsIn, Polynomial.mem_roots']
    constructor
    · rintro ⟨⟨_, hw⟩, hb⟩
      exact ⟨hw, by simpa [Complex.dist_eq, sub_zero] using Metric.mem_ball.1 hb⟩
    · rintro ⟨hw, hb⟩
      exact ⟨⟨hP, hw⟩, by simpa [Complex.dist_eq, sub_zero] using hb⟩
  -- every zero in the disk is listed exactly once
  have hnodup : M.Nodup := by
    refine Multiset.nodup_iff_count_le_one.2 fun w => ?_
    by_cases hw : w ∈ M
    · obtain ⟨hw0, hwR⟩ := (hmemM w).1 hw
      have hcnt : Multiset.count w M = Multiset.count w P.roots := by
        rw [hMdef, Shields.rootsIn, Multiset.count_filter, if_pos]
        simpa [Complex.dist_eq, sub_zero] using hwR
      rw [hcnt, Polynomial.count_roots]
      by_contra hgt
      have h2 : 1 < P.rootMultiplicity w := by omega
      exact hsimple w hwR.le hw0
        ((Polynomial.one_lt_rootMultiplicity_iff_isRoot hP).1 h2).2
    · simp [Multiset.count_eq_zero_of_notMem hw]
  rw [← Multiset.toFinset_card_of_nodup hnodup]
  congr 1
  ext w
  rw [Multiset.mem_toFinset, hmemM w, mem_diskRoots hP]
  exact ⟨fun h => ⟨h.1, lt_of_le_of_ne h.2 fun hEq => hsphere w hEq h.1⟩,
    fun h => ⟨h.1, h.2.le⟩⟩

end ForgacsTran
