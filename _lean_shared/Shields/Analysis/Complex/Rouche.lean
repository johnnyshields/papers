/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Shields.Analysis.Complex.ArgumentPrinciple.Analytic

/-!
# Rouché's theorem for analytic functions

Mathlib has the argument principle for meromorphic functions but no Rouché, and the
counting form Rouché needs is a statement about a *displayed* factorization rather than
about a divisor: `Shields.FactoredOn F c R n a G` says `F z = (∏_{j<n} (z - a j)) * G z`
at every `z`, with `G` analytic and nowhere zero on the closed disc and every `a j`
strictly inside.  Every `F` analytic on the disc and nonvanishing on its boundary admits
one (`Shields.exists_factoredOn`), the `n` it displays is the number of zeros with
multiplicity, and the counting integral of `F' / F` reads it off.

## Main results

* `Shields.argumentPrinciple` — a contour integral agreeing on the circle with
  `∑_j (z - a j)⁻¹ + G' / G` is `2πi` times the number of listed points.  The cofactor
  contributes nothing because its logarithmic derivative is analytic on the disc, and each
  listed point contributes one full turn.
* `Shields.circleIntegral_logDeriv_eq_of_factoredOn` — that hypothesis discharged from a
  factorization, which is the form the homotopy consumes.
* `Shields.exists_factoredOn` — every analytic `F` nonvanishing on the circle factors.
  The zeros are divided out with `dslope` rather than locally, which is what keeps the
  cofactor analytic on the whole disc instead of near one point.
* `Shields.rouche` — **Rouché**, unconditionally: with `‖g‖ < ‖f‖` on the circle, any
  factorization of `f` and any factorization of `f + g` display the same `n`.  Neither
  count is assumed, and neither is assumed to exist.
* `Shields.factoredOn_of_norm_lt` — Rouché one-sidedly: a factorization of `f` transfers
  to `f + g` with the same count, no factorization of `f + g` assumed.
* `Shields.rouche_of_analytic` — the two factorizations exhibited, for a caller that wants
  the roots rather than the number.

## Implementation notes

The homotopy `f + t·g` is run at the level of the counting *integral*, not of the count:
the boundary hypothesis makes every member of the family factor, so the integral is
`2πi` times an integer at every `t`, it is continuous in `t`, and a continuous integer is
constant.  This avoids having to produce a continuous selection of the roots.

`Shields.exists_factoredOn_aux` runs the same peel-one-zero induction as
`Shields.exists_zeroFactor_aux`, over `n : ℕ` and `a : ℕ → ℂ` rather than over a `Multiset ℂ`.
The two indexings are kept because they are what different consumers hold: a caller with a root
list indexed by `Finset.range n` and one with a multiset of roots each read the count off the
presentation it already has, and translating either way costs an enumeration lemma.

`Shields.factoredOn_sq` and `Shields.exists_factoredOn_sq_sub` are non-vacuity witnesses:
the first shows the count is multiplicity rather than cardinality, the second that Rouché
transports it.

## Papers depending on this file

* `edrei-spectral-classification`, `exterior-sinc-hierarchies`, `hard-edge-edrei`,
  `forgacs-tran-numerators` — zero counting on a disc.
-/

open Complex Finset

namespace Shields


/-- **The poles contribute `2πi` each.**  For finitely many points `a_j` inside the
circle, `∮ ∑_j (z - a_j)⁻¹ = 2πi · #s`.

This is the zero-counting half of the argument principle: the sum is the
logarithmic derivative of `∏_j (z - a_j)`, and each simple pole is worth one full
turn. -/
theorem circleIntegral_sum_sub_inv {c : ℂ} {R : ℝ} (hR : 0 < R)
    (s : Finset ℕ) (a : ℕ → ℂ) (ha : ∀ j ∈ s, a j ∈ Metric.ball c R) :
    (∮ z in C(c, R), ∑ j ∈ s, (z - a j)⁻¹) = s.card * (2 * Real.pi * I) := by
  have hns : ∀ j ∈ s, a j ∉ Metric.sphere c |R| := by
    intro j hj hmem
    rw [Metric.mem_sphere, abs_of_pos hR] at hmem
    exact absurd hmem (ne_of_lt (Metric.mem_ball.mp (ha j hj)))
  rw [circleIntegral.integral_fun_sum
    (fun j hj => circleIntegrable_sub_inv_iff.2 (Or.inr (hns j hj)))]
  rw [Finset.sum_congr rfl fun j hj => circleIntegral.integral_sub_inv_of_mem_ball (ha j hj)]
  simp [Finset.sum_const, nsmul_eq_mul]

/-- **The argument principle, factored form.**  If the logarithmic derivative of
`f` splits as `∑_j (z - a_j)⁻¹ + g'/g` on the circle, with the `a_j` inside and `g`
analytic and zero-free on the closed disk, then
\[
  \oint_{|z-c|=R}\frac{f'}{f} = 2\pi i\,\#s .
\]
The contour integral counts the zeros. -/
theorem argumentPrinciple {c : ℂ} {R : ℝ} (hR : 0 < R) (s : Finset ℕ) (a : ℕ → ℂ)
    (g F : ℂ → ℂ) (ha : ∀ j ∈ s, a j ∈ Metric.ball c R)
    (hg : AnalyticOnNhd ℂ g (Metric.closedBall c R))
    (hgne : ∀ z ∈ Metric.closedBall c R, g z ≠ 0)
    (hsplit : Set.EqOn F (fun z => (∑ j ∈ s, (z - a j)⁻¹) + deriv g z / g z)
      (Metric.sphere c R))
    (hint₁ : CircleIntegrable (fun z => ∑ j ∈ s, (z - a j)⁻¹) c R)
    (hint₂ : CircleIntegrable (fun z => deriv g z / g z) c R) :
    (∮ z in C(c, R), F z) = s.card * (2 * Real.pi * I) := by
  rw [circleIntegral.integral_congr (le_of_lt hR) hsplit,
    circleIntegral.integral_add hint₁ hint₂,
    circleIntegral_sum_sub_inv hR s a ha,
    circleIntegral_logDeriv_eq_zero (le_of_lt hR) g hg hgne, add_zero]

/-! ### Dividing the zeros out

Mathlib factors a zero out of an analytic function only locally: the `g` of
`AnalyticAt.analyticOrderAt_eq_natCast` is analytic *at* `z₀`, and the identity it
satisfies holds on a neighborhood of `z₀`.  `dslope` does better.  It is the
difference quotient `(F u - F w)/(u - w)`, filled in at `u = w` by `deriv F w`; it
is analytic wherever `F` is, and `(z - w) • dslope F w z = F z` at *every* `z` once
`F w = 0`.  Iterating it divides out a zero with its full multiplicity and leaves
a function analytic on the same set as `F`.

That division is `Shields.exists_pow_factor`, in
`Shields.Analysis.Complex.ArgumentPrinciple.Analytic`, and the two `dslope` lemmas it rests on
are `analyticAt_dslope` and `analyticOnNhd_iterate_dslope` in the same module: neither needs `U`
open, so all three serve the closed-disc factorization here and the argument-principle route
there. -/

/-- **A closed-disk factorization.**  `F z = (∏_{j<n}(z - a_j))·G z` at every point
of the plane, with each `a_j` strictly inside the circle and `G` analytic and
zero-free on the closed disk.

The `a_j` are then exactly the zeros of `F` in the closed disk, listed with
multiplicity — the product is itself the multiplicity statement — so `n` is the
number of zeros the argument principle counts. -/
structure FactoredOn (F : ℂ → ℂ) (c : ℂ) (R : ℝ) (n : ℕ) (a : ℕ → ℂ) (G : ℂ → ℂ) : Prop where
  /-- Every displayed root lies strictly inside the circle. -/
  mem_ball : ∀ j < n, a j ∈ Metric.ball c R
  /-- The cofactor is analytic on the closed disk. -/
  analytic : AnalyticOnNhd ℂ G (Metric.closedBall c R)
  /-- The cofactor has no zero on the closed disk. -/
  ne_zero : ∀ z ∈ Metric.closedBall c R, G z ≠ 0
  /-- The factorization, valid at every point of the plane. -/
  eq : ∀ z, F z = (∏ j ∈ Finset.range n, (z - a j)) * G z

/-- The displayed roots are the zeros: nothing else in the closed disk vanishes,
and every `a_j` does. -/
theorem FactoredOn.eq_zero_iff {F : ℂ → ℂ} {c : ℂ} {R : ℝ} {n : ℕ} {a : ℕ → ℂ} {G : ℂ → ℂ}
    (h : FactoredOn F c R n a G) {z : ℂ} (hz : z ∈ Metric.closedBall c R) :
    F z = 0 ↔ ∃ j < n, a j = z := by
  rw [h.eq z, mul_eq_zero, Finset.prod_eq_zero_iff]
  simp [h.ne_zero z hz, sub_eq_zero, eq_comm]

/-- A factorization transfers along a pointwise identity of functions: `FactoredOn.eq` holds at
every point of the plane, so equal functions factor alike. -/
theorem FactoredOn.congr {F F' : ℂ → ℂ} {c : ℂ} {R : ℝ} {n : ℕ} {a : ℕ → ℂ} {G : ℂ → ℂ}
    (h : FactoredOn F c R n a G) (heq : ∀ z, F' z = F z) : FactoredOn F' c R n a G :=
  ⟨h.mem_ball, h.analytic, h.ne_zero, fun z => (heq z).trans (h.eq z)⟩

/-- **No zeros, nothing displayed.**  With the zero set of the closed disk empty, `F` is its own
zero-free cofactor and the root list is the empty one. -/
theorem factoredOn_of_zeros_empty {c : ℂ} {R : ℝ} {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F (Metric.closedBall c R))
    (hempty : {z ∈ Metric.closedBall c R | F z = 0} = ∅) :
    FactoredOn F c R 0 (fun _ => 0) F :=
  ⟨by omega, hF, fun z hz hz0 => by
    have hmem : z ∈ {z ∈ Metric.closedBall c R | F z = 0} := ⟨hz, hz0⟩
    rw [hempty] at hmem
    exact hmem, by simp⟩

/-- Appending `k` copies of `w` to a root list multiplies the product by
`(z - w)^k`. -/
theorem prod_range_add_pow (n k : ℕ) (b : ℕ → ℂ) (w z : ℂ) :
    (∏ j ∈ Finset.range (n + k), (z - if j < n then b j else w))
      = (∏ j ∈ Finset.range n, (z - b j)) * (z - w) ^ k := by
  induction k with
  | zero =>
    simp only [Nat.add_zero, pow_zero, mul_one]
    exact Finset.prod_congr rfl fun j hj => by rw [if_pos (Finset.mem_range.mp hj)]
  | succ k ih =>
    rw [← Nat.add_assoc, Finset.prod_range_succ, ih, if_neg (by omega)]
    ring

/-- The recursion behind `exists_factoredOn`, with the number of *distinct* zeros
bounded in advance.  Each step divides out one zero with its full multiplicity, so
the bound drops by at least one. -/
theorem exists_factoredOn_aux {c : ℂ} {R : ℝ} (hR : 0 < R) :
    ∀ (m : ℕ) (F : ℂ → ℂ), AnalyticOnNhd ℂ F (Metric.closedBall c R) →
      (∀ z ∈ Metric.sphere c R, F z ≠ 0) →
      {z ∈ Metric.closedBall c R | F z = 0}.ncard ≤ m →
      ∃ (n : ℕ) (a : ℕ → ℂ) (G : ℂ → ℂ), FactoredOn F c R n a G := by
  intro m
  induction m with
  | zero =>
    intro F hF hne hcard
    have hfin := finite_zeros_of_ne_zero_on_sphere hR hF hne
    exact ⟨0, fun _ => 0, F,
      factoredOn_of_zeros_empty hF ((Set.ncard_eq_zero hfin).mp (Nat.le_zero.mp hcard))⟩
  | succ m ih =>
    intro F hF hne hcard
    have hfin := finite_zeros_of_ne_zero_on_sphere hR hF hne
    rcases Set.eq_empty_or_nonempty {z ∈ Metric.closedBall c R | F z = 0} with
      hempty | ⟨w, hw, hw0⟩
    · exact ⟨0, fun _ => 0, F, factoredOn_of_zeros_empty hF hempty⟩
    · have hwb : w ∈ Metric.ball c R := mem_ball_of_eq_zero hne hw hw0
      obtain ⟨k, H, hH, hHw, hFH⟩ := exists_pow_factor hF hw
        (not_eventually_eq_zero_of_ne_zero_on_sphere hR hF hne hw)
      have hHne : ∀ z ∈ Metric.sphere c R, H z ≠ 0 := by
        intro z hz hz0
        exact hne z hz (by rw [hFH z, hz0, mul_zero])
      have hsub : {z ∈ Metric.closedBall c R | H z = 0} ⊂
          {z ∈ Metric.closedBall c R | F z = 0} := by
        constructor
        · rintro z ⟨hz, hz0⟩
          exact ⟨hz, by rw [hFH z, hz0, mul_zero]⟩
        · intro hcon
          exact hHw (hcon ⟨hw, hw0⟩).2
      have hlt : {z ∈ Metric.closedBall c R | H z = 0}.ncard ≤ m := by
        have := Set.ncard_lt_ncard hsub hfin
        omega
      obtain ⟨n, b, G, hfac⟩ := ih H hH hHne hlt
      refine ⟨n + k, fun j => if j < n then b j else w, G,
        ⟨?_, hfac.analytic, hfac.ne_zero, ?_⟩⟩
      · intro j hj
        by_cases hjn : j < n
        · simpa [hjn] using hfac.mem_ball j hjn
        · simpa [hjn] using hwb
      · intro z
        rw [hFH z, hfac.eq z]
        simp only [prod_range_add_pow n k b w z]
        ring

/-- **Every function analytic on the closed disk and nonvanishing on its circle
factors.**  This is what makes the argument principle unconditional: the factored
presentation it consumes always exists. -/
theorem exists_factoredOn {c : ℂ} {R : ℝ} (hR : 0 < R) {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F (Metric.closedBall c R))
    (hne : ∀ z ∈ Metric.sphere c R, F z ≠ 0) :
    ∃ (n : ℕ) (a : ℕ → ℂ) (G : ℂ → ℂ), FactoredOn F c R n a G :=
  exists_factoredOn_aux hR _ F hF hne le_rfl

/-- **The argument principle for a factorization.**  `∮ F'/F = 2πi·n`, with `n` the
number of zeros of `F` inside the circle counted with multiplicity. -/
theorem circleIntegral_logDeriv_eq_of_factoredOn {c : ℂ} {R : ℝ} (hR : 0 < R) {F : ℂ → ℂ}
    {n : ℕ} {a : ℕ → ℂ} {G : ℂ → ℂ} (h : FactoredOn F c R n a G) :
    (∮ z in C(c, R), deriv F z / F z) = n * (2 * Real.pi * I) := by
  have hFeq : F = fun z => (∏ j ∈ Finset.range n, (z - a j)) * G z := funext h.eq
  have hsub : ∀ z ∈ Metric.sphere c R, ∀ j < n, z - a j ≠ 0 := by
    intro z hz j hj hzero
    rw [sub_eq_zero] at hzero
    rw [hzero] at hz
    exact absurd (Metric.mem_sphere.mp hz) (ne_of_lt (Metric.mem_ball.mp (h.mem_ball j hj)))
  have hsplit : Set.EqOn (fun z => deriv F z / F z)
      (fun z => (∑ j ∈ Finset.range n, (z - a j)⁻¹) + deriv G z / G z)
      (Metric.sphere c R) := fun z hz =>
    logDeriv_prod_sub_mul hFeq (fun j hj => hsub z hz j (Finset.mem_range.mp hj))
      (h.ne_zero z (Metric.sphere_subset_closedBall hz))
      ((h.analytic z (Metric.sphere_subset_closedBall hz)).differentiableAt)
  have hint₁ : CircleIntegrable (fun z => ∑ j ∈ Finset.range n, (z - a j)⁻¹) c R := by
    refine ContinuousOn.circleIntegrable hR.le (continuousOn_finsetSum _ fun j hj => ?_)
    exact (continuousOn_id.sub continuousOn_const).inv₀
      fun z hz => hsub z hz j (Finset.mem_range.mp hj)
  have hlog : AnalyticOnNhd ℂ (fun z => deriv G z / G z) (Metric.closedBall c R) :=
    fun z hz => (h.analytic.deriv z hz).div (h.analytic z hz) (h.ne_zero z hz)
  have hint₂ : CircleIntegrable (fun z => deriv G z / G z) c R :=
    (hlog.continuousOn.mono Metric.sphere_subset_closedBall).circleIntegrable hR.le
  simpa using argumentPrinciple hR (Finset.range n) a G (fun z => deriv F z / F z)
    (fun j hj => h.mem_ball j (Finset.mem_range.mp hj)) h.analytic h.ne_zero hsplit hint₁ hint₂

/-! ### Rouché

The count is *invariant* under a perturbation smaller on the boundary.  The
classical proof runs the count along `f + t·g` for `t ∈ [0,1]`: the boundary
hypothesis keeps every member zero-free on the circle, so every member factors and
its counting integral is `2πi` times a natural number; the integral moves
continuously in `t`; and a continuous integer cannot move at all. -/

/-- **The dominating function has no zero where it dominates.** -/
theorem ne_zero_of_norm_lt {c : ℂ} {R : ℝ} {f g : ℂ → ℂ}
    (hlt : ∀ z ∈ Metric.sphere c R, ‖g z‖ < ‖f z‖) {z : ℂ} (hz : z ∈ Metric.sphere c R) :
    f z ≠ 0 :=
  norm_ne_zero_iff.1 ((norm_nonneg (g z)).trans_lt (hlt z hz)).ne'

/-- **Nor does the perturbed function.**  This is `add_smul_ne_zero_of_norm_lt` at the far end of
the family, `t = 1`, with the radius resolved. -/
theorem add_ne_zero_of_norm_lt {c : ℂ} {R : ℝ} (hR : 0 < R) {f g : ℂ → ℂ}
    (hlt : ∀ z ∈ Metric.sphere c R, ‖g z‖ < ‖f z‖) {z : ℂ} (hz : z ∈ Metric.sphere c R) :
    f z + g z ≠ 0 := by
  have habs : |R| = R := abs_of_pos hR
  simpa using add_smul_ne_zero_of_norm_lt f g (by rwa [habs]) (t := 1)
    (Set.right_mem_Icc.mpr zero_le_one) (by rwa [habs])

theorem count_eq_of_continuous {c : ℂ} {R : ℝ} (f g : ℂ → ℂ) (N : ℝ → ℤ)
    (hN : ContinuousOn N (Set.Icc (0 : ℝ) 1))
    (hcount : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (∮ z in C(c, R), deriv (fun w => f w + (t : ℂ) * g w) z
          / (f z + (t : ℂ) * g z)) = (N t : ℂ) * (2 * Real.pi * I)) :
    (∮ z in C(c, R), deriv f z / f z)
      = (∮ z in C(c, R), deriv (fun w => f w + g w) z / (f z + g z)) := by
  have h0 := hcount 0 (by norm_num)
  have h1 := hcount 1 (by norm_num)
  simp only [Complex.ofReal_zero, Complex.ofReal_one, zero_mul, one_mul, add_zero] at h0 h1
  rw [h0, h1, int_eq_of_continuousOn_Icc N hN]

/-- The same, for a family jointly continuous on the whole plane. -/
theorem continuous_circleIntegral_param_uncurry {c : ℂ} {R : ℝ} (F : ℝ → ℂ → ℂ)
    (hF : Continuous (Function.uncurry F)) :
    Continuous fun t : ℝ => ∮ z in C(c, R), F t z :=
  continuous_circleIntegral_param F
    (hF.comp (continuous_fst.prodMk ((continuous_circleMap c R).comp continuous_snd)))

theorem circleIntegral_eq_of_int_count {c : ℂ} {R : ℝ} (Φ : ℝ → ℂ → ℂ) (N : ℝ → ℤ)
    (hcont : Continuous fun p : ℝ × ℝ => Φ p.1 (circleMap c R p.2))
    (hcount : ∀ t : ℝ,
      (∮ z in C(c, R), Φ t z) = (N t : ℂ) * (2 * Real.pi * I)) :
    (∮ z in C(c, R), Φ 0 z) = (∮ z in C(c, R), Φ 1 z) := by
  have hI : Continuous fun t : ℝ => ∮ z in C(c, R), Φ t z :=
    continuous_circleIntegral_param Φ hcont
  rw [hcount 0, hcount 1,
    int_eq_of_continuous_mul_two_pi_I (N := N) (by simpa only [hcount] using hI)]

/-- The deformation argument with the count supplied by hand.  `rouche_integral`
discharges the hypothesis; this is what remains once the counting integrals are
known to be integer multiples of `2πi`. -/
theorem circleIntegral_logDeriv_eq_of_count {c : ℂ} {R : ℝ} (f g : ℂ → ℂ) (N : ℝ → ℤ)
    (hcont : Continuous (Function.uncurry fun t : ℝ => fun z : ℂ =>
      deriv (fun w => f w + (t : ℂ) * g w) z / (f z + (t : ℂ) * g z)))
    (hcount : ∀ t : ℝ,
      (∮ z in C(c, R), deriv (fun w => f w + (t : ℂ) * g w) z / (f z + (t : ℂ) * g z))
        = (N t : ℂ) * (2 * Real.pi * I)) :
    (∮ z in C(c, R), deriv f z / f z)
      = (∮ z in C(c, R), deriv (fun w => f w + g w) z / (f z + g z)) := by
  have h := circleIntegral_eq_of_int_count
    (fun t z => deriv (fun w => f w + (t : ℂ) * g w) z / (f z + (t : ℂ) * g z)) N
    (hcont.comp (continuous_fst.prodMk ((continuous_circleMap c R).comp continuous_snd))) hcount
  simpa only [Complex.ofReal_zero, Complex.ofReal_one, zero_mul, one_mul, add_zero] using h

/-- **Rouché's theorem, integral form.**  If `‖g‖ < ‖f‖` on the circle and both are
analytic on the closed disk, the two counting integrals agree.  Nothing is assumed
about either count.

Each side is `2πi` times a zero count by the argument principle, and the two counts
agree by `Shields.zeroCount_add_eq`, which deforms `f` into `f + g` along a family the
boundary hypothesis keeps zero-free on the circle. -/
theorem rouche_integral {c : ℂ} {R : ℝ} (hR : 0 < R) {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall c R))
    (hg : AnalyticOnNhd ℂ g (Metric.closedBall c R))
    (hlt : ∀ z ∈ Metric.sphere c R, ‖g z‖ < ‖f z‖) :
    (∮ z in C(c, R), deriv f z / f z)
      = (∮ z in C(c, R), deriv (fun w => f w + g w) z / (f z + g z)) := by
  have hsum : AnalyticOnNhd ℂ (f + g) (Metric.closedBall c R) := fun z hz =>
    (hf z hz).add (hg z hz)
  have hsumne : ∀ z ∈ Metric.sphere c R, (f + g) z ≠ 0 := fun z hz =>
    add_ne_zero_of_norm_lt hR hlt hz
  have key : (∮ z in C(c, R), deriv (f + g) z / (f + g) z)
      = ((zeroCount f c R : ℕ) : ℂ) * (2 * Real.pi * I) := by
    rw [circleIntegral_logDeriv hR hsum hsumne, zeroCount_add_eq hR hf hg hlt]
  rw [circleIntegral_logDeriv hR hf fun z hz => ne_zero_of_norm_lt hlt hz, ← key]
  rfl

/-- **Rouché's theorem.**  If `‖g‖ < ‖f‖` on the circle and both are analytic on
the closed disk, then `f` and `f + g` have the same number of zeros inside,
counted with multiplicity.

The count is read off a factorization of either function, which is exactly the
list of its zeros with multiplicity; `rouche_of_analytic` supplies the two
factorizations from the same hypotheses. -/
theorem rouche {c : ℂ} {R : ℝ} (hR : 0 < R) {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall c R))
    (hg : AnalyticOnNhd ℂ g (Metric.closedBall c R))
    (hlt : ∀ z ∈ Metric.sphere c R, ‖g z‖ < ‖f z‖)
    {n n' : ℕ} {a a' : ℕ → ℂ} {G G' : ℂ → ℂ}
    (hfac : FactoredOn f c R n a G)
    (hfac' : FactoredOn (fun w => f w + g w) c R n' a' G') :
    n = n' := by
  have h₁ := circleIntegral_logDeriv_eq_of_factoredOn hR hfac
  have h₂ := circleIntegral_logDeriv_eq_of_factoredOn hR hfac'
  have h₃ := rouche_integral hR hf hg hlt
  rw [h₁, h₂] at h₃
  exact_mod_cast mul_right_cancel₀ Complex.two_pi_I_ne_zero h₃

/-- **Rouché read one-sidedly.**  A factorization of `f` transfers to `f + g` with the same
count, no factorization of `f + g` assumed: `exists_factoredOn` produces one, needing only
analyticity and non-vanishing on the circle, and `rouche` identifies its length with `n`. -/
theorem factoredOn_of_norm_lt {c : ℂ} {R : ℝ} (hR : 0 < R) {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall c R))
    (hg : AnalyticOnNhd ℂ g (Metric.closedBall c R))
    (hlt : ∀ z ∈ Metric.sphere c R, ‖g z‖ < ‖f z‖)
    {n : ℕ} {a : ℕ → ℂ} {G : ℂ → ℂ} (hfac : FactoredOn f c R n a G) :
    ∃ (a' : ℕ → ℂ) (G' : ℂ → ℂ), FactoredOn (fun w => f w + g w) c R n a' G' := by
  obtain ⟨n', a', G', hfac'⟩ := exists_factoredOn hR (fun z hz => (hf z hz).add (hg z hz))
    (fun z hz => add_ne_zero_of_norm_lt hR hlt hz)
  have hnn : n = n' := rouche hR hf hg hlt hfac hfac'
  exact ⟨a', G', by rw [hnn]; exact hfac'⟩

/-- **Rouché's theorem, packaged.**  Under `‖g‖ < ‖f‖` on the circle, both `f` and
`f + g` factor over the closed disk with the *same* number `n` of roots
displayed. -/
theorem rouche_of_analytic {c : ℂ} {R : ℝ} (hR : 0 < R) {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall c R))
    (hg : AnalyticOnNhd ℂ g (Metric.closedBall c R))
    (hlt : ∀ z ∈ Metric.sphere c R, ‖g z‖ < ‖f z‖) :
    ∃ (n : ℕ) (a a' : ℕ → ℂ) (G G' : ℂ → ℂ),
      FactoredOn f c R n a G ∧ FactoredOn (fun w => f w + g w) c R n a' G' := by
  obtain ⟨n, a, G, h₁⟩ := exists_factoredOn hR hf fun z hz => ne_zero_of_norm_lt hlt hz
  obtain ⟨a', G', h₂⟩ := factoredOn_of_norm_lt hR hf hg hlt h₁
  exact ⟨n, a, a', G, G', h₁, h₂⟩

/-! ### A worked instance

The count `FactoredOn` displays is the number of zeros *with multiplicity*, and
nothing weaker: `z ↦ z²` admits no factorization over the unit disk with fewer
than two roots listed, since a cofactor absorbing either factor would vanish at
the origin.  Rouché then forces `z² - 1/2` to carry two roots as well. -/

/-- The double zero of `z²` at the origin, displayed. -/
theorem factoredOn_sq : FactoredOn (fun z : ℂ => z ^ 2) 0 1 2 (fun _ => 0) (fun _ => 1) where
  mem_ball := by intro j _; simp
  analytic := fun z _ => analyticAt_const
  ne_zero := fun z _ => one_ne_zero
  eq := by intro z; simp [sq]

/-- The count cannot be short-changed: no factorization of `z²` over the unit disk
lists fewer roots, because the cofactor would have to vanish at the origin. -/
theorem not_factoredOn_sq_zero (a : ℕ → ℂ) (G : ℂ → ℂ) :
    ¬ FactoredOn (fun z : ℂ => z ^ 2) 0 1 0 a G := by
  intro h
  have h0 := h.eq 0
  simp at h0
  exact h.ne_zero 0 (by simp) h0.symm

/-- `z² - 1/2` has two zeros in the unit disk, by Rouché against `z²`. -/
theorem exists_factoredOn_sq_sub :
    ∃ (a : ℕ → ℂ) (G : ℂ → ℂ),
      FactoredOn (fun w : ℂ => w ^ 2 + (-2⁻¹ : ℂ)) 0 1 2 a G := by
  have hf : AnalyticOnNhd ℂ (fun z : ℂ => z ^ 2) (Metric.closedBall 0 1) :=
    fun z _ => analyticAt_id.pow 2
  have hg : AnalyticOnNhd ℂ (fun _ : ℂ => (-2⁻¹ : ℂ)) (Metric.closedBall 0 1) :=
    fun _ _ => analyticAt_const
  have hlt : ∀ z ∈ Metric.sphere (0 : ℂ) 1, ‖(-2⁻¹ : ℂ)‖ < ‖z ^ 2‖ := by
    intro z hz
    have hz1 : ‖z‖ = 1 := by simpa using Metric.mem_sphere.mp hz
    rw [norm_pow, hz1, one_pow]
    norm_num
  obtain ⟨n, a, a', G, G', h₁, h₂⟩ := rouche_of_analytic one_pos hf hg hlt
  have hn : 2 = n := rouche one_pos hf hg hlt factoredOn_sq h₂
  subst hn
  exact ⟨a', G', h₂⟩

/-! ### What this covers

All of Rouché is proved.  `rouche` concludes equality of the zero *counts* from
`‖g‖ < ‖f‖` on the circle, with nothing assumed about either count: the factored
presentation `argumentPrinciple` consumes is produced by `exists_factoredOn` for
every member of the family, so each counting integral is `2πi` times a natural
number, and the deformation argument closes.

The geometric applications — locating the zeros of a specific family — are the caller's, and
nothing in this module knows about them.
-/


/-! ### Axiom footprint -/

/-- info: 'Shields.rouche_of_analytic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rouche_of_analytic

end Shields
