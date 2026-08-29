/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.FTMinModulus.ArgumentCone
import ForgacsTran.FTBranchEndpointUpper
import ForgacsTran.PencilIndex

/-!
# The first positive critical point

`ArgumentCone.ftCritical_neg_below_ftTau` reduces the positive-real half of
`Forgacs2017RationalDenominator` Prop. 1 to one statement: `E = XQ' - rQ` does not
vanish below the branch radius.  This module proves it, proves their Lemma 5 for
the negative axis at `r = 1`, and closes `hcone` and `hmin` there.

The route is the factorization `E = -Σ·Q` with `Σ(s) = ∑_k s/(a_k - s) + r`, the
real form of `FTBranchZMono.ftSigma`.  Each summand is strictly increasing on any
interval missing its own pole, so `Σ` has at most one zero per gap between
consecutive zeros of `Q`; below the smallest zero both factors are positive, so
`E` is negative there; and the endpoint limit of the branch radius is a zero of
`E` inside the first gap, hence the first positive zero of `E`.  Lemma 3 places
the branch radius below that limit.

## Main statements

* `ftSigmaReal`, `eval_ftCriticalReal_eq_neg_sigma_mul` — the bracket and the
  factorization `E = -Σ·Q`, over `ℝ` and away from the zeros of `Q`.
* `ftSigmaReal_lt_of_lt` — `Σ` is strictly increasing across any interval that
  misses every `a_k`.
* `ftCritical_ne_zero_below_of_first_gap` — the endpoint limit is the *first*
  positive zero of `E`.
* `ftCritical_ne_zero_below_ftTau` — hence `E` has no zero below the branch
  radius, which is what `ftCritical_neg_below_ftTau` consumes.
* `negDivPow_lt_ftBranchZ_of_simple` — the positive-real half of their Prop. 1,
  with no hypothesis beyond the admissible class, a simple smallest zero, and
  their own exclusion `(r, n) ≠ (1, 2)`.
* `negDivPow_ge_of_neg` — their Lemma 5: on the negative axis the fiber map is
  bounded below by `b`, its value at the negative critical point.  `Σ` is strictly
  increasing there, so it changes sign exactly once, and the fiber map's
  derivative is `Σ(s)Q(s)/s²` with `Q > 0`.
* `negDivPow_neg_ne_ftBranchZ_one` — hence the negative-real half at `r = 1`,
  since the branch value stays strictly under `b`.
* `ftTau_le_of_repeated_min`, `negDivPow_lt_ftBranchZ_of_repeated` — the same
  half at a *repeated* smallest zero, where there is no first gap and the
  endpoint limit is that zero itself, so no critical point enters at all.
* `negDivPow_lt_ftBranchZ_pos` — the two multiplicity cases are exhaustive at a
  minimizing index, so the positive half holds with no hypothesis on any zero.
* `cone_at_branch_pi`, `ft_minModulus_at_branch_pi` — `hcone` and so
  `thm:FT-geometry`'s `hmin` at `r = 1`, with no analytic hypothesis and no
  multiplicity restriction.  `cone_at_branch_one` and
  `ft_minModulus_at_branch_one` are these with the multiplicity hypotheses they
  no longer need, kept for consumers written against the earlier form.
* `ft_minModulus_at_branch_cubic`, `cubic_min_not_simple` — the pencil
  `Q(t) = (1-t)^3`, which the simple-zero form cannot reach and this one does.

## Implementation notes

**Differs from the paper's route.**  Their Prop. 1 reaches "the derivative does
not vanish on `(0, t_a)`" by naming `t_a` as the first positive critical point and
citing Lemma 3 for `τ < t_a`.  Here `t_a` is not named separately: the endpoint
limit of `τ` *is* the first positive zero of `E`, proved so by the gap count on
`Σ`, and Lemma 3 enters as `FTBranchMonotone.ftTau_strictAnti` against that limit.
Naming one object rather than two is what lets the comparison be stated without
an auxiliary existence claim.

At `r ≥ 3` odd the negative axis is not reached here: `eq:ab-def` has no finite
upper endpoint there, so `negDivPow_ge_of_neg` has no `b` to be bounded by, and
their own argument closes that case through the `C₁ ∩ C₂` geometry instead.

The multiplicity of the smallest zero splits the argument but restricts nothing.
At `ρ = 1` — their Fig. 5 — `FTBranchGap.exists_tendsto_ftTau_mem_first_gap`
places the endpoint limit strictly inside the first gap, and the whole `Σ`
analysis above is what identifies it as `E`'s first positive zero.  At `ρ ≥ 2`
there is no first gap and that route is unavailable, but none is needed: the
limit is the smallest zero itself, every factor of `Q` is nonnegative below it,
and the fiber map is nonpositive where the branch value is positive.  The
`ρ ≥ 2` case is therefore shorter than `ρ = 1`, not harder, and
`negDivPow_lt_ftBranchZ_pos` joins them by cases at a minimizing index.

Sorry-free.

## References

* `../../shields-2026-forgacs-tran-numerators.tex`, «Spectral geometry, residues,
  and the principal amplitude» — `sec:geometry`, `thm:FT-geometry`.
* `Forgacs2017RationalDenominator`, Proposition 1 and Lemma 3.

## Tags

critical point, first gap, real zeros, Forgacs-Tran
-/

namespace ForgacsTran

open Real Set Polynomial

/-! ### The real bracket -/

/-- `Σ(s) = ∑_k s/(a_k - s) + r`, the real form of `FTBranchZMono.ftSigma`. -/
noncomputable def ftSigmaReal {n : ℕ} (a : Fin n → ℝ) (r : ℕ) (s : ℝ) : ℝ :=
  (∑ k, s / (a k - s)) + r

/-- **`E = -Σ·Q` over `ℝ`.**  `FTBranchZMono.eval_ftCritical_ftRootPoly` is this over
`ℂ`; the real form is what the sign analysis below runs on. -/
theorem eval_ftCriticalReal_eq_neg_sigma_mul {n r : ℕ} {c : ℝ} {a : Fin n → ℝ} {s : ℝ}
    (h : ∀ k, a k - s ≠ 0) :
    (ftCriticalReal (ftRootPolyReal c a) r).eval s
      = -(ftSigmaReal a r s) * (ftRootPolyReal c a).eval s := by
  have hD : (derivative (ftRootPolyReal c a)).eval s
      = c * (-(∑ k, 1 / (a k - s)) * ∏ k, (a k - s)) := by
    rw [ftRootPolyReal, derivative_mul, derivative_C]
    simp [eval_derivative_prod_sub Finset.univ a s fun k _ => h k]
  have hsum : s * (∑ k, 1 / (a k - s)) = ∑ k, s / (a k - s) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [mul_one_div]
  rw [eval_ftCriticalReal, hD, eval_ftRootPolyReal, ftSigmaReal]
  have : s * (c * (-(∑ k, 1 / (a k - s)) * ∏ k, (a k - s)))
      = -(s * (∑ k, 1 / (a k - s))) * (c * ∏ k, (a k - s)) := by ring
  rw [this, hsum]
  ring

/-- Each summand `s/(a - s)` is strictly increasing across any interval missing
its pole: the difference is `a(t - s)/((a - t)(a - s))`. -/
theorem div_sub_lt_div_sub {a s t : ℝ} (ha : 0 < a) (hst : s < t)
    (hsign : 0 < (a - t) * (a - s)) : s / (a - s) < t / (a - t) := by
  have ht : a - t ≠ 0 := by intro h; rw [h] at hsign; simp at hsign
  have hs : a - s ≠ 0 := by intro h; rw [h] at hsign; simp at hsign
  rw [← sub_pos]
  have key : t / (a - t) - s / (a - s) = a * (t - s) / ((a - t) * (a - s)) := by
    field
  rw [key]
  exact div_pos (mul_pos ha (sub_pos.2 hst)) hsign

/-- `Σ` is strictly increasing across any interval missing every zero of `Q`. -/
theorem ftSigmaReal_lt_of_lt {n r : ℕ} {a : Fin n → ℝ} (hn : 0 < n) (ha : ∀ k, 0 < a k)
    {s t : ℝ} (hst : s < t) (hsign : ∀ k, 0 < (a k - t) * (a k - s)) :
    ftSigmaReal a r s < ftSigmaReal a r t := by
  have hlt : ∀ k, s / (a k - s) < t / (a k - t) := fun k =>
    div_sub_lt_div_sub (ha k) hst (hsign k)
  have hsum := Finset.sum_lt_sum_of_nonempty
    (Finset.univ_nonempty_iff.2 (Fin.pos_iff_nonempty.1 hn)) fun k (_ : k ∈ Finset.univ) => hlt k
  simp only [ftSigmaReal]
  linarith

/-! ### The first positive zero of `E` -/

/-- **The endpoint limit is the first positive zero of `E`.**  Below the smallest
zero of `Q` both `Σ` and `Q` are positive, at that zero `E` does not vanish
because the zero is simple, and above it `Σ` is strictly increasing with a zero
at `L`, so it is negative in between while `Q` keeps its sign. -/
theorem ftCritical_ne_zero_below_of_first_gap {n r : ℕ} {c : ℝ} {a : Fin n → ℝ}
    (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r) {i : Fin n}
    (hmin : ∀ k, a i ≤ a k) (hsimple : ∀ k, k ≠ i → a k ≠ a i)
    {L : ℝ} (hLi : a i < L) (hLj : ∀ k, k ≠ i → L < a k)
    (hLe : (ftCriticalReal (ftRootPolyReal c a) r).eval L = 0) :
    ∀ s ∈ Ioo (0 : ℝ) L, (ftCriticalReal (ftRootPolyReal c a) r).eval s ≠ 0 := by
  have hn : 0 < n := Fin.pos_iff_nonempty.2 ⟨i⟩
  have hLne : ∀ k, a k - L ≠ 0 := by
    intro k
    rcases eq_or_ne k i with rfl | hk
    · exact sub_ne_zero.2 (by linarith)
    · exact sub_ne_zero.2 (by linarith [hLj k hk])
  have hQL : (ftRootPolyReal c a).eval L ≠ 0 := by
    rw [eval_ftRootPolyReal]
    exact mul_ne_zero hc.ne' (Finset.prod_ne_zero_iff.2 fun k _ => hLne k)
  have hSL : ftSigmaReal a r L = 0 := by
    have hfac := eval_ftCriticalReal_eq_neg_sigma_mul (c := c) (r := r) hLne
    rw [hLe] at hfac
    rcases mul_eq_zero.1 hfac.symm with h | h
    · linarith [neg_eq_zero.1 h]
    · exact absurd h hQL
  intro s hs
  rcases lt_trichotomy s (a i) with hlt | heq | hgt
  · exact ne_of_lt (eval_ftCriticalReal_neg_of_lt_min hc hr hmin hs.1 hlt)
  · rw [heq]
    exact eval_ftCriticalReal_ne_zero_of_simple hc.ne' ha hsimple
  · have hsne : ∀ k, a k - s ≠ 0 := by
      intro k
      rcases eq_or_ne k i with rfl | hk
      · exact sub_ne_zero.2 (by linarith)
      · exact sub_ne_zero.2 (by linarith [hLj k hk, hs.2])
    have hQs : (ftRootPolyReal c a).eval s ≠ 0 := by
      rw [eval_ftRootPolyReal]
      exact mul_ne_zero hc.ne' (Finset.prod_ne_zero_iff.2 fun k _ => hsne k)
    have hsign : ∀ k, 0 < (a k - L) * (a k - s) := by
      intro k
      rcases eq_or_ne k i with rfl | hk
      · exact mul_pos_of_neg_of_neg (by linarith) (by linarith)
      · exact mul_pos (by linarith [hLj k hk]) (by linarith [hLj k hk, hs.2])
    have hSs : ftSigmaReal a r s < 0 := by
      have hlt := ftSigmaReal_lt_of_lt (r := r) hn ha hs.2 hsign
      linarith
    rw [eval_ftCriticalReal_eq_neg_sigma_mul hsne]
    exact mul_ne_zero (by linarith) hQs

/-- **`E` has no zero below the branch radius.**  This is the statement
`ArgumentCone.ftCritical_neg_below_ftTau` consumes: Lemma 3 puts the branch
radius under the endpoint limit, and that limit is the first positive zero. -/
theorem ftCritical_ne_zero_below_ftTau {n r : ℕ} {c : ℝ} {a : Fin n → ℝ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r)
    (hne : ¬(r = 1 ∧ n = 2)) {i : Fin n} (hmin : ∀ k, a i ≤ a k)
    (hsimple : ∀ k, k ≠ i → a k ≠ a i) {θ : ℝ} (hθ : θ ∈ Ioo 0 (π / r)) :
    ∀ s ∈ Ioo (0 : ℝ) (ftTau a r (n - 1) θ),
      (ftCriticalReal (ftRootPolyReal c a) r).eval s ≠ 0 := by
  classical
  have hn : 0 < n := by omega
  have hnem : (Finset.univ.erase i).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin]
    omega
  obtain ⟨j, hjmem, hjmin⟩ := Finset.exists_min_image _ a hnem
  have hij : i ≠ j := Ne.symm (Finset.mem_erase.1 hjmem).1
  obtain ⟨L, hLi, hLj, hLtend, hLe⟩ :=
    exists_tendsto_ftTau_mem_first_gap hn2 ha hr hij hmin hsimple hc
  have hLall : ∀ k, k ≠ i → L < a k := fun k hk =>
    lt_of_lt_of_le hLj (hjmin k (Finset.mem_erase.2 ⟨hk, Finset.mem_univ k⟩))
  have hτL : ftTau a r (n - 1) θ ≤ L := by
    refine ge_of_tendsto hLtend ?_
    filter_upwards [Ioo_mem_nhdsGT hθ.1] with θ' hθ'
    have hθ'arc : θ' ∈ Ioo (0 : ℝ) (π / r) := ⟨hθ'.1, lt_trans hθ'.2 hθ.2⟩
    have hb' : FTBranchAt a r (n - 1) θ' :=
      ftBranchAt_of_arc_principal hn ha hr (Or.inl hn2) hθ'arc
    have hb : FTBranchAt a r (n - 1) θ :=
      ftBranchAt_of_arc_principal hn ha hr (Or.inl hn2) hθ
    exact (ftTau_strictAnti hn ha hr hne (ftTau_pos hb') (ftTau_pos hb) hθ'.1 hθ'.2 hθ.2
      (ftAngleSum_ftTau hb') (ftAngleSum_ftTau hb)).le
  intro s hs
  exact ftCritical_ne_zero_below_of_first_gap ha hc hr hmin hsimple hLi hLall hLe s
    ⟨hs.1, lt_of_lt_of_le hs.2 hτL⟩

/-- **The positive-real half of `Forgacs2017RationalDenominator` Prop. 1**, with
no hypothesis beyond the admissible class, a simple smallest zero, and their own
exclusion `(r, n) ≠ (1, 2)`: no real `s` in `(0, τ(θ)]` is a zero of the pencil. -/
theorem negDivPow_lt_ftBranchZ_of_simple {n r : ℕ} {a : Fin n → ℝ} {c : ℝ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r)
    (hne : ¬(r = 1 ∧ n = 2)) {i : Fin n} (hmin : ∀ k, a i ≤ a k)
    (hsimple : ∀ k, k ≠ i → a k ≠ a i) {θ : ℝ} (hθ : θ ∈ Ioo 0 (π / r))
    {s : ℝ} (hs0 : 0 < s) (hsτ : s ≤ ftTau a r (n - 1) θ) :
    -(ftRootPolyReal c a).eval s / s ^ r < ftBranchZ a c r (n - 1) θ :=
  negDivPow_lt_ftBranchZ_of_ftCritical_neg (by omega) ha hc hr (Or.inl hn2) hθ
    (ftCritical_neg_below_ftTau ha hc hr
      (ftCritical_ne_zero_below_ftTau hn2 ha hc hr hne hmin hsimple hθ)) hs0 hsτ

/-! ### The negative real axis at `r = 1` -/

/-- `Q > 0` on the negative axis. -/
theorem eval_ftRootPolyReal_pos_of_neg {n : ℕ} {c : ℝ} {a : Fin n → ℝ} (ha : ∀ k, 0 < a k)
    (hc : 0 < c) {s : ℝ} (hs : s < 0) : 0 < (ftRootPolyReal c a).eval s := by
  rw [eval_ftRootPolyReal]
  exact mul_pos hc (Finset.prod_pos fun k _ => by linarith [ha k])

/-- The derivative of the fiber map on the negative axis, with `E` eliminated in
favour of `Σ`: it is `Σ(s)Q(s)/s^{r+1}`, and `s^{r+1}` is positive at odd `r`. -/
theorem hasDerivAt_negDivPow_sigma {n r : ℕ} {c : ℝ} {a : Fin n → ℝ} (ha : ∀ k, 0 < a k)
    (hr : 1 ≤ r) {s : ℝ} (hs : s < 0) :
    HasDerivAt (fun u : ℝ => -(ftRootPolyReal c a).eval u / u ^ r)
      (ftSigmaReal a r s * (ftRootPolyReal c a).eval s / s ^ (r + 1)) s := by
  have hne : ∀ k, a k - s ≠ 0 := fun k => sub_ne_zero.2 (by linarith [ha k])
  have h := hasDerivAt_negDivPow (ftRootPolyReal c a) hr hs.ne
  have hfac := eval_ftCriticalReal_eq_neg_sigma_mul (c := c) (r := r) hne
  rw [eval_ftCriticalReal] at hfac
  have hEq : -(s * (derivative (ftRootPolyReal c a)).eval s
        - r * (ftRootPolyReal c a).eval s) / s ^ (r + 1)
      = ftSigmaReal a r s * (ftRootPolyReal c a).eval s / s ^ (r + 1) := by
    rw [hfac]; ring
  rwa [hEq] at h

/-- **`Forgacs2017RationalDenominator` Lemma 5, the bound the negative axis
carries.**  At `r = 1` the fiber map on `(-∞, 0)` is bounded below by its value at
the negative critical point `-L`, which is the `b` of `eq:ab-def`.

`Σ` is strictly increasing on the negative axis, so it changes sign exactly once
there, at `-L`; the fiber map's derivative is `Σ(s)Q(s)/s²` with `Q > 0`, so the
map falls to `-L` and rises after it. -/
theorem negDivPow_ge_of_neg {n : ℕ} {c : ℝ} {a : Fin n → ℝ} (hn : 0 < n)
    (ha : ∀ k, 0 < a k) (hc : 0 < c) {L : ℝ} (hL : 0 < L)
    (hEL : (ftCriticalReal (ftRootPolyReal c a) 1).eval (-L) = 0) {s : ℝ} (hs : s < 0) :
    -(ftRootPolyReal c a).eval (-L) / (-L) ^ 1
      ≤ -(ftRootPolyReal c a).eval s / s ^ 1 := by
  set f : ℝ → ℝ := fun u : ℝ => -(ftRootPolyReal c a).eval u / u ^ 1 with hfdef
  have hLneg : -L < 0 := by linarith
  have hne : ∀ k, a k - (-L) ≠ 0 := fun k => sub_ne_zero.2 (by linarith [ha k])
  have hSL : ftSigmaReal a 1 (-L) = 0 := by
    have hfac := eval_ftCriticalReal_eq_neg_sigma_mul (c := c) (r := 1) hne
    rw [hEL] at hfac
    rcases mul_eq_zero.1 hfac.symm with h | h
    · linarith [neg_eq_zero.1 h]
    · exact absurd h (eval_ftRootPolyReal_pos_of_neg ha hc hLneg).ne'
  have hsign : ∀ {x y : ℝ}, x < 0 → y < 0 → ∀ k, 0 < (a k - y) * (a k - x) := by
    intro x y hx hy k
    exact mul_pos (by linarith [ha k]) (by linarith [ha k])
  have hcont : ∀ S : Set ℝ, (∀ u ∈ S, u ≠ 0) → ContinuousOn f S := by
    intro S hS
    exact ContinuousOn.div (Polynomial.continuous _).continuousOn.neg
      ((continuous_pow 1).continuousOn) fun u hu => pow_ne_zero _ (hS u hu)
  have hderiv : ∀ u : ℝ, u < 0 →
      deriv f u = ftSigmaReal a 1 u * (ftRootPolyReal c a).eval u / u ^ (1 + 1) :=
    fun u hu => (hasDerivAt_negDivPow_sigma ha le_rfl hu).deriv
  rcases lt_or_ge s (-L) with hlt | hge
  · -- to the left of the critical point the map is strictly decreasing
    have hanti : StrictAntiOn f (Iic (-L)) := by
      refine strictAntiOn_of_deriv_neg (convex_Iic _)
        (hcont _ fun u hu => by have : u ≤ -L := hu; intro h; rw [h] at this; linarith)
        fun u hu => ?_
      rw [interior_Iic] at hu
      have huneg : u < 0 := by have : u < -L := hu; linarith
      rw [hderiv u huneg]
      have hS : ftSigmaReal a 1 u < 0 := by
        have := ftSigmaReal_lt_of_lt (r := 1) hn ha (show u < -L from hu)
          (fun k => hsign huneg hLneg k)
        linarith
      have hQ := eval_ftRootPolyReal_pos_of_neg ha hc huneg
      have hpow : (0 : ℝ) < u ^ (1 + 1) := by
        have h2 : u ^ (1 + 1) = u * u := by ring
        rw [h2]; exact mul_pos_of_neg_of_neg huneg huneg
      exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hS hQ) hpow
    exact (hanti hlt.le (le_refl (-L)) hlt).le
  · -- to the right of it the map is strictly increasing, up to the origin
    rcases eq_or_lt_of_le hge with heq | hgt
    · rw [← heq]
    · have hmono : StrictMonoOn f (Ico (-L) 0) := by
        refine strictMonoOn_of_deriv_pos (convex_Ico _ _)
          (hcont _ fun u hu => ne_of_lt hu.2) fun u hu => ?_
        rw [interior_Ico] at hu
        rw [hderiv u hu.2]
        have hS : 0 < ftSigmaReal a 1 u := by
          have := ftSigmaReal_lt_of_lt (r := 1) hn ha hu.1 (fun k => hsign hLneg hu.2 k)
          linarith
        have hQ := eval_ftRootPolyReal_pos_of_neg ha hc hu.2
        have hpow : (0 : ℝ) < u ^ (1 + 1) := by
          have h2 : u ^ (1 + 1) = u * u := by ring
          rw [h2]; exact mul_pos_of_neg_of_neg hu.2 hu.2
        exact div_pos (mul_pos hS hQ) hpow
      exact (hmono ⟨le_refl (-L), hLneg⟩ ⟨hgt.le, hs⟩ hgt).le

/-- **The negative-real half of their Prop. 1 at `r = 1`.**  The branch value is
below `b` by strict monotonicity, and `b` is what the negative axis is bounded
below by, so the fiber map never takes the branch value there. -/
theorem negDivPow_neg_ne_ftBranchZ_one {n : ℕ} {a : Fin n → ℝ} {c : ℝ} (hn2 : 2 ≤ n)
    (ha : ∀ k, 0 < a k) (hc : 0 < c) {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) (π / ((1 : ℕ) : ℝ)))
    {s : ℝ} (hs : s < 0) :
    -(ftRootPolyReal c a).eval s / s ^ 1 ≠ ftBranchZ a c 1 (n - 1) θ := by
  have hn : 0 < n := by omega
  have hcast : π / ((1 : ℕ) : ℝ) = π := pi_div_natCast_one
  rw [hcast] at hθ
  obtain ⟨L, hL, hτ, hEL⟩ := exists_tendsto_ftTau_nhdsLT_pi hn2 ha hc
  set b : ℝ := -(ftRootPolyReal c a).eval (-L) / (-L) ^ 1 with hbdef
  -- the branch value is strictly below `b`
  have hb : ∀ ψ ∈ Ioo (0 : ℝ) π, FTBranchAt a 1 (n - 1) ψ := by
    intro ψ hψ
    exact ftBranchAt_of_arc_principal hn ha le_rfl (Or.inl hn2) (by rwa [hcast])
  have hparp : Even (n + (n - 1) + 1) := even_add_pred_add_one hn
  have hmono : StrictMonoOn (ftBranchZ a c 1 (n - 1)) (Ioo (0 : ℝ) π) := by
    have := ftBranchZ_strictMonoOn (c := c) hn ha hc (le_refl 1) hparp
      (fun ψ hψ => hb ψ (by rwa [hcast] at hψ))
    rwa [hcast] at this
  have htend : Filter.Tendsto (ftBranchZ a c 1 (n - 1)) (nhdsWithin π (Ioo 0 π)) (nhds b) := by
    refine tendsto_ftBranchZ_upper_pi ha hL ?_
      (hτ.mono_left (nhdsWithin_mono _ Ioo_subset_Iio_self))
    filter_upwards [self_mem_nhdsWithin] with ψ hψ
    exact ⟨hψ, hb ψ hψ⟩
  haveI : (nhdsWithin π (Ioo (0 : ℝ) π)).NeBot := right_nhdsWithin_Ioo_neBot pi_pos
  have hzb : ftBranchZ a c 1 (n - 1) θ < b := by
    obtain ⟨θ₂, hθ₂⟩ : (Ioo θ π).Nonempty := Set.nonempty_Ioo.2 hθ.2
    have hθ₂arc : θ₂ ∈ Ioo (0 : ℝ) π := ⟨lt_trans hθ.1 hθ₂.1, hθ₂.2⟩
    have h1 : ftBranchZ a c 1 (n - 1) θ < ftBranchZ a c 1 (n - 1) θ₂ :=
      hmono hθ hθ₂arc hθ₂.1
    have h2 : ftBranchZ a c 1 (n - 1) θ₂ ≤ b := by
      refine ge_of_tendsto htend ?_
      filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
        (eventually_gt_nhds hθ₂.2)] with ψ hψ hgt
      exact (hmono hθ₂arc hψ hgt).le
    linarith
  have hge := negDivPow_ge_of_neg hn ha hc hL hEL hs
  linarith

/-! ### The repeated smallest zero -/

/-- **The bracket at a repeated smallest zero.**  There is no first gap there, so
the route of `ftCritical_ne_zero_below_ftTau` is unavailable — and none is needed:
`FTBranchLimitPoint.tendsto_ftTau_nhdsGT_zero_of_repeated_min` identifies the
endpoint limit as the smallest zero itself, and Lemma 3 puts the branch radius
under it. -/
theorem ftTau_le_of_repeated_min {n r : ℕ} {a : Fin n → ℝ} (hn2 : 2 ≤ n)
    (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) (hne : ¬(r = 1 ∧ n = 2)) {i j : Fin n}
    (hij : i ≠ j) (haij : a i = a j) (hmin : ∀ k, a i ≤ a k) {θ : ℝ}
    (hθ : θ ∈ Ioo 0 (π / r)) : ftTau a r (n - 1) θ ≤ a i := by
  have hn : 0 < n := by omega
  refine ge_of_tendsto (tendsto_ftTau_nhdsGT_zero_of_repeated_min hn2 ha hr hij haij hmin) ?_
  filter_upwards [Ioo_mem_nhdsGT hθ.1] with θ' hθ'
  have hθ'arc : θ' ∈ Ioo (0 : ℝ) (π / r) := ⟨hθ'.1, lt_trans hθ'.2 hθ.2⟩
  have hb' : FTBranchAt a r (n - 1) θ' :=
    ftBranchAt_of_arc_principal hn ha hr (Or.inl hn2) hθ'arc
  have hb : FTBranchAt a r (n - 1) θ :=
    ftBranchAt_of_arc_principal hn ha hr (Or.inl hn2) hθ
  exact (ftTau_strictAnti hn ha hr hne (ftTau_pos hb') (ftTau_pos hb) hθ'.1 hθ'.2 hθ.2
    (ftAngleSum_ftTau hb') (ftAngleSum_ftTau hb)).le

/-- **The positive-real half at a repeated smallest zero.**  Every factor of `Q`
is nonnegative up to the branch radius, so the fiber map is nonpositive there
while the branch value is positive.  No critical point enters, which is why this
case is shorter than the simple one rather than harder. -/
theorem negDivPow_lt_ftBranchZ_of_repeated {n r : ℕ} {a : Fin n → ℝ} {c : ℝ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r)
    (hne : ¬(r = 1 ∧ n = 2)) {i j : Fin n} (hij : i ≠ j) (haij : a i = a j)
    (hmin : ∀ k, a i ≤ a k) {θ : ℝ} (hθ : θ ∈ Ioo 0 (π / r))
    {s : ℝ} (hs0 : 0 < s) (hsτ : s ≤ ftTau a r (n - 1) θ) :
    -(ftRootPolyReal c a).eval s / s ^ r < ftBranchZ a c r (n - 1) θ := by
  have hn : 0 < n := by omega
  have hθπ : θ ∈ Ioo 0 π := ftArc_subset hr hθ
  have hb : FTBranchAt a r (n - 1) θ :=
    ftBranchAt_of_arc_principal hn ha hr (Or.inl hn2) hθ
  have hparp : Even (n + (n - 1) + 1) := even_add_pred_add_one hn
  have hz : 0 < ftBranchZ a c r (n - 1) θ := ftBranchZ_pos ha hc hparp hθπ hb
  have hsx : s ≤ a i :=
    le_trans hsτ (ftTau_le_of_repeated_min hn2 ha hr hne hij haij hmin hθ)
  have hQ : 0 ≤ (ftRootPolyReal c a).eval s := by
    rw [eval_ftRootPolyReal]
    exact mul_nonneg hc.le (Finset.prod_nonneg fun k _ => by linarith [hmin k])
  have hpow : (0 : ℝ) < s ^ r := pow_pos hs0 r
  have hle : -(ftRootPolyReal c a).eval s / s ^ r ≤ 0 := by
    rw [div_nonpos_iff]
    exact Or.inr ⟨by linarith, hpow.le⟩
  linarith

/-- **The positive-real half of `Forgacs2017RationalDenominator` Prop. 1, at every
multiplicity.**  The two cases are exhaustive at a minimizing index: either it is
simple, and the first positive critical point places the branch radius, or it is
repeated, and the endpoint limit does. -/
theorem negDivPow_lt_ftBranchZ_pos {n r : ℕ} {a : Fin n → ℝ} {c : ℝ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r)
    (hne : ¬(r = 1 ∧ n = 2)) {θ : ℝ} (hθ : θ ∈ Ioo 0 (π / r))
    {s : ℝ} (hs0 : 0 < s) (hsτ : s ≤ ftTau a r (n - 1) θ) :
    -(ftRootPolyReal c a).eval s / s ^ r < ftBranchZ a c r (n - 1) θ := by
  classical
  have hn : 0 < n := by omega
  obtain ⟨i, -, hmini⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin n)) a
    (Finset.univ_nonempty_iff.2 (Fin.pos_iff_nonempty.1 hn))
  have hmin : ∀ k, a i ≤ a k := fun k => hmini k (Finset.mem_univ k)
  by_cases hsimple : ∀ k, k ≠ i → a k ≠ a i
  · exact negDivPow_lt_ftBranchZ_of_simple hn2 ha hc hr hne hmin hsimple hθ hs0 hsτ
  · push Not at hsimple
    obtain ⟨j, hji, hja⟩ := hsimple
    exact negDivPow_lt_ftBranchZ_of_repeated hn2 ha hc hr hne (Ne.symm hji) hja.symm
      hmin hθ hs0 hsτ

/-! ### `hcone` and `hmin` at `r = 1` -/

/-- **`ArgumentCone`'s `hcone` at `r = 1`, discharged.**  Both real halves of
`Forgacs2017RationalDenominator` Prop. 1 are in hand at every multiplicity, and at
`r = 1` they are the whole of the argument condition. -/
theorem cone_at_branch_pi {n : ℕ} {a : Fin n → ℝ} {c : ℝ} (hn3 : 3 ≤ n)
    (ha : ∀ k, 0 < a k) (hc : 0 < c) :
    FTArgumentCone (ftRootPoly c a) 1 (ftBranchZ a c 1 (n - 1)) (ftTau a 1 (n - 1)) :=
  cone_of_no_real_root_pi rfl ha hc
    (fun θ hθ s hs0 hsτ => negDivPow_lt_ftBranchZ_pos (by omega) ha hc (le_refl 1)
      (by omega) hθ hs0 hsτ)
    (fun θ hθ s hs _ => negDivPow_neg_ne_ftBranchZ_one (by omega) ha hc hθ hs)

/-- **`thm:FT-geometry`'s `hmin` at `r = 1`, unconditional** on the admissible
class — `Forgacs2017RationalDenominator` Props. 1--2 for the constructed branch,
with no analytic hypothesis and no restriction on the multiplicity of any zero.
`n ≥ 3` is their own `(deg Q, r) ≠ (2,1)`. -/
theorem ft_minModulus_at_branch_pi {n : ℕ} {a : Fin n → ℝ} {c : ℝ} (hn3 : 3 ≤ n)
    (ha : ∀ k, 0 < a k) (hc : 0 < c) :
    FTMinModulusGap (ftRootPoly c a) 1 (ftBranchZ a c 1 (n - 1)) (ftTau a 1 (n - 1)) :=
  ft_minModulus_at_branch (by omega) ha hc (le_refl 1) (cone_at_branch_pi hn3 ha hc)

/-- `cone_at_branch_pi` with the multiplicity hypotheses it no longer needs, kept
so that consumers written against the simple-zero form still elaborate. -/
theorem cone_at_branch_one {n : ℕ} {a : Fin n → ℝ} {c : ℝ} (hn3 : 3 ≤ n)
    (ha : ∀ k, 0 < a k) (hc : 0 < c) {i : Fin n} (_hmin : ∀ k, a i ≤ a k)
    (_hsimple : ∀ k, k ≠ i → a k ≠ a i) :
    FTArgumentCone (ftRootPoly c a) 1 (ftBranchZ a c 1 (n - 1)) (ftTau a 1 (n - 1)) :=
  cone_at_branch_pi hn3 ha hc

/-- `ft_minModulus_at_branch_pi` with the multiplicity hypotheses it no longer
needs, kept so that consumers written against the simple-zero form still
elaborate. -/
theorem ft_minModulus_at_branch_one {n : ℕ} {a : Fin n → ℝ} {c : ℝ} (hn3 : 3 ≤ n)
    (ha : ∀ k, 0 < a k) (hc : 0 < c) {i : Fin n} (_hmin : ∀ k, a i ≤ a k)
    (_hsimple : ∀ k, k ≠ i → a k ≠ a i) :
    FTMinModulusGap (ftRootPoly c a) 1 (ftBranchZ a c 1 (n - 1)) (ftTau a 1 (n - 1)) :=
  ft_minModulus_at_branch_pi hn3 ha hc

/-! ### The cubic pencil -/

/-- **`Q(t) = (1-t)^3` is inside the multiplicity-free form.**  Its smallest zero
has multiplicity three, so `ft_minModulus_at_branch_one`'s simplicity hypothesis
cannot be met at it — `cubic_min_not_simple` — while the three hypotheses
`ft_minModulus_at_branch_pi` carries are immediate.  This is the non-vacuity
witness for the multiplicity-free statement. -/
theorem ft_minModulus_at_branch_cubic :
    ∀ θ ∈ Ioo (0 : ℝ) (π / ((1 : ℕ) : ℝ)), ∀ w : ℂ,
      (ftDen (ftRootPoly (1 : ℝ) ![(1 : ℝ), 1, 1]) 1
          ((ftBranchZ ![(1 : ℝ), 1, 1] 1 1 2 θ : ℝ) : ℂ)).eval w = 0 →
        w ≠ ftPrincipal (ftTau ![(1 : ℝ), 1, 1] 1 2) θ →
        w ≠ (starRingEnd ℂ) (ftPrincipal (ftTau ![(1 : ℝ), 1, 1] 1 2) θ) →
        ftTau ![(1 : ℝ), 1, 1] 1 2 θ < ‖w‖ :=
  ft_minModulus_at_branch_pi (n := 3) (le_refl 3)
    (fun k => by fin_cases k <;> norm_num) one_pos

/-- No minimizing index of the cubic pencil is simple, so the simple-zero form
does not reach it. -/
theorem cubic_min_not_simple :
    ¬ ∃ i : Fin 3, (∀ k, ![(1 : ℝ), 1, 1] i ≤ ![(1 : ℝ), 1, 1] k) ∧
      ∀ k, k ≠ i → ![(1 : ℝ), 1, 1] k ≠ ![(1 : ℝ), 1, 1] i := by
  rintro ⟨i, -, hs⟩
  fin_cases i
  · exact hs 1 (by decide) (by norm_num)
  · exact hs 0 (by decide) (by norm_num)
  · exact hs 0 (by decide) (by norm_num)

end ForgacsTran
