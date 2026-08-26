/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.FTMinModulus.PrincipalGap
import ForgacsTran.FTBranchGap
import ForgacsTran.FTBranchMonotone

/-!
# The argument of an inner zero

`PrincipalGap.ft_minModulus_at_branch` carries one hypothesis, `hcone`: a zero of
the pencil in the closed disk of radius `τ(θ)` has argument strictly inside the
double cone `|arg| < π/r`.  It is the two paragraphs of
`Forgacs2017RationalDenominator` Prop. 1 that place such a zero — "We first argue
that `t* ∉ ℝ`", and "the argument `θ^{t*}` of `t*` lies in `(0, π/r)`".

At `r = 1` the second paragraph is empty: the cone is the whole plane cut along
the reals, so `hcone` *is* the statement that no zero of the pencil in the closed
disk is real.  That reduction is `cone_of_no_real_root_pi`, and the real
exclusion splits along the sign of the zero.

## Main statements

* `negDivPow_ftTau_lt_ftBranchZ` — the fiber map `-Q(s)/s^r` at the positive real
  point of the branch circle is below the branch value.  This is the magnitude
  comparison their Prop. 1 opens with, and it needs no complex geometry: each
  chord `|a_k - τ|` is shorter than `|a_k - τe^{-iθ}|` by `2a_kτ(1 - \cos θ)`.
* `negDivPow_lt_ftBranchZ_of_ftCritical_neg` — hence the whole real interval
  `(0, τ(θ)]` is below it, once `-Q(s)/s^r` is increasing there.  This is the
  positive half of their `t* ∉ ℝ`.
* `ftCritical_neg_below_ftTau` — that monotonicity, reduced to the single
  statement that the branch radius stays below the first positive critical point.
* `no_neg_real_root_of_even` — the negative half at even `r`, where the sign of
  `s^r` settles it outright.
* `abs_arg_mem_Ioo_pi`, `cone_of_no_real_root_pi` — `hcone` at `r = 1` is exactly
  the absence of a real zero in the closed disk.
* `ftCritical_ne_zero_below_ftTau_of_lt` — the residual statement, reduced to
  `τ(θ)` lying below the first positive zero of `E`, which
  `FTBranchMonotone.ftTau_strictAnti` and
  `FTBranchGap.exists_tendsto_ftTau_mem_first_gap` bracket from both sides.

## References

* `../../shields-2026-forgacs-tran-numerators.tex`, «Spectral geometry, residues,
  and the principal amplitude» — `sec:geometry`, `thm:FT-geometry`.
* `Forgacs2017RationalDenominator`, Proposition 1 and Lemmas 3, 5 and 6.

## Tags

argument, minimum modulus, real zeros, critical point
-/

namespace ForgacsTran

open Real Set Polynomial

/-! ### The fiber map at the real point of the branch circle -/

/-- Every chord from a zero of `Q` to the positive real point of the circle
`|t| = τ` is strictly shorter than the chord to the branch point, the difference
of squares being `2a_kτ(1 - \cos θ)`. -/
theorem abs_sub_lt_sqrt_quad {a τ θ : ℝ} (ha : 0 < a) (hτ : 0 < τ) (hθ : θ ∈ Ioo 0 π) :
    |a - τ| < Real.sqrt (a ^ 2 - 2 * a * τ * Real.cos θ + τ ^ 2) := by
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hcos : Real.cos θ < 1 := by
    nlinarith [Real.sin_sq_add_cos_sq θ, Real.cos_le_one θ, mul_pos hs hs]
  have hsq : (a - τ) ^ 2 < a ^ 2 - 2 * a * τ * Real.cos θ + τ ^ 2 := by
    nlinarith [mul_pos (mul_pos ha hτ) (sub_pos.2 hcos)]
  have habs : |a - τ| = Real.sqrt ((a - τ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
  rw [habs]
  exact Real.sqrt_lt_sqrt (sq_nonneg _) hsq

/-- **The magnitude comparison of `Forgacs2017RationalDenominator` Prop. 1.**  The
fiber map `-Q(s)/s^r` at the positive real point `s = τ(θ)` of the branch circle
is strictly below the branch value `z(θ)`.

The whole computation is real: `|Q(τ)| = c∏|a_k - τ|`, the branch value is
`c∏|a_k - τe^{-iθ}|/τ^r` through `ftBranchZ_eq_chordProd`, and every chord is
shortened by moving the point onto the positive real axis.

**Differs from the paper's route.**  `Forgacs2017RationalDenominator` obtains this
comparison from the minimum-modulus property on the circle `|t| = τ(θ)`, so it is
downstream of their Props. 1--2.  Here it is a chord inequality and uses no complex
geometry at all: each chord `|a_k - τ|` beats `|a_k - τe^{-iθ}|` by exactly
`2 a_k τ (1 - cos θ)`.  Taking it first is what lets the argument cone be
established without the minimum-modulus statement it would otherwise depend on. -/
theorem negDivPow_ftTau_lt_ftBranchZ {n r : ℕ} {a : Fin n → ℝ} {c : ℝ} (hn : 0 < n)
    (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r)
    {θ : ℝ} (hθ : θ ∈ Ioo 0 (π / r)) :
    -(ftRootPolyReal c a).eval (ftTau a r (n - 1) θ) / ftTau a r (n - 1) θ ^ r
      < ftBranchZ a c r (n - 1) θ := by
  have hθπ : θ ∈ Ioo 0 π := ftArc_subset hr hθ
  have hb : FTBranchAt a r (n - 1) θ := ftBranchAt_of_arc_principal hn ha hr hnr hθ
  set τ : ℝ := ftTau a r (n - 1) θ with hτdef
  have hτ : 0 < τ := ftTau_pos hb
  have hτr : (0 : ℝ) < τ ^ r := by positivity
  have hparp : Even (n + (n - 1) + 1) := by
    have hEq : n + (n - 1) + 1 = 2 * n := by omega
    rw [hEq]; exact even_two_mul n
  have hZ : ftBranchZ a c r (n - 1) θ = c * ftChordProd a τ θ / τ ^ r :=
    ftBranchZ_eq_chordProd ha hparp hθπ hb rfl
  have hsθ : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθπ.1 hθπ.2
  have hcos : Real.cos θ < 1 := by
    nlinarith [Real.sin_sq_add_cos_sq θ, Real.cos_le_one θ, mul_pos hsθ hsθ]
  have hchord : ∀ k, (0 : ℝ) < Real.sqrt (a k ^ 2 - 2 * a k * τ * Real.cos θ + τ ^ 2) := by
    intro k
    refine Real.sqrt_pos.2 ?_
    nlinarith [sq_nonneg (a k - τ), mul_pos (mul_pos (ha k) hτ) (sub_pos.2 hcos)]
  -- the product of the shorter chords is smaller, unless it vanishes
  have hle : -(ftRootPolyReal c a).eval τ ≤ c * ∏ k, |a k - τ| := by
    rw [eval_ftRootPolyReal]
    have habs : |∏ k, (a k - τ)| = ∏ k, |a k - τ| := Finset.abs_prod _ _
    have h1 : -(∏ k, (a k - τ)) ≤ ∏ k, |a k - τ| := by
      rw [← habs]; exact neg_le_abs _
    have hrw : -(c * ∏ k, (a k - τ)) = c * (-(∏ k, (a k - τ))) := by ring
    rw [hrw]
    exact mul_le_mul_of_nonneg_left h1 hc.le
  have hlt : c * ∏ k, |a k - τ| < c * ftChordProd a τ θ := by
    refine mul_lt_mul_of_pos_left ?_ hc
    rw [ftChordProd]
    rcases eq_or_ne (∏ k, |a k - τ|) 0 with h0 | h0
    · rw [h0]
      exact Finset.prod_pos fun k _ => hchord k
    · have hpos : ∀ k, (0 : ℝ) < |a k - τ| := by
        intro k
        rcases (abs_nonneg (a k - τ)).lt_or_eq with h | h
        · exact h
        · exact absurd (Finset.prod_eq_zero (Finset.mem_univ k) h.symm) h0
      exact Finset.prod_lt_prod_of_nonempty (fun k _ => hpos k)
        (fun k _ => abs_sub_lt_sqrt_quad (ha k) hτ hθπ)
        (Finset.univ_nonempty_iff.2 (Fin.pos_iff_nonempty.1 hn))
  rw [hZ, div_lt_div_iff_of_pos_right hτr]
  linarith

/-! ### The positive real axis -/

/-- **The positive half of their `t* ∉ ℝ`.**  Once `-Q(s)/s^r` is increasing on
`(0, τ(θ))`, every real `s` in `(0, τ(θ)]` has `-Q(s)/s^r` below the branch value,
so no such `s` is a zero of the pencil. -/
theorem negDivPow_lt_ftBranchZ_of_ftCritical_neg {n r : ℕ} {a : Fin n → ℝ} {c : ℝ}
    (hn : 0 < n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r)
    {θ : ℝ} (hθ : θ ∈ Ioo 0 (π / r))
    (hE : ∀ s ∈ Ioo (0 : ℝ) (ftTau a r (n - 1) θ),
      (ftCriticalReal (ftRootPolyReal c a) r).eval s < 0)
    {s : ℝ} (hs0 : 0 < s) (hsτ : s ≤ ftTau a r (n - 1) θ) :
    -(ftRootPolyReal c a).eval s / s ^ r < ftBranchZ a c r (n - 1) θ := by
  have hb : FTBranchAt a r (n - 1) θ := ftBranchAt_of_arc_principal hn ha hr hnr hθ
  have hτ : 0 < ftTau a r (n - 1) θ := ftTau_pos hb
  have hneg : ∀ u ∈ Ioo (0 : ℝ) (ftTau a r (n - 1) θ),
      u * (derivative (ftRootPolyReal c a)).eval u
        - r * (ftRootPolyReal c a).eval u < 0 := by
    intro u hu
    have := hE u hu
    rwa [eval_ftCriticalReal] at this
  have hmono := strictMonoOn_negDivPow (P := ftRootPolyReal c a) hr hτ hneg
  have hstep : -(ftRootPolyReal c a).eval s / s ^ r
      ≤ -(ftRootPolyReal c a).eval (ftTau a r (n - 1) θ) / ftTau a r (n - 1) θ ^ r := by
    rcases eq_or_lt_of_le hsτ with h | h
    · rw [h]
    · exact (hmono ⟨hs0, hsτ⟩ ⟨hτ, le_rfl⟩ h).le
  exact lt_of_le_of_lt hstep (negDivPow_ftTau_lt_ftBranchZ hn ha hc hr hnr hθ)

/-- The monotonicity `negDivPow_lt_ftBranchZ_of_ftCritical_neg` consumes, reduced
to a single nonvanishing statement: `E` starts at `-rQ(0) < 0` and cannot change
sign without a zero. -/
theorem ftCritical_neg_below_ftTau {n r : ℕ} {a : Fin n → ℝ} {c : ℝ}
    (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r) {θ : ℝ}
    (hno : ∀ s ∈ Ioo (0 : ℝ) (ftTau a r (n - 1) θ),
      (ftCriticalReal (ftRootPolyReal c a) r).eval s ≠ 0) :
    ∀ s ∈ Ioo (0 : ℝ) (ftTau a r (n - 1) θ),
      (ftCriticalReal (ftRootPolyReal c a) r).eval s < 0 := by
  have hP0 : 0 < (ftRootPolyReal c a).eval 0 := by
    rw [eval_ftRootPolyReal]
    exact mul_pos hc (Finset.prod_pos fun k _ => by simpa using ha k)
  intro s hs
  have hno' : ∀ u ∈ Ioo (0 : ℝ) (ftTau a r (n - 1) θ),
      u * (derivative (ftRootPolyReal c a)).eval u
        - r * (ftRootPolyReal c a).eval u ≠ 0 := by
    intro u hu
    have := hno u hu
    rwa [eval_ftCriticalReal] at this
  have := ftCritical_eval_neg hr hP0 hno' s hs
  rwa [eval_ftCriticalReal]

/-! ### The negative real axis at even `r` -/

/-- **The negative half at even `r`.**  There `s^r > 0` while `Q(s) > 0`, so the
fiber map is negative on the whole negative axis and the branch value is positive.
No containment and no critical point are used, and the bound is not restricted to
the closed disk. -/
theorem no_neg_real_root_of_even {n r : ℕ} {a : Fin n → ℝ} {c : ℝ} (hn : 0 < n)
    (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r)
    (hrpar : Even r) {θ : ℝ} (hθ : θ ∈ Ioo 0 (π / r)) {s : ℝ} (hs : s < 0) :
    -(ftRootPolyReal c a).eval s / s ^ r < ftBranchZ a c r (n - 1) θ := by
  have hθπ : θ ∈ Ioo 0 π := ftArc_subset hr hθ
  have hb : FTBranchAt a r (n - 1) θ := ftBranchAt_of_arc_principal hn ha hr hnr hθ
  have hparp : Even (n + (n - 1) + 1) := by
    have hEq : n + (n - 1) + 1 = 2 * n := by omega
    rw [hEq]; exact even_two_mul n
  have hz : 0 < ftBranchZ a c r (n - 1) θ := ftBranchZ_pos ha hc hparp hθπ hb
  have hQ : 0 < (ftRootPolyReal c a).eval s := by
    rw [eval_ftRootPolyReal]
    exact mul_pos hc (Finset.prod_pos fun k _ => by linarith [ha k])
  have hpow : 0 < s ^ r := hrpar.pow_pos hs.ne
  have : -(ftRootPolyReal c a).eval s / s ^ r < 0 := div_neg_of_neg_of_pos (by linarith) hpow
  linarith

/-! ### `hcone` at `r = 1` -/

/-- A nonreal number has argument strictly inside `(0, π)` in absolute value: the
two excluded values `0` and `π` are exactly the two real directions. -/
theorem abs_arg_mem_Ioo_pi {w : ℂ} (h : w.im ≠ 0) : |Complex.arg w| ∈ Ioo 0 π := by
  have hmem := Complex.arg_mem_Ioc w
  refine ⟨abs_pos.2 fun h0 => h (Complex.arg_eq_zero_iff.1 h0).2, ?_⟩
  · rcases lt_or_eq_of_le hmem.2 with hlt | heq
    · rw [abs_lt]
      exact ⟨hmem.1, hlt⟩
    · exact absurd (Complex.arg_eq_pi_iff.1 heq).2 h

/-- The pencil at a real point is the real pencil. -/
theorem eval_ftDen_ofReal {n r : ℕ} (c : ℝ) (a : Fin n → ℝ) (z s : ℝ) :
    (ftDen (ftRootPoly c a) r ((z : ℝ) : ℂ)).eval ((s : ℝ) : ℂ)
      = (((ftRootPolyReal c a).eval s + z * s ^ r : ℝ) : ℂ) := by
  rw [ftDen_eval, eval_ftRootPoly, eval_ftRootPolyReal]
  push_cast
  ring

/-- The origin is never a zero of the pencil: `Q(0) = c∏_k a_k > 0` and `r ≥ 1`
kills the other term. -/
theorem eval_ftDen_zero_ne_zero {n r : ℕ} {a : Fin n → ℝ} {c : ℝ} (ha : ∀ k, 0 < a k)
    (hc : 0 < c) (hr : 1 ≤ r) (z : ℂ) : (ftDen (ftRootPoly c a) r z).eval 0 ≠ 0 := by
  have hQ : (0 : ℝ) < c * ∏ k, a k :=
    mul_pos hc (Finset.prod_pos fun k _ => ha k)
  rw [ftDen_eval, eval_ftRootPoly, zero_pow (by omega : r ≠ 0), mul_zero, add_zero,
    show ((c : ℂ) * ∏ k, ((a k : ℂ) - 0)) = (((c * ∏ k, a k : ℝ)) : ℂ) by simp]
  exact_mod_cast hQ.ne'

/-- **`hcone` at `r = 1` is the absence of a real zero in the closed disk.**  The
double cone `|\arg t| < π/r` is then the whole plane cut along the reals, so
their second paragraph — the one that runs on `C₁ ∩ C₂` and the angle bound —
has nothing to prove, and the argument condition reduces to the real exclusion
their first paragraph carries. -/
theorem cone_of_no_real_root_pi {n r : ℕ} {a : Fin n → ℝ} {c : ℝ} (hr1 : r = 1)
    (ha : ∀ k, 0 < a k) (hc : 0 < c)
    (hpos : ∀ θ ∈ Ioo (0 : ℝ) (π / r), ∀ s : ℝ, 0 < s → s ≤ ftTau a r (n - 1) θ →
      -(ftRootPolyReal c a).eval s / s ^ r < ftBranchZ a c r (n - 1) θ)
    (hneg : ∀ θ ∈ Ioo (0 : ℝ) (π / r), ∀ s : ℝ, s < 0 → -s ≤ ftTau a r (n - 1) θ →
      -(ftRootPolyReal c a).eval s / s ^ r ≠ ftBranchZ a c r (n - 1) θ) :
    ∀ θ ∈ Ioo (0 : ℝ) (π / r), ∀ w : ℂ,
      (ftDen (ftRootPoly c a) r ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ)).eval w = 0 →
        ‖w‖ ≤ ftTau a r (n - 1) θ → |Complex.arg w| ∈ Ioo 0 (π / r) := by
  subst hr1
  intro θ hθ w hw hnorm
  have hπr : π / ((1 : ℕ) : ℝ) = π := by norm_num
  rw [hπr]
  refine abs_arg_mem_Ioo_pi fun him => ?_
  -- a real zero solves the real pencil equation
  have hw0 : w ≠ 0 := fun h =>
    eval_ftDen_zero_ne_zero ha hc le_rfl _ (h ▸ hw)
  have hre : w = ((w.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
  set s : ℝ := w.re with hsdef
  have hs0 : s ≠ 0 := fun h => hw0 (by rw [hre, h]; simp)
  have hreal : (ftRootPolyReal c a).eval s + ftBranchZ a c 1 (n - 1) θ * s ^ 1 = 0 := by
    have := hw
    rw [hre, eval_ftDen_ofReal] at this
    exact_mod_cast this
  have hnorms : |s| ≤ ftTau a 1 (n - 1) θ := by
    rw [hre] at hnorm
    simpa [Complex.norm_real, Real.norm_eq_abs] using hnorm
  have hval : -(ftRootPolyReal c a).eval s / s ^ 1 = ftBranchZ a c 1 (n - 1) θ := by
    field_simp
    linarith [hreal]
  rcases lt_or_gt_of_ne hs0 with hlt | hgt
  · exact hneg θ hθ s hlt (by rwa [abs_of_neg hlt] at hnorms) hval
  · exact absurd hval (ne_of_lt (hpos θ hθ s hgt (by rwa [abs_of_pos hgt] at hnorms)))

end ForgacsTran
