/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.PowerSeries.Log

/-!
# Lagrange--Bürmann inversion for formal power series

Let `u` be a power series with unit constant term, `f = X * u`, and let `g` be a compositional
inverse of `f`. Writing `v` for the inverse of `u`, so that `v = X / f` as a formal quotient:

## Main results

* `Shields.coeff_subst_mul_inv_pow_mul_derivative`: the change-of-variables identity of formal
  residue calculus, `[w ^ m]((F ∘ f) * v ^ (m + 1) * f') = [w ^ m] F`, for every `F`.
* `Shields.lagrange_burmann`: `(m + 1) • [w ^ (m + 1)](H ∘ g) = [w ^ m](H' * v ^ (m + 1))`.
* `Shields.lagrange_burmann_coeff`: the case `H = X`, i.e.
  `(m + 1) • [w ^ (m + 1)] g = [w ^ m] v ^ (m + 1)`.
* `Shields.exists_compInverse`: the compositional inverse exists and again has the form `X * q`.
* `Shields.expOf` and its coefficient identities: the formal exponential of a series with zero
  constant term, over a `ℚ`-algebra.

## Implementation notes

Everything is phrased through `v` rather than through `1 / f`, which has a pole at the origin and is
not a power series. The `IsAddTorsionFree` hypothesis is what lets `(m + 1) •` be canceled; over a
`ℚ`-algebra it is automatic, but stating it this way keeps the coefficient identities available over
`ℤ`-flat bases.

Mathlib has no Lagrange inversion at the pinned revision, and none is in flight.

## Tags

formal power series, Lagrange inversion, Lagrange-Bürmann, compositional inverse, residue
-/

namespace Shields

open PowerSeries

section Residue

variable {A : Type*} [CommRing A] {u v : A⟦X⟧}

/-- Differentiating `u v = 1` gives `v² u' = -v'`.  This is `Derivation.leibniz_of_mul_eq_one`
for the power-series derivation, restated with the product written out and the square on the
side the residue identities use it from. -/
theorem sq_mul_derivative_of_mul_eq_one (huv : u * v = 1) :
    v ^ 2 * d⁄dX A u = -d⁄dX A v := by
  have h := (derivative A).leibniz_of_mul_eq_one (by rw [mul_comm]; exact huv : v * u = 1)
  simp only [smul_eq_mul] at h
  rw [h]; ring

/-- `(X u)' = u + X u'`. -/
theorem derivative_X_mul (u : A⟦X⟧) : d⁄dX A (X * u) = u + X * d⁄dX A u := by
  rw [Derivation.leibniz]
  simp [smul_eq_mul, add_comm]

/-- `X * u` has zero constant coefficient, so it may be substituted into. -/
theorem hasSubst_X_mul (u : A⟦X⟧) : HasSubst (X * u : A⟦X⟧) :=
  HasSubst.of_constantCoeff_zero' (by simp)

/-- Substitution of `X u` into a monomial. -/
theorem subst_C_mul_X_pow (u : A⟦X⟧) (a : A) (k : ℕ) :
    (C a * X ^ k : A⟦X⟧).subst (X * u) = C a * (X * u) ^ k := by
  have hf := hasSubst_X_mul u
  rw [subst_mul hf, subst_pow hf, subst_X hf, subst_C]
  rfl

/-- The `j = 0` case of the residue identity. -/
theorem coeff_zero_inv_mul_derivative (huv : u * v = 1) :
    coeff 0 (v * d⁄dX A (X * u)) = 1 := by
  have h : v * d⁄dX A (X * u) = 1 + X * (v * d⁄dX A u) := by
    rw [derivative_X_mul]; linear_combination huv
  rw [h]; simp

/-- The residue identity cleared of its denominator: `j [w^j](v^{j+1}(Xu)') = 0` for
`j ≥ 1`.  This is `res(dF) = 0` with the Laurent series eliminated. -/
theorem nsmul_coeff_succ_inv_pow_mul_derivative (huv : u * v = 1) (i : ℕ) :
    (i + 1) • coeff (i + 1) (v ^ (i + 1 + 1) * d⁄dX A (X * u)) = 0 := by
  have hs := sq_mul_derivative_of_mul_eq_one huv
  have key : (i + 1) • (v ^ (i + 1 + 1) * d⁄dX A (X * u))
      = (i + 1) • v ^ (i + 1) - X * d⁄dX A (v ^ (i + 1)) := by
    rw [derivative_pow, derivative_X_mul]
    simp only [nsmul_eq_mul, Nat.add_sub_cancel]
    push_cast
    linear_combination ((i : A⟦X⟧) + 1) * v ^ (i + 1) * huv
      + ((i : A⟦X⟧) + 1) * X * v ^ i * hs
  have hc := congrArg (coeff (i + 1)) key
  rw [map_nsmul, map_sub, map_nsmul, coeff_succ_X_mul, coeff_derivative] at hc
  rw [hc, nsmul_eq_mul]
  push_cast
  ring

/-- **The residue identity.**  `[w^j](v^{j+1}(X u)') = 1` if `j = 0` and `0` otherwise.
This is what change of variables in the formal residue reduces to once the Laurent
series are cleared. -/
theorem coeff_inv_pow_mul_derivative [IsAddTorsionFree A] (huv : u * v = 1) (j : ℕ) :
    coeff j (v ^ (j + 1) * d⁄dX A (X * u)) = if j = 0 then 1 else 0 := by
  obtain _ | i := j
  · simpa using coeff_zero_inv_mul_derivative huv
  · rw [if_neg (Nat.succ_ne_zero i)]
    refine IsAddTorsionFree.nsmul_right_injective (n := i + 1) (by omega) ?_
    simpa using nsmul_coeff_succ_inv_pow_mul_derivative huv i

end Residue

section ChangeOfVariables

variable {A : Type*} [CommRing A] [IsAddTorsionFree A] {u v : A⟦X⟧}

/-- Change of variables on the monomials `C a * X^k`. -/
private theorem coeff_cov_monomial (huv : u * v = 1) (a : A) (k m : ℕ) :
    coeff m ((C a * X ^ k : A⟦X⟧).subst (X * u) * v ^ (m + 1) * d⁄dX A (X * u))
      = coeff m (C a * X ^ k : A⟦X⟧) := by
  rw [subst_C_mul_X_pow, mul_pow,
    show (C a * (X ^ k * u ^ k) * v ^ (m + 1) * d⁄dX A (X * u) : A⟦X⟧)
      = C a * (X ^ k * (u ^ k * v ^ (m + 1) * d⁄dX A (X * u))) by ring,
    coeff_C_mul, coeff_C_mul_X_pow, coeff_X_pow_mul']
  rcases le_or_gt k m with hk | hk
  · rw [if_pos hk]
    obtain ⟨j, rfl⟩ : ∃ j, m = k + j := ⟨m - k, by omega⟩
    have hsplit : u ^ k * v ^ (k + j + 1) = v ^ (j + 1) := by
      rw [show v ^ (k + j + 1) = v ^ k * v ^ (j + 1) by ring, ← mul_assoc, ← mul_pow, huv,
        one_pow, one_mul]
    rw [show k + j - k = j by omega, hsplit, coeff_inv_pow_mul_derivative huv j]
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp
    · rw [if_neg (by omega), if_neg (by omega), mul_zero]
  · rw [if_neg (by omega), if_neg (by omega), mul_zero]

/-- Change of variables on polynomials. -/
private theorem coeff_cov_poly (huv : u * v = 1) (p : Polynomial A) (m : ℕ) :
    coeff m ((p : A⟦X⟧).subst (X * u) * v ^ (m + 1) * d⁄dX A (X * u))
      = coeff m (p : A⟦X⟧) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [Polynomial.coe_add, subst_add (hasSubst_X_mul u), add_mul, add_mul, map_add, map_add,
      hp, hq]
  | monomial k a =>
    have hm : ((Polynomial.monomial k a : Polynomial A) : A⟦X⟧) = C a * X ^ k := by
      rw [Polynomial.coe_monomial]
      ext n
      rw [coeff_monomial, coeff_C_mul_X_pow]
    rw [hm]
    exact coeff_cov_monomial huv a k m

/-- **Change of variables in the formal residue.**  For every `F`,
`[w^m]((F ∘ f) · v^{m+1} · f') = [w^m] F`, where `f = X u` and `u v = 1`.

In residue notation this is `res(H(f) f') = res(H)` for `H = F · w^{-(m+1)}`; the factor
`w^{-(m+1)}` has been cleared, which is why only power series appear. -/
theorem coeff_subst_mul_inv_pow_mul_derivative (huv : u * v = 1) (F : A⟦X⟧) (m : ℕ) :
    coeff m (F.subst (X * u) * v ^ (m + 1) * d⁄dX A (X * u)) = coeff m F := by
  have hf := hasSubst_X_mul u
  obtain ⟨G, hG⟩ : (X : A⟦X⟧) ^ (m + 1) ∣ F - ((trunc (m + 1) F : Polynomial A) : A⟦X⟧) := by
    rw [X_pow_dvd_iff]
    intro k hk
    rw [map_sub, coeff_coe_trunc_of_lt hk, sub_self]
  have hFsplit : F = ((trunc (m + 1) F : Polynomial A) : A⟦X⟧) + X ^ (m + 1) * G := by
    rw [← hG]; ring
  have hvanish : ∀ Q : A⟦X⟧, coeff m ((X : A⟦X⟧) ^ (m + 1) * Q) = 0 := fun Q => by
    rw [coeff_X_pow_mul', if_neg (by omega)]
  rw [hFsplit, subst_add hf, subst_mul hf, subst_pow hf, subst_X hf, add_mul, add_mul,
    map_add, map_add, coeff_cov_poly huv,
    show ((X * u : A⟦X⟧) ^ (m + 1) * G.subst (X * u) * v ^ (m + 1) * d⁄dX A (X * u))
      = X ^ (m + 1) * (u ^ (m + 1) * G.subst (X * u) * v ^ (m + 1) * d⁄dX A (X * u)) by ring,
    hvanish, hvanish, add_zero]

end ChangeOfVariables

section Inversion

variable {A : Type*} [CommRing A] [IsAddTorsionFree A] {u v g : A⟦X⟧}

/-- **Lagrange--Bürmann inversion, strong form.**  If `f = X u` with `u v = 1` and `g` is
a compositional inverse of `f`, then for every `H`,

    (m+1) • [w^{m+1}] (H ∘ g)  =  [w^m] (H' · v^{m+1}),

or, in classical notation, `n [w^n] H(g(w)) = [t^{n-1}](H'(t) (t/f(t))^n)`, the formal
quotient `t/f(t)` being the power series `v`. -/
theorem lagrange_burmann (huv : u * v = 1) (hg0 : constantCoeff g = 0)
    (hg : g.subst (X * u) = X) (H : A⟦X⟧) (m : ℕ) :
    (m + 1) • coeff (m + 1) (H.subst g) = coeff m (d⁄dX A H * v ^ (m + 1)) := by
  have hf := hasSubst_X_mul u
  have hgs : HasSubst g := HasSubst.of_constantCoeff_zero' hg0
  -- `(g' ∘ f) · f' = (g ∘ f)' = 1`
  have hchain : (d⁄dX A g).subst (X * u) * d⁄dX A (X * u) = 1 := by
    rw [← derivative_subst hf, hg, derivative_X]
  -- the derivative of `H ∘ g`, pushed through change of variables
  have hcov := coeff_subst_mul_inv_pow_mul_derivative huv
    ((d⁄dX A H).subst g * d⁄dX A g) m
  rw [subst_mul hf, subst_comp_subst_apply hgs hf, hg, X_subst,
    show ((d⁄dX A H) * (d⁄dX A g).subst (X * u) * v ^ (m + 1) * d⁄dX A (X * u) : A⟦X⟧)
      = d⁄dX A H * v ^ (m + 1) * ((d⁄dX A g).subst (X * u) * d⁄dX A (X * u)) by ring,
    hchain, mul_one] at hcov
  rw [hcov, ← derivative_subst hgs, coeff_derivative, nsmul_eq_mul]
  push_cast
  ring

/-- **Lagrange--Bürmann inversion.**  With `f = X u`, `u v = 1` and `g` a compositional
inverse of `f`,

    (m+1) • [w^{m+1}] g  =  [w^m] v^{m+1},

classically `n [w^n] g = [t^{n-1}](t/f(t))^n`. -/
theorem lagrange_burmann_coeff (huv : u * v = 1) (hg0 : constantCoeff g = 0)
    (hg : g.subst (X * u) = X) (m : ℕ) :
    (m + 1) • coeff (m + 1) g = coeff m (v ^ (m + 1)) := by
  have h := lagrange_burmann huv hg0 hg X m
  rwa [subst_X (HasSubst.of_constantCoeff_zero' hg0), derivative_X, one_mul] at h

omit [IsAddTorsionFree A] in
/-- The inversion hypotheses are satisfiable.  If `constantCoeff u` is a unit then `X u`
has a compositional inverse in both directions, and that inverse again has the form
`X q`. -/
theorem exists_compInverse (u : A⟦X⟧) (hu : IsUnit (constantCoeff u)) :
    ∃ q : A⟦X⟧, (X * q).subst (X * u) = X ∧ (X * u).subst (X * q) = X := by
  have h0 : constantCoeff (X * u : A⟦X⟧) = 0 := by simp
  have h1 : IsUnit (coeff 1 (X * u : A⟦X⟧)) := by
    rwa [coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply]
  obtain ⟨q, hq⟩ : (X : A⟦X⟧) ∣ substInvOfIsUnit (X * u) h1 := by
    rw [X_dvd_iff]
    exact constantCoeff_substInvOfIsUnit _ h1
  refine ⟨q, ?_, ?_⟩
  · rw [← hq]; exact subst_substInvOfIsUnit_left (X * u) h0 h1
  · rw [← hq]; exact subst_substInvOfIsUnit_right (X * u) h0 h1

end Inversion

section Exponential

variable {A : Type*} [CommRing A] [Algebra ℚ A] {a b c : A⟦X⟧}

/-- Substituting a series with zero constant term does not move the constant term. -/
theorem constantCoeff_subst_eq {A : Type*} [CommRing A] {a : A⟦X⟧} (ha : constantCoeff a = 0)
    (F : A⟦X⟧) : constantCoeff (F.subst a) = constantCoeff F := by
  have has : HasSubst a := HasSubst.of_constantCoeff_zero' ha
  have ha' : MvPowerSeries.constantCoeff (a : A⟦X⟧) = 0 := by
    rw [← constantCoeff_eq]; exact ha
  have hz : MvPowerSeries.constantCoeff (F - C (constantCoeff F) : A⟦X⟧) = 0 := by
    rw [← constantCoeff_eq]; simp
  have hkey : constantCoeff ((F - C (constantCoeff F)).subst a) = 0 := by
    rw [constantCoeff_eq]; exact constantCoeff_subst_eq_zero ha' _ hz
  have hsplit : F = C (constantCoeff F) + (F - C (constantCoeff F)) := by ring
  nth_rewrite 1 [hsplit]
  rw [subst_add has, map_add, hkey, add_zero, subst_C]
  exact constantCoeff_C _

/-- `e^c`, the exponential of a power series with zero constant term. -/
noncomputable def expOf (c : A⟦X⟧) : A⟦X⟧ := (exp A).subst c

theorem constantCoeff_expOf (hc : constantCoeff c = 0) : constantCoeff (expOf c) = 1 := by
  rw [expOf, constantCoeff_subst_eq hc, constantCoeff_exp]

/-- `(e^c)' = e^c c'`. -/
theorem derivative_expOf (hc : constantCoeff c = 0) :
    d⁄dX A (expOf c) = expOf c * d⁄dX A c := by
  rw [expOf, derivative_subst (HasSubst.of_constantCoeff_zero' hc), derivative_exp]

variable [IsAddTorsionFree A]

theorem expOf_zero : expOf (0 : A⟦X⟧) = 1 := by
  refine derivative.ext ?_ ?_
  · rw [derivative_expOf (by simp), map_zero, mul_zero, derivative_one]
  · rw [constantCoeff_expOf (by simp), map_one]

/-- `e^a e^{-a} = 1`. -/
theorem expOf_mul_expOf_neg (ha : constantCoeff a = 0) :
    expOf a * expOf (-a) = 1 := by
  have hna : constantCoeff (-a) = 0 := by simp [ha]
  refine derivative.ext ?_ ?_
  · rw [Derivation.leibniz, derivative_expOf ha, derivative_expOf hna, derivative_one]
    simp only [smul_eq_mul, map_neg]
    ring
  · rw [map_mul, constantCoeff_expOf ha, constantCoeff_expOf hna, map_one, one_mul]

/-- `e^{a+b} = e^a e^b`. -/
theorem expOf_add (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) :
    expOf (a + b) = expOf a * expOf b := by
  have hna : constantCoeff (-a) = 0 := by simp [ha]
  have hnb : constantCoeff (-b) = 0 := by simp [hb]
  have hab : constantCoeff (a + b) = 0 := by simp [ha, hb]
  have hW : expOf (a + b) * (expOf (-a) * expOf (-b)) = 1 := by
    refine derivative.ext ?_ ?_
    · rw [Derivation.leibniz, Derivation.leibniz, derivative_expOf hab, derivative_expOf hna,
        derivative_expOf hnb, derivative_one]
      simp only [smul_eq_mul, map_neg, map_add]
      ring
    · rw [map_mul, map_mul, constantCoeff_expOf hab, constantCoeff_expOf hna,
        constantCoeff_expOf hnb, map_one]
      ring
  have h1 := expOf_mul_expOf_neg ha
  have h2 := expOf_mul_expOf_neg hb
  linear_combination (expOf a * expOf b) * hW
    - (expOf (a + b) * expOf b * expOf (-b)) * h1 - expOf (a + b) * h2

/-- `e^{n c} = (e^c)^n`. -/
theorem expOf_nsmul (hc : constantCoeff c = 0) (n : ℕ) :
    expOf (n • c) = expOf c ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero, expOf_zero]
  | succ n ih => rw [succ_nsmul, expOf_add (by simp [hc]) hc, ih, pow_succ]

end Exponential

section ExpCoefficients

variable {A : Type*} [CommRing A] [Algebra ℚ A] {c : A⟦X⟧}

omit [Algebra ℚ A] in
theorem coeff_mul_range (F G : A⟦X⟧) (n : ℕ) :
    coeff n (F * G) = ∑ i ∈ Finset.range (n + 1), coeff i F * coeff (n - i) G := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

theorem coeff_zero_expOf (hc : constantCoeff c = 0) : coeff 0 (expOf c) = 1 := by
  rw [coeff_zero_eq_constantCoeff_apply, constantCoeff_expOf hc]

/-- The recursion `(m+1)[w^{m+1}]e^c = ∑_{i ≤ m} [w^i]e^c · (m-i+1)[w^{m-i+1}]c`, from
`(e^c)' = e^c c'`. -/
theorem coeff_succ_expOf (hc : constantCoeff c = 0) (m : ℕ) :
    coeff (m + 1) (expOf c) * (m + 1)
      = ∑ i ∈ Finset.range (m + 1),
          coeff i (expOf c) * (coeff (m - i + 1) c * ((m - i : ℕ) + 1)) := by
  have h := congrArg (coeff m) (derivative_expOf hc)
  rw [coeff_derivative, coeff_mul_range] at h
  simpa only [coeff_derivative] using h

theorem coeff_one_expOf (hc : constantCoeff c = 0) :
    coeff 1 (expOf c) = coeff 1 c := by
  have h := coeff_succ_expOf hc 0
  simpa [coeff_zero_expOf hc] using h

theorem coeff_two_expOf (hc : constantCoeff c = 0) :
    2 * coeff 2 (expOf c) = 2 * coeff 2 c + coeff 1 c ^ 2 := by
  have h := coeff_succ_expOf hc 1
  rw [Finset.sum_range_succ, Finset.sum_range_one, coeff_zero_expOf hc,
    coeff_one_expOf hc] at h
  push_cast at h
  linear_combination h

theorem coeff_three_expOf (hc : constantCoeff c = 0) :
    6 * coeff 3 (expOf c)
      = 6 * coeff 3 c + 6 * coeff 1 c * coeff 2 c + coeff 1 c ^ 3 := by
  have h := coeff_succ_expOf hc 2
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
    coeff_zero_expOf hc, coeff_one_expOf hc] at h
  push_cast at h
  linear_combination 2 * h + coeff 1 c * coeff_two_expOf hc

theorem coeff_four_expOf (hc : constantCoeff c = 0) :
    24 * coeff 4 (expOf c)
      = 24 * coeff 4 c + 24 * coeff 1 c * coeff 3 c + 12 * coeff 2 c ^ 2
        + 12 * coeff 1 c ^ 2 * coeff 2 c + coeff 1 c ^ 4 := by
  have h := coeff_succ_expOf hc 3
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one, coeff_zero_expOf hc, coeff_one_expOf hc] at h
  push_cast at h
  linear_combination 6 * h + (6 * coeff 2 c) * coeff_two_expOf hc
    + coeff 1 c * coeff_three_expOf hc

end ExpCoefficients


/-! ### Uniqueness of the compositional inverse, and dilations

A compositional inverse is unique, and a dilation of the series dilates the inverse by the
reciprocal constant.  On the logarithmic-derivative side the constant is invisible, which is what
makes any invariant built from `q'q^{-1}` blind to a dilation.
-/

section Uniqueness

variable {A : Type*} [CommRing A]

/-- **The compositional inverse is unique.**  If `χ` is a left inverse of `h` and `a` is a right
inverse, then `a = χ`: substituting `a` into `χ.subst h = X` gives `a` on the left by
associativity and `χ` on the right by `h.subst a = X`. -/
theorem subst_eq_of_subst_eq_X {h a χ : A⟦X⟧} (ha : HasSubst a) (hh : HasSubst h)
    (h1 : h.subst a = X) (h2 : χ.subst h = X) : a = χ := by
  have hcomp := subst_comp_subst_apply hh ha χ
  rw [h2, h1, subst_X ha, X_subst] at hcomp
  exact hcomp

/-- Substituting `a` into a rescaled series is substituting the rescaled `a`. -/
theorem subst_rescale (c : A) (F : A⟦X⟧) {a : A⟦X⟧} (ha : HasSubst a) :
    (rescale c F).subst a = F.subst (c • a) := by
  rw [rescale_eq_subst, subst_comp_subst_apply (HasSubst.smul_X' c) ha F, subst_smul ha,
    subst_X ha]

/-- **A dilation acts on the compositional inverse by a scalar.**  If `h_f(t) = h_g(ct)` then
`χ_g = cχ_f`. -/
theorem inverse_eq_smul_of_rescale {c : A} {hf hg χf χg : A⟦X⟧} (hχf : HasSubst χf)
    (hhg : HasSubst hg) (hres : hf = rescale c hg) (h1 : hf.subst χf = X)
    (h2 : χg.subst hg = X) : c • χf = χg := by
  have hsub : HasSubst (c • χf : A⟦X⟧) := by
    rw [smul_eq_C_mul]
    exact HasSubst.mul_right hχf
  refine subst_eq_of_subst_eq_X hsub hhg ?_ h2
  rw [← subst_rescale c hg hχf, ← hres, h1]

/-- The converse. -/
theorem rescale_of_inverse_eq_smul {c : A} {hf hg χf : A⟦X⟧} (hχf : HasSubst χf)
    (hhf : HasSubst hf) (hfl : χf.subst hf = X) (h2 : hg.subst (c • χf) = X) :
    hf = rescale c hg := by
  refine subst_eq_of_subst_eq_X hhf hχf hfl ?_
  rw [subst_rescale c hg hχf, h2]

end Uniqueness

section LogDeriv

variable {A : Type*} [CommRing A]

/-- Inverses are unique, so a constant factor on `q` puts the reciprocal factor on `p`. -/
theorem inv_eq_of_C_mul {c c' : A} (hc : c * c' = 1) {qf qg pf pg : A⟦X⟧}
    (hqf : qf * pf = 1) (hqg : qg * pg = 1) (hq : qg = C c * qf) : pg = C (c') * pf := by
  have halt : qg * (C c' * pf) = 1 := by
    rw [hq]
    calc C c * qf * (C c' * pf) = (C c * C c') * (qf * pf) := by ring
      _ = 1 := by rw [← map_mul, hc, map_one, hqf, mul_one]
  calc pg = pg * (qg * (C c' * pf)) := by rw [halt, mul_one]
    _ = (qg * pg) * (C c' * pf) := by ring
    _ = C c' * pf := by rw [hqg, one_mul]

/-- **A logarithmic derivative does not see a constant factor.**  The `C c` on `q'` and the
`C c'` on `p` cancel outright, so `(cq)'(cq)^{-1} = q'q^{-1}` exactly. -/
theorem logDeriv_eq_of_C_mul {c c' : A} (hc : c * c' = 1) {qf qg pf pg : A⟦X⟧}
    (hqf : qf * pf = 1) (hqg : qg * pg = 1) (hq : qg = C c * qf) :
    d⁄dX A qg * pg = d⁄dX A qf * pf := by
  have hp := inv_eq_of_C_mul hc hqf hqg hq
  have hd : d⁄dX A qg = C c * d⁄dX A qf := by
    rw [hq, Derivation.leibniz]
    simp
  rw [hd, hp]
  calc C c * d⁄dX A qf * (C c' * pf) = (C c * C c') * (d⁄dX A qf * pf) := by ring
    _ = d⁄dX A qf * pf := by rw [← map_mul, hc, map_one, one_mul]

variable [IsAddTorsionFree A]

/-- Over a torsion-free ring a formal power series with vanishing derivative is its own constant
term.  Both sides have derivative zero and the same constant term, which is what
`PowerSeries.derivative.ext` asks for. -/
theorem eq_C_of_derivative_eq_zero {F : A⟦X⟧} (h : d⁄dX A F = 0) : F = C (constantCoeff F) :=
  PowerSeries.derivative.ext (by simp [h]) (by simp)

/-- **Conversely, equal logarithmic derivatives force a constant factor.**  The quotient
`q_g p_f` has zero derivative, hence is constant; multiplying back by `q_f` gives
`q_g = C c · q_f`, with `c` read off the constant terms.

The leading capital is `PowerSeries.C`, the constant-coefficient embedding, exactly as in
Mathlib's own `PowerSeries.C_eq_zero` and `Polynomial.C_mul`. -/
theorem C_mul_of_logDeriv_eq {qf qg pf pg : A⟦X⟧} (hqf : qf * pf = 1) (hqg : qg * pg = 1)
    (hlog : d⁄dX A qg * pg = d⁄dX A qf * pf) :
    qg = C (constantCoeff (qg * pf)) * qf := by
  have hpf : d⁄dX A pf = -(d⁄dX A qf * pf * pf) := by
    have h0 : d⁄dX A (qf * pf) = 0 := by rw [hqf]; simp
    rw [Derivation.leibniz] at h0
    simp only [smul_eq_mul] at h0
    have := congrArg (fun z => z * pf) h0
    simp only [zero_mul] at this
    have hcancel : qf * d⁄dX A pf * pf = d⁄dX A pf := by
      calc qf * d⁄dX A pf * pf = (qf * pf) * d⁄dX A pf := by ring
        _ = d⁄dX A pf := by rw [hqf, one_mul]
    linear_combination this - hcancel
  have hqg' : d⁄dX A qg = d⁄dX A qf * pf * qg := by
    calc d⁄dX A qg = d⁄dX A qg * (qg * pg) := by rw [hqg, mul_one]
      _ = (d⁄dX A qg * pg) * qg := by ring
      _ = d⁄dX A qf * pf * qg := by rw [hlog]
  have hF : d⁄dX A (qg * pf) = 0 := by
    rw [Derivation.leibniz]
    simp only [smul_eq_mul]
    rw [hpf, hqg']
    ring
  have hconst := eq_C_of_derivative_eq_zero hF
  calc qg = qg * (pf * qf) := by rw [mul_comm pf qf, hqf, mul_one]
    _ = (qg * pf) * qf := by ring
    _ = C (constantCoeff (qg * pf)) * qf := congrArg (· * qf) hconst

end LogDeriv


/-! ### Axiom footprint -/

/-- info: 'Shields.lagrange_burmann_coeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lagrange_burmann_coeff

/-- info: 'Shields.exists_compInverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_compInverse

/-- info: 'Shields.expOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms expOf

end Shields
