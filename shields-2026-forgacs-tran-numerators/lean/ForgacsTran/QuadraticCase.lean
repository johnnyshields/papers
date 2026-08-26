/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.Amplitude

/-!
# The quadratic case

At `deg Q = 2`, `r = 1` the pencil is `q₂t² + (q₁+z)t + q₀` and everything the
general theory imports from `Forgacs2017RationalDenominator` can be written down
instead: the principal pair is explicit, `τ` is constant, `z(θ)` is elementary
and strictly increasing, and both endpoint collisions are exactly double.  This
is the configuration `thm:FT-geometry` excludes, so nothing here may lean on it.

## Main statements

* `quadDen_eval_principal` — `t_±(θ) = τ e^{±iθ}` with `τ = √(q₀/q₂)` constant and
  `z(θ) = -q₁ - 2√(q₀q₂) cos θ` are denominator zeros, at every angle.
* `quadDen_eq_sq_lower`, `quadDen_eq_sq_upper` — at either endpoint the pencil is
  a perfect square `q₂(t ∓ τ)²`, so each collision is exactly double and the
  principal pair exhausts the denominator zeros.
* `quadratic_z_strictMonoOn` — `z` strictly increasing on `[0,π]`, which is what
  fixes `I_{Q,1} = (-q₁-2√(q₀q₂), -q₁+2√(q₀q₂))`.
* `card_Ioo_ge_of_card_Icc` — the remark's "hence at least `M-K-2` in
  `I_{Q,1}`": passing from the closed interval to the open one costs at most the
  two endpoints.

## Implementation notes

`quadPoly_coeff` is `private`, so it is **not addressable from `AxiomCheck`** — a
`#print axioms` there cannot name it.  Its axiom footprint is pinned transitively, through the
guarded results that consume it, and that is the only route available for a private
declaration.  Do not read the absent guard as a gap in the sweep.

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Forgács--Tran geometry
and endpoint separation» (`sec:geometry`, `subsec:FT-geometry`,
`rem:quadratic-case`).

## Tags

quadratic case, denominator pencil, real-rootedness
-/

namespace ForgacsTran

open Polynomial Real

/-- `rem:quadratic-case` — `Q(t) = q₀ + q₁t + q₂t²`, promoted to `ℂ[X]`. -/
noncomputable def quadPoly (q0 q1 q2 : ℝ) : Polynomial ℂ :=
  C ((q0 : ℝ) : ℂ) + C ((q1 : ℝ) : ℂ) * X + C ((q2 : ℝ) : ℂ) * X ^ 2

@[simp] theorem quadPoly_eval (q0 q1 q2 : ℝ) (t : ℂ) :
    (quadPoly q0 q1 q2).eval t = (q0 : ℂ) + (q1 : ℂ) * t + (q2 : ℂ) * t ^ 2 := by
  simp [quadPoly]

/-- `q₂τ² = q₀` and `q₂τ = √(q₀q₂)` for `τ = √(q₀/q₂)`. -/
private theorem quad_tau_facts {q0 q2 : ℝ} (hq0 : 0 < q0) (hq2 : 0 < q2) :
    q2 * Real.sqrt (q0 / q2) ^ 2 = q0 ∧
      q2 * Real.sqrt (q0 / q2) = Real.sqrt (q0 * q2) := by
  have hdiv : (0 : ℝ) ≤ q0 / q2 := by positivity
  refine ⟨by rw [Real.sq_sqrt hdiv]; field_simp, ?_⟩
  have h1 : (0 : ℝ) ≤ q2 * Real.sqrt (q0 / q2) := by positivity
  have h2 : (q2 * Real.sqrt (q0 / q2)) ^ 2 = q0 * q2 := by
    rw [mul_pow, Real.sq_sqrt hdiv]; field_simp
  rw [← h2, Real.sqrt_sq h1]

/-- **`rem:quadratic-case`, the principal pair.**  For every angle `θ`, the point
`τ e^{iθ}` with the *constant* `τ = √(q₀/q₂)` is a zero of the pencil at
`z(θ) = -q₁ - 2√(q₀q₂) cos θ`.  Constancy of `τ` is exactly why
`thm:FT-geometry` excludes `(deg Q, r) = (2,1)`. -/
theorem quadDen_eval_principal {q0 q1 q2 : ℝ} (hq0 : 0 < q0) (hq2 : 0 < q2) (θ : ℝ) :
    (ftDen (quadPoly q0 q1 q2) 1
        (((-q1 - 2 * Real.sqrt (q0 * q2) * Real.cos θ : ℝ)) : ℂ)).eval
      (((Real.sqrt (q0 / q2) : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) = 0 := by
  obtain ⟨hτ2, hτs⟩ := quad_tau_facts hq0 hq2
  set E : ℂ := Complex.exp ((θ : ℂ) * Complex.I) with hE
  set F : ℂ := Complex.exp (-(θ : ℂ) * Complex.I) with hF
  set τ : ℝ := Real.sqrt (q0 / q2) with hτdef
  have hEF : E * F = 1 := by rw [hE, hF, ← Complex.exp_add]; simp
  have hsum : E + F = 2 * ((Real.cos θ : ℝ) : ℂ) := by
    rw [hE, hF, Complex.exp_mul_I,
      show -(θ : ℂ) * Complex.I = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  have hq2τ : ((q2 : ℝ) : ℂ) * ((τ : ℝ) : ℂ) ^ 2 = ((q0 : ℝ) : ℂ) := by exact_mod_cast hτ2
  rw [ftDen_eval, quadPoly_eval, pow_one]
  have hgoal : ((q0 : ℝ) : ℂ) + ((q1 : ℝ) : ℂ) * (((τ : ℝ) : ℂ) * E)
      + ((q2 : ℝ) : ℂ) * (((τ : ℝ) : ℂ) * E) ^ 2
      + ((-q1 - 2 * Real.sqrt (q0 * q2) * Real.cos θ : ℝ) : ℂ) * (((τ : ℝ) : ℂ) * E)
      = E * (((q0 : ℝ) : ℂ) * (E + F)
          - 2 * ((Real.sqrt (q0 * q2) : ℝ) : ℂ) * ((Real.cos θ : ℝ) : ℂ) * ((τ : ℝ) : ℂ)) := by
    have h1 : ((q2 : ℝ) : ℂ) * (((τ : ℝ) : ℂ) * E) ^ 2 = ((q0 : ℝ) : ℂ) * E ^ 2 := by
      rw [mul_pow, ← mul_assoc, hq2τ]
    rw [h1]
    push_cast
    linear_combination (-((q0 : ℝ) : ℂ)) * hEF
  rw [hgoal, hsum]
  have hsq : ((Real.sqrt (q0 * q2) : ℝ) : ℂ) * ((τ : ℝ) : ℂ) = ((q0 : ℝ) : ℂ) := by
    have hq : Real.sqrt (q0 * q2) * τ = q0 := by rw [← hτs]; linear_combination hτ2
    exact_mod_cast hq
  linear_combination E * (-2 * ((Real.cos θ : ℝ) : ℂ)) * hsq

/-- **`rem:quadratic-case`, the lower endpoint.**  At `z = -q₁-2√(q₀q₂)` the
pencil is `q₂(t-τ)²`, so the collision there is exactly double. -/
theorem quadDen_eq_sq_lower {q0 q1 q2 : ℝ} (hq0 : 0 < q0) (hq2 : 0 < q2) :
    ftDen (quadPoly q0 q1 q2) 1 (((-q1 - 2 * Real.sqrt (q0 * q2) : ℝ)) : ℂ)
      = C ((q2 : ℝ) : ℂ) * (X - C (((Real.sqrt (q0 / q2) : ℝ)) : ℂ)) ^ 2 := by
  obtain ⟨hτ2, hτs⟩ := quad_tau_facts hq0 hq2
  refine Polynomial.funext fun t => ?_
  simp only [ftDen_eval, quadPoly_eval, eval_mul, eval_C, eval_pow, eval_sub, eval_X, pow_one]
  have hA : ((q2 : ℝ) : ℂ) * ((Real.sqrt (q0 / q2) : ℝ) : ℂ) ^ 2 = ((q0 : ℝ) : ℂ) := by
    exact_mod_cast hτ2
  have hB : ((q2 : ℝ) : ℂ) * ((Real.sqrt (q0 / q2) : ℝ) : ℂ)
      = ((Real.sqrt (q0 * q2) : ℝ) : ℂ) := by exact_mod_cast hτs
  push_cast
  linear_combination -hA + (2 * t) * hB

/-- **`rem:quadratic-case`, the upper endpoint.**  At `z = -q₁+2√(q₀q₂)` the
pencil is `q₂(t+τ)²`: again exactly double. -/
theorem quadDen_eq_sq_upper {q0 q1 q2 : ℝ} (hq0 : 0 < q0) (hq2 : 0 < q2) :
    ftDen (quadPoly q0 q1 q2) 1 (((-q1 + 2 * Real.sqrt (q0 * q2) : ℝ)) : ℂ)
      = C ((q2 : ℝ) : ℂ) * (X + C (((Real.sqrt (q0 / q2) : ℝ)) : ℂ)) ^ 2 := by
  obtain ⟨hτ2, hτs⟩ := quad_tau_facts hq0 hq2
  refine Polynomial.funext fun t => ?_
  simp only [ftDen_eval, quadPoly_eval, eval_mul, eval_C, eval_pow, eval_add, eval_X, pow_one]
  have hA : ((q2 : ℝ) : ℂ) * ((Real.sqrt (q0 / q2) : ℝ) : ℂ) ^ 2 = ((q0 : ℝ) : ℂ) := by
    exact_mod_cast hτ2
  have hB : ((q2 : ℝ) : ℂ) * ((Real.sqrt (q0 / q2) : ℝ) : ℂ)
      = ((Real.sqrt (q0 * q2) : ℝ) : ℂ) := by exact_mod_cast hτs
  push_cast
  linear_combination -hA - (2 * t) * hB

/-- **`rem:quadratic-case`, `z` strictly increasing.**  `z(θ) = -q₁ - 2√(q₀q₂)cos θ`
is strictly increasing on `[0,π]`, so it carries that interval bijectively onto
`[-q₁-2√(q₀q₂), -q₁+2√(q₀q₂)]` and `I_{Q,1}` is its interior. -/
theorem quadratic_z_strictMonoOn {q0 q2 : ℝ} (hq0 : 0 < q0) (hq2 : 0 < q2) (q1 : ℝ) :
    StrictMonoOn (fun θ => -q1 - 2 * Real.sqrt (q0 * q2) * Real.cos θ) (Set.Icc 0 π) := by
  have hs : 0 < Real.sqrt (q0 * q2) := Real.sqrt_pos.mpr (by positivity)
  intro x hx y hy hxy
  have hcos : Real.cos y < Real.cos x := Real.strictAntiOn_cos hx hy hxy
  simp only
  nlinarith [hcos, hs]

/-- **`rem:quadratic-case`, the endpoint concession.**  Shohat's theorem places
the guaranteed sign changes in the *closed* interval; passing to the open one
loses at most the two endpoints. -/
theorem card_Ioo_ge_of_card_Icc {S : Finset ℝ} {a b : ℝ} {n : ℕ}
    (h : n ≤ S.card) (hsub : ∀ x ∈ S, x ∈ Set.Icc a b) :
    n - 2 ≤ (S.filter (fun x => a < x ∧ x < b)).card := by
  classical
  have hsub2 : S ⊆ S.filter (fun x => a < x ∧ x < b) ∪ ({a, b} : Finset ℝ) := by
    intro x hxS
    by_cases hc : a < x ∧ x < b
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hxS, hc⟩)
    · refine Finset.mem_union_right _ ?_
      obtain ⟨hxa, hxb⟩ := hsub x hxS
      simp only [not_and_or, not_lt] at hc
      rcases hc with h1 | h1
      · simp [le_antisymm h1 hxa]
      · simp [le_antisymm hxb h1]
  have hab2 : ({a, b} : Finset ℝ).card ≤ 2 := by
    simpa using Finset.card_insert_le a {b}
  have hcard : S.card ≤ (S.filter (fun x => a < x ∧ x < b)).card + 2 := by
    calc S.card ≤ (S.filter (fun x => a < x ∧ x < b) ∪ ({a, b} : Finset ℝ)).card :=
          Finset.card_le_card hsub2
      _ ≤ (S.filter (fun x => a < x ∧ x < b)).card + ({a, b} : Finset ℝ).card :=
          Finset.card_union_le _ _
      _ ≤ (S.filter (fun x => a < x ∧ x < b)).card + 2 := by omega
  omega


/-! ### The Favard branch: `p_m`, Chebyshev, and the orthogonal-polynomial zeros -/

/-- **`rem:quadratic-case`, `Q2`.**  The Favard normalization `p_m = q₀(-q₀)^m H_m`
of the denominator-only sequence, given by its monic three-term recurrence
`p_m = (z+q₁)p_{m-1} - q₀q₂ p_{m-2}`.
**Differs from the paper's route.**  `rem:quadratic-case` defines `p_m = q₀(-q₀)^m H_m` from the
generating function and derives the recurrence.  Here the recurrence is the
definition and the identification with `q₀(-q₀)^m H_m` is proved, in
`quadFavard_eval_eq_coeffPoly`; monicity and degree are then available by
induction before any coefficient extraction.
-/
noncomputable def quadFavard (q0 q1 q2 : ℝ) : ℕ → Polynomial ℝ
  | 0 => 1
  | 1 => X + C q1
  | (m + 2) => (X + C q1) * quadFavard q0 q1 q2 (m + 1) - C (q0 * q2) * quadFavard q0 q1 q2 m

@[simp] theorem quadFavard_zero (q0 q1 q2 : ℝ) : quadFavard q0 q1 q2 0 = 1 := rfl

@[simp] theorem quadFavard_one (q0 q1 q2 : ℝ) : quadFavard q0 q1 q2 1 = X + C q1 := rfl

theorem quadFavard_add_two (q0 q1 q2 : ℝ) (m : ℕ) :
    quadFavard q0 q1 q2 (m + 2)
      = (X + C q1) * quadFavard q0 q1 q2 (m + 1) - C (q0 * q2) * quadFavard q0 q1 q2 m := rfl

/-- **`rem:quadratic-case`, `Q2`.**  Each `p_m` is monic of degree `m` — the
Favard normalization is what makes the pencil's denominator sequence a monic
orthogonal-polynomial system. -/
theorem quadFavard_monic_natDegree (q0 q1 q2 : ℝ) : ∀ m : ℕ,
    (quadFavard q0 q1 q2 m).Monic ∧ (quadFavard q0 q1 q2 m).natDegree = m := by
  have key : ∀ m : ℕ,
      ((quadFavard q0 q1 q2 m).Monic ∧ (quadFavard q0 q1 q2 m).natDegree = m) ∧
      ((quadFavard q0 q1 q2 (m + 1)).Monic ∧ (quadFavard q0 q1 q2 (m + 1)).natDegree = m + 1) := by
    intro m
    induction m with
    | zero =>
      refine ⟨⟨monic_one, by simp⟩, ⟨monic_X_add_C q1, by simp⟩⟩
    | succ n ih =>
      obtain ⟨⟨hmn, hdn⟩, ⟨hmn1, hdn1⟩⟩ := ih
      refine ⟨⟨hmn1, hdn1⟩, ?_⟩
      have hmul : ((X + C q1) * quadFavard q0 q1 q2 (n + 1)).Monic := (monic_X_add_C q1).mul hmn1
      have hdmul : ((X + C q1) * quadFavard q0 q1 q2 (n + 1)).natDegree = n + 2 := by
        rw [(monic_X_add_C q1).natDegree_mul hmn1, natDegree_X_add_C, hdn1]
        omega
      have hdC : (-(C (q0 * q2) * quadFavard q0 q1 q2 n)).natDegree ≤ n := by
        rw [natDegree_neg]
        refine le_trans (natDegree_mul_le) ?_
        rw [natDegree_C, hdn]
        omega
      have hdeg : (-(C (q0 * q2) * quadFavard q0 q1 q2 n)).degree
          < ((X + C q1) * quadFavard q0 q1 q2 (n + 1)).degree := by
        refine degree_lt_degree ?_
        rw [hdmul]
        omega
      have hres : quadFavard q0 q1 q2 (n + 2)
          = (X + C q1) * quadFavard q0 q1 q2 (n + 1) + -(C (q0 * q2) * quadFavard q0 q1 q2 n) := by
        rw [quadFavard_add_two]; ring
      refine ⟨by rw [hres]; exact hmul.add_of_left hdeg, ?_⟩
      rw [hres, natDegree_add_eq_left_of_degree_lt hdeg, hdmul]
  exact fun m => (key m).1

/-- **`rem:quadratic-case`, `Q3`.**  `p_m(z) = (q₀q₂)^{m/2} U_m((z+q₁)/(2√(q₀q₂)))`,
written with `s = √(q₀q₂)` so the half-power is `s^m`.  This is the classical
quasi-orthogonal identification: the denominator sequence is a rescaled
Chebyshev system of the second kind.
**Differs from the paper's route.**  The paper writes the constant as `(q₀q₂)^{m/2}`.  Here it is
`s^m`
for `s = √(q₀q₂)` — the same number, but a natural-number power, so the
induction on the Chebyshev recurrence runs in `Monoid.npow` and no `rpow` or
parity split on `m` is needed.
-/
theorem quadFavard_eval_eq_chebyshev {q0 q2 : ℝ} (hq0 : 0 < q0) (hq2 : 0 < q2) (q1 : ℝ)
    (m : ℕ) (z : ℝ) :
    (quadFavard q0 q1 q2 m).eval z
      = Real.sqrt (q0 * q2) ^ m
        * (Polynomial.Chebyshev.U ℝ (m : ℤ)).eval ((z + q1) / (2 * Real.sqrt (q0 * q2))) := by
  set s : ℝ := Real.sqrt (q0 * q2) with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hs2 : s ^ 2 = q0 * q2 := Real.sq_sqrt (by positivity)
  set w : ℝ := (z + q1) / (2 * s) with hw
  have h2ws : 2 * w * s = z + q1 := by rw [hw]; field_simp
  have key : ∀ m : ℕ,
      ((quadFavard q0 q1 q2 m).eval z
          = s ^ m * (Polynomial.Chebyshev.U ℝ (m : ℤ)).eval w) ∧
      ((quadFavard q0 q1 q2 (m + 1)).eval z
          = s ^ (m + 1) * (Polynomial.Chebyshev.U ℝ ((m : ℤ) + 1)).eval w) := by
    intro m
    induction m with
    | zero => refine ⟨by simp [Polynomial.Chebyshev.U_zero], ?_⟩
              simp [Polynomial.Chebyshev.U_one, ← h2ws]
              ring
    | succ n ih =>
      obtain ⟨ihn, ihn1⟩ := ih
      refine ⟨by exact_mod_cast ihn1, ?_⟩
      have hU : Polynomial.Chebyshev.U ℝ ((n : ℤ) + 2)
          = 2 * X * Polynomial.Chebyshev.U ℝ ((n : ℤ) + 1)
            - Polynomial.Chebyshev.U ℝ (n : ℤ) := Polynomial.Chebyshev.U_add_two ℝ (n : ℤ)
      have hidx : ((n : ℤ) + 1) + 1 = (n : ℤ) + 2 := by ring
      rw [show n + 1 + 1 = n + 2 from rfl, quadFavard_add_two]
      push_cast
      rw [hidx, hU]
      simp only [eval_sub, eval_mul, eval_add, eval_X, eval_C, eval_ofNat]
      rw [ihn1, ihn]
      rw [← h2ws, ← hs2]
      ring
  exact (key m).1


/-- The `k`-th zero of `p_m`: the Chebyshev node pulled back through
`z ↦ (z+q₁)/(2√(q₀q₂))`. -/
noncomputable def quadRoot (q0 q1 q2 : ℝ) (m k : ℕ) : ℝ :=
  -q1 + 2 * Real.sqrt (q0 * q2) * Real.cos ((k + 1) * π / (m + 1))

private theorem quadRoot_angle_mem {m k : ℕ} (hk : k < m) :
    0 < ((k : ℝ) + 1) * π / (m + 1) ∧ ((k : ℝ) + 1) * π / (m + 1) < π := by
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hkm : ((k : ℝ) + 1) < (m : ℝ) + 1 := by exact_mod_cast Nat.succ_lt_succ hk
  refine ⟨by positivity, ?_⟩
  rw [div_lt_iff₀ hm1]
  nlinarith [pi_pos]

/-- **`rem:quadratic-case`, `Q4`.**  The zeros of `p_m` are exactly the `m`
Chebyshev nodes pulled back to the `z`-line.
**Addition.**  The paper states nothing about the zeros of `p_m`: it applies
Shohat's theorem to the weighted combination `F_M`, not to `p_m`, and names the
`(2,1)` case classical without spelling out its orthogonal-polynomial content.
This lemma and the two after it supply that content — the zero set, its
simplicity and count, and the interlacing — which
`Polynomial.Chebyshev.roots_U_real` makes available once
`quadFavard_eval_eq_chebyshev` is in hand.  There is no paper route here to
differ from.
-/
theorem quadFavard_eval_eq_zero_iff {q0 q2 : ℝ} (hq0 : 0 < q0) (hq2 : 0 < q2) (q1 : ℝ)
    (m : ℕ) (z : ℝ) :
    (quadFavard q0 q1 q2 m).eval z = 0 ↔ ∃ k < m, z = quadRoot q0 q1 q2 m k := by
  classical
  have hs0 : 0 < Real.sqrt (q0 * q2) := Real.sqrt_pos.mpr (by positivity)
  have hUne : (Polynomial.Chebyshev.U ℝ (m : ℤ)) ≠ 0 := by
    simp only [ne_eq, Polynomial.Chebyshev.U_eq_zero_iff]
    omega
  have hiff : (quadFavard q0 q1 q2 m).eval z = 0
      ↔ (Polynomial.Chebyshev.U ℝ (m : ℤ)).eval ((z + q1) / (2 * Real.sqrt (q0 * q2))) = 0 := by
    rw [quadFavard_eval_eq_chebyshev hq0 hq2 q1 m z, mul_eq_zero]
    constructor
    · rintro (h | h)
      · exact absurd h (pow_ne_zero _ hs0.ne')
      · exact h
    · exact fun h => Or.inr h
  rw [hiff]
  constructor
  · intro h
    have hmem : (z + q1) / (2 * Real.sqrt (q0 * q2)) ∈ (Polynomial.Chebyshev.U ℝ (m : ℤ)).roots :=
      (Polynomial.mem_roots hUne).2 h
    rw [Polynomial.Chebyshev.roots_U_real m] at hmem
    obtain ⟨k, hk, hkz⟩ :
        ∃ k < m, Real.cos (((k : ℝ) + 1) * π / (m + 1)) = (z + q1) / (2 * Real.sqrt (q0 * q2)) := by
      simpa using hmem
    refine ⟨k, hk, ?_⟩
    rw [quadRoot, hkz]
    field
  · rintro ⟨k, hk, rfl⟩
    have hw : (quadRoot q0 q1 q2 m k + q1) / (2 * Real.sqrt (q0 * q2))
        = Real.cos ((k + 1) * π / (m + 1)) := by
      rw [quadRoot]; field_simp; ring
    rw [hw]
    have hmem : Real.cos (((k : ℝ) + 1) * π / (m + 1))
        ∈ (Polynomial.Chebyshev.U ℝ (m : ℤ)).roots := by
      rw [Polynomial.Chebyshev.roots_U_real m]
      simpa using Finset.mem_image.2 ⟨k, Finset.mem_range.2 hk, rfl⟩
    exact (Polynomial.mem_roots hUne).1 hmem

/-- **`rem:quadratic-case`, `Q4`.**  Every zero of `p_m` lies in the open interval
`I_{Q,1} = (-q₁-2√(q₀q₂), -q₁+2√(q₀q₂))`. -/
theorem quadFavard_root_mem_Ioo {q0 q2 : ℝ} (hq0 : 0 < q0) (hq2 : 0 < q2) (q1 : ℝ)
    {m : ℕ} {z : ℝ} (hz : (quadFavard q0 q1 q2 m).eval z = 0) :
    z ∈ Set.Ioo (-q1 - 2 * Real.sqrt (q0 * q2)) (-q1 + 2 * Real.sqrt (q0 * q2)) := by
  obtain ⟨k, hk, rfl⟩ := (quadFavard_eval_eq_zero_iff hq0 hq2 q1 m z).1 hz
  have hs0 : 0 < Real.sqrt (q0 * q2) := Real.sqrt_pos.mpr (by positivity)
  obtain ⟨hlo, hhi⟩ := quadRoot_angle_mem hk
  have hup : Real.cos (((k : ℝ) + 1) * π / (m + 1)) < 1 := by
    have := Real.strictAntiOn_cos (Set.mem_Icc.2 ⟨le_refl 0, pi_pos.le⟩)
      (Set.mem_Icc.2 ⟨hlo.le, hhi.le⟩) hlo
    simpa using this
  have hdn : (-1 : ℝ) < Real.cos (((k : ℝ) + 1) * π / (m + 1)) := by
    have := Real.strictAntiOn_cos (Set.mem_Icc.2 ⟨hlo.le, hhi.le⟩)
      (Set.mem_Icc.2 ⟨pi_pos.le, le_refl π⟩) hhi
    simpa using this
  rw [quadRoot]
  constructor <;> nlinarith [hs0, hup, hdn]

/-- **`rem:quadratic-case`, `Q4`.**  `p_m` is real-rooted with exactly `m` zeros,
all simple: the `m` Chebyshev nodes are distinct and `deg p_m = m`. -/
theorem quadFavard_roots_card {q0 q2 : ℝ} (hq0 : 0 < q0) (hq2 : 0 < q2) (q1 : ℝ) (m : ℕ) :
    (quadFavard q0 q1 q2 m).roots.card = m ∧ (quadFavard q0 q1 q2 m).roots.Nodup := by
  classical
  have hs0 : 0 < Real.sqrt (q0 * q2) := Real.sqrt_pos.mpr (by positivity)
  obtain ⟨hmon, hdeg⟩ := quadFavard_monic_natDegree q0 q1 q2 m
  set Z : Finset ℝ := (Finset.range m).image (fun k => quadRoot q0 q1 q2 m k) with hZ
  have hcosinj : Set.InjOn (fun k : ℕ => Real.cos (((k : ℝ) + 1) * π / (m + 1)))
      (Finset.range m) := by
    exact (Finset.range m).nodup_map_iff_injOn.mp
      (by simpa using Polynomial.Chebyshev.roots_U_real_nodup m)
  have hinj : Set.InjOn (fun k : ℕ => quadRoot q0 q1 q2 m k) (Finset.range m) := by
    intro x hx y hy hxy
    refine hcosinj hx hy ?_
    simp only [quadRoot] at hxy
    have h2s : (2 * Real.sqrt (q0 * q2)) ≠ 0 := by positivity
    refine mul_left_cancel₀ h2s ?_
    linarith
  have hZcard : Z.card = m := by
    rw [hZ, Finset.card_image_of_injOn hinj, Finset.card_range]
  have hZsub : Z ⊆ (quadFavard q0 q1 q2 m).roots.toFinset := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hx
    refine Multiset.mem_toFinset.2 ((Polynomial.mem_roots hmon.ne_zero).2 ?_)
    exact (quadFavard_eval_eq_zero_iff hq0 hq2 q1 m _).2 ⟨k, Finset.mem_range.1 hk, rfl⟩
  have hle : m ≤ (quadFavard q0 q1 q2 m).roots.card := by
    calc m = Z.card := hZcard.symm
      _ ≤ (quadFavard q0 q1 q2 m).roots.toFinset.card := Finset.card_le_card hZsub
      _ ≤ (quadFavard q0 q1 q2 m).roots.card := Multiset.toFinset_card_le _
  have hge : (quadFavard q0 q1 q2 m).roots.card ≤ m := by
    have := (quadFavard q0 q1 q2 m).card_roots'
    omega
  have hcard : (quadFavard q0 q1 q2 m).roots.card = m := le_antisymm hge hle
  refine ⟨hcard, ?_⟩
  have htf : (quadFavard q0 q1 q2 m).roots.toFinset.card
      = (quadFavard q0 q1 q2 m).roots.card := by
    have h1 : Z.card ≤ (quadFavard q0 q1 q2 m).roots.toFinset.card := Finset.card_le_card hZsub
    have h2 := Multiset.toFinset_card_le (quadFavard q0 q1 q2 m).roots
    omega
  exact Multiset.toFinset_card_eq_card_iff_nodup.1 htf

/-- **`rem:quadratic-case`, `Q4`.**  Consecutive members interlace: between two
zeros of `p_{m+1}` there is exactly one zero of `p_m`, and conversely.  With the
zeros real, simple and inside `I_{Q,1}`, this is the full orthogonal-polynomial
signature of the Favard branch. -/
theorem quadFavard_interlace {q0 q2 : ℝ} (hq0 : 0 < q0) (hq2 : 0 < q2) (q1 : ℝ)
    {m k : ℕ} (hk : k < m) :
    quadRoot q0 q1 q2 (m + 1) (k + 1) < quadRoot q0 q1 q2 m k ∧
      quadRoot q0 q1 q2 m k < quadRoot q0 q1 q2 (m + 1) k := by
  have hs0 : 0 < Real.sqrt (q0 * q2) := Real.sqrt_pos.mpr (by positivity)
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hm2 : (0 : ℝ) < (m : ℝ) + 1 + 1 := by positivity
  have hkm : ((k : ℝ) + 1) < (m : ℝ) + 1 := by exact_mod_cast Nat.succ_lt_succ hk
  -- the three angles, all in `[0,π]`
  have hA : ((k : ℝ) + 1) * π / ((m : ℝ) + 1 + 1) < ((k : ℝ) + 1) * π / ((m : ℝ) + 1) := by
    rw [div_lt_div_iff₀ hm2 hm1]
    nlinarith [pi_pos]
  have hB : ((k : ℝ) + 1) * π / ((m : ℝ) + 1) < ((k : ℝ) + 1 + 1) * π / ((m : ℝ) + 1 + 1) := by
    rw [div_lt_div_iff₀ hm1 hm2]
    nlinarith [pi_pos]
  have hmem0 : ((k : ℝ) + 1) * π / ((m : ℝ) + 1 + 1) ∈ Set.Icc 0 π := by
    refine Set.mem_Icc.2 ⟨by positivity, ?_⟩
    rw [div_le_iff₀ hm2]; nlinarith [pi_pos]
  have hmem1 : ((k : ℝ) + 1) * π / ((m : ℝ) + 1) ∈ Set.Icc 0 π := by
    refine Set.mem_Icc.2 ⟨by positivity, ?_⟩
    rw [div_le_iff₀ hm1]; nlinarith [pi_pos]
  have hmem2 : ((k : ℝ) + 1 + 1) * π / ((m : ℝ) + 1 + 1) ∈ Set.Icc 0 π := by
    refine Set.mem_Icc.2 ⟨by positivity, ?_⟩
    rw [div_le_iff₀ hm2]; nlinarith [pi_pos]
  have hc1 := Real.strictAntiOn_cos hmem0 hmem1 hA
  have hc2 := Real.strictAntiOn_cos hmem1 hmem2 hB
  simp only [quadRoot]
  push_cast
  constructor <;> nlinarith [hs0, hc1, hc2]


/-! ### `Q1` — the denominator recurrence off the generating function -/

private theorem quadPoly_coeff (q0 q1 q2 : ℝ) :
    (quadPoly q0 q1 q2).coeff 0 = ((q0 : ℝ) : ℂ) ∧
      (quadPoly q0 q1 q2).coeff 1 = ((q1 : ℝ) : ℂ) ∧
      (quadPoly q0 q1 q2).coeff 2 = ((q2 : ℝ) : ℂ) ∧
      ∀ j, 3 ≤ j → (quadPoly q0 q1 q2).coeff j = 0 := by
  refine ⟨by simp [quadPoly], by simp [quadPoly], by simp [quadPoly], fun j hj => ?_⟩
  have h1 : j ≠ 0 := by omega
  have h2 : j ≠ 1 := by omega
  have h3 : ¬ (j = 2) := by omega
  simp [quadPoly, coeff_C, coeff_X, coeff_X_pow, h1, h3]
  intro h
  exact absurd h (by omega : ¬ ((1 : ℕ) = j))

/-- **`rem:quadratic-case`, `Q1`.**  The denominator-only coefficients
`H_m = [t^m](Q+zt)^{-1}` satisfy the three-term recurrence
`q₀H_m + (z+q₁)H_{m-1} + q₂H_{m-2} = 0`.  This is the generating function read
as a recurrence, and it is what the Favard normalization of `Q2` acts on. -/
theorem quad_denominator_recurrence {q0 q1 q2 : ℝ} (hq0 : 0 < q0) {M : ℕ} (hM : 2 ≤ M) :
    C ((q0 : ℝ) : ℂ) * ftCoeffPoly (quadPoly q0 q1 q2) 1 1 M
      + (C ((q1 : ℝ) : ℂ) + X) * ftCoeffPoly (quadPoly q0 q1 q2) 1 1 (M - 1)
      + C ((q2 : ℝ) : ℂ) * ftCoeffPoly (quadPoly q0 q1 q2) 1 1 (M - 2) = 0 := by
  classical
  obtain ⟨hc0, hc1, hc2, hcj⟩ := quadPoly_coeff q0 q1 q2
  set Q := quadPoly q0 q1 q2 with hQ
  set H : ℕ → Polynomial ℂ := ftCoeffPoly Q 1 1 with hH
  have hd1 : ftDenCoeff Q 1 1 = C ((q1 : ℝ) : ℂ) + X := by simp [ftDenCoeff, hc1]
  have hd2 : ftDenCoeff Q 1 2 = C ((q2 : ℝ) : ℂ) := by
    simp [ftDenCoeff, hc2, show ¬ (2 = 1) by omega]
  have hdj : ∀ j, 3 ≤ j → ftDenCoeff Q 1 j = 0 := by
    intro j hj
    simp [ftDenCoeff, hcj j hj, show ¬ (j = 1) by omega]
  -- the convolution collapses to two terms
  have hpair : (M - 2) ≠ (M - 1) := by omega
  have hsub : ({M - 2, M - 1} : Finset ℕ) ⊆ Finset.range M := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> exact Finset.mem_range.2 (by omega)
  have hzero : ∀ i ∈ Finset.range M, i ∉ ({M - 2, M - 1} : Finset ℕ) →
      ftDenCoeff Q 1 (M - i) * H i = 0 := by
    intro i hi hni
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hni
    have hlt : i < M := Finset.mem_range.1 hi
    rw [hdj (M - i) (by omega), zero_mul]
  have hsum : ∑ i ∈ Finset.range M, ftDenCoeff Q 1 (M - i) * H i
      = ftDenCoeff Q 1 2 * H (M - 2) + ftDenCoeff Q 1 1 * H (M - 1) := by
    rw [← Finset.sum_subset hsub hzero, Finset.sum_pair hpair]
    congr 2 <;> [skip; skip] <;> congr 1 <;> omega
  have hMcoeff : ((1 : Polynomial ℂ).coeff M) = 0 := by
    rw [Polynomial.coeff_one, if_neg (by omega)]
  have hrec : H M = C ((quadPoly q0 q1 q2).coeff 0)⁻¹
      * (C ((1 : Polynomial ℂ).coeff M)
        - ∑ i ∈ Finset.range M, ftDenCoeff Q 1 (M - i) * H i) := ftCoeffPoly_eq Q 1 1 M
  have hq0c : ((q0 : ℝ) : ℂ) ≠ 0 := by
    simpa using hq0.ne'
  have hcc : C ((q0 : ℝ) : ℂ) * C (((q0 : ℝ) : ℂ))⁻¹ = 1 := by
    rw [← C_mul, mul_inv_cancel₀ hq0c, C_1]
  rw [hrec, hMcoeff, hsum, hd1, hd2, hc0, C_0, zero_sub, ← mul_assoc, hcc, one_mul]
  ring


/-- **`rem:quadratic-case`, `Q1`–`Q2` joined.**  The recurrence-defined `p_m` of
`quadFavard` *is* the Favard normalization `q₀(-q₀)^m H_m` of the
denominator-only sequence.  Without this the two halves of the remark — the
generating function and the Chebyshev system — would be unrelated objects. -/
theorem quadFavard_eval_eq_coeffPoly {q0 q1 q2 : ℝ} (hq0 : 0 < q0) (m : ℕ) (z : ℝ) :
    (((quadFavard q0 q1 q2 m).eval z : ℝ) : ℂ)
      = ((q0 : ℝ) : ℂ) * (-((q0 : ℝ) : ℂ)) ^ m
        * (ftCoeffPoly (quadPoly q0 q1 q2) 1 1 m).eval ((z : ℝ) : ℂ) := by
  have hq0c : ((q0 : ℝ) : ℂ) ≠ 0 := by simpa using hq0.ne'
  obtain ⟨hc0, hc1, _, _⟩ := quadPoly_coeff q0 q1 q2
  set Q := quadPoly q0 q1 q2 with hQ
  set H : ℕ → ℂ := fun m => (ftCoeffPoly Q 1 1 m).eval ((z : ℝ) : ℂ) with hH
  have hcp0 : (ftCoeffPoly Q 1 1 0).eval (((z : ℝ) : ℂ)) = (((q0 : ℝ) : ℂ))⁻¹ := by
    simp [ftCoeffPoly_eq Q 1 1 0, hc0]
  have hH0 : H 0 = (((q0 : ℝ) : ℂ))⁻¹ := hcp0
  have hH1 : H 1 = -((((q0 : ℝ) : ℂ))⁻¹ * ((((q1 : ℝ) : ℂ) + (z : ℂ)) * (((q0 : ℝ) : ℂ))⁻¹)) := by
    change (ftCoeffPoly Q 1 1 1).eval (((z : ℝ) : ℂ)) = _
    simp [ftCoeffPoly_eq Q 1 1 1, hc0, ftDenCoeff, hc1, hcp0, Polynomial.coeff_one]
  have key : ∀ n : ℕ,
      ((((quadFavard q0 q1 q2 n).eval z : ℝ) : ℂ)
          = ((q0 : ℝ) : ℂ) * (-((q0 : ℝ) : ℂ)) ^ n * H n) ∧
      ((((quadFavard q0 q1 q2 (n + 1)).eval z : ℝ) : ℂ)
          = ((q0 : ℝ) : ℂ) * (-((q0 : ℝ) : ℂ)) ^ (n + 1) * H (n + 1)) := by
    intro n
    induction n with
    | zero =>
      refine ⟨by simp [hH0]; field_simp, ?_⟩
      rw [quadFavard_one]
      simp only [eval_add, eval_X, eval_C]
      rw [hH1]
      push_cast
      field
    | succ k ih =>
      obtain ⟨ihk, ihk1⟩ := ih
      refine ⟨ihk1, ?_⟩
      have hrec := congrArg (Polynomial.eval ((z : ℝ) : ℂ))
        (quad_denominator_recurrence (q0 := q0) (q1 := q1) (q2 := q2) hq0
          (M := k + 2) (by omega))
      simp only [eval_add, eval_mul, eval_C, eval_X, eval_zero] at hrec
      rw [show k + 2 - 1 = k + 1 from rfl, show k + 2 - 2 = k from rfl] at hrec
      have hHrec : ((q0 : ℝ) : ℂ) * H (k + 2)
          + (((q1 : ℝ) : ℂ) + (z : ℂ)) * H (k + 1) + ((q2 : ℝ) : ℂ) * H k = 0 := by
        simpa [hH] using hrec
      rw [show k + 1 + 1 = k + 2 from rfl, quadFavard_add_two]
      simp only [eval_sub, eval_mul, eval_add, eval_X, eval_C]
      push_cast
      rw [ihk, ihk1]
      have hH2 : H (k + 2)
          = -((((q1 : ℝ) : ℂ) + (z : ℂ)) * H (k + 1) + ((q2 : ℝ) : ℂ) * H k)
            / ((q0 : ℝ) : ℂ) := by
        field_simp
        linear_combination hHrec
      rw [hH2]
      field
  exact (key m).1

end ForgacsTran
