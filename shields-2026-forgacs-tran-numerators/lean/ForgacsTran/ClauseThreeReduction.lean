/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.Sharpness

/-!
# The reduction side of `thm:main` clause 3

Two things clause 3 needs from `sec:reduction`, neither of which is a missing primitive:

## Main statements

* **`deg B_N` is not constant.**  `laurentWeight` is defined through a `choose` on
  `eq:canonical-Laurent-factorization`, and the development carried only the upper bound
  `eq:reduced-degree-complexity` — so nothing in it exhibited a numerator whose reduced weight
  is nonconstant, and against that the `C_1deg B_N` term of clause 3 could not be told apart
  from a constant.  `laurentWeight_X_pow` computes it at `N = z^E`, and
  `natDegree_laurentWeight_unbounded` makes the term unbounded at a fixed pencil.

* **`P_m ≠ 0` eventually**, which is `thm:main` clause 2(i) and which clause 3 inherits.
  `EventualDegree.eventual_ne_zero` proves it for the reduced sequence out of the top
  coefficient — `lem:eventual-degree`'s attainment argument — and
  `LaurentReduction.reduction_coeff_eventually` identifies `P_m` with that sequence at the
  shifted index.  `eventual_coeffPoly_ne_zero` is the composition, and the only care it needs
  is the index shift.

## Implementation notes

This module sits on `sec:reduction` alone; nothing here reaches the `sec:geometry` or
`sec:dominance` chain.

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`,
`eq:canonical-Laurent-factorization`, `eq:reduction-coeff` and `lem:eventual-degree` in the
service of clause 3.

## Tags

reduction, numerator-uniform defect, weight polynomial
-/

namespace ForgacsTran

open Polynomial LaurentPolynomial

/-- **The reduced weight at `N = z^E`.**  `laurentWeight` is defined through a `choose` on
`eq:canonical-Laurent-factorization`, and the development carries only the upper bound
`eq:reduced-degree-complexity` — so nothing in it exhibits a numerator whose reduced weight is
nonconstant, and without one the `C_1deg B_N` term of `thm:main` clause 3 could not be told
apart from a constant.

The pure power `N = z^E` is the cheapest witness.  On the curve, `z ↦ -Q(t)/t^r`, so
`L_N = (-Q)^E t^{-rE}` and the canonical pair is `(-rE, (-Q)^E)` — its second component has
`\coeff_0 = (-Q(0))^E ≠ 0`, which is what uniqueness needs. -/
theorem laurentWeight_X_pow {K : Type*} [Field K] (Q : Polynomial K) {r : ℕ} (hr : 1 ≤ r)
    (hQ0 : Q.coeff 0 ≠ 0) (E : ℕ) :
    laurentWeight Q r (X ^ E) = (-Q) ^ E := by
  have hmax : 0 < max Q.natDegree r := lt_of_lt_of_le Nat.zero_lt_one (le_max_of_le_right hr)
  have hmaxW : ((0 : ℕ) : WithBot ℕ) < ((max Q.natDegree r : ℕ) : WithBot ℕ) := by
    exact_mod_cast hmax
  have hB0 : ((-Q) ^ E).coeff 0 ≠ 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_pow, Polynomial.eval_neg]
    refine pow_ne_zero _ (neg_ne_zero.2 ?_)
    rwa [← Polynomial.coeff_zero_eq_eval_zero]
  have hproper : ∀ β, ((X ^ E : (Polynomial K)[X]).coeff β).degree
      < ((max Q.natDegree r : ℕ) : WithBot ℕ) := by
    intro β
    rw [Polynomial.coeff_X_pow]
    split_ifs with h
    · rw [Polynomial.degree_one]
      simpa using hmaxW
    · rw [Polynomial.degree_zero]
      exact WithBot.bot_lt_coe _
  have hQpow : toLaurent ((-Q) ^ E) = (-(toLaurent Q) : K[T;T⁻¹]) ^ E := by
    rw [map_pow, map_neg]
  have hfac : curveEval Q r (X ^ E) = T (-((r : ℤ) * E)) * toLaurent ((-Q) ^ E) := by
    rw [map_pow, curveEval_X, curveCoord, mul_pow, T_pow, hQpow,
      show ((E : ℕ) : ℤ) * -(r : ℤ) = -((r : ℤ) * E) by ring]
    ring
  exact ((laurentShift_weight_unique Q hr hQ0 (pow_ne_zero E Polynomial.X_ne_zero) hproper
    hB0 hfac).2).symm


/-- `deg B_{z^E} = Edeg Q`.  So for a fixed pencil with `Q` nonconstant the reduced weight
degree takes every multiple of `deg Q`, and the `C_1deg B_N` term of clause 3 is exercised
rather than idle. -/
theorem natDegree_laurentWeight_X_pow {K : Type*} [Field K] (Q : Polynomial K) {r : ℕ}
    (hr : 1 ≤ r) (hQ0 : Q.coeff 0 ≠ 0) (E : ℕ) :
    (laurentWeight Q r (X ^ E)).natDegree = E * Q.natDegree := by
  rw [laurentWeight_X_pow Q hr hQ0 E, Polynomial.natDegree_pow, Polynomial.natDegree_neg]


/-- **`deg B_N` is unbounded at a fixed `(Q, r)`.**  Given any bound, a proper numerator
exceeds it, so no single constant can replace the `C_1deg B_N` term. -/
theorem natDegree_laurentWeight_unbounded {K : Type*} [Field K] (Q : Polynomial K) {r : ℕ}
    (hr : 1 ≤ r) (hQ0 : Q.coeff 0 ≠ 0) (hQdeg : 1 ≤ Q.natDegree) (n : ℕ) :
    ∃ N : (Polynomial K)[X], N ≠ 0 ∧
      (∀ β, (N.coeff β).degree < ((max Q.natDegree r : ℕ) : WithBot ℕ)) ∧
      n < (laurentWeight Q r N).natDegree := by
  refine ⟨X ^ (n + 1), pow_ne_zero _ Polynomial.X_ne_zero, ?_, ?_⟩
  · intro β
    have hmax : 0 < max Q.natDegree r := lt_of_lt_of_le Nat.zero_lt_one (le_max_of_le_right hr)
    have hmaxW : ((0 : ℕ) : WithBot ℕ) < ((max Q.natDegree r : ℕ) : WithBot ℕ) := by
      exact_mod_cast hmax
    rw [Polynomial.coeff_X_pow]
    split_ifs with h
    · rw [Polynomial.degree_one]; simpa using hmaxW
    · rw [Polynomial.degree_zero]; exact WithBot.bot_lt_coe _
  · rw [natDegree_laurentWeight_X_pow Q hr hQ0]
    calc n < n + 1 := Nat.lt_succ_self n
      _ = (n + 1) * 1 := by ring
      _ ≤ (n + 1) * Q.natDegree := by exact Nat.mul_le_mul_left _ hQdeg


/-- `deg B_1 = 0`: the trivial numerator has reduced weight `1`.  Paired with
`laurentWeight_X_pow` this pins both ends of the range `deg B_N` takes. -/
theorem laurentWeight_one {K : Type*} [Field K] (Q : Polynomial K) {r : ℕ} (hr : 1 ≤ r)
    (hQ0 : Q.coeff 0 ≠ 0) :
    laurentWeight Q r 1 = 1 := by
  have hmax : 0 < max Q.natDegree r := lt_of_lt_of_le Nat.zero_lt_one (le_max_of_le_right hr)
  have hmaxW : ((0 : ℕ) : WithBot ℕ) < ((max Q.natDegree r : ℕ) : WithBot ℕ) := by
    exact_mod_cast hmax
  have hproper : ∀ β, ((1 : (Polynomial K)[X]).coeff β).degree
      < ((max Q.natDegree r : ℕ) : WithBot ℕ) := by
    intro β
    rw [Polynomial.coeff_one]
    split_ifs
    · rw [Polynomial.degree_one]; simpa using hmaxW
    · rw [Polynomial.degree_zero]; exact WithBot.bot_lt_coe _
  have hfac : curveEval Q r 1 = T 0 * toLaurent (1 : Polynomial K) := by
    rw [map_one, map_one, LaurentPolynomial.T_zero, one_mul]
  exact ((laurentShift_weight_unique Q hr hQ0 one_ne_zero hproper
    (by simp) hfac).2).symm


/-- **Paper `thm:main` clause 2(i) for a proper bivariate numerator.**  For all sufficiently
large `m` the coefficient polynomial `P_m` of `eq:P-generating-intro` is nonzero.

The threshold is `max(m_0, (M_0 + λ_N)^+)`.  Taking the `ℕ`-truncation of
`M_0 + λ_N` is safe in the direction needed — `(·)^+` only ever *raises* the
threshold — and above it `m - λ_N ≥ M_0 ≥ 0`, so the `toNat` in
`eq:reduction-coeff` is not truncating and the reduced sequence really is past its own
threshold.

`hb0`, the `b_0 ≠ 0` that `eventual_ne_zero` consumes, costs nothing here: at
`b_M = B_N(M)` it is `B_N(0) ≠ 0`, which is the defining condition of
`eq:canonical-Laurent-factorization` itself and is delivered by
`curveEval_eq_T_mul_weight`. -/
theorem eventual_coeffPoly_ne_zero {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]
    (Q : Polynomial 𝕜) {r : ℕ} (hr : 1 ≤ r)
    (hQ0 : Q.coeff 0 ≠ 0) (hQ1 : Q.coeff 1 ≠ 0)
    {N : (Polynomial 𝕜)[X]} (hN : N ≠ 0)
    (hproper : ∀ β, (N.coeff β).degree < ((max Q.natDegree r : ℕ) : WithBot ℕ))
    (P F : ℕ → Polynomial 𝕜)
    (hP : ∀ m, denomConv (ftDenom Q r) P m = (swapVars N).coeff m)
    (hF : ∀ M, denomConv (ftDenom Q r) F M
      = Polynomial.C ((laurentWeight Q r N).coeff M)) :
    ∃ m₀ : ℕ, ∀ m, m₀ ≤ m → P m ≠ 0 := by
  obtain ⟨hb0, -⟩ := curveEval_eq_T_mul_weight Q hr hQ0 hN hproper
  obtain ⟨M₀, hM₀⟩ :=
    eventual_ne_zero Q hr hQ0 hQ1 (fun M => (laurentWeight Q r N).coeff M) hb0 F hF
  obtain ⟨m0, hm0⟩ := reduction_coeff_eventually Q hr hQ0 hN hproper P F hP hF
  refine ⟨max m0 (((M₀ : ℤ) + laurentShift Q r N).toNat), fun m hm => ?_⟩
  have hm0' : m0 ≤ m := le_trans (le_max_left _ _) hm
  have hK : (((M₀ : ℤ) + laurentShift Q r N).toNat) ≤ m := le_trans (le_max_right _ _) hm
  have hKZ : ((((M₀ : ℤ) + laurentShift Q r N).toNat : ℕ) : ℤ) ≤ (m : ℤ) := by
    exact_mod_cast hK
  have hMle : M₀ ≤ ((m : ℤ) - laurentShift Q r N).toNat := by omega
  rw [hm0 m hm0']
  exact hM₀ _ hMle


/-- **The composition is not vacuous.**  `eventual_coeffPoly_ne_zero` takes four hypotheses —
a nonzero proper numerator and the two recurrences of `sec:reduction` — and a conclusion drawn
from an unsatisfiable set would be worth nothing.  At `N = 1` all four hold:
`Sharpness.exists_denomConv_recurrence` solves the recurrence for any right-hand side, and
`swapVars_C` puts `(\operatorname{swap}N)_m` in the constant shape it solves for. -/
theorem eventual_coeffPoly_ne_zero_nonvacuous {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]
    (Q : Polynomial 𝕜) {r : ℕ} (hr : 1 ≤ r) (hQ0 : Q.coeff 0 ≠ 0) :
    ∃ (N : (Polynomial 𝕜)[X]) (P F : ℕ → Polynomial 𝕜),
      N ≠ 0 ∧
      (∀ β, (N.coeff β).degree < ((max Q.natDegree r : ℕ) : WithBot ℕ)) ∧
      (∀ m, denomConv (ftDenom Q r) P m = (swapVars N).coeff m) ∧
      (∀ M, denomConv (ftDenom Q r) F M
        = Polynomial.C ((laurentWeight Q r N).coeff M)) := by
  have hmax : 0 < max Q.natDegree r := lt_of_lt_of_le Nat.zero_lt_one (le_max_of_le_right hr)
  have hmaxW : ((0 : ℕ) : WithBot ℕ) < ((max Q.natDegree r : ℕ) : WithBot ℕ) := by
    exact_mod_cast hmax
  obtain ⟨F, hF⟩ :=
    exists_denomConv_recurrence Q hr hQ0 (fun m => (1 : Polynomial 𝕜).coeff m)
  refine ⟨1, F, F, one_ne_zero, ?_, ?_, ?_⟩
  · intro β
    rw [Polynomial.coeff_one]
    split_ifs
    · rw [Polynomial.degree_one]; simpa using hmaxW
    · rw [Polynomial.degree_zero]; exact WithBot.bot_lt_coe _
  · intro m
    rw [hF m, map_one, Polynomial.coeff_one, Polynomial.coeff_one]
    split_ifs <;> simp
  · intro M
    rw [hF M, laurentWeight_one Q hr hQ0]


/-! ### Why the onset must stay inside the quantifier over numerators

`rem:degree-attainment` is already formalized, in `Sharpness`: `lateWeight`,
`natDegree_lt_of_lateWeight` and `exists_lateDrop` exhibit the remark's own family
`B^{(L)} = 1 - (L+1)t` at `Q = 1 - t`, `r = 2`, dropping the degree at `M = 2L + 1` for
arbitrary `L`.  What is stated there is about an abstract weight sequence `b`.

Clause 3 needs it one step further along, in the numerator's vocabulary: it is
`deg B_N = deg(\text{laurentWeight } Q\, r\, N)` that the constants `C_0`, `C_1` are allowed
to see, so the necessity of putting the onset **inside** `∀ N` is a statement about
numerators, not about weight sequences.  `laurentWeight_C` carries the family across —
a numerator constant in `z` restricts to itself on the curve — and
`onset_not_uniform_in_natDegree_laurentWeight` is the result. -/

/-- The reduced weight of a numerator constant in `z`.  On the curve `N = p(t)` restricts to
`p(t)`, so the canonical pair of `eq:canonical-Laurent-factorization` is `(0, p)` as soon as
`p(0) ≠ 0`. -/
theorem laurentWeight_C {K : Type*} [Field K] (Q : Polynomial K) {r : ℕ} (hr : 1 ≤ r)
    (hQ0 : Q.coeff 0 ≠ 0) {p : Polynomial K} (hp0 : p.coeff 0 ≠ 0)
    (hproper : p.degree < ((max Q.natDegree r : ℕ) : WithBot ℕ)) :
    laurentWeight Q r (Polynomial.C p) = p := by
  have hp : p ≠ 0 := fun h => hp0 (by rw [h]; simp)
  have hN : (Polynomial.C p : (Polynomial K)[X]) ≠ 0 := Polynomial.C_ne_zero.2 hp
  have hprop : ∀ β, ((Polynomial.C p : (Polynomial K)[X]).coeff β).degree
      < ((max Q.natDegree r : ℕ) : WithBot ℕ) := by
    intro β
    rcases eq_or_ne β 0 with rfl | hβ
    · simpa using hproper
    · rw [Polynomial.coeff_C, if_neg hβ, Polynomial.degree_zero]
      exact WithBot.bot_lt_coe _
  have hfac : curveEval Q r (Polynomial.C p) = T 0 * toLaurent p := by
    rw [curveEval_C, LaurentPolynomial.T_zero, one_mul]
  exact ((laurentShift_weight_unique Q hr hQ0 hN hprop hp0 hfac).2).symm

theorem natDegree_one_sub_X {𝕜 : Type*} [Field 𝕜] :
    ((1 : Polynomial 𝕜) - X).natDegree = 1 := by
  compute_degree!

/-- Paper `rem:degree-attainment`, the numerator-side family: `N^{(L)} = B^{(L)}(t)`, constant
in `z`, whose reduced weight is `B^{(L)} = 1 - (L+1)t` itself. -/
noncomputable def lateWeightPoly {𝕜 : Type*} [Field 𝕜] (L : ℕ) : Polynomial 𝕜 :=
  1 - Polynomial.C ((L : 𝕜) + 1) * X

theorem lateWeightPoly_coeff {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜] (L : ℕ) (m : ℕ) :
    (lateWeightPoly L : Polynomial 𝕜).coeff m = lateWeight L m := by
  rw [lateWeightPoly, lateWeight, Polynomial.coeff_sub, Polynomial.coeff_one,
    Polynomial.coeff_C_mul, Polynomial.coeff_X]
  rcases m with _ | m
  · norm_num
  · rcases m with _ | m <;> norm_num

theorem lateWeightPoly_lead_ne_zero {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜] (L : ℕ) :
    ((L : 𝕜) + 1) ≠ 0 := by
  have h : ((L + 1 : ℕ) : 𝕜) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  simpa using h

theorem natDegree_lateWeightPoly {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜] (L : ℕ) :
    (lateWeightPoly L : Polynomial 𝕜).natDegree = 1 := by
  have hc : ((L : 𝕜) + 1) ≠ 0 := lateWeightPoly_lead_ne_zero L
  have hrw : (lateWeightPoly L : Polynomial 𝕜)
      = Polynomial.C (-((L : 𝕜) + 1)) * X + Polynomial.C 1 := by
    rw [lateWeightPoly, map_neg, map_one]; ring
  rw [hrw, Polynomial.natDegree_linear (neg_ne_zero.2 hc)]

/-- **Paper `rem:degree-attainment`, in clause 3's own vocabulary.**  The onset of
`lem:eventual-degree` is not a function of `deg B_N`: at `Q = 1 - t`, `r = 2`, for every `M_0`
there is a **proper nonzero numerator** whose reduced weight has degree exactly `1`, and whose
reduced sequence drops below `⌊ M/2⌋` at some `M ≥ M_0`.

This is what makes the onset `m_0` of `exceptionalRoots_numeratorUniform` a *proved* necessity
inside `∀ N` rather than a stylistic choice: `deg B_N` is pinned at `1` across the whole
family, so no `m_0` computed from `deg B_N` alone can serve all of them, while `C_0` and `C_1`
are untouched — the defect stays bounded, only its onset moves.

`Sharpness.exists_lateDrop` gives the same content over an abstract weight sequence `b`; what
is added here is that the family is realized by numerators, so `deg B_N` — the quantity clause
3 actually measures — is the one held fixed. -/
theorem onset_not_uniform_in_natDegree_laurentWeight {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]
    (M₀ : ℕ) :
    ∃ (N : (Polynomial 𝕜)[X]) (F : ℕ → Polynomial 𝕜) (M : ℕ),
      N ≠ 0 ∧
      (∀ β, (N.coeff β).degree
        < ((max ((1 : Polynomial 𝕜) - X).natDegree 2 : ℕ) : WithBot ℕ)) ∧
      (laurentWeight ((1 : Polynomial 𝕜) - X) 2 N).natDegree = 1 ∧
      (∀ m, denomConv (ftDenom ((1 : Polynomial 𝕜) - X) 2) F m
        = Polynomial.C ((laurentWeight ((1 : Polynomial 𝕜) - X) 2 N).coeff m)) ∧
      M₀ ≤ M ∧ (F M).natDegree < M / 2 := by
  set L : ℕ := max M₀ 1 with hLdef
  have hL : 1 ≤ L := le_max_right _ _
  have hQ0 : ((1 : Polynomial 𝕜) - X).coeff 0 ≠ 0 := coeff_zero_one_sub_X_ne
  have hmax : max ((1 : Polynomial 𝕜) - X).natDegree 2 = 2 := by
    rw [natDegree_one_sub_X]; norm_num
  have hp0 : (lateWeightPoly L : Polynomial 𝕜).coeff 0 ≠ 0 := by
    rw [lateWeightPoly_coeff, lateWeight_zero]; exact one_ne_zero
  have hpdeg : (lateWeightPoly L : Polynomial 𝕜).degree
      < ((max ((1 : Polynomial 𝕜) - X).natDegree 2 : ℕ) : WithBot ℕ) := by
    rw [hmax, Polynomial.degree_eq_natDegree
      (fun h => hp0 (by rw [h]; simp)), natDegree_lateWeightPoly]
    exact_mod_cast (by norm_num : (1 : ℕ) < 2)
  have hw : laurentWeight ((1 : Polynomial 𝕜) - X) 2 (Polynomial.C (lateWeightPoly L))
      = lateWeightPoly L := laurentWeight_C _ (by norm_num) hQ0 hp0 hpdeg
  obtain ⟨F, hF⟩ := exists_denomConv_recurrence ((1 : Polynomial 𝕜) - X) (r := 2)
    (by norm_num) hQ0 (lateWeight L)
  refine ⟨Polynomial.C (lateWeightPoly L), F, 2 * L + 1,
    Polynomial.C_ne_zero.2 (fun h => hp0 (by rw [h]; simp)), ?_, ?_, ?_, ?_, ?_⟩
  · intro β
    rcases eq_or_ne β 0 with rfl | hβ
    · simpa using hpdeg
    · rw [Polynomial.coeff_C, if_neg hβ, Polynomial.degree_zero]
      exact WithBot.bot_lt_coe _
  · rw [hw, natDegree_lateWeightPoly]
  · intro m
    rw [hw, lateWeightPoly_coeff, hF m]
  · have : M₀ ≤ L := le_max_left _ _
    omega
  · have hdiv : (2 * L + 1) / 2 = L := by omega
    rw [hdiv]
    exact natDegree_lt_of_lateWeight hL F hF


end ForgacsTran
