/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.EventualDegree
import ForgacsTran.LaurentReduction

/-!
# The reduction bounds are attained

Both remarks are *sharpness* claims, so in each the witness is the whole content: a theorem
re-deriving the bound would prove nothing.  Each is exhibited.

A prerequisite came first.  `lem:eventual-degree` and everything around it quantify over
sequences `F` satisfying the `sec:reduction` recurrence, and nothing produced one, so a witness
stated against that hypothesis could have been vacuous.  `exists_denomConv_recurrence` closes
it: `Q(0) ≠ 0` makes the leading denominator coefficient a unit, and the recurrence is power
series division.

## Main statements

* `coeff_one_pow`, `leadCoeffPoly_eval_one` — `eq:leading-z-coeff` at `s = 1` is the affine
  function `B(0)(ℓ+1)Λ_Q + B'(0)` of `ℓ`, so its root moves with the weight.
* `lateWeight`, `leadCoeffPoly_lateWeight_eval`, `natDegree_lt_of_lateWeight`,
  `exists_lateDrop` — `rem:degree-attainment`: with `Q = 1 - t` and `r = 2` the degree-one
  weight `B^{(L)} = 1 - (L+1)t` drops the degree at `M = 2L+1`, and `L` is arbitrary, so the
  onset of `lem:eventual-degree` is not a function of `deg B`.
* `curveEval_C_mul_X_pow`, `laurentCanon_C_mul_X_pow`,
  `natDegree_laurentWeight_eq_of_C_mul_X_pow`, `reduced_degree_bound_attained` —
  `rem:canonical-bounds-sharp`, first claim: `eq:reduced-degree-complexity` is attained, at
  every admissible `p` and every `E`, in the regime `q ≥ r`.
* `canonical_division_threshold_sharp` — `rem:canonical-bounds-sharp`, second claim:
  `eq:reduction-threshold` sits at the right index.  For `q > r` and `N = t^{q-1} z^E` the
  quotient of `eq:canonical-Laurent-division` is exhibited — `exists_canonical_division`
  supplies it only existentially — and its `z^0` coefficient is `t^k B` with `B(0) ≠ 0`, so its
  Laurent support runs from `k` to `k + deg B`, and that top exponent is `E(q-r) - 1`, one
  below the threshold.

## Implementation notes

Not covered: the `q ≤ r` branch of `rem:canonical-bounds-sharp`'s degree claim, whose witness
is `N = t^p + c z^E`; and the failure of `eq:reduction-coeff` at `E(q-r) - 1`, which needs the
true coefficient sequence of `N/D` against the reduced one.

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «The canonical Laurent reduction»
and «Eventual degree» (`sec:reduction`, `rem:degree-attainment`, `rem:canonical-bounds-sharp`).

## Tags

sharpness, attained bound, reduction
-/


namespace ForgacsTran

open Polynomial
open LaurentPolynomial (T)
open scoped LaurentPolynomial

variable {𝕜 : Type*} [Field 𝕜]

/-! ### The recurrence has a solution

`lem:eventual-degree` and its supporting lemmas quantify over sequences `F` satisfying the
`sec:reduction` recurrence.  Nothing so far produces one, so a witness stated against that
hypothesis could be vacuous.  `Q(0) ≠ 0` makes the leading denominator coefficient a unit,
and the recurrence is then power-series division. -/

/-- Paper `sec:reduction`: the denominator recurrence `∑_i d_i F_{M-i} = C(b_M)` has a
solution for every right-hand side.  This is what makes the witnesses below genuine
sequences rather than vacuous hypotheses. -/
theorem exists_denomConv_recurrence (Q : Polynomial 𝕜) {r : ℕ} (hr : 1 ≤ r)
    (hQ0 : Q.coeff 0 ≠ 0) (b : ℕ → 𝕜) :
    ∃ F : ℕ → Polynomial 𝕜, ∀ M, denomConv (ftDenom Q r) F M = C (b M) := by
  classical
  set D : PowerSeries (Polynomial 𝕜) := PowerSeries.mk (ftDenom Q r) with hD
  have hu : IsUnit (C (Q.coeff 0) : Polynomial 𝕜) :=
    (Polynomial.isUnit_C).2 (isUnit_iff_ne_zero.2 hQ0)
  obtain ⟨u, hu'⟩ := hu
  have hd0 : PowerSeries.constantCoeff D = (u : Polynomial 𝕜) := by
    rw [hD, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk,
      ftDenom, if_neg (by omega : (0 : ℕ) ≠ r), add_zero, hu']
  set Dinv := PowerSeries.invOfUnit D u with hDinv
  have hDD : D * Dinv = 1 := PowerSeries.mul_invOfUnit D u hd0
  set Fs : PowerSeries (Polynomial 𝕜) := PowerSeries.mk (fun M => C (b M)) * Dinv with hFs
  refine ⟨fun M => PowerSeries.coeff M Fs, fun M => ?_⟩
  have hmul : D * Fs = PowerSeries.mk (fun M => C (b M)) := by
    rw [hFs, ← mul_assoc, mul_comm D _, mul_assoc, hDD, mul_one]
  have hcoeff := congrArg (PowerSeries.coeff M) hmul
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    PowerSeries.coeff_mk] at hcoeff
  simpa [denomConv, hD, PowerSeries.coeff_mk] using hcoeff

/-! ### The nominal leading coefficient at `s = 1` -/

/-- For a series with constant term `1`, the `t`-coefficient of a power scales linearly. -/
theorem coeff_one_pow {f : PowerSeries 𝕜} (hf : PowerSeries.constantCoeff f = 1) (n : ℕ) :
    PowerSeries.coeff 1 (f ^ n) = (n : 𝕜) * PowerSeries.coeff 1 f := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h0 : PowerSeries.coeff 0 (f ^ n) = 1 := by
        rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, hf, one_pow]
      rw [pow_succ, PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
        Finset.sum_range_one]
      simp only [Nat.sub_zero, Nat.sub_self]
      rw [ih, h0, PowerSeries.coeff_zero_eq_constantCoeff_apply, hf]
      push_cast
      ring

/-- **Paper `eq:leading-z-coeff` at `s = 1`.**  The nominal leading coefficient is the affine
function `B(0)(ℓ+1)Λ_Q + B'(0)` of `ℓ`, so its root moves with the weight. -/
theorem leadCoeffPoly_eval_one [CharZero 𝕜] {Q : Polynomial 𝕜} (hQ0 : Q.coeff 0 ≠ 0)
    (b : ℕ → 𝕜) (K : ℕ) :
    (leadCoeffPoly Q b 1).eval ((K : ℕ) : 𝕜) = b 0 * ((K : 𝕜) * lambdaQ Q) + b 1 := by
  rw [leadCoeffPoly_eval hQ0 b 1 K, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
    Finset.sum_range_one]
  have h0 : PowerSeries.coeff 0 ((ftNorm Q) ^ K) = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, constantCoeff_ftNorm hQ0,
      one_pow]
  have h1 : PowerSeries.coeff 1 ((ftNorm Q) ^ K) = (K : 𝕜) * lambdaQ Q := by
    rw [coeff_one_pow (constantCoeff_ftNorm hQ0) K, coeff_one_ftNorm hQ0]
  simp only [Nat.sub_zero, Nat.sub_self, bSeries, PowerSeries.coeff_mk]
  rw [h0, h1]
  ring


/-! ### `rem:degree-attainment` — the onset is not a function of `deg B` -/

theorem lambdaQ_one_sub_X : lambdaQ ((1 : Polynomial 𝕜) - X) = 1 := by
  have h0 : ((1 : Polynomial 𝕜) - X).coeff 0 = 1 := by simp
  have h1 : ((1 : Polynomial 𝕜) - X).coeff 1 = -1 := by
    simp [Polynomial.coeff_one]
  rw [lambdaQ, h0, h1]
  ring

theorem coeff_zero_one_sub_X_ne : ((1 : Polynomial 𝕜) - X).coeff 0 ≠ 0 := by simp

/-- Paper `rem:degree-attainment`: the degree-one weights `B^{(L)}(t) = 1 - (L+1)t`. -/
noncomputable def lateWeight (L : ℕ) : ℕ → 𝕜 :=
  fun i => if i = 0 then 1 else if i = 1 then -((L : 𝕜) + 1) else 0

theorem lateWeight_zero (L : ℕ) : (lateWeight L : ℕ → 𝕜) 0 = 1 := by simp [lateWeight]

theorem lateWeight_one (L : ℕ) : (lateWeight L : ℕ → 𝕜) 1 = -((L : 𝕜) + 1) := by
  simp [lateWeight]

theorem lateWeight_of_two_le (L : ℕ) {i : ℕ} (hi : 2 ≤ i) : (lateWeight L : ℕ → 𝕜) i = 0 := by
  have h0 : i ≠ 0 := by omega
  have h1 : i ≠ 1 := by omega
  simp [lateWeight, h0, h1]

theorem lateWeight_one_ne_zero [CharZero 𝕜] (L : ℕ) : (lateWeight L : ℕ → 𝕜) 1 ≠ 0 := by
  rw [lateWeight_one, neg_ne_zero]
  have h : ((L + 1 : ℕ) : 𝕜) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  push_cast at h
  exact h

/-- **Paper `rem:degree-attainment`.**  With `Q = 1 - t`, the nominal leading coefficient of
`eq:leading-z-coeff` at `s = 1` vanishes at `ℓ = L` for the weight `B^{(L)} = 1 - (L+1)t`:
`[t]B^{(L)}/(1-t)^{L+1} = (L+1) - (L+1) = 0`.

**Differs from the paper's route.**  `rem:degree-attainment` extracts that coefficient
directly from the series and observes the two terms cancel; here the same vanishing is read
off `eq:leading-z-coeff`'s polynomial in `ℓ`, which `leadCoeffPoly_eval_one` puts in the
affine form `B(0)(ℓ+1)Λ_Q + B'(0)`.  The affine form is what makes the root's dependence on
the weight visible, and it is what `exists_lateDrop` moves with `L`. -/
theorem leadCoeffPoly_lateWeight_eval [CharZero 𝕜] (L : ℕ) :
    (leadCoeffPoly ((1 : Polynomial 𝕜) - X) (lateWeight L) 1).eval (((L + 1 : ℕ)) : 𝕜) = 0 := by
  rw [leadCoeffPoly_eval_one coeff_zero_one_sub_X_ne _ (L + 1), lateWeight_zero,
    lateWeight_one, lambdaQ_one_sub_X]
  push_cast
  ring

/-- **Paper `rem:degree-attainment`.**  With `Q = 1 - t` and `r = 2`, the weight
`B^{(L)} = 1 - (L+1)t` drops the degree at `M = 2L + 1`: `deg F_{2L+1} < L = ⌊M/r⌋`. -/
theorem natDegree_lt_of_lateWeight [CharZero 𝕜] {L : ℕ} (hL : 1 ≤ L)
    (F : ℕ → Polynomial 𝕜)
    (hrec : ∀ M, denomConv (ftDenom ((1 : Polynomial 𝕜) - X) 2) F M = C (lateWeight L M)) :
    (F (2 * L + 1)).natDegree < L := by
  have hQ0 : ((1 : Polynomial 𝕜) - X).coeff 0 ≠ 0 := coeff_zero_one_sub_X_ne
  have hdiv : (2 * L + 1) / 2 = L := by omega
  have hmod : (2 * L + 1) % 2 = 1 := by omega
  have htop := coeff_top ((1 : Polynomial 𝕜) - X) (by norm_num) hQ0 (lateWeight L) F hrec
    (2 * L + 1)
  rw [hdiv, hmod] at htop
  have hz : PowerSeries.coeff 1 (ftTail ((1 : Polynomial 𝕜) - X) (lateWeight L) L) = 0 := by
    have h := coeff_ftTail_eq_eval hQ0 (lateWeight L) 1 L
    rw [leadCoeffPoly_lateWeight_eval L] at h
    have h1 : ((1 : Polynomial 𝕜) - X).coeff 0 = 1 := by simp
    rw [h1, one_pow, one_mul] at h
    exact h
  rw [hz, mul_zero] at htop
  have hle := eventual_natDegree_le ((1 : Polynomial 𝕜) - X) (by norm_num) hQ0
    (lateWeight L) F hrec (2 * L + 1)
  rw [hdiv] at hle
  rcases eq_or_lt_of_le hle with heq | hlt
  · exfalso
    have hlead : (F (2 * L + 1)).leadingCoeff = 0 := by
      rw [Polynomial.leadingCoeff, heq, htop]
    have hzero : F (2 * L + 1) = 0 := Polynomial.leadingCoeff_eq_zero.1 hlead
    rw [hzero, Polynomial.natDegree_zero] at heq
    omega
  · exact hlt

/-- **Paper `rem:degree-attainment`, and the point of it.**  The onset of
`lem:eventual-degree` is not a function of `deg B`: for every `M₀` there is a weight of
degree exactly one — together with a genuine solution of the `sec:reduction` recurrence, not
merely a hypothesis about one — whose degree drops at an index beyond `M₀`.

This is what makes the `M₀` of `eventual_natDegree_eq` depend on `B`. -/
theorem exists_lateDrop [CharZero 𝕜] (M₀ : ℕ) :
    ∃ (b : ℕ → 𝕜) (F : ℕ → Polynomial 𝕜) (M : ℕ),
      b 0 ≠ 0 ∧ b 1 ≠ 0 ∧ (∀ i, 2 ≤ i → b i = 0) ∧ M₀ ≤ M ∧
      (∀ m, denomConv (ftDenom ((1 : Polynomial 𝕜) - X) 2) F m = C (b m)) ∧
      (F M).natDegree < M / 2 := by
  set L : ℕ := max M₀ 1 with hLdef
  have hL : 1 ≤ L := le_max_right _ _
  obtain ⟨F, hF⟩ := exists_denomConv_recurrence ((1 : Polynomial 𝕜) - X) (r := 2)
    (by norm_num) coeff_zero_one_sub_X_ne (lateWeight L)
  refine ⟨lateWeight L, F, 2 * L + 1, ?_, lateWeight_one_ne_zero L,
    fun i hi => lateWeight_of_two_le L hi, ?_, hF, ?_⟩
  · rw [lateWeight_zero]; exact one_ne_zero
  · have : M₀ ≤ L := le_max_left _ _
    omega
  · have hdiv : (2 * L + 1) / 2 = L := by omega
    rw [hdiv]
    exact natDegree_lt_of_lateWeight hL F hF


/-! ### `rem:canonical-bounds-sharp` — the reduced-degree bound is attained -/

/-- The Laurent restriction of `N = a(t) z^E`. -/
theorem curveEval_C_mul_X_pow (Q : Polynomial 𝕜) (r E : ℕ) (a : Polynomial 𝕜) :
    curveEval Q r (C a * X ^ E)
      = T (-((r : ℤ) * E)) * toLaurent (C ((-1 : 𝕜) ^ E) * (a * Q ^ E)) := by
  have hpow : (curveCoord Q r : 𝕜[T;T⁻¹]) ^ E
      = (-1) ^ E * (toLaurent Q) ^ E * T (-((r : ℤ) * E)) := by
    rw [curveCoord, mul_pow, neg_pow, LaurentPolynomial.T_pow]
    ring_nf
  have hC : (toLaurent (C ((-1 : 𝕜) ^ E)) : 𝕜[T;T⁻¹]) = (-1) ^ E := by
    rw [Polynomial.toLaurent_C, map_pow, map_neg, map_one]
  have hmul : (toLaurent (a * Q ^ E) : 𝕜[T;T⁻¹]) = toLaurent a * (toLaurent Q) ^ E := by
    rw [map_mul, map_pow]
  rw [map_mul, map_pow, curveEval_C, curveEval_X, hpow, map_mul, hC, hmul]
  ring

/-- **Paper `rem:canonical-bounds-sharp`.**  For `N = a(t) z^E` with `a(0) ≠ 0`, the canonical
factorization is explicit: `λ_N = -rE` and `B_N = (-1)^E a Q^E`. -/
theorem laurentCanon_C_mul_X_pow (Q : Polynomial 𝕜) {r : ℕ} (hr : 1 ≤ r)
    (hQ0 : Q.coeff 0 ≠ 0) (E : ℕ) {a : Polynomial 𝕜} (ha0 : a.coeff 0 ≠ 0)
    (hdeg : a.degree < ((max Q.natDegree r : ℕ) : WithBot ℕ)) :
    laurentShift Q r (C a * X ^ E) = -((r : ℤ) * E) ∧
      laurentWeight Q r (C a * X ^ E) = C ((-1 : 𝕜) ^ E) * (a * Q ^ E) := by
  have hane : a ≠ 0 := fun h => ha0 (by rw [h]; simp)
  have hQne : Q ≠ 0 := fun h => hQ0 (by rw [h]; simp)
  have hN : (C a * X ^ E : (Polynomial 𝕜)[X]) ≠ 0 := by
    refine mul_ne_zero ?_ (pow_ne_zero _ Polynomial.X_ne_zero)
    simpa using hane
  have hproper : ∀ β, ((C a * X ^ E : (Polynomial 𝕜)[X]).coeff β).degree
      < ((max Q.natDegree r : ℕ) : WithBot ℕ) := by
    intro β
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    by_cases hβ : β = E
    · rw [if_pos hβ, mul_one]; exact hdeg
    · rw [if_neg hβ, mul_zero, Polynomial.degree_zero]; exact WithBot.bot_lt_coe _
  have hQpow : (Q ^ E).coeff 0 = (Q.coeff 0) ^ E := by
    rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_pow,
      ← Polynomial.coeff_zero_eq_eval_zero]
  have hB : (C ((-1 : 𝕜) ^ E) * (a * Q ^ E)).coeff 0 ≠ 0 := by
    rw [Polynomial.coeff_C_mul, Polynomial.mul_coeff_zero, hQpow]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (mul_ne_zero ha0 (pow_ne_zero _ hQ0))
  obtain ⟨h1, h2⟩ :=
    laurentShift_weight_unique Q hr hQ0 hN hproper hB (curveEval_C_mul_X_pow Q r E a)
  exact ⟨h1.symm, h2.symm⟩

/-- **Paper `rem:canonical-bounds-sharp`.**  `eq:reduced-degree-complexity` is *attained*,
not merely safe.  For `q ≥ r` and `N = a(t) z^E` with `a(0) ≠ 0` and `deg a = p < max{q, r}`,
the reduced weight has degree exactly `p + E max{q, r}` — the bound
`natDegree_laurentWeight_le` gives at that `p` and `E`. -/
theorem natDegree_laurentWeight_eq_of_C_mul_X_pow (Q : Polynomial 𝕜) {r : ℕ} (hr : 1 ≤ r)
    (hQ0 : Q.coeff 0 ≠ 0) (hqr : r ≤ Q.natDegree) (E : ℕ)
    {a : Polynomial 𝕜} (ha0 : a.coeff 0 ≠ 0)
    (hdeg : a.degree < ((max Q.natDegree r : ℕ) : WithBot ℕ)) :
    (laurentWeight Q r (C a * X ^ E)).natDegree
      = a.natDegree + E * max Q.natDegree r := by
  have hane : a ≠ 0 := fun h => ha0 (by rw [h]; simp)
  have hQne : Q ≠ 0 := fun h => hQ0 (by rw [h]; simp)
  rw [(laurentCanon_C_mul_X_pow Q hr hQ0 E ha0 hdeg).2,
    Polynomial.natDegree_C_mul (by norm_num : ((-1 : 𝕜) ^ E) ≠ 0),
    Polynomial.natDegree_mul hane (pow_ne_zero _ hQne), Polynomial.natDegree_pow,
    max_eq_left hqr]

/-- **Paper `rem:canonical-bounds-sharp`, the two degree data it names.**  The reduced-degree
bound is attained at every admissible `p` in the regime `q ≥ r`: `N = (1 + t^p) z^E` for
`1 ≤ p < max{q, r}`, and `N = z^E` for `p = 0`.  In each case
`natDegree_laurentWeight_le` is an equality, so the bound cannot be improved. -/
theorem reduced_degree_bound_attained (Q : Polynomial 𝕜) {r : ℕ} (hr : 1 ≤ r)
    (hQ0 : Q.coeff 0 ≠ 0) (hqr : r ≤ Q.natDegree) (E p : ℕ)
    (hp : p < max Q.natDegree r) :
    ∃ N : (Polynomial 𝕜)[X], N ≠ 0 ∧
      (∀ β, (N.coeff β).degree < ((max Q.natDegree r : ℕ) : WithBot ℕ)) ∧
      (∀ β, (N.coeff β).natDegree ≤ p) ∧ N.natDegree ≤ E ∧
      laurentShift Q r N = -((r : ℤ) * E) ∧
      (laurentWeight Q r N).natDegree = p + E * max Q.natDegree r := by
  classical
  rcases Nat.eq_zero_or_pos p with hp0 | hp1
  · -- `p = 0`: the numerator `z^E`
    subst hp0
    have hone : (1 : Polynomial 𝕜).degree < ((max Q.natDegree r : ℕ) : WithBot ℕ) := by
      rw [Polynomial.degree_one]
      exact_mod_cast (by omega : (0 : ℕ) < max Q.natDegree r)
    have ha0 : (1 : Polynomial 𝕜).coeff 0 ≠ 0 := by simp
    refine ⟨C 1 * X ^ E, mul_ne_zero (by simp) (pow_ne_zero _ Polynomial.X_ne_zero),
      ?_, ?_, ?_, ?_, ?_⟩
    · intro β
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      by_cases hβ : β = E
      · rw [if_pos hβ, mul_one]; exact hone
      · rw [if_neg hβ, mul_zero, Polynomial.degree_zero]; exact WithBot.bot_lt_coe _
    · intro β
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      by_cases hβ : β = E
      · rw [if_pos hβ, mul_one, Polynomial.natDegree_one]
      · rw [if_neg hβ, mul_zero, Polynomial.natDegree_zero]
    · refine le_trans Polynomial.natDegree_mul_le ?_
      rw [Polynomial.natDegree_C, Polynomial.natDegree_X_pow, zero_add]
    · exact (laurentCanon_C_mul_X_pow Q hr hQ0 E ha0 hone).1
    · rw [natDegree_laurentWeight_eq_of_C_mul_X_pow Q hr hQ0 hqr E ha0 hone,
        Polynomial.natDegree_one]
  · -- `1 ≤ p`: the numerator `(1 + t^p) z^E`
    have h1 : (1 : Polynomial 𝕜).degree < (X ^ p : Polynomial 𝕜).degree := by
      rw [Polynomial.degree_one, Polynomial.degree_X_pow]
      exact_mod_cast hp1
    have hdegA : (1 + X ^ p : Polynomial 𝕜).degree = (p : WithBot ℕ) := by
      rw [Polynomial.degree_add_eq_right_of_degree_lt h1, Polynomial.degree_X_pow]
    have hnatA : (1 + X ^ p : Polynomial 𝕜).natDegree = p :=
      Polynomial.natDegree_eq_of_degree_eq_some hdegA
    have ha0 : (1 + X ^ p : Polynomial 𝕜).coeff 0 ≠ 0 := by
      rw [Polynomial.coeff_add, Polynomial.coeff_one_zero, Polynomial.coeff_X_pow,
        if_neg (by omega : ¬ (0 = p))]
      norm_num
    have hdeglt : (1 + X ^ p : Polynomial 𝕜).degree
        < ((max Q.natDegree r : ℕ) : WithBot ℕ) := by
      rw [hdegA]; exact_mod_cast hp
    have hAne : (1 + X ^ p : Polynomial 𝕜) ≠ 0 := fun h => ha0 (by rw [h]; simp)
    refine ⟨C (1 + X ^ p : Polynomial 𝕜) * X ^ E, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact mul_ne_zero (Polynomial.C_ne_zero.2 hAne) (pow_ne_zero _ Polynomial.X_ne_zero)
    · intro β
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      by_cases hβ : β = E
      · rw [if_pos hβ, mul_one]; exact hdeglt
      · rw [if_neg hβ, mul_zero, Polynomial.degree_zero]; exact WithBot.bot_lt_coe _
    · intro β
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      by_cases hβ : β = E
      · rw [if_pos hβ, mul_one, hnatA]
      · rw [if_neg hβ, mul_zero, Polynomial.natDegree_zero]; omega
    · refine le_trans Polynomial.natDegree_mul_le ?_
      rw [Polynomial.natDegree_C, Polynomial.natDegree_X_pow, zero_add]
    · exact (laurentCanon_C_mul_X_pow Q hr hQ0 E ha0 hdeglt).1
    · rw [natDegree_laurentWeight_eq_of_C_mul_X_pow Q hr hQ0 hqr E ha0 hdeglt, hnatA]


/-! ### `rem:canonical-bounds-sharp` — the threshold is at the right index

`eq:reduction-threshold` puts the reduction at `E(q-r)`.  The remark's second claim is that
this cannot be lowered: for `q > r` and `N = t^{q-1} z^E` the quotient `S_N` of
`eq:canonical-Laurent-division` carries a nonzero Laurent term of exponent exactly
`E(q-r) - 1`, one below it.  The witness is the content, so `S_N` is exhibited rather than
bounded — `exists_canonical_division` supplies it only existentially. -/

/-- **Paper `rem:canonical-bounds-sharp`.**  `eq:reduction-threshold` is attained.  For
`q > r` and `N = t^{q-1} z^E` the quotient of `eq:canonical-Laurent-division` is explicit; its
`z^0` coefficient is `t^k` times a polynomial `B` with `B(0) ≠ 0`, so its Laurent support runs
from `k` to `k + deg B`, and that top exponent is `E(q-r) - 1` — one **below** the threshold
`E(q-r)`.  The bound of `clearedRestrict_eq` therefore cannot be lowered. -/
theorem canonical_division_threshold_sharp (Q : Polynomial 𝕜) {r q E : ℕ}
    (hr : 1 ≤ r) (hQ0 : Q.coeff 0 ≠ 0) (hq : Q.natDegree = q) (hqr : r < q) (hE : 1 ≤ E) :
    ∃ (S : (𝕜[T;T⁻¹])[X]) (k : ℤ) (B : Polynomial 𝕜),
      (C (X ^ (q - 1)) * X ^ E : (Polynomial 𝕜)[X]).map toLaurent
          = (denomPencil Q r).map toLaurent * S
            + C (curveEval Q r (C (X ^ (q - 1)) * X ^ E)) ∧
        S.coeff 0 = T k * toLaurent B ∧ B.coeff 0 ≠ 0 ∧
        k + (B.natDegree : ℤ) = (E : ℤ) * ((q : ℤ) - (r : ℤ)) - 1 := by
  classical
  have hq1 : 1 ≤ q := by omega
  set g : 𝕜[T;T⁻¹] := curveCoord Q r with hgdef
  set a : 𝕜[T;T⁻¹] := toLaurent (X ^ (q - 1) : Polynomial 𝕜) with hadef
  have ha : a = T ((q : ℤ) - 1) := by
    rw [hadef, Polynomial.toLaurent_X_pow]
    congr 1
    omega
  set Ssum : (𝕜[T;T⁻¹])[X] := ∑ i ∈ Finset.range E, X ^ i * (C g) ^ (E - 1 - i) with hSsum
  refine ⟨C (T (-(r : ℤ)) * a) * Ssum, (q : ℤ) - 1 - (r : ℤ) * E,
    C ((-1 : 𝕜) ^ (E - 1)) * Q ^ (E - 1), ?_, ?_, ?_, ?_⟩
  · -- the division identity
    have hgeom : Ssum * (X - C g) = X ^ E - (C g) ^ E := by
      rw [hSsum]; exact geom_sum₂_mul X (C g) E
    have hcurve : curveEval Q r (C (X ^ (q - 1)) * X ^ E) = a * g ^ E := by
      rw [hadef, hgdef]
      simp only [map_mul, map_pow, curveEval_C, curveEval_X]
    have hM : (C (X ^ (q - 1)) * X ^ E : (Polynomial 𝕜)[X]).map toLaurent = C a * X ^ E := by
      rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, hadef]
    have hTT : (C (T (r : ℤ)) : (𝕜[T;T⁻¹])[X]) * C (T (-(r : ℤ))) = 1 := by
      rw [← Polynomial.C_mul, ← LaurentPolynomial.T_add]
      simp
    have hkey : (denomPencil Q r).map toLaurent * (C (T (-(r : ℤ)) * a) * Ssum)
        = C a * (X ^ E - C (g ^ E)) := by
      rw [map_denomPencil, ← hgdef, Polynomial.C_mul]
      calc C (T (r : ℤ)) * (X - C g) * (C (T (-(r : ℤ))) * C a * Ssum)
          = (C (T (r : ℤ)) * C (T (-(r : ℤ)))) * (C a * (Ssum * (X - C g))) := by ring
        _ = C a * (Ssum * (X - C g)) := by rw [hTT, one_mul]
        _ = C a * (X ^ E - C (g ^ E)) := by rw [hgeom, ← C_pow]
    rw [hM, hcurve, hkey, Polynomial.C_mul]
    ring
  · -- the `z^0` coefficient
    have hs0 : Ssum.coeff 0 = g ^ (E - 1) := by
      rw [hSsum, Polynomial.finsetSum_coeff, Finset.sum_eq_single 0]
      · rw [pow_zero, one_mul, Nat.sub_zero, ← C_pow, Polynomial.coeff_C_zero]
      · intro i hi hi0
        rw [← C_pow, show (X : (𝕜[T;T⁻¹])[X]) ^ i * C (g ^ (E - 1 - i))
            = C (g ^ (E - 1 - i)) * X ^ i by ring, Polynomial.coeff_C_mul,
          Polynomial.coeff_X_pow, if_neg (Ne.symm hi0), mul_zero]
      · intro h
        exact absurd (Finset.mem_range.2 hE) h
    have hgpow : g ^ (E - 1)
        = (-1) ^ (E - 1) * (toLaurent Q) ^ (E - 1) * T (-((r : ℤ) * ((E : ℤ) - 1))) := by
      rw [hgdef, curveCoord, mul_pow, neg_pow, LaurentPolynomial.T_pow]
      rw [show ((E - 1 : ℕ) : ℤ) * -(r : ℤ) = -((r : ℤ) * ((E : ℤ) - 1)) by
        push_cast [Nat.cast_sub hE]; ring]
    rw [Polynomial.coeff_C_mul, hs0, hgpow, ha, map_mul, Polynomial.toLaurent_C, map_pow,
      map_pow, map_neg, map_one]
    rw [show (T (-(r : ℤ)) : 𝕜[T;T⁻¹]) * T ((q : ℤ) - 1)
        * ((-1) ^ (E - 1) * toLaurent Q ^ (E - 1) * T (-((r : ℤ) * ((E : ℤ) - 1))))
        = ((-1) ^ (E - 1) * toLaurent Q ^ (E - 1))
          * (T (-(r : ℤ)) * T ((q : ℤ) - 1) * T (-((r : ℤ) * ((E : ℤ) - 1)))) by ring,
      ← LaurentPolynomial.T_add, ← LaurentPolynomial.T_add,
      show -(r : ℤ) + ((q : ℤ) - 1) + -((r : ℤ) * ((E : ℤ) - 1))
        = (q : ℤ) - 1 - (r : ℤ) * E by ring]
    ring
  · -- `B(0) ≠ 0`, so `k` really is the bottom exponent
    have hQpow : (Q ^ (E - 1)).coeff 0 = (Q.coeff 0) ^ (E - 1) := by
      rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_pow,
        ← Polynomial.coeff_zero_eq_eval_zero]
    rw [Polynomial.coeff_C_mul, hQpow]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ hQ0)
  · -- the top exponent is one below the threshold
    have hQne : Q ≠ 0 := fun h => hQ0 (by rw [h]; simp)
    have hdeg : (C ((-1 : 𝕜) ^ (E - 1)) * Q ^ (E - 1)).natDegree = (E - 1) * q := by
      rw [Polynomial.natDegree_C_mul (by norm_num : ((-1 : 𝕜) ^ (E - 1)) ≠ 0),
        Polynomial.natDegree_pow, hq]
    rw [hdeg]
    push_cast [Nat.cast_sub hE]
    ring

end ForgacsTran
