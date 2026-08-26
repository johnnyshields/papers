/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.Reduction

/-!
# Canonical Laurent reduction

The denominator pencil `D(t,z) = Q(t) + z t^r` cuts out a curve carrying a
Laurent coordinate: `t` is a unit modulo `D`, and `z = g(t) = -Q(t)/t^r`.
Everything here is algebra over an arbitrary field, instantiated at `ℝ` in the
paper; no analysis enters.

## Main statements

* `eq:denominator-coordinate-ring` — `curveEval` is the substitution `z ↦ g(t)`
  from `K[t][z]` onto `K[t,t⁻¹]`; `curveEval_surjective` exhibits `t⁻¹` as a
  polynomial in `t` and `g(t)` (the paper's unit witness), `ker_curveEval`
  identifies the kernel with `(D)`, and `denomCoordRingEquiv` assembles the ring
  isomorphism `K[t,z]/(D) ≅ K[t,t⁻¹]`.  The kernel is reached without Gauss's
  lemma: `t^{rE} z^E ≡ (-Q)^E` modulo `D`, and `D` is coprime to `t` because
  `D ≡ Q(0)` modulo `t`.
* `lem:laurent-reduction` — `curveEval_ne_zero_of_proper` gives `L_N ≠ 0` for a
  nonzero proper numerator, `curveEval_eq_T_mul_weight` and
  `laurentShift_weight_unique` give the canonical factorization
  `L_N = t^{λ_N} B_N` of `eq:canonical-Laurent-factorization` and its
  uniqueness, and `exists_canonical_division` gives
  `eq:canonical-Laurent-division`.
* `eq:reduction-threshold` and `eq:reduction-coeff` — `reduction_coeff` shows
  `P_m = F_{m-λ_N}` for every `m ≥ E_N max{q-r,0}`, where `P` solves the
  `prop:initial-data` recurrence for `N` and `F` solves it for `B_N`.  The
  paper's convention that `[t^k] = 0` for `k < 0` is carried as the explicit
  side condition `λ_N ≤ m`, since `F` is indexed by `ℕ`.
  `reduction_coeff_eventually` is the form the bulk count consumes.
* `eq:reduced-degree-complexity` — `natDegree_laurentWeight_le`.
* `eq:P-linear-combination` — `reduced_tail_linear_combination` writes the
  reduced sequence as the fixed finite combination `∑_j b_j H_{M-j}` of the
  denominator-only sequence `H` of `eq:H-generating`.
* `eq:exact-eventual-degree-shift` — `eventual_natDegree_le_shift` gives the
  upper bound `deg P_m ≤ ⌊(m-λ_N)/r⌋` outright, from the proven half of
  `lem:eventual-degree`; `exact_eventual_degree_shift` composes
  `eq:reduction-coeff` with the full `lem:eventual-degree` for the reduced
  sequence, which it takes as a hypothesis, to give the equality.

## Implementation notes

`rem:canonical-bounds-sharp`, which shows the threshold and the reduced-degree
bound are attained, is not formalized; the sharpness witnesses are checked in
`../scripts/check_canonical_reduction.py`.

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Canonical Laurent
reduction and eventual degree» (`sec:reduction`, `lem:laurent-reduction`).

## Tags

Laurent reduction, rational generating function, initial conditions
-/

open Polynomial
open LaurentPolynomial (T)
open scoped LaurentPolynomial

namespace ForgacsTran

variable {K : Type*} [Field K]

/-! ### A vanishing combination with coprime weights

Supporting step for `lem:laurent-reduction`.  Clearing the Laurent denominators
of `L_N` turns `L_N = 0` into a polynomial identity
`∑_β n_β u^β v^{E-β} = 0` with `u = ±Q`, `v = t^r` coprime.  Reading it modulo
`u` kills every term but `β = 0`, so `u ∣ n_0`; the degree hypothesis then forces
`n_0 = 0` and the argument repeats. -/

/-- Paper `sec:reduction` (supporting step for `lem:laurent-reduction`).  If `u`
and `v` are coprime and every `n_β` has degree below `deg u`, the only vanishing
combination `∑_β n_β u^β v^{E-β}` is the trivial one. -/
theorem eq_zero_of_coprime_comb_eq_zero {u v : K[X]} (huv : IsCoprime u v) :
    ∀ (E : ℕ) (n : ℕ → K[X]), (∀ β, (n β).degree < u.degree) →
      (∑ β ∈ Finset.range (E + 1), n β * u ^ β * v ^ (E - β) = 0) →
      ∀ β, β ≤ E → n β = 0 := by
  have hu0 : ∀ n : ℕ → K[X], (∀ β, (n β).degree < u.degree) → u ≠ 0 := by
    intro n hdeg h0
    have := hdeg 0
    rw [h0, degree_zero] at this
    exact absurd this (by simp)
  intro E
  induction E with
  | zero =>
    intro n hdeg hsum β hβ
    interval_cases β
    simpa using hsum
  | succ E ih =>
    intro n hdeg hsum
    have hune : u ≠ 0 := hu0 n hdeg
    -- Peel the `β = 0` term: `∑_{β=0}^{E+1} = u · ∑_{β=0}^{E} + n_0 v^{E+1}`.
    have hterm : ∀ β ∈ Finset.range (E + 1),
        n (β + 1) * u ^ (β + 1) * v ^ (E + 1 - (β + 1))
          = u * (n (β + 1) * u ^ β * v ^ (E - β)) := by
      intro β _
      have h : E + 1 - (β + 1) = E - β := by omega
      rw [h]; ring
    have hpeel : u * (∑ β ∈ Finset.range (E + 1), n (β + 1) * u ^ β * v ^ (E - β))
        + n 0 * v ^ (E + 1) = 0 := by
      rw [← hsum, Finset.sum_range_succ' (fun β => n β * u ^ β * v ^ (E + 1 - β)) (E + 1)]
      simp only [pow_zero, Nat.sub_zero, mul_one]
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    set Sg := ∑ β ∈ Finset.range (E + 1), n (β + 1) * u ^ β * v ^ (E - β) with hSg
    have hdvd : u ∣ n 0 * v ^ (E + 1) := ⟨-Sg, by linear_combination hpeel⟩
    have hcop : IsCoprime u (v ^ (E + 1)) := huv.pow_right
    have hn0 : n 0 = 0 :=
      eq_zero_of_dvd_of_degree_lt (hcop.dvd_of_dvd_mul_right hdvd) (hdeg 0)
    have hSzero : Sg = 0 := by
      have h1 : u * Sg = 0 := by
        have := hpeel
        rw [hn0] at this
        simpa using this
      exact (mul_eq_zero.mp h1).resolve_left hune
    have hrec := ih (fun β => n (β + 1)) (fun β => hdeg (β + 1)) hSzero
    intro β hβ
    match β with
    | 0 => exact hn0
    | (b + 1) => exact hrec b (by omega)

/-! ### The denominator curve and its Laurent coordinate -/

/-- Paper `sec:reduction`: the denominator pencil `D(t,z) = Q(t) + z t^r`, read
in `K[t][z]`. -/
noncomputable def denomPencil (Q : K[X]) (r : ℕ) : (K[X])[X] :=
  C Q + C (X ^ r) * X

/-- Paper `sec:reduction`, `eq:denominator-coordinate-ring`: the Laurent
coordinate `g(t) = -Q(t)/t^r` of the curve `D = 0`. -/
noncomputable def curveCoord (Q : K[X]) (r : ℕ) : K[T;T⁻¹] :=
  -(toLaurent Q) * T (-(r : ℤ))

/-- Paper `sec:reduction`, `eq:denominator-coordinate-ring`: the substitution
homomorphism `z ↦ g(t)` from `K[t][z]` onto `K[t,t⁻¹]`.  Paper
`eq:Laurent-restriction` writes its value at `N` as `L_N = N(t,g(t))`. -/
noncomputable def curveEval (Q : K[X]) (r : ℕ) : (K[X])[X] →+* K[T;T⁻¹] :=
  eval₂RingHom toLaurent (curveCoord Q r)

@[simp] theorem curveEval_C (Q : K[X]) (r : ℕ) (p : K[X]) :
    curveEval Q r (C p) = toLaurent p := by
  simp [curveEval]

@[simp] theorem curveEval_X (Q : K[X]) (r : ℕ) :
    curveEval Q r X = curveCoord Q r := by
  simp [curveEval]

/-- Paper `sec:reduction`, `eq:denominator-coordinate-ring`: the pencil vanishes
on the curve, `D(t,g(t)) = 0`. -/
@[simp] theorem curveEval_denomPencil (Q : K[X]) (r : ℕ) :
    curveEval Q r (denomPencil Q r) = 0 := by
  simp only [denomPencil, map_add, map_mul, curveEval_C, curveEval_X, curveCoord,
    Polynomial.toLaurent_X_pow]
  rw [show (T (r : ℤ) : K[T;T⁻¹]) * (-(toLaurent Q) * T (-(r : ℤ)))
      = -(toLaurent Q) * (T (r : ℤ) * T (-(r : ℤ))) by ring]
  rw [← LaurentPolynomial.T_add]
  simp

/-! ### Clearing the Laurent denominators

`t^{rE} L_N` is a genuine polynomial once `E ≥ deg_z N`, and equals the
combination `∑_β (-1)^β n_β Q^β t^{r(E-β)}` in the two coprime weights `Q` and
`t^r`.  This is what turns `L_N = 0` into the hypothesis of
`eq_zero_of_coprime_comb_eq_zero`, and it is also how `D ∣ N` is detected. -/

/-- Paper `sec:reduction` (supporting step for `lem:laurent-reduction`): the
Laurent restriction `L_N` cleared by `t^{rE}`, for any `E` at or above
`deg_z N`. -/
noncomputable def clearedRestrict (Q : K[X]) (r E : ℕ) (N : (K[X])[X]) : K[X] :=
  ∑ β ∈ Finset.range (E + 1), (-1) ^ β * N.coeff β * Q ^ β * X ^ (r * (E - β))

/-- Paper `sec:reduction` (supporting): `t^{rE} L_N = clearedRestrict`. -/
theorem toLaurent_clearedRestrict (Q : K[X]) (r E : ℕ) (N : (K[X])[X])
    (hN : N.natDegree < E + 1) :
    toLaurent (clearedRestrict Q r E N) = curveEval Q r N * T ((r : ℤ) * E) := by
  have hsum : curveEval Q r N
      = ∑ β ∈ Finset.range (E + 1), toLaurent (N.coeff β) * curveCoord Q r ^ β := by
    simpa [curveEval] using
      (Polynomial.eval₂_eq_sum_range' (toLaurent (R := K)) hN (curveCoord Q r))
  rw [hsum, Finset.sum_mul, clearedRestrict, map_sum]
  refine Finset.sum_congr rfl fun β hβ => ?_
  have hβE : β ≤ E := by
    have := Finset.mem_range.mp hβ; omega
  have hpow : (curveCoord Q r : K[T;T⁻¹]) ^ β
      = (-1) ^ β * (toLaurent Q) ^ β * T (-((r : ℤ) * β)) := by
    rw [curveCoord, mul_pow, neg_pow, LaurentPolynomial.T_pow]
    ring_nf
  have hshift : ((r : ℤ) * E) - (r : ℤ) * β = ((r * (E - β) : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub hβE]; ring
  rw [hpow, map_mul, map_mul, map_mul, map_pow, map_pow, Polynomial.toLaurent_X_pow,
    map_neg, map_one]
  rw [show (toLaurent (N.coeff β) * ((-1 : K[T;T⁻¹]) ^ β * toLaurent Q ^ β
        * T (-((r : ℤ) * β)))) * T ((r : ℤ) * E)
      = ((-1 : K[T;T⁻¹]) ^ β * toLaurent (N.coeff β) * toLaurent Q ^ β)
        * (T (-((r : ℤ) * β)) * T ((r : ℤ) * E)) by ring]
  rw [← LaurentPolynomial.T_add, show -((r : ℤ) * β) + (r : ℤ) * E
      = ((r : ℤ) * E) - (r : ℤ) * β by ring, hshift]

/-- Paper `sec:reduction`, `eq:denominator-coordinate-ring`: `L_N = 0` exactly
when the cleared combination vanishes. -/
theorem curveEval_eq_zero_iff (Q : K[X]) (r E : ℕ) (N : (K[X])[X])
    (hN : N.natDegree < E + 1) :
    curveEval Q r N = 0 ↔ clearedRestrict Q r E N = 0 := by
  constructor
  · intro h
    have := toLaurent_clearedRestrict Q r E N hN
    rw [h, zero_mul] at this
    exact Polynomial.toLaurent_eq_zero.mp this
  · intro h
    have hz := toLaurent_clearedRestrict Q r E N hN
    rw [h, map_zero] at hz
    have hT : (T ((r : ℤ) * E) : K[T;T⁻¹]) * T (-((r : ℤ) * E)) = 1 := by
      rw [← LaurentPolynomial.T_add]; simp
    calc curveEval Q r N = curveEval Q r N * (T ((r : ℤ) * E) * T (-((r : ℤ) * E))) := by
          rw [hT, mul_one]
      _ = (curveEval Q r N * T ((r : ℤ) * E)) * T (-((r : ℤ) * E)) := by ring
      _ = 0 := by rw [← hz]; simp

/-! ### The kernel is the pencil ideal

`D` is a unit modulo `t` — the paper's witness for `t` being a unit modulo `D`,
read the other way round — so `D` is coprime to `t` in `K[t][z]`.  Since
`t^{rE} N` is congruent to the cleared restriction modulo `D`, a numerator with
`L_N = 0` is divisible by `t^{rE} D`, hence by `D`. -/

/-- Paper `sec:reduction`, `eq:denominator-coordinate-ring`: the pencil is
coprime to `t` in `K[t][z]`, because `D ≡ Q(0)` modulo `t` and `Q(0) ≠ 0`. -/
theorem isCoprime_denomPencil_C_X (Q : K[X]) {r : ℕ} (hr : 1 ≤ r)
    (hQ0 : Q.coeff 0 ≠ 0) : IsCoprime (denomPencil Q r) (C X : (K[X])[X]) := by
  set W : (K[X])[X] := C Q.divX + C (X ^ (r - 1)) * X with hW
  have hXr : (X : K[X]) ^ r = X * X ^ (r - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hD : denomPencil Q r = C (C (Q.coeff 0)) + C X * W := by
    have hQ : X * Q.divX + C (Q.coeff 0) = Q := Polynomial.X_mul_divX_add Q
    rw [denomPencil, hW, hXr]
    rw [show (C (C (Q.coeff 0)) : (K[X])[X]) + C X * (C Q.divX + C (X ^ (r - 1)) * X)
        = C (X * Q.divX + C (Q.coeff 0)) + C (X * X ^ (r - 1)) * X by
      rw [map_add, map_mul, map_mul]; ring]
    rw [hQ]
  refine ⟨C (C (Q.coeff 0)⁻¹), -(C (C (Q.coeff 0)⁻¹) * W), ?_⟩
  rw [hD]
  have : (C (C (Q.coeff 0)⁻¹) : (K[X])[X]) * C (C (Q.coeff 0)) = 1 := by
    rw [← map_mul, ← map_mul, inv_mul_cancel₀ hQ0, map_one, map_one]
  calc C (C (Q.coeff 0)⁻¹) * (C (C (Q.coeff 0)) + C X * W)
        + -(C (C (Q.coeff 0)⁻¹) * W) * C X
      = C (C (Q.coeff 0)⁻¹) * C (C (Q.coeff 0)) := by ring
    _ = 1 := this

/-- Paper `sec:reduction`, `eq:denominator-coordinate-ring` (supporting): modulo
`D` one has `t^r z ≡ -Q`, so `t^{rE} N` is congruent to the cleared
restriction. -/
theorem denomPencil_dvd_sub_clearedRestrict (Q : K[X]) (r E : ℕ) (N : (K[X])[X])
    (hN : N.natDegree < E + 1) :
    denomPencil Q r ∣ C (X ^ (r * E)) * N - C (clearedRestrict Q r E N) := by
  have hNsum : N = ∑ β ∈ Finset.range (E + 1), C (N.coeff β) * X ^ β := by
    conv_lhs => rw [Polynomial.as_sum_range' N (E + 1) hN]
    exact Finset.sum_congr rfl fun β _ => (Polynomial.C_mul_X_pow_eq_monomial).symm
  have hstep : ∀ β : ℕ, denomPencil Q r
      ∣ (C (X ^ (r * β)) * X ^ β - C ((-Q) ^ β) : (K[X])[X]) := by
    intro β
    have hab : (C (X ^ r) * X : (K[X])[X]) - C (-Q) = denomPencil Q r := by
      rw [denomPencil, map_neg]; ring
    have hdv := sub_dvd_pow_sub_pow (C (X ^ r) * X : (K[X])[X]) (C (-Q)) β
    rw [hab] at hdv
    rwa [mul_pow, ← map_pow, ← pow_mul, ← map_pow] at hdv
  have hlhs : C (X ^ (r * E)) * N
      = ∑ β ∈ Finset.range (E + 1), C (X ^ (r * E)) * (C (N.coeff β) * X ^ β) := by
    conv_lhs => rw [hNsum]
    rw [Finset.mul_sum]
  rw [clearedRestrict, map_sum, hlhs, ← Finset.sum_sub_distrib]
  refine Finset.dvd_sum fun β hβ => ?_
  have hβE : β ≤ E := by have := Finset.mem_range.mp hβ; omega
  have hsplit : r * (E - β) + r * β = r * E := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hβE]
  have hfac : C (X ^ (r * E)) * (C (N.coeff β) * X ^ β)
      - C ((-1) ^ β * N.coeff β * Q ^ β * X ^ (r * (E - β)))
      = C (N.coeff β * X ^ (r * (E - β)))
        * (C (X ^ (r * β)) * X ^ β - C ((-Q) ^ β)) := by
    have hb : (N.coeff β * X ^ (r * (E - β))) * X ^ (r * β) = X ^ (r * E) * N.coeff β := by
      rw [mul_assoc, ← pow_add, hsplit]; ring
    have hd : (N.coeff β * X ^ (r * (E - β))) * (-Q) ^ β
        = (-1) ^ β * N.coeff β * Q ^ β * X ^ (r * (E - β)) := by
      rw [neg_pow]; ring
    conv_rhs => rw [mul_sub, ← mul_assoc, ← map_mul, ← map_mul, hb, hd, map_mul]
    ring
  rw [hfac]
  exact Dvd.dvd.mul_left (hstep β) _

/-- **Paper `eq:denominator-coordinate-ring`.**  The kernel of the substitution
`z ↦ g(t)` is exactly the pencil ideal: `K[t,z]/(D) ≅ K[t,t⁻¹]` at the level of
kernels. -/
theorem ker_curveEval (Q : K[X]) {r : ℕ} (hr : 1 ≤ r) (hQ0 : Q.coeff 0 ≠ 0) :
    RingHom.ker (curveEval Q r) = Ideal.span {denomPencil Q r} := by
  apply le_antisymm
  · intro N hN
    have hNz : curveEval Q r N = 0 := hN
    set E := N.natDegree with hE
    have hcl : clearedRestrict Q r E N = 0 :=
      (curveEval_eq_zero_iff Q r E N (by omega)).mp hNz
    have hdvd : denomPencil Q r ∣ C (X ^ (r * E)) * N := by
      have := denomPencil_dvd_sub_clearedRestrict Q r E N (by omega)
      rwa [hcl, map_zero, sub_zero] at this
    have hcop : IsCoprime (denomPencil Q r) (C (X ^ (r * E)) : (K[X])[X]) := by
      have := (isCoprime_denomPencil_C_X Q hr hQ0).pow_right (n := r * E)
      rwa [← map_pow] at this
    exact Ideal.mem_span_singleton.mpr (hcop.dvd_of_dvd_mul_left hdvd)
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact curveEval_denomPencil Q r

/-! ### Surjectivity and the coordinate ring

The paper's witness `1 = t(-(Q_1(t) + z t^{r-1})/Q(0))` says that `t` is a unit
modulo `D`.  Read in `K[t,t⁻¹]` it exhibits `t⁻¹` as a polynomial in `t` and
`g(t)`, which is what makes the substitution surjective. -/

/-- Paper `sec:reduction`, `eq:denominator-coordinate-ring`: `t⁻¹` is a
polynomial in `t` and `g(t)`, the paper's unit witness for `t`. -/
theorem T_neg_one_mem_range (Q : K[X]) {r : ℕ} (hr : 1 ≤ r) (hQ0 : Q.coeff 0 ≠ 0) :
    (T (-1) : K[T;T⁻¹]) ∈ (curveEval Q r).range := by
  have hrm : ((r - 1 : ℕ) : ℤ) = (r : ℤ) - 1 := by
    have : (1 : ℤ) ≤ (r : ℤ) := by exact_mod_cast hr
    push_cast [Nat.cast_sub hr]; ring
  -- `Q = t Q₁ + Q(0)` and `g t^r = -Q` give `Q(0) = -t (Q₁ + g t^{r-1})`.
  set V : K[T;T⁻¹] := LaurentPolynomial.C (Q.coeff 0)⁻¹
      * (-(toLaurent Q.divX + curveCoord Q r * T ((r : ℤ) - 1))) with hV
  have hQsplit : toLaurent Q
      = T 1 * toLaurent Q.divX + LaurentPolynomial.C (Q.coeff 0) := by
    conv_lhs => rw [← Polynomial.X_mul_divX_add Q]
    rw [map_add, map_mul, Polynomial.toLaurent_X, Polynomial.toLaurent_C]
  have hgr : curveCoord Q r * T (r : ℤ) = -(toLaurent Q) := by
    rw [curveCoord, mul_assoc, ← LaurentPolynomial.T_add]
    simp
  have hTV : (T 1 : K[T;T⁻¹]) * V = 1 := by
    have hsplit : (T 1 : K[T;T⁻¹]) * (curveCoord Q r * T ((r : ℤ) - 1))
        = curveCoord Q r * T (r : ℤ) := by
      rw [show (T 1 : K[T;T⁻¹]) * (curveCoord Q r * T ((r : ℤ) - 1))
          = curveCoord Q r * (T 1 * T ((r : ℤ) - 1)) by ring,
        ← LaurentPolynomial.T_add]
      norm_num
    have key : (T 1 : K[T;T⁻¹]) * (-(toLaurent Q.divX + curveCoord Q r * T ((r : ℤ) - 1)))
        = LaurentPolynomial.C (Q.coeff 0) := by
      rw [mul_neg, mul_add, hsplit, hgr, hQsplit]
      ring
    rw [hV, show (T 1 : K[T;T⁻¹]) * (LaurentPolynomial.C (Q.coeff 0)⁻¹
        * (-(toLaurent Q.divX + curveCoord Q r * T ((r : ℤ) - 1))))
        = LaurentPolynomial.C (Q.coeff 0)⁻¹
          * (T 1 * (-(toLaurent Q.divX + curveCoord Q r * T ((r : ℤ) - 1)))) by ring,
      key, ← map_mul, inv_mul_cancel₀ hQ0, map_one]
  have hVmem : V ∈ (curveEval Q r).range := by
    refine ⟨C (Polynomial.C (Q.coeff 0)⁻¹)
      * (-(C Q.divX + X * C (X ^ (r - 1)))), ?_⟩
    simp only [map_mul, map_neg, map_add, curveEval_C, curveEval_X,
      Polynomial.toLaurent_C, Polynomial.toLaurent_X_pow, hrm]
    rw [hV]
  have : (T (-1) : K[T;T⁻¹]) = V := by
    calc (T (-1) : K[T;T⁻¹]) = T (-1) * (T 1 * V) := by rw [hTV, mul_one]
      _ = (T (-1) * T 1) * V := by ring
      _ = V := by rw [← LaurentPolynomial.T_add]; simp
  rwa [this]

/-- **Paper `eq:denominator-coordinate-ring`.**  The substitution `z ↦ g(t)` is
surjective onto `K[t,t⁻¹]`. -/
theorem curveEval_surjective (Q : K[X]) {r : ℕ} (hr : 1 ≤ r) (hQ0 : Q.coeff 0 ≠ 0) :
    Function.Surjective (curveEval Q r) := by
  intro f
  obtain ⟨n, f', hf⟩ := LaurentPolynomial.exists_T_pow f
  have hTn : (T (-1) : K[T;T⁻¹]) ^ n ∈ (curveEval Q r).range :=
    Subring.pow_mem _ (T_neg_one_mem_range Q hr hQ0) n
  have hmem : f ∈ (curveEval Q r).range := by
    have hfe : f = toLaurent f' * T (-1) ^ n := by
      rw [LaurentPolynomial.T_pow]
      have hcancel : (T (n : ℤ) : K[T;T⁻¹]) * T ((n : ℤ) * (-1)) = 1 := by
        rw [← LaurentPolynomial.T_add]; simp
      calc f = f * (T (n : ℤ) * T ((n : ℤ) * (-1))) := by rw [hcancel, mul_one]
        _ = (f * T (n : ℤ)) * T ((n : ℤ) * (-1)) := by ring
        _ = toLaurent f' * T ((n : ℤ) * (-1)) := by rw [hf]
    rw [hfe]
    exact Subring.mul_mem _ ⟨C f', by simp⟩ hTn
  exact RingHom.mem_range.mp hmem

/-- **Paper `eq:denominator-coordinate-ring`.**  `K[t,z]/(D) ≅ K[t,t⁻¹]`, the
Laurent coordinate ring of the denominator curve, with `z ↦ g(t)`. -/
noncomputable def denomCoordRingEquiv (Q : K[X]) {r : ℕ} (hr : 1 ≤ r)
    (hQ0 : Q.coeff 0 ≠ 0) :
    ((K[X])[X] ⧸ Ideal.span {denomPencil Q r}) ≃+* K[T;T⁻¹] :=
  (Ideal.quotEquivOfEq (ker_curveEval Q hr hQ0).symm).trans
    (RingHom.quotientKerEquivOfSurjective (curveEval_surjective Q hr hQ0))

@[simp] theorem denomCoordRingEquiv_mk (Q : K[X]) {r : ℕ} (hr : 1 ≤ r)
    (hQ0 : Q.coeff 0 ≠ 0) (N : (K[X])[X]) :
    denomCoordRingEquiv Q hr hQ0 (Ideal.Quotient.mk _ N) = curveEval Q r N := rfl

/-! ### The restriction of a proper numerator is nonzero

Paper `lem:laurent-reduction`, first assertion.  Clearing denominators turns
`L_N = 0` into a vanishing combination in the coprime weights `Q` and `t^r`;
whichever of the two has the larger degree — that degree is `d = deg_t D` — the
properness bound `deg_t N < d` puts every coefficient below it, and
`eq_zero_of_coprime_comb_eq_zero` applies. -/

/-- Paper `sec:reduction` (supporting): `Q` and `t^r` are coprime, since
`Q(0) ≠ 0`. -/
theorem isCoprime_Q_X_pow (Q : K[X]) (r : ℕ) (hQ0 : Q.coeff 0 ≠ 0) :
    IsCoprime Q ((X : K[X]) ^ r) := by
  have hXQ : IsCoprime (X : K[X]) Q :=
    (Polynomial.prime_X.coprime_iff_not_dvd).mpr (by
      rw [Polynomial.X_dvd_iff]; exact hQ0)
  exact (hXQ.symm).pow_right

/-- **Paper `lem:laurent-reduction`, first assertion.**  For a nonzero proper
numerator — `deg_t N < d = max{deg Q, r}` — the Laurent restriction
`L_N = N(t,g(t))` is nonzero. -/
theorem curveEval_ne_zero_of_proper (Q : K[X]) {r : ℕ} (_hr : 1 ≤ r)
    (hQ0 : Q.coeff 0 ≠ 0) {N : (K[X])[X]} (hN : N ≠ 0)
    (hproper : ∀ β, (N.coeff β).degree < ((max Q.natDegree r : ℕ) : WithBot ℕ)) :
    curveEval Q r N ≠ 0 := by
  intro hzero
  set E := N.natDegree with hE
  have hcl : clearedRestrict Q r E N = 0 :=
    (curveEval_eq_zero_iff Q r E N (by omega)).mp hzero
  set m : ℕ → K[X] := fun β => (-1) ^ β * N.coeff β with hm
  have hmdeg : ∀ β, (m β).degree = (N.coeff β).degree := by
    intro β
    rw [hm]
    simp only
    rcases Nat.even_or_odd β with h | h
    · rw [h.neg_one_pow, one_mul]
    · rw [h.neg_one_pow]
      simp
  have hsum : ∑ β ∈ Finset.range (E + 1), m β * Q ^ β * ((X : K[X]) ^ r) ^ (E - β) = 0 := by
    rw [← hcl, clearedRestrict]
    exact Finset.sum_congr rfl fun β _ => by rw [hm, ← pow_mul]
  have hQne : Q ≠ 0 := fun h => hQ0 (by rw [h]; simp)
  have hmzero : ∀ β, β ≤ E → m β = 0 := by
    rcases le_or_gt r Q.natDegree with hcase | hcase
    · -- `d = deg Q`: read the combination modulo `Q`.
      have hdegQ : Q.degree = ((max Q.natDegree r : ℕ) : WithBot ℕ) := by
        rw [Polynomial.degree_eq_natDegree hQne, max_eq_left hcase]
      exact eq_zero_of_coprime_comb_eq_zero (isCoprime_Q_X_pow Q r hQ0) E m
        (fun β => by rw [hmdeg β, hdegQ]; exact hproper β) hsum
    · -- `d = r`: read it modulo `t^r`, after reflecting the index.
      have hdegX : ((X : K[X]) ^ r).degree = ((max Q.natDegree r : ℕ) : WithBot ℕ) := by
        rw [Polynomial.degree_X_pow, max_eq_right hcase.le]
      have hrefl : ∑ γ ∈ Finset.range (E + 1),
          m (E - γ) * ((X : K[X]) ^ r) ^ γ * Q ^ (E - γ) = 0 := by
        rw [← hsum]
        rw [← Finset.sum_range_reflect
          (fun β => m (E - β) * ((X : K[X]) ^ r) ^ β * Q ^ (E - β)) (E + 1)]
        refine Finset.sum_congr rfl fun γ hγ => ?_
        have hγE : γ ≤ E := by have := Finset.mem_range.mp hγ; omega
        have h1 : E + 1 - 1 - γ = E - γ := by omega
        have h2 : E - (E - γ) = γ := by omega
        rw [h1, h2]
        ring
      intro β hβ
      have := eq_zero_of_coprime_comb_eq_zero ((isCoprime_Q_X_pow Q r hQ0).symm) E
        (fun γ => m (E - γ)) (fun γ => by rw [hmdeg (E - γ), hdegX]; exact hproper (E - γ))
        hrefl (E - β) (by omega)
      rwa [show E - (E - β) = β by omega] at this
  apply hN
  refine Polynomial.ext fun β => ?_
  rw [Polynomial.coeff_zero]
  rcases le_or_gt β E with hβ | hβ
  · have h0 := hmzero β hβ
    rw [hm] at h0
    simp only at h0
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    · exact h
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

/-! ### The canonical Laurent factorization

Paper `eq:canonical-Laurent-factorization`: a nonzero Laurent polynomial is
`t^λ B` for a unique integer `λ` and a unique polynomial `B` with `B(0) ≠ 0`. -/

/-- Paper `eq:canonical-Laurent-factorization` (existence). -/
theorem exists_canonical_factorization {f : K[T;T⁻¹]} (hf : f ≠ 0) :
    ∃ p : ℤ × K[X], p.2.coeff 0 ≠ 0 ∧ f = T p.1 * toLaurent p.2 := by
  obtain ⟨n, f', hf'⟩ := LaurentPolynomial.exists_T_pow f
  have hTn : ∀ (h : K[T;T⁻¹]) (k : ℤ), h * T k * T (-k) = h := by
    intro h k
    rw [mul_assoc, ← LaurentPolynomial.T_add]
    simp
  have hf'0 : f' ≠ 0 := by
    intro h
    rw [h, map_zero] at hf'
    apply hf
    have h2 : f * T (n : ℤ) * T (-(n : ℤ)) = f := hTn f (n : ℤ)
    rw [← hf', zero_mul] at h2
    exact h2.symm
  obtain ⟨B, hBeq, hBnd⟩ :=
    Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd f' hf'0 0
  set k := f'.rootMultiplicity 0 with hk
  rw [map_zero, sub_zero] at hBeq hBnd
  refine ⟨((k : ℤ) - n, B), ?_, ?_⟩
  · simpa [Polynomial.X_dvd_iff] using hBnd
  · have h1 : toLaurent f' = T (k : ℤ) * toLaurent B := by
      rw [hBeq, map_mul, Polynomial.toLaurent_X_pow]
    change f = T ((k : ℤ) - (n : ℤ)) * toLaurent B
    rw [LaurentPolynomial.T_sub]
    calc f = f * T (n : ℤ) * T (-(n : ℤ)) := (hTn f (n : ℤ)).symm
      _ = T (k : ℤ) * toLaurent B * T (-(n : ℤ)) := by rw [← hf', h1]
      _ = T (k : ℤ) * T (-(n : ℤ)) * toLaurent B := by ring

/-- Paper `eq:canonical-Laurent-factorization` (uniqueness). -/
theorem canonical_factorization_unique {l l' : ℤ} {B B' : K[X]} (hB : B.coeff 0 ≠ 0)
    (hB' : B'.coeff 0 ≠ 0)
    (h : (T l : K[T;T⁻¹]) * toLaurent B = T l' * toLaurent B') :
    l = l' ∧ B = B' := by
  have key : ∀ (a a' : ℤ) (C C' : K[X]), C.coeff 0 ≠ 0 → a ≤ a' →
      (T a : K[T;T⁻¹]) * toLaurent C = T a' * toLaurent C' → a = a' ∧ C = C' := by
    intro a a' C C' hC hle heq
    set k := (a' - a).toNat with hkdef
    have hka : ((k : ℤ)) = a' - a := Int.toNat_of_nonneg (by omega)
    have h1 : toLaurent C = toLaurent ((X : K[X]) ^ k * C') := by
      have hstep : (T (-a) : K[T;T⁻¹]) * (T a * toLaurent C)
          = T (-a) * (T a' * toLaurent C') := by rw [heq]
      rw [← mul_assoc, ← mul_assoc, ← LaurentPolynomial.T_add,
        ← LaurentPolynomial.T_add] at hstep
      simp only [neg_add_cancel, LaurentPolynomial.T_zero, one_mul] at hstep
      rw [show (-a + a' : ℤ) = a' - a from by ring] at hstep
      rw [hstep, map_mul, Polynomial.toLaurent_X_pow, hka]
    have h2 : C = (X : K[X]) ^ k * C' := Polynomial.toLaurent_injective h1
    have hk0 : k = 0 := by
      by_contra hne
      apply hC
      rw [h2, Polynomial.mul_coeff_zero, Polynomial.coeff_X_pow, if_neg (Ne.symm hne),
        zero_mul]
    refine ⟨by omega, ?_⟩
    rw [h2, hk0, pow_zero, one_mul]
  rcases le_total l l' with hle | hle
  · exact key l l' B B' hB hle h
  · obtain ⟨h1, h2⟩ := key l' l B' B hB' hle h.symm
    exact ⟨h1.symm, h2.symm⟩

open scoped Classical in
/-- Paper `eq:canonical-Laurent-factorization`: the canonical pair `(λ, B)` of a
Laurent polynomial, with the junk value `(0,0)` at `0`. -/
noncomputable def laurentCanon (f : K[T;T⁻¹]) : ℤ × K[X] :=
  if h : f = 0 then (0, 0) else (exists_canonical_factorization h).choose

/-- Paper `eq:canonical-Laurent-factorization`: `λ_N`, the Laurent valuation. -/
noncomputable def laurentShift (Q : K[X]) (r : ℕ) (N : (K[X])[X]) : ℤ :=
  (laurentCanon (curveEval Q r N)).1

/-- Paper `eq:canonical-Laurent-factorization`: `B_N`, the reduced weight. -/
noncomputable def laurentWeight (Q : K[X]) (r : ℕ) (N : (K[X])[X]) : K[X] :=
  (laurentCanon (curveEval Q r N)).2

theorem laurentCanon_spec {f : K[T;T⁻¹]} (hf : f ≠ 0) :
    (laurentCanon f).2.coeff 0 ≠ 0 ∧ f = T (laurentCanon f).1 * toLaurent (laurentCanon f).2 := by
  classical
  rw [laurentCanon, dif_neg hf]
  exact (exists_canonical_factorization hf).choose_spec

/-- **Paper `eq:canonical-Laurent-factorization`.**  `L_N = t^{λ_N} B_N` with
`B_N(0) ≠ 0`, for a nonzero proper numerator. -/
theorem curveEval_eq_T_mul_weight (Q : K[X]) {r : ℕ} (hr : 1 ≤ r) (hQ0 : Q.coeff 0 ≠ 0)
    {N : (K[X])[X]} (hN : N ≠ 0)
    (hproper : ∀ β, (N.coeff β).degree < ((max Q.natDegree r : ℕ) : WithBot ℕ)) :
    (laurentWeight Q r N).coeff 0 ≠ 0 ∧
      curveEval Q r N
        = T (laurentShift Q r N) * toLaurent (laurentWeight Q r N) :=
  laurentCanon_spec (curveEval_ne_zero_of_proper Q hr hQ0 hN hproper)

/-- **Paper `eq:canonical-Laurent-factorization`, uniqueness.**  The pair
`(λ_N, B_N)` is the only one. -/
theorem laurentShift_weight_unique (Q : K[X]) {r : ℕ} (hr : 1 ≤ r) (hQ0 : Q.coeff 0 ≠ 0)
    {N : (K[X])[X]} (hN : N ≠ 0)
    (hproper : ∀ β, (N.coeff β).degree < ((max Q.natDegree r : ℕ) : WithBot ℕ))
    {l : ℤ} {B : K[X]} (hB : B.coeff 0 ≠ 0)
    (heq : curveEval Q r N = T l * toLaurent B) :
    l = laurentShift Q r N ∧ B = laurentWeight Q r N := by
  obtain ⟨hw0, hw⟩ := curveEval_eq_T_mul_weight Q hr hQ0 hN hproper
  exact canonical_factorization_unique hB hw0 (heq.symm.trans hw)

/-! ### Division on the curve

Paper `eq:canonical-Laurent-division`: `N = D S_N + L_N` with `S_N` a Laurent
polynomial in `t` and a polynomial in `z`.  Over `K[t,t⁻¹]` the pencil is
`t^r (z - g)`, and `t^r` is a unit, so this is division of `N` by the monic
linear `z - g`. -/

/-- Paper `sec:reduction` (supporting): over the Laurent ring the pencil
factors as `D = t^r (z - g)`. -/
theorem map_denomPencil (Q : K[X]) (r : ℕ) :
    (denomPencil Q r).map toLaurent
      = C (T (r : ℤ)) * (X - C (curveCoord Q r)) := by
  have hgr : (T (r : ℤ) : K[T;T⁻¹]) * curveCoord Q r = -(toLaurent Q) := by
    rw [curveCoord, show (T (r : ℤ) : K[T;T⁻¹]) * (-(toLaurent Q) * T (-(r : ℤ)))
      = -(toLaurent Q) * (T (r : ℤ) * T (-(r : ℤ))) by ring, ← LaurentPolynomial.T_add]
    simp
  rw [denomPencil]
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
    Polynomial.toLaurent_X_pow]
  rw [mul_sub, ← map_mul, hgr, map_neg]
  ring

/-- **Paper `eq:canonical-Laurent-division`.**  `N = D S_N + L_N` with
`S_N ∈ K[t,t⁻¹][z]`. -/
theorem exists_canonical_division (Q : K[X]) (r : ℕ) (N : (K[X])[X]) :
    ∃ S : (K[T;T⁻¹])[X],
      N.map toLaurent = (denomPencil Q r).map toLaurent * S + C (curveEval Q r N) := by
  set g := curveCoord Q r with hg
  set M := N.map (toLaurent (R := K)) with hM
  have hmonic : (X - C g : (K[T;T⁻¹])[X]).Monic := Polynomial.monic_X_sub_C g
  have heval : M.eval g = curveEval Q r N := by
    rw [hM, Polynomial.eval_map]
    rfl
  have hdiv : M = (X - C g) * (M /ₘ (X - C g)) + C (curveEval Q r N) := by
    have hd := Polynomial.modByMonic_add_div M (X - C g)
    rw [Polynomial.modByMonic_X_sub_C_eq_C_eval, heval] at hd
    linear_combination -hd
  refine ⟨C (T (-(r : ℤ))) * (M /ₘ (X - C g)), ?_⟩
  rw [map_denomPencil]
  rw [show (C (T (r : ℤ)) * (X - C g) : (K[T;T⁻¹])[X]) * (C (T (-(r : ℤ)))
        * (M /ₘ (X - C g)))
      = (C (T (r : ℤ)) * C (T (-(r : ℤ)))) * ((X - C g) * (M /ₘ (X - C g))) by ring]
  rw [← map_mul, ← LaurentPolynomial.T_add]
  simp only [add_neg_cancel, LaurentPolynomial.T_zero, map_one, one_mul]
  exact hdiv

/-! ### The reduced degree

Paper `eq:reduced-degree-complexity`: `deg B_N ≤ p_N + E_N max{q,r}`.  Clearing
by `t^{rE}` turns `L_N` into a polynomial `A` of that degree, and `A = t^μ B_N`
for a nonnegative `μ`, so `B_N` cannot be longer. -/

/-- Paper `sec:reduction` (supporting): a polynomial equal to `t^l B` with
`B(0) ≠ 0` is `t^l B` with `l` a nonnegative integer. -/
theorem exists_pow_mul_of_toLaurent_eq (l : ℤ) {A B : K[X]} (hB : B.coeff 0 ≠ 0)
    (h : toLaurent A = T l * toLaurent B) : ∃ k : ℕ, (k : ℤ) = l ∧ A = X ^ k * B := by
  have hBne : B ≠ 0 := fun hb => hB (by rw [hb]; simp)
  have hAne : A ≠ 0 := by
    intro ha
    rw [ha, map_zero] at h
    have hz : (T (-l) : K[T;T⁻¹]) * (T l * toLaurent B) = 0 := by rw [← h, mul_zero]
    rw [← mul_assoc, ← LaurentPolynomial.T_add] at hz
    simp only [neg_add_cancel, LaurentPolynomial.T_zero, one_mul] at hz
    exact hBne (Polynomial.toLaurent_eq_zero.mp hz)
  obtain ⟨A', hAeq, hAnd⟩ :=
    Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd A hAne 0
  set k := A.rootMultiplicity 0 with hk
  rw [map_zero, sub_zero] at hAeq hAnd
  have hA'0 : A'.coeff 0 ≠ 0 := by simpa [Polynomial.X_dvd_iff] using hAnd
  have hfac : (T (k : ℤ) : K[T;T⁻¹]) * toLaurent A' = T l * toLaurent B := by
    rw [← h, hAeq, map_mul, Polynomial.toLaurent_X_pow]
  obtain ⟨hkl, hAB⟩ := canonical_factorization_unique hA'0 hB hfac
  exact ⟨k, hkl, by rw [hAeq, hAB]⟩

/-- Paper `sec:reduction` (supporting): if a polynomial equals `t^l B` with
`B(0) ≠ 0`, then `B` is no longer than it. -/
theorem natDegree_le_of_toLaurent_eq (l : ℤ) {A B : K[X]} (hB : B.coeff 0 ≠ 0)
    (h : toLaurent A = T l * toLaurent B) : B.natDegree ≤ A.natDegree := by
  obtain ⟨k, -, hAeq⟩ := exists_pow_mul_of_toLaurent_eq l hB h
  have hBne : B ≠ 0 := fun hb => hB (by rw [hb]; simp)
  rw [hAeq, Polynomial.natDegree_mul (pow_ne_zero _ Polynomial.X_ne_zero) hBne]
  omega

/-- Paper `sec:reduction` (supporting): the cleared restriction obeys the
`eq:reduced-degree-complexity` bound. -/
theorem natDegree_clearedRestrict_le (Q : K[X]) (r E : ℕ) (N : (K[X])[X]) {p : ℕ}
    (hp : ∀ β, (N.coeff β).natDegree ≤ p) :
    (clearedRestrict Q r E N).natDegree ≤ p + E * max Q.natDegree r := by
  rw [clearedRestrict]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun β hβ => ?_
  have hβE : β ≤ E := by have := Finset.mem_range.mp hβ; omega
  have hbound : β * Q.natDegree + r * (E - β) ≤ E * max Q.natDegree r := by
    have h1 : β * Q.natDegree ≤ β * max Q.natDegree r :=
      Nat.mul_le_mul_left _ (le_max_left _ _)
    have h2 : r * (E - β) ≤ max Q.natDegree r * (E - β) :=
      Nat.mul_le_mul_right _ (le_max_right _ _)
    have h3 : β * max Q.natDegree r + max Q.natDegree r * (E - β)
        = E * max Q.natDegree r := by
      rw [mul_comm (max Q.natDegree r) (E - β), ← Nat.add_mul, Nat.add_sub_cancel' hβE]
    omega
  calc ((-1 : K[X]) ^ β * N.coeff β * Q ^ β * X ^ (r * (E - β))).natDegree
      ≤ ((-1 : K[X]) ^ β * N.coeff β * Q ^ β).natDegree
        + ((X : K[X]) ^ (r * (E - β))).natDegree := Polynomial.natDegree_mul_le
    _ ≤ (((-1 : K[X]) ^ β * N.coeff β).natDegree + (Q ^ β).natDegree)
        + ((X : K[X]) ^ (r * (E - β))).natDegree :=
      Nat.add_le_add_right Polynomial.natDegree_mul_le _
    _ ≤ ((0 + (N.coeff β).natDegree) + β * Q.natDegree) + r * (E - β) := by
      gcongr
      · calc ((-1 : K[X]) ^ β * N.coeff β).natDegree
            ≤ ((-1 : K[X]) ^ β).natDegree + (N.coeff β).natDegree :=
              Polynomial.natDegree_mul_le
          _ ≤ 0 + (N.coeff β).natDegree := by
              have hc : ((-1 : K[X]) ^ β).natDegree = 0 := by
                rw [← map_one (Polynomial.C : K →+* K[X]), ← map_neg, ← map_pow,
                  Polynomial.natDegree_C]
              omega
      · exact Polynomial.natDegree_pow_le
      · rw [Polynomial.natDegree_X_pow]
    _ ≤ p + E * max Q.natDegree r := by
      have := hp β
      omega

/-- Paper `sec:reduction` (supporting): the cleared restriction is `t^μ B_N`,
with `μ = λ_N + rE` a nonnegative integer. -/
theorem clearedRestrict_eq (Q : K[X]) {r : ℕ} (hr : 1 ≤ r) (hQ0 : Q.coeff 0 ≠ 0)
    {N : (K[X])[X]} (hN : N ≠ 0)
    (hproper : ∀ β, (N.coeff β).degree < ((max Q.natDegree r : ℕ) : WithBot ℕ))
    {E : ℕ} (hE : N.natDegree ≤ E) :
    ∃ μ : ℕ, (μ : ℤ) = laurentShift Q r N + (r : ℤ) * E ∧
      clearedRestrict Q r E N = X ^ μ * laurentWeight Q r N := by
  obtain ⟨hw0, hw⟩ := curveEval_eq_T_mul_weight Q hr hQ0 hN hproper
  have hcl : toLaurent (clearedRestrict Q r E N)
      = T (laurentShift Q r N + (r : ℤ) * E) * toLaurent (laurentWeight Q r N) := by
    rw [toLaurent_clearedRestrict Q r E N (by omega), hw, LaurentPolynomial.T_add]
    ring
  exact exists_pow_mul_of_toLaurent_eq _ hw0 hcl

/-- **Paper `eq:reduced-degree-complexity`.**  `deg B_N ≤ p_N + E_N max{q,r}`,
where `p_N` bounds `deg_t N` and `E_N` bounds `deg_z N`. -/
theorem natDegree_laurentWeight_le (Q : K[X]) {r : ℕ} (hr : 1 ≤ r) (hQ0 : Q.coeff 0 ≠ 0)
    {N : (K[X])[X]} (hN : N ≠ 0)
    (hproper : ∀ β, (N.coeff β).degree < ((max Q.natDegree r : ℕ) : WithBot ℕ))
    {p E : ℕ} (hp : ∀ β, (N.coeff β).natDegree ≤ p) (hE : N.natDegree ≤ E) :
    (laurentWeight Q r N).natDegree ≤ p + E * max Q.natDegree r := by
  obtain ⟨hw0, hw⟩ := curveEval_eq_T_mul_weight Q hr hQ0 hN hproper
  have hcl : toLaurent (clearedRestrict Q r E N)
      = T (laurentShift Q r N + (r : ℤ) * E) * toLaurent (laurentWeight Q r N) := by
    rw [toLaurent_clearedRestrict Q r E N (by omega), hw, LaurentPolynomial.T_add]
    ring
  exact le_trans (natDegree_le_of_toLaurent_eq _ hw0 hcl)
    (natDegree_clearedRestrict_le Q r E N hp)

/-! ### The reduced coefficient recurrence

Paper `eq:reduction-coeff`: for all sufficiently large `m`, the coefficient
polynomial `P_m` of `N/D` is the coefficient of `t^{m-λ_N}` in `B_N/D`.

Clearing by `t^{rE}` turns `eq:canonical-Laurent-division` into a polynomial
identity `t^{rE} N = D S̃ + t^{μ} B_N` with `S̃ ∈ K[t,z]` and `μ = λ_N + rE ≥ 0`.
Exchanging the two indeterminates reads that off as an identity of denominator
recurrences, and `prop:initial-data` uniqueness identifies the two shifted
sequences up to the finitely many coefficients of `S̃`. -/

/-- Paper `sec:reduction` (supporting): the exchange of the indeterminates,
`K[t][z] → K[z][t]`.  Its `t`-coefficients are the `z`-polynomials that the
denominator recurrence of `prop:initial-data` acts on. -/
noncomputable def swapVars : (K[X])[X] →+* (K[X])[X] :=
  eval₂RingHom (Polynomial.mapRingHom (Polynomial.C : K →+* K[X])) (C X)

@[simp] theorem swapVars_C (p : K[X]) :
    swapVars (C p) = p.map (Polynomial.C : K →+* K[X]) := by
  simp [swapVars]

@[simp] theorem swapVars_X : swapVars (X : (K[X])[X]) = C X := by
  simp [swapVars]

/-- Paper `sec:reduction` (supporting): the exchanged pencil has the
`t`-coefficients `d_i = C(Q_i) + [i=r]·z` of `lem:eventual-degree`. -/
theorem coeff_swapVars_denomPencil (Q : K[X]) (r j : ℕ) :
    (swapVars (denomPencil Q r)).coeff j = ftDenom Q r j := by
  have hmono : ((X : (K[X])[X]) ^ r * C X) = Polynomial.monomial r (X : K[X]) := by
    rw [mul_comm, Polynomial.C_mul_X_pow_eq_monomial]
  rw [denomPencil, map_add, map_mul, swapVars_C, swapVars_C, swapVars_X,
    Polynomial.map_pow, Polynomial.map_X, hmono, ftDenom, Polynomial.coeff_add,
    Polynomial.coeff_map, Polynomial.coeff_monomial]
  by_cases h : j = r
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun hc => h hc.symm)]

/-- Paper `prop:initial-data` (supporting): multiplication of polynomials is the
denominator convolution of their coefficients. -/
theorem coeff_mul_eq_denomConv {A : Type*} [CommRing A] (p q : A[X]) (m : ℕ) :
    (p * q).coeff m = denomConv p.coeff q.coeff m := by
  rw [Polynomial.coeff_mul, denomConv, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

/-- Paper `sec:reduction` (supporting): shifting a sequence by `k` shifts its
denominator convolution by `k`. -/
theorem denomConv_shift {A : Type*} [CommRing A] (d P : ℕ → A) (k m : ℕ) :
    denomConv d (fun i => if k ≤ i then P (i - k) else 0) m
      = if k ≤ m then denomConv d P (m - k) else 0 := by
  simp only [denomConv]
  by_cases hk : k ≤ m
  · rw [if_pos hk]
    have hle : m - k + 1 ≤ m + 1 := by omega
    have hsub : Finset.range (m - k + 1) ⊆ Finset.range (m + 1) := by
      intro x hx
      simp only [Finset.mem_range] at hx ⊢
      omega
    have hzero : ∀ j ∈ Finset.range (m + 1), j ∉ Finset.range (m - k + 1) →
        d j * (if k ≤ m - j then P (m - j - k) else 0) = 0 := by
      intro j hj hj2
      have h1 : ¬ (j < m - k + 1) := fun h => hj2 (Finset.mem_range.mpr h)
      have h2 : j < m + 1 := Finset.mem_range.mp hj
      have hneg : ¬ (k ≤ m - j) := by omega
      rw [if_neg hneg, mul_zero]
    rw [← Finset.sum_subset hsub hzero]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j < m - k + 1 := Finset.mem_range.mp hj
    have hpos : k ≤ m - j := by omega
    rw [if_pos hpos]
    congr 2
    omega
  · rw [if_neg hk]
    refine Finset.sum_eq_zero fun j hj => ?_
    have hj' : j < m + 1 := Finset.mem_range.mp hj
    have hneg : ¬ (k ≤ m - j) := by omega
    rw [if_neg hneg, mul_zero]

/-- Paper `sec:reduction` (supporting): the `t`-degree of the exchanged
numerator is bounded by the `t`-degrees of its `z`-coefficients. -/
theorem natDegree_swapVars_le {N : (K[X])[X]} {p : ℕ}
    (h : ∀ β, (N.coeff β).natDegree ≤ p) : (swapVars N).natDegree ≤ p := by
  have hsum : swapVars N = ∑ β ∈ Finset.range (N.natDegree + 1),
      (N.coeff β).map (Polynomial.C : K →+* K[X]) * (C X : (K[X])[X]) ^ β := by
    simpa [swapVars] using
      (Polynomial.eval₂_eq_sum_range' (Polynomial.mapRingHom (Polynomial.C : K →+* K[X]))
        (Nat.lt_succ_self N.natDegree) (C X : (K[X])[X]))
  rw [hsum]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun β _ => ?_
  calc ((N.coeff β).map (Polynomial.C : K →+* K[X]) * (C X : (K[X])[X]) ^ β).natDegree
      ≤ ((N.coeff β).map (Polynomial.C : K →+* K[X])).natDegree
        + ((C X : (K[X])[X]) ^ β).natDegree := Polynomial.natDegree_mul_le
    _ ≤ p + 0 := by
        gcongr
        · exact le_trans Polynomial.natDegree_map_le (h β)
        · rw [← map_pow, Polynomial.natDegree_C]
    _ = p := by omega

/-- Paper `sec:reduction` (supporting): the exchanged pencil has a nonzero
coefficient at `t^d`, `d = max{deg Q, r}`. -/
theorem coeff_swapVars_denomPencil_max_ne_zero (Q : K[X]) {r : ℕ} (_hr : 1 ≤ r)
    (hQ0 : Q.coeff 0 ≠ 0) :
    (swapVars (denomPencil Q r)).coeff (max Q.natDegree r) ≠ 0 := by
  have hQne : Q ≠ 0 := fun h => hQ0 (by rw [h]; simp)
  rw [coeff_swapVars_denomPencil, ftDenom]
  by_cases h : max Q.natDegree r = r
  · rw [if_pos h]
    intro hc
    have h1 : (Polynomial.C (Q.coeff (max Q.natDegree r)) + X : K[X]).coeff 1
        = (0 : K[X]).coeff 1 := by rw [hc]
    simp at h1
  · rw [if_neg h, add_zero]
    have hq : max Q.natDegree r = Q.natDegree := by
      rcases max_cases Q.natDegree r with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact h1
      · exact absurd h1 h
    rw [hq]
    exact fun hc => Polynomial.leadingCoeff_ne_zero.mpr hQne
      (by rwa [Polynomial.leadingCoeff, ← Polynomial.C_eq_zero])

/-- **Paper `eq:reduction-coeff`.**  Let `P` be the coefficient sequence of
`N/D` — the solution of the `prop:initial-data` recurrence with right-hand side
the `t`-coefficients of `N` — and let `F` be that of `B_N/D`.  Then
`P_m = F_{m-λ_N}` for all sufficiently large `m`. -/
theorem reduction_coeff (Q : K[X]) {r : ℕ} (hr : 1 ≤ r) (hQ0 : Q.coeff 0 ≠ 0)
    {N : (K[X])[X]} (hN : N ≠ 0)
    (hproper : ∀ β, (N.coeff β).degree < ((max Q.natDegree r : ℕ) : WithBot ℕ))
    (P F : ℕ → K[X])
    (hP : ∀ m, denomConv (ftDenom Q r) P m = (swapVars N).coeff m)
    (hF : ∀ M, denomConv (ftDenom Q r) F M
      = Polynomial.C ((laurentWeight Q r N).coeff M)) :
    ∀ m : ℕ, N.natDegree * (Q.natDegree - r) ≤ m → laurentShift Q r N ≤ (m : ℤ) →
      P m = F (((m : ℤ) - laurentShift Q r N).toNat) := by
  classical
  set E := N.natDegree with hE
  set B := laurentWeight Q r N with hB
  set l := laurentShift Q r N with hl
  obtain ⟨hw0, hw⟩ := curveEval_eq_T_mul_weight Q hr hQ0 hN hproper
  have hcl : toLaurent (clearedRestrict Q r E N)
      = T (l + (r : ℤ) * E) * toLaurent B := by
    rw [toLaurent_clearedRestrict Q r E N (by omega), hw, LaurentPolynomial.T_add]
    ring
  obtain ⟨μ, hμ, hA⟩ := exists_pow_mul_of_toLaurent_eq _ hw0 hcl
  obtain ⟨S, hS⟩ := denomPencil_dvd_sub_clearedRestrict Q r E N (by omega)
  -- The cleared division identity, exchanged into `K[z][t]`.
  have hid : (X : K[X][X]) ^ (r * E) * swapVars N
      = swapVars (denomPencil Q r) * swapVars S
        + X ^ μ * B.map (Polynomial.C : K →+* K[X]) := by
    have h0 : C ((X : K[X]) ^ (r * E)) * N
        = denomPencil Q r * S + C ((X : K[X]) ^ μ * B) := by
      rw [← hA]; linear_combination hS
    have h1 := congrArg (swapVars (K := K)) h0
    rw [map_mul, map_add, map_mul, swapVars_C, swapVars_C, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X] at h1
    exact h1
  set d := ftDenom Q r with hd
  set Pa : ℕ → K[X] := fun i => if r * E ≤ i then P (i - r * E) else 0 with hPa
  set Fa : ℕ → K[X] := fun i => if μ ≤ i then F (i - μ) else 0 with hFa
  have hkey : ∀ m, denomConv d Pa m
      = denomConv d (fun i => (swapVars S).coeff i + Fa i) m := by
    intro m
    have hL : denomConv d Pa m = ((X : K[X][X]) ^ (r * E) * swapVars N).coeff m := by
      rw [hPa, denomConv_shift,
        show (X : K[X][X]) ^ (r * E) * swapVars N = swapVars N * X ^ (r * E) from mul_comm _ _,
        Polynomial.coeff_mul_X_pow']
      by_cases h : r * E ≤ m
      · rw [if_pos h, if_pos h, hP]
      · rw [if_neg h, if_neg h]
    have hR1 : denomConv d (fun i => (swapVars S).coeff i) m
        = (swapVars (denomPencil Q r) * swapVars S).coeff m := by
      rw [coeff_mul_eq_denomConv]
      exact Finset.sum_congr rfl fun j _ => by
        rw [hd, coeff_swapVars_denomPencil]
    have hR2 : denomConv d Fa m
        = ((X : K[X][X]) ^ μ * B.map (Polynomial.C : K →+* K[X])).coeff m := by
      rw [hFa, denomConv_shift,
        show (X : K[X][X]) ^ μ * B.map (Polynomial.C : K →+* K[X])
          = B.map (Polynomial.C : K →+* K[X]) * X ^ μ from mul_comm _ _,
        Polynomial.coeff_mul_X_pow']
      by_cases h : μ ≤ m
      · rw [if_pos h, if_pos h, hF, Polynomial.coeff_map]
      · rw [if_neg h, if_neg h]
    have hRsplit : denomConv d (fun i => (swapVars S).coeff i + Fa i) m
        = denomConv d (fun i => (swapVars S).coeff i) m + denomConv d Fa m := by
      simp only [denomConv, mul_add]
      rw [Finset.sum_add_distrib]
    rw [hL, hRsplit, hR1, hR2, hid, Polynomial.coeff_add]
  have hunit : IsUnit (d 0) := by
    rw [hd, ftDenom_zero Q hr]
    exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hQ0)
  have heq := initial_data_unique hunit hkey
  -- `eq:reduction-threshold`: the cleared quotient has `t`-degree below `E max{q,r}`.
  set dd := max Q.natDegree r with hdd
  have hdd1 : 1 ≤ dd := le_trans hr (le_max_right _ _)
  have hNdeg : ∀ β, (N.coeff β).natDegree ≤ dd - 1 := by
    intro β
    by_cases hz : N.coeff β = 0
    · rw [hz]; simp
    · have := hproper β
      rw [Polynomial.degree_eq_natDegree hz] at this
      have : (N.coeff β).natDegree < dd := by exact_mod_cast this
      omega
  have hBne : laurentWeight Q r N ≠ 0 := fun hb => hw0 (by rw [hb]; simp)
  have hμB : μ + B.natDegree ≤ (dd - 1) + E * dd := by
    have h1 : (clearedRestrict Q r E N).natDegree ≤ (dd - 1) + E * dd :=
      natDegree_clearedRestrict_le Q r E N hNdeg
    rwa [hA, Polynomial.natDegree_mul (pow_ne_zero _ Polynomial.X_ne_zero) hBne,
      Polynomial.natDegree_X_pow] at h1
  have hScoeff : ∀ n, E * dd ≤ n → (swapVars S).coeff n = 0 := by
    intro n hn
    by_cases hS0 : swapVars S = 0
    · rw [hS0, Polynomial.coeff_zero]
    have hDc := coeff_swapVars_denomPencil_max_ne_zero Q hr hQ0
    have hDne : swapVars (denomPencil Q r) ≠ 0 := fun hc => hDc (by rw [hc]; simp)
    have hDle : dd ≤ (swapVars (denomPencil Q r)).natDegree :=
      Polynomial.le_natDegree_of_ne_zero hDc
    have hprod : swapVars (denomPencil Q r) * swapVars S
        = (X : K[X][X]) ^ (r * E) * swapVars N
          - X ^ μ * B.map (Polynomial.C : K →+* K[X]) := by
      rw [hid]; ring
    have hrhs : ((X : K[X][X]) ^ (r * E) * swapVars N
        - X ^ μ * B.map (Polynomial.C : K →+* K[X])).natDegree ≤ (dd - 1) + E * dd := by
      refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
      · refine le_trans Polynomial.natDegree_mul_le ?_
        rw [Polynomial.natDegree_X_pow]
        have h2 : (swapVars N).natDegree ≤ dd - 1 := natDegree_swapVars_le hNdeg
        have h3 : r * E ≤ E * dd := by
          rw [mul_comm r E]
          exact Nat.mul_le_mul_left E (le_max_right Q.natDegree r)
        omega
      · refine le_trans Polynomial.natDegree_mul_le ?_
        rw [Polynomial.natDegree_X_pow]
        have h4 : (B.map (Polynomial.C : K →+* K[X])).natDegree ≤ B.natDegree :=
          Polynomial.natDegree_map_le
        omega
    have hSdeg : (swapVars S).natDegree < E * dd := by
      rw [← hprod, Polynomial.natDegree_mul hDne hS0] at hrhs
      omega
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  intro m hm hml
  have hμle : μ ≤ m + r * E := by
    have hcast : (μ : ℤ) ≤ (m : ℤ) + (r : ℤ) * (E : ℤ) := by rw [hμ]; omega
    have : ((μ : ℤ)) ≤ ((m + r * E : ℕ) : ℤ) := by push_cast; omega
    exact_mod_cast this
  have hthr : E * dd ≤ m + r * E := by
    have hsplit : (Q.natDegree - r) + r = dd := by rw [hdd]; omega
    calc E * dd = E * ((Q.natDegree - r) + r) := by rw [hsplit]
      _ = E * (Q.natDegree - r) + r * E := by ring
      _ ≤ m + r * E := by
          have : N.natDegree * (Q.natDegree - r) ≤ m := hm
          omega
  have hfun := congrFun heq (m + r * E)
  rw [hPa, hFa] at hfun
  simp only [if_pos (by omega : r * E ≤ m + r * E), if_pos hμle,
    Nat.add_sub_cancel] at hfun
  rw [hScoeff (m + r * E) hthr, zero_add] at hfun
  rw [hfun]
  congr 1
  omega

/-- **Paper `eq:reduction-coeff`**, in the eventual form the bulk count
consumes. -/
theorem reduction_coeff_eventually (Q : K[X]) {r : ℕ} (hr : 1 ≤ r) (hQ0 : Q.coeff 0 ≠ 0)
    {N : (K[X])[X]} (hN : N ≠ 0)
    (hproper : ∀ β, (N.coeff β).degree < ((max Q.natDegree r : ℕ) : WithBot ℕ))
    (P F : ℕ → K[X])
    (hP : ∀ m, denomConv (ftDenom Q r) P m = (swapVars N).coeff m)
    (hF : ∀ M, denomConv (ftDenom Q r) F M
      = Polynomial.C ((laurentWeight Q r N).coeff M)) :
    ∃ m0 : ℕ, ∀ m, m0 ≤ m → P m = F (((m : ℤ) - laurentShift Q r N).toNat) := by
  refine ⟨max (N.natDegree * (Q.natDegree - r)) (laurentShift Q r N).toNat, fun m hm => ?_⟩
  refine reduction_coeff Q hr hQ0 hN hproper P F hP hF m (le_trans (le_max_left _ _) hm) ?_
  have h1 : (laurentShift Q r N).toNat ≤ m := le_trans (le_max_right _ _) hm
  have h2 : ((laurentShift Q r N).toNat : ℤ) ≤ (m : ℤ) := by exact_mod_cast h1
  omega

/-! ### The eventual degree of the original numerator

Paper `eq:exact-eventual-degree-shift`: composing `eq:reduction-coeff` with the
eventual degree of the reduced sequence gives `deg P_m = ⌊(m-λ_N)/r⌋`.  The
`lem:eventual-degree` equality for the reduced sequence enters as a hypothesis,
so this composes with whatever supplies it. -/

/-- **Paper `eq:exact-eventual-degree-shift`.**  Given `lem:eventual-degree` for
the reduced sequence `F` — `deg F_M = ⌊M/r⌋` eventually — the coefficient
polynomials of `N/D` satisfy `deg P_m = ⌊(m-λ_N)/r⌋` eventually. -/
theorem exact_eventual_degree_shift (Q : K[X]) {r : ℕ} (hr : 1 ≤ r)
    (hQ0 : Q.coeff 0 ≠ 0) {N : (K[X])[X]} (hN : N ≠ 0)
    (hproper : ∀ β, (N.coeff β).degree < ((max Q.natDegree r : ℕ) : WithBot ℕ))
    (P F : ℕ → K[X])
    (hP : ∀ m, denomConv (ftDenom Q r) P m = (swapVars N).coeff m)
    (hF : ∀ M, denomConv (ftDenom Q r) F M
      = Polynomial.C ((laurentWeight Q r N).coeff M))
    (hdeg : ∃ M0 : ℕ, ∀ M, M0 ≤ M → (F M).natDegree = M / r) :
    ∃ m0 : ℕ, ∀ m, m0 ≤ m →
      (P m).natDegree = (((m : ℤ) - laurentShift Q r N).toNat) / r := by
  obtain ⟨m1, h1⟩ := reduction_coeff_eventually Q hr hQ0 hN hproper P F hP hF
  obtain ⟨M0, h2⟩ := hdeg
  refine ⟨max m1 (M0 + (laurentShift Q r N).toNat), fun m hm => ?_⟩
  have hm1 : m1 ≤ m := le_trans (le_max_left _ _) hm
  have hm2 : M0 + (laurentShift Q r N).toNat ≤ m := le_trans (le_max_right _ _) hm
  have hM0 : M0 ≤ (((m : ℤ) - laurentShift Q r N).toNat) := by
    have hcast : (M0 : ℤ) + ((laurentShift Q r N).toNat : ℤ) ≤ (m : ℤ) := by
      exact_mod_cast hm2
    omega
  rw [h1 m hm1, h2 _ hM0]

/-! ### The reduced tail as a fixed linear combination

Paper `eq:P-linear-combination`: writing `B_N = ∑_j b_j t^j`, the reduced
sequence is the fixed finite combination `∑_j b_j H_{M-j}` of the
denominator-only sequence `H` of `eq:H-generating`.  Convolution of sequences is
multiplication of power series, so this is associativity plus the fact that `H`
inverts the denominator. -/

/-- Paper `prop:initial-data` (supporting): the denominator convolution is
multiplication of the generating power series. -/
theorem mk_denomConv {A : Type*} [CommRing A] (f g : ℕ → A) :
    PowerSeries.mk (denomConv f g) = PowerSeries.mk f * PowerSeries.mk g := by
  ext m
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mul, denomConv,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp

/-- **Paper `eq:P-linear-combination`.**  With `H` the denominator-only sequence
of `eq:H-generating` — the solution of the recurrence with right-hand side
`δ_{M,0}` — the reduced sequence for the weight `B` is the fixed finite
combination `F_M = ∑_j b_j H_{M-j}`. -/
theorem reduced_tail_linear_combination (Q : K[X]) {r : ℕ} (hr : 1 ≤ r)
    (hQ0 : Q.coeff 0 ≠ 0) (B : K[X]) (H F : ℕ → K[X])
    (hH : ∀ M, denomConv (ftDenom Q r) H M = if M = 0 then 1 else 0)
    (hF : ∀ M, denomConv (ftDenom Q r) F M = Polynomial.C (B.coeff M)) :
    ∀ M, F M
      = ∑ j ∈ Finset.range (M + 1), Polynomial.C (B.coeff j) * H (M - j) := by
  set d := ftDenom Q r with hd
  set b : ℕ → K[X] := fun j => Polynomial.C (B.coeff j) with hb
  set G : ℕ → K[X] := denomConv b H with hG
  have hmkH : PowerSeries.mk (denomConv d H) = 1 := by
    ext m
    rw [PowerSeries.coeff_mk, hH, PowerSeries.coeff_one]
  have hGrec : ∀ M, denomConv d G M = b M := by
    intro M
    have hmk : PowerSeries.mk (denomConv d G) = PowerSeries.mk b := by
      rw [hG, mk_denomConv, mk_denomConv,
        show PowerSeries.mk d * (PowerSeries.mk b * PowerSeries.mk H)
          = PowerSeries.mk b * (PowerSeries.mk d * PowerSeries.mk H) by ring,
        ← mk_denomConv, hmkH, mul_one]
    have := congrArg (fun φ => PowerSeries.coeff M φ) hmk
    simpa using this
  have hunit : IsUnit (d 0) := by
    rw [hd, ftDenom_zero Q hr]
    exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hQ0)
  have heq : F = G := initial_data_unique hunit (fun M => by rw [hF M, hGrec M])
  intro M
  rw [heq, hG, denomConv]

/-- **Paper `eq:exact-eventual-degree-shift`, the half that needs no hypothesis.**
The `lem:eventual-degree` upper bound transported through `eq:reduction-coeff`:
`deg P_m ≤ ⌊(m-λ_N)/r⌋` for all large `m`.  This is the bound the bulk count of
`subsec:proof` consumes, so a general bivariate numerator no longer has to be
identified with the reduced sequence. -/
theorem eventual_natDegree_le_shift (Q : K[X]) {r : ℕ} (hr : 1 ≤ r)
    (hQ0 : Q.coeff 0 ≠ 0) {N : (K[X])[X]} (hN : N ≠ 0)
    (hproper : ∀ β, (N.coeff β).degree < ((max Q.natDegree r : ℕ) : WithBot ℕ))
    (P F : ℕ → K[X])
    (hP : ∀ m, denomConv (ftDenom Q r) P m = (swapVars N).coeff m)
    (hF : ∀ M, denomConv (ftDenom Q r) F M
      = Polynomial.C ((laurentWeight Q r N).coeff M)) :
    ∃ m0 : ℕ, ∀ m, m0 ≤ m →
      (P m).natDegree ≤ (((m : ℤ) - laurentShift Q r N).toNat) / r := by
  obtain ⟨m0, h0⟩ := reduction_coeff_eventually Q hr hQ0 hN hproper P F hP hF
  refine ⟨m0, fun m hm => ?_⟩
  rw [h0 m hm]
  exact eventual_natDegree_le Q hr hQ0 (fun M => (laurentWeight Q r N).coeff M) F hF _

end ForgacsTran
