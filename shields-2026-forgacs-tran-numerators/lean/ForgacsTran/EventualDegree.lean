/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.Reduction

/-!
# Eventual degree of the reduced coefficient polynomials

`coeff_top` is `eq:leading-z-coeff`: the `z^{⌊M/r⌋}` coefficient of `F_M` is
`(-1)^{⌊M/r⌋}` times the `t^{M mod r}` coefficient of `B/Q^{⌊M/r⌋+1}`, which the
paper reads off `eq:F-coefficient-expansion`.  Here it is derived from the
defining recurrence instead of from the geometric expansion
`eq:geometric-expansion`: at the top `z`-degree the bound annihilates every term
of `∑_i d_i F_{M-i} = C(b_M)` except the convolution by `Q` that `B/Q^{ℓ+1}`
itself satisfies, so the identity follows by induction on `M`.

`leadCoeffPoly` is the paper's polynomial in `ℓ`: `Q(0)^{ℓ+1}[t^s]B/Q^{ℓ+1}` has
degree at most `s` in `ℓ` with leading coefficient `B(0)Λ_Q^s/s!`, where
`Λ_Q = -Q'(0)/Q(0)`.  Writing `Q(0)/Q = 1 + W` with `W(0) = 0` turns the binomial
theorem into that polynomial, `descPochhammer` supplying `binom(ℓ+1, i)` as a
polynomial in `ℓ` of degree `i`.  With `B(0) ≠ 0` and `Λ_Q ≠ 0` it is nonzero,
hence has finitely many roots, and the top coefficient of `F_M` is nonzero once
`⌊M/r⌋` passes the largest root over the `r` residues `s = M mod r`.  The onset
is not uniform in `B` — `rem:degree-attainment` gives degree-one weights with
degree drops at arbitrarily late `M` — which is why `M₀` depends on `B`.

The hypothesis `Q'(0) ≠ 0` is what `eq:Q-hypotheses` supplies for a nonconstant
`Q`: `lambdaQ_eq_sum` identifies `Λ_Q` with `∑_j 1/x_j` for `Q = Q(0)∏_j(1-t/x_j)`,
`lambdaQ_pos` makes that sum positive when the zeros are, and
`lambdaQ_ne_zero_iff` converts positivity into `Q'(0) ≠ 0`.  The closing pair
`eventual_natDegree_eq_of_positive_zeros` and `eventual_ne_zero_of_positive_zeros`
state the two conclusions on the paper's own data, with `Q'(0) ≠ 0` discharged
rather than assumed.

## Implementation notes

Stated over an arbitrary field of characteristic zero, as `Reduction` is: the
paper works over `ℝ` and the analytic bridge instantiates at `ℂ`.  Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Canonical Laurent
reduction and eventual degree» (`sec:reduction`, `subsec:eventual-degree`,
`lem:eventual-degree`): for the reduced sequence `F_M(z) = [t^M] B(t)/(Q(t)+z t^r)`
of `eq:F-M-def`, the bound `deg F_M ≤ ⌊M/r⌋` of `Reduction.eventual_natDegree_le`
is attained for all large `M`, so `eventual_natDegree_eq` gives the equality
`deg F_M = ⌊M/r⌋`.  `eventual_ne_zero` records the nonvanishing `P_m ≠ 0` that
`thm:main` clause 2 presupposes; it comes out of the same coefficient.

## Tags

eventual degree, coefficient polynomial, Laurent reduction
-/

open Polynomial

namespace ForgacsTran

variable {𝕜 : Type*} [Field 𝕜]

/-! ### The tail series `B/Q^{ℓ+1}` -/

/-- Paper `eq:F-M-def` — the weight `B` read as a power series in `t`.  Only the
coefficient sequence enters, so `B` need not be a polynomial. -/
noncomputable def bSeries (b : ℕ → 𝕜) : PowerSeries 𝕜 := PowerSeries.mk b

/-- Paper `eq:leading-z-coeff` — the series `B(t)/Q(t)^{ℓ+1}` whose `t^s`
coefficient is the top `z`-coefficient of `F_M`, up to sign. -/
noncomputable def ftTail (Q : Polynomial 𝕜) (b : ℕ → 𝕜) (l : ℕ) : PowerSeries 𝕜 :=
  bSeries b * ((Q : PowerSeries 𝕜)⁻¹) ^ (l + 1)

/-- Paper `sec:reduction` (supporting) — `Q(0) ≠ 0` says `Q` is invertible in
`𝕜⟦t⟧`. -/
theorem constantCoeff_coe_ne_zero {Q : Polynomial 𝕜} (hQ0 : Q.coeff 0 ≠ 0) :
    PowerSeries.constantCoeff (Q : PowerSeries 𝕜) ≠ 0 := by
  simpa [← PowerSeries.coeff_zero_eq_constantCoeff_apply] using hQ0

/-- Paper `sec:reduction` (supporting) — the convolution by `Q` in `t`. -/
theorem coeff_coe_mul (Q : Polynomial 𝕜) (φ : PowerSeries 𝕜) (m : ℕ) :
    PowerSeries.coeff m ((Q : PowerSeries 𝕜) * φ)
      = ∑ i ∈ Finset.range (m + 1), Q.coeff i * PowerSeries.coeff (m - i) φ := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => PowerSeries.coeff i (Q : PowerSeries 𝕜) * PowerSeries.coeff j φ)]
  simp [Polynomial.coeff_coe]

/-- Paper `eq:leading-z-coeff` (supporting) — multiplying `B/Q^{ℓ+2}` by `Q`
drops one power. -/
theorem coe_mul_ftTail_succ (Q : Polynomial 𝕜) (hQ0 : Q.coeff 0 ≠ 0) (b : ℕ → 𝕜) (l : ℕ) :
    (Q : PowerSeries 𝕜) * ftTail Q b (l + 1) = ftTail Q b l := by
  have h : (Q : PowerSeries 𝕜) * ((Q : PowerSeries 𝕜)⁻¹) = 1 :=
    PowerSeries.mul_inv_cancel _ (constantCoeff_coe_ne_zero hQ0)
  unfold ftTail
  rw [show l + 1 + 1 = (l + 1) + 1 from rfl, pow_succ,
    show (Q : PowerSeries 𝕜) * (bSeries b * (((Q : PowerSeries 𝕜)⁻¹) ^ (l + 1)
        * ((Q : PowerSeries 𝕜)⁻¹)))
      = (bSeries b * ((Q : PowerSeries 𝕜)⁻¹) ^ (l + 1))
        * ((Q : PowerSeries 𝕜) * ((Q : PowerSeries 𝕜)⁻¹)) from by ring, h, mul_one]

/-- Paper `eq:leading-z-coeff` (supporting) — `Q · (B/Q) = B`. -/
theorem coe_mul_ftTail_zero (Q : Polynomial 𝕜) (hQ0 : Q.coeff 0 ≠ 0) (b : ℕ → 𝕜) :
    (Q : PowerSeries 𝕜) * ftTail Q b 0 = bSeries b := by
  have h : (Q : PowerSeries 𝕜) * ((Q : PowerSeries 𝕜)⁻¹) = 1 :=
    PowerSeries.mul_inv_cancel _ (constantCoeff_coe_ne_zero hQ0)
  unfold ftTail
  rw [pow_one, show (Q : PowerSeries 𝕜) * (bSeries b * ((Q : PowerSeries 𝕜)⁻¹))
      = bSeries b * ((Q : PowerSeries 𝕜) * ((Q : PowerSeries 𝕜)⁻¹)) from by ring, h, mul_one]

/-! ### The top `z`-coefficient (`eq:leading-z-coeff`) -/

/-- Paper `sec:reduction` (supporting) — the denominator recurrence read one
`z`-coefficient at a time. -/
theorem coeff_denomConv (Q : Polynomial 𝕜) (r : ℕ) (b : ℕ → 𝕜) (F : ℕ → Polynomial 𝕜)
    (hrec : ∀ M, denomConv (ftDenom Q r) F M = C (b M)) (M l : ℕ) :
    (∑ i ∈ Finset.range (M + 1), (ftDenom Q r i * F (M - i)).coeff l) = (C (b M)).coeff l := by
  calc ∑ i ∈ Finset.range (M + 1), (ftDenom Q r i * F (M - i)).coeff l
      = (∑ i ∈ Finset.range (M + 1), ftDenom Q r i * F (M - i)).coeff l :=
        (Polynomial.finsetSum_coeff _ _ _).symm
    _ = (C (b M)).coeff l := by
        rw [show (∑ i ∈ Finset.range (M + 1), ftDenom Q r i * F (M - i))
          = denomConv (ftDenom Q r) F M from rfl, hrec M]

/-- Paper `sec:reduction` (supporting) — away from the resonant index `i = r` the
denominator coefficient is the constant `Q_i`. -/
theorem ftDenom_mul_coeff_of_ne (Q : Polynomial 𝕜) {r i : ℕ} (hi : i ≠ r)
    (p : Polynomial 𝕜) (l : ℕ) : (ftDenom Q r i * p).coeff l = Q.coeff i * p.coeff l := by
  rw [ftDenom, if_neg hi, add_zero, Polynomial.coeff_C_mul]

/-- **Paper `eq:leading-z-coeff`.**  If a `z`-polynomial sequence `F` satisfies the
`sec:reduction` denominator recurrence `∑_i d_i F_{M-i} = C(b_M)` with
`d_i = C(Q.coeff i) + [i=r]·X`, then the coefficient of `z^{⌊M/r⌋}` in `F_M` — the
top coefficient allowed by `eventual_natDegree_le` — is `(-1)^{⌊M/r⌋}` times the
`t^{M mod r}` coefficient of `B/Q^{⌊M/r⌋+1}`.  This is the entry of
`eq:F-coefficient-expansion` at `j = ⌊M/r⌋`, obtained from the recurrence rather
than from the geometric expansion `eq:geometric-expansion`: at the top
`z`-degree, the degree bound annihilates every term of the recurrence except the
convolution by `Q` that `B/Q^{ℓ+1}` itself satisfies. -/
theorem coeff_top (Q : Polynomial 𝕜) {r : ℕ} (hr : 1 ≤ r) (hQ0 : Q.coeff 0 ≠ 0)
    (b : ℕ → 𝕜) (F : ℕ → Polynomial 𝕜)
    (hrec : ∀ M, denomConv (ftDenom Q r) F M = C (b M)) (M : ℕ) :
    (F M).coeff (M / r)
      = (-1) ^ (M / r) * PowerSeries.coeff (M % r) (ftTail Q b (M / r)) := by
  have hrpos : 0 < r := hr
  have hdeg : ∀ m, (F m).natDegree ≤ m / r := eventual_natDegree_le Q hr hQ0 b F hrec
  induction M using Nat.strong_induction_on with
  | _ M ih =>
  rcases lt_or_ge M r with hMr | hMr
  · -- `M < r`: the top degree is `0` and the recurrence is the convolution `Q · (B/Q) = B`
    have hl : M / r = 0 := Nat.div_eq_of_lt hMr
    have hs : M % r = M := Nat.mod_eq_of_lt hMr
    rw [hl, hs, pow_zero, one_mul]
    refine mul_left_cancel₀ hQ0 ?_
    -- both sides satisfy the same convolution identity
    have hF : (∑ i ∈ Finset.range M, Q.coeff (i + 1) * (F (M - (i + 1))).coeff 0)
        + Q.coeff 0 * (F M).coeff 0 = b M := by
      have h := coeff_denomConv Q r b F hrec M 0
      rw [Polynomial.coeff_C_zero] at h
      rw [← h, Finset.sum_range_succ']
      refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun i hi => ?_)
        (ftDenom_mul_coeff_of_ne Q (by omega) _ _).symm
      exact (ftDenom_mul_coeff_of_ne Q (by have := Finset.mem_range.mp hi; omega) _ _).symm
    have hT : (∑ i ∈ Finset.range M, Q.coeff (i + 1)
          * PowerSeries.coeff (M - (i + 1)) (ftTail Q b 0))
        + Q.coeff 0 * PowerSeries.coeff M (ftTail Q b 0) = b M := by
      have h := coeff_coe_mul Q (ftTail Q b 0) M
      rw [coe_mul_ftTail_zero Q hQ0 b, bSeries, PowerSeries.coeff_mk,
        Finset.sum_range_succ'
          (fun i => Q.coeff i * PowerSeries.coeff (M - i) (ftTail Q b 0)) M] at h
      simpa using h.symm
    have htail : (∑ i ∈ Finset.range M, Q.coeff (i + 1) * (F (M - (i + 1))).coeff 0)
        = ∑ i ∈ Finset.range M, Q.coeff (i + 1)
            * PowerSeries.coeff (M - (i + 1)) (ftTail Q b 0) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have him : i < M := Finset.mem_range.mp hi
      have hlt : M - (i + 1) < M := by omega
      have h0 : (M - (i + 1)) / r = 0 := Nat.div_eq_of_lt (by omega)
      have h1 : (M - (i + 1)) % r = M - (i + 1) := Nat.mod_eq_of_lt (by omega)
      have := ih (M - (i + 1)) hlt
      rw [h0, h1, pow_zero, one_mul] at this
      rw [this]
    rw [htail] at hF
    exact add_left_cancel (hF.trans hT.symm)
  · -- `r ≤ M`: peel the resonant term and use `Q · (B/Q^{ℓ+1}) = B/Q^ℓ`
    obtain ⟨k, hk⟩ : ∃ k, M / r = k + 1 := by
      refine ⟨M / r - 1, ?_⟩
      have : 1 ≤ M / r := (Nat.one_le_div_iff hrpos).mpr hMr
      omega
    set s := M % r with hsdef
    have hs : s < r := Nat.mod_lt _ hrpos
    have hMs : r * (k + 1) + s = M := by rw [← hk, hsdef]; exact Nat.div_add_mod M r
    have hrk : r * (k + 1) = r * k + r := by ring
    have hMk : M - r = r * k + s := by omega
    have hMrk : (M - r) / r = k := by
      rw [hMk, Nat.add_comm, Nat.add_mul_div_left _ _ hrpos, Nat.div_eq_of_lt hs, Nat.zero_add]
    have hMrs : (M - r) % r = s := by
      rw [hMk, Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hs]
    rw [hk]
    -- at the top `z`-degree the recurrence keeps only `0 ≤ i ≤ s` and the resonant `i = r`
    have hsplit : (∑ i ∈ Finset.range (M + 1), (ftDenom Q r i * F (M - i)).coeff (k + 1))
        = (∑ i ∈ Finset.range (s + 1), Q.coeff i * (F (M - i)).coeff (k + 1))
          + (F (M - r)).coeff k := by
      have hnot : r ∉ Finset.range (s + 1) := by simp only [Finset.mem_range]; omega
      have hsub : insert r (Finset.range (s + 1)) ⊆ Finset.range (M + 1) := by
        intro i hi
        simp only [Finset.mem_insert, Finset.mem_range] at hi ⊢
        omega
      have hvanish : ∀ i ∈ Finset.range (M + 1), i ∉ insert r (Finset.range (s + 1)) →
          (ftDenom Q r i * F (M - i)).coeff (k + 1) = 0 := by
        intro i hi hni
        simp only [Finset.mem_insert, Finset.mem_range, not_or] at hni
        have hir : i ≠ r := hni.1
        have his : s < i := by have := hni.2; omega
        have hlt : (M - i) / r < k + 1 := by
          refine (Nat.div_lt_iff_lt_mul hrpos).mpr ?_
          have hcomm : (k + 1) * r = r * (k + 1) := by ring
          omega
        rw [ftDenom_mul_coeff_of_ne Q hir,
          Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hdeg (M - i)) hlt), mul_zero]
      have hres : (ftDenom Q r r * F (M - r)).coeff (k + 1) = (F (M - r)).coeff k := by
        have hz : (F (M - r)).coeff (k + 1) = 0 :=
          Polynomial.coeff_eq_zero_of_natDegree_lt
            (lt_of_le_of_lt (hdeg (M - r)) (by rw [hMrk]; omega))
        rw [ftDenom, if_pos rfl, add_mul, Polynomial.coeff_add, Polynomial.coeff_C_mul, hz,
          mul_zero, zero_add, Polynomial.coeff_X_mul]
      rw [← Finset.sum_subset hsub hvanish, Finset.sum_insert hnot, hres, add_comm]
      refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun i hi => ?_) rfl
      exact ftDenom_mul_coeff_of_ne Q (by have := Finset.mem_range.mp hi; omega) _ _
    have hCz : (C (b M)).coeff (k + 1) = 0 := by
      rw [Polynomial.coeff_C, if_neg (Nat.succ_ne_zero k)]
    have hmain : (∑ i ∈ Finset.range (s + 1), Q.coeff i * (F (M - i)).coeff (k + 1))
        + (F (M - r)).coeff k = 0 := by
      rw [← hsplit, coeff_denomConv Q r b F hrec M (k + 1)]
      exact hCz
    rw [Finset.sum_range_succ' (fun i => Q.coeff i * (F (M - i)).coeff (k + 1)) s] at hmain
    simp only [Nat.sub_zero] at hmain
    have hIH1 : ∀ i ∈ Finset.range s, Q.coeff (i + 1) * (F (M - (i + 1))).coeff (k + 1)
        = (-1 : 𝕜) ^ (k + 1)
          * (Q.coeff (i + 1) * PowerSeries.coeff (s - (i + 1)) (ftTail Q b (k + 1))) := by
      intro i hi
      have his : i < s := Finset.mem_range.mp hi
      have he : M - (i + 1) = r * (k + 1) + (s - (i + 1)) := by omega
      have hlt : M - (i + 1) < M := by omega
      have hd : (M - (i + 1)) / r = k + 1 := by
        rw [he, Nat.add_comm, Nat.add_mul_div_left _ _ hrpos, Nat.div_eq_of_lt (by omega),
          Nat.zero_add]
      have hm : (M - (i + 1)) % r = s - (i + 1) := by
        rw [he, Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
      have hih := ih (M - (i + 1)) hlt
      rw [hd, hm] at hih
      rw [hih]; ring
    have hIH2 : (F (M - r)).coeff k
        = (-1 : 𝕜) ^ k * PowerSeries.coeff s (ftTail Q b k) := by
      have hih := ih (M - r) (by omega)
      rwa [hMrk, hMrs] at hih
    have hQT : PowerSeries.coeff s (ftTail Q b k)
        = (∑ i ∈ Finset.range s, Q.coeff (i + 1)
            * PowerSeries.coeff (s - (i + 1)) (ftTail Q b (k + 1)))
          + Q.coeff 0 * PowerSeries.coeff s (ftTail Q b (k + 1)) := by
      have h := coeff_coe_mul Q (ftTail Q b (k + 1)) s
      rw [coe_mul_ftTail_succ Q hQ0 b k] at h
      rw [h, Finset.sum_range_succ'
        (fun i => Q.coeff i * PowerSeries.coeff (s - i) (ftTail Q b (k + 1))) s]
      simp
    rw [Finset.sum_congr rfl hIH1, ← Finset.mul_sum, hIH2, hQT] at hmain
    have hsign : (-1 : 𝕜) ^ (k + 1) = -(-1 : 𝕜) ^ k := by rw [pow_succ]; ring
    rw [hsign] at hmain ⊢
    refine mul_left_cancel₀ hQ0 ?_
    linear_combination hmain


/-! ### The leading coefficient as a polynomial in `ℓ` -/

/-- Paper `eq:leading-z-coeff` — the normalized denominator `Q(0)/Q(t)`, a power
series with constant term `1`.  Its powers are what the paper expands as
`Q(0)^{ℓ+1}Q^{-(ℓ+1)} = ∏_j(1-t/x_j)^{-(ℓ+1)}`. -/
noncomputable def ftNorm (Q : Polynomial 𝕜) : PowerSeries 𝕜 :=
  PowerSeries.C (Q.coeff 0) * ((Q : PowerSeries 𝕜)⁻¹)

/-- Paper `eq:leading-z-coeff` — `Λ_Q = -Q'(0)/Q(0)`, which under
`eq:Q-hypotheses` is `∑_j 1/x_j > 0`. -/
noncomputable def lambdaQ (Q : Polynomial 𝕜) : 𝕜 := -Q.coeff 1 / Q.coeff 0

theorem constantCoeff_ftNorm {Q : Polynomial 𝕜} (hQ0 : Q.coeff 0 ≠ 0) :
    PowerSeries.constantCoeff (ftNorm Q) = 1 := by
  rw [ftNorm, map_mul, PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_inv,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
    mul_inv_cancel₀ hQ0]

/-- Paper `eq:leading-z-coeff` — the `t`-coefficient of `Q(0)/Q(t)` is `Λ_Q`. -/
theorem coeff_one_ftNorm {Q : Polynomial 𝕜} (hQ0 : Q.coeff 0 ≠ 0) :
    PowerSeries.coeff 1 (ftNorm Q) = lambdaQ Q := by
  have hinv : (Q : PowerSeries 𝕜) * ((Q : PowerSeries 𝕜)⁻¹) = 1 :=
    PowerSeries.mul_inv_cancel _ (constantCoeff_coe_ne_zero hQ0)
  have h0 : PowerSeries.coeff 0 ((Q : PowerSeries 𝕜)⁻¹) = (Q.coeff 0)⁻¹ := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_inv,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe]
  have h := coeff_coe_mul Q ((Q : PowerSeries 𝕜)⁻¹) 1
  rw [hinv, PowerSeries.coeff_one, if_neg one_ne_zero, Finset.sum_range_succ,
    Finset.sum_range_one, h0] at h
  have h1 : PowerSeries.coeff 1 ((Q : PowerSeries 𝕜)⁻¹) = -Q.coeff 1 / (Q.coeff 0 * Q.coeff 0) := by
    field_simp at h ⊢
    linear_combination -h
  rw [ftNorm, PowerSeries.coeff_C_mul, h1, lambdaQ]
  field_simp

theorem X_dvd_ftNorm_sub_one {Q : Polynomial 𝕜} (hQ0 : Q.coeff 0 ≠ 0) :
    (PowerSeries.X : PowerSeries 𝕜) ∣ (ftNorm Q - 1) := by
  rw [PowerSeries.X_dvd_iff, map_sub, constantCoeff_ftNorm hQ0, map_one, sub_self]

/-- Paper `eq:leading-z-coeff` (supporting) — `(Q(0)/Q - 1)^i` has a zero of order
`i` at the origin, so it cannot reach the coefficient `t^s` when `i > s`. -/
theorem coeff_bSeries_mul_sub_pow_of_lt {Q : Polynomial 𝕜} (hQ0 : Q.coeff 0 ≠ 0)
    (b : ℕ → 𝕜) {s i : ℕ} (h : s < i) :
    PowerSeries.coeff s (bSeries b * (ftNorm Q - 1) ^ i) = 0 := by
  obtain ⟨V, hV⟩ := X_dvd_ftNorm_sub_one hQ0 (Q := Q)
  rw [hV, mul_pow, show bSeries b * ((PowerSeries.X : PowerSeries 𝕜) ^ i * V ^ i)
      = (PowerSeries.X : PowerSeries 𝕜) ^ i * (bSeries b * V ^ i) from by ring,
    PowerSeries.coeff_X_pow_mul', if_neg (by omega)]

/-- Paper `eq:leading-z-coeff` (supporting) — at `i = s` the surviving coefficient
is `B(0)Λ_Q^s`. -/
theorem coeff_bSeries_mul_sub_pow_self {Q : Polynomial 𝕜} (hQ0 : Q.coeff 0 ≠ 0)
    (b : ℕ → 𝕜) (s : ℕ) :
    PowerSeries.coeff s (bSeries b * (ftNorm Q - 1) ^ s) = b 0 * (lambdaQ Q) ^ s := by
  obtain ⟨V, hV⟩ := X_dvd_ftNorm_sub_one hQ0 (Q := Q)
  have hV1 : PowerSeries.constantCoeff V = lambdaQ Q := by
    have hc : PowerSeries.coeff 1 (ftNorm Q - 1) = PowerSeries.coeff 1 (ftNorm Q) := by
      simp [PowerSeries.coeff_one]
    rw [← coeff_one_ftNorm hQ0, ← hc, hV]
    simp [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  rw [hV, mul_pow, show bSeries b * ((PowerSeries.X : PowerSeries 𝕜) ^ s * V ^ s)
      = (PowerSeries.X : PowerSeries 𝕜) ^ s * (bSeries b * V ^ s) from by ring,
    PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, map_pow, hV1, bSeries]
  simp

/-- **Paper `eq:leading-z-coeff`.**  The binomial expansion of
`(Q(0)/Q)^K = (1 + W)^K` reduced to the `t^s` coefficient: only `i ≤ s` survives,
because `W` vanishes at the origin. -/
theorem coeff_bSeries_mul_ftNorm_pow {Q : Polynomial 𝕜} (hQ0 : Q.coeff 0 ≠ 0)
    (b : ℕ → 𝕜) (s K : ℕ) :
    PowerSeries.coeff s (bSeries b * (ftNorm Q) ^ K)
      = ∑ i ∈ Finset.range (s + 1),
          (K.choose i : 𝕜) * PowerSeries.coeff s (bSeries b * (ftNorm Q - 1) ^ i) := by
  set g : ℕ → 𝕜 := fun i =>
    (K.choose i : 𝕜) * PowerSeries.coeff s (bSeries b * (ftNorm Q - 1) ^ i) with hg
  have hexp : PowerSeries.coeff s (bSeries b * (ftNorm Q) ^ K)
      = ∑ i ∈ Finset.range (K + 1), g i := by
    have hsplit : (ftNorm Q : PowerSeries 𝕜) = (ftNorm Q - 1) + 1 := by ring
    rw [hsplit, add_pow, Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hg]
    simp only [one_pow, mul_one]
    rw [show bSeries b * ((ftNorm Q - 1) ^ i * (K.choose i : PowerSeries 𝕜))
        = (bSeries b * (ftNorm Q - 1) ^ i) * (K.choose i : PowerSeries 𝕜) from by ring]
    rw [show ((K.choose i : ℕ) : PowerSeries 𝕜) = PowerSeries.C ((K.choose i : ℕ) : 𝕜) by
      simp, PowerSeries.coeff_mul_C]
    ring
  have hzeroK : ∀ i ∈ Finset.range (max K s + 1), i ∉ Finset.range (K + 1) → g i = 0 := by
    intro i _ hi
    have : K < i := by simpa [Finset.mem_range] using hi
    simp [hg, Nat.choose_eq_zero_of_lt this]
  have hzeros : ∀ i ∈ Finset.range (max K s + 1), i ∉ Finset.range (s + 1) → g i = 0 := by
    intro i _ hi
    have : s < i := by simpa [Finset.mem_range] using hi
    simp [hg, coeff_bSeries_mul_sub_pow_of_lt hQ0 b this]
  have hsubK : Finset.range (K + 1) ⊆ Finset.range (max K s + 1) := by
    intro i hi; simp only [Finset.mem_range] at hi ⊢; omega
  have hsubs : Finset.range (s + 1) ⊆ Finset.range (max K s + 1) := by
    intro i hi; simp only [Finset.mem_range] at hi ⊢; omega
  rw [hexp, Finset.sum_subset hsubK hzeroK, ← Finset.sum_subset hsubs hzeros]

/-- **Paper `eq:leading-z-coeff`.**  `Q(0)^{ℓ+1}[t^s]B/Q^{ℓ+1}`, as an explicit
polynomial in `ℓ`: the binomial coefficients `binom(ℓ+1, i)` of the expansion are
polynomials in `ℓ+1` of degree `i`, supplied by `descPochhammer`. -/
noncomputable def leadCoeffPoly (Q : Polynomial 𝕜) (b : ℕ → 𝕜) (s : ℕ) : Polynomial 𝕜 :=
  ∑ i ∈ Finset.range (s + 1),
    C (PowerSeries.coeff s (bSeries b * (ftNorm Q - 1) ^ i) / (Nat.factorial i : 𝕜))
      * descPochhammer 𝕜 i

variable [CharZero 𝕜]

/-- **Paper `eq:leading-z-coeff`.**  `leadCoeffPoly` evaluates to the coefficient
it was built from. -/
theorem leadCoeffPoly_eval {Q : Polynomial 𝕜} (hQ0 : Q.coeff 0 ≠ 0) (b : ℕ → 𝕜) (s K : ℕ) :
    (leadCoeffPoly Q b s).eval (K : 𝕜)
      = PowerSeries.coeff s (bSeries b * (ftNorm Q) ^ K) := by
  rw [coeff_bSeries_mul_ftNorm_pow hQ0 b s K, leadCoeffPoly, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hfac : (Nat.factorial i : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr i.factorial_ne_zero
  rw [Polynomial.eval_mul, Polynomial.eval_C, Nat.cast_choose_eq_descPochhammer_div]
  field_simp

omit [CharZero 𝕜] in
/-- **Paper `eq:leading-z-coeff`.**  The polynomial in `ℓ` has degree at most `s`. -/
theorem leadCoeffPoly_natDegree_le (Q : Polynomial 𝕜) (b : ℕ → 𝕜) (s : ℕ) :
    (leadCoeffPoly Q b s).natDegree ≤ s := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
  have hi' : i ≤ s := by have := Finset.mem_range.mp hi; omega
  exact le_trans (le_trans (Polynomial.natDegree_C_mul_le _ _)
    (le_of_eq (descPochhammer_natDegree (R := 𝕜) i))) hi'

omit [CharZero 𝕜] in
/-- **Paper `eq:leading-z-coeff`.**  Its degree-`s` coefficient is `B(0)Λ_Q^s/s!`,
the paper's leading coefficient. -/
theorem leadCoeffPoly_coeff {Q : Polynomial 𝕜} (hQ0 : Q.coeff 0 ≠ 0) (b : ℕ → 𝕜) (s : ℕ) :
    (leadCoeffPoly Q b s).coeff s = b 0 * (lambdaQ Q) ^ s / (Nat.factorial s : 𝕜) := by
  have hmc : (descPochhammer 𝕜 s).coeff s = 1 := by
    have h := (monic_descPochhammer (R := 𝕜) s).coeff_natDegree
    rwa [descPochhammer_natDegree (R := 𝕜) s] at h
  rw [leadCoeffPoly, Polynomial.finsetSum_coeff, Finset.sum_eq_single s]
  · rw [Polynomial.coeff_C_mul, hmc, mul_one, coeff_bSeries_mul_sub_pow_self hQ0 b s]
  · intro i hi his
    have hlt : i < s := by have := Finset.mem_range.mp hi; omega
    exact Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt (le_trans (Polynomial.natDegree_C_mul_le _ _)
        (le_of_eq (descPochhammer_natDegree (R := 𝕜) i))) hlt)
  · intro hs
    exact absurd (Finset.self_mem_range_succ s) hs


/-! ### Attainment of the degree bound (`lem:eventual-degree`) -/

/-- Paper `lem:eventual-degree` (supporting) — a nonzero polynomial vanishes at
only finitely many points, so it is nonzero at every large natural argument. -/
theorem exists_nat_forall_eval_ne_zero {p : Polynomial 𝕜} (hp : p ≠ 0) :
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → p.eval (K : 𝕜) ≠ 0 := by
  have hfin : ((Nat.cast : ℕ → 𝕜) ⁻¹' {x : 𝕜 | p.IsRoot x}).Finite :=
    (Polynomial.finite_setOfPred_isRoot hp).preimage Nat.cast_injective.injOn
  obtain ⟨K₀, hK₀⟩ := hfin.bddAbove
  refine ⟨K₀ + 1, fun K hK hroot => ?_⟩
  have : K ≤ K₀ := hK₀ (show K ∈ _ from hroot)
  omega

omit [CharZero 𝕜] in
/-- Paper `eq:leading-z-coeff` — `Λ_Q ≠ 0` exactly when `Q'(0) ≠ 0`.  Under
`eq:Q-hypotheses` with `Q` nonconstant, `Λ_Q = ∑_j 1/x_j > 0`, so the hypothesis
`Q'(0) ≠ 0` of the degree theorem is discharged there; `lambdaQ_eq_sum` below
identifies the sum. -/
theorem lambdaQ_ne_zero_iff {Q : Polynomial 𝕜} (hQ0 : Q.coeff 0 ≠ 0) :
    lambdaQ Q ≠ 0 ↔ Q.coeff 1 ≠ 0 := by
  rw [lambdaQ, div_ne_zero_iff, neg_ne_zero]
  exact and_iff_left hQ0

omit [CharZero 𝕜] in
/-- Paper `eq:leading-z-coeff` — `Q'(0) ≠ 0` gives `Λ_Q ≠ 0`. -/
theorem lambdaQ_ne_zero {Q : Polynomial 𝕜} (hQ0 : Q.coeff 0 ≠ 0) (hQ1 : Q.coeff 1 ≠ 0) :
    lambdaQ Q ≠ 0 := (lambdaQ_ne_zero_iff hQ0).mpr hQ1

/-- **Paper `eq:leading-z-coeff`.**  The polynomial in `ℓ` is nonzero: its degree-`s`
coefficient is `B(0)Λ_Q^s/s!`. -/
theorem leadCoeffPoly_ne_zero {Q : Polynomial 𝕜} (hQ0 : Q.coeff 0 ≠ 0) (hQ1 : Q.coeff 1 ≠ 0)
    {b : ℕ → 𝕜} (hb0 : b 0 ≠ 0) (s : ℕ) : leadCoeffPoly Q b s ≠ 0 := by
  intro hzero
  have h := leadCoeffPoly_coeff hQ0 b s
  rw [hzero, Polynomial.coeff_zero] at h
  have hfac : (Nat.factorial s : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr s.factorial_ne_zero
  exact div_ne_zero (mul_ne_zero hb0 (pow_ne_zero s (lambdaQ_ne_zero hQ0 hQ1))) hfac h.symm

/-- **Paper `eq:leading-z-coeff`.**  `Q(0)^{ℓ+1}[t^s]B/Q^{ℓ+1}` is the value of the
polynomial `leadCoeffPoly` at `ℓ+1`. -/
theorem coeff_ftTail_eq_eval {Q : Polynomial 𝕜} (hQ0 : Q.coeff 0 ≠ 0) (b : ℕ → 𝕜) (s l : ℕ) :
    (Q.coeff 0) ^ (l + 1) * PowerSeries.coeff s (ftTail Q b l)
      = (leadCoeffPoly Q b s).eval (((l + 1 : ℕ) : 𝕜)) := by
  have h : bSeries b * (ftNorm Q) ^ (l + 1)
      = PowerSeries.C ((Q.coeff 0) ^ (l + 1)) * ftTail Q b l := by
    rw [ftNorm, ftTail, mul_pow, ← map_pow]; ring
  rw [leadCoeffPoly_eval hQ0 b s (l + 1), h, PowerSeries.coeff_C_mul]

/-- **`lem:eventual-degree`, attainment.**  For a `z`-polynomial sequence `F`
satisfying the `sec:reduction` denominator recurrence with `Q(0) ≠ 0`, `Q'(0) ≠ 0`
and `B(0) ≠ 0`, the top coefficient allowed by `eventual_natDegree_le` is nonzero
for all large `M`.

For each of the `r` residues `s = M mod r`, `eq:leading-z-coeff` makes that
coefficient equal to `(-1)^{⌊M/r⌋}Q(0)^{-(⌊M/r⌋+1)}` times the value at `⌊M/r⌋+1`
of a polynomial in `ℓ` of degree at most `s` whose degree-`s` coefficient is
`B(0)Λ_Q^s/s!`.  That polynomial is nonzero, so it has finitely many roots, and
`M₀` is `r` times one past the largest of them over the `r` residues. -/
theorem exists_forall_coeff_top_ne_zero (Q : Polynomial 𝕜) {r : ℕ} (hr : 1 ≤ r)
    (hQ0 : Q.coeff 0 ≠ 0) (hQ1 : Q.coeff 1 ≠ 0) (b : ℕ → 𝕜) (hb0 : b 0 ≠ 0)
    (F : ℕ → Polynomial 𝕜) (hrec : ∀ M, denomConv (ftDenom Q r) F M = C (b M)) :
    ∃ M₀ : ℕ, ∀ M, M₀ ≤ M → (F M).coeff (M / r) ≠ 0 := by
  have hrpos : 0 < r := hr
  choose K0 hK0 using fun s : ℕ =>
    exists_nat_forall_eval_ne_zero (leadCoeffPoly_ne_zero hQ0 hQ1 hb0 s)
  refine ⟨r * ((Finset.range r).sup K0 + 1), fun M hM => ?_⟩
  have hlow : (Finset.range r).sup K0 + 1 ≤ M / r :=
    (Nat.le_div_iff_mul_le hrpos).mpr (by rw [Nat.mul_comm] at hM; exact hM)
  have hsr : M % r < r := Nat.mod_lt _ hrpos
  have hKle : K0 (M % r) ≤ M / r + 1 :=
    le_trans (Finset.le_sup (f := K0) (Finset.mem_range.mpr hsr)) (by omega)
  have hval : (leadCoeffPoly Q b (M % r)).eval (((M / r + 1 : ℕ) : 𝕜)) ≠ 0 :=
    hK0 (M % r) (M / r + 1) hKle
  have htail : PowerSeries.coeff (M % r) (ftTail Q b (M / r)) ≠ 0 := by
    intro hz
    rw [← coeff_ftTail_eq_eval hQ0 b (M % r) (M / r), hz, mul_zero] at hval
    exact hval rfl
  rw [coeff_top Q hr hQ0 b F hrec M]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) htail

/-- **`lem:eventual-degree`.**  For all sufficiently large `M`,
`deg F_M = ⌊M/r⌋`: the bound of `eventual_natDegree_le` is attained.

The onset is not uniform in `B` — `rem:degree-attainment` exhibits degree-one
weights with degree drops at arbitrarily late `M` — so the conclusion is
genuinely eventual, and `M₀` depends on `B` through the roots of
`leadCoeffPoly`. -/
theorem eventual_natDegree_eq (Q : Polynomial 𝕜) {r : ℕ} (hr : 1 ≤ r)
    (hQ0 : Q.coeff 0 ≠ 0) (hQ1 : Q.coeff 1 ≠ 0) (b : ℕ → 𝕜) (hb0 : b 0 ≠ 0)
    (F : ℕ → Polynomial 𝕜) (hrec : ∀ M, denomConv (ftDenom Q r) F M = C (b M)) :
    ∃ M₀ : ℕ, ∀ M, M₀ ≤ M → (F M).natDegree = M / r := by
  obtain ⟨M₀, hM₀⟩ := exists_forall_coeff_top_ne_zero Q hr hQ0 hQ1 b hb0 F hrec
  exact ⟨M₀, fun M hM => le_antisymm (eventual_natDegree_le Q hr hQ0 b F hrec M)
    (Polynomial.le_natDegree_of_ne_zero (hM₀ M hM))⟩

/-- **`thm:main` clause 2, nonvanishing.**  Every sufficiently large coefficient
polynomial is nonzero.  This is the statement `P_m ≠ 0` that the interval clause
of `thm:main` presupposes, and it comes out of the same top coefficient. -/
theorem eventual_ne_zero (Q : Polynomial 𝕜) {r : ℕ} (hr : 1 ≤ r)
    (hQ0 : Q.coeff 0 ≠ 0) (hQ1 : Q.coeff 1 ≠ 0) (b : ℕ → 𝕜) (hb0 : b 0 ≠ 0)
    (F : ℕ → Polynomial 𝕜) (hrec : ∀ M, denomConv (ftDenom Q r) F M = C (b M)) :
    ∃ M₀ : ℕ, ∀ M, M₀ ≤ M → F M ≠ 0 := by
  obtain ⟨M₀, hM₀⟩ := exists_forall_coeff_top_ne_zero Q hr hQ0 hQ1 b hb0 F hrec
  refine ⟨M₀, fun M hM hzero => hM₀ M hM ?_⟩
  rw [hzero, Polynomial.coeff_zero]

/-! ### `Λ_Q` under the paper's hypotheses (`eq:Q-hypotheses`) -/

omit [CharZero 𝕜] in
/-- Paper `eq:Q-hypotheses` (supporting) — a product of factors `1 - c_j t` has
constant term `1`. -/
theorem coeff_zero_prod_linear {ι : Type*} (t : Finset ι) (c : ι → 𝕜) :
    (∏ j ∈ t, (1 - C (c j) * X)).coeff 0 = 1 := by
  rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_prod]
  simp

omit [CharZero 𝕜] in
/-- Paper `eq:Q-hypotheses` (supporting) — the `t`-coefficient of
`∏_j(1 - t/x_j)` is `-∑_j 1/x_j`. -/
theorem coeff_one_prod_linear {ι : Type*} (t : Finset ι) (c : ι → 𝕜) :
    (∏ j ∈ t, (1 - C (c j) * X)).coeff 1 = -∑ j ∈ t, c j := by
  -- `Finset.induction` wants `DecidableEq ι`; the statement does not, so the instance
  -- belongs to the proof rather than to the signature.
  classical
  induction t using Finset.induction with
  | empty => simp [Polynomial.coeff_one]
  | insert a t ha ih =>
    have hX : (X * ∏ j ∈ t, (1 - C (c j) * X)).coeff 1
        = (∏ j ∈ t, (1 - C (c j) * X)).coeff 0 := Polynomial.coeff_X_mul _ 0
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      show (1 - C (c a) * X) * (∏ j ∈ t, (1 - C (c j) * X))
        = (∏ j ∈ t, (1 - C (c j) * X)) - C (c a) * (X * ∏ j ∈ t, (1 - C (c j) * X)) from by ring,
      Polynomial.coeff_sub, Polynomial.coeff_C_mul, ih, hX, coeff_zero_prod_linear]
    ring

omit [CharZero 𝕜] in
/-- Paper `eq:Q-hypotheses` (supporting) — `Q(0)` is the scalar in front of the
product of linear factors. -/
theorem coeff_zero_of_factorization {ι : Type*} (t : Finset ι) (c : ι → 𝕜) (q0 : 𝕜)
    {Q : Polynomial 𝕜} (hQ : Q = C q0 * ∏ j ∈ t, (1 - C (c j) * X)) : Q.coeff 0 = q0 := by
  rw [hQ, Polynomial.coeff_C_mul, coeff_zero_prod_linear, mul_one]

omit [CharZero 𝕜] in
/-- **Paper `eq:Q-hypotheses`, `eq:leading-z-coeff`.**  For `Q = Q(0)∏_j(1-t/x_j)`,
the paper's `Λ_Q = -Q'(0)/Q(0)` is `∑_j 1/x_j`. -/
theorem lambdaQ_eq_sum {ι : Type*} (t : Finset ι) (c : ι → 𝕜)
    {q0 : 𝕜} (hq0 : q0 ≠ 0) {Q : Polynomial 𝕜} (hQ : Q = C q0 * ∏ j ∈ t, (1 - C (c j) * X)) :
    lambdaQ Q = ∑ j ∈ t, c j := by
  have h0 : Q.coeff 0 = q0 := coeff_zero_of_factorization t c q0 hQ
  have h1 : Q.coeff 1 = q0 * -∑ j ∈ t, c j := by
    rw [hQ, Polynomial.coeff_C_mul, coeff_one_prod_linear]
  rw [lambdaQ, h0, h1]
  field_simp

/-! ### The degree theorems under `eq:Q-hypotheses`

Over `ℝ`, with `Q(t) = Q(0)∏_{j}(1-t/x_j)` and `0 < x_1 ≤ … ≤ x_n`, the reciprocals
`c j = 1/x_j` are positive, so `Λ_Q = ∑_j 1/x_j > 0` and the hypothesis `Q'(0) ≠ 0`
of `eventual_natDegree_eq` is discharged rather than assumed.  The nonemptiness of
the index set is the paper's nonconstant `Q`, which `eq:Q-hypotheses` does not
supply on its own — `max{deg Q, r} > 1` allows `deg Q = 0` when `r > 1` — so it
stays an explicit hypothesis, as the paper's exclusion of constant `Q` from the
global theorem does. -/

/-- **Paper `eq:Q-hypotheses`, `eq:leading-z-coeff`.**  For a nonconstant
`Q = Q(0)∏_j(1-t/x_j)` with only positive zeros, `Λ_Q = ∑_j 1/x_j > 0`. -/
theorem lambdaQ_pos {ι : Type*} {t : Finset ι} (ht : t.Nonempty)
    {c : ι → ℝ} (hc : ∀ j ∈ t, 0 < c j) {q0 : ℝ} (hq0 : q0 ≠ 0)
    {Q : Polynomial ℝ} (hQ : Q = C q0 * ∏ j ∈ t, (1 - C (c j) * X)) :
    0 < lambdaQ Q := by
  rw [lambdaQ_eq_sum t c hq0 hQ]
  exact Finset.sum_pos hc ht

/-- **Paper `eq:Q-hypotheses`.**  A nonconstant `Q` with only positive zeros has
`Q'(0) ≠ 0`, since `-Q'(0)/Q(0) = ∑_j 1/x_j` is a positive sum. -/
theorem coeff_one_ne_zero_of_positive_zeros {ι : Type*} {t : Finset ι}
    (ht : t.Nonempty) {c : ι → ℝ} (hc : ∀ j ∈ t, 0 < c j) {q0 : ℝ} (hq0 : q0 ≠ 0)
    {Q : Polynomial ℝ} (hQ : Q = C q0 * ∏ j ∈ t, (1 - C (c j) * X)) : Q.coeff 1 ≠ 0 := by
  have hQ0 : Q.coeff 0 ≠ 0 := by
    rw [coeff_zero_of_factorization t c q0 hQ]; exact hq0
  exact (lambdaQ_ne_zero_iff hQ0).mp (ne_of_gt (lambdaQ_pos ht hc hq0 hQ))

/-- **`lem:eventual-degree` under `eq:Q-hypotheses`.**  For a nonconstant
`Q(t) = Q(0)∏_j(1-t/x_j)` with `0 < x_j`, a weight with `B(0) ≠ 0`, and `r ≥ 1`,
the reduced sequence of `eq:F-M-def` satisfies `deg F_M = ⌊M/r⌋` for all
sufficiently large `M`.  Nothing beyond the paper's own hypotheses is assumed:
`Q'(0) ≠ 0` comes from the positivity of the zeros. -/
theorem eventual_natDegree_eq_of_positive_zeros {ι : Type*} {t : Finset ι}
    (ht : t.Nonempty) {c : ι → ℝ} (hc : ∀ j ∈ t, 0 < c j) {q0 : ℝ} (hq0 : q0 ≠ 0)
    {Q : Polynomial ℝ} (hQ : Q = C q0 * ∏ j ∈ t, (1 - C (c j) * X))
    {r : ℕ} (hr : 1 ≤ r) (b : ℕ → ℝ) (hb0 : b 0 ≠ 0) (F : ℕ → Polynomial ℝ)
    (hrec : ∀ M, denomConv (ftDenom Q r) F M = C (b M)) :
    ∃ M₀ : ℕ, ∀ M, M₀ ≤ M → (F M).natDegree = M / r := by
  have hQ0 : Q.coeff 0 ≠ 0 := by
    rw [coeff_zero_of_factorization t c q0 hQ]; exact hq0
  exact eventual_natDegree_eq Q hr hQ0
    (coeff_one_ne_zero_of_positive_zeros ht hc hq0 hQ) b hb0 F hrec

/-- **`thm:main` clause 2 under `eq:Q-hypotheses`.**  Under the same data, every
sufficiently large coefficient polynomial is nonzero. -/
theorem eventual_ne_zero_of_positive_zeros {ι : Type*} {t : Finset ι}
    (ht : t.Nonempty) {c : ι → ℝ} (hc : ∀ j ∈ t, 0 < c j) {q0 : ℝ} (hq0 : q0 ≠ 0)
    {Q : Polynomial ℝ} (hQ : Q = C q0 * ∏ j ∈ t, (1 - C (c j) * X))
    {r : ℕ} (hr : 1 ≤ r) (b : ℕ → ℝ) (hb0 : b 0 ≠ 0) (F : ℕ → Polynomial ℝ)
    (hrec : ∀ M, denomConv (ftDenom Q r) F M = C (b M)) :
    ∃ M₀ : ℕ, ∀ M, M₀ ≤ M → F M ≠ 0 := by
  have hQ0 : Q.coeff 0 ≠ 0 := by
    rw [coeff_zero_of_factorization t c q0 hQ]; exact hq0
  exact eventual_ne_zero Q hr hQ0
    (coeff_one_ne_zero_of_positive_zeros ht hc hq0 hQ) b hb0 F hrec


end ForgacsTran
