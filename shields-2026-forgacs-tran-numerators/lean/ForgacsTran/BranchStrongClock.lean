/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.BranchClockSpacing
import ForgacsTran.BranchInteriorC1

/-!
# `prop:local-strong-clock` at the general pencil, with the remainder discharged

`BranchClockSpacing.exists_ft_local_strong_clock_at_branch` leaves the remainder
in its binder list: the decomposition and its `C⁰` and `C¹` bounds are assumed
there, because only the `C⁰` half had a general producer.
`BranchInteriorC1.exists_ftBranchErr_C1` supplies the `C¹` half, and this module
runs the composition.

## Main statements

* `exists_ftBranchErr_C0` — `eq:principal-decomposition`'s error is `O(σ^M)`,
  for the *named* error function rather than for an existentially chosen one.
* `exists_ft_local_strong_clock_at_branch_closed` — `eq:local-strong-clock` at
  the general admissible pencil with nothing about the remainder assumed, and
  the pair shown **consecutive**: no zero of `F_M` between them.

## Implementation notes

**Two thresholds in `M`, and both are geometric-beats-polynomial.**  The `C⁰`
half needs `Cσ^M < sinδ`, so the error cannot reach the cosine's own scale;
the `C¹` half needs `(M+1)Cσ^M` below the phase's own turning.
`WeightedDominance.exists_succ_pow_mul_geometric_le` supplies both, at `p = 0`
and `p = 1`.

**`κ_2` is bound before `M₀`, and that is what gives the second inequality
content.**  Chosen after the two zeros it is absorbing — the right side is
strictly increasing and unbounded in it, so every left side is covered
(`ClockSpacing.exists_absorbing_constant`, which exhibits the choice).  Chosen
once for the pencil and the subarc it is not: the coefficient it multiplies is
`((π + 2E)/((M+1) − κ))²/((M+1) − κ)`, which is `O(M^{-3})`, so a **fixed** `κ_2`
leaves an `M^{-3}` rate however large it is, and that rate is
`eq:local-strong-clock`.  A `κ_2` free to grow with `M` destroys exactly that,
and nothing in the statement would have failed.

**`u₀` is bound after `M`, and that is not cosmetic.**  `Φ_M(lo) = (M+1)lo - ψ(lo)`
grows without bound in `M`, so for a *fixed* `u₀` the first window binder
`Φ_M(lo) ≤ u₀ - δ` fails at large `M` and an `∃ M₀, ∀ M ≥ M₀` statement over a
fixed `u₀` is eventually vacuously true.  Binding `u₀` inside the `∀ M` is what
makes the conclusion say something at every `M` above the threshold: the
admissible interval for `u₀` is `[Φ_M(lo) + δ, Φ_M(hi) - π - δ]`, which has
length at least `π` once `Φ_M` turns by `π + 2δ`, and an interval of length `π`
contains a zero of the cosine.  `cubic_local_strong_clock_closed` binds `u₀`
outside, and `scripts/check_cubic_strong_clock_threshold.py` accordingly exhibits
its witness by choosing `u₀ = 130.376` **at** `M = 73` rather than in advance.

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Local phase
quantization and strong-clock spacing» (`subsec:strong-clock`,
`prop:local-strong-clock`, `eq:local-strong-clock`,
`eq:C1-interior-remainder`).

## Tags

strong clock, interior remainder, admissible pencil
-/

namespace ForgacsTran

open Real Set

variable {n r : ℕ} {a : Fin n → ℝ} {c : ℝ} {B : Polynomial ℂ}

/-- **`eq:principal-decomposition`'s `C⁰` bound, for the named error.**
`ClockSpacing`'s producers return the error existentially; the `C¹` half is about
`ftBranchErr`, and the two only compose if the same function carries both.  The
decomposition clause pins the error, so the identification is a subtraction. -/
theorem exists_ftBranchErr_C0 (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c)
    (hr : 1 ≤ r) (hcls : 3 ≤ n ∨ 2 ≤ r) (hBr : HasRealCoeffs B) (hB0 : B ≠ 0)
    {lo hi : ℝ} (hlohi : lo ≤ hi) (harc : Icc lo hi ⊆ Ioo 0 (π / r))
    (hBne : ∀ θ ∈ Icc lo hi, B.eval (ftPrincipal (ftTau a r (n - 1)) θ) ≠ 0) :
    ∃ C σ : ℝ, 0 ≤ C ∧ 0 < σ ∧ σ < 1 ∧
      ∀ (M : ℕ), ∀ θ ∈ Icc lo hi,
        |ftBranchErr c B a r (n - 1) lo M θ| ≤ C * σ ^ M := by
  classical
  have hn : 0 < n := by omega
  have hnr : 2 ≤ n ∨ 2 ≤ r := Or.inl hn2
  obtain ⟨-, hτpos⟩ := ft_branch_root_and_pos (a := a) (r := r) c hn ha hr hnr
  have hagree : ∀ θ ∈ Ioo (0 : ℝ) (π / r), ftTau a r (n - 1) θ = ftTau a r (n - 1) θ :=
    fun _ _ => rfl
  have hdata : ∃ CI σ : ℝ, 0 < σ ∧ σ < 1 ∧
      ∀ (M : ℕ), ∀ θ ∈ Icc lo hi,
        |ftRemainder (ftRootPoly c a) B r (ftBranchZ a c r (n - 1))
          (ftTau a r (n - 1)) M θ| ≤ CI * σ ^ M := by
    rcases Nat.lt_or_ge r 2 with hr1 | hr2
    · have hrone : r = 1 := by omega
      subst hrone
      have hn3 : 3 ≤ n := by rcases hcls with h | h <;> omega
      obtain ⟨CI, σI, -, -, hσ0, hσ1, -, hrem, -, -⟩ :=
        exists_interior_data_on_subinterval_pi (a := a) (c := c) (B := B)
          (τ := ftTau a 1 (n - 1)) hn3 ha hc hBr hB0 hagree hlohi harc
      exact ⟨CI, σI, hσ0, hσ1, fun M θ hθ => hrem M θ hθ.1 hθ.2⟩
    · obtain ⟨CI, σI, -, -, hσ0, hσ1, -, hrem, -, -⟩ :=
        exists_interior_data_on_subinterval_two_le (a := a) (c := c) (B := B)
          (τ := ftTau a r (n - 1)) hn2 ha hc hr2 hBr hB0 hagree hlohi harc
      exact ⟨CI, σI, hσ0, hσ1, fun M θ hθ => hrem M θ hθ.1 hθ.2⟩
  obtain ⟨CI, σ, hσ0, hσ1, hrem⟩ := hdata
  have hWc : ContinuousOn (fun θ => ftAmp (ftRootPoly c a) B r
      ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ)
      (ftPrincipal (ftTau a r (n - 1)) θ)) (Icc lo hi) := by
    refine ContinuousOn.congr
      (continuousOn_ftBranchAmp (B := B) hn ha hc.ne' hr hnr harc) ?_
    exact fun θ hθ => (ftBranchAmp_eq_ftAmp (B := B) (c := c) hn ha hr hnr (harc hθ)).symm
  have hWne : ∀ θ ∈ Icc lo hi, ftAmp (ftRootPoly c a) B r
      ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ)
      (ftPrincipal (ftTau a r (n - 1)) θ) ≠ 0 := by
    intro θ hθ
    rw [← ftBranchAmp_eq_ftAmp (B := B) (c := c) hn ha hr hnr (harc hθ)]
    exact ftBranchAmp_ne_zero hn ha hc.ne' hr hnr (harc hθ) (hBne θ hθ)
  obtain ⟨A, hA, hfloor⟩ := exists_amplitude_floor_on_subarc hWc hWne
  refine ⟨max CI 0 / (2 * A), σ, by positivity, hσ0, hσ1, fun M θ hθ => ?_⟩
  obtain ⟨e, heq, hbd⟩ := interior_cos_error_geometric (M := M)
    (ψ := ftBranchPhase (ftRootPoly c a) B a r (n - 1) lo)
    (hτpos θ (harc hθ)) hA hσ0.le (hfloor θ hθ)
    (le_trans (hrem M θ hθ)
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hσ0.le M)))
    (ftAmp_eq_polar_at_branch (B := B) hn ha hc.ne' hr hnr hlohi harc hBne hθ)
  have hid : ftBranchErr c B a r (n - 1) lo M θ = e := by
    have hspec := ftBranchErr_spec c B a r (n - 1) lo M θ
    rw [heq] at hspec
    exact (add_left_cancel hspec).symm
  rw [hid]
  exact hbd

/-- **`eq:local-strong-clock` at the general admissible pencil, with nothing
about the remainder assumed.**  `exists_ft_local_strong_clock_at_branch` with its
decomposition, `C⁰` and `C¹` binders discharged: the decomposition from
`ftBranchErr_spec`, the value bound from `exists_ftBranchErr_C0`, the derivative
and its bound from `BranchInteriorC1.exists_ftBranchErr_C1`.

The subarc `[lo, hi]` sits strictly inside a compact divisor-free `[lo', hi']`,
which is the manuscript's `𝒥 ⊂ 𝒥_0` and is what a two-sided derivative at the
endpoints of `[lo, hi]` needs.

**Where to find the manuscript's own sentences in this conclusion**, since two of
them are stated here in a stronger form than the paper writes and a reader
looking for the literal wording will not match on it:

* *"every zero of `F_M` in `z(𝒥)` … is `z(θ_{k,M})` for a unique
  `θ_{k,M} ∈ 𝒥`"* is the `∃!` clause, **specialized to a zero**.  That clause
  carries no `eval w = 0` antecedent, because the proof does not use one:
  uniqueness of the parameter holds at *every* point of `z(𝒥)`, zero or not, and
  it comes from `ftBranchZ_strictMonoOn` alone.  Adding the hypothesis back would
  state something strictly weaker and would leave an antecedent nothing consumes,
  so it is deliberately absent rather than overlooked.  No weakened restatement
  is provided: a second, weaker declaration is what a later reader cites by
  accident.
* *"the indices `k` running consecutively"* is the `k' = k + 1` clause, whose
  hypothesis is that no zero of `F_M` lies strictly between the two — which is
  what "consecutive" means and what the isolation clause above supplies for the
  produced pair. -/
theorem exists_ft_local_strong_clock_at_branch_closed
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r)
    (hcls : 3 ≤ n ∨ 2 ≤ r) (hBr : HasRealCoeffs B) (hB0 : B ≠ 0)
    {lo' hi' lo hi δ : ℝ}
    (harc : Icc lo' hi' ⊆ Ioo 0 (π / r))
    (hBne : ∀ θ ∈ Icc lo' hi', B.eval (ftPrincipal (ftTau a r (n - 1)) θ) ≠ 0)
    (hlo : lo' < lo) (hhi : hi < hi') (hlohi : lo < hi)
    (hδ : 0 < δ) (hδ4 : δ ≤ π / 4) :
    ∃ κ ≥ (0 : ℝ), ∃ κ₂ ≥ (0 : ℝ), ∃ C ≥ (0 : ℝ), ∃ σ : ℝ, 0 < σ ∧ σ < 1 ∧
      ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      -- the quantization point the rest of the statement is about EXISTS
      (∃ u₀ : ℝ, Real.cos u₀ = 0 ∧
        ((M : ℝ) + 1) * lo - ftBranchPhase (ftRootPoly c a) B a r (n - 1) lo' lo
            ≤ u₀ - δ ∧
        u₀ + π + δ ≤ ((M : ℝ) + 1) * hi
            - ftBranchPhase (ftRootPoly c a) B a r (n - 1) lo' hi) ∧
      ∀ u₀ : ℝ, Real.cos u₀ = 0 →
      ((M : ℝ) + 1) * lo - ftBranchPhase (ftRootPoly c a) B a r (n - 1) lo' lo
          ≤ u₀ - δ →
      u₀ + π + δ ≤ ((M : ℝ) + 1) * hi
          - ftBranchPhase (ftRootPoly c a) B a r (n - 1) lo' hi →
      ∃ θk ∈ Icc lo hi, ∃ θk1 ∈ Icc lo hi, θk < θk1 ∧
        (ftCoeffPoly (ftRootPoly c a) B r M).eval
            ((ftBranchZ a c r (n - 1) θk : ℝ) : ℂ) = 0 ∧
        (ftCoeffPoly (ftRootPoly c a) B r M).eval
            ((ftBranchZ a c r (n - 1) θk1 : ℝ) : ℂ) = 0 ∧
        (∀ θ ∈ Icc lo hi, θk < θ → θ < θk1 →
          (ftCoeffPoly (ftRootPoly c a) B r M).eval
            ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ) ≠ 0) ∧
        (∀ θ ∈ Icc lo hi,
          (ftCoeffPoly (ftRootPoly c a) B r M).eval
              ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ) = 0 →
            (Polynomial.derivative (ftCoeffPoly (ftRootPoly c a) B r M)).eval
              ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ) ≠ 0) ∧
        (∀ w ∈ (fun θ : ℝ => ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ)) '' Icc lo hi,
          ∃! θ : ℝ, θ ∈ Icc lo hi
            ∧ ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ) = w) ∧
        (∀ θ ∈ Icc lo hi,
          (ftCoeffPoly (ftRootPoly c a) B r M).eval
              ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ) = 0 →
            ∃ k : ℤ, |((M : ℝ) + 1) * θ
                - ftBranchPhase (ftRootPoly c a) B a r (n - 1) lo' θ
                - (u₀ + (k : ℝ) * π)| ≤ π / 2 * (C * σ ^ M)) ∧
        (∀ θ ∈ Icc lo hi, ∀ θ' ∈ Icc lo hi, ∀ k k' : ℤ,
          (ftCoeffPoly (ftRootPoly c a) B r M).eval
              ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ) = 0 →
          (ftCoeffPoly (ftRootPoly c a) B r M).eval
              ((ftBranchZ a c r (n - 1) θ' : ℝ) : ℂ) = 0 →
          θ < θ' →
          (∀ s ∈ Icc lo hi, θ < s → s < θ' →
            (ftCoeffPoly (ftRootPoly c a) B r M).eval
              ((ftBranchZ a c r (n - 1) s : ℝ) : ℂ) ≠ 0) →
          |((M : ℝ) + 1) * θ - ftBranchPhase (ftRootPoly c a) B a r (n - 1) lo' θ
              - (u₀ + (k : ℝ) * π)| < δ →
          |((M : ℝ) + 1) * θ' - ftBranchPhase (ftRootPoly c a) B a r (n - 1) lo' θ'
              - (u₀ + (k' : ℝ) * π)| < δ →
            k' = k + 1) ∧
        θk1 - θk ≤ (π + 2 * (π / 2 * (C * σ ^ M))) / (((M : ℝ) + 1) - κ) ∧
          |(θk1 - θk) - π / ((M : ℝ) + 1)
              - π * (ftBranchAmpDeriv (ftRootPoly c a) B a r (n - 1) θk
                  / ftBranchAmp (ftRootPoly c a) B a r (n - 1) θk).im
                / ((M : ℝ) + 1) ^ 2|
            ≤ (2 * (π / 2 * (C * σ ^ M))
                  + κ₂ * ((π + 2 * (π / 2 * (C * σ ^ M)))
                      / (((M : ℝ) + 1) - κ)) ^ 2)
                / (((M : ℝ) + 1) - κ)
              + π * κ ^ 2 / (((M : ℝ) + 1) ^ 2 * (((M : ℝ) + 1) - κ)) := by
  classical
  have hpi := Real.pi_pos
  have hsub : Icc lo hi ⊆ Icc lo' hi' := fun θ hθ =>
    ⟨le_trans hlo.le hθ.1, le_trans hθ.2 hhi.le⟩
  have hlohi' : lo' ≤ hi' := le_trans hlo.le (le_trans hlohi.le hhi.le)
  have hsin : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ (by linarith)
  -- the `C⁰` and `C¹` halves, on the same error function and the same phase
  obtain ⟨C₀, σ₀, hC₀, hσ₀0, hσ₀1, hval⟩ :=
    exists_ftBranchErr_C0 hn2 ha hc hr hcls hBr hB0 hlohi' harc hBne
  obtain ⟨C₁, σ₁, hC₁, hσ₁0, hσ₁1, hder⟩ :=
    exists_ftBranchErr_C1 hn2 ha hc hr hcls hBr harc hBne hlo hhi hlohi.le
  set C : ℝ := max C₀ C₁ with hC
  set σ : ℝ := max σ₀ σ₁ with hσ
  have hC0 : 0 ≤ C := le_trans hC₀ (le_max_left _ _)
  have hσ0 : 0 < σ := lt_of_lt_of_le hσ₀0 (le_max_left _ _)
  have hσ1 : σ < 1 := max_lt hσ₀1 hσ₁1
  have hvalC : ∀ (M : ℕ), ∀ θ ∈ Icc lo hi,
      |ftBranchErr c B a r (n - 1) lo' M θ| ≤ C * σ ^ M := by
    intro M θ hθ
    refine le_trans (hval M θ (hsub hθ)) ?_
    exact mul_le_mul (le_max_left _ _)
      (pow_le_pow_left₀ hσ₀0.le (le_max_left _ _) M) (by positivity) hC0
  have hderC : ∀ (M : ℕ), ∀ θ ∈ Icc lo hi,
      |deriv (ftBranchErr c B a r (n - 1) lo' M) θ| ≤ ((M : ℝ) + 1) * C * σ ^ M := by
    intro M θ hθ
    refine le_trans (hder M θ hθ).2 ?_
    have h1 : ((M : ℝ) + 1) * C₁ ≤ ((M : ℝ) + 1) * C :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
    exact mul_le_mul h1 (pow_le_pow_left₀ hσ₁0.le (le_max_right _ _) M)
      (by positivity) (by positivity)
  have hn : 0 < n := by omega
  have hnr : 2 ≤ n ∨ 2 ≤ r := Or.inl hn2
  obtain ⟨-, hτpos⟩ := ft_branch_root_and_pos (a := a) (r := r) c hn ha hr hnr
  set W := ftBranchAmp (ftRootPoly c a) B a r (n - 1) with hWdef
  set dW := ftBranchAmpDeriv (ftRootPoly c a) B a r (n - 1) with hdWdef
  set ψ := ftBranchPhase (ftRootPoly c a) B a r (n - 1) lo' with hψdef
  have hψd : ∀ θ ∈ Icc lo hi, HasDerivAt ψ ((dW θ / W θ).im) θ := fun θ hθ =>
    hasDerivAt_ftBranchPhase hn ha hc.ne' hr hnr harc hBne (hsub hθ)
  -- the phase bound, and the two thresholds
  obtain ⟨κ, hκ0, hκ⟩ :=
    exists_ftBranch_phase_deriv_bound (B := B) (by omega) ha hc.ne' hr (Or.inl hn2)
      (fun θ hθ => harc (hsub hθ)) (fun θ hθ => hBne θ (hsub hθ))
  -- the Taylor constant is taken on `[lo', hi']`, so that its phase is based where
  -- `ftBranchErr`'s is; restricting to `[lo, hi]` afterwards keeps the same `ψ`.
  obtain ⟨κ₂, hκ₂0, htay'⟩ :=
    exists_ftBranch_taylor_bound (B := B) (by omega) ha hc.ne' hr (Or.inl hn2) harc hBne
  have htay : ∀ θa ∈ Icc lo hi, ∀ θb ∈ Icc lo hi, θa ≤ θb →
      |ftBranchPhase (ftRootPoly c a) B a r (n - 1) lo' θb
          - ftBranchPhase (ftRootPoly c a) B a r (n - 1) lo' θa
          - (ftBranchAmpDeriv (ftRootPoly c a) B a r (n - 1) θa
              / ftBranchAmp (ftRootPoly c a) B a r (n - 1) θa).im * (θb - θa)|
        ≤ κ₂ * (θb - θa) ^ 2 :=
    fun θa hθa θb hθb hab => htay' θa (hsub hθa) θb (hsub hθb) hab
  obtain ⟨M₁, hM₁⟩ := exists_succ_pow_mul_geometric_le hσ0.le hσ1 hC0 (half_pos hsin) 0
  obtain ⟨M₂, hM₂⟩ :=
    exists_succ_pow_mul_geometric_le hσ0.le hσ1 hC0 (by norm_num : (0:ℝ) < 1 / 2) 1
  obtain ⟨M₃, hM₃⟩ : ∃ M₃ : ℕ, ∀ M : ℕ, M₃ ≤ M → κ + 1 ≤ (M : ℝ) + 1 := by
    obtain ⟨N, hN⟩ := exists_nat_ge κ
    exact ⟨N, fun M hM => by
      have : (N : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
      linarith⟩
  -- the fourth threshold: `Φ_M` must turn by more than `2π + 2δ` across `[lo, hi]`
  -- before a quantization point is guaranteed to sit in the admissible window
  obtain ⟨M₄, hM₄⟩ : ∃ M₄ : ℕ, ∀ M : ℕ, M₄ ≤ M →
      2 * π + 2 * δ ≤ (((M : ℝ) + 1) - κ) * (hi - lo) := by
    obtain ⟨N, hN⟩ := exists_nat_ge (κ + (2 * π + 2 * δ) / (hi - lo))
    refine ⟨N, fun M hM => ?_⟩
    have hMN : (N : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    have hd : 0 < hi - lo := by linarith
    have h2 : (2 * π + 2 * δ) / (hi - lo) ≤ (M : ℝ) - κ := by linarith
    rw [div_le_iff₀ hd] at h2
    nlinarith [h2, hd]
  refine ⟨κ, hκ0, κ₂, hκ₂0, C, hC0, σ, hσ0, hσ1, max (max (max M₁ M₂) M₃) M₄,
    fun M hM => ⟨?_, fun u₀ hcos hwlo hwhi => ?_⟩⟩
  all_goals have hMa : M₁ ≤ M :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hM
  all_goals have hMb : M₂ ≤ M :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hM
  all_goals have hMc : M₃ ≤ M :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hM
  all_goals have hMd : M₄ ≤ M := le_trans (le_max_right _ _) hM
  -- the exhibition: `Φ_M` turns far enough, and the cosine's zeros are `π` apart
  · have hmvt : |ψ hi - ψ lo| ≤ κ * (hi - lo) :=
      phase_mvt_bound hψd hκ ⟨le_rfl, hlohi.le⟩ ⟨hlohi.le, le_rfl⟩ hlohi.le
    have hgap : (((M : ℝ) + 1) * lo - ψ lo) + π
        ≤ (((M : ℝ) + 1) * hi - ψ hi) - π - δ - δ := by
      have hm := abs_le.1 hmvt
      nlinarith [hm.2, hM₄ M hMd]
    obtain ⟨u, hucos, hu1, hu2⟩ := exists_quantization_point_in_interval
      (A := ((M : ℝ) + 1) * lo - ψ lo + δ)
      (B := ((M : ℝ) + 1) * hi - ψ hi - π - δ) (by linarith)
    exact ⟨u, hucos, by linarith, by linarith⟩
  have hLκ : κ + 1 ≤ (M : ℝ) + 1 := hM₃ M hMc
  -- the composition, with `κ` and `ψ` NAMED rather than existentially bound: the
  -- `C⁰` and `C¹` halves are about `ftBranchErr` at the base `lo'`, so a version
  -- hiding the phase behind an existential would not compose with them.
  have hΦd : ∀ θ ∈ Icc lo hi,
      HasDerivAt (fun θ' => ((M : ℝ) + 1) * θ' - ψ θ')
        (((M : ℝ) + 1) - (dW θ / W θ).im) θ := by
    intro θ hθ
    have hlin : HasDerivAt (fun θ' : ℝ => ((M : ℝ) + 1) * θ') ((M : ℝ) + 1) θ := by
      simpa using (hasDerivAt_id θ).const_mul (((M : ℝ) + 1))
    exact hlin.sub (hψd θ hθ)
  have hΦpos : ∀ θ ∈ Icc lo hi, 0 < ((M : ℝ) + 1) - (dW θ / W θ).im := by
    intro θ hθ
    have := abs_le.1 (hκ θ hθ)
    linarith
  have hmono : StrictMonoOn (fun θ' => ((M : ℝ) + 1) * θ' - ψ θ') (Icc lo hi) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc lo hi)
      (fun θ hθ => (hΦd θ hθ).continuousAt.continuousWithinAt) (fun θ hθ => ?_)
    rw [interior_Icc] at hθ
    have hθ' : θ ∈ Icc lo hi := ⟨hθ.1.le, hθ.2.le⟩
    rw [(hΦd θ hθ').deriv]
    exact hΦpos θ hθ'
  obtain ⟨P, hP⟩ := exists_real_ftCoeffPoly_of_real (hasRealCoeffs_ftRootPoly c a) hBr r M
  have hWne : ∀ θ ∈ Icc lo hi, W θ ≠ 0 := fun θ hθ =>
    ftBranchAmp_ne_zero hn ha hc.ne' hr hnr (harc (hsub hθ)) (hBne θ (hsub hθ))
  have hWpos : ∀ θ ∈ Icc lo hi,
      0 < ftPrincipalAmp (ftRootPoly c a) B r (ftBranchZ a c r (n - 1))
        (ftTau a r (n - 1)) θ := by
    intro θ hθ
    have heq : ftPrincipalAmp (ftRootPoly c a) B r (ftBranchZ a c r (n - 1))
        (ftTau a r (n - 1)) θ = ‖W θ‖ := by
      rw [ftPrincipalAmp, hWdef,
        ← ftBranchAmp_eq_ftAmp (B := B) (c := c) hn ha hr hnr (harc (hsub hθ))]
    rw [heq]
    exact norm_pos_iff.2 (hWne θ hθ)
  -- the two thresholds, in the shapes the composition consumes
  have hC0M : (0 : ℝ) ≤ C * σ ^ M := by positivity
  have hebd : ∀ θ ∈ Icc lo hi, |ftBranchErr c B a r (n - 1) lo' M θ| < Real.sin δ := by
    intro θ hθ
    have h1 := hM₁ M hMa
    rw [pow_zero, one_mul] at h1
    linarith [hvalC M θ hθ]
  have hCeb : ∀ θ ∈ Icc lo hi, ((M : ℝ) + 1) * C * σ ^ M
      < Real.sqrt 2 / 2 * (((M : ℝ) + 1) - (dW θ / W θ).im) := by
    intro θ hθ
    have h2 := hM₂ M hMb
    rw [pow_one] at h2
    have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hnn : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    have hd1 : (1 : ℝ) ≤ ((M : ℝ) + 1) - (dW θ / W θ).im := by
      have := abs_le.1 (hκ θ hθ)
      linarith
    nlinarith [h2, hsq, hnn]
  -- simplicity, stated over EVERY zero in the subarc rather than the produced
  -- pair: the clause is then independent of how the zeros are enumerated
  have hsimple : ∀ θ ∈ Icc lo hi,
      (ftCoeffPoly (ftRootPoly c a) B r M).eval
          ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ) = 0 →
        (Polynomial.derivative (ftCoeffPoly (ftRootPoly c a) B r M)).eval
          ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ) ≠ 0 := by
    intro θ hθ hFz
    have hθ' : θ ∈ Icc lo' hi' := hsub hθ
    have hθarc : θ ∈ Ioo (0 : ℝ) (π / r) := harc hθ'
    have hb' : ∀ s ∈ Ioo (0 : ℝ) (π / r), FTBranchAt a r (n - 1) s :=
      fun _s hs => ftBranchAt_of_arc_principal hn ha hr hnr hs
    -- the real model, and the zero read there
    have hPz : P.eval (ftBranchZ a c r (n - 1) θ) = 0 := by
      have h := hFz
      rw [← hP, eval_map_ofReal] at h
      exact_mod_cast h
    -- the phase zero, from the converse
    have hzero : Real.cos (((M : ℝ) + 1) * θ - ψ θ)
        + ftBranchErr c B a r (n - 1) lo' M θ = 0 :=
      phase_zero_of_ftCoeffPoly_eval_eq_zero
        (ftBranchErr_spec c B a r (n - 1) lo' M θ) hFz
    -- transversality of the phase equation there
    have hcross : -Real.sin (((M : ℝ) + 1) * θ - ψ θ)
        * (((M : ℝ) + 1) - (dW θ / W θ).im)
        + deriv (ftBranchErr c B a r (n - 1) lo' M) θ ≠ 0 :=
      deriv_phase_eq_ne_zero (Φ := fun s => ((M : ℝ) + 1) * s - ψ s)
        (dΦ := fun s => ((M : ℝ) + 1) - (dW s / W s).im)
        (e := ftBranchErr c B a r (n - 1) lo' M)
        (de := deriv (ftBranchErr c B a r (n - 1) lo' M)) (θ := θ)
        hδ hδ4 (hΦpos θ hθ) (hderC M θ hθ) (hCeb θ hθ) (hebd θ hθ) hzero
    -- the identity, on a neighbourhood, against `‖W‖` rather than `ftPrincipalAmp`
    have hnb : Ioo lo' hi' ∈ nhds θ :=
      isOpen_Ioo.mem_nhds ⟨lt_of_lt_of_le hlo hθ.1, lt_of_le_of_lt hθ.2 hhi⟩
    have hid : (fun s => ftTau a r (n - 1) s ^ (M + 1)
          * P.eval (ftBranchZ a c r (n - 1) s))
        =ᶠ[nhds θ] fun s => 2 * ‖W s‖
          * (Real.cos (((M : ℝ) + 1) * s - ψ s)
            + ftBranchErr c B a r (n - 1) lo' M s) := by
      filter_upwards [hnb] with s hs
      have hsIcc : s ∈ Icc lo' hi' := ⟨hs.1.le, hs.2.le⟩
      have hAeq : ftPrincipalAmp (ftRootPoly c a) B r (ftBranchZ a c r (n - 1))
          (ftTau a r (n - 1)) s = ‖W s‖ := by
        rw [ftPrincipalAmp, hWdef,
          ← ftBranchAmp_eq_ftAmp (B := B) (c := c) hn ha hr hnr (harc hsIcc)]
      have hWs : (0 : ℝ) < ‖W s‖ := norm_pos_iff.2
        (ftBranchAmp_ne_zero hn ha hc.ne' hr hnr (harc hsIcc) (hBne s hsIcc))
      have hne2 : (2 : ℝ) * ‖W s‖ ≠ 0 := by positivity
      have hspec := ftBranchErr_spec c B a r (n - 1) lo' M s
      rw [hAeq, ← hP, re_scaled_coeff_eq, div_eq_iff hne2] at hspec
      rw [hspec]
      ring
    -- the transfer
    have hd : (Polynomial.derivative P).eval (ftBranchZ a c r (n - 1) θ) ≠ 0 :=
      derivative_eval_ne_zero_of_transversal (M := M) (P := P)
        (τ := ftTau a r (n - 1)) (z := ftBranchZ a c r (n - 1))
        (A := fun s => ‖W s‖) (Φ := fun s => ((M : ℝ) + 1) * s - ψ s)
        (e := ftBranchErr c B a r (n - 1) lo' M)
        (dΦ := fun s => ((M : ℝ) + 1) - (dW s / W s).im)
        (de := deriv (ftBranchErr c B a r (n - 1) lo' M)) (θ := θ) hid
        (hasDerivAt_ftTau hn ha hr hθarc hb') (hτpos θ hθarc)
        (hasDerivAt_ftBranchZ hn ha hr hθarc hb'
          (ftBranchZ_pos_principal hn ha hc hr hnr hθarc).ne')
        (ftBranchZDeriv_pos hn ha hr hθarc (hb' θ hθarc)
          (ftBranchZ_pos_principal hn ha hc hr hnr hθarc)).ne'
        (hasDerivAt_ftBranchAmpNorm hn ha hc.ne' hr hnr hθarc (hBne θ hθ'))
        (norm_pos_iff.2
          (ftBranchAmp_ne_zero hn ha hc.ne' hr hnr hθarc (hBne θ hθ')))
        (hΦd θ hθ) ((hder M θ hθ).1) hPz hzero hcross
    intro hcon
    rw [← hP, Polynomial.derivative_map, eval_map_ofReal] at hcon
    exact hd (by exact_mod_cast hcon)
  -- the parameter of a point of `z(𝒥)` is unique: `z` is strictly monotone on the
  -- arc (`ftBranchZ_strictMonoOn`), hence injective on the subarc.  The zero
  -- condition is NOT an antecedent here — uniqueness holds at every point of the
  -- image, and adding it would state something weaker than what is true.
  have hzinj : ∀ w ∈ (fun θ : ℝ => ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ)) '' Icc lo hi,
      ∃! θ : ℝ, θ ∈ Icc lo hi ∧ ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ) = w := by
    have hmonoz : StrictMonoOn (ftBranchZ a c r (n - 1)) (Ioo 0 (π / r)) :=
      ftBranchZ_strictMonoOn hn ha hc hr (even_add_pred_add_one hn)
        (fun _s hs => ftBranchAt_of_arc_principal hn ha hr hnr hs)
    have hinj : Set.InjOn (ftBranchZ a c r (n - 1)) (Icc lo hi) :=
      (hmonoz.injOn).mono (fun θ hθ => harc (hsub hθ))
    rintro w ⟨θ₀, hθ₀, rfl⟩
    refine ⟨θ₀, ⟨hθ₀, rfl⟩, ?_⟩
    rintro θ ⟨hθ, hw⟩
    dsimp only at hw
    exact hinj hθ hθ₀ (Complex.ofReal_inj.1 hw)
  -- the zero-to-phase-zero converse, used by both remaining clauses
  have hphz : ∀ θ ∈ Icc lo hi,
      (ftCoeffPoly (ftRootPoly c a) B r M).eval
          ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ) = 0 →
        Real.cos (((M : ℝ) + 1) * θ - ψ θ)
          + ftBranchErr c B a r (n - 1) lo' M θ = 0 := fun θ _ hFz =>
    phase_zero_of_ftCoeffPoly_eval_eq_zero
      (ftBranchErr_spec c B a r (n - 1) lo' M θ) hFz
  -- `eq:local-phase-quantization` AT THE BRANCH, with the index it is indexed by:
  -- `phase_zero_localized` supplies the integer, `phase_quantization_error`
  -- sharpens the `δ` window to the `O(σ^M)` the display asserts.
  have hquant : ∀ θ ∈ Icc lo hi,
      (ftCoeffPoly (ftRootPoly c a) B r M).eval
          ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ) = 0 →
        ∃ k : ℤ, |((M : ℝ) + 1) * θ - ψ θ - (u₀ + (k : ℝ) * π)|
          ≤ π / 2 * (C * σ ^ M) := by
    intro θ hθ hFz
    have hz0 := hphz θ hθ hFz
    obtain ⟨k, hk⟩ := phase_zero_localized (Φ := fun s => ((M : ℝ) + 1) * s - ψ s)
      (e := ftBranchErr c B a r (n - 1) lo' M) (u₀ := u₀) (δ := δ) (θ := θ)
      hδ (by linarith) hcos (hebd θ hθ) hz0
    refine ⟨k, ?_⟩
    have hcosk : Real.cos (u₀ + (k : ℝ) * π) = 0 := by
      rw [Real.cos_add_int_mul_pi, hcos, mul_zero]
    have hnear : |((M : ℝ) + 1) * θ - ψ θ - (u₀ + (k : ℝ) * π)| ≤ π / 2 := by
      have := hk; linarith [abs_nonneg (((M : ℝ) + 1) * θ - ψ θ - (u₀ + (k : ℝ) * π))]
    exact phase_quantization_error hcosk hnear hz0 (hvalC M θ hθ)
  -- "the indices `k` running consecutively", at the branch
  have hcons : ∀ θ ∈ Icc lo hi, ∀ θ' ∈ Icc lo hi, ∀ k k' : ℤ,
      (ftCoeffPoly (ftRootPoly c a) B r M).eval
          ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ) = 0 →
      (ftCoeffPoly (ftRootPoly c a) B r M).eval
          ((ftBranchZ a c r (n - 1) θ' : ℝ) : ℂ) = 0 →
      θ < θ' →
      (∀ s ∈ Icc lo hi, θ < s → s < θ' →
        (ftCoeffPoly (ftRootPoly c a) B r M).eval
          ((ftBranchZ a c r (n - 1) s : ℝ) : ℂ) ≠ 0) →
      |((M : ℝ) + 1) * θ - ψ θ - (u₀ + (k : ℝ) * π)| < δ →
      |((M : ℝ) + 1) * θ' - ψ θ' - (u₀ + (k' : ℝ) * π)| < δ →
        k' = k + 1 := by
    intro θ hθ θ' hθ' k k' hFz hFz' hltθ hadjF hwk hwk'
    refine adjacent_phase_zeros_consecutive_index
      (Φ := fun s => ((M : ℝ) + 1) * s - ψ s)
      (dΦ := fun s => ((M : ℝ) + 1) - (dW s / W s).im)
      (e := ftBranchErr c B a r (n - 1) lo' M)
      (de := deriv (ftBranchErr c B a r (n - 1) lo' M))
      (Ce := ((M : ℝ) + 1) * C * σ ^ M)
      hδ hδ4 hcos hmono hΦd (fun s hs => (hder M s hs).1) hΦpos
      (fun s hs => hderC M s hs) hCeb hebd hθ hθ' hltθ
      (hphz θ hθ hFz) (hphz θ' hθ' hFz') hwk hwk' ?_
    intro s hs hgt hlts hzs
    -- a phase zero here would be a zero of `F_M`, contradicting adjacency
    refine hadjF s hs hgt hlts ?_
    have hpa : ftPrincipalAmp (ftRootPoly c a) B r (ftBranchZ a c r (n - 1))
        (ftTau a r (n - 1)) s = ‖W s‖ := by
      rw [ftPrincipalAmp, hWdef,
        ← ftBranchAmp_eq_ftAmp (B := B) (c := c) hn ha hr hnr (harc (hsub hs))]
    obtain ⟨P', hP'⟩ := exists_real_ftCoeffPoly_of_real
      (hasRealCoeffs_ftRootPoly c a) hBr r M
    exact ftCoeffPoly_eval_eq_zero_of_phase_zero (ψ := ψ) hP'
      (hτpos s (harc (hsub hs))) (hWpos s hs)
      (by rw [ftBranchErr_spec c B a r (n - 1) lo' M s]) hzs
  obtain ⟨θk, hk, θk1, hk1, hlt, hz1, hz2, hiso, hsp1, hsp2⟩ :=
    ft_local_strong_clock_on_FM_consecutive
    (Q := ftRootPoly c a) (B := B) (r := r) (M := M)
    (z := ftBranchZ a c r (n - 1)) (τ := ftTau a r (n - 1)) (ψ := ψ)
    (Φ := fun θ => ((M : ℝ) + 1) * θ - ψ θ)
    (dΦ := fun θ => ((M : ℝ) + 1) - (dW θ / W θ).im)
    (e := ftBranchErr c B a r (n - 1) lo' M)
    (de := deriv (ftBranchErr c B a r (n - 1) lo' M))
    (W := W) (dW := dW)
    (L := (M : ℝ) + 1) (κ := κ) (κ₂ := κ₂) (P := P)
    (Ce := ((M : ℝ) + 1) * C * σ ^ M)
    (fun _ => rfl) rfl hlohi.le hcos hδ hδ4 hmono hΦd
    (fun θ hθ => (hder M θ hθ).1) hΦpos (fun θ hθ => hderC M θ hθ) hCeb
    hebd hwlo hwhi hP (fun θ hθ => hτpos θ (harc (hsub hθ))) hWpos
    (fun θ _ => ftBranchErr_spec c B a r (n - 1) lo' M θ)
    hκ0 hκ₂0 hC0M hLκ hψd hκ htay (fun θ hθ => hvalC M θ hθ)
  exact ⟨θk, hk, θk1, hk1, hlt, hz1, hz2, hiso, hsimple, hzinj, hquant, hcons,
    hsp1, hsp2⟩

/-- **The closed statement's hypothesis set is inhabited, and its body is
entered.**  At `B = 1` the amplitude divisor is empty, so a subarc strictly
inside a divisor-free interval is free to be anything compact; `n = 3`, `r = 1`
is the smallest admissible pair at `r = 1`.

**It projects the `u_0`-existence clause rather than discarding it.**  An earlier
version destructured with a `-` at `M₀` and everything beneath, so it certified
that `κ, κ_2, C, σ` exist and said nothing about whether the `∀ u_0` body is ever
reached — and the body is genuinely empty at small `M`, since `Φ_M` has not
turned far enough for the admissible window to be nonempty.  A witness against an
unreachable body certifies nothing, which is the same `-`-discard trap the
statements themselves have carried twice. -/
theorem ft_local_strong_clock_at_branch_closed_applies :
    ∃ (κ κ₂ C σ : ℝ) (M₀ : ℕ), 0 ≤ κ ∧ 0 ≤ κ₂ ∧ 0 ≤ C ∧ 0 < σ ∧ σ < 1 ∧
      ∀ M : ℕ, M₀ ≤ M → ∃ u₀ : ℝ, Real.cos u₀ = 0 ∧
        ((M : ℝ) + 1) * (6 / 5)
            - ftBranchPhase (ftRootPoly 1 ![1, 1, 1]) 1 ![1, 1, 1] 1 2 1 (6 / 5)
          ≤ u₀ - π / 4 ∧
        u₀ + π + π / 4 ≤ ((M : ℝ) + 1) * (9 / 5)
            - ftBranchPhase (ftRootPoly 1 ![1, 1, 1]) 1 ![1, 1, 1] 1 2 1 (9 / 5) := by
  have h3 : (3 : ℝ) < π := Real.pi_gt_three
  have harc : Icc (1 : ℝ) 2 ⊆ Ioo 0 (π / ((1 : ℕ) : ℝ)) := by
    intro θ hθ
    exact ⟨by linarith [hθ.1], by rw [pi_div_natCast_one]; linarith [hθ.2]⟩
  obtain ⟨κ, hκ, κ₂, hκ₂, C, hC, σ, hσ0, hσ1, M₀, hbody⟩ :=
    exists_ft_local_strong_clock_at_branch_closed (n := 3) (a := ![1, 1, 1]) (c := 1)
      (B := 1) (lo' := 1) (hi' := 2) (lo := 6 / 5) (hi := 9 / 5) (δ := π / 4)
      (by norm_num) (fun k => by fin_cases k <;> norm_num) one_pos le_rfl
      (Or.inl (by norm_num)) hasRealCoeffs_one one_ne_zero harc (fun θ _ => by simp)
      (by norm_num) (by norm_num) (by norm_num) (by positivity) le_rfl
  exact ⟨κ, κ₂, C, σ, M₀, hκ, hκ₂, hC, hσ0, hσ1, fun M hM => (hbody M hM).1⟩

end ForgacsTran
