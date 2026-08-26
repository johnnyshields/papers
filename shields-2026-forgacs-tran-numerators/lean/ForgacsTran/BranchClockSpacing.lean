/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.BranchAmplitude
import ForgacsTran.CubicPhaseSign
import ForgacsTran.InteriorSupply

/-!
# `prop:local-strong-clock` at the general admissible pencil

`CubicClockSpacing.cubic_local_strong_clock` discharges every branch-side binder
of `ConsequencesComposition.ClockSpacing.ft_local_strong_clock_on_FM` at one
pencil, by writing `τ` in closed form.  This module does the same at **every**
admissible pencil, on a compact subarc of `(0, π/r)` disjoint from
`InteriorSupply.ftAmplitudeDivisor`.

What replaces the closed form is `BranchAmplitude`: `eq:Dprime-identity` makes
`W` a fixed `z`-free rational function of the branch point, `BranchCurvature`
puts the branch point in `C²`, and compactness turns the resulting continuous
`ψ'` and `ψ''` into `κ` and `κ_2`.

## Main statements

* `exists_ft_branch_clock_data` — the five constants `prop:local-strong-clock`
  runs on, `κ`, `κ_2`, `C_I`, `A` and `σ`, at the general pencil, with one phase
  `ψ` serving both the derivative bounds and the decomposition.
* `exists_ft_local_strong_clock_at_branch` — `eq:local-strong-clock` for the
  zeros of `F_M` at the general pencil, with `κ` and the phase produced and every
  branch-side binder discharged.
* `ft_local_strong_clock_at_branch_applies`,
  `ft_branch_clock_data_applies` — the hypothesis sets, met at a real pencil.

## Implementation notes

**What is still a binder, and why.**  The `C^1` half of the remainder:
`e_M` differentiable with `|e_M'|` bounded below the turning of `Φ_M`.
`CubicInteriorRemainder` produces it at the witness pencil out of
`PoleExpansion.hasDerivAt_ftContourRem_comp`, and there is no general producer
in this tree.  The `C^0` half is **not** a binder — `exists_ft_branch_clock_data`
discharges it, over `InteriorSupply.exists_interior_data_on_subinterval_pi` and
`..._two_le` — but `exists_ft_local_strong_clock_at_branch` still takes the
decomposition as a hypothesis, because the `C^0` and `C^1` halves have to arrive
with the *same* error function and only one of them has a producer.

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Local phase
quantization and strong-clock spacing» (`subsec:strong-clock`,
`prop:local-strong-clock`, `eq:local-strong-clock`,
`eq:phase-derivative-bound`).

## Tags

strong clock, zero spacing, branch regularity, admissible pencil
-/

namespace ForgacsTran

open Real Set

/-- **`eq:local-strong-clock` at the general admissible pencil.**  Two
consecutive zeros of `F_M` in `z(𝒥)`, ordered, with the spacing law between
their angles — for every `Q` of the admissible class and every `r ≥ 1`, on a
compact subarc on which the reduced numerator does not vanish along the branch.

Everything on the branch side is produced rather than assumed:

* `κ` is `eq:phase-derivative-bound`, by compactness on `Im(W'/W)`, which
  `BranchAmplitude.hasDerivAt_ftBranchAmp` makes continuous;
* `ψ` is `ftBranchPhase`, the lift of `arg W` along the arc, and it is the same
  `ψ` the returned polar identity names, so the decomposition hypothesis can be
  built against it;
* `κ_2` is `eq:local-strong-clock`'s second-order constant, by compactness on
  `Im(W''/W - (W'/W)^2)` — the step that needs `γ''` to be *continuous*, which is
  `BranchAmplitude.continuousAt_ftGammaDeriv2`;
* `Φ_M` is strictly increasing because `Φ_M' = M + 1 - ψ' ≥ 1`;
* `hPmap`, `hτ` and `hW` come from the reality of the pencil, `ftTau_pos` and
  `ftBranchAmp_ne_zero`.

The remainder alone is left; see the module docstring.

**`κ` is hoisted out of the `M`-quantifier deliberately.**  It is a constant of
the pencil and the subarc, and the `C^1` remainder hypothesis is stated against
it, so a version producing `κ` after `M` would let the two disagree. -/
theorem exists_ft_local_strong_clock_at_branch {n r : ℕ} {a : Fin n → ℝ} {c : ℝ}
    {B : Polynomial ℂ} (hn : 0 < n) (ha : ∀ k, 0 < a k) (hc : c ≠ 0) (hr : 1 ≤ r)
    (hnr : 2 ≤ n ∨ 2 ≤ r) (hBr : HasRealCoeffs B) {lo hi : ℝ} (hlohi : lo ≤ hi)
    (harc : Icc lo hi ⊆ Ioo 0 (π / r))
    (hBne : ∀ θ ∈ Icc lo hi, B.eval (ftPrincipal (ftTau a r (n - 1)) θ) ≠ 0) :
    ∃ κ ≥ (0 : ℝ), ∃ κ₂ ≥ (0 : ℝ), ∃ ψ : ℝ → ℝ,
      (∀ θ ∈ Icc lo hi,
        ftAmp (ftRootPoly c a) B r ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ)
            (ftPrincipal (ftTau a r (n - 1)) θ)
          = ((ftPrincipalAmp (ftRootPoly c a) B r (ftBranchZ a c r (n - 1))
                (ftTau a r (n - 1)) θ : ℝ) : ℂ)
            * Complex.exp ((ψ θ : ℂ) * Complex.I)) ∧
      ∀ (M : ℕ) (u₀ δ C Ce : ℝ) (e de : ℝ → ℝ),
        Real.cos u₀ = 0 → 0 < δ → δ ≤ π / 4 → κ + 1 ≤ (M : ℝ) + 1 →
        ((M : ℝ) + 1) * lo - ψ lo ≤ u₀ - δ →
        u₀ + π + δ ≤ ((M : ℝ) + 1) * hi - ψ hi →
        (∀ θ ∈ Icc lo hi,
          ((((ftTau a r (n - 1) θ : ℝ) : ℂ)) ^ (M + 1)
                * (ftCoeffPoly (ftRootPoly c a) B r M).eval
                    ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ)).re
              / (2 * ftPrincipalAmp (ftRootPoly c a) B r (ftBranchZ a c r (n - 1))
                  (ftTau a r (n - 1)) θ)
            = Real.cos (((M : ℝ) + 1) * θ - ψ θ) + e θ) →
        (∀ θ ∈ Icc lo hi, |e θ| < Real.sin δ) →
        0 ≤ C → (∀ θ ∈ Icc lo hi, |e θ| ≤ C) →
        (∀ θ ∈ Icc lo hi, HasDerivAt e (de θ) θ) →
        (∀ θ ∈ Icc lo hi, |de θ| ≤ Ce) →
        Ce < Real.sqrt 2 / 2 * (((M : ℝ) + 1) - κ) →
        ∃ θk ∈ Icc lo hi, ∃ θk1 ∈ Icc lo hi, θk < θk1 ∧
          (ftCoeffPoly (ftRootPoly c a) B r M).eval
              ((ftBranchZ a c r (n - 1) θk : ℝ) : ℂ) = 0 ∧
          (ftCoeffPoly (ftRootPoly c a) B r M).eval
              ((ftBranchZ a c r (n - 1) θk1 : ℝ) : ℂ) = 0 ∧
          (∀ θ ∈ Icc lo hi, θk < θ → θ < θk1 →
            (ftCoeffPoly (ftRootPoly c a) B r M).eval
              ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ) ≠ 0) ∧
          θk1 - θk ≤ (π + 2 * (π / 2 * C)) / (((M : ℝ) + 1) - κ) ∧
            |(θk1 - θk) - π / ((M : ℝ) + 1)
                - π * (ftBranchAmpDeriv (ftRootPoly c a) B a r (n - 1) θk
                    / ftBranchAmp (ftRootPoly c a) B a r (n - 1) θk).im
                  / ((M : ℝ) + 1) ^ 2|
              ≤ (2 * (π / 2 * C)
                    + κ₂ * ((π + 2 * (π / 2 * C)) / (((M : ℝ) + 1) - κ)) ^ 2)
                  / (((M : ℝ) + 1) - κ)
                + π * κ ^ 2 / (((M : ℝ) + 1) ^ 2 * (((M : ℝ) + 1) - κ)) := by
  classical
  obtain ⟨-, hτpos⟩ := ft_branch_root_and_pos (a := a) (r := r) c hn ha hr hnr
  obtain ⟨κ, hκ0, hκ⟩ := exists_ftBranch_phase_deriv_bound (B := B) hn ha hc hr hnr harc hBne
  obtain ⟨κ₂, hκ₂0, htay⟩ :=
    exists_ftBranch_taylor_bound (B := B) hn ha hc hr hnr harc hBne
  refine ⟨κ, hκ0, κ₂, hκ₂0, ftBranchPhase (ftRootPoly c a) B a r (n - 1) lo, ?_, ?_⟩
  · -- `W = ‖W‖e^{iψ}` with the constructed phase
    intro θ hθ
    have hpolar := ftBranchAmp_eq_polar (B := B) hn ha hc hr hnr hlohi harc hBne hθ
    have hval := ftBranchAmp_eq_ftAmp (B := B) (c := c) hn ha hr hnr (harc hθ)
    rw [hval] at hpolar
    rw [hpolar]
    rfl
  intro M u₀ δ C Ce e de hcos hδ hδ4 hLκ hlo hhi hdec heb hCnn hCeb hed hdeb hCe
  set W := ftBranchAmp (ftRootPoly c a) B a r (n - 1) with hWdef
  set dW := ftBranchAmpDeriv (ftRootPoly c a) B a r (n - 1) with hdWdef
  set ψ := ftBranchPhase (ftRootPoly c a) B a r (n - 1) lo with hψdef
  have hne : ∀ θ ∈ Icc lo hi, W θ ≠ 0 :=
    fun θ hθ => ftBranchAmp_ne_zero hn ha hc hr hnr (harc hθ) (hBne θ hθ)
  have hψd : ∀ θ ∈ Icc lo hi, HasDerivAt ψ ((dW θ / W θ).im) θ :=
    fun θ hθ => hasDerivAt_ftBranchPhase hn ha hc hr hnr harc hBne hθ
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
  have hWpos : ∀ θ ∈ Icc lo hi,
      0 < ftPrincipalAmp (ftRootPoly c a) B r (ftBranchZ a c r (n - 1))
        (ftTau a r (n - 1)) θ := by
    intro θ hθ
    have hval := ftBranchAmp_eq_ftAmp (B := B) (c := c) hn ha hr hnr (harc hθ)
    have : ftPrincipalAmp (ftRootPoly c a) B r (ftBranchZ a c r (n - 1))
        (ftTau a r (n - 1)) θ = ‖W θ‖ := by rw [ftPrincipalAmp, ← hval]
    rw [this]
    exact norm_pos_iff.2 (hne θ hθ)
  exact ft_local_strong_clock_on_FM_consecutive
    (Q := ftRootPoly c a) (B := B) (r := r) (M := M)
    (z := ftBranchZ a c r (n - 1)) (τ := ftTau a r (n - 1)) (ψ := ψ)
    (Φ := fun θ => ((M : ℝ) + 1) * θ - ψ θ)
    (dΦ := fun θ => ((M : ℝ) + 1) - (dW θ / W θ).im)
    (e := e) (de := de) (W := W) (dW := dW)
    (L := (M : ℝ) + 1) (κ := κ) (κ₂ := κ₂) (P := P)
    (fun _ => rfl) rfl hlohi hcos hδ hδ4 hmono hΦd hed hΦpos hdeb
    (fun θ hθ => by
      have := abs_le.1 (hκ θ hθ)
      have h2 : (0 : ℝ) < Real.sqrt 2 / 2 := by positivity
      nlinarith [hCe])
    heb hlo hhi hP (fun θ hθ => hτpos θ (harc hθ)) hWpos hdec
    hκ0 hκ₂0 hCnn hLκ hψd (fun θ hθ => hκ θ hθ) htay hCeb



/-! ### `κ`, `κ_2`, `C_I`, `A` and `σ` together, at the general admissible pencil

The branch side and the `C^0` remainder side of `prop:local-strong-clock`, produced in
one statement so that the same `ψ` serves both — which is the point of carrying the
differentiable `ftBranchPhase` rather than `exists_polar_phase`'s `arg`.

`InteriorSupply.exists_interior_data_on_subinterval_pi` and `..._two_le` already give
`C_I` and `σ` at this generality, with the class split the paper itself makes: `r = 1`
needs `3 ≤ n`, which is `thm:FT-geometry`'s exclusion of `(deg Q, r) = (2,1)`, and
`r ≥ 2` needs only `2 ≤ n`.  `A` is the amplitude floor by compactness, which is what a
divisor-free subarc has and `eq:amplitude-deletion` is not needed for. -/

/-- **The five constants of `prop:local-strong-clock`, at the general admissible
pencil.**  On a compact subarc of `(0, π/r)` on which `B` does not vanish along the
branch:

* `κ` bounds `ψ' = Im(W'/W)` — `eq:phase-derivative-bound`;
* `κ_2` bounds `ψ'' = Im(W''/W - (W'/W)^2)` — the `O(M^{-3})` term's constant;
* `C_I` and `σ` bound the remainder geometrically — `eq:principal-decomposition`;
* `A` is the amplitude floor, and `C_I/(2A)` is the error constant the quantization
  runs in.

`ψ` is one function serving both halves: it differentiates to `Im(W'/W)` **and** is the
phase of the decomposition.  Producing them separately would give two branches of
`arg W` differing by a multiple of `2π`, and the composition would not close.

What is **not** here is the `C^1` half of the remainder — `e_M` differentiable with
`|e_M'|` bounded.  `CubicInteriorRemainder` produces it at the witness pencil out of
`PoleExpansion.hasDerivAt_ftContourRem_comp`; there is no general producer in this tree,
and it is the one input `exists_ft_local_strong_clock_at_branch` still takes on trust. -/
theorem exists_ft_branch_clock_data {n r : ℕ} {a : Fin n → ℝ} {c : ℝ} {B : Polynomial ℂ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r)
    (hcls : 3 ≤ n ∨ 2 ≤ r) (hBr : HasRealCoeffs B) (hB0 : B ≠ 0)
    {lo hi : ℝ} (hlohi : lo ≤ hi) (harc : Icc lo hi ⊆ Ioo 0 (π / r))
    (hBne : ∀ θ ∈ Icc lo hi, B.eval (ftPrincipal (ftTau a r (n - 1)) θ) ≠ 0) :
    ∃ (κ κ₂ CI A σ : ℝ) (ψ : ℝ → ℝ) (e : ℕ → ℝ → ℝ),
      0 ≤ κ ∧ 0 ≤ κ₂ ∧ 0 ≤ CI ∧ 0 < A ∧ 0 < σ ∧ σ < 1 ∧
      (∀ θ ∈ Icc lo hi,
        |(ftBranchAmpDeriv (ftRootPoly c a) B a r (n - 1) θ
          / ftBranchAmp (ftRootPoly c a) B a r (n - 1) θ).im| ≤ κ) ∧
      (∀ θ ∈ Icc lo hi,
        |(ftBranchAmpDeriv2 (ftRootPoly c a) B a r (n - 1) θ
              / ftBranchAmp (ftRootPoly c a) B a r (n - 1) θ
            - (ftBranchAmpDeriv (ftRootPoly c a) B a r (n - 1) θ
              / ftBranchAmp (ftRootPoly c a) B a r (n - 1) θ) ^ 2).im| ≤ κ₂) ∧
      (∀ θ ∈ Icc lo hi, HasDerivAt ψ
        ((ftBranchAmpDeriv (ftRootPoly c a) B a r (n - 1) θ
          / ftBranchAmp (ftRootPoly c a) B a r (n - 1) θ).im) θ) ∧
      (∀ (M : ℕ), ∀ θ ∈ Icc lo hi,
        ((((ftTau a r (n - 1) θ : ℝ) : ℂ)) ^ (M + 1)
              * (ftCoeffPoly (ftRootPoly c a) B r M).eval
                  ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ)).re
            / (2 * ftPrincipalAmp (ftRootPoly c a) B r (ftBranchZ a c r (n - 1))
                (ftTau a r (n - 1)) θ)
          = Real.cos (((M : ℝ) + 1) * θ - ψ θ) + e M θ) ∧
      (∀ (M : ℕ), ∀ θ ∈ Icc lo hi, |e M θ| ≤ CI / (2 * A) * σ ^ M) := by
  classical
  have hn : 0 < n := by omega
  have hnr : 2 ≤ n ∨ 2 ≤ r := Or.inl hn2
  have hc0 : c ≠ 0 := hc.ne'
  obtain ⟨-, hτpos⟩ := ft_branch_root_and_pos (a := a) (r := r) c hn ha hr hnr
  -- the branch side
  obtain ⟨κ, hκ0, hκ⟩ := exists_ftBranch_phase_deriv_bound (B := B) hn ha hc0 hr hnr harc hBne
  obtain ⟨κ₂, hκ₂0, hκ₂⟩ :=
    exists_ftBranch_phase_curvature_bound (B := B) hn ha hc0 hr hnr harc hBne
  -- the remainder side: `C_I` and `σ`, from the interior supply at this generality
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
  -- the amplitude floor, by compactness on a divisor-free subarc
  have hWc : ContinuousOn (fun θ => ftAmp (ftRootPoly c a) B r
      ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ) (ftPrincipal (ftTau a r (n - 1)) θ))
      (Icc lo hi) := by
    refine ContinuousOn.congr (continuousOn_ftBranchAmp (B := B) hn ha hc0 hr hnr harc) ?_
    exact fun θ hθ => (ftBranchAmp_eq_ftAmp (B := B) (c := c) hn ha hr hnr (harc hθ)).symm
  have hWne : ∀ θ ∈ Icc lo hi, ftAmp (ftRootPoly c a) B r
      ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ) (ftPrincipal (ftTau a r (n - 1)) θ) ≠ 0 := by
    intro θ hθ
    rw [← ftBranchAmp_eq_ftAmp (B := B) (c := c) hn ha hr hnr (harc hθ)]
    exact ftBranchAmp_ne_zero hn ha hc0 hr hnr (harc hθ) (hBne θ hθ)
  obtain ⟨A, hA, hfloor⟩ := exists_amplitude_floor_on_subarc hWc hWne
  -- `C_I` is nonnegative wherever the subarc is inhabited; take the max regardless
  refine ⟨κ, κ₂, max CI 0, A, σ, ftBranchPhase (ftRootPoly c a) B a r (n - 1) lo,
    fun M θ => ((((ftTau a r (n - 1) θ : ℝ) : ℂ)) ^ (M + 1)
          * (ftCoeffPoly (ftRootPoly c a) B r M).eval
              ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ)).re
        / (2 * ftPrincipalAmp (ftRootPoly c a) B r (ftBranchZ a c r (n - 1))
            (ftTau a r (n - 1)) θ)
      - Real.cos (((M : ℝ) + 1) * θ - ftBranchPhase (ftRootPoly c a) B a r (n - 1) lo θ),
    hκ0, hκ₂0, le_max_right _ _, hA, hσ0, hσ1, hκ, hκ₂,
    fun θ hθ => hasDerivAt_ftBranchPhase hn ha hc0 hr hnr harc hBne hθ,
    fun M θ _ => by ring, fun M θ hθ => ?_⟩
  obtain ⟨e, heq, hbd⟩ := interior_cos_error_geometric (M := M)
    (ψ := ftBranchPhase (ftRootPoly c a) B a r (n - 1) lo)
    (hτpos θ (harc hθ)) hA hσ0.le (hfloor θ hθ)
    (le_trans (hrem M θ hθ)
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hσ0.le M)))
    (ftAmp_eq_polar_at_branch hn ha hc0 hr hnr hlohi harc hBne hθ)
  have hE : ((((ftTau a r (n - 1) θ : ℝ) : ℂ)) ^ (M + 1)
        * (ftCoeffPoly (ftRootPoly c a) B r M).eval
            ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ)).re
      / (2 * ftPrincipalAmp (ftRootPoly c a) B r (ftBranchZ a c r (n - 1))
          (ftTau a r (n - 1)) θ)
      - Real.cos (((M : ℝ) + 1) * θ
          - ftBranchPhase (ftRootPoly c a) B a r (n - 1) lo θ) = e := by
    rw [heq]; ring
  dsimp only
  rw [hE]
  exact hbd

/-! ### The hypothesis set is inhabited

`lake build` cannot tell whether a hypothesis is satisfiable, and the theorem above
carries nine of them.  The instance below meets every one at a concrete pencil, with
the numerator taken constant so that the amplitude divisor is empty and the subarc is
free to be anything compact inside the arc.

**Instantiated at the boundary of each ℕ parameter**: `r = 1`, `deg B = 0`, and
`n = 3`, which is the smallest degree admitting `r = 1` (`not_ftBranchAt_one_one`
refutes `n = r = 1`, and `thm:FT-geometry` excludes `(2,1)`).

A **degenerate** subarc `lo = hi` is legal and makes the `M`-body vacuous, correctly:
`hlo` and `hhi` then read `Φ(lo) ≤ u_0 - δ` and `u_0 + π + δ ≤ Φ(lo)`, which
contradict each other.  Two consecutive zeros do not fit in a point. -/

theorem hasRealCoeffs_one : HasRealCoeffs (1 : Polynomial ℂ) := fun k => by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · rw [Polynomial.coeff_one, if_neg (Nat.ne_of_gt hk), map_zero]

/-- **`exists_ft_local_strong_clock_at_branch` applies at a real pencil.**  The polar
identity is its first conjunct; obtaining it discharges the whole hypothesis list, so
this is the non-vacuity witness rather than a new statement. -/
theorem ft_local_strong_clock_at_branch_applies :
    ∃ κ ≥ (0 : ℝ), ∃ ψ : ℝ → ℝ, ∀ θ ∈ Icc (1 : ℝ) 2,
      ftAmp (ftRootPoly 1 ![1, 1, 1]) 1 1
          ((ftBranchZ ![1, 1, 1] 1 1 2 θ : ℝ) : ℂ)
          (ftPrincipal (ftTau ![1, 1, 1] 1 2) θ)
        = ((ftPrincipalAmp (ftRootPoly 1 ![1, 1, 1]) 1 1
              (ftBranchZ ![1, 1, 1] 1 1 2) (ftTau ![1, 1, 1] 1 2) θ : ℝ) : ℂ)
          * Complex.exp ((ψ θ : ℂ) * Complex.I) := by
  have harc : Icc (1 : ℝ) 2 ⊆ Ioo 0 (π / ((1 : ℕ) : ℝ)) := by
    intro θ hθ
    have h3 : (3 : ℝ) < π := Real.pi_gt_three
    exact ⟨by linarith [hθ.1], by push_cast; rw [div_one]; linarith [hθ.2]⟩
  obtain ⟨κ, hκ0, κ₂, hκ₂0, ψ, hpolar, -⟩ :=
    exists_ft_local_strong_clock_at_branch (n := 3) (a := ![1, 1, 1]) (c := 1)
      (B := 1) (by norm_num) (fun k => by fin_cases k <;> norm_num) one_ne_zero
      le_rfl (Or.inl (by norm_num)) hasRealCoeffs_one (by norm_num) harc
      (fun θ _ => by simp)
  exact ⟨κ, hκ0, ψ, hpolar⟩

/-- **`exists_ft_branch_clock_data` applies at the same pencil.**  Its five constants
exist there, so the wider hypothesis list — the interior supply's class split and
`B ≠ 0` on top of the branch side — is met too. -/
theorem ft_branch_clock_data_applies :
    ∃ κ κ₂ CI A σ : ℝ, 0 ≤ κ ∧ 0 ≤ κ₂ ∧ 0 ≤ CI ∧ 0 < A ∧ 0 < σ ∧ σ < 1 := by
  have harc : Icc (1 : ℝ) 2 ⊆ Ioo 0 (π / ((1 : ℕ) : ℝ)) := by
    intro θ hθ
    have h3 : (3 : ℝ) < π := Real.pi_gt_three
    exact ⟨by linarith [hθ.1], by push_cast; rw [div_one]; linarith [hθ.2]⟩
  obtain ⟨κ, κ₂, CI, A, σ, -, -, hκ, hκ₂, hCI, hA, hσ0, hσ1, -⟩ :=
    exists_ft_branch_clock_data (n := 3) (a := ![1, 1, 1]) (c := 1) (B := 1)
      (by norm_num) (fun k => by fin_cases k <;> norm_num) one_pos le_rfl
      (Or.inl (by norm_num)) hasRealCoeffs_one one_ne_zero (by norm_num) harc
      (fun θ _ => by simp)
  exact ⟨κ, κ₂, CI, A, σ, hκ, hκ₂, hCI, hA, hσ0, hσ1⟩

end ForgacsTran
