/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.WeightedDominanceBranch
import ForgacsTran.RhoOneDominanceComposition

/-!
# The dominance band shrinks for free

`WeightedDominanceBranch.ft_weighted_dominance` produces its own `ε`, while
`PhaseSupplyProducer.exists_ftPhaseSupply_of_dominance` takes one as a
parameter and constrains it through `hband` — every amplitude zero of the arc
inside `[ε, π/r - ε]`.  Composing the two therefore needs one `ε` meeting two
constraints that pull in opposite directions: `hband` wants it small enough to
catch every zero, and the dominance interior data is stated on the band, which
wants it large.

The two are compatible, and the reason is that **`ε` occurs in
`ft_weighted_dominance` only inside the antecedent**, in the two clauses
`ε ≤ θ → θ ≤ π/r - ε`.  The conclusion does not mention it.  So a smaller `ε`
supplies a *larger* band of interior data, which restricts to the original one,
and the implication carries over unchanged:

`ε' ≤ ε` gives `[ε, π/r - ε] ⊆ [ε', π/r - ε']`, hence
`data at ε' → data at ε → conclusion`.

The consequence for the composition is that `ε` may be taken as small as
`hband` requires without renegotiating anything on the dominance side, so the
seam is not a constraint conflict — it is a restriction, and it costs nothing.

**The predicate carries the spectral parameter.**  The corners do not all run at
one: the `ρ ≥ 2` cells use `ftBranchZLower` and the `ρ = 1` cells
`ftBranchZLowerAt a c r l aEnd` at the endpoint their geometry produces, and
`ftBranchZLower a c r l = ftBranchZLowerAt a c r l 0` definitionally.  So
`ftInteriorData` takes `z`, and one antitonicity proof serves every cell rather
than one per spelling.

## Main statements

* `ftInteriorData` — the antecedent of the corner theorems, named and carrying
  its own `z`, so that the restriction is stated once rather than transcribed per
  corner.
* `ftInteriorData_antitone` — the restriction: data on a wider band gives data
  on a narrower one, at the same witnesses.
* `ft_weighted_dominance_band_antitone` — the dominance conclusion transported
  from the produced `ε` down to any smaller positive one.
* `ft_weighted_dominance_at_any_band`,
  `ft_weighted_dominance_rho_one_two_le_at_any_band` — the two `2 ≤ r` corners
  restated so the caller picks the band.

Sorry-free.

## References

Formalizes `shields-2026-forgacs-tran-numerators.tex`, «Angular discrepancy and
proof of the main theorem» (`subsec:proof`, `eq:retained-range`), and
`thm:weighted-dominance`.
-/

namespace ForgacsTran

open Polynomial Complex
open scoped Topology

variable {n r : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ}

/-- The antecedent of `WeightedDominanceBranch.ft_weighted_dominance`, at the
branch, named so the band can be moved without transcribing the clause list.

`Θ` is the deleted window family and `ε` the half-width of the band the
interior data is stated on. -/
def ftInteriorData (c : ℝ) (a : Fin n → ℝ) (r : ℕ) (x₁ : ℝ) (z : ℝ → ℝ)
    (B : Polynomial ℂ) (ε : ℝ) (Θ : ℕ → Set ℝ) : Prop :=
  ∃ (CI σI AI : ℝ) (Sd : Finset ℝ) (νd : ℝ → ℕ),
    0 < σI ∧ σI < 1 ∧ 0 < AI ∧ (∀ θj ∈ Sd, 1 ≤ νd θj) ∧
    (∀ (M : ℕ) (θ : ℝ), ε ≤ θ → θ ≤ Real.pi / r - ε →
      |ftRemainder (ftRootPoly c a) B r z (ftTauArc a r (n - 1) x₁) M θ|
        ≤ CI * σI ^ M) ∧
    (∀ θ : ℝ, ε ≤ θ → θ ≤ Real.pi / r - ε →
      AI * ∏ θj ∈ Sd, |θ - θj| ^ νd θj
        ≤ ftPrincipalAmp (ftRootPoly c a) B r z (ftTauArc a r (n - 1) x₁) θ) ∧
    (∀ (M : ℕ) (θ : ℝ), θ ∉ Θ M → ∀ θj ∈ Sd,
      Real.exp (-((-Real.log σI) / (2 * Sd.card) * M / νd θj)) ≤ |θ - θj|)

/-- **Interior data restricts to a narrower band.**  The witnesses are
unchanged; only the two band clauses are weakened, and each is weakened by
`[ε, π/r - ε] ⊆ [ε', π/r - ε']` for `ε' ≤ ε`.

This is what makes the `ε` seam of the composition free: the dominance side
never has to be re-derived at a smaller `ε`. -/
theorem ftInteriorData_antitone {z : ℝ → ℝ} {B : Polynomial ℂ} {ε ε' : ℝ}
    {Θ : ℕ → Set ℝ}
    (hle : ε' ≤ ε) (hdata : ftInteriorData c a r x₁ z B ε' Θ) :
    ftInteriorData c a r x₁ z B ε Θ := by
  obtain ⟨CI, σI, AI, Sd, νd, h1, h2, h3, h4, hrem, hamp, hwin⟩ := hdata
  refine ⟨CI, σI, AI, Sd, νd, h1, h2, h3, h4, ?_, ?_, hwin⟩
  · exact fun M θ hlo hhi => hrem M θ (le_trans hle hlo) (by linarith)
  · exact fun θ hlo hhi => hamp θ (le_trans hle hlo) (by linarith)

/-- **`thm:weighted-dominance` with the band shrunk.**  The dominance
conclusion holds against interior data on any wider band, so the `ε` the
composition needs may be dictated entirely by `hband`.

The hypothesis is the conclusion of `WeightedDominanceBranch.ft_weighted_dominance`
after its two existentials are opened, stated through `ftInteriorData`. -/
theorem ft_weighted_dominance_band_antitone {z : ℝ → ℝ} {B : Polynomial ℂ}
    {h ε ε' : ℝ}
    (hle : ε' ≤ ε)
    (hconc : ∀ Θ : ℕ → Set ℝ, ftInteriorData c a r x₁ z B ε Θ →
      ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ θ : ℝ,
        h / M ≤ θ → θ ≤ Real.pi / r - h / M → θ ∉ Θ M →
          ftRemainder (ftRootPoly c a) B r (ftBranchZLower a c r (n - 1))
              (ftTauArc a r (n - 1) x₁) M θ
            ≤ ftPrincipalAmp (ftRootPoly c a) B r (ftBranchZLower a c r (n - 1))
              (ftTauArc a r (n - 1) x₁) θ / 2) :
    ∀ Θ : ℕ → Set ℝ, ftInteriorData c a r x₁ z B ε' Θ →
      ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ θ : ℝ,
        h / M ≤ θ → θ ≤ Real.pi / r - h / M → θ ∉ Θ M →
          ftRemainder (ftRootPoly c a) B r (ftBranchZLower a c r (n - 1))
              (ftTauArc a r (n - 1) x₁) M θ
            ≤ ftPrincipalAmp (ftRootPoly c a) B r (ftBranchZLower a c r (n - 1))
              (ftTauArc a r (n - 1) x₁) θ / 2 :=
  fun Θ hdata => hconc Θ (ftInteriorData_antitone hle hdata)

/-- **`ft_weighted_dominance` restated through `ftInteriorData`, at any band.**

Two things are checked here rather than assumed.  That the `def` above really is
the inline antecedent `WeightedDominanceBranch.ft_weighted_dominance` states --
the two are spellings of one predicate, and a seam where they are merely
believed equal is where a later `exact` fails three lemmas downstream.  And that
the produced `ε` may be replaced by **any** smaller positive one, which is what
lets `PhaseSupplyProducer.exists_ftPhaseSupply_of_dominance` fix `ε` from
`hband` alone. -/
theorem ft_weighted_dominance_at_any_band {ρ : ℕ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 2 ≤ r)
    (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ) :
    ∃ h > (0 : ℝ), ∀ (B : Polynomial ℂ), HasRealCoeffs B → B.eval 0 ≠ 0 →
      ∃ ε > (0 : ℝ), ∀ ε' : ℝ, 0 < ε' → ε' ≤ ε → ∀ Θ : ℕ → Set ℝ,
        ftInteriorData c a r x₁ (ftBranchZLower a c r (n - 1)) B ε' Θ →
        ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ θ : ℝ,
          h / M ≤ θ → θ ≤ Real.pi / r - h / M → θ ∉ Θ M →
            ftRemainder (ftRootPoly c a) B r (ftBranchZLower a c r (n - 1))
                (ftTauArc a r (n - 1) x₁) M θ
              ≤ ftPrincipalAmp (ftRootPoly c a) B r (ftBranchZLower a c r (n - 1))
                (ftTauArc a r (n - 1) x₁) θ / 2 := by
  obtain ⟨h, hh, hmain⟩ := ft_weighted_dominance hn2 ha hc hr hx₁ hmin hcard hρ
  refine ⟨h, hh, fun B hBr hB0 => ?_⟩
  obtain ⟨ε, hε, hεmain⟩ := hmain B hBr hB0
  exact ⟨ε, hε, fun ε' _ hle Θ hdata => hεmain Θ (ftInteriorData_antitone hle hdata)⟩

/-- **The same at the `ρ = 1`, `2 ≤ r` corner.**  That corner runs at
`ftBranchZLowerAt` rather than `ftBranchZLower`, and at the endpoint `ta` its
geometry produces rather than at the smallest zero — which is exactly why
`ftInteriorData` carries the spectral parameter rather than hardcoding one.

Its numerator binders are the same two as the `ρ ≥ 2` corner's, so unlike the
`r = 1` cells it fits the phase supply's bundle without a third clause. -/
theorem ft_weighted_dominance_rho_one_two_le_at_any_band
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 2 ≤ r)
    {i : Fin n} (hmin : ∀ k, a i ≤ a k) (hsimple : ∀ k, k ≠ i → a k ≠ a i) :
    ∃ h > (0 : ℝ), ∃ ta > (0 : ℝ),
      ∀ B : Polynomial ℂ, HasRealCoeffs B → B.eval 0 ≠ 0 →
        ∃ ε > (0 : ℝ), ∀ ε' : ℝ, 0 < ε' → ε' ≤ ε → ∀ Θ : ℕ → Set ℝ,
          ftInteriorData c a r ta
              (ftBranchZLowerAt a c r (n - 1)
                (-((ftRootPolyReal c a).eval ta) / ta ^ r)) B ε' Θ →
          ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ θ : ℝ,
            h / M ≤ θ → θ ≤ Real.pi / r - h / M → θ ∉ Θ M →
              ftRemainder (ftRootPoly c a) B r
                  (ftBranchZLowerAt a c r (n - 1)
                    (-((ftRootPolyReal c a).eval ta) / ta ^ r))
                  (ftTauArc a r (n - 1) ta) M θ
                ≤ ftPrincipalAmp (ftRootPoly c a) B r
                  (ftBranchZLowerAt a c r (n - 1)
                    (-((ftRootPolyReal c a).eval ta) / ta ^ r))
                  (ftTauArc a r (n - 1) ta) θ / 2 := by
  obtain ⟨h, hh, ta, hta, hmain⟩ :=
    ft_weighted_dominance_rho_one_two_le hn2 ha hc hr hmin hsimple
  refine ⟨h, hh, ta, hta, fun B hBr hB0 => ?_⟩
  obtain ⟨ε, hε, hεmain⟩ := hmain B hBr hB0
  exact ⟨ε, hε, fun ε' _ hle Θ hdata => hεmain Θ (ftInteriorData_antitone hle hdata)⟩

/-! ### The two `r = 1` corners

These are stated by their own theorems at `π` rather than `π / r`, since `r` is
already substituted there.  `ftInteriorData` is at `π / r`, so feeding it needs
`π / (1 : ℕ) = π` as well as the band restriction — two conversions, not one. -/

/-- **`ft_weighted_dominance_one` with the band shrunk.**  `ρ ≥ 2`, `r = 1`. -/
theorem ft_weighted_dominance_one_at_any_band {ρ : ℕ}
    (hn3 : 3 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hx₁ : 0 < x₁)
    (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ) :
    ∃ h > (0 : ℝ), ∀ (B : Polynomial ℂ), HasRealCoeffs B → B.eval 0 ≠ 0 →
      ∃ ε > (0 : ℝ), ∀ ε' : ℝ, 0 < ε' → ε' ≤ ε → ∀ Θ : ℕ → Set ℝ,
        ftInteriorData c a 1 x₁ (ftBranchZLower a c 1 (n - 1)) B ε' Θ →
        ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ θ : ℝ,
          h / M ≤ θ → θ ≤ Real.pi - h / M → θ ∉ Θ M →
            ftRemainder (ftRootPoly c a) B 1 (ftBranchZLower a c 1 (n - 1))
                (ftTauArc a 1 (n - 1) x₁) M θ
              ≤ ftPrincipalAmp (ftRootPoly c a) B 1 (ftBranchZLower a c 1 (n - 1))
                (ftTauArc a 1 (n - 1) x₁) θ / 2 := by
  obtain ⟨h, hh, L, hL, hmain⟩ := ft_weighted_dominance_one hn3 ha hc hx₁ hmin hcard hρ
  refine ⟨h, hh, fun B hBr hB0 => ?_⟩
  obtain ⟨ε, hε, hεmain⟩ := hmain B hBr hB0
  refine ⟨ε, hε, fun ε' _ hle Θ hdata => hεmain Θ ?_⟩
  obtain ⟨CI, σI, AI, Sd, νd, h1, h2, h3, h4, hrem, hamp, hwin⟩ :=
    ftInteriorData_antitone hle hdata
  exact ⟨CI, σI, AI, Sd, νd, h1, h2, h3, h4,
    fun M θ hlo hhi => hrem M θ hlo (by simpa using hhi),
    fun θ hlo hhi => hamp θ hlo (by simpa using hhi), hwin⟩

/-- **`ft_weighted_dominance_rho_one` with the band shrunk.**  `ρ = 1`, `r = 1`;
its collar constant is the literal `1` rather than an existential. -/
theorem ft_weighted_dominance_rho_one_at_any_band
    (hn3 : 3 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c)
    {i : Fin n} (hmin : ∀ k, a i ≤ a k) (hsimple : ∀ k, k ≠ i → a k ≠ a i) :
    ∃ ta > (0 : ℝ),
      ∀ B : Polynomial ℂ, HasRealCoeffs B → B.eval 0 ≠ 0 →
        ∃ ε > (0 : ℝ), ∀ ε' : ℝ, 0 < ε' → ε' ≤ ε → ∀ Θ : ℕ → Set ℝ,
          ftInteriorData c a 1 ta
              (ftBranchZLowerAt a c 1 (n - 1)
                (-((ftRootPolyReal c a).eval ta) / ta ^ 1)) B ε' Θ →
          ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ θ : ℝ,
            1 / M ≤ θ → θ ≤ Real.pi - 1 / M → θ ∉ Θ M →
              ftRemainder (ftRootPoly c a) B 1
                  (ftBranchZLowerAt a c 1 (n - 1)
                    (-((ftRootPolyReal c a).eval ta) / ta ^ 1))
                  (ftTauArc a 1 (n - 1) ta) M θ
                ≤ ftPrincipalAmp (ftRootPoly c a) B 1
                  (ftBranchZLowerAt a c 1 (n - 1)
                    (-((ftRootPolyReal c a).eval ta) / ta ^ 1))
                  (ftTauArc a 1 (n - 1) ta) θ / 2 := by
  obtain ⟨ta, hta, L, hL, hmain⟩ := ft_weighted_dominance_rho_one hn3 ha hc hmin hsimple
  refine ⟨ta, hta, fun B hBr hB0 => ?_⟩
  obtain ⟨ε, hε, hεmain⟩ := hmain B hBr hB0
  refine ⟨ε, hε, fun ε' _ hle Θ hdata => hεmain Θ ?_⟩
  obtain ⟨CI, σI, AI, Sd, νd, h1, h2, h3, h4, hrem, hamp, hwin⟩ :=
    ftInteriorData_antitone hle hdata
  exact ⟨CI, σI, AI, Sd, νd, h1, h2, h3, h4,
    fun M θ hlo hhi => hrem M θ hlo (by simpa using hhi),
    fun θ hlo hhi => hamp θ hlo (by simpa using hhi), hwin⟩

end ForgacsTran
