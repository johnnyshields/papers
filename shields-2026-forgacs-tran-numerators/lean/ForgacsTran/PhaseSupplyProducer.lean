/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.AngularDiscrepancyFT
import ForgacsTran.InteriorSupply
import ForgacsTran.CubicPhaseSign
import ForgacsTran.QuadraticDefect

/-!
# `FTPhaseSupply` produced, down to two hypotheses

`AngularDiscrepancyFT.FTPhaseSupply` has twelve clauses.  Ten of them are
bookkeeping about the pencil that the tree already proves, and carrying them as
hypotheses only defers the question of whether they are meetable.  This module
produces those ten and leaves exactly two:

* `eq:dominance-bound` on the retained range — `thm:weighted-dominance`, and
* the branch supply of `lem:amplitude-divisor` and `cor:linear-phase-variation`.

What that buys is not brevity at the composition.  It is that **the shape of what
is still owed becomes checkable now**: the two hypotheses below are the two
statements, in the form their theorems conclude, and anything else that turns out
to be needed has to appear as a third.

## Main statements

* `ftWindowRadius` — the common half-width of `eq:amplitude-deletion`, at the
  largest multiplicity, so that the deleted family is nested-free (`AngularBlocks`).
* `exists_ftPhaseSupply_of_dominance` — the producer.
* `ftAngularDiscrepancy_of_dominance` — that composed onto
  `AngularDiscrepancyFT.ftAngularDiscrepancy_of_supply`, so
  `prop:angular-discrepancy` follows from the two hypotheses in one step.

## Implementation notes

**The divisor is taken once, on a fixed band, not per index.**  `eq:retained-range`
is `[h/M, π/r - h/M]`, which moves, so a divisor computed on it would move too and
`eq:amplitude-window-negligible` — which is about a *fixed* `S` — would not apply.
`subsec:proof` fixes `ε` first so that every amplitude zero lies in
`(ε, π/r - ε)`, and that is `hband` below.  With it, `S` is one `Finset` for all
`M` and every constant derived from it is `M`-free.

**`Ret` is produced, not assumed.**  It is `eq:retained-range` verbatim — the
collar minus the windows — so `hRet` is `fun _ _ _ h => h` and the clause carries
no content of its own.  The coordinator flagged this as the candidate for a
clause that could not be produced without the dominance bound; it is not one.

**`N` is `max (deg B) 1`.**  The multiplicities are bounded by `deg B` through
`eq:amplitude-zero-count`, and the `1` covers a constant weight, where the
divisor is empty and the bound is vacuous but `tendsto_deletedLength` still wants
a positive `N`.

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Angular discrepancy and
proof of the main theorem» (`subsec:proof`, `eq:Omega-M`, `eq:retained-range`,
`eq:amplitude-deletion`, `eq:amplitude-window-negligible`) over
«Spectral geometry, residues, and the principal amplitude» (`sec:geometry`,
`lem:amplitude-divisor`, `eq:amplitude-zero-count`) and «Canonical Laurent
reduction and eventual degree» (`sec:reduction`, `lem:eventual-degree`).

## Tags

phase supply, amplitude divisor, retained range, uniformity
-/

open Polynomial

namespace ForgacsTran

open Set Real

/-- **`eq:amplitude-deletion` at one common half-width.**  Every window is taken
at the largest multiplicity's radius, which contains all of them
(`AngularBookkeeping.windowRadius_le`) and leaves the family free of nesting —
without which the retained blocks of `AngularBlocks` have no ordered
decomposition. -/
noncomputable def ftWindowRadius (Q B : Polynomial ℂ) (r : ℕ) (z τ : ℝ → ℝ)
    (ε σ : ℝ) (M : ℕ) : ℝ :=
  windowRadius σ (ftAmplitudeDivisor Q B r z τ ε (π / r - ε))
    (fun _ => max B.natDegree 1) M 0

/-- **The window predicate implies membership outside the deleted family.**
`AngularBookkeeping.amplitudeWindows_spec` is the converse — outside the union,
every zero is at least its radius away.  This is the direction the composition
needs: `thm:weighted-dominance` concludes under `θ ∉ Θ M`, and
`exists_ftPhaseSupply_of_dominance` supplies the gap. -/
theorem notMem_amplitudeWindows_of_gap {σ : ℝ} {S : Finset ℝ} {ν : ℝ → ℕ} {M : ℕ}
    {θ : ℝ} (h : ∀ θj ∈ S, windowRadius σ S ν M θj ≤ |θ - θj|) :
    θ ∉ amplitudeWindows σ S ν M := by
  rw [amplitudeWindows]
  intro hmem
  obtain ⟨θj, hθj, hin⟩ := Set.mem_iUnion₂.1 hmem
  have hgap := h θj hθj
  rw [Set.mem_Ioo] at hin
  have hlt : |θ - θj| < windowRadius σ S ν M θj :=
    abs_lt.2 ⟨by linarith [hin.1], by linarith [hin.2]⟩
  exact absurd hgap (not_le.2 hlt)

/-- **The deleted family meets `thm:weighted-dominance`'s own interior clause.**
The theorem asks its caller for a `Θ` outside which every amplitude zero is at
least `exp(-cM/ν_j)` away — the **per-zero** radius of `eq:amplitude-deletion`.
The family built here uses one **common** radius, at the largest multiplicity,
and that is admissible precisely because the common radius is the larger:
`AngularBookkeeping.windowRadius_le`.

This is the direction the composition supplies rather than consumes, and it is
checked here for the same reason the other direction is: each side is
well-formed on its own, so nothing in the build compares them. -/
theorem amplitudeWindows_meets_interior_clause {σ : ℝ} {S : Finset ℝ} {ν : ℝ → ℕ}
    {N : ℕ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (hν : ∀ θj ∈ S, 1 ≤ ν θj) (hνN : ∀ θj ∈ S, ν θj ≤ N) :
    ∀ (M : ℕ) (θ : ℝ), θ ∉ amplitudeWindows σ S (fun _ => N) M →
      ∀ θj ∈ S, windowRadius σ S ν M θj ≤ |θ - θj| := by
  intro M θ hθ θj hθj
  refine le_trans ?_ (amplitudeWindows_spec hθ θj hθj)
  refine le_trans (windowRadius_le (S := S) (N := N) (M := M) hσ1 hσ0
    (hν θj hθj) (hνN θj hθj)) (le_of_eq ?_)
  rw [windowRadius]
  congr 1
  ring

/-- **`eq:dominance-bound` in the shape the producer takes.**  The threshold form
of `thm:weighted-dominance` concludes under `θ ∉ Θ M`; this converts that to the
window predicate, at the deleted family built from the divisor at one common
radius.

Both sides are **eventual** in `M`, which is the point: the dominance theorem
delivers `∃ M₀, ∀ M ≥ M₀`, and a producer asking for every index instead would
be asking for something no theorem in the tree supplies. -/
theorem hdom_of_threshold_form {Q B : Polynomial ℂ} {r : ℕ} {z τ : ℝ → ℝ}
    {S : Finset ℝ} {ν : ℝ → ℕ} {hcol σ : ℝ}
    (hconc : ∃ Md : ℕ, ∀ M : ℕ, Md ≤ M → ∀ θ : ℝ,
      hcol / M ≤ θ → θ ≤ π / r - hcol / M → θ ∉ amplitudeWindows σ S ν M →
      ftRemainder Q B r z τ M θ ≤ ftPrincipalAmp Q B r z τ θ / 2) :
    ∃ Md : ℕ, ∀ M : ℕ, Md ≤ M → ∀ θ : ℝ,
      hcol / M ≤ θ → θ ≤ π / r - hcol / M →
      (∀ θj ∈ S, windowRadius σ S ν M θj ≤ |θ - θj|) →
      ftRemainder Q B r z τ M θ ≤ ftPrincipalAmp Q B r z τ θ / 2 := by
  obtain ⟨Md, hMd⟩ := hconc
  exact ⟨Md, fun M hM θ h1 h2 hgap =>
    hMd M hM θ h1 h2 (notMem_amplitudeWindows_of_gap hgap)⟩

theorem ftWindowRadius_pos (Q B : Polynomial ℂ) (r : ℕ) (z τ : ℝ → ℝ)
    (ε σ : ℝ) (M : ℕ) : 0 < ftWindowRadius Q B r z τ ε σ M :=
  Real.exp_pos _

/-- **`FTPhaseSupply`, produced down to `eq:dominance-bound` and the branch.**

Ten of the twelve clauses are discharged here: the real coefficient polynomial
(`CubicPhaseSign.hasRealCoeffs_ftCoeffPoly`), its eventual nonvanishing and
degree (`lem:eventual-degree`), the divisor and `eq:amplitude-zero-count`
(`InteriorSupply.ftAmplitudeDivisor_count` through
`AngularDiscrepancy.card_le_of_one_le_sum`, which is a step and not a rewording),
the window family and `eq:amplitude-window-negligible`
(`AngularBookkeeping.eventually_deletedLength_le_one`), the retained range, and
the nonvanishing of the amplitude on it
(`InteriorSupply.ftAmplitudeDivisor_complete`, contrapositively).

`hcol` is a parameter, and the caller binds it ahead of `∀ B` — that is where
`prop:angular-discrepancy`'s uniformity lives and this theorem neither creates
nor can destroy it. -/
theorem exists_ftPhaseSupply_of_dominance
    {Q B : Polynomial ℂ} {r : ℕ} {z τ : ℝ → ℝ} {hcol κ₀ κ₁ ε σ : ℝ}
    (hQ : HasRealCoeffs Q) (hB : HasRealCoeffs B) (hr : 1 ≤ r)
    (hQ0 : Q.coeff 0 ≠ 0) (hQ1 : Q.coeff 1 ≠ 0) (hB0 : B ≠ 0) (hBev : B.eval 0 ≠ 0)
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hh : 0 < hcol)
    (hεband : Icc ε (π / r - ε) ⊆ Ioo 0 π)
    (hτ : ∀ θ ∈ Icc ε (π / r - ε), 0 < τ θ)
    -- `thm:FT-geometry`: the principal branch is a simple root of the pencil
    (hroot : ∀ θ ∈ Icc ε (π / r - ε),
      (ftDen Q r ((z θ : ℝ) : ℂ)).eval (ftPrincipal τ θ) = 0)
    (hsimple : ∀ θ ∈ Icc ε (π / r - ε),
      (derivative (ftDen Q r ((z θ : ℝ) : ℂ))).eval (ftPrincipal τ θ) ≠ 0)
    -- `subsec:proof`: `ε` chosen so every amplitude zero of the arc is inside the band
    (hband : ∀ θ ∈ Ioo (0 : ℝ) (π / r),
      ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ) = 0 → θ ∈ Icc ε (π / r - ε))
    -- (1) `eq:dominance-bound` across `eq:retained-range`
    (hdom : ∃ Md : ℕ, ∀ M : ℕ, Md ≤ M → ∀ θ : ℝ, hcol / M ≤ θ → θ ≤ π / r - hcol / M →
      (∀ θj ∈ ftAmplitudeDivisor Q B r z τ ε (π / r - ε),
        ftWindowRadius Q B r z τ ε σ M ≤ |θ - θj|) →
      ftRemainder Q B r z τ M θ ≤ ftPrincipalAmp Q B r z τ θ / 2)
    -- (2) `lem:amplitude-divisor` + `cor:linear-phase-variation` on any ordered
    --     family of blocks where the amplitude does not vanish
    (hbranch : ∃ Mb : ℕ, ∀ M : ℕ, Mb ≤ M → ∀ (k : ℕ) (Lb Rb : Fin k → ℝ),
      (∀ i, Lb i ∈ Icc 0 (π / r)) → (∀ i, Rb i ∈ Icc 0 (π / r)) →
      (∀ i j, i < j → Rb i ≤ Lb j) →
      (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i),
        ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ) ≠ 0) →
      ∃ (ψ dψ : Fin k → ℝ → ℝ) (varψ : Fin k → ℝ),
        (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i),
          ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ)
            = ((ftPrincipalAmp Q B r z τ θ : ℝ) : ℂ)
              * Complex.exp ((ψ i θ : ℂ) * Complex.I)) ∧
        (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i), HasDerivAt (ψ i) (dψ i θ) θ) ∧
        (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i), |dψ i θ| < (M : ℝ) + 1) ∧
        (∀ i, 0 ≤ varψ i) ∧
        (∀ i, Lb i < Rb i → |ψ i (Rb i) - ψ i (Lb i)| ≤ varψ i) ∧
        ∑ i, varψ i ≤ κ₀ + κ₁ * B.natDegree) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → FTPhaseSupply Q B r z τ hcol κ₀ κ₁ M := by
  classical
  obtain ⟨Md, hdom⟩ := hdom
  obtain ⟨Mb, hbranch⟩ := hbranch
  have hπ : (0 : ℝ) < π := pi_pos
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  -- the real coefficient polynomials
  obtain ⟨Pr, hPr⟩ := exists_real_ftCoeffPoly_family_of_real hQ hB r
  -- the recurrence, and the two eventual facts off it
  have hrec : ∀ M, denomConv (ftDenom Q r) (ftCoeffPoly Q B r) M = C (B.coeff M) :=
    fun M => denomConv_ftCoeffPoly Q B hr hQ0 M
  have hBc0 : B.coeff 0 ≠ 0 := by rwa [Polynomial.coeff_zero_eq_eval_zero]
  obtain ⟨M₁, hM₁⟩ :=
    eventual_ne_zero Q hr hQ0 hQ1 (fun M => B.coeff M) hBc0 (ftCoeffPoly Q B r) hrec
  -- the divisor, fixed on the band
  set S : Finset ℝ := ftAmplitudeDivisor Q B r z τ ε (π / r - ε) with hS
  set N : ℕ := max B.natDegree 1 with hN
  have hN1 : 1 ≤ N := le_max_right _ _
  set J : ℕ := S.card with hJ
  -- `eq:amplitude-zero-count`: the DISTINCT count, off the multiplicity sum
  have hmul : ∀ θj ∈ S, 1 ≤ B.rootMultiplicity (ftPrincipal τ θj) := by
    intro θj hθj
    have hz : ftAmp Q B r ((z θj : ℝ) : ℂ) (ftPrincipal τ θj) = 0 :=
      ftAmplitudeDivisor_zero hθj
    have hmem : θj ∈ Icc ε (π / r - ε) := ftAmplitudeDivisor_subset (Finset.mem_coe.2 hθj)
    have hBz : B.eval (ftPrincipal τ θj) = 0 :=
      (ftAmp_eq_zero_iff (hroot θj hmem) (hsimple θj hmem)).1 hz
    have hpos : 0 < B.rootMultiplicity (ftPrincipal τ θj) :=
      (Polynomial.rootMultiplicity_pos hB0).2 hBz
    omega
  have hJdeg : J ≤ B.natDegree :=
    card_le_of_one_le_sum hmul (ftAmplitudeDivisor_count hB0 hεband hτ)
  -- the enumeration of the divisor
  set e : ℕ → ℝ := fun i => if h : i < J then S.orderEmbOfFin hJ.symm ⟨i, h⟩ else 0 with he
  have hemono : ∀ i j, i < j → j < J → e i ≤ e j := by
    intro i j hij hjJ
    have hiJ : i < J := lt_trans hij hjJ
    simp only [he, dif_pos hiJ, dif_pos hjJ]
    exact le_of_lt ((S.orderEmbOfFin hJ.symm).strictMono (by exact hij))
  have hemem : ∀ i, i < J → e i ∈ S := by
    intro i hi
    simp only [he, dif_pos hi]
    exact S.orderEmbOfFin_mem hJ.symm _
  have hesurj : ∀ θ ∈ S, ∃ i, i < J ∧ e i = θ := by
    intro θ hθ
    have : θ ∈ Set.range (S.orderEmbOfFin hJ.symm) := by
      rw [S.range_orderEmbOfFin hJ.symm]; exact hθ
    obtain ⟨i, hi⟩ := this
    exact ⟨i, i.isLt, by simp only [he, dif_pos i.isLt]; rw [← hi]⟩
  -- `eq:amplitude-window-negligible` for the ENLARGED (common-radius) family
  have hdel : ∀ M : ℕ, deletedLength σ S (fun _ => N) M
      = 2 * ftWindowRadius Q B r z τ ε σ M * J := by
    intro M
    have hconst : ∀ θj : ℝ, (2 : ℝ) * windowRadius σ S (fun _ => N) M θj
        = 2 * ftWindowRadius Q B r z τ ε σ M := fun _ => rfl
    rw [deletedLength, Finset.sum_congr rfl (fun θj _ => hconst θj), Finset.sum_const,
      nsmul_eq_mul, ← hJ]
    ring
  obtain ⟨M₂, hM₂⟩ := Filter.eventually_atTop.1
    (eventually_deletedLength_le_one (σ := σ) (S := S) (ν := fun _ => N) (N := N)
      hσ0 hσ1 hN1 (fun _ _ => hN1) (fun _ _ => le_rfl))
  refine ⟨max (max (max M₁ M₂) 1) (max Md Mb), fun M hM => ?_⟩
  have hMbase : max (max M₁ M₂) 1 ≤ M := le_trans (le_max_left _ _) hM
  have hMM1 : M₁ ≤ M :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hMbase
  have hMM2 : M₂ ≤ M :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hMbase
  have hM1le : 1 ≤ M := le_trans (le_max_right _ _) hMbase
  have hMd : Md ≤ M := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hM
  have hMb : Mb ≤ M := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hM
  set ρ : ℝ := ftWindowRadius Q B r z τ ε σ M with hρ
  set Ret : Set ℝ := {θ | hcol / M ≤ θ ∧ θ ≤ π / r - hcol / M
    ∧ ∀ j, j < J → ρ ≤ |θ - e j|} with hRetdef
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM1le
  have hcolpos : 0 < hcol / M := by positivity
  -- the amplitude does not vanish anywhere on the retained range
  have hWne : ∀ θ ∈ Ret, ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ) ≠ 0 := by
    rintro θ ⟨h1, h2, h3⟩ hzero
    have hθopen : θ ∈ Ioo (0 : ℝ) (π / r) :=
      ⟨lt_of_lt_of_le hcolpos h1, lt_of_le_of_lt h2 (by linarith)⟩
    have hmemS : θ ∈ S :=
      ftAmplitudeDivisor_complete hB0 hεband hτ hroot hsimple (hband θ hθopen hzero) hzero
    obtain ⟨i, hiJ, hei⟩ := hesurj θ hmemS
    have hgap := h3 i hiJ
    rw [hei, sub_self, abs_zero] at hgap
    exact absurd hgap (not_le.2 (ftWindowRadius_pos Q B r z τ ε σ M))
  refine ⟨Pr M, e, Ret, J, ρ, hPr M, hM₁ M hMM1, ?_, hM1le,
    ftWindowRadius_pos _ _ _ _ _ _ _ _, hJdeg, hemono, ?_, ?_, ?_, ?_, ?_⟩
  · -- `lem:eventual-degree` against the total angular measure
    refine le_trans ?_ (natDegree_le_angular_measure M hr)
    exact_mod_cast eventual_natDegree_le Q hr hQ0 (fun M => B.coeff M)
      (ftCoeffPoly Q B r) hrec M
  · -- `eq:amplitude-window-negligible`
    have := hM₂ M hMM2
    rw [hdel M] at this
    calc ((M : ℝ) + 1) * (2 * ρ * J) = ((M : ℝ) + 1) * (2 * ρ * J) := rfl
      _ ≤ 1 := by rw [hρ]; exact this
  · -- `Ret` is `eq:retained-range` verbatim
    exact fun θ h1 h2 h3 => ⟨h1, h2, fun j hj => h3 j hj⟩
  · -- the amplitude does not vanish on the retained range
    exact hWne
  · -- `eq:dominance-bound`
    rintro θ ⟨h1, h2, h3⟩
    refine hdom M hMd θ h1 h2 fun θj hθj => ?_
    obtain ⟨i, hiJ, hei⟩ := hesurj θj hθj
    rw [← hei]
    exact h3 i hiJ
  · -- the branch supply
    intro k Lb Rb hL hR hord hret
    exact hbranch M hMb k Lb Rb hL hR hord
      fun i hi θ hθ => hWne θ (hret i hi hθ)

/-- **`prop:angular-discrepancy` from `eq:dominance-bound` and the branch.**  The
producer composed onto `AngularDiscrepancyFT.ftAngularDiscrepancy_of_supply`:
everything between `thm:weighted-dominance` and the discrepancy is discharged,
and what is left is the two statements those theorems conclude.

**The binder order is preserved and is the point.**  `hcol`, `κ₀` and `κ₁` are
bound **before** `∀ B` — so `C₀` and `C₁` are built from constants of `Q` and `r`
alone and a `B`-dependent collar is unwritable — while `ε` and `σ` are bound
*after* it, which is where `subsec:proof` puts them ("for the fixed weight `B`,
decrease to some `0 < ε ≤ ε_*`"), and `M₀` after that. -/
theorem ftAngularDiscrepancy_of_dominance {Q : Polynomial ℂ} {r : ℕ} {z τ : ℝ → ℝ}
    (hQ : HasRealCoeffs Q) (hr : 1 ≤ r) (hQ0 : Q.coeff 0 ≠ 0) (hQ1 : Q.coeff 1 ≠ 0)
    (hzmono : StrictMonoOn z (Icc 0 (π / r))) (hzcont : ContinuousOn z (Icc 0 (π / r)))
    (hτ0 : ∀ θ ∈ Icc 0 (π / r), 0 < τ θ)
    (hsupply : ∃ hcol κ₀ κ₁ : ℝ, 0 < hcol ∧ 0 ≤ κ₀ ∧ 0 ≤ κ₁ ∧
      ∀ B : Polynomial ℂ, HasRealCoeffs B → B.eval 0 ≠ 0 →
        ∃ ε σ : ℝ, 0 ≤ ε ∧ 0 < σ ∧ σ < 1 ∧
          Icc ε (π / r - ε) ⊆ Ioo 0 π ∧
          (∀ θ ∈ Icc ε (π / r - ε),
            (ftDen Q r ((z θ : ℝ) : ℂ)).eval (ftPrincipal τ θ) = 0) ∧
          (∀ θ ∈ Icc ε (π / r - ε),
            (derivative (ftDen Q r ((z θ : ℝ) : ℂ))).eval (ftPrincipal τ θ) ≠ 0) ∧
          (∀ θ ∈ Ioo (0 : ℝ) (π / r),
            ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ) = 0 →
              θ ∈ Icc ε (π / r - ε)) ∧
          (∃ Md : ℕ, ∀ M : ℕ, Md ≤ M → ∀ θ : ℝ,
            hcol / M ≤ θ → θ ≤ π / r - hcol / M →
            (∀ θj ∈ ftAmplitudeDivisor Q B r z τ ε (π / r - ε),
              ftWindowRadius Q B r z τ ε σ M ≤ |θ - θj|) →
            ftRemainder Q B r z τ M θ ≤ ftPrincipalAmp Q B r z τ θ / 2) ∧
          (∃ Mb : ℕ, ∀ M : ℕ, Mb ≤ M → ∀ (k : ℕ) (Lb Rb : Fin k → ℝ),
            (∀ i, Lb i ∈ Icc 0 (π / r)) → (∀ i, Rb i ∈ Icc 0 (π / r)) →
            (∀ i j, i < j → Rb i ≤ Lb j) →
            (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i),
              ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ) ≠ 0) →
            ∃ (ψ dψ : Fin k → ℝ → ℝ) (varψ : Fin k → ℝ),
              (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i),
                ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ)
                  = ((ftPrincipalAmp Q B r z τ θ : ℝ) : ℂ)
                    * Complex.exp ((ψ i θ : ℂ) * Complex.I)) ∧
              (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i),
                HasDerivAt (ψ i) (dψ i θ) θ) ∧
              (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i), |dψ i θ| < (M : ℝ) + 1) ∧
              (∀ i, 0 ≤ varψ i) ∧
              (∀ i, Lb i < Rb i → |ψ i (Rb i) - ψ i (Lb i)| ≤ varψ i) ∧
              ∑ i, varψ i ≤ κ₀ + κ₁ * B.natDegree)) :
    FTAngularDiscrepancy Q r z := by
  obtain ⟨hcol, κ₀, κ₁, hh, hκ₀, hκ₁, hmain⟩ := hsupply
  refine ftAngularDiscrepancy_of_supply hzmono hzcont hτ0
    ⟨hcol, κ₀, κ₁, hh.le, hκ₀, hκ₁, fun B hB hBev => ?_⟩
  obtain ⟨ε, σ, hε0, hσ0, hσ1, hεband, hroot, hsimple, hband, hdom, hbranch⟩ :=
    hmain B hB hBev
  have hB0 : B ≠ 0 := fun h => hBev (by rw [h]; simp)
  have hsub : Icc ε (π / r - ε) ⊆ Icc 0 (π / r) :=
    Icc_subset_Icc hε0 (by linarith)
  exact exists_ftPhaseSupply_of_dominance hQ hB hr hQ0 hQ1 hB0 hBev hσ0 hσ1 hh
    hεband (fun θ hθ => hτ0 θ (hsub hθ)) hroot hsimple hband hdom hbranch

end ForgacsTran
