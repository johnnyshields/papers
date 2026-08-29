/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.AngularWindow
import ForgacsTran.MainClauses

/-!
# `prop:angular-discrepancy` at the pencil

`AngularWindow` proves `eq:angular-discrepancy` over abstract counts.  This
module instantiates it at `F_M` and produces the term
`ConsequencesComposition.FTAngularDiscrepancy Q r z` that
`prop:equidistribution` and `cor:angular-rigidity` already consume.

## Main statements

* `ftRemainder_eq_abs` — `eq:principal-decomposition` read as a *real* identity:
  `|R_M|` is the absolute value of `τ^{M+1}F_M(z(θ))` less twice the real part of
  the principal term.
* `FTPhaseSupply` — the supply of `subsec:proof` at one weight and one index.
* `ftAngularDiscrepancy_of_supply` — the producer.

## Implementation notes

**The binder order is the theorem, and it is discharged here.**  `h`, `κ₀` and
`κ₁` do not appear in the producer's binder list at all: they are bound inside
`hsupply`, ahead of `∀ B`, and obtained in the proof.  So `C₀` and `C₁` are
*built* from constants of `Q` and `r` before the weight is seen, and a
carried-instead-of-applied constant could not hide — it would have to be a
binder, and there would be nothing to bind it to.  What comes after `B` is the
threshold `M₀`, which is where `subsec:proof` puts it too ("the threshold in `M`
may depend on `B`, but the discrepancy constants do not").

**What the supply asserts, and what it does not.**  `FTPhaseSupply` is
`thm:FT-geometry`, `lem:amplitude-divisor` and `thm:weighted-dominance` at one
index, in the shape those theorems conclude in.  It is a hypothesis: this module
composes, it does not discharge the analysis.  The one place it is *stronger*
than the manuscript's literal statement is the common window half-width — see
`AngularBlocks`, where the reason is that a nested family of windows has no
ordered block decomposition, and `AngularBookkeeping.windowRadius_le` is what
makes the strengthening free.

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Angular discrepancy and
proof of the main theorem» (`subsec:proof`, `prop:angular-discrepancy`,
`eq:angular-discrepancy`).

## Tags

angular discrepancy, uniformity, weight polynomial
-/

namespace ForgacsTran

open Set Real

/-- **`eq:principal-decomposition` as a real identity.**  `ftRemainder` is the
modulus of a complex number that is in fact real: the normalized coefficient is
real because `Q` and `B` are, and so is twice the real part it is compared
against.  This is what lets the phase count's `|R_M| ≤ |W|/2` be read off
`eq:dominance-bound`. -/
theorem ftRemainder_eq_abs {Q B : Polynomial ℂ} {r M : ℕ} {z τ : ℝ → ℝ}
    {P : Polynomial ℝ} (hP : P.map (algebraMap ℝ ℂ) = ftCoeffPoly Q B r M)
    {θ : ℝ} (hτ : 0 < τ θ) :
    ftRemainder Q B r z τ M θ
      = |(τ θ) ^ (M + 1) * P.eval (z θ)
          - 2 * (ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ)
              * Complex.exp (-(((((M : ℝ) + 1) * θ : ℝ)) : ℂ) * Complex.I)).re| := by
  have heval : (ftCoeffPoly Q B r M).eval ((z θ : ℝ) : ℂ) = ((P.eval (z θ) : ℝ) : ℂ) := by
    rw [← hP, Polynomial.eval_map,
      show (((z θ : ℝ) : ℂ)) = (algebraMap ℝ ℂ) (z θ) from rfl,
      Polynomial.eval₂_at_apply]
    rfl
  have hratio : ((τ θ : ℝ) : ℂ) ^ (M + 1)
      * (ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ) / (ftPrincipal τ θ) ^ (M + 1))
      = ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ)
        * Complex.exp (-(((((M : ℝ) + 1) * θ : ℝ)) : ℂ) * Complex.I) := by
    rw [show ((τ θ : ℝ) : ℂ) ^ (M + 1)
        * (ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ) / (ftPrincipal τ θ) ^ (M + 1))
        = (((τ θ : ℝ) : ℂ) ^ (M + 1) / (ftPrincipal τ θ) ^ (M + 1))
          * ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ) by ring,
      ftPrincipal_pow_ratio hτ M]
    ring
  rw [ftRemainder, heval, hratio,
    show (((τ θ : ℝ) : ℂ)) ^ (M + 1) * ((P.eval (z θ) : ℝ) : ℂ)
      = (((τ θ) ^ (M + 1) * P.eval (z θ) : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

/-- **`subsec:proof`'s supply at one weight and one index.**  Everything the
count consumes at `F_M`: the branch of `thm:FT-geometry` through
`eq:principal-decomposition`, the divisor of `lem:amplitude-divisor` with
`eq:amplitude-zero-count`, `thm:weighted-dominance` across `eq:retained-range`,
`eq:amplitude-window-negligible`, `eq:phase-derivative-bound`, and
`cor:linear-phase-variation` over the retained blocks.

`hcol` is the collar constant `h(Q,r)` of `eq:retained-range` and `κ₀`, `κ₁` are
the constants of `eq:linear-phase-variation`.  All three are parameters here; it
is `ftAngularDiscrepancy_of_supply` that binds them ahead of the weight, which is
where the uniformity of `prop:angular-discrepancy` is discharged.

**The variation enters summed.**  The last clause bounds `∑ᵢ Var_{ℐᵢ}ψ` over the
whole family by `κ₀ + κ₁ deg B`, and there is no way to supply a per-component
cap instead: `J+1` components each at `κ₀ + κ₁ deg B` would sum to
`(J+1)(κ₀ + κ₁ deg B)`, quadratic once `J ≤ deg B`, and that is exactly the
uniformity `thm:main` clause 3 asserts.  The shape of the clause excludes it. -/
def FTPhaseSupply (Q B : Polynomial ℂ) (r : ℕ) (z τ : ℝ → ℝ)
    (hcol κ₀ κ₁ : ℝ) (M : ℕ) : Prop :=
  ∃ (P : Polynomial ℝ) (e : ℕ → ℝ) (Ret : Set ℝ) (J : ℕ) (ρ : ℝ),
    P.map (algebraMap ℝ ℂ) = ftCoeffPoly Q B r M ∧
    ftCoeffPoly Q B r M ≠ 0 ∧
    ((ftCoeffPoly Q B r M).natDegree : ℝ) ≤ ((M : ℝ) + 1) * (π / r) / π ∧
    1 ≤ M ∧ 0 < ρ ∧ J ≤ B.natDegree ∧
    (∀ i j, i < j → j < J → e i ≤ e j) ∧
    ((M : ℝ) + 1) * (2 * ρ * J) ≤ 1 ∧
    (∀ θ, hcol / M ≤ θ → θ ≤ π / r - hcol / M →
      (∀ j, j < J → ρ ≤ |θ - e j|) → θ ∈ Ret) ∧
    (∀ θ ∈ Ret, ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ) ≠ 0) ∧
    (∀ θ ∈ Ret, ftRemainder Q B r z τ M θ ≤ ftPrincipalAmp Q B r z τ θ / 2) ∧
    (∀ (k : ℕ) (Lb Rb : Fin k → ℝ),
      (∀ i, Lb i ∈ Icc 0 (π / r)) → (∀ i, Rb i ∈ Icc 0 (π / r)) →
      (∀ i j, i < j → Rb i ≤ Lb j) →
      (∀ i, Lb i < Rb i → Icc (Lb i) (Rb i) ⊆ Ret) →
      ∃ (ψ dψ : Fin k → ℝ → ℝ) (varψ : Fin k → ℝ),
        (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i),
          ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ)
            = ((ftPrincipalAmp Q B r z τ θ : ℝ) : ℂ)
              * Complex.exp ((ψ i θ : ℂ) * Complex.I)) ∧
        (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i), HasDerivAt (ψ i) (dψ i θ) θ) ∧
        (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i), |dψ i θ| < (M : ℝ) + 1) ∧
        (∀ i, 0 ≤ varψ i) ∧
        (∀ i, Lb i < Rb i → |ψ i (Rb i) - ψ i (Lb i)| ≤ varψ i) ∧
        ∑ i, varψ i ≤ κ₀ + κ₁ * B.natDegree)

/-- **`eq:angular-distinct-lower` at the pencil.**  The supply instantiated at
`F_M`: the distinct zeros of the coefficient polynomial inside `z(I_{α,β})`,
uniformly over windows, at the constants
`C₀ = (4h+1+κ₀)/π + 2` and `C₁ = κ₁/π + 2`.

The `α`, `β` binders come **last**, which is what lets one application serve the
window and both of its complements in `abs_windowCount_sub_le`. -/
theorem exists_windowZeros_of_supply {Q B : Polynomial ℂ} {r M : ℕ} {z τ : ℝ → ℝ}
    {hcol κ₀ κ₁ : ℝ} (hh : 0 < hcol) (hκ₀ : 0 ≤ κ₀) (hκ₁ : 0 ≤ κ₁)
    (hzmono : StrictMonoOn z (Ioo 0 (π / r))) (hzcont : ContinuousOn z (Ioo 0 (π / r)))
    (hτ : ∀ θ ∈ Ioo 0 (π / r), 0 < τ θ)
    (hs : FTPhaseSupply Q B r z τ hcol κ₀ κ₁ M)
    {α β : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : β ≤ π / r) :
    ∃ Z : Finset ℂ,
      ((M : ℝ) + 1) * (β - α) / π - ((4 * hcol + 1 + κ₀) / π + 2)
          - (κ₁ / π + 2) * (B.natDegree : ℝ) ≤ (Z.card : ℝ) ∧
      (∀ w ∈ Z, (ftCoeffPoly Q B r M).IsRoot w) ∧
      (∀ w ∈ Z, w ∈ ftWindow z α β) := by
  obtain ⟨P, e, Ret, J, ρ, hPeq, hPne, hdeg, hM1, hρ, hJK, he, hwin, hRet, hWne,
    hdom, hbranch⟩ := hs
  have hcolnn : (0 : ℝ) ≤ hcol / M := by positivity
  have hcolpos : (0 : ℝ) < hcol / M := by
    have : (0 : ℝ) < M := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hM1
    positivity
  set Ret' : Set ℝ := Ret ∩ Ioo 0 (π / r) with hRet'
  have hRet'sub : Ret' ⊆ Ioo 0 (π / r) := inter_subset_right
  set W : ℝ → ℂ := fun θ => ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ) with hW
  set Rm : ℝ → ℝ := fun θ => (τ θ) ^ (M + 1) * P.eval (z θ)
      - 2 * (W θ * Complex.exp (-(((((M : ℝ) + 1) * θ : ℝ)) : ℂ) * Complex.I)).re with hRm
  have hdec : ∀ θ ∈ Ioo 0 (π / r), (τ θ) ^ (M + 1) * P.eval (z θ)
      = 2 * (W θ * Complex.exp (-(((((M : ℝ) + 1) * θ : ℝ)) : ℂ) * Complex.I)).re
        + Rm θ := fun θ _ => by rw [hRm]; ring
  have hdomb : ∀ θ ∈ Ret', |Rm θ| ≤ ‖W θ‖ / 2 := by
    intro θ hθ
    have hτθ : 0 < τ θ := hτ θ (hRet'sub hθ)
    have hd := hdom θ hθ.1
    rwa [ftRemainder_eq_abs hPeq hτθ, ftPrincipalAmp] at hd
  have hWne' : ∀ θ ∈ Ret', W θ ≠ 0 := fun θ hθ => hWne θ hθ.1
  have hRet'mem : ∀ θ, hcol / M ≤ θ → θ ≤ π / r - hcol / M →
      (∀ j, j < J → ρ ≤ |θ - e j|) → θ ∈ Ret' := by
    intro θ h1 h2 h3
    exact ⟨hRet θ h1 h2 h3, ⟨lt_of_lt_of_le hcolpos h1, by linarith⟩⟩
  obtain ⟨Z, hZc, hZr, hZm⟩ :=
    exists_windowZeros (P := P) (z := z) (τ := fun θ => (τ θ) ^ (M + 1))
      (Rm := Rm) (W := W) (e := e) (Ret := Ret') (J := J) (M := M) (K := B.natDegree)
      (ρ := ρ) (hcol := hcol) (κ₀ := κ₀) (κ₁ := κ₁) (bnd := π / r)
      hM1 hh hρ hα hαβ hβ hJK hwin he hzmono hzcont
      (fun θ hθ => pow_pos (hτ θ hθ) _) hRet'mem hWne' hdomb hdec hκ₀ hκ₁
      (fun k Lb Rb hL hR hord hret =>
        hbranch k Lb Rb hL hR hord fun i hi => subset_trans (hret i hi) inter_subset_left)
  exact ⟨Z, hZc, by rw [← hPeq]; exact hZr, hZm⟩

open scoped Classical in
/-- **`prop:angular-discrepancy`.**  The producer of
`ConsequencesComposition.FTAngularDiscrepancy`, which
`ft_equidistribution_of_discrepancy` and `ft_angular_clock_of_discrepancy`
already consume.

`C₀ = 2((4h+1+κ₀)/π + 2)` and `C₁ = 2(κ₁/π + 2)` are built from `h`, `κ₀`, `κ₁`
alone, and every one of those is bound inside `hsupply` ahead of `∀ B`.  The
doubling is the complementation: `subsec:proof` gets the upper bound by applying
`eq:angular-distinct-lower` to the two complementary intervals, so the two-sided
constant is twice the one-sided one. -/
theorem ftAngularDiscrepancy_of_supply {Q : Polynomial ℂ} {r : ℕ} {z τ : ℝ → ℝ}
    (hzmono : StrictMonoOn z (Ioo 0 (π / r)))
    (hzcont : ContinuousOn z (Ioo 0 (π / r)))
    (hτ : ∀ θ ∈ Ioo 0 (π / r), 0 < τ θ)
    (hsupply : ∃ hcol κ₀ κ₁ : ℝ, 0 < hcol ∧ 0 ≤ κ₀ ∧ 0 ≤ κ₁ ∧
      ∀ B : Polynomial ℂ, HasRealCoeffs B → B.eval 0 ≠ 0 →
        ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → FTPhaseSupply Q B r z τ hcol κ₀ κ₁ M) :
    FTAngularDiscrepancy Q r z := by
  classical
  obtain ⟨hcol, κ₀, κ₁, hh, hκ₀, hκ₁, hmain⟩ := hsupply
  have hπ : (0 : ℝ) < π := pi_pos
  refine ⟨2 * ((4 * hcol + 1 + κ₀) / π + 2), 2 * (κ₁ / π + 2), by positivity,
    by positivity, fun B hB hB0 => ?_⟩
  obtain ⟨M₀, hM₀⟩ := hmain B hB hB0
  refine ⟨M₀, fun M hM α β hα hαβ hβ => ?_⟩
  have hs := hM₀ M hM
  obtain ⟨-, -, -, -, -, -, hPne, hdeg, -, -, -, -, -, -, -, -⟩ := id hs
  exact abs_windowCount_sub_le (Pc := ftCoeffPoly Q B r M) (z := z) (M := M)
    (K := B.natDegree) (C₀ := (4 * hcol + 1 + κ₀) / π + 2) (C₁ := κ₁ / π + 2)
    (bnd := π / r) (α := α) (β := β) hPne (by positivity) (by positivity)
    hzmono hα hαβ.le hβ hdeg
    (fun α' β' hα' hαβ' hβ' =>
      exists_windowZeros_of_supply hh hκ₀ hκ₁ hzmono hzcont hτ hs hα' hαβ' hβ')

end ForgacsTran
