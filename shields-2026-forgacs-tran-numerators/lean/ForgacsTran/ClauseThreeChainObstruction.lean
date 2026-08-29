/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.BranchDivisorWitness
import ForgacsTran.ClauseThreeComposition

/-!
# What `FTChainGeom` asks for that the arc does not have

`ClauseThreeComposition.FTChainGeom` reads as a multi-component bundle: a chain `w` whose
odd-to-even steps are the components of `eq:Omega-M`, at most `K + 1` of them, with the
even-to-odd steps standing for the deleted amplitude windows.  It is not one, and the two
theorems here say why.

The chain lives inside a single set `A` that is `Set.OrdConnected`, so `A` contains the
whole closed interval from `w 0` to `w (2n)` — the gaps between components included.  Every
clause stated `∀ θ ∈ A` therefore holds across those gaps too, and two of them are strong:
`A` is off the deleted windows `Θ M`, and the principal amplitude does not vanish on `A`.
Meanwhile the length clause forces that interval to span all but `2h/M + wid` of the
viewing arc, with `wid` itself below `1/(M+1)`.

So `FTChainGeom` implies a *single* interval, nearly the whole arc, carrying no amplitude
zero at all — which is the case `lem:amplitude-divisor` calls `deg B = 0` on the branch.
A weight whose reduced form contributes one zero of the principal amplitude in the interior
of the arc refutes the bundle, and every witness of it in this tree is at one component
with `Θ = ∅`.  `BranchDivisorWitness.branchWitnessB` builds such a weight at every
admissible pencil and every angle of the open arc, real and nonvanishing at the origin —
which is exactly the class the phase-supply producers quantify over — so the absence of a
producer is not a gap in the search.

This is why there is no producer of `FTChainGeom` from the admissible class, and why
`ClauseThreeSupply` reaches `thm:main` clause 3 through `AngularDiscrepancyFT.FTPhaseSupply`
instead: that supply carries one branch per component and asks for nonvanishing only on the
retained set, which is what `eq:amplitude-zero-count` leaves.

Sorry-free.

## Main statements

* `ftChainGeom_span` — the chain's span is one interval, inside the retained range, off the
  deleted windows, on which `τ > 0` and the principal amplitude does not vanish.
* `not_ftChainGeom_of_amp_zero` — one amplitude zero in the interior of the retained range
  refutes the bundle.
* `exists_weight_not_ftChainGeom` — at every admissible pencil there IS such a weight, real
  and nonvanishing at the origin, so no producer of the bundle from the admissible class can
  exist.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, `prop:angular-discrepancy`,
`eq:Omega-M`, `eq:retained-range`, `eq:amplitude-zero-count`, `lem:amplitude-divisor`.

## Tags

chain geometry, amplitude zeros, order connected, obstruction
-/

namespace ForgacsTran

open Set Real

/-- **The chain spans one interval, and every `∀ θ ∈ A` clause holds across it.**

`A` is order-connected and contains `w 0` and `w (2n)`, so it contains `[w 0, w (2n)]`; the
components' total length telescopes below `w (2n) - w 0` because `w` is monotone.  The
deleted windows are therefore *not* deleted from the span: they sit inside it, carrying the
retained-range clause, the positivity of `τ`, and the nonvanishing of the principal
amplitude with them. -/
theorem ftChainGeom_span {Q B : Polynomial ℂ} {r : ℕ} {z τ ψ : ℝ → ℝ} {M K : ℕ}
    {hwin wid κ₀ κ₁ h bb : ℝ} {Θ : ℕ → Set ℝ} {T : Set ℝ}
    (hgeom : FTChainGeom Q B r z τ ψ M K hwin wid κ₀ κ₁ h bb Θ T) :
    ∃ u v : ℝ, u ≤ v ∧ π / r - 2 * hwin / M - wid ≤ v - u ∧
      (∀ θ ∈ Icc u v, h / M ≤ θ ∧ θ ≤ bb - h / M ∧ θ ∉ Θ M) ∧
      (∀ θ ∈ Icc u v, 0 < τ θ) ∧
      (∀ θ ∈ Icc u v, ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ) ≠ 0) := by
  obtain ⟨A, w, n, dψ, κ, hAconn, hret, hw, hmem, _hsep, _hzmono, _hzT, hτ, hWne, _hpolar,
    _hψ, _hκbd, _hMκ, _hcard, hlen, _hwid, _hvar⟩ := hgeom
  have hsub : Icc (w 0) (w (2 * n)) ⊆ A := hAconn.out (hmem 0) (hmem (2 * n))
  have hle : w 0 ≤ w (2 * n) := hw (Nat.zero_le _)
  -- the components telescope below the span
  have htel : ∀ m : ℕ, ∑ i ∈ Finset.range m, (w (2 * i + 1) - w (2 * i))
      ≤ w (2 * m) - w 0 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [Finset.sum_range_succ]
        have h1 : w (2 * m + 1) ≤ w (2 * (m + 1)) := hw (by omega)
        linarith [ih]
  refine ⟨w 0, w (2 * n), hle, le_trans hlen (htel n), fun θ hθ => hret θ (hsub hθ),
    fun θ hθ => hτ θ (hsub hθ), fun θ hθ => hWne θ (hsub hθ)⟩

/-- **One interior amplitude zero refutes the chain geometry.**

At `bb = π/r` the span of `ftChainGeom_span` sits inside `[h/M, π/r - h/M]` and is longer
than `π/r - 2hwin/M - wid`, so it reaches within `2hwin/M - h/M + wid` of either end of the
arc.  Any `θ₀` further in than that lies in the span, where the bundle asserts the principal
amplitude does not vanish.

`lem:amplitude-divisor` puts such a `θ₀` on the arc for exactly the weights whose reduced
form has a zero on the branch, which is the generic case; that is the sub-statement no
producer of `FTChainGeom` from the admissible class can supply. -/
theorem not_ftChainGeom_of_amp_zero {Q B : Polynomial ℂ} {r : ℕ} {z τ ψ : ℝ → ℝ} {M K : ℕ}
    {hwin wid κ₀ κ₁ h : ℝ} {Θ : ℕ → Set ℝ} {T : Set ℝ} {θ₀ : ℝ}
    (hlo : 2 * hwin / M - h / M + wid ≤ θ₀)
    (hhi : θ₀ ≤ π / r + h / M - 2 * hwin / M - wid)
    (hzero : ftAmp Q B r ((z θ₀ : ℝ) : ℂ) (ftPrincipal τ θ₀) = 0) :
    ¬ FTChainGeom Q B r z τ ψ M K hwin wid κ₀ κ₁ h (π / r) Θ T := by
  intro hgeom
  obtain ⟨u, v, huv, hlen, hret, -, hWne⟩ := ftChainGeom_span hgeom
  have hu : h / M ≤ u := (hret u ⟨le_rfl, huv⟩).1
  have hv : v ≤ π / r - h / M := (hret v ⟨huv, le_rfl⟩).2.1
  exact hWne θ₀ ⟨by linarith, by linarith⟩ hzero

/-- **At every admissible pencil there is an admissible weight refuting the bundle.**

`BranchDivisorWitness.branchWitnessB` is the real quadratic whose zeros are the branch point
at `θ_j` and its conjugate; it is real, does not vanish at the origin, and puts `θ_j` in the
amplitude divisor.  Feed that zero to `not_ftChainGeom_of_amp_zero`.

Every parameter of the bundle other than the pencil is universally quantified — the branch
`ψ`, the deleted windows `Θ`, the target `T`, the component cap `K`, the index `M`, and the
four constants — so this is not the failure of one instantiation.  `FTPhaseSupply` is
therefore the strongest supply the admissible class produces, and the route to `thm:main`
clause 3 has to run through it. -/
theorem exists_weight_not_ftChainGeom {n r : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ} {z : ℝ → ℝ}
    (hn : 0 < n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r)
    (hz : ∀ θ ∈ Ioo (0 : ℝ) (π / r), z θ = ftBranchZ a c r (n - 1) θ)
    {θj : ℝ} (hθj : θj ∈ Ioo (0 : ℝ) (π / r))
    {M K : ℕ} {ψ : ℝ → ℝ} {hwin wid κ₀ κ₁ h : ℝ} {Θ : ℕ → Set ℝ} {T : Set ℝ}
    (hlo : 2 * hwin / M - h / M + wid ≤ θj)
    (hhi : θj ≤ π / r + h / M - 2 * hwin / M - wid) :
    ∃ B : Polynomial ℂ, HasRealCoeffs B ∧ B.eval 0 ≠ 0 ∧
      ¬ FTChainGeom (ftRootPoly c a) B r z (ftTauArc a r (n - 1) x₁) ψ M K
          hwin wid κ₀ κ₁ h (π / r) Θ T := by
  classical
  obtain ⟨B, ε, hBr, -, hBev, -, -, hmem, -⟩ :=
    exists_nonempty_ftAmplitudeDivisor_at_branch (x₁ := x₁) hn ha hc hr hnr hz hθj
  refine ⟨B, hBr, hBev, not_ftChainGeom_of_amp_zero hlo hhi ?_⟩
  rw [ftAmplitudeDivisor, Finset.mem_filter] at hmem
  exact hmem.2.2

end ForgacsTran
