/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.AmplitudeAlong
import ForgacsTran.BranchSupplyGeometry

/-!
# The cofactor and amplitude groups at the general pencil

`AmplitudeAlong` produces `hSd`, `hSc`, `hWd` and `hWc` from branch data alone, and
`BranchSupply.ftCofactorAlong_ne_zero` produces `hS0` from the pencil's own simplicity.
Both were stated at a free `(Q, z, τ)` and instantiated only at the cubic.  This module
instantiates them at `(ftRootPoly c a, ftBranchZLower, ftTauArc)`, which is the triple
`PhaseSupplyGeneral` runs at, so that four of the branch supply's binders stop being
hypotheses of the general theorem.

**The state on the open arc is the whole input.**  Three facts — the branch point is
nonzero, it is a root of the pencil at its own spectral value, and it misses the zeros of
`E = XQ' - rQ` — carry every one of them: the first two give the cofactor's derivative
through `S = E(γ)/γ`, and the third gives its nonvanishing.  All three are already
unconditional at the admissible class (`FTGeometryAssembly.ft_branch_root_and_pos`,
`BranchAmplitude.eval_ftCritical_ftPrincipal_ne_zero`), so nothing new is assumed.

**The radii have to be exchanged pointwise, not as functions.**  The general facts are
stated at `ftTau` and `ftBranchZ`, and the supply runs at `ftTauArc` and `ftBranchZLower`,
which differ from them at `θ = 0` and at `π/r`.  Every statement here is quantified over
the **open** arc, where `ftTauArc_agree` and `ftBranchZLower_agree` apply, so the exchange
is a rewrite at each point rather than a congruence of functions.

Sorry-free.

## Main statements

* `ft_branch_state_arc` — the three-clause state on the open arc, at the arc's own radius.
* `ftArcCofactorDeriv`, `ftArcAmpDeriv` — the `dS` and `dW` the general pencil supplies.
* `ft_cofactor_group` — `hSd`, `hSc` and `hS0` at the general pencil.
* `ft_amplitude_group` — `hWd` and `hWc` at the general pencil, for every weight.

## References

Formalizes `../../shields-2026-forgacs-tran-numerators.tex`, `sec:geometry`,
`eq:Dprime-identity`, `eq:principal-simple`, `lem:amplitude-divisor`.

## Tags

cofactor, residue amplitude, branch, general pencil, Forgács–Tran
-/

namespace ForgacsTran

open Polynomial Set Real

variable {n r : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ}

/-! ### The two derivative data, named

`ftCofactorAlongDeriv` and `ftAmpAlongDeriv` take the branch's derivative as an argument,
which at this pencil is always `ftGammaDeriv`.  Naming the two instances keeps the general
supply's statement readable — every occurrence below is one of these two. -/

/-- **`dS` at the general pencil**: `∂_tD` along the arc, differentiated. -/
noncomputable def ftArcCofactorDeriv {n : ℕ} (a : Fin n → ℝ) (c : ℝ) (r : ℕ) (x₁ : ℝ) :
    ℝ → ℂ :=
  ftCofactorAlongDeriv (ftRootPoly c a) r (ftTauArc a r (n - 1) x₁)
    (ftGammaDeriv a r (n - 1))

/-- **`dW` at the general pencil**: the residue amplitude along the arc, differentiated. -/
noncomputable def ftArcAmpDeriv {n : ℕ} (a : Fin n → ℝ) (B : Polynomial ℂ) (c : ℝ) (r : ℕ)
    (x₁ : ℝ) : ℝ → ℂ :=
  ftAmpAlongDeriv (ftRootPoly c a) B r (ftBranchZLower a c r (n - 1))
    (ftTauArc a r (n - 1) x₁) (ftGammaDeriv a r (n - 1)) (ftArcCofactorDeriv a c r x₁)

/-- **The branch state on the open arc, at the arc's radius.**  Nonvanishing of the branch
point, the pencil's vanishing there, and `E(γ) ≠ 0` — the three clauses
`BranchSupply.ftCofactorAlong_ne_zero_on` and `AmplitudeAlong.hasDerivAt_ftCofactorAlong`
consume between them.

`ftTauArc` and `ftBranchZLower` are exchanged for `ftTau` and `ftBranchZ` at each point of
the open arc, which is where they agree. -/
theorem ft_branch_state_arc (hn : 0 < n) (ha : ∀ k, 0 < a k) (hc : c ≠ 0)
    (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r) :
    ∀ s ∈ Ioo (0 : ℝ) (π / r),
      ftPrincipal (ftTauArc a r (n - 1) x₁) s ≠ 0
      ∧ (ftDen (ftRootPoly c a) r ((ftBranchZLower a c r (n - 1) s : ℝ) : ℂ)).eval
          (ftPrincipal (ftTauArc a r (n - 1) x₁) s) = 0
      ∧ ftCriticalAlong (ftRootPoly c a) r (ftTauArc a r (n - 1) x₁) s ≠ 0 := by
  intro s hs
  obtain ⟨hroot, hpos⟩ := ft_branch_root_and_pos (a := a) (r := r) c hn ha hr hnr
  have hγ : ftPrincipal (ftTauArc a r (n - 1) x₁) s = ftPrincipal (ftTau a r (n - 1)) s :=
    ftPrincipal_congr (ftTauArc_agree a r (n - 1) x₁ hs.1 hs.2)
  refine ⟨?_, ?_, ?_⟩
  · rw [hγ]
    exact ftPrincipal_ne_zero (hpos s hs).ne'
  · rw [hγ, ftBranchZLower_agree a c r (n - 1) hs.1]
    exact hroot s hs
  · rw [ftCriticalAlong, hγ]
    exact eval_ftCritical_ftPrincipal_ne_zero hn ha hc hr hnr hs

/-- **`hSd`, `hSc` and `hS0` at the general pencil.**  The cofactor's derivative along the
arc is `ftCofactorAlongDeriv`, built from `γ'` and `γ ≠ 0` alone — no `z'` enters, because
`∂_tD` collapses to `E(γ)/γ` at a root of the pencil.

This is the group `PhaseSupplyGeneral` had been carrying as three hypotheses. -/
theorem ft_cofactor_group (hn : 0 < n) (ha : ∀ k, 0 < a k) (hc : c ≠ 0)
    (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r) :
    (∀ s ∈ Ioo (0 : ℝ) (π / r),
        HasDerivAt (ftCofactorAlong (ftRootPoly c a) r (ftBranchZLower a c r (n - 1))
          (ftTauArc a r (n - 1) x₁))
          (ftArcCofactorDeriv a c r x₁ s) s)
      ∧ ContinuousOn (ftArcCofactorDeriv a c r x₁) (Ioo (0 : ℝ) (π / r))
      ∧ (∀ s ∈ Ioo (0 : ℝ) (π / r),
          ftCofactorAlong (ftRootPoly c a) r (ftBranchZLower a c r (n - 1))
            (ftTauArc a r (n - 1) x₁) s ≠ 0) := by
  have hb : ∀ θ ∈ Ioo (0 : ℝ) (π / r), FTBranchAt a r (n - 1) θ :=
    fun θ hθ => ftBranchAt_of_arc_principal hn ha hr hnr hθ
  obtain ⟨hγd0, -, -, -⟩ := ft_geometry_group hn ha hr hnr hb x₁ 0
  rw [← ftTauArc_eq_ftTauArcAt] at hγd0
  have hstate := ft_branch_state_arc (x₁ := x₁) hn ha hc hr hnr
  have hγ0 : ∀ s ∈ Ioo (0 : ℝ) (π / r),
      ftPrincipal (ftTauArc a r (n - 1) x₁) s ≠ 0 := fun s hs => (hstate s hs).1
  have hroot : ∀ s ∈ Ioo (0 : ℝ) (π / r),
      (ftDen (ftRootPoly c a) r ((ftBranchZLower a c r (n - 1) s : ℝ) : ℂ)).eval
        (ftPrincipal (ftTauArc a r (n - 1) x₁) s) = 0 := fun s hs => (hstate s hs).2.1
  refine ⟨fun s hs => hasDerivAt_ftCofactorAlong hr isOpen_Ioo hs (hγd0 s hs) hγ0 hroot,
    ?_, fun s hs => ftCofactorAlong_ne_zero hr (hstate s hs).1 (hstate s hs).2.1
      (hstate s hs).2.2⟩
  refine continuousOn_ftCofactorAlongDeriv (fun s hs => ?_) (fun s hs => ?_) hγ0
  · exact (hγd0 s hs).continuousAt.continuousWithinAt
  · exact (continuousAt_ftGammaDeriv hn ha hr hs hb).continuousWithinAt

/-- **`hWd` and `hWc` at the general pencil**, for every weight.  `W = -B(γ)/S`, so the
quotient rule over the cofactor group gives both — and it reaches the amplitude's own
zeros, since what must not vanish is `S` and not `W`. -/
theorem ft_amplitude_group (B : Polynomial ℂ) (hn : 0 < n) (ha : ∀ k, 0 < a k)
    (hc : c ≠ 0) (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r) :
    (∀ s ∈ Ioo (0 : ℝ) (π / r),
        HasDerivAt (fun x => ftAmp (ftRootPoly c a) B r
          ((ftBranchZLower a c r (n - 1) x : ℝ) : ℂ)
          (ftPrincipal (ftTauArc a r (n - 1) x₁) x))
          (ftArcAmpDeriv a B c r x₁ s) s)
      ∧ ContinuousOn (ftArcAmpDeriv a B c r x₁) (Ioo (0 : ℝ) (π / r)) := by
  have hb : ∀ θ ∈ Ioo (0 : ℝ) (π / r), FTBranchAt a r (n - 1) θ :=
    fun θ hθ => ftBranchAt_of_arc_principal hn ha hr hnr hθ
  obtain ⟨hγd0, -, -, -⟩ := ft_geometry_group hn ha hr hnr hb x₁ 0
  rw [← ftTauArc_eq_ftTauArcAt] at hγd0
  obtain ⟨hSd, hSc, hS0⟩ := ft_cofactor_group (x₁ := x₁) hn ha hc hr hnr
  have hγc : ContinuousOn (ftPrincipal (ftTauArc a r (n - 1) x₁)) (Ioo (0 : ℝ) (π / r)) :=
    fun s hs => (hγd0 s hs).continuousAt.continuousWithinAt
  refine ⟨fun s hs => hasDerivAt_ftAmpAlong (hγd0 s hs) (hSd s hs) (hS0 s hs), ?_⟩
  refine continuousOn_ftAmpAlongDeriv hγc
    (fun s hs => (continuousAt_ftGammaDeriv hn ha hr hs hb).continuousWithinAt)
    (fun s hs => (hSd s hs).continuousAt.continuousWithinAt) hSc hS0

end ForgacsTran
