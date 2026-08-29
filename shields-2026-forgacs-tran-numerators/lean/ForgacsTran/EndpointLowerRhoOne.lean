/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.EndpointUpperGeneralN
import ForgacsTran.SpectralFiber

/-!
# The `ρ = 1` lower endpoint: the extension `hk₀` needs

At `2 ≤ ρ` the lower endpoint of the viewing arc is the smallest root `x₁`, the
branch radius runs into it, and the spectral parameter runs into
`g(x₁) = -Q(x₁)/x₁^r = 0` because `x₁` is a zero of `Q`.  `EndpointPackage`
extends both to the closed interval on that basis.

At `ρ = 1` neither endpoint value is the same.  The radius runs into the critical
point `t_a`, which is strictly inside `(x₁, x₂)` and is NOT a zero of `Q`, and the
parameter runs into `a_end = -Q(t_a)/t_a^r`, which is not `0`.

**The two extensions are not symmetric, and that is the defect.**
`ftTauLower a r l x₁` takes its endpoint value as an ARGUMENT — the name `x₁` is
what the `2 ≤ ρ` caller supplies, not part of the definition — so a `ρ = 1`
caller may pass `t_a` and get the right function.  `ftBranchZLower a c r l`
hardcodes `0`.  So at `ρ = 1` the extended parameter is wrong at the single point
`θ = 0`, and `thm:weighted-dominance`'s

  `hk₀ : 1 ≤ (ftDen Q r (z 0)).rootMultiplicity te₀`

becomes the claim `Q(t_a) = 0`, which is FALSE — `t_a` is a critical point of `g`,
not a root of `Q`.  Measured at three pencils in `scripts/`: `Q(t_a)` is `-0.613`,
`-0.375`, `-0.966`.

This is a FALSE BINDER rather than a missing lemma, so nothing in the tree fails:
a `ρ = 1` composition would typecheck against a hypothesis nobody can discharge.

This module supplies the parameterized extension without touching
`EndpointPackage`, and shows the existing one is its `0` case, so no consumer of
`ftBranchZLower` sees any change.

## Main statements

* `ftBranchZLowerAt` — the extension with the endpoint value as an argument.
* `ftBranchZLower_eq_ftBranchZLowerAt` — the existing definition is the `a = 0`
  case, which is why this is additive rather than a change.
* `eval_ftDen_branch_value` — at any nonzero `s₀`, the pencil at that point's own
  branch value vanishes there.  This is what makes `hk₀` true once the endpoint
  value is right, and at `2 ≤ ρ` it degenerates to `Q(x₁) = 0`.

## References

* `../../shields-2026-forgacs-tran-numerators.tex`, `thm:weighted-dominance`,
  `eq:ab-def`.

## Tags

lower endpoint, rho = 1, endpoint extension, false binder
-/

namespace ForgacsTran

open Polynomial

/-- The spectral parameter extended to the closed endpoint interval, with the
endpoint value supplied rather than assumed.  `EndpointPackage.ftBranchZLower` is
this at `a = 0`, which is the `2 ≤ ρ` value `g(x₁) = 0`. -/
noncomputable def ftBranchZLowerAt {n : ℕ} (a : Fin n → ℝ) (c : ℝ) (r l : ℕ)
    (aEnd : ℝ) : ℝ → ℝ :=
  fun θ => if 0 < θ then ftBranchZ a c r l θ else aEnd

theorem ftBranchZLowerAt_agree {n : ℕ} (a : Fin n → ℝ) (c : ℝ) (r l : ℕ) (aEnd : ℝ)
    {θ : ℝ} (hθ : 0 < θ) : ftBranchZLowerAt a c r l aEnd θ = ftBranchZ a c r l θ := by
  rw [ftBranchZLowerAt, if_pos hθ]

@[simp] theorem ftBranchZLowerAt_zero {n : ℕ} (a : Fin n → ℝ) (c : ℝ) (r l : ℕ)
    (aEnd : ℝ) : ftBranchZLowerAt a c r l aEnd 0 = aEnd := by
  rw [ftBranchZLowerAt, if_neg (lt_irrefl 0)]

/-- **The existing extension is the `a = 0` case.**  Nothing consuming
`ftBranchZLower` is affected by the parameterized form existing. -/
theorem ftBranchZLower_eq_ftBranchZLowerAt {n : ℕ} (a : Fin n → ℝ) (c : ℝ) (r l : ℕ) :
    ftBranchZLower a c r l = ftBranchZLowerAt a c r l 0 := rfl

/-- **The pencil at a point's own branch value vanishes there.**  With
`z = -Q(s₀)/s₀^r`, `D(·,z)` has `s₀` as a root, for any `s₀ ≠ 0` and any `r`.

This is what makes `hk₀` true once the endpoint value is the branch's own.  At
`2 ≤ ρ` it degenerates: `s₀ = x₁` is a zero of `Q`, so the branch value is `0` and
the statement reduces to `Q(x₁) = 0` — which is why the hardcoded `0` is invisible
there and false at `ρ = 1`. -/
theorem eval_ftDen_branch_value {Q : Polynomial ℂ} {r : ℕ} {s₀ : ℂ} (hs₀ : s₀ ≠ 0) :
    (ftDen Q r (-(Q.eval s₀) / s₀ ^ r)).eval s₀ = 0 := by
  rw [ftDen_eval]
  field

end ForgacsTran
