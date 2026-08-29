/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.CompositionLinks
import ForgacsTran.EndpointLowerRhoOne

/-!
# The viewing arc at a simple smallest zero

`CompositionLinks` supplies the geometry of the composition at the endpoint-extended
spectral parameter `ftBranchZLower`, whose value at `0` is the `2 ≤ ρ` endpoint `g(x_1) = 0`.
At a simple smallest zero the branch arrives at a critical point strictly inside the first
gap instead, so the parameter is `EndpointLowerRhoOne.ftBranchZLowerAt` with that value
supplied.

The three statements below are the same three facts at the parameterized spelling.  They
are one rewrite each: `ftBranchZLowerAt_agree` says the two extensions agree wherever
`θ > 0`, and the viewing arc is open, so **the endpoint value cannot enter** — which is
exactly why the composition at `ρ = 1` needs no new geometry, only the endpoint's identity.

The arc is open for a reason and not for convenience: at `π/r` the branch radius vanishes
and the spectral parameter has already diverged, so the closed-arc forms of these
statements are false (`EndpointArcObstruction`).

## Main statements

* `strictMonoOn_ftBranchZLowerAt_Ioo`, `continuousOn_ftBranchZLowerAt_Ioo`,
  `ftBranchZLowerAt_pos` — the spectral parameter's three facts on the open arc, at an
  arbitrary supplied endpoint value.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, `thm:FT-geometry`, `eq:ab-def`.

## Tags

viewing arc, simple zero, lower endpoint, spectral parameter
-/

open Polynomial Set Real

namespace ForgacsTran

variable {n r : ℕ} {a : Fin n → ℝ} {c aEnd : ℝ}

/-- **`z` is strictly increasing on the open viewing arc**, whatever endpoint value the
extension carries: off `0` the two extensions agree, and `0` is not on the arc. -/
theorem strictMonoOn_ftBranchZLowerAt_Ioo (hn : 0 < n) (ha : ∀ k, 0 < a k) (hc : 0 < c)
    (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r) :
    StrictMonoOn (ftBranchZLowerAt a c r (n - 1) aEnd) (Ioo 0 (π / r)) := by
  obtain ⟨-, -, hmono, -⟩ := ft_branch_supplies (a := a) (c := c) hn ha hc hr hnr
  intro x hx y hy hxy
  rw [ftBranchZLowerAt_agree a c r (n - 1) aEnd hx.1,
    ftBranchZLowerAt_agree a c r (n - 1) aEnd hy.1]
  exact hmono hx hy hxy

/-- **`z` is continuous on the open viewing arc**, whatever endpoint value it carries. -/
theorem continuousOn_ftBranchZLowerAt_Ioo (hn : 0 < n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r)
    (hnr : 2 ≤ n ∨ 2 ≤ r) :
    ContinuousOn (ftBranchZLowerAt a c r (n - 1) aEnd) (Ioo 0 (π / r)) := by
  refine (continuousOn_ftBranchZ (a := a) c hn ha hr hnr).congr fun θ hθ => ?_
  exact ftBranchZLowerAt_agree a c r (n - 1) aEnd hθ.1

/-- **`z > 0` on the open viewing arc**, whatever endpoint value it carries. -/
theorem ftBranchZLowerAt_pos (hn : 0 < n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r)
    (hnr : 2 ≤ n ∨ 2 ≤ r) {θ : ℝ} (hθ : θ ∈ Ioo 0 (π / r)) :
    0 < ftBranchZLowerAt a c r (n - 1) aEnd θ := by
  rw [ftBranchZLowerAt_agree a c r (n - 1) aEnd hθ.1]
  exact ftBranchZ_pos_principal hn ha hc hr hnr hθ

end ForgacsTran
