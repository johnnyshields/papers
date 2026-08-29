/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.EndpointUpperPackage

/-!
# The lower endpoint's corner, at every pencil

`ftTauArcAt` repairs the upper endpoint's convention: `ftTauArc` is defined to be `0`
past `π/r`, which is the limit only when the branch runs into the origin, and the
parameterized form carries the finite value an `r = 1` arc ends at.

**The lower endpoint has the mirror defect and the repair does not reach it.**  Both
extensions are built on

    ftTauLower a r l x₁ θ = if 0 < θ then ftTau a r l θ else x₁,

so to the left of `0` the radius is the **constant** `x₁` while to the right it is the
branch.  A two-sided derivative at `0` therefore exists only if the branch enters with
slope `0`, and generically it does not: at the cubic pencil `τ(θ) = 1 - |θ|/√3 + O(θ²)`
to the right, so the right slope is `-√3/3` against a left slope of `0`
(`../scripts/check_cubic_branch_corner.py`, C2).

So `BranchSupply`'s `hγd`, `hd2` and `hc2` — which ask for the derivatives on an open set
containing the **closed** arc — remain unsatisfiable at the lower end after the upper one
is repaired.  The statement below is pencil-free: it names the exact condition, so a
caller can see at once whether its branch escapes.

Nothing here says the closed-arc group is unreachable.  It says the two ends need
separate repairs, and that a one-sided hypothesis at `0` is what the geometry supports.

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, `thm:FT-geometry`,
`lem:principal-endpoint-regularity`.

## Tags

lower endpoint, branch corner, arc extension, Forgács–Tran
-/

namespace ForgacsTran

open Set Real

/-- To the left of `0` the arc extension is the constant `x₁`. -/
theorem ftTauLower_of_nonpos {n : ℕ} (a : Fin n → ℝ) (r l : ℕ) (x₁ : ℝ) {θ : ℝ}
    (hθ : θ ≤ 0) : ftTauLower a r l x₁ θ = x₁ := by
  rw [ftTauLower, if_neg (not_lt.2 hθ)]

/-- Hence its left derivative at `0` is `0`. -/
theorem hasDerivWithinAt_ftTauLower_Iic {n : ℕ} (a : Fin n → ℝ) (r l : ℕ) (x₁ : ℝ) :
    HasDerivWithinAt (ftTauLower a r l x₁) 0 (Iic (0 : ℝ)) 0 :=
  (hasDerivAt_const (0 : ℝ) x₁).hasDerivWithinAt.congr
    (fun _y hy => ftTauLower_of_nonpos a r l x₁ hy) (ftTauLower_of_nonpos a r l x₁ le_rfl)

/-- **The arc extension has a corner at `0` unless the branch enters with slope zero.**
The left side is a plateau and the right side is the branch, so a two-sided derivative
forces the branch's entry slope to vanish.

This is the lower-endpoint twin of `ftTauArc`'s upper-endpoint convention, and it is not
repaired by carrying the correct endpoint value: `ftTauArcAt` differs from `ftTauArc`
only past `π/r`, while this is at `0`. -/
theorem not_hasDerivAt_ftTauLower_zero {n : ℕ} {a : Fin n → ℝ} {r l : ℕ} {x₁ c : ℝ}
    (hc : c ≠ 0)
    (hright : HasDerivWithinAt (ftTauLower a r l x₁) c (Ici (0 : ℝ)) 0) (d : ℝ) :
    ¬ HasDerivAt (ftTauLower a r l x₁) d 0 := by
  intro hd
  have hUi : UniqueDiffWithinAt ℝ (Ici (0 : ℝ)) 0 := uniqueDiffOn_Ici 0 0 (by simp)
  have hUc : UniqueDiffWithinAt ℝ (Iic (0 : ℝ)) 0 := uniqueDiffOn_Iic 0 0 (by simp)
  have h1 : c = d := hUi.eq_deriv _ hright hd.hasDerivWithinAt
  have h2 : (0 : ℝ) = d :=
    hUc.eq_deriv _ (hasDerivWithinAt_ftTauLower_Iic a r l x₁) hd.hasDerivWithinAt
  exact hc (by rw [h1, ← h2])

/-- The same for `ftTauArc`, which agrees with `ftTauLower` on a neighbourhood of `0`. -/
theorem not_hasDerivAt_ftTauArc_zero {n : ℕ} {a : Fin n → ℝ} {r l : ℕ} {x₁ c : ℝ}
    (hr : 0 < r) (hc : c ≠ 0)
    (hright : HasDerivWithinAt (ftTauLower a r l x₁) c (Ici (0 : ℝ)) 0) (d : ℝ) :
    ¬ HasDerivAt (ftTauArc a r l x₁) d 0 := by
  have hpos : (0 : ℝ) < π / r := by
    have : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
    positivity
  have hEq : ftTauArc a r l x₁ =ᶠ[nhds (0 : ℝ)] ftTauLower a r l x₁ := by
    filter_upwards [Iio_mem_nhds hpos] with t ht
    exact ftTauArc_eq_lower a r l x₁ ht
  intro hd
  exact not_hasDerivAt_ftTauLower_zero hc hright d (hd.congr_of_eventuallyEq hEq.symm)

end ForgacsTran
