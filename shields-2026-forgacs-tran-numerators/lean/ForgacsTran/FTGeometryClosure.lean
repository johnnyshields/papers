/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.FTMinModulus.PrincipalGap
import ForgacsTran.FTBranchEndpointUpper
import ForgacsTran.FTMinModulus.RealCritical

/-!
# `thm:FT-geometry` at the constructed branch, with one hypothesis

`FTGeometryBranch` reduced `ft_geometry`'s seven analytic binders to two by
calling it at the constructed `ftTau`/`ftBranchZ` instead of at assumed
functions; `FTBranchEndpointUpper` discharged the upper-endpoint limit, and
`FTMinModulus.PrincipalGap` reduced the minimum-modulus gap to the argument
condition `hcone`.  This module joins them, so the count is checked by the
elaborator rather than read off three module headers.

Both conventions of `eq:ab-def` are reached, and in each the only hypothesis
beyond the admissible class is `hcone`:

* `ft_geometry_at_branch_of_cone_pi` — the finite `b`, at `r = 1`.
* `ft_geometry_unbounded_at_branch_of_cone` — `b = +∞`, at `2 ≤ r`.

## Why the route departs from the paper's

`Forgacs2017RationalDenominator` closes its Prop. 1 by bracketing the radius
between two values of the *index-`l`* branch and walking that branch.  That needs
the index-`l` branch to exist across the arc, and it does not: it lives only on an
initial segment, and `not_arc_wide_of_two_mul_lt` exhibits an arc angle outside it
whenever `2 * r < n`.  A statement carrying the arc-wide index condition is
therefore **vacuous** there rather than merely unproved — which at `r = 1` would
have left the cubic pencil the rest of this tree is built on outside every
minimum-modulus statement.

`ftProp1_closing_principal` runs the squeeze on the *principal* index instead, in
the opposite direction, evaluating the index-`l` branch only at the single angle
where it is known to exist.  The principal branch exists across the whole arc with
no hypothesis, so the intermediate value step and both monotonicities apply
unconditionally, and the index condition disappears rather than being weakened.

## Main statements

* `ft_geometry_at_branch_of_cone_pi` — `thm:FT-geometry` at the constructed
  branch, finite upper-endpoint convention, `hcone` the only analytic binder.
* `ft_geometry_unbounded_at_branch_of_cone` — the same in the `b = +∞`
  convention.
-/

namespace ForgacsTran

open Real Set

/-- **`thm:FT-geometry` at the constructed branch, finite upper-endpoint
convention, one analytic hypothesis.**  This is the convention `eq:ab-def`
reaches at `r = 1`, and the one the tree's own witnesses use.  The upper-endpoint
limit is `exists_tendsto_ftBranchZ_arc_end_pi` and the minimum-modulus gap is
`ft_minModulus_at_branch`, so nothing about the branch is assumed beyond the
argument condition `hcone`. -/
theorem ft_geometry_at_branch_of_cone_pi {n : ℕ} {a : Fin n → ℝ} {c : ℝ}
    (hn3 : 3 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c)
    (hcone : ∀ θ ∈ Ioo (0 : ℝ) (π / ((1 : ℕ) : ℝ)), ∀ w : ℂ,
      (ftDen (ftRootPoly c a) 1 ((ftBranchZ a c 1 (n - 1) θ : ℝ) : ℂ)).eval w = 0 →
        ‖w‖ ≤ ftTau a 1 (n - 1) θ → |Complex.arg w| ∈ Ioo 0 (π / ((1 : ℕ) : ℝ))) :
    ∃ za b : ℝ,
      ftBranchZ a c 1 (n - 1) '' Ioo 0 (π / ((1 : ℕ) : ℝ)) = Ioo za b
        ∧ (∀ θ ∈ Ioo 0 (π / ((1 : ℕ) : ℝ)),
            (ftDen (ftRootPoly c a) 1 ((ftBranchZ a c 1 (n - 1) θ : ℝ) : ℂ)).eval
                (ftPrincipal (ftTau a 1 (n - 1)) θ) = 0
              ∧ (ftDen (ftRootPoly c a) 1 ((ftBranchZ a c 1 (n - 1) θ : ℝ) : ℂ)).eval
                  ((starRingEnd ℂ) (ftPrincipal (ftTau a 1 (n - 1)) θ)) = 0
              ∧ ‖ftPrincipal (ftTau a 1 (n - 1)) θ‖ = ftTau a 1 (n - 1) θ
              ∧ ‖(starRingEnd ℂ) (ftPrincipal (ftTau a 1 (n - 1)) θ)‖
                  = ftTau a 1 (n - 1) θ)
        ∧ (∀ θ ∈ Ioo 0 (π / ((1 : ℕ) : ℝ)), ∀ w : ℂ,
            (ftDen (ftRootPoly c a) 1 ((ftBranchZ a c 1 (n - 1) θ : ℝ) : ℂ)).eval w = 0 →
              ‖w‖ ≤ ftTau a 1 (n - 1) θ →
                w = ftPrincipal (ftTau a 1 (n - 1)) θ
                  ∨ w = (starRingEnd ℂ) (ftPrincipal (ftTau a 1 (n - 1)) θ)) :=
  ft_geometry_at_branch_of_three_le hn3 ha hc
    (ft_minModulus_at_branch (by omega) ha hc le_rfl hcone)

/-- **`thm:FT-geometry` at the constructed branch, unbounded convention, one
analytic hypothesis.**  The `b = +∞` of `eq:ab-def`, which that display reaches
exactly when `r > 1`. -/
theorem ft_geometry_unbounded_at_branch_of_cone {n r : ℕ} {a : Fin n → ℝ} {c : ℝ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 2 ≤ r)
    (hcone : ∀ θ ∈ Ioo (0 : ℝ) (π / r), ∀ w : ℂ,
      (ftDen (ftRootPoly c a) r ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ)).eval w = 0 →
        ‖w‖ ≤ ftTau a r (n - 1) θ → |Complex.arg w| ∈ Ioo 0 (π / r)) :
    ∃ za : ℝ,
      ftBranchZ a c r (n - 1) '' Ioo 0 (π / r) = Ioi za
        ∧ (∀ θ ∈ Ioo 0 (π / r),
            (ftDen (ftRootPoly c a) r ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ)).eval
                (ftPrincipal (ftTau a r (n - 1)) θ) = 0
              ∧ (ftDen (ftRootPoly c a) r ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ)).eval
                  ((starRingEnd ℂ) (ftPrincipal (ftTau a r (n - 1)) θ)) = 0
              ∧ ‖ftPrincipal (ftTau a r (n - 1)) θ‖ = ftTau a r (n - 1) θ
              ∧ ‖(starRingEnd ℂ) (ftPrincipal (ftTau a r (n - 1)) θ)‖
                  = ftTau a r (n - 1) θ)
        ∧ (∀ θ ∈ Ioo 0 (π / r), ∀ w : ℂ,
            (ftDen (ftRootPoly c a) r ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ)).eval w = 0 →
              ‖w‖ ≤ ftTau a r (n - 1) θ →
                w = ftPrincipal (ftTau a r (n - 1)) θ
                  ∨ w = (starRingEnd ℂ) (ftPrincipal (ftTau a r (n - 1)) θ)) :=
  ft_geometry_at_branch_unbounded hn2 ha hc (by omega)
    (tendsto_ftBranchZ_atTop_arc_end hn2 ha hc hr)
    (ft_minModulus_at_branch hn2 ha hc (by omega) hcone)

/-- **`thm:FT-geometry` at the constructed branch, with no analytic hypothesis at
all.**  At `r = 1` and a simple smallest zero, `hcone` is discharged by
`cone_at_branch_one`, so every binder of `ft_geometry` is supplied from the
admissible class: the pencil is `ftRootPoly c a`, the spectral parameter
`ftBranchZ`, the principal pair `ftPrincipal (ftTau …)`, and nothing about any of
them is posited.

One hypothesis sits beyond the admissible class: `3 ≤ n`, which is where the
route below stops rather than where the theorem does.  `n = 2` at `r = 1` is
`rem:quadratic-case`, and the cone route genuinely fails there —
`negDivPow_lt_ftBranchZ_pos` carries `¬(r = 1 ∧ n = 2)`, as does
`Forgacs2017RationalDenominator` Lemma 3.  The case is closed instead by a degree
count, in `FTGeometryBoundary.ft_geometry_at_branch_quadratic`: the pencil is
quadratic there, so the principal pair is the whole denominator.  There is no
restriction on the
multiplicity of the smallest zero — `ft_minModulus_at_branch_pi` splits by cases
at a minimizing index, and simple or repeated is exhaustive, so the union carries
neither branch's extra binder.  In particular `cubicQ = (1-t)^3`, where that zero
has multiplicity three, is covered. -/
theorem ft_geometry_at_branch_pi {n : ℕ} {a : Fin n → ℝ} {c : ℝ}
    (hn3 : 3 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) :
    ∃ za b : ℝ,
      ftBranchZ a c 1 (n - 1) '' Ioo 0 (π / ((1 : ℕ) : ℝ)) = Ioo za b
        ∧ (∀ θ ∈ Ioo 0 (π / ((1 : ℕ) : ℝ)),
            (ftDen (ftRootPoly c a) 1 ((ftBranchZ a c 1 (n - 1) θ : ℝ) : ℂ)).eval
                (ftPrincipal (ftTau a 1 (n - 1)) θ) = 0
              ∧ (ftDen (ftRootPoly c a) 1 ((ftBranchZ a c 1 (n - 1) θ : ℝ) : ℂ)).eval
                  ((starRingEnd ℂ) (ftPrincipal (ftTau a 1 (n - 1)) θ)) = 0
              ∧ ‖ftPrincipal (ftTau a 1 (n - 1)) θ‖ = ftTau a 1 (n - 1) θ
              ∧ ‖(starRingEnd ℂ) (ftPrincipal (ftTau a 1 (n - 1)) θ)‖
                  = ftTau a 1 (n - 1) θ)
        ∧ (∀ θ ∈ Ioo 0 (π / ((1 : ℕ) : ℝ)), ∀ w : ℂ,
            (ftDen (ftRootPoly c a) 1 ((ftBranchZ a c 1 (n - 1) θ : ℝ) : ℂ)).eval w = 0 →
              ‖w‖ ≤ ftTau a 1 (n - 1) θ →
                w = ftPrincipal (ftTau a 1 (n - 1)) θ
                  ∨ w = (starRingEnd ℂ) (ftPrincipal (ftTau a 1 (n - 1)) θ)) :=
  ft_geometry_at_branch_of_three_le hn3 ha hc
    (ft_minModulus_at_branch_pi hn3 ha hc)

end ForgacsTran
