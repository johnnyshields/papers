/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.FTGeometryAssembly
import ForgacsTran.FTMinModulus.UpperEndpoint
import ForgacsTran.FTBranchZMono
import ForgacsTran.FTBranchLemma5
import ForgacsTran.PencilIndex

/-!
# `thm:FT-geometry` at the constructed branch

`FTGeometryAssembly.ft_geometry` takes the parametrization of `eq:principal-pair`
as seven hypotheses on a pair of abstract functions `z, τ`.  Those hypotheses are
what `thm:FT-geometry` *asserts*, so a theorem that assumes them repackages the
statement rather than proving it.

This module supplies them at the objects the tree actually constructs —
`ftTau a r (n-1)` and `ftBranchZ a c r (n-1)`, on the admissible class
`Q = c∏_k(a_k - t)` with every `a_k > 0` — and calls `ft_geometry` with them.
Five of the seven are discharged outright:

| `ft_geometry` binder | discharged by |
|---|---|
| `hbranch`, `hτpos` | `ft_branch_root_and_pos` |
| `hzmono` | `ftBranchZ_strictMonoOn` |
| `hzcont` | `continuousOn_ftBranchZ` |
| `hza` | `exists_tendsto_ftBranchZ_arc_zero` |

Two are named as hypotheses of `ft_geometry_at_branch`, and each is a statement
about the constructed branch rather than about an assumed one, so neither can be
met by choosing convenient functions:

* `hzb` — the upper-endpoint limit of `z`.  This one is **discharged**, in both
  conventions of `eq:ab-def`: `exists_tendsto_ftBranchZ_arc_end_pi` at `r = 1`
  and `tendsto_ftBranchZ_atTop_arc_end` for `2 ≤ r`, resting on the
  upper-endpoint radius limits `exists_tendsto_ftTau_nhdsLT_pi` and
  `tendsto_ftTau_nhdsLT_upper`.  `ft_geometry_at_branch_of_three_le` and
  `ft_geometry_at_branch_unbounded_of_two_le` are the one-binder forms that
  result.
* `hmin` — the minimum-modulus assertion, `Forgacs2017RationalDenominator`
  Props. 1--2.  `FTBranchZMono.ftProp1_angle_eq` closes their Prop. 1 for the
  constructed branch, and `FTMinModulus.Propositions` carries the distance-product
  machinery of Prop. 2, but nothing assembles them into the pointwise gap.  It is
  the last analytic binder between this tree and an unconditional
  `thm:FT-geometry`.

Stating them this way is what makes the gap measurable: the reduction is checked
by the elaborator rather than asserted in a table, and the survivor is exactly the
statement a later pass has to prove.  Seven analytic binders on abstract functions
became two here and one in `FTBranchEndpointUpper`, and the one left is `hmin`.

## Main statements

* `ft_geometry_at_branch` — `thm:FT-geometry` at the constructed branch, in the
  finite upper-endpoint convention of `eq:ab-def` (`r = 1`).
* `ft_geometry_at_branch_unbounded` — the same in the `b = +∞` convention.
* `natDegree_ftRootPoly` — the pencil has degree `n` over `ℂ`, which is what
  `FTGeometryBoundary`'s degree count and `InteriorSupply`'s root enumeration
  read the zero count off.
-/

namespace ForgacsTran

open Real Polynomial Set

/-- The complex pencil has degree `n`, like its real model: `algebraMap ℝ ℂ` is
injective, so mapping it changes no coefficient's vanishing. -/
theorem natDegree_ftRootPoly {n : ℕ} {c : ℝ} (hc : c ≠ 0) (a : Fin n → ℝ) :
    (ftRootPoly c a).natDegree = n := by
  have hmap : ftRootPoly c a = (ftRootPolyReal c a).map (algebraMap ℝ ℂ) := by
    rw [ftRootPoly, ftRootPolyReal, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_prod]
    simp
  rw [hmap, Polynomial.natDegree_map_eq_of_injective (algebraMap ℝ ℂ).injective,
    natDegree_ftRootPolyReal hc]

/-- The four binders of `ft_geometry` the constructed branch supplies without any
further hypothesis: the principal pair is a zero of the pencil at its own
spectral value, the radius is positive, and `z` is continuous and strictly
increasing along the viewing arc. -/
theorem ft_branch_supplies {n r : ℕ} {a : Fin n → ℝ} {c : ℝ} (hn : 0 < n)
    (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r) :
    (∀ θ ∈ Ioo 0 (π / r),
        (ftDen (ftRootPoly c a) r ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ)).eval
          (ftPrincipal (ftTau a r (n - 1)) θ) = 0)
      ∧ (∀ θ ∈ Ioo 0 (π / r), 0 < ftTau a r (n - 1) θ)
      ∧ StrictMonoOn (ftBranchZ a c r (n - 1)) (Ioo 0 (π / r))
      ∧ ContinuousOn (ftBranchZ a c r (n - 1)) (Ioo 0 (π / r)) := by
  have hpar : Even (n + (n - 1) + 1) := even_add_pred_add_one hn
  have hb : ∀ θ ∈ Ioo 0 (π / r), FTBranchAt a r (n - 1) θ := fun θ hθ =>
    ftBranchAt_of_arc_principal hn ha hr hnr hθ
  obtain ⟨hroot, hpos⟩ := ft_branch_root_and_pos c hn ha hr hnr
  exact ⟨hroot, hpos, ftBranchZ_strictMonoOn hn ha hc hr hpar hb,
    continuousOn_ftBranchZ c hn ha hr hnr⟩

/-- **`thm:FT-geometry` at the constructed branch**, in the finite
upper-endpoint convention of `eq:ab-def`.

Compared with `FTGeometryAssembly.ft_geometry` this carries no `hbranch`,
`hτpos`, `hzmono`, `hzcont` or `hza`: those are produced from the admissible
class alone.  The two hypotheses left are the upper-endpoint limit and the
minimum-modulus gap, both stated about `ftTau`/`ftBranchZ` themselves. -/
theorem ft_geometry_at_branch {n r : ℕ} {a : Fin n → ℝ} {c : ℝ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r) {b : ℝ}
    (hzb : Filter.Tendsto (ftBranchZ a c r (n - 1))
      (nhdsWithin (π / r) (Ioo 0 (π / r))) (nhds b))
    (hmin : FTMinModulusGap (ftRootPoly c a) r (ftBranchZ a c r (n - 1)) (ftTau a r (n - 1))) :
    ∃ za : ℝ,
      ftBranchZ a c r (n - 1) '' Ioo 0 (π / r) = Ioo za b
        ∧ FTPrincipalPair (ftRootPoly c a) r (ftBranchZ a c r (n - 1)) (ftTau a r (n - 1))
        ∧ FTPrincipalDisk (ftRootPoly c a) r (ftBranchZ a c r (n - 1)) (ftTau a r (n - 1)) := by
  obtain ⟨hroot, hpos, hmono, hcont⟩ :=
    ft_branch_supplies (a := a) (c := c) (by omega) ha hc hr (Or.inl hn2)
  obtain ⟨za, hza⟩ := exists_tendsto_ftBranchZ_arc_zero c hn2 ha hr hc
  exact ⟨za, ft_geometry (hasRealCoeffs_ftRootPoly c a) hr hroot hpos hmono hcont
    hza hzb hmin⟩

/-- **`thm:FT-geometry` at the constructed branch, unbounded convention.**  The
`b = +∞` of `eq:ab-def`, which that display reaches exactly when `r > 1`.  The
hypothesis list is `ft_geometry_at_branch`'s with the upper limit replaced by
divergence, and the conclusion is the same three clauses over the ray. -/
theorem ft_geometry_at_branch_unbounded {n r : ℕ} {a : Fin n → ℝ} {c : ℝ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r)
    (hzb : Filter.Tendsto (ftBranchZ a c r (n - 1))
      (nhdsWithin (π / r) (Ioo 0 (π / r))) Filter.atTop)
    (hmin : FTMinModulusGap (ftRootPoly c a) r (ftBranchZ a c r (n - 1)) (ftTau a r (n - 1))) :
    ∃ za : ℝ,
      ftBranchZ a c r (n - 1) '' Ioo 0 (π / r) = Ioi za
        ∧ FTPrincipalPair (ftRootPoly c a) r (ftBranchZ a c r (n - 1)) (ftTau a r (n - 1))
        ∧ FTPrincipalDisk (ftRootPoly c a) r (ftBranchZ a c r (n - 1)) (ftTau a r (n - 1)) := by
  obtain ⟨hroot, hpos, hmono, hcont⟩ :=
    ft_branch_supplies (a := a) (c := c) (by omega) ha hc hr (Or.inl hn2)
  obtain ⟨za, hza⟩ := exists_tendsto_ftBranchZ_arc_zero c hn2 ha hr hc
  exact ⟨za, ft_geometry_unbounded (hasRealCoeffs_ftRootPoly c a) hr hroot hpos hmono
    hcont hza hzb hmin⟩

end ForgacsTran
