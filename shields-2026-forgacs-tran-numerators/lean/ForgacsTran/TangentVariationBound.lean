/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.BranchSupply
import ForgacsTran.PhaseTangency

/-!
# The tangent angle's variation, at every base point

`BranchSupply.exists_uniform_ftBranchSupply` asks for

    hKvar : ∀ c ∈ Ioo 0 (π/r),
      eVariationOn (polarAngle dγ d2γ 0 c) (Ioo 0 (π/r)) ≤ ENNReal.ofReal Kγ

— the tangent's total turning, capped uniformly in the base point.  This produces it.

**The `∀ c` costs nothing, and not because the branches are related.**  One might expect to
prove the bound at one base point and transport it along
`PolarAngleBase.polarAngle_base_shift`, since the branches differ by a constant.  No
transport is needed: `polarAngle`'s **derivative does not mention the base point at all**
— it is `Im(γ''/γ')` whichever `c` the lift starts from — so the derivative bound that
gives the variation is one statement, and `∀ c` is discharged by `intro`.

So the hypothesis is a bound on `|Im(γ''/γ')|` over the open arc, which is
`ArcPhaseBound`'s own shape one object over: there it is `Im(W'/W)` for the amplitude,
here `Im(γ''/γ')` for the tangent.

**The closed sub-interval is where the base point and the evaluation point meet.**
`ViewingAngle.hasDerivAt_polarAngle_base` is stated on a closed interval containing both,
and the open arc supplies one for each pair — `[min c x, max c x]` — so nothing is asked
at the ends of the arc.

Sorry-free.

* `im_div_eq_wedge_div_normSq` — the tangent ratio as `wedge/‖·‖²`, which is how a
  curvature identity becomes this bound.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`,
`cor:linear-phase-variation`, `eq:linear-phase-variation`, `eq:viewing-angle-bound`.

## Tags

viewing angle, bounded variation, tangent turning, Forgács–Tran
-/

namespace ForgacsTran

open Set

/-- **`hKvar`, from a bound on `|Im(γ''/γ')|` over the open arc.**  The cap is
`κ·(b-a)`, the bound times the arc's length, which is what a derivative bound gives and
is `M`-free. -/
theorem eVariationOn_polarAngle_tangent_le {dγ d2γ : ℝ → ℂ} {a b κ : ℝ}
    (hd2 : ∀ s ∈ Ioo a b, HasDerivAt dγ (d2γ s) s)
    (hc2 : ContinuousOn d2γ (Ioo a b))
    (hreg : ∀ s ∈ Ioo a b, dγ s ≠ 0) (hκ : 0 ≤ κ)
    (hbd : ∀ s ∈ Ioo a b, |(d2γ s / dγ s).im| ≤ κ) :
    ∀ c ∈ Ioo a b,
      eVariationOn (polarAngle dγ d2γ 0 c) (Ioo a b) ≤ ENNReal.ofReal (κ * (b - a)) := by
  intro c hc
  refine eVariationOn_le_of_abs_deriv_le hκ (fun x hx => ?_) hbd
  have hpq : Icc (min c x) (max c x) ⊆ Ioo a b := by
    intro s hs
    exact ⟨lt_of_lt_of_le (lt_min hc.1 hx.1) hs.1,
      lt_of_le_of_lt hs.2 (max_lt hc.2 hx.2)⟩
  have h := hasDerivAt_polarAngle_base (γ := dγ) (dγ := d2γ) (β := 0)
    isOpen_Ioo hpq (fun s hs => hd2 s hs) hc2 (fun s hs => hreg s (hpq hs))
    ⟨min_le_left _ _, le_max_left _ _⟩ ⟨min_le_right _ _, le_max_right _ _⟩
  simpa using h

/-- The same at a named cap, which is the shape `exists_uniform_ftBranchSupply` states. -/
theorem eVariationOn_polarAngle_tangent_le_of_le {dγ d2γ : ℝ → ℂ} {a b κ Kγ : ℝ}
    (hd2 : ∀ s ∈ Ioo a b, HasDerivAt dγ (d2γ s) s)
    (hc2 : ContinuousOn d2γ (Ioo a b))
    (hreg : ∀ s ∈ Ioo a b, dγ s ≠ 0) (hκ : 0 ≤ κ)
    (hbd : ∀ s ∈ Ioo a b, |(d2γ s / dγ s).im| ≤ κ)
    (hle : κ * (b - a) ≤ Kγ) :
    ∀ c ∈ Ioo a b,
      eVariationOn (polarAngle dγ d2γ 0 c) (Ioo a b) ≤ ENNReal.ofReal Kγ := fun c hc =>
  le_trans (eVariationOn_polarAngle_tangent_le hd2 hc2 hreg hκ hbd c hc)
    (ENNReal.ofReal_le_ofReal hle)

/-! ### The tangent ratio through the wedge -/

/-- **`Im(u/w)` is the wedge over the squared modulus.**  `u/w = u·conj w/‖w‖²`, and the
imaginary part of the numerator is `wedge u w`.  This is what turns a curvature identity —
which is a statement about `wedge γ'' γ'` — into the bound `eVariationOn_polarAngle_tangent_le`
consumes. -/
theorem im_div_eq_wedge_div_normSq (u w : ℂ) :
    (u / w).im = wedge u w / Complex.normSq w := by
  rw [Complex.div_im, wedge, sub_div]

end ForgacsTran
