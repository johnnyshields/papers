/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.CubicPhaseSupplyComposition
import ForgacsTran.CubicCollisionWitness

/-!
# The arc radius with its upper endpoint value carried

`EndpointUpperPackage.ftTauArc` extends the branch radius past the arc by

  `ftTauArc a r l x₁ θ = if θ < π/r then ftTauLower a r l x₁ θ else 0`,

and the `0` is the upper endpoint's limit **only when the branch runs into the
origin**, which is the `2 ≤ r` picture.  At `r = 1` the upper endpoint is finite —
`cubicTau π = 1/2` — so `ftTauArc` is discontinuous there
(`not_continuousAt_ftTauArc_cubic_pi`), and every hypothesis asking for `τ` to be
continuous on a neighbourhood of the closed arc is unsatisfiable at `r = 1`.

`ftTauArcAt` carries the endpoint value as a parameter, exactly as
`EndpointLowerRhoOne.ftBranchZLowerAt` carries the lower one, and
`ftTauArc a r l x₁ = ftTauArcAt a r l x₁ 0` holds by `rfl` — so the `2 ≤ r` case
keeps its present meaning as the `0` instance rather than being special-cased.

## The two endpoints are not symmetric, and the fix repairs only one of them

At the cubic pencil, with the endpoint value supplied:

* **Upper endpoint — fully repaired.**  `ftTauArcAt … (1/2)` agrees with `cubicTau`
  at `π`, and `cubicTauDeriv π = 0`, which is also the slope of the constant
  extension beyond `π`.  Value and derivative both match, so the corrected
  function is genuinely differentiable there.
* **Lower endpoint — one-sided, and no endpoint value can fix it.**  `ftTauLower`
  extends by the constant `x₁`, whose slope is `0`, while the branch arrives with
  `cubicTauDeriv 0 = -√3/3 ≠ 0`.  The *value* matches, so continuity holds; the
  derivative does not, so only `HasDerivWithinAt … (Ici 0)` can hold.

So the definition fix and the one-sided binders are answers to **different**
endpoints, and neither substitutes for the other.

## References

* `../../shields-2026-forgacs-tran-numerators.tex`, `eq:ab-def`,
  `lem:principal-endpoint-regularity`.

## Tags

branch radius, endpoint convention, one-sided derivative, Forgács–Tran
-/

namespace ForgacsTran

open Set Real

/-- The arc radius extended past `π/r` by a **prescribed** endpoint value rather
than by `0`.  `ftTauArc` is the `aEnd = 0` instance. -/
noncomputable def ftTauArcAt {n : ℕ} (a : Fin n → ℝ) (r l : ℕ) (x₁ aEnd : ℝ) :
    ℝ → ℝ :=
  fun θ => if θ < Real.pi / r then ftTauLower a r l x₁ θ else aEnd

/-- **The existing extension is the `aEnd = 0` case**, so nothing consuming
`ftTauArc` is affected by the parameterized form existing. -/
theorem ftTauArc_eq_ftTauArcAt {n : ℕ} (a : Fin n → ℝ) (r l : ℕ) (x₁ : ℝ) :
    ftTauArc a r l x₁ = ftTauArcAt a r l x₁ 0 := rfl

theorem ftTauArcAt_eq_lower {n : ℕ} (a : Fin n → ℝ) (r l : ℕ) (x₁ aEnd : ℝ) {θ : ℝ}
    (hθ : θ < Real.pi / r) : ftTauArcAt a r l x₁ aEnd θ = ftTauLower a r l x₁ θ := by
  rw [ftTauArcAt, if_pos hθ]

theorem ftTauArcAt_agree {n : ℕ} (a : Fin n → ℝ) (r l : ℕ) (x₁ aEnd : ℝ) {θ : ℝ}
    (hθ0 : 0 < θ) (hθ : θ < Real.pi / r) :
    ftTauArcAt a r l x₁ aEnd θ = ftTau a r l θ := by
  rw [ftTauArcAt_eq_lower a r l x₁ aEnd hθ, ftTauLower_agree a r l x₁ hθ0]

@[simp] theorem ftTauArcAt_zero {n : ℕ} (a : Fin n → ℝ) (r : ℕ) (l : ℕ) (x₁ aEnd : ℝ)
    (hr : 0 < Real.pi / r) : ftTauArcAt a r l x₁ aEnd 0 = x₁ := by
  rw [ftTauArcAt_eq_lower a r l x₁ aEnd hr, ftTauLower, if_neg (lt_irrefl 0)]

@[simp] theorem ftTauArcAt_arc_end {n : ℕ} (a : Fin n → ℝ) (r l : ℕ) (x₁ aEnd : ℝ) :
    ftTauArcAt a r l x₁ aEnd (Real.pi / r) = aEnd := by
  rw [ftTauArcAt, if_neg (lt_irrefl _)]

/-! ### At the cubic pencil, the corrected radius **is** the branch -/

/-- **The repair, at the cubic.**  With the upper endpoint value supplied,
`ftTauArcAt` agrees with `cubicTau` on the whole **closed** arc — the open arc by
`ftTauArc_eq_cubicTau_of_mem`, the lower end by `ftTauLower`'s own value, and the
upper end because the endpoint value is now `cubicTau π` rather than `0`. -/
theorem ftTauArcAt_eq_cubicTau {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) π) :
    ftTauArcAt ![1, 1, 1] 1 2 1 (1 / 2) θ = cubicTau θ := by
  have hpi : π / ((1 : ℕ) : ℝ) = π := pi_div_natCast_one
  rcases eq_or_lt_of_le hθ.1 with h0 | h0
  · rw [← h0, ftTauArcAt_zero _ _ _ _ _ (by rw [hpi]; exact pi_pos), cubicTau_zero]
  rcases eq_or_lt_of_le hθ.2 with hpi' | hpi'
  · rw [hpi', show (π : ℝ) = π / ((1 : ℕ) : ℝ) from hpi.symm, ftTauArcAt_arc_end]
    rw [hpi, cubicTau_pi]
  · rw [ftTauArcAt_agree _ _ _ _ _ h0 (by rw [hpi]; exact hpi')]
    exact (cubicTau_eq_ftTau ⟨h0, hpi'⟩).symm

/-- **The upper endpoint is fully repaired**, derivative included: the branch
arrives at `π` with slope `0`, which is also the slope of the constant extension
beyond it, so value *and* derivative match. -/
theorem cubicTauDeriv_pi : cubicTauDeriv π = 0 := by
  rw [cubicTauDeriv]
  norm_num

/-- **The lower endpoint cannot be repaired by any endpoint value.**  The branch
arrives at `0` with slope `-√3/3`, while `ftTauLower` extends by a constant, whose
slope is `0`.  The values agree — so continuity holds — and the derivatives do
not, so only a one-sided derivative on `Ici 0` can hold there. -/
theorem cubicTauDeriv_zero_ne_zero : cubicTauDeriv 0 ≠ 0 := by
  rw [cubicTauDeriv]
  have hs : Real.sin ((π - 0) / 3) = Real.sqrt 3 / 2 := by
    rw [sub_zero]
    have : (π : ℝ) / 3 = π / 3 := rfl
    rw [this, Real.sin_pi_div_three]
  have hc : Real.cos ((π - 0) / 3) = 1 / 2 := by
    rw [sub_zero, Real.cos_pi_div_three]
  rw [hs, hc]
  have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  intro hcon
  rw [div_eq_zero_iff] at hcon
  rcases hcon with h | h
  · rw [neg_eq_zero] at h; linarith
  · norm_num at h

end ForgacsTran
