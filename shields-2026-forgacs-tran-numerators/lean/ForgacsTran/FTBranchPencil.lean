/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.FTBranchValue
import ForgacsTran.Geometry

/-!
# The branch as a zero of the denominator pencil

The output of Lemmas 2 and 4(i), restated on the objects the rest of the tree
uses: `ftDen Q r z` and `ftBranch`.

## Main statements

* `ftRootPoly` — `Q(t) = c ∏_k (τ_k - t)`, the denominator of
  `Forgacs2017RationalDenominator` with its zeros displayed.
* `exists_ftDen_root_on_arc` — for every `θ` in the viewing arc there is a real
  `z` and a radius `τ` with `(ftDen Q r z).eval (τ e^{-iθ}) = 0`.
* `exists_ftBranch_real_on_arc` — the same fact read through `ftBranch`, which is
  the form `thm:FT-geometry` consumes: the fiber map `-Q(t)/t^r` is real at the
  branch point.

## Implementation notes

Sorry-free.

## References

Formalizes `Forgacs2017RationalDenominator` Lemmas 2--5, the branch
`thm:FT-geometry` imports.

## Tags

denominator pencil, branch, zero
-/

namespace ForgacsTran

open Real Set Polynomial

/-- `Q(t) = c ∏_k (τ_k - t)` with the zeros `τ_k` displayed. -/
noncomputable def ftRootPoly {n : ℕ} (c : ℝ) (a : Fin n → ℝ) : Polynomial ℂ :=
  C (c : ℂ) * ∏ k, (C ((a k : ℝ) : ℂ) - X)

@[simp] theorem eval_ftRootPoly {n : ℕ} (c : ℝ) (a : Fin n → ℝ) (t : ℂ) :
    (ftRootPoly c a).eval t = (c : ℂ) * ∏ k, ((a k : ℂ) - t) := by
  simp [ftRootPoly, eval_prod]

/-- **`Forgacs2017RationalDenominator` Lemmas 2 and 4(i) on the pencil.**  Every
angle of the viewing arc carries a denominator zero `τ e^{-iθ}` at a real
spectral parameter. -/
theorem exists_ftDen_root_on_arc {n r l : ℕ} {a : Fin n → ℝ} {c : ℝ} (hn : 0 < n)
    (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r) (hl : l < n) {θ : ℝ}
    (hθ0 : 0 < θ) (hθr : θ < π / r) (hrange : (n : ℝ) * θ < r * θ + l * π) :
    ∃ τ : ℝ, 0 < τ ∧ ∃ z : ℝ, 0 < (-1 : ℝ) ^ (n + l + 1) * z ∧
      (ftDen (ftRootPoly c a) r (z : ℂ)).eval (ftArcPoint τ θ) = 0 := by
  obtain ⟨τ, hτ, z, hz, hroot⟩ :=
    exists_ftArcPoint_real (a := a) (c := c) hn ha hc hr hl hθ0 hθr hrange
  refine ⟨τ, hτ, z, hz, ?_⟩
  rw [ftDen_eval, eval_ftRootPoly]
  exact hroot

/-- The same fact through `ftBranch`: at the branch point the fiber map
`g(t) = -Q(t)/t^r` takes a real value, which is what `thm:FT-geometry` reads off
the arc. -/
theorem exists_ftBranch_real_on_arc {n r l : ℕ} {a : Fin n → ℝ} {c : ℝ} (hn : 0 < n)
    (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r) (hl : l < n) {θ : ℝ}
    (hθ0 : 0 < θ) (hθr : θ < π / r) (hrange : (n : ℝ) * θ < r * θ + l * π) :
    ∃ τ : ℝ, 0 < τ ∧ ∃ z : ℝ, 0 < (-1 : ℝ) ^ (n + l + 1) * z ∧
      ftBranch (fun s => (ftRootPoly c a).eval s) r (ftArcPoint τ θ) = (z : ℂ) := by
  obtain ⟨τ, hτ, z, hz, hroot⟩ :=
    exists_ftDen_root_on_arc (a := a) (c := c) hn ha hc hr hl hθ0 hθr hrange
  refine ⟨τ, hτ, z, hz, ?_⟩
  have hne : ftArcPoint τ θ ≠ 0 := by
    simp only [ftArcPoint]
    exact mul_ne_zero (by exact_mod_cast ne_of_gt hτ) (Complex.exp_ne_zero _)
  exact ((ftDen_eq_zero_iff_ftBranch hne).1 hroot).symm

end ForgacsTran
