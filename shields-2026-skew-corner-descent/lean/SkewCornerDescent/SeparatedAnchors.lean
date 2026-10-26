/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.AnchorChambers
import SkewCornerDescent.RationalChambers

/-!
# Distinct rational anchor roots

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:exposure`).

A finite family of distinct rational corrections has distinct regular roots on a nonempty
part of any open lower-coordinate chamber. Higher-coordinate choices preserve the roots.

Sorry-free.
-/

namespace SkewCornerDescent

/-- The actual zero of a rational monic response at its anchor coordinate. -/
noncomputable def rationalAnchorRoot {α : Type*}
    (p q : α → MvPolynomial ℕ ℝ) (a : α) (x : ℕ → ℝ) : ℝ :=
  -(MvPolynomial.eval x (p a) / MvPolynomial.eval x (q a))

/-- A rational anchor root depends only on the strictly lower coordinates. -/
theorem rational_anchor_root_locality {α : Type*} (K : ℕ)
    (p q : α → MvPolynomial ℕ ℝ)
    (hp : ∀ a j, j ∈ (p a).vars → j < K)
    (hq : ∀ a j, j ∈ (q a).vars → j < K)
    (a : α) (x y : ℕ → ℝ) (hxy : ∀ j, j < K → x j = y j) :
    rationalAnchorRoot p q a x = rationalAnchorRoot p q a y := by
  unfold rationalAnchorRoot
  rw [rational_correction_locality K (p a) (q a) (hp a) (hq a) x y hxy]

/-- Pairwise distinct fractions have regular distinct roots inside any nonempty open chamber. -/
theorem exists_separated_rational_anchors {α ι : Type*} [Finite α] [Finite ι]
    (p q : α → MvPolynomial ℕ ℝ) (r : ι → MvPolynomial ℕ ℝ)
    (hq : ∀ a, q a ≠ 0) (hr : ∀ i, r i ≠ 0)
    (hdiff : ∀ a b, a ≠ b → p a * q b - p b * q a ≠ 0)
    (U : Set (ℕ → ℝ)) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ x ∈ U, (∀ a, MvPolynomial.eval x (q a) ≠ 0) ∧
      (∀ i, MvPolynomial.eval x (r i) ≠ 0) ∧
      Function.Injective (fun a => rationalAnchorRoot p q a x) := by
  classical
  let pairs := {ab : α × α // ab.1 ≠ ab.2}
  let family : α ⊕ (ι ⊕ pairs) → MvPolynomial ℕ ℝ := fun i =>
    match i with
    | .inl a => q a
    | .inr (.inl j) => r j
    | .inr (.inr ab) => p ab.val.1 * q ab.val.2 - p ab.val.2 * q ab.val.1
  have hf : ∀ i, family i ≠ 0 := by
    intro i
    rcases i with a | (j | ab)
    · exact hq a
    · exact hr j
    · exact hdiff _ _ ab.property
  obtain ⟨x, hx, hreg⟩ := exists_finite_polynomials_ne_zero_on_open family hf U hU hne
  have hqa : ∀ a, MvPolynomial.eval x (q a) ≠ 0 := fun a => hreg (.inl a)
  refine ⟨x, hx, hqa, fun i => hreg (.inr (.inl i)), ?_⟩
  intro a b he
  by_contra hab
  have hcross := hreg (.inr (.inr ⟨(a, b), hab⟩))
  change MvPolynomial.eval x (p a * q b - p b * q a) ≠ 0 at hcross
  simp only [map_sub, map_mul] at hcross
  apply hcross
  have he' : MvPolynomial.eval x (p a) / MvPolynomial.eval x (q a) =
      MvPolynomial.eval x (p b) / MvPolynomial.eval x (q b) := neg_injective he
  have h := (div_eq_div_iff (hqa a) (hqa b)).mp he'
  exact sub_eq_zero.mpr h

/-- Root substitution zeros the anchor's own literal response without changing its correction. -/
theorem rational_anchor_response_zero {α : Type*} (K : ℕ)
    (p q : α → MvPolynomial ℕ ℝ)
    (hp : ∀ a j, j ∈ (p a).vars → j < K)
    (hq : ∀ a j, j ∈ (q a).vars → j < K) (a : α) (x : ℕ → ℝ) :
    rationalTriangularResponse K (p a) (q a)
      (anchorAssignment K (rationalAnchorRoot p q) a x) = 0 := by
  have hc := rational_correction_locality K (p a) (q a) (hp a) (hq a)
    (anchorAssignment K (rationalAnchorRoot p q) a x) x (by
      intro j hj
      simp only [anchorAssignment, Function.update_of_ne (Nat.ne_of_lt hj)])
  unfold rationalTriangularResponse
  rw [hc]
  simp only [anchorAssignment, Function.update_self, rationalAnchorRoot, neg_add_cancel]

end SkewCornerDescent
