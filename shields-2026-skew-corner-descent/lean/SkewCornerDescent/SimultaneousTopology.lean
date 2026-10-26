/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.ExposureTopology

/-!
# Open simultaneous root chambers

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:exposure`).

Finite strict-sign conditions at every regular anchor root and pairwise root separation
are open in the free coordinates. A simultaneous witness therefore supplies a chamber.

Sorry-free.
-/

namespace SkewCornerDescent

/-- Distinct regular root values are equivalent to a nonzero evaluated cross-difference. -/
theorem rational_roots_ne_iff {α : Type*} (p q : α → MvPolynomial ℕ ℝ)
    (a b : α) (x : ℕ → ℝ)
    (ha : MvPolynomial.eval x (q a) ≠ 0) (hb : MvPolynomial.eval x (q b) ≠ 0) :
    rationalAnchorRoot p q a x ≠ rationalAnchorRoot p q b x ↔
      MvPolynomial.eval x (p a * q b - p b * q a) ≠ 0 := by
  simp only [rationalAnchorRoot, neg_inj, map_sub, map_mul, ne_eq, sub_eq_zero]
  exact not_congr (div_eq_div_iff ha hb)

/-- Pairwise regular root separation is an open polynomial condition. -/
theorem rational_root_separation_open {α : Type*} [Finite α]
    (p q : α → MvPolynomial ℕ ℝ) :
    IsOpen {x : ℕ → ℝ | (∀ a, MvPolynomial.eval x (q a) ≠ 0) ∧
      ∀ a b, a ≠ b → MvPolynomial.eval x (p a * q b - p b * q a) ≠ 0} := by
  classical
  change IsOpen ({x : ℕ → ℝ | ∀ a, MvPolynomial.eval x (q a) ≠ 0} ∩
    {x : ℕ → ℝ | ∀ a b, a ≠ b →
      MvPolynomial.eval x (p a * q b - p b * q a) ≠ 0})
  apply IsOpen.inter
  · simp only [Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro a
    exact isOpen_ne.preimage (q a).continuous_eval
  · simp only [Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro a
    apply isOpen_iInter_of_finite
    intro b
    apply isOpen_iInter_of_finite
    intro _
    exact isOpen_ne.preimage (p a * q b - p b * q a).continuous_eval

/-- Strict signs at every anchor root form an open chamber with every denominator retained. -/
theorem simultaneous_root_signs_open {α ι : Type*} [Finite α] [Finite ι]
    (K : ℕ) (ap aq : α → MvPolynomial ℕ ℝ)
    (top : ι → ℕ) (p q : ι → MvPolynomial ℕ ℝ) (positive : Bool) :
    IsOpen {x : ℕ → ℝ | ∀ a, MvPolynomial.eval x (aq a) ≠ 0 ∧
      ∀ i, let y := anchorAssignment K (rationalAnchorRoot ap aq) a x
        MvPolynomial.eval y (q i) ≠ 0 ∧
          responseSign positive (rationalTriangularResponse (top i) (p i) (q i) y)} := by
  simp only [Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro a
  exact rational_anchor_chamber_open K (ap a) (aq a) top p q positive

end SkewCornerDescent
