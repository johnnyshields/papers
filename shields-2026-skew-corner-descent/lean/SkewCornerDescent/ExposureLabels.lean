/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.SimultaneousTopology

/-!
# Positive cap products and normalized anchor labels

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:exposure`).

Both prescribed cap signs give a positive product. Normalizing root differences by that
product preserves their order, so the exposed extreme is the extreme normalized label.

Sorry-free.
-/

namespace SkewCornerDescent

/-- Two caps with the same strict prescribed sign have positive product. -/
theorem signed_cap_product_pos (positive : Bool) {L Q : ℝ}
    (hL : responseSign positive L) (hQ : responseSign positive Q) : 0 < L * Q := by
  cases positive
  · exact mul_pos_of_neg_of_neg hL hQ
  · exact mul_pos hL hQ

/-- The paper's cap-normalized label written using the actual anchor root. -/
noncomputable def normalizedAnchorLabel (F reference root : ℝ) : ℝ :=
  (root - reference) / F

/-- Positive cap normalization preserves the strict order of all anchor roots. -/
theorem normalizedAnchorLabel_lt_iff {F reference a b : ℝ} (hF : 0 < F) :
    normalizedAnchorLabel F reference a < normalizedAnchorLabel F reference b ↔ a < b := by
  unfold normalizedAnchorLabel
  rw [div_lt_div_iff_of_pos_right hF]
  exact sub_lt_sub_iff_right reference

/-- Same-anchor response values at an exposed root are cap times the label difference. -/
theorem anchor_response_eq_normalized_difference {α : Type*}
    (K : ℕ) (p q : α → MvPolynomial ℕ ℝ)
    (hp : ∀ a j, j ∈ (p a).vars → j < K)
    (hq : ∀ a j, j ∈ (q a).vars → j < K)
    (a b : α) (x : ℕ → ℝ) (F reference : ℝ) (hF : F ≠ 0) :
    rationalTriangularResponse K (p b) (q b)
      (anchorAssignment K (rationalAnchorRoot p q) a x) =
        F * (normalizedAnchorLabel F reference (rationalAnchorRoot p q a x) -
          normalizedAnchorLabel F reference (rationalAnchorRoot p q b x)) := by
  have hc := rational_correction_locality K (p b) (q b) (hp b) (hq b)
    (anchorAssignment K (rationalAnchorRoot p q) a x) x (by
      intro j hj
      simp only [anchorAssignment, Function.update_of_ne (Nat.ne_of_lt hj)])
  unfold rationalTriangularResponse
  rw [hc]
  simp only [anchorAssignment, Function.update_self, rationalAnchorRoot, normalizedAnchorLabel]
  field_simp
  ring

/-- Constant active labels keep the same unique least and greatest identities in either chamber. -/
theorem constant_active_label_extremes {α : Type*} [Finite α] [Nonempty α]
    (label : α → ℚ) (hinj : Function.Injective label) :
    (∃ a, ∀ b, b ≠ a → (label a : ℝ) < (label b : ℝ)) ∧
    (∃ a, ∀ b, b ≠ a → (label b : ℝ) < (label a : ℝ)) := by
  have hi : Function.Injective (fun a => (label a : ℝ)) :=
    Rat.cast_injective.comp hinj
  exact ⟨exists_least_anchor_label _ hi, exists_greatest_anchor_label _ hi⟩

end SkewCornerDescent
