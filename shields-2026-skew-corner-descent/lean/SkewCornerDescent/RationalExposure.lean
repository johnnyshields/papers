/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.SimultaneousChambers

/-!
# Exposure of finite rational triangular families

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:exposure`).

Lower responses are signed on an open chamber, distinct anchor roots are separated there,
and higher coordinates are chosen simultaneously at all roots. An extreme root exposes
one anchor while every other response has the prescribed sign.

Sorry-free.
-/

namespace SkewCornerDescent

/-- Either sign admits one exposed anchor and signed responses at every other index. -/
theorem exists_rational_exposure {lo hi α : Type*}
    [Finite lo] [Finite hi] [Finite α] [Nonempty α]
    (N K : ℕ) (hNK : N ≤ K)
    (lowTop : lo → ℕ) (highTop : hi → ℕ)
    (lp lq : lo → MvPolynomial ℕ ℝ) (hp hq : hi → MvPolynomial ℕ ℝ)
    (ap aq : α → MvPolynomial ℕ ℝ)
    (hlo : ∀ i, N ≤ lowTop i ∧ lowTop i < K) (hhi : ∀ i, K < highTop i)
    (hlp : ∀ i j, j ∈ (lp i).vars → j < lowTop i)
    (hlq : ∀ i j, j ∈ (lq i).vars → j < N) (hlq0 : ∀ i, lq i ≠ 0)
    (hhp : ∀ i j, j ∈ (hp i).vars → j < highTop i)
    (hhq : ∀ i j, j ∈ (hq i).vars → j < N) (hhq0 : ∀ i, hq i ≠ 0)
    (hap : ∀ a j, j ∈ (ap a).vars → j < K)
    (haq : ∀ a j, j ∈ (aq a).vars → j < N) (haq0 : ∀ a, aq a ≠ 0)
    (hdiff : ∀ a b, a ≠ b → ap a * aq b - ap b * aq a ≠ 0)
    (positive : Bool) :
    ∃ (y : ℕ → ℝ) (a : α),
      (∀ i, MvPolynomial.eval y (lq i) ≠ 0) ∧
      (∀ i, MvPolynomial.eval y (hq i) ≠ 0) ∧
      (∀ b, MvPolynomial.eval y (aq b) ≠ 0) ∧
      rationalTriangularResponse K (ap a) (aq a) y = 0 ∧
      (∀ i, responseSign positive (rationalTriangularResponse (lowTop i) (lp i) (lq i) y)) ∧
      (∀ i, responseSign positive (rationalTriangularResponse (highTop i) (hp i) (hq i) y)) ∧
      ∀ b, b ≠ a → responseSign positive (rationalTriangularResponse K (ap b) (aq b) y) := by
  classical
  obtain ⟨x, hinjx, hregular, hsigned⟩ := exists_simultaneous_rational_roots N K hNK
    lowTop highTop lp lq hp hq ap aq hlo hhi hlp hlq hlq0 hhp hhq hhq0 hap haq haq0
    hdiff positive
  have haqK : ∀ a j, j ∈ (aq a).vars → j < K :=
    fun a j hj => lt_of_lt_of_le (haq a j hj) hNK
  have hextreme : ∃ a, ∀ b, b ≠ a → responseSign positive
      (rationalAnchorRoot ap aq a x - rationalAnchorRoot ap aq b x) := by
    cases positive
    · obtain ⟨a, ha⟩ := exists_least_anchor_label _ hinjx
      exact ⟨a, fun b hba => sub_neg.mpr (ha b hba)⟩
    · obtain ⟨a, ha⟩ := exists_greatest_anchor_label _ hinjx
      exact ⟨a, fun b hba => sub_pos.mpr (ha b hba)⟩
  obtain ⟨a, ha⟩ := hextreme
  let y := anchorAssignment K (rationalAnchorRoot ap aq) a x
  have hden (q : MvPolynomial ℕ ℝ) (hs : ∀ j ∈ q.vars, j < N) :
      MvPolynomial.eval y q = MvPolynomial.eval x q := by
    apply eval_polynomial_eq_of_agree_below q K
      (fun j hj => lt_of_lt_of_le (hs j hj) hNK)
    intro j hj
    simp only [y, anchorAssignment, Function.update_of_ne (Nat.ne_of_lt hj)]
  refine ⟨y, a, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun i => ((hsigned a).1 i).1
  · exact fun i => ((hsigned a).2 i).1
  · intro b
    rw [hden (aq b) (haq b)]
    exact hregular b
  · exact rational_anchor_response_zero K ap aq hap haqK a x
  · exact fun i => ((hsigned a).1 i).2
  · exact fun i => ((hsigned a).2 i).2
  · intro b hba
    have hc := rational_correction_locality K (ap b) (aq b) (hap b) (haqK b)
      y x (by
        intro j hj
        simp only [y, anchorAssignment, Function.update_of_ne (Nat.ne_of_lt hj)])
    change responseSign positive (y K + MvPolynomial.eval y (ap b) /
      MvPolynomial.eval y (aq b))
    rw [hc]
    simpa only [y, anchorAssignment, Function.update_self, rationalAnchorRoot, sub_neg_eq_add]
      using ha b hba

end SkewCornerDescent
