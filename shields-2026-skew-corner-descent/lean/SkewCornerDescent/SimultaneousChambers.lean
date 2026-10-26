/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.SeparatedAnchors

/-!
# Simultaneous strict signs at every rational anchor root

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:exposure`).

Lower-coordinate polynomial avoidance and one higher-coordinate construction sign all
responses off the anchor at every same-anchor root. The roots stay pairwise distinct.

Sorry-free.
-/

namespace SkewCornerDescent

/-- A finite rational triangular family has regular signed off-anchor responses at every root. -/
theorem exists_simultaneous_rational_roots {lo hi α : Type*}
    [Finite lo] [Finite hi] [Finite α]
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
    ∃ x : ℕ → ℝ,
      Function.Injective (fun a => rationalAnchorRoot ap aq a x) ∧
      (∀ a, MvPolynomial.eval x (aq a) ≠ 0) ∧
      ∀ a, let y := anchorAssignment K (rationalAnchorRoot ap aq) a x
        (∀ i, MvPolynomial.eval y (lq i) ≠ 0 ∧
          responseSign positive (rationalTriangularResponse (lowTop i) (lp i) (lq i) y)) ∧
        (∀ i, MvPolynomial.eval y (hq i) ≠ 0 ∧
          responseSign positive (rationalTriangularResponse (highTop i) (hp i) (hq i) y)) := by
  classical
  let U : Set (ℕ → ℝ) := {x | ∀ i, MvPolynomial.eval x (lq i) ≠ 0 ∧
    responseSign positive (MvPolynomial.eval x
      (clearedTriangularResponse (lowTop i) (lp i) (lq i)))}
  obtain ⟨hU, hUne⟩ := rational_triangular_chamber lowTop lp lq N
    (fun i => (hlo i).1) hlp hlq hlq0 positive
  obtain ⟨base, hbase, hbaq, hbhq, hinj⟩ :=
    exists_separated_rational_anchors ap aq hq haq0 hhq0 hdiff U hU hUne
  have haqK : ∀ a j, j ∈ (aq a).vars → j < K :=
    fun a j hj => lt_of_lt_of_le (haq a j hj) hNK
  have hroot := rational_anchor_root_locality K ap aq hap haqK
  obtain ⟨x, hx, hhigh⟩ := exists_signed_above_anchor K highTop hhi
    (fun i z => MvPolynomial.eval z (hp i) / MvPolynomial.eval z (hq i))
    (fun i z w hzw => rational_correction_locality (highTop i) (hp i) (hq i)
      (hhp i) (fun j hj => lt_of_lt_of_le (hhq i j hj) (le_trans hNK (hhi i).le))
      z w hzw) (rationalAnchorRoot ap aq) hroot base positive
  have hroots : ∀ a, rationalAnchorRoot ap aq a x = rationalAnchorRoot ap aq a base :=
    fun a => anchor_roots_eq_of_agree_through K _ hroot x base hx a
  have hden (q : MvPolynomial ℕ ℝ) (hs : ∀ j ∈ q.vars, j < N) (a : α) :
      MvPolynomial.eval (anchorAssignment K (rationalAnchorRoot ap aq) a x) q =
        MvPolynomial.eval base q := by
    apply eval_polynomial_eq_of_agree_below q K
      (fun j hj => lt_of_lt_of_le (hs j hj) hNK)
    intro j hj
    simp only [anchorAssignment, Function.update_of_ne (Nat.ne_of_lt hj), hx j hj.le]
  refine ⟨x, ?_, ?_, fun a => ⟨?_, ?_⟩⟩
  · intro a b he
    apply hinj
    simpa only [hroots] using he
  · intro a
    rw [eval_polynomial_eq_of_agree_below (aq a) K (haqK a) x base
      (fun j hj => hx j hj.le)]
    exact hbaq a
  · intro i
    refine ⟨by rw [hden (lq i) (hlq i) a]; exact (hbase i).1, ?_⟩
    have hresp := response_below_anchor_preserved K (lowTop i) (hlo i).2
      (fun z => MvPolynomial.eval z (lp i) / MvPolynomial.eval z (lq i))
      (fun z w hzw => rational_correction_locality (lowTop i) (lp i) (lq i) (hlp i)
        (fun j hj => lt_of_lt_of_le (hlq i j hj) (hlo i).1) z w hzw)
      (rationalAnchorRoot ap aq) a x base hx
    change responseSign positive (_ + _ / _)
    rw [hresp]
    apply (responseSign_div_iff_cleared positive _ _ _ (hbase i).1).mpr
    simpa only [clearedTriangularResponse, map_mul, map_add, MvPolynomial.eval_X]
      using (hbase i).2
  · intro i
    exact ⟨by rw [hden (hq i) (hhq i) a]; exact hbhq i, hhigh i a⟩

end SkewCornerDescent
