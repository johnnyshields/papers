/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.EvenCutNonzeroRefinement
import SkewClassInflation.InitialCutCodePeriods

/-!
# Actual computed closure states and simultaneous period invariants

The finite induction assembly for factor-reversal reconstruction in
`thm:sharp-inflation` of `shields-2026-skew-class-inflation.tex`.
All states, preceding periods, and frontiers are computed from the
original normalized source.  The odd-point propagation obligation is
explicit; no bundled or implicit proof-gap input is introduced.
Sorry-free.
-/

namespace SkewClassInflation

/-- The actual candidate period and frontier after the specified number of refinement steps. -/
noncomputable def cutClosureState {N : ℕ} (α : Composition N) (k i : ℕ) : ℕ × Finset ℕ :=
  (evenCutClosureStep α)^[i] (evenCutClosureInitial α k)

/-- Successive actual states are related by the existing computed refinement step. -/
theorem cutClosureState_succ {N : ℕ} (α : Composition N) (k i : ℕ) :
    cutClosureState α k (i + 1) = evenCutClosureStep α (cutClosureState α k i) := by
  simp only [cutClosureState, Function.iterate_succ_apply']

/-- The full-code channel's actual preceding period at each computed state. -/
noncomputable def cutClosurePrevious {N : ℕ} (α : Composition N) (k : ℕ) : ℕ → ℕ
  | 0 => N
  | i + 1 => (cutClosureState α k i).1

/-- The unrestricted inventory propagation obligation at every actual computed frontier.

This is an explicit proof obligation, not an asserted theorem.  The bounded
first-stage producer is `bounded_even_discrepancy_agrees`; it does not establish
this unrestricted integer statement for every state.
-/
def cutClosureOddPropagation {N : ℕ} (α : Composition N) (k : ℕ) : Prop :=
  ∀ i : ℕ, ∀ t ∈ evenCutDisagreements α (cutClosureState α k i).1 (cutClosureState α k i).2,
    ∀ z : ℤ, ¬ ((cutClosureState α k i).1 : ℤ) ∣ z → compositionCutSignInt α z ≠ 0 →
      compositionCutSignInt α (z + (t : ℤ)) = compositionCutSignInt α z

/-- Every actual candidate period is positive. -/
theorem cutClosureState_pos {N : ℕ} (α : Composition N) (k : ℕ)
    (hne : (undeterminedCuts α k).Nonempty) (i : ℕ) : 0 < (cutClosureState α k i).1 :=
  evenCutClosure_iterate_pos α (evenCutClosureInitial α k) (undeterminedGcd_pos α k hne) i

/-- Every actual candidate period still divides the true whole weight. -/
theorem cutClosureState_dvd_weight {N : ℕ} (α : Composition N) (k : ℕ)
    (hne : (undeterminedCuts α k).Nonempty) (i : ℕ) : (cutClosureState α k i).1 ∣ N := by
  induction i with
  | zero => exact undeterminedGcd_dvd_weight α k hne
  | succ i ih =>
    rw [cutClosureState_succ]
    exact (evenCutClosureStep_dvd α _).trans ih

/-- The actual preceding full-code period still divides the true whole weight. -/
theorem cutClosurePrevious_dvd_weight {N : ℕ} (α : Composition N) (k : ℕ)
    (hne : (undeterminedCuts α k).Nonempty) (i : ℕ) : cutClosurePrevious α k i ∣ N := by
  cases i with
  | zero => exact dvd_refl N
  | succ i => exact cutClosureState_dvd_weight α k hne i

/-- Every actual candidate period remains strictly below the true whole weight. -/
theorem cutClosureState_lt_weight {N : ℕ} (α : Composition N) (k : ℕ)
    (hne : (undeterminedCuts α k).Nonempty) (i : ℕ) : (cutClosureState α k i).1 < N := by
  induction i with
  | zero => exact undeterminedGcd_lt_weight α k hne
  | succ i ih =>
    rw [cutClosureState_succ]
    have hp := cutClosureState_pos α k hne i
    have hle := Nat.le_of_dvd hp (evenCutClosureStep_dvd α (cutClosureState α k i))
    exact hle.trans_lt ih

/-- The actual candidate is the gcd of its preceding period and its actual frontier. -/
theorem cutClosureState_gcd {N : ℕ} (α : Composition N) (k : ℕ)
    (hne : (undeterminedCuts α k).Nonempty) (i : ℕ) :
    (cutClosureState α k i).1 =
      (cutClosurePrevious α k i).gcd ((cutClosureState α k i).2.gcd id) := by
  cases i with
  | zero =>
    change undeterminedGcd α k = N.gcd (undeterminedGcd α k)
    apply Nat.dvd_antisymm
    · exact Nat.dvd_gcd (undeterminedGcd_dvd_weight α k hne) (dvd_refl _)
    · exact Nat.gcd_dvd_right _ _
  | succ i =>
    rw [cutClosureState_succ]
    rfl

/-- Actual unrestricted frontier propagation supplies all simultaneous period invariants.

The `hR` producer is the remaining inventory propagation obligation, not a
consequence of the termination theorem.
-/
theorem cutClosureState_invariants {N : ℕ} (α : Composition N) (k : ℕ)
    (hk : k ∈ properCuts α) (hkr : N - k ∉ properCuts α)
    (hfirst : ∀ j < k, compositionCutType α j ≠ 1)
    (hne : (undeterminedCuts α k).Nonempty) (hR : cutClosureOddPropagation α k) :
    ∀ i : ℕ, 1 < (cutClosureState α k i).1 ∧ ¬ (cutClosureState α k i).1 ∣ k ∧
      Function.Periodic (periodMask (compositionCutSignInt α) (cutClosureState α k i).1)
        ((cutClosureState α k i).1 : ℤ) ∧
      Function.Periodic (periodMask (compositionCutCode α) (cutClosureState α k i).1)
        (cutClosurePrevious α k i : ℤ) := by
  have hkb := properCuts_bounds α k hk
  have hN : 0 < N := by omega
  have hFk : compositionCutSignInt α (k : ℤ) ≠ 0 := by
    unfold compositionCutSignInt
    rw [compositionCutResidue_nat N k hkb.2]
    simp only [compositionCutSign, hk, hkr, ite_true, ite_false, sub_zero]
    decide
  obtain ⟨hp, _, hpN, hpk, hperiod⟩ := undeterminedGcd_signed_period α k hk hkr hfirst hne
  intro i
  induction i with
  | zero =>
    exact ⟨hp, hpk, compositionCutSignInt_masked_period (p := undeterminedGcd α k)
      α hN (by omega) hpN hperiod,
      compositionCutCode_masked_whole_period α hpN⟩
  | succ i ih =>
    have hg := cutClosureState_gcd α k hne i
    have hh := evenCutClosure_strong_refinement α hN (cutClosurePrevious α k i)
      (cutClosureState α k i).2 (cutClosurePrevious_dvd_weight α k hne i)
      (by rw [← hg]; exact lt_trans Nat.zero_lt_one ih.1) k
      (by rw [← hg]; exact ih.2.1) hFk
      (by rw [← hg]; exact ih.2.2.1) (by rw [← hg]; exact ih.2.2.2)
      (by rw [← hg]; exact hR i)
    rw [← hg] at hh
    rw [cutClosureState_succ]
    exact hh

end SkewClassInflation
