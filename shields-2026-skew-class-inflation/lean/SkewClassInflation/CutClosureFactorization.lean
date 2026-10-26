/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.CutClosureInvariants
import SkewClassInflation.StableCutCodeFactorization

/-!
# Full actual factorization reduction to unrestricted frontier propagation

The terminating induction assembly for factor-reversal reconstruction
in `thm:sharp-inflation` of `shields-2026-skew-class-inflation.tex`.
Computed finite termination, witness-preserving period refinement, and
the full-code cut constructor produce both literal proper factors.
The sole propagation premise is explicit and remains a separate
inventory proof obligation.  Sorry-free.
-/

namespace SkewClassInflation

/-- Unrestricted actual frontier propagation gives a literal proper ordinary factorization.

`hR` is the named inventory propagation obligation.  Termination, axiom guards,
and the bounded first-stage comparison do not discharge it.
-/
theorem proper_factorization_of_actual_frontier_propagation {N : ℕ}
    (α : Composition N) (k : ℕ) (hk : k ∈ properCuts α) (hkr : N - k ∉ properCuts α)
    (hfirst : ∀ j < k, compositionCutType α j ≠ 1)
    (hne : (undeterminedCuts α k).Nonempty) (hR : cutClosureOddPropagation α k) :
    ∃ p m : ℕ, 1 < p ∧ 2 ≤ m ∧ m * p = N ∧
      ∃ δ : Composition m, ∃ ε : Composition p, (compositionProduct δ ε).blocks = α.blocks := by
  have hkb := properCuts_bounds α k hk
  have hN : 0 < N := by omega
  obtain ⟨i, _, hD⟩ := undetermined_evenCutClosure_terminates α k hne
  change evenCutDisagreements α (cutClosureState α k i).1 (cutClosureState α k i).2 = ∅ at hD
  obtain ⟨hp, _, hP, hQ⟩ := cutClosureState_invariants α k hk hkr hfirst hne hR i
  have hg := cutClosureState_gcd α k hne i
  have hfull := stable_frontier_cutCode_period α hN (cutClosurePrevious α k i)
    (cutClosureState α k i).2 (cutClosurePrevious_dvd_weight α k hne i)
    (by rwa [← hg]) (by rwa [← hg]) (by rwa [← hg])
  rw [← hg] at hfull
  obtain ⟨m, hm, hweight, δ, ε, hfactor⟩ := proper_factorization_of_cutCode_period α hp
    (cutClosureState_lt_weight α k hne i) (cutClosureState_dvd_weight α k hne i) hfull
  exact ⟨(cutClosureState α k i).1, m, hp, hm, hweight, δ, ε, hfactor⟩

end SkewClassInflation
