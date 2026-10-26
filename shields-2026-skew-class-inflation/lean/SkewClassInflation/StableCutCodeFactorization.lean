/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.InitialCutCodePeriods

/-!
# Literal factorization at an actual stable cut frontier

The terminating branch of factor-reversal reconstruction for
`thm:sharp-inflation` of `shields-2026-skew-class-inflation.tex`.
An empty next discrepancy set keeps the candidate period unchanged.
The full-code refinement theorem then produces the full cut period
and its actual proper factors.  Sorry-free.
-/

namespace SkewClassInflation

/-- At a stable actual frontier the existing signed invariant supplies the full code period. -/
theorem stable_frontier_cutCode_period {N : ℕ} (α : Composition N) (hN : 0 < N)
    (q : ℕ) (T : Finset ℕ) (hqN : q ∣ N)
    (hP : Function.Periodic
      (periodMask (compositionCutSignInt α) (q.gcd (T.gcd id)))
      (q.gcd (T.gcd id) : ℤ))
    (hQ : Function.Periodic
      (periodMask (compositionCutCode α) (q.gcd (T.gcd id))) (q : ℤ))
    (hD : evenCutDisagreements α (q.gcd (T.gcd id)) T = ∅) :
    Function.Periodic (periodMask (compositionCutCode α) (q.gcd (T.gcd id)))
      (q.gcd (T.gcd id) : ℤ) := by
  have hstep : (evenCutClosureStep α (q.gcd (T.gcd id), T)).1 = q.gcd (T.gcd id) := by
    change (q.gcd (T.gcd id)).gcd ((evenCutDisagreements α (q.gcd (T.gcd id)) T).gcd id) = _
    rw [hD, Finset.gcd_empty, Nat.gcd_zero_right]
  have hP' : Function.Periodic
      (periodMask (compositionCutSignInt α)
        (evenCutClosureStep α (q.gcd (T.gcd id), T)).1)
      ((evenCutClosureStep α (q.gcd (T.gcd id), T)).1 : ℤ) := by
    rwa [hstep]
  have hh := evenCutClosure_code_refinement α hN q T hqN hQ hP'
  rwa [hstep] at hh

/-- An empty next frontier produces factors with the exact actual gcd as the inner weight. -/
theorem undetermined_factorization_of_stable_frontier_at_gcd {N : ℕ}
    (α : Composition N) (k : ℕ)
    (hk : k ∈ properCuts α) (hkr : N - k ∉ properCuts α)
    (hfirst : ∀ j < k, compositionCutType α j ≠ 1)
    (hne : (undeterminedCuts α k).Nonempty)
    (hD : evenCutDisagreements α (undeterminedGcd α k) (undeterminedCuts α k) = ∅) :
    ∃ m : ℕ, 2 ≤ m ∧ m * undeterminedGcd α k = N ∧
      ∃ δ : Composition m, ∃ ε : Composition (undeterminedGcd α k),
        (compositionProduct δ ε).blocks = α.blocks := by
  obtain ⟨hp, hpN, hd, _, hperiod⟩ := undeterminedGcd_signed_period α k hk hkr hfirst hne
  let T := undeterminedCuts α k
  let p := undeterminedGcd α k
  have hN : 0 < N := by omega
  have hg : N.gcd (T.gcd id) = p := by
    apply Nat.dvd_antisymm
    · exact Nat.gcd_dvd_right _ _
    · exact Nat.dvd_gcd hd (dvd_refl p)
  have hP := compositionCutSignInt_masked_period α hN (by omega) hd hperiod
  have hQ := compositionCutCode_masked_whole_period α hd
  have hfull : Function.Periodic (periodMask (compositionCutCode α) p) (p : ℤ) := by
    have hh := stable_frontier_cutCode_period α hN N T (dvd_refl N)
      (by rwa [hg]) (by rwa [hg]) (by rwa [hg])
    rwa [hg] at hh
  exact proper_factorization_of_cutCode_period α hp hpN hd hfull

/-- A normalized nonempty undetermined source with no next even discrepancies has proper factors. -/
theorem undetermined_factorization_of_stable_frontier {N : ℕ} (α : Composition N) (k : ℕ)
    (hk : k ∈ properCuts α) (hkr : N - k ∉ properCuts α)
    (hfirst : ∀ j < k, compositionCutType α j ≠ 1)
    (hne : (undeterminedCuts α k).Nonempty)
    (hD : evenCutDisagreements α (undeterminedGcd α k) (undeterminedCuts α k) = ∅) :
    ∃ p m : ℕ, 1 < p ∧ 2 ≤ m ∧ m * p = N ∧
      ∃ δ : Composition m, ∃ ε : Composition p, (compositionProduct δ ε).blocks = α.blocks := by
  obtain ⟨hp, _, _, _, _⟩ := undeterminedGcd_signed_period α k hk hkr hfirst hne
  obtain ⟨m, hm, hweight, δ, ε, hfactor⟩ :=
    undetermined_factorization_of_stable_frontier_at_gcd α k hk hkr hfirst hne hD
  exact ⟨undeterminedGcd α k, m, hp, hm, hweight, δ, ε, hfactor⟩

end SkewClassInflation
