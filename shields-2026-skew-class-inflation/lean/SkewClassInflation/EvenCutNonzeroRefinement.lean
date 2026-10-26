/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.ZeroFrontierPeriods
import SkewClassInflation.IntegerCutSigns
import SkewClassInflation.EvenCutCodeRefinement

/-!
# Actual period refinement preserving the original nonzero witness

The simultaneous period-assembly step for factor-reversal
reconstruction in `thm:sharp-inflation` of
`shields-2026-skew-class-inflation.tex`.  Actual even frontier values
supply the zero endpoints.  Odd-point propagation then gives both
next period channels and keeps the original witness outside their
exceptional multiples.  Sorry-free.
-/

namespace SkewClassInflation

/-- Actual even zeros keep the refined signed period nontrivial.

The `hodd` premise is the unrestricted nonempty-frontier inventory propagation
obligation.  `bounded_even_discrepancy_agrees` supplies only the bounded first-stage
case, not this unrestricted integer statement.
-/
theorem evenCutClosure_nonzero_signed_refinement {N : ℕ} (α : Composition N) (hN : 0 < N)
    (p : ℕ) (hp : 0 < p) (T : Finset ℕ) (k : ℕ) (hk : ¬ p ∣ k)
    (hFk : compositionCutSignInt α (k : ℤ) ≠ 0)
    (hP : Function.Periodic (periodMask (compositionCutSignInt α) p) (p : ℤ))
    (hodd : ∀ t ∈ evenCutDisagreements α p T, ∀ z : ℤ,
      ¬ (p : ℤ) ∣ z → compositionCutSignInt α z ≠ 0 →
        compositionCutSignInt α (z + (t : ℤ)) = compositionCutSignInt α z) :
    1 < (evenCutClosureStep α (p, T)).1 ∧ ¬ (evenCutClosureStep α (p, T)).1 ∣ k ∧
      Function.Periodic
        (periodMask (compositionCutSignInt α) (evenCutClosureStep α (p, T)).1)
        ((evenCutClosureStep α (p, T)).1 : ℤ) :=
  zero_frontier_preserves_nonzero_witness (compositionCutSignInt α) p hp
    (evenCutDisagreements α p T) k hk hFk hP
    (evenCutDisagreements_negative_sign_zero α hN p T) hodd

/-- The actual odd propagation input supplies both next period channels and the original witness.

As in `evenCutClosure_nonzero_signed_refinement`, the unrestricted `hodd` producer
remains the inventory propagation obligation; it is not supplied by termination.
-/
theorem evenCutClosure_strong_refinement {N : ℕ} (α : Composition N) (hN : 0 < N)
    (q : ℕ) (T : Finset ℕ) (hqN : q ∣ N) (hp : 0 < q.gcd (T.gcd id)) (k : ℕ)
    (hk : ¬ q.gcd (T.gcd id) ∣ k) (hFk : compositionCutSignInt α (k : ℤ) ≠ 0)
    (hP : Function.Periodic
      (periodMask (compositionCutSignInt α) (q.gcd (T.gcd id))) (q.gcd (T.gcd id) : ℤ))
    (hQ : Function.Periodic
      (periodMask (compositionCutCode α) (q.gcd (T.gcd id))) (q : ℤ))
    (hodd : ∀ t ∈ evenCutDisagreements α (q.gcd (T.gcd id)) T, ∀ z : ℤ,
      ¬ (q.gcd (T.gcd id) : ℤ) ∣ z → compositionCutSignInt α z ≠ 0 →
        compositionCutSignInt α (z + (t : ℤ)) = compositionCutSignInt α z) :
    let d := (evenCutClosureStep α (q.gcd (T.gcd id), T)).1
    1 < d ∧ ¬ d ∣ k ∧
      Function.Periodic (periodMask (compositionCutSignInt α) d) (d : ℤ) ∧
      Function.Periodic (periodMask (compositionCutCode α) d) (q.gcd (T.gcd id) : ℤ) := by
  obtain ⟨hd, hdk, hP'⟩ := evenCutClosure_nonzero_signed_refinement α hN
    (q.gcd (T.gcd id)) hp T k hk hFk hP hodd
  exact ⟨hd, hdk, hP', evenCutClosure_code_refinement α hN q T hqN hQ hP'⟩

end SkewClassInflation
