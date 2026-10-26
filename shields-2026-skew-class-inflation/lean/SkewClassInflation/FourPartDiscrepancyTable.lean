/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.LabeledCoarseningCounts

/-!
# Exact four-part even-discrepancy alternatives

The finite Boolean calculation in the first even-discrepancy
propagation step for `thm:sharp-inflation` of
`shields-2026-skew-class-inflation.tex`.  Index permutations are labeled,
so repeated part values do not change this count.  The table records
only the symbolic cut pattern; applying it to a composition also
requires the actual retained-order bridge.  Sorry-free.
-/

namespace SkewClassInflation

/-- The seven nonempty subset cuts before the distinguished complementary part. -/
def discrepancyLeftCuts (m x z a c : Bool) : ℕ → Bool
  | 1 => m
  | 2 => x
  | 3 => !x
  | 4 => z
  | 5 => z
  | 6 => a
  | 7 => c
  | _ => false

/-- Reflected subset cuts, including the flipped undetermined coordinate. -/
def discrepancyRightCuts (m x z b d : Bool) : ℕ → Bool
  | 1 => !m
  | 2 => x
  | 3 => !x
  | 4 => !z
  | 5 => !z
  | 6 => b
  | 7 => d
  | _ => false

/-- Read the true subset or its reflected complement from the four distinct index labels. -/
def discrepancyMaskCut (L R : ℕ → Bool) (mask : ℕ) : Bool :=
  if mask < 8 then L mask else R (15 - mask)

/-- The exact labeled count for any four-part subset cut pattern. -/
def fourPartMaskCount (L R : ℕ → Bool) : ℕ := by
  classical
  exact (Finset.univ.filter (fun σ : Equiv.Perm (Fin 4) =>
    discrepancyMaskCut L R (2 ^ (σ 0).val) &&
    discrepancyMaskCut L R (2 ^ (σ 0).val + 2 ^ (σ 1).val) &&
    discrepancyMaskCut L R (15 - 2 ^ (σ 3).val))).card

/-- The count specialized to the actual two-channel discrepancy pattern. -/
def fourPartDiscrepancyCount (m x z a b c d : Bool) : ℕ :=
  fourPartMaskCount (discrepancyLeftCuts m x z a c) (discrepancyRightCuts m x z b d)

/-- Equal signed values and four-part counts leave exactly the two stated alternatives. -/
theorem fourPartDiscrepancy_alternatives : ∀ m x z a b c d : Bool,
    ((a = c ∧ b = d) ∨ (a = b ∧ c = d)) →
    fourPartDiscrepancyCount m x z a b c d = fourPartDiscrepancyCount (!m) x z a b c d →
      (a = z ∧ b = !z ∧ c = z ∧ d = !z) ∨
        (a = x ∧ b = x ∧ c = !x ∧ d = !x) := by
  decide +kernel

end SkewClassInflation
