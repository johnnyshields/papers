/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.PeriodicCutEncoding
import Mathlib.Data.ZMod.Basic

/-!
# Actual integer signed reflection and even frontier zeros

The endpoint input to nonzero-witness preservation for
`thm:sharp-inflation` of `shields-2026-skew-class-inflation.tex`.
The integer extension uses the same true composition residues on both
sides of reflection.  Every actual even frontier point therefore has
zero signed value at its negative coordinate.  Sorry-free.
-/

namespace SkewClassInflation

/-- The integer-periodic signed cut channel is genuinely odd. -/
theorem compositionCutSignInt_neg {N : ℕ} (α : Composition N) (hN : 0 < N) (z : ℤ) :
    compositionCutSignInt α (-z) = -compositionCutSignInt α z := by
  classical
  let _ : NeZero N := ⟨Nat.ne_of_gt hN⟩
  have hres (w : ℤ) : compositionCutResidue N w = (w : ZMod N).val := by
    have hh := (compositionCutResidue_cast N hN w).trans (ZMod.val_intCast w).symm
    exact_mod_cast hh
  have hzero : compositionCutSign α 0 = 0 := by
    apply compositionCutSign_eq_zero_of_not_one
    rw [compositionCutType_outside α 0 (Or.inl rfl)]
    decide
  have hneg (a : ZMod N) : compositionCutSign α (-a).val = -compositionCutSign α a.val := by
    by_cases ha : a = 0
    · subst a
      simp only [neg_zero, ZMod.val_zero, hzero, neg_zero]
    · rw [ZMod.neg_val, ite_eq_right ha,
        compositionCutSign_reflect α a.val a.val_lt.le]
  unfold compositionCutSignInt
  rw [hres (-z), hres z, Int.cast_neg]
  exact hneg (z : ZMod N)

/-- Every actual discrepancy frontier generator has a zero signed value at its negative. -/
theorem evenCutDisagreements_negative_sign_zero {N : ℕ} (α : Composition N) (hN : 0 < N)
    (p : ℕ) (T : Finset ℕ) (t : ℕ) (ht : t ∈ evenCutDisagreements α p T) :
    compositionCutSignInt α (-(t : ℤ)) = 0 := by
  have hb := evenCutDisagreements_bounds α p T t ht
  obtain ⟨_, _, _, heven, _, _⟩ := (Finset.mem_filter.mp ht).2
  rw [compositionCutSignInt_neg α hN (t : ℤ)]
  unfold compositionCutSignInt
  rw [compositionCutResidue_nat N t hb.2.1,
    compositionCutSign_eq_zero_of_not_one α t heven, neg_zero]

end SkewClassInflation
