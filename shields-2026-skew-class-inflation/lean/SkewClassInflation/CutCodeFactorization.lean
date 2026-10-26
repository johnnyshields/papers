/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.EvenCutCodeRefinement
import SkewClassInflation.SignedCutFactorization

/-!
# Literal proper factors from the actual full-code period

The final cut-encoding bridge in factor-reversal reconstruction for
`thm:sharp-inflation` of `shields-2026-skew-class-inflation.tex`.
The full masked code period identifies every nonmultiple actual cut.
The existing cut constructor then supplies both literal factors and
their genuine smaller positive weights.  Sorry-free.
-/

namespace SkewClassInflation

/-- A full masked code period gives the exact nonmultiple proper-cut period. -/
theorem cutCode_periodic_cuts {N p : ℕ} (α : Composition N) (hp : 0 < p) (hpN : p < N)
    (hper : Function.Periodic (periodMask (compositionCutCode α) p) (p : ℤ))
    (x : ℕ) (hxN : x < N) (hmod : x % p ≠ 0) :
    x ∈ properCuts α ↔ x % p ∈ properCuts α := by
  have hxdiv : ¬ p ∣ x := fun hd => hmod (Nat.mod_eq_zero_of_dvd hd)
  have hrdiv : ¬ p ∣ x % p := by
    intro hd
    have hh := Nat.mod_eq_zero_of_dvd hd
    rw [Nat.mod_mod] at hh
    exact hmod hh
  have hxi : ¬ (p : ℤ) ∣ (x : ℤ) := fun hd => hxdiv (Int.natCast_dvd_natCast.mp hd)
  have hri : ¬ (p : ℤ) ∣ ((x % p : ℕ) : ℤ) :=
    fun hd => hrdiv (Int.natCast_dvd_natCast.mp hd)
  have hrN : x % p < N := (Nat.mod_lt x hp).trans hpN
  have hh := periodic_int_remainder (periodMask (compositionCutCode α) p) (p : ℤ) hper (x : ℤ)
  rw [← Int.natCast_emod] at hh
  simp only [periodMask, hxi, hri, ite_false, compositionCutCode,
    compositionCutResidue_nat N x hxN, compositionCutResidue_nat N (x % p) hrN] at hh
  rw [compositionCutCodeNat_cut_iff, compositionCutCodeNat_cut_iff, hh]

/-- The full-code period constructs proper ordinary factors, without a supplied factor datum. -/
theorem proper_factorization_of_cutCode_period {N p : ℕ} (α : Composition N)
    (hp : 1 < p) (hpN : p < N) (hd : p ∣ N)
    (hper : Function.Periodic (periodMask (compositionCutCode α) p) (p : ℤ)) :
    ∃ m : ℕ, 2 ≤ m ∧ m * p = N ∧ ∃ δ : Composition m, ∃ ε : Composition p,
      (compositionProduct δ ε).blocks = α.blocks := by
  let m := N / p
  have hweight : m * p = N := Nat.div_mul_cancel hd
  have hm : 2 ≤ m := by nlinarith
  let θ := α.cast hweight.symm
  have hcuts : properCuts θ = properCuts α := properCuts_cast α hweight.symm
  have hperiod : ∀ x, 0 < x → x < m * p → x % p ≠ 0 →
      (x ∈ properCuts θ ↔ x % p ∈ properCuts θ) := by
    intro x _ hx hm
    rw [hcuts]
    exact cutCode_periodic_cuts α (by omega) hpN hper x (by rwa [hweight] at hx) hm
  have hfactor := periodic_factorization θ (by omega) hperiod
  refine ⟨m, hm, hweight, periodicOuter θ, periodicInner θ, ?_⟩
  exact congrArg Composition.blocks hfactor

end SkewClassInflation
