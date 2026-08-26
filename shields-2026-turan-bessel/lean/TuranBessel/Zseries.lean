/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import TuranBessel.Convolution
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# The reciprocal-gamma series and the weights `S_m`

Formalizes `shields-2026-turan-bessel.tex`, `sec:main` (`eq:Zdef`) and «Reciprocal-gamma
convolution and canonical--microcanonical structure»
(`sec:coefficients`), the step immediately after `lem:convolution`:
```
  Z(a,λ) = ∑_{k≥0} λ^k/(k! Γ(a+k)),      [λ^m] Z(a,λ)² = S_m .
```

`Z` is entire in `λ`, because `Γ(a+k) ≥ Γ(a) min(a,1)` bounds the reciprocal
gamma weights uniformly and leaves the exponential series as majorant.  Squaring
is then a Cauchy product whose `m`-th coefficient is the diagonal case of
`lem:convolution`.

This is the coefficient identity of `thm:coefficients` for the scalar entry;
the matrix entries additionally need parameter differentiation of `1/Γ(a+k)`,
which produces the polygamma family.

Sorry-free and axiom-clean.
-/

open scoped BigOperators
open Finset

namespace TuranBessel

variable {a : ℝ}

/-! ### A uniform lower bound on the gamma weights -/

/-- `(a)_k ≥ min(a,1)` for `a > 0`: the first factor is `a` and every later one
is at least `1`. -/
theorem min_one_le_poch (ha : 0 < a) (k : ℕ) : min a 1 ≤ poch a k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk
        simp [poch_succ]
      · have h1 : (1 : ℝ) ≤ a + (k : ℝ) := by
          have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
          linarith
        have hmin : 0 < min a 1 := lt_min ha one_pos
        rw [poch_succ]
        nlinarith [ih]

/-- `Γ(a+k) ≥ Γ(a) min(a,1) > 0`, uniformly in `k`. -/
theorem Gamma_mul_min_le_Gamma_add (ha : 0 < a) (k : ℕ) :
    Real.Gamma a * min a 1 ≤ Real.Gamma (a + (k : ℝ)) := by
  rw [Gamma_add_natCast ha k]
  exact mul_le_mul_of_nonneg_left (min_one_le_poch ha k) (Real.Gamma_pos_of_pos ha).le

/-! ### The series -/

/-- The `k`-th term of `Z(a,λ) = ∑ λ^k/(k!Γ(a+k))` (`eq:Zdef`). -/
noncomputable def zterm (a lam : ℝ) (k : ℕ) : ℝ :=
  lam ^ k / ((Nat.factorial k : ℝ) * Real.Gamma (a + (k : ℝ)))

theorem summable_norm_zterm (ha : 0 < a) (lam : ℝ) :
    Summable (fun k => ‖zterm a lam k‖) := by
  have hGa : 0 < Real.Gamma a := Real.Gamma_pos_of_pos ha
  have hmin : 0 < min a 1 := lt_min ha one_pos
  have hD : 0 < Real.Gamma a * min a 1 := mul_pos hGa hmin
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
    ((Real.summable_pow_div_factorial |lam|).mul_left (1 / (Real.Gamma a * min a 1)))
  have hGk : 0 < Real.Gamma (a + (k : ℝ)) :=
    Real.Gamma_pos_of_pos (by have := Nat.cast_nonneg (α := ℝ) k; linarith)
  have hfk : (0 : ℝ) < (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hnorm : ‖zterm a lam k‖
      = |lam| ^ k / ((Nat.factorial k : ℝ) * Real.Gamma (a + (k : ℝ))) := by
    rw [zterm, Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos (mul_pos hfk hGk)]
  have hlow : Real.Gamma a * min a 1 ≤ Real.Gamma (a + (k : ℝ)) :=
    Gamma_mul_min_le_Gamma_add ha k
  have hinv : 1 / Real.Gamma (a + (k : ℝ)) ≤ 1 / (Real.Gamma a * min a 1) :=
    one_div_le_one_div_of_le hD hlow
  have habs : (0 : ℝ) ≤ |lam| ^ k / (Nat.factorial k : ℝ) := by positivity
  rw [hnorm]
  calc |lam| ^ k / ((Nat.factorial k : ℝ) * Real.Gamma (a + (k : ℝ)))
      = (|lam| ^ k / (Nat.factorial k : ℝ)) * (1 / Real.Gamma (a + (k : ℝ))) := by
        field_simp
    _ ≤ (|lam| ^ k / (Nat.factorial k : ℝ)) * (1 / (Real.Gamma a * min a 1)) :=
        mul_le_mul_of_nonneg_left hinv habs
    _ = 1 / (Real.Gamma a * min a 1) * (|lam| ^ k / (Nat.factorial k : ℝ)) := by ring

theorem summable_zterm (ha : 0 < a) (lam : ℝ) : Summable (zterm a lam) :=
  (summable_norm_zterm ha lam).of_norm

/-- `Z(a,λ)`, the reciprocal-gamma series of `eq:Zdef`. -/
noncomputable def Zfun (a lam : ℝ) : ℝ := ∑' k, zterm a lam k

/-- `Z(a,λ) > 0` for `a > 0` and `λ ≥ 0`. -/
theorem Zfun_pos {a lam : ℝ} (ha : 0 < a) (hlam : 0 ≤ lam) : 0 < Zfun a lam := by
  refine (summable_zterm ha lam).tsum_pos (fun k => ?_) 0 ?_
  · have hGk : 0 < Real.Gamma (a + (k : ℝ)) :=
      Real.Gamma_pos_of_pos (by have := Nat.cast_nonneg (α := ℝ) k; linarith)
    have hfk : (0 : ℝ) < (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos k
    exact div_nonneg (pow_nonneg hlam k) (by positivity)
  · have hGa : 0 < Real.Gamma a := Real.Gamma_pos_of_pos ha
    simp only [zterm, pow_zero, Nat.factorial_zero, Nat.cast_one, Nat.cast_zero, add_zero,
      one_mul]
    positivity

/-! ### The square -/

/-- The weight `S_m = (2a+m-1)_m/(m! Γ(a+m)²)` of `sec:coefficients`. -/
noncomputable def sweight (a : ℝ) (m : ℕ) : ℝ :=
  poch (2 * a + (m : ℝ) - 1) m / ((Nat.factorial m : ℝ) * Real.Gamma (a + (m : ℝ)) ^ 2)

theorem sweight_pos (ha : 0 < a) (m : ℕ) : 0 < sweight a m := by
  have hG : 0 < Real.Gamma (a + (m : ℝ)) :=
    Real.Gamma_pos_of_pos (by have := Nat.cast_nonneg (α := ℝ) m; linarith)
  have hfm : (0 : ℝ) < (Nat.factorial m : ℝ) := by exact_mod_cast Nat.factorial_pos m
  have hnum : 0 < poch (2 * a + (m : ℝ) - 1) m :=
    poch_pos (fun i hi => by
      have hle : (i : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hi
      nlinarith [ha, hle, Nat.cast_nonneg (α := ℝ) i])
  rw [sweight]
  positivity

/-- **`[λ^m] Z(a,λ)² = S_m`** (`sec:coefficients`, the display after
`lem:convolution`).  The Cauchy square of the reciprocal-gamma series has the
diagonal convolution weights as coefficients. -/
theorem Zfun_sq (ha : 0 < a) (lam : ℝ) :
    Zfun a lam ^ 2 = ∑' m, sweight a m * lam ^ m := by
  have hnorm := summable_norm_zterm ha lam
  rw [Zfun, sq, tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hnorm hnorm]
  refine tsum_congr fun m => ?_
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hconv := gamma_convolution_diag ha m
  have hterm : ∀ i ∈ range (m + 1),
      zterm a lam i * zterm a lam (m - i)
        = lam ^ m * (1 / ((Nat.factorial i : ℝ) * (Nat.factorial (m - i) : ℝ)
            * Real.Gamma (a + (i : ℝ)) * Real.Gamma (a + ((m - i : ℕ) : ℝ)))) := by
    intro i hi
    have him : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hpow : lam ^ i * lam ^ (m - i) = lam ^ m := by
      rw [← pow_add, Nat.add_sub_cancel' him]
    simp only [zterm]
    rw [div_mul_div_comm, hpow]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hconv, sweight]
  ring

/-- The square-root-free weight of `Coefficients` is the analytic weight with the
common factor `Γ(a)²` removed: `sred a m = S_m Γ(a)²`.  Every sign statement
about `Δ_n` is therefore a statement about `S_m` up to the positive factor
`Γ(a)^{-4}`. -/
theorem sred_eq_sweight_mul (ha : 0 < a) (m : ℕ) :
    sred a m = sweight a m * Real.Gamma a ^ 2 := by
  rw [sweight]
  exact sred_eq_weight_mul_Gamma_sq ha m

end TuranBessel
