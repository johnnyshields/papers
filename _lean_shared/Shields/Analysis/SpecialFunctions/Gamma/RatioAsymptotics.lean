/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Ratio asymptotics for the Gamma function

`Γ(n + a) / Γ(n + b) ∼ n ^ (a - b)` as `n → ∞` along the natural numbers, for complex
shifts `a` and `b` avoiding the poles.

Mathlib carries Euler's limit `Complex.GammaSeq_tendsto_Gamma` but no ratio asymptotic, and
the ratio does not need Stirling.  The Pochhammer denominator of `Complex.GammaSeq` is a
quotient of Gamma values, so Euler's limit already says

`n ^ s * Γ(n + 1) / Γ(s + n + 1) → 1`,

and the two-parameter statement is the quotient of two copies of that, at `s = a - 1` and
`s = b - 1`.

The hypothesis `∀ m : ℕ, a ≠ 1 - m` says exactly that none of `a, a + 1, a + 2, …` is a pole
of `Γ`, so every Gamma value appearing is nonzero.

## Main results

* `Shields.Gamma_add_natCast_add_one` — `Γ(s + n + 1) = Γ(s) * ∏ j ≤ n, (s + j)`.
* `Shields.Gamma_natCast_add_ne_zero` — `Γ(n + a) ≠ 0` for every `n`, off the poles.
* `Shields.gammaSeq_eq` — `GammaSeq s n = n ^ s * Γ(n + 1) * Γ(s) / Γ(s + n + 1)`.
* `Shields.tendsto_cpow_mul_Gamma_div_Gamma` — `n ^ s * Γ(n + 1) / Γ(s + n + 1) → 1`.
* `Shields.tendsto_Gamma_div_Gamma_div_cpow` — `Γ(n + a) / (Γ(n + b) * n ^ (a - b)) → 1`.
* `Shields.tendsto_Gamma_div_Gamma_div_rpow` — the same statement for `Real.Gamma`.

## Papers depending on this file

* `growing-rank-edrei` — the entrywise half of `lem:trace-norm`.  The balanced factors of
  the excitation determinant are built from Lagrange cardinal functions whose entries are
  ratios of Gamma values at shifted arguments; the limit kernel `eq:gamma-cardinal` is what
  those ratios converge to, one entry at a time.

Sorry-free.
-/

namespace Shields

open Filter Topology

/-- Off the poles of `Γ`, the Pochhammer product appearing in `Complex.GammaSeq` is a
quotient of Gamma values: `Γ(s + n + 1) = Γ(s) * ∏_{j = 0}^{n} (s + j)`.

The leading capital follows Mathlib's own `Real.Gamma_add_one` and `Complex.Gamma_ne_zero`:
`Gamma` is one of the conventionally-capital function names, so a theorem about it opens on
`Gamma_` rather than on `gamma_`. -/
theorem Gamma_add_natCast_add_one {s : ℂ} (hs : ∀ m : ℕ, s ≠ -m) (n : ℕ) :
    Complex.Gamma (s + n + 1) = Complex.Gamma s * ∏ j ∈ Finset.range (n + 1), (s + j) := by
  induction n with
  | zero =>
    have h0 : s ≠ 0 := by simpa using hs 0
    rw [Finset.prod_range_one, Nat.cast_zero, add_zero, Complex.Gamma_add_one s h0, mul_comm]
  | succ n ih =>
    have hne : s + (n : ℂ) + 1 ≠ 0 := by
      intro h
      refine hs (n + 1) ?_
      push_cast
      linear_combination h
    have harg : s + ((n + 1 : ℕ) : ℂ) + 1 = s + (n : ℂ) + 1 + 1 := by push_cast; ring
    rw [Finset.prod_range_succ, harg, Complex.Gamma_add_one _ hne, ih]
    push_cast
    ring

/-- Each factor of the Pochhammer product is nonzero off the poles. -/
theorem prod_add_natCast_ne_zero {s : ℂ} (hs : ∀ m : ℕ, s ≠ -m) (n : ℕ) :
    (∏ j ∈ Finset.range (n + 1), (s + (j : ℂ))) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun j _ h => hs j ?_
  linear_combination h

/-- `Γ(s + n + 1)` is nonzero whenever `s` avoids the poles of `Γ`. -/
theorem Gamma_add_natCast_add_one_ne_zero {s : ℂ} (hs : ∀ m : ℕ, s ≠ -m) (n : ℕ) :
    Complex.Gamma (s + n + 1) ≠ 0 := by
  refine Complex.Gamma_ne_zero fun m h => hs (m + n + 1) ?_
  push_cast at h ⊢
  linear_combination h

/-- **`Γ(n + a)` is nonzero at every natural `n`**, when `a` misses `1, 0, -1, …`.

That hypothesis is what `∀ m : ℕ, a ≠ 1 - m` says, and this is the only use made of it besides
shifting into `Complex.Gamma_ne_zero`'s own form: the forward translates `a, a+1, a+2, …` are then
all off the poles, so every Gamma value in the ratio is invertible. -/
theorem Gamma_natCast_add_ne_zero {a : ℂ} (ha : ∀ m : ℕ, a ≠ 1 - m) (n : ℕ) :
    Complex.Gamma ((n : ℂ) + a) ≠ 0 := by
  refine Complex.Gamma_ne_zero fun m h => ha (m + n + 1) ?_
  push_cast at h ⊢
  linear_combination h

/-- Euler's sequence rewritten with its denominator as a Gamma quotient. -/
theorem gammaSeq_eq {s : ℂ} (hs : ∀ m : ℕ, s ≠ -m) (n : ℕ) :
    Complex.GammaSeq s n
      = (n : ℂ) ^ s * Complex.Gamma (n + 1) * Complex.Gamma s / Complex.Gamma (s + n + 1) := by
  have hG : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero hs
  have hP := prod_add_natCast_ne_zero hs n
  simp only [Complex.GammaSeq]
  rw [Gamma_add_natCast_add_one hs n, Complex.Gamma_nat_eq_factorial]
  field_simp

/-- The one-parameter ratio asymptotic, which is Euler's limit divided by `Γ(s)`. -/
theorem tendsto_cpow_mul_Gamma_div_Gamma {s : ℂ} (hs : ∀ m : ℕ, s ≠ -m) :
    Tendsto (fun n : ℕ => (n : ℂ) ^ s * Complex.Gamma (n + 1) / Complex.Gamma (s + n + 1))
      atTop (𝓝 1) := by
  have hG : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero hs
  have h := (Complex.GammaSeq_tendsto_Gamma s).div_const (Complex.Gamma s)
  rw [div_self hG] at h
  have heq : ∀ n : ℕ, Complex.GammaSeq s n / Complex.Gamma s
      = (n : ℂ) ^ s * Complex.Gamma (n + 1) / Complex.Gamma (s + n + 1) := by
    intro n
    have hd := Gamma_add_natCast_add_one_ne_zero hs n
    rw [gammaSeq_eq hs n]
    field_simp
  simpa only [heq] using h

/-- `Γ(n + a) / Γ(n + b) ∼ n ^ (a - b)`.  The hypotheses say that `a` and `b` avoid the
poles of `Γ` together with all their forward integer translates. -/
theorem tendsto_Gamma_div_Gamma_div_cpow {a b : ℂ}
    (ha : ∀ m : ℕ, a ≠ 1 - m) (hb : ∀ m : ℕ, b ≠ 1 - m) :
    Tendsto (fun n : ℕ => Complex.Gamma (n + a) / (Complex.Gamma (n + b) * (n : ℂ) ^ (a - b)))
      atTop (𝓝 1) := by
  have hsa : ∀ m : ℕ, a - 1 ≠ -m := fun m h => ha m (by linear_combination h)
  have hsb : ∀ m : ℕ, b - 1 ≠ -m := fun m h => hb m (by linear_combination h)
  have Ha : Tendsto
      (fun n : ℕ => (n : ℂ) ^ (a - 1) * Complex.Gamma (n + 1) / Complex.Gamma (n + a))
      atTop (𝓝 1) := by
    have h := tendsto_cpow_mul_Gamma_div_Gamma hsa
    simpa only [show ∀ n : ℕ, a - 1 + (n : ℂ) + 1 = (n : ℂ) + a from fun n => by ring] using h
  have Hb : Tendsto
      (fun n : ℕ => (n : ℂ) ^ (b - 1) * Complex.Gamma (n + 1) / Complex.Gamma (n + b))
      atTop (𝓝 1) := by
    have h := tendsto_cpow_mul_Gamma_div_Gamma hsb
    simpa only [show ∀ n : ℕ, b - 1 + (n : ℂ) + 1 = (n : ℂ) + b from fun n => by ring] using h
  have key := Hb.div Ha one_ne_zero
  rw [one_div_one] at key
  refine key.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  simp only [Pi.div_apply]
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hfac : Complex.Gamma ((n : ℂ) + 1) ≠ 0 := by
    rw [Complex.Gamma_nat_eq_factorial]
    exact_mod_cast Nat.factorial_ne_zero n
  have hGa : Complex.Gamma ((n : ℂ) + a) ≠ 0 := Gamma_natCast_add_ne_zero ha n
  have hGb : Complex.Gamma ((n : ℂ) + b) ≠ 0 := Gamma_natCast_add_ne_zero hb n
  have hpa : (n : ℂ) ^ (a - 1) ≠ 0 := fun h => hn0 ((Complex.cpow_eq_zero_iff _ _).mp h).1
  have hpb : (n : ℂ) ^ (b - 1) ≠ 0 := fun h => hn0 ((Complex.cpow_eq_zero_iff _ _).mp h).1
  have hpab : (n : ℂ) ^ (a - b) ≠ 0 := fun h => hn0 ((Complex.cpow_eq_zero_iff _ _).mp h).1
  have hsplit : (n : ℂ) ^ (a - 1) = (n : ℂ) ^ (a - b) * (n : ℂ) ^ (b - 1) := by
    rw [← Complex.cpow_add _ _ hn0]
    congr 1
    ring
  rw [hsplit]
  field_simp

/-- The real form of `Shields.tendsto_Gamma_div_Gamma_div_cpow`. -/
theorem tendsto_Gamma_div_Gamma_div_rpow {a b : ℝ}
    (ha : ∀ m : ℕ, a ≠ 1 - m) (hb : ∀ m : ℕ, b ≠ 1 - m) :
    Tendsto (fun n : ℕ => Real.Gamma (n + a) / (Real.Gamma (n + b) * (n : ℝ) ^ (a - b)))
      atTop (𝓝 1) := by
  have hac : ∀ m : ℕ, (a : ℂ) ≠ 1 - m := fun m h => ha m (by exact_mod_cast h)
  have hbc : ∀ m : ℕ, (b : ℂ) ≠ 1 - m := fun m h => hb m (by exact_mod_cast h)
  have h := tendsto_Gamma_div_Gamma_div_cpow hac hbc
  have hcast : ∀ n : ℕ,
      Complex.Gamma ((n : ℂ) + a) / (Complex.Gamma ((n : ℂ) + b) * (n : ℂ) ^ ((a : ℂ) - b))
        = ((Real.Gamma ((n : ℝ) + a)
            / (Real.Gamma ((n : ℝ) + b) * (n : ℝ) ^ (a - b)) : ℝ) : ℂ) := by
    intro n
    rw [Complex.ofReal_div, Complex.ofReal_mul,
      Complex.ofReal_cpow (by positivity : (0 : ℝ) ≤ (n : ℝ))]
    push_cast [← Complex.Gamma_ofReal]
    ring_nf
  rw [funext hcast] at h
  have h3 := (Complex.continuous_re.tendsto (1 : ℂ)).comp h
  simp only [Function.comp_def, Complex.ofReal_re, Complex.one_re] at h3
  exact h3

end Shields
