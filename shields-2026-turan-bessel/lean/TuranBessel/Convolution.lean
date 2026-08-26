/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import TuranBessel.Coefficients
import Mathlib.RingTheory.Binomial
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Asymmetric reciprocal-gamma convolution

Formalizes `shields-2026-turan-bessel.tex`, «Reciprocal-gamma convolution and
canonical--microcanonical structure» (`sec:coefficients`, `lem:convolution`,
`eq:asymmetric-convolution`):
```
  ∑_{i=0}^m 1/(i!(m-i)! Γ(α+i) Γ(β+m-i))
      = (α+β+m-1)_m / (m! Γ(α+m) Γ(β+m)),     α, β > 0.
```

The Gamma factors are removable.  `Γ(x+m) = Γ(x)(x)_m` clears every one of them
and leaves the polynomial identity
```
  ∑_{i=0}^m C(m,i) (α+i)_{m-i} (β+m-i)_i = (α+β+m-1)_m,
```
which is Chu–Vandermonde written in ascending Pochhammer symbols.  Reindexing
`(x)_k = (x+k-1)^{\underline{k}}` turns it into the descending form
`Ring.descPochhammer_smeval_add`, so the analytic content is exactly the
Gamma recursion and the combinatorial content is already available.

Sorry-free and axiom-clean.
-/

open scoped BigOperators
open Finset

namespace TuranBessel

/-! ### `poch` as an evaluated ascending Pochhammer polynomial -/

/-- `(x)_{m+1} = (x)_m (x+m)`. -/
theorem poch_succ (x : ℝ) (m : ℕ) : poch x (m + 1) = poch x m * (x + (m : ℝ)) := by
  simp [poch, Finset.prod_range_succ]

/-- The ascending product `(x)_m` of `Coefficients` is the evaluated Mathlib
`ascPochhammer`. -/
theorem poch_eq_ascPochhammer_eval (x : ℝ) (m : ℕ) :
    poch x m = (ascPochhammer ℝ m).eval x := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [poch_succ, ih, ascPochhammer_succ_eval]

/-! ### Gamma shifted by a natural number -/

/-- `Γ(x+m) = Γ(x)(x)_m` for `x > 0`, from the functional equation. -/
theorem Gamma_add_natCast {x : ℝ} (hx : 0 < x) (m : ℕ) :
    Real.Gamma (x + (m : ℝ)) = Real.Gamma x * poch x m := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hpos : (0 : ℝ) < x + (m : ℝ) := by
        have := Nat.cast_nonneg (α := ℝ) m; linarith
      have hcast : x + ((m + 1 : ℕ) : ℝ) = (x + (m : ℝ)) + 1 := by push_cast; ring
      rw [hcast, Real.Gamma_add_one (ne_of_gt hpos), ih, poch_succ]
      ring

/-! ### The Chu–Vandermonde core -/

/-- **The Gamma-free content of `lem:convolution`.**  Ascending Chu–Vandermonde,
```
  ∑_{i=0}^m C(m,i) (α+i)_{m-i} (β+m-i)_i = (α+β+m-1)_m .
```
An identity of polynomials in `(α,β)`, with no analytic hypothesis. -/
theorem poch_vandermonde (α β : ℝ) (m : ℕ) :
    ∑ i ∈ range (m + 1),
        (m.choose i : ℝ) * (poch (α + (i : ℝ)) (m - i) * poch (β + ((m - i : ℕ) : ℝ)) i)
      = poch (α + β + (m : ℝ) - 1) m := by
  have key := Ring.descPochhammer_smeval_add (R := ℝ) (r := β + (m : ℝ) - 1)
    (s := α + (m : ℝ) - 1) m (Commute.all _ _)
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at key
  -- rewrite every descending Pochhammer as an ascending one
  have hdesc : ∀ (r : ℝ) (k : ℕ),
      (descPochhammer ℤ k).smeval r = poch (r - (k : ℝ) + 1) k := fun r k => by
    rw [Polynomial.descPochhammer_smeval_eq_ascPochhammer,
      Polynomial.ascPochhammer_smeval_eq_eval, poch_eq_ascPochhammer_eval]
  simp only [hdesc] at key
  have hlhs : (β + (m : ℝ) - 1 + (α + (m : ℝ) - 1)) - (m : ℝ) + 1 = α + β + (m : ℝ) - 1 := by
    ring
  rw [hlhs] at key
  rw [key]
  refine Finset.sum_congr rfl fun i hi => ?_
  have him : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hsub : ((m - i : ℕ) : ℝ) = (m : ℝ) - (i : ℝ) := Nat.cast_sub him
  have h1 : β + (m : ℝ) - 1 - (i : ℝ) + 1 = β + ((m - i : ℕ) : ℝ) := by rw [hsub]; ring
  have h2 : α + (m : ℝ) - 1 - ((m - i : ℕ) : ℝ) + 1 = α + (i : ℝ) := by rw [hsub]; ring
  rw [h1, h2]
  ring

/-! ### The Gamma form -/

/-- **`lem:convolution`** (`eq:asymmetric-convolution`).  For `α, β > 0` and
`m ∈ ℕ`,
```
  ∑_{i=0}^m 1/(i!(m-i)! Γ(α+i) Γ(β+m-i)) = (α+β+m-1)_m/(m! Γ(α+m) Γ(β+m)).
``` -/
theorem gamma_convolution {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (m : ℕ) :
    ∑ i ∈ range (m + 1),
        1 / ((Nat.factorial i : ℝ) * (Nat.factorial (m - i) : ℝ)
              * Real.Gamma (α + (i : ℝ)) * Real.Gamma (β + ((m - i : ℕ) : ℝ)))
      = poch (α + β + (m : ℝ) - 1) m
          / ((Nat.factorial m : ℝ) * Real.Gamma (α + (m : ℝ)) * Real.Gamma (β + (m : ℝ))) := by
  have hGα : 0 < Real.Gamma (α + (m : ℝ)) :=
    Real.Gamma_pos_of_pos (by have := Nat.cast_nonneg (α := ℝ) m; linarith)
  have hGβ : 0 < Real.Gamma (β + (m : ℝ)) :=
    Real.Gamma_pos_of_pos (by have := Nat.cast_nonneg (α := ℝ) m; linarith)
  have hfm : (0 : ℝ) < (Nat.factorial m : ℝ) := by exact_mod_cast Nat.factorial_pos m
  rw [eq_div_iff (by positivity), Finset.sum_mul, ← poch_vandermonde α β m]
  refine Finset.sum_congr rfl fun i hi => ?_
  have him : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hsub : ((m - i : ℕ) : ℝ) = (m : ℝ) - (i : ℝ) := Nat.cast_sub him
  have hαi : 0 < α + (i : ℝ) := by have := Nat.cast_nonneg (α := ℝ) i; linarith
  have hβmi : 0 < β + ((m - i : ℕ) : ℝ) := by
    have := Nat.cast_nonneg (α := ℝ) (m - i); linarith
  have hGαi : 0 < Real.Gamma (α + (i : ℝ)) := Real.Gamma_pos_of_pos hαi
  have hGβmi : 0 < Real.Gamma (β + ((m - i : ℕ) : ℝ)) := Real.Gamma_pos_of_pos hβmi
  have hfi : (0 : ℝ) < (Nat.factorial i : ℝ) := by exact_mod_cast Nat.factorial_pos i
  have hfmi : (0 : ℝ) < (Nat.factorial (m - i) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (m - i)
  -- split the two Gamma values at `m`
  have hsplitα : Real.Gamma (α + (m : ℝ))
      = Real.Gamma (α + (i : ℝ)) * poch (α + (i : ℝ)) (m - i) := by
    have h := Gamma_add_natCast hαi (m - i)
    rw [hsub] at h
    rw [show α + (m : ℝ) = α + (i : ℝ) + ((m : ℝ) - (i : ℝ)) by ring]
    exact h
  have hsplitβ : Real.Gamma (β + (m : ℝ))
      = Real.Gamma (β + ((m - i : ℕ) : ℝ)) * poch (β + ((m - i : ℕ) : ℝ)) i := by
    have := Gamma_add_natCast hβmi i
    rw [show β + (m : ℝ) = β + ((m - i : ℕ) : ℝ) + (i : ℝ) by rw [hsub]; ring]
    exact this
  -- and the factorials
  have hfact : (Nat.factorial m : ℝ)
      = (m.choose i : ℝ) * ((Nat.factorial i : ℝ) * (Nat.factorial (m - i) : ℝ)) := by
    have h := Nat.choose_mul_factorial_mul_factorial him
    have h' : ((m.choose i * Nat.factorial i * Nat.factorial (m - i) : ℕ) : ℝ)
        = ((Nat.factorial m : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    linarith
  rw [hsplitα, hsplitβ, hfact]
  field_simp

/-! ### The diagonal case and the reduced weight -/

/-- `α = β = a` in `lem:convolution`: the diagonal convolution is the paper's
weight `S_m = (2a+m-1)_m/(m! Γ(a+m)²)` (`sec:coefficients`). -/
theorem gamma_convolution_diag {a : ℝ} (ha : 0 < a) (m : ℕ) :
    ∑ i ∈ range (m + 1),
        1 / ((Nat.factorial i : ℝ) * (Nat.factorial (m - i) : ℝ)
              * Real.Gamma (a + (i : ℝ)) * Real.Gamma (a + ((m - i : ℕ) : ℝ)))
      = poch (2 * a + (m : ℝ) - 1) m
          / ((Nat.factorial m : ℝ) * Real.Gamma (a + (m : ℝ)) ^ 2) := by
  have := gamma_convolution ha ha m
  rw [show a + a + (m : ℝ) - 1 = 2 * a + (m : ℝ) - 1 by ring] at this
  rw [this, sq]
  ring_nf

/-- `sred a m = S_m Γ(a)²`: the square-root-free weight of `Coefficients` is the
analytic weight `S_m` with the common factor `Γ(a)²` removed. -/
theorem sred_eq_weight_mul_Gamma_sq {a : ℝ} (ha : 0 < a) (m : ℕ) :
    sred a m
      = poch (2 * a + (m : ℝ) - 1) m
          / ((Nat.factorial m : ℝ) * Real.Gamma (a + (m : ℝ)) ^ 2) * Real.Gamma a ^ 2 := by
  have hG : Real.Gamma (a + (m : ℝ)) = Real.Gamma a * poch a m := Gamma_add_natCast ha m
  have hGa : 0 < Real.Gamma a := Real.Gamma_pos_of_pos ha
  have hp : 0 < poch a m := poch_pos (fun i _ => by
    have := Nat.cast_nonneg (α := ℝ) i; linarith)
  have hfm : (0 : ℝ) < (Nat.factorial m : ℝ) := by exact_mod_cast Nat.factorial_pos m
  rw [sred, hG]
  field_simp

end TuranBessel
