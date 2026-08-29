/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Shields.LinearAlgebra.Matrix.TotallyNonneg.Reciprocal
import Shields.Analysis.SpecificLimits.LogConcaveRatio

/-!
# A totally nonnegative Toeplitz symbol forces a nonnegative characteristic root

A sequence whose lower-triangular Toeplitz truncations have nonnegative `2 × 2` minors is
log-concave: `c k * c (k + 2) ≤ c (k + 1) ^ 2` is one such minor, taken on the rows `k + 1`,
`k + 2` and the columns `0`, `1`.  Feeding that into `Shields.exists_nonneg_root_of_logConcave_rec`
turns total nonnegativity into a statement about the *roots* of any linear recursion the sequence
satisfies: there must be a nonnegative real one.

Combined with `Shields.minorsNonneg_toeplitzLower_altSeq`, which carries total nonnegativity from
a symbol to the alternated coefficients of its reciprocal, this is the step the classical
Aissen--Schoenberg--Whitney argument takes with Pringsheim's theorem.

## Main results

* `Shields.logConcave_of_minorsNonneg` — nonnegative `2 × 2` Toeplitz minors give log-concavity.
* `Shields.exists_nonneg_root_of_minorsNonneg_rec` — a strictly positive sequence with
  nonnegative `2 × 2` Toeplitz minors, satisfying a linear recursion of order `n`, forces that
  recursion's characteristic polynomial to have a nonnegative real root.
* `Shields.logConcave_altSeq` — the alternated reciprocal coefficients of a totally nonnegative
  symbol are log-concave.

## Implementation notes

The positivity hypothesis is strict, and it is not removable: see the discussion in
`Shields.Analysis.SpecificLimits.LogConcaveRatio`.

## References

* [Aissen, Schoenberg and Whitney, *On the generating functions of totally positive
  sequences I*][Aissen1952GeneratingFunctions]

## Papers depending on this file

* `zero-reconstruction-edrei` — the converse direction for Toeplitz symbols.

## Tags

totally nonnegative, Toeplitz, log-concave, Polya frequency, linear recurrence
-/

namespace Shields

open Finset

/-- **Nonnegative `2 × 2` Toeplitz minors give log-concavity.**  The minor on rows `k + 1`,
`k + 2` and columns `0`, `1` of the truncation of size `k + 3` is exactly
`c (k + 1) ^ 2 - c k * c (k + 2)`. -/
theorem logConcave_of_minorsNonneg {c : ℕ → ℝ}
    (hA : ∀ n, MinorsNonneg 2 (toeplitzLower c n)) (k : ℕ) :
    c k * c (k + 2) ≤ c (k + 1) * c (k + 1) := by
  have hmono : ∀ u v : Fin (k + 3), u < v → StrictMono ![u, v] := by
    intro u v huv x y hxy
    fin_cases x <;> fin_cases y <;> simp_all
  have hrow : (⟨k + 1, by omega⟩ : Fin (k + 3)) < ⟨k + 2, by omega⟩ :=
    Fin.mk_lt_mk.mpr (by omega)
  have hcol : (⟨0, by omega⟩ : Fin (k + 3)) < ⟨1, by omega⟩ :=
    Fin.mk_lt_mk.mpr (by omega)
  have h := hA (k + 3)
    ![⟨k + 1, by omega⟩, ⟨k + 2, by omega⟩] ![⟨0, by omega⟩, ⟨1, by omega⟩]
    (mem_increasingSelections.mpr (hmono _ _ hrow))
    (mem_increasingSelections.mpr (hmono _ _ hcol))
  rw [Matrix.det_fin_two] at h
  simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    toeplitzLower_apply] at h
  norm_num at h
  linarith

/-- **Total nonnegativity forces a nonnegative characteristic root.**  A strictly positive
sequence whose Toeplitz truncations have nonnegative `2 × 2` minors is log-concave, so its
consecutive ratios descend to a limit, and that limit is a root of any linear recursion the
sequence satisfies. -/
theorem exists_nonneg_root_of_minorsNonneg_rec {c : ℕ → ℝ} {n : ℕ} {a : ℕ → ℝ}
    (hpos : ∀ k, 0 < c k) (hA : ∀ m, MinorsNonneg 2 (toeplitzLower c m))
    (hrec : ∀ k, c (k + n) = ∑ i ∈ Finset.range n, a i * c (k + i)) :
    ∃ L : ℝ, 0 ≤ L ∧ L ^ n = ∑ i ∈ Finset.range n, a i * L ^ i :=
  exists_nonneg_root_of_logConcave_rec hpos (logConcave_of_minorsNonneg hA) hrec

/-- The alternated coefficients of the reciprocal of a totally nonnegative symbol are
log-concave.  This is the `2 × 2` case of `Shields.minorsNonneg_toeplitzLower_altSeq`. -/
theorem logConcave_altSeq {a b : ℕ → ℝ} (ha : a 0 = 1)
    (hab : convCoeff a b = fun m => if m = 0 then (1 : ℝ) else 0)
    (hA : ∀ n r, MinorsNonneg r (toeplitzLower a n)) (k : ℕ) :
    altSeq b k * altSeq b (k + 2) ≤ altSeq b (k + 1) * altSeq b (k + 1) :=
  logConcave_of_minorsNonneg
    (fun n => minorsNonneg_toeplitzLower_altSeq ha hab (hA n) 2) k


/-! ### Axiom footprint -/

/-- info: 'Shields.exists_nonneg_root_of_minorsNonneg_rec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_nonneg_root_of_minorsNonneg_rec

/-- info: 'Shields.logConcave_altSeq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms logConcave_altSeq

end Shields
