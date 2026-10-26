/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.SignedNormalProducts

/-!
# Signed rational residue matching and the whole defect

Supports `shields-2026-skew-corner-descent.tex` (`eq:residue-match`,
`eq:original-defect`, `lem:original-transfer`). A geometric cross identity and
exact signed rational matching produce the raw defect matching equation.
All integer exponents, including negative multiplicities, are retained. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open scoped BigOperators

/-- Geometric matching converts the standing signed rational match into the
raw original defect's matching equation. No raw defect equality is assumed. -/
theorem rationalDefect_residue_match {F ι : Type*} [Field F]
    (f E w β ε : F) (s : Finset ι) (α : ι → F) (e : ι → ℤ) (a b : ℕ)
    (hf : f ≠ 0) (hw : w ≠ 0) (hcross : E * w = f ^ 2)
    (hdegree : (∑ i ∈ s, e i) = (b : ℤ) - a)
    (hmatch : f ^ a / w ^ b = ε * ∏ i ∈ s, (β / f ^ 2 - α i) ^ e i) :
    E ^ b = ε * f ^ a * ∏ i ∈ s, (β - α i * f ^ 2) ^ e i := by
  classical
  have hg : f ^ 2 ≠ 0 := pow_ne_zero 2 hf
  have hsplit (i : ι) : β / f ^ 2 - α i = (β - α i * f ^ 2) / f ^ 2 := by
    field_simp
  have hprod : (∏ i ∈ s, (f ^ 2) ^ e i) = (f ^ 2) ^ (∑ i ∈ s, e i) := by
    clear hdegree hmatch
    induction s using Finset.induction_on with
    | empty => simp only [Finset.prod_empty, Finset.sum_empty, zpow_zero]
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, zpow_add₀ hg, ih]
  simp_rw [hsplit, div_zpow] at hmatch
  rw [Finset.prod_div_distrib, hprod, hdegree, zpow_sub₀ hg, zpow_natCast, zpow_natCast] at hmatch
  have hE : E = f ^ 2 / w := (eq_div_iff hw).mpr hcross
  have hpow (k : ℕ) : (f ^ 2) ^ k = (f ^ k) ^ 2 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
  calc
    E ^ b = (f ^ a / w ^ b) * ((f ^ 2) ^ b / f ^ a) := by
      rw [hE, div_pow, hpow]
      field_simp
    _ = (ε * ((∏ i ∈ s, (β - α i * f ^ 2) ^ e i) /
        ((f ^ 2) ^ b / (f ^ 2) ^ a))) * ((f ^ 2) ^ b / f ^ a) := by rw [hmatch]
    _ = ε * f ^ a * ∏ i ∈ s, (β - α i * f ^ 2) ^ e i := by
      rw [hpow b, hpow a]
      field_simp
      ring_nf
      simp only [mul_comm (f ^ 2)]

end SkewCornerDescent.Matrix
