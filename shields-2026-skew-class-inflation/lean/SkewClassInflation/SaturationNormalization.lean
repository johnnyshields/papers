/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.SaturationPrivateCorner
import SkewClassInflation.TriangularSubstitution
import Mathlib.Algebra.MvPolynomial.Monad

/-!
# Triangular power substitution after normalizing the seam generators

The injectivity input to `eq:saturation-substitution` in
`shields-2026-skew-class-inflation.tex`.  Setting the small and large
seam generators to one leaves every private pivot intact and gives
nonzero constant leading coefficients.  Sorry-free.
-/

namespace SkewClassInflation.SaturationInner

open SkewJacobiNegative MvPolynomial

variable (A : SaturationInner)

/-- Set both seam generators to one and retain every other independent generator. -/
noncomputable def normalizeSeams : CompleteRing →ₐ[ℚ] CompleteRing :=
  MvPolynomial.bind₁ (fun j : ℕ+ => if j.val = A.c ∨ j.val = A.d then 1 else MvPolynomial.X j)

/-- Both specified overlap values normalize to one, including the original unit when `c = 0`. -/
theorem normalizeSeams_complete (v : ℕ) (hv : v = A.c ∨ v = A.d) :
    A.normalizeSeams (complete v) = 1 := by
  by_cases hz : v = 0
  · subst v
    rw [Nat.cast_zero, complete_zero, map_one]
  · let j : ℕ+ := ⟨v, by omega⟩
    have hc : complete (v : ℤ) = MvPolynomial.X j := complete_nat j
    rw [hc]
    simp only [normalizeSeams, MvPolynomial.bind₁, MvPolynomial.aeval_X]
    change (if v = A.c ∨ v = A.d then (1 : CompleteRing) else MvPolynomial.X j) = 1
    exact ite_eq_left hv

/-- Normalization cannot introduce a generator absent from the original support. -/
theorem normalizeSeams_vars_subset (p : CompleteRing) : (A.normalizeSeams p).vars ⊆ p.vars := by
  classical
  intro j hj
  obtain ⟨i, hip, hji⟩ := MvPolynomial.mem_vars_bind₁
    (fun i : ℕ+ => if i.val = A.c ∨ i.val = A.d then (1 : CompleteRing) else MvPolynomial.X i) p hj
  by_cases hi : i.val = A.c ∨ i.val = A.d
  · simp only [hi, ite_true, MvPolynomial.vars_one, Finset.notMem_empty] at hji
  · simp only [hi, ite_false, MvPolynomial.vars_X, Finset.mem_singleton] at hji
    exact hji ▸ hip

/-- The private pivot is the actual largest-generator index of the full repeated power. -/
def privateLabel (m : ℕ+) : ℕ+ :=
  ⟨(A.power m.val m.pos).toBetaDiagram.largestLabel.toNat,
    by have := (A.power m.val m.pos).toBetaDiagram.largestLabel_pos; omega⟩

/-- Exact affine index of the actual private pivot. -/
theorem privateLabel_value (m : ℕ+) :
    ((A.privateLabel m).val : ℤ) = (m.val : ℤ) * A.spanIncrement + A.d := by
  change (((A.power m.val m.pos).toBetaDiagram.largestLabel.toNat : ℕ) : ℤ) = _
  rw [Int.toNat_of_nonneg (A.power m.val m.pos).toBetaDiagram.largestLabel_pos.le,
    A.power_largest_label]

/-- Positive copy orders have strictly increasing private pivots. -/
theorem privateLabel_strictMono : StrictMono A.privateLabel := by
  intro m n hmn
  have hm := A.privateLabel_value m
  have hn := A.privateLabel_value n
  have hq := A.spanIncrement_pos
  have he : (m.val : ℤ) < n.val := by exact_mod_cast hmn
  change (A.privateLabel m).val < (A.privateLabel n).val
  exact_mod_cast (show (((A.privateLabel m).val : ℤ) < (A.privateLabel n).val) by
    nlinarith)

/-- No private pivot can coincide with either seam generator. -/
theorem privateLabel_above_seam (m : ℕ+) : A.d < (A.privateLabel m).val := by
  have he := A.privateLabel_value m
  have hm : (0 : ℤ) < m.val := by exact_mod_cast m.pos
  have hq := A.spanIncrement_pos
  exact_mod_cast (show (A.d : ℤ) < (A.privateLabel m).val by nlinarith)

/-- Normalization fixes every actual private generator. -/
theorem normalizeSeams_privateLabel (m : ℕ+) :
    A.normalizeSeams (MvPolynomial.X (A.privateLabel m)) = MvPolynomial.X (A.privateLabel m) := by
  have hn : ¬ ((A.privateLabel m).val = A.c ∨ (A.privateLabel m).val = A.d) := by
    have := A.privateLabel_above_seam m
    have := A.c_lt_d
    omega
  simp only [normalizeSeams, MvPolynomial.bind₁, MvPolynomial.aeval_X, ite_eq_right hn]

/-- The normalized actual power has a nonzero constant private coefficient and lower residual. -/
theorem normalized_power_corner (m : ℕ+) :
    A.normalizeSeams (A.power m.val m.pos).toBetaDiagram.schur =
      (-1 : CompleteRing) ^ (m.val * A.k) * MvPolynomial.X (A.privateLabel m) +
        A.normalizeSeams (A.power m.val m.pos).toBetaDiagram.cornerResidual := by
  let D := (A.power m.val m.pos).toBetaDiagram
  have he := D.schur_corner_split
  change D.schur = D.cornerCoefficient * MvPolynomial.X (A.privateLabel m) + D.cornerResidual at he
  have hc : A.normalizeSeams D.cornerCoefficient = (-1 : CompleteRing) ^ (m.val * A.k) := by
    change A.normalizeSeams ((-1 : CompleteRing) ^ (m.val * A.k) *
      (A.power m.val m.pos).toBetaDiagram.cornerPolynomial) = _
    rw [map_mul, A.power_cofactor, map_pow, map_pow,
      A.normalizeSeams_complete A.c (Or.inl rfl), one_pow, mul_one, map_neg, map_one]
  have hh := congrArg (fun p : CompleteRing => A.normalizeSeams p) he
  rw [map_add, map_mul, hc, A.normalizeSeams_privateLabel] at hh
  exact hh

/-- Every normalized residual variable is strictly below its actual private pivot. -/
theorem normalized_residual_vars_lt (m : ℕ+) (j : ℕ+)
    (hj : j ∈ (A.normalizeSeams (A.power m.val m.pos).toBetaDiagram.cornerResidual).vars) :
    j < A.privateLabel m := by
  have he := (A.power_corner_expansion m.val m.pos).2 j
    (A.normalizeSeams_vars_subset _ hj)
  rw [← A.privateLabel_value m] at he
  exact_mod_cast he

/-- The normalized full power retains degree one in its own private generator. -/
theorem normalized_power_private_degree (m : ℕ+) :
    (A.normalizeSeams (A.power m.val m.pos).toBetaDiagram.schur).degreeOf
      (A.privateLabel m) = 1 := by
  rw [A.normalized_power_corner]
  have hd := degreeOf_zero_of_vars_lt
    (A.normalizeSeams (A.power m.val m.pos).toBetaDiagram.cornerResidual)
    (A.privateLabel m) (A.normalized_residual_vars_lt m)
  have hc : (-1 : CompleteRing) ^ (m.val * A.k) = MvPolynomial.C ((-1 : ℚ) ^ (m.val * A.k)) := by
    simp
  have hprod : (((-1 : CompleteRing) ^ (m.val * A.k)) *
      MvPolynomial.X (A.privateLabel m)).degreeOf (A.privateLabel m) = 1 := by
    rw [MvPolynomial.degreeOf_mul_eq (pow_ne_zero _ (by norm_num)) (MvPolynomial.X_ne_zero _),
      hc, MvPolynomial.degreeOf_C, MvPolynomial.degreeOf_X_self, zero_add]
  rw [MvPolynomial.degreeOf_add_eq_of_degreeOf_lt (by rw [hd, hprod]; decide), hprod]

/-- A later private pivot occurs in no earlier normalized power. -/
theorem normalized_power_later_degree (m n : ℕ+) (hmn : m < n) :
    (A.normalizeSeams (A.power m.val m.pos).toBetaDiagram.schur).degreeOf
      (A.privateLabel n) = 0 := by
  apply degreeOf_zero_of_vars_lt
  intro j hj
  have he := (A.power m.val m.pos).toBetaDiagram.vars_le_largestLabel j
    (A.normalizeSeams_vars_subset _ hj)
  rw [A.power_largest_label, ← A.privateLabel_value m] at he
  have hbound : j ≤ A.privateLabel m := by exact_mod_cast he
  exact hbound.trans_lt (A.privateLabel_strictMono hmn)

/-- Substituting the actual seam-normalized power functions is injective. -/
theorem normalized_substitution_injective :
    Function.Injective (MvPolynomial.aeval (fun m : ℕ+ =>
      A.normalizeSeams (A.power m.val m.pos).toBetaDiagram.schur) :
        CompleteRing →ₐ[ℚ] CompleteRing) :=
  triangular_pnat_injective _ A.privateLabel A.normalized_power_private_degree
    A.normalized_power_later_degree

end SkewClassInflation.SaturationInner
