/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.LinearCombination
import Shields.LinearAlgebra.Matrix.TotallyNonneg.PolyaFrequency
import Shields.LinearAlgebra.Matrix.TotallyNonneg.Reciprocal

/-!
# Total nonnegativity of a quadratic symbol

For a symbol of degree at most two, `1 + p t + q t^2`, total nonnegativity of the lower-triangular
Toeplitz matrices is equivalent to a factorization `(1 + y_1 t)(1 + y_2 t)` with `y_1, y_2 \ge 0`,
i.e. to `p, q \ge 0` together with `4q \le p^2`.

One direction is the finite Pólya-frequency implication of `PolyaFrequency`.  The other runs
through the reciprocal series.  Write `\sum_k c_k t^k` for the expansion of
`1/(1 - p t + q t^2)`; then `(-1)^k c_k` are the coefficients of the reciprocal of the symbol, so
`Shields.altSeq_nonneg` forces `c_k \ge 0` for every `k`.  The `c_k` satisfy the second-order
recurrence `c_{k+2} = p c_{k+1} - q c_k`, and a Chebyshev-type sequence with a negative
discriminant cannot stay nonnegative: the ratios `u_k = c_{k+1}/c_k` satisfy
`u_k - u_{k+1} = (u_k^2 - p u_k + q)/u_k \ge (q - p^2/4)/p`, a fixed positive drop, so finitely
many steps drive `u_k` below zero.

## Main results

* `Shields.discrim_nonneg_of_rec`: a sequence with `c_0 = 1`, `c_1 = p`,
  `c_{k+2} = p c_{k+1} - q c_k` and every term nonnegative has `4q \le p^2`.
* `Shields.minorsNonneg_quadCoeff_iff`: the Toeplitz matrices of `1 + p t + q t^2` have all
  minors nonnegative iff the symbol factors into linear factors with nonnegative roots.

## Implementation notes

The reciprocal sequence is defined directly by its own two-term recurrence
(`Shields.quadInvCoeff`) rather than through `Shields.recipCoeff`, so that the convolution
identity is a three-term computation and the sign twist is a single application of
`Shields.altSeq`.

The equivalence is stated for degree at most two only.  Nonnegativity of the reciprocal
coefficients is genuinely weaker in higher degree: `1 + t + t^2 + t^3` has reciprocal
`1 - t + t^4 - t^5 + \cdots`, whose alternated coefficients `1, 1, 0, 0, 1, 1, 0, 0, \ldots` are
all nonnegative, while the `2 \times 2` minor of its Toeplitz matrix on rows `\{1,2\}` and
columns `\{0,1\}` equals `-1`.  Beyond degree two the classical argument needs the
zero-localization half of the Aissen--Schoenberg--Whitney theorem, which is not proved here.

## References

* M. Aissen, I. J. Schoenberg and A. M. Whitney, *On the generating functions of totally positive
  sequences I*, J. Analyze Math. **2** (1952), 93--103, Lem. 1 and Thm. 1.
* S. M. Fallat and C. R. Johnson, *Totally Nonnegative Matrices*, Princeton Univ. Press, 2011,
  Ch. 1.

## Tags

totally nonnegative, toeplitz matrix, polya frequency, quadratic, discriminant
-/

open Finset

namespace Shields

variable {R : Type*} [CommRing R]

/-- The coefficient sequence of the quadratic `1 + p t + q t^2`. -/
def quadCoeff (p q : R) (m : ℕ) : R :=
  if m = 0 then 1 else if m = 1 then p else if m = 2 then q else 0

@[simp] theorem quadCoeff_zero (p q : R) : quadCoeff p q 0 = 1 := rfl

@[simp] theorem quadCoeff_one (p q : R) : quadCoeff p q 1 = p := rfl

@[simp] theorem quadCoeff_two (p q : R) : quadCoeff p q 2 = q := rfl

theorem quadCoeff_eq_zero (p q : R) {m : ℕ} (hm : 3 ≤ m) : quadCoeff p q m = 0 := by
  rw [quadCoeff, if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- A linear symbol `1 + y t` has vanishing coefficients from degree two on. -/
theorem quadCoeff_zero_eq_zero (y : R) {m : ℕ} (hm : 2 ≤ m) : quadCoeff y 0 m = 0 := by
  rcases Nat.lt_or_ge m 3 with h | h
  · rw [show m = 2 by omega, quadCoeff_two]
  · exact quadCoeff_eq_zero _ _ h

/-! ### The quadratic as a product of two root factors -/

theorem rootProdCoeff_nil : rootProdCoeff ([] : List R) = fun m => if m = 0 then (1 : R) else 0 :=
  rfl

theorem convCoeff_delta_right (a : ℕ → R) :
    convCoeff a (fun m => if m = 0 then (1 : R) else 0) = a := by
  funext m
  rw [convCoeff, Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (Nat.succ_pos m))]
  · simp
  · intro j _ hj
    simp [hj]

theorem rootProdCoeff_cons (y : R) (ys : List R) :
    rootProdCoeff (y :: ys) = convCoeff (quadCoeff y 0) (rootProdCoeff ys) := by
  funext m
  rw [rootProdCoeff, convCoeff, convCoeff]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  rw [quadCoeff]
  split_ifs <;> rfl

theorem rootProdCoeff_singleton (y : R) : rootProdCoeff [y] = quadCoeff y 0 := by
  rw [rootProdCoeff_cons, rootProdCoeff_nil, convCoeff_delta_right]

theorem rootProdCoeff_pair (y₁ y₂ : R) :
    rootProdCoeff [y₁, y₂] = quadCoeff (y₁ + y₂) (y₁ * y₂) := by
  rw [rootProdCoeff_cons, rootProdCoeff_singleton]
  funext m
  rw [convCoeff]
  match m with
  | 0 => simp
  | 1 => simp [Finset.sum_range_succ]
  | 2 => simp [Finset.sum_range_succ]
  | (k + 3) =>
      rw [quadCoeff_eq_zero _ _ (by omega)]
      refine Finset.sum_eq_zero fun j hj => ?_
      rcases Nat.lt_or_ge j 2 with h | h
      · rw [quadCoeff_zero_eq_zero y₁ (by omega : 2 ≤ k + 3 - j), zero_mul]
      · rw [quadCoeff_zero_eq_zero y₂ h, mul_zero]

/-! ### The reciprocal of a quadratic -/

/-- The coefficients of `1/(1 + p t + q t^2)`: `b_0 = 1`, `b_1 = -p`,
`b_{k+2} = -p b_{k+1} - q b_k`. -/
def quadInvCoeff (p q : R) : ℕ → R
  | 0 => 1
  | 1 => -p
  | (k + 2) => -p * quadInvCoeff p q (k + 1) - q * quadInvCoeff p q k

@[simp] theorem quadInvCoeff_zero (p q : R) : quadInvCoeff p q 0 = 1 := by rw [quadInvCoeff]

@[simp] theorem quadInvCoeff_one (p q : R) : quadInvCoeff p q 1 = -p := by rw [quadInvCoeff]

theorem quadInvCoeff_add_two (p q : R) (k : ℕ) :
    quadInvCoeff p q (k + 2) = -p * quadInvCoeff p q (k + 1) - q * quadInvCoeff p q k := by
  rw [quadInvCoeff]

theorem convCoeff_quadCoeff_quadInvCoeff (p q : R) :
    convCoeff (quadCoeff p q) (quadInvCoeff p q) = fun m => if m = 0 then (1 : R) else 0 := by
  funext m
  rw [convCoeff]
  match m with
  | 0 => simp
  | 1 => simp [Finset.sum_range_succ]
  | (k + 2) =>
      have hz : ∀ j ∈ Finset.range k, quadCoeff p q (k + 2 - j) * quadInvCoeff p q j = 0 := by
        intro j hj
        rw [Finset.mem_range] at hj
        rw [quadCoeff_eq_zero _ _ (by omega), zero_mul]
      have e2 : k + 2 - k = 2 := by omega
      have e1 : k + 2 - (k + 1) = 1 := by omega
      have e0 : k + 2 - (k + 2) = 0 := by omega
      rw [if_neg (by omega), show k + 2 + 1 = k + 3 from rfl, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_eq_zero hz, e2, e1, e0,
        quadCoeff_zero, quadCoeff_one, quadCoeff_two, quadInvCoeff_add_two]
      ring

/-- The alternated reciprocal coefficients satisfy the Chebyshev-type recurrence
`c_{k+2} = p c_{k+1} - q c_k`. -/
theorem altSeq_quadInvCoeff_add_two (p q : R) (k : ℕ) :
    altSeq (quadInvCoeff p q) (k + 2)
      = p * altSeq (quadInvCoeff p q) (k + 1) - q * altSeq (quadInvCoeff p q) k := by
  rw [altSeq_apply, altSeq_apply, altSeq_apply, quadInvCoeff_add_two, pow_succ, pow_succ]
  ring

section Real

/-- A Chebyshev-type sequence with nonnegative terms has a nonnegative discriminant.  The ratios
`u_k = c_{k+1}/c_k` drop by at least the fixed amount `(q - p^2/4)/p` at every step, so a negative
discriminant drives them below zero in finitely many steps. -/
theorem discrim_nonneg_of_rec {p q : ℝ} {c : ℕ → ℝ} (h0 : c 0 = 1) (h1 : c 1 = p)
    (hrec : ∀ k, c (k + 2) = p * c (k + 1) - q * c k) (hc : ∀ k, 0 ≤ c k) :
    4 * q ≤ p ^ 2 := by
  by_contra hcon
  rw [not_le] at hcon
  have hq : 0 < q := by nlinarith [sq_nonneg p]
  -- The Casoratian of the recurrence.
  have hcas : ∀ k, c (k + 1) ^ 2 - c (k + 2) * c k = q ^ (k + 1) := by
    intro k
    induction k with
    | zero =>
        have e : c 2 = p * c 1 - q * c 0 := hrec 0
        change c 1 ^ 2 - c 2 * c 0 = q ^ 1
        rw [e, h0, h1]; ring
    | succ k ih =>
        have e1 : c (k + 3) = p * c (k + 2) - q * c (k + 1) := hrec (k + 1)
        have e2 : c (k + 2) = p * c (k + 1) - q * c k := hrec k
        change c (k + 2) ^ 2 - c (k + 3) * c (k + 1) = q ^ (k + 2)
        linear_combination (-(c (k + 1))) * e1 + c (k + 2) * e2 + q * ih
  -- No term vanishes: a zero term makes the Casoratian nonpositive.
  have hpos : ∀ k, 0 < c k := by
    intro k
    match k with
    | 0 => rw [h0]; norm_num
    | (j + 1) =>
        rcases lt_or_eq_of_le (hc (j + 1)) with h | h
        · exact h
        · exfalso
          have hcj := hcas j
          rw [← h] at hcj
          nlinarith [mul_nonneg (hc (j + 2)) (hc j), pow_pos hq (j + 1)]
  have hp : 0 < p := by have := hpos 1; rwa [h1] at this
  set s : ℝ := (q - p ^ 2 / 4) / p with hs_def
  have hspos : 0 < s := div_pos (by linarith) hp
  have hupos : ∀ k, 0 < c (k + 1) / c k := fun k => div_pos (hpos (k + 1)) (hpos k)
  have hurec : ∀ k, c (k + 2) / c (k + 1) = p - q / (c (k + 1) / c k) := by
    intro k
    have hk : c k ≠ 0 := ne_of_gt (hpos k)
    have hk1 : c (k + 1) ≠ 0 := ne_of_gt (hpos (k + 1))
    rw [hrec k, div_div_eq_mul_div]
    field_simp
  have hdrop : ∀ k, c (k + 1) / c k ≤ p → s ≤ c (k + 1) / c k - c (k + 2) / c (k + 1) := by
    intro k hk
    have h1' : 0 < c (k + 1) / c k := hupos k
    have hk : c k ≠ 0 := ne_of_gt (hpos k)
    have hk1 : c (k + 1) ≠ 0 := ne_of_gt (hpos (k + 1))
    have hkey : q - p ^ 2 / 4
        ≤ (c (k + 1) / c k - c (k + 2) / c (k + 1)) * (c (k + 1) / c k) := by
      rw [hurec k]
      have he : (c (k + 1) / c k - (p - q / (c (k + 1) / c k))) * (c (k + 1) / c k)
          = (c (k + 1) / c k) ^ 2 - p * (c (k + 1) / c k) + q := by
        field
      rw [he]
      nlinarith [sq_nonneg (c (k + 1) / c k - p / 2)]
    have hd : 0 ≤ c (k + 1) / c k - c (k + 2) / c (k + 1) := by nlinarith
    have h2 : q - p ^ 2 / 4 ≤ (c (k + 1) / c k - c (k + 2) / c (k + 1)) * p := by nlinarith
    rw [hs_def, div_le_iff₀ hp]
    exact h2
  have hbound : ∀ k : ℕ, c (k + 1) / c k ≤ p - k * s := by
    intro k
    induction k with
    | zero => rw [h0, h1]; norm_num
    | succ k ih =>
        have hle : c (k + 1) / c k ≤ p := by
          have : (0 : ℝ) ≤ (k : ℝ) * s := mul_nonneg (Nat.cast_nonneg k) (le_of_lt hspos)
          linarith
        have := hdrop k hle
        push_cast
        change c (k + 2) / c (k + 1) ≤ p - ((k : ℝ) + 1) * s
        nlinarith
  obtain ⟨N, hN⟩ := exists_nat_gt (p / s)
  rw [div_lt_iff₀ hspos] at hN
  have := hbound N
  have := hupos N
  linarith

/-! ### The equivalence -/

/-- **Total nonnegativity of a quadratic symbol.**  The lower-triangular Toeplitz matrices of
`1 + p t + q t^2` have every increasing-selection minor nonnegative exactly when the symbol is a
product of two linear factors with nonnegative roots.  This is the Aissen--Schoenberg--Whitney
equivalence in degree two, both directions. -/
theorem minorsNonneg_quadCoeff_iff {p q : ℝ} :
    (∀ n r, MinorsNonneg r (toeplitzLower (quadCoeff p q) n)) ↔
      ∃ y₁ y₂ : ℝ, 0 ≤ y₁ ∧ 0 ≤ y₂ ∧ quadCoeff p q = rootProdCoeff [y₁, y₂] := by
  constructor
  · intro hA
    have hent : ∀ k, 0 ≤ quadCoeff p q k :=
      coeff_nonneg_of_minorsNonneg (fun n => hA n 1)
    have hp : 0 ≤ p := by simpa using hent 1
    have hq : 0 ≤ q := by simpa using hent 2
    have hcnn : ∀ k, 0 ≤ altSeq (quadInvCoeff p q) k :=
      altSeq_nonneg (quadCoeff_zero p q) (convCoeff_quadCoeff_quadInvCoeff p q) hA
    have hdisc : 4 * q ≤ p ^ 2 :=
      discrim_nonneg_of_rec (by simp) (by simp)
        (altSeq_quadInvCoeff_add_two p q) hcnn
    set d : ℝ := Real.sqrt (p ^ 2 - 4 * q) with hd_def
    have hdnn : 0 ≤ d := Real.sqrt_nonneg _
    have hdsq : d ^ 2 = p ^ 2 - 4 * q := Real.sq_sqrt (by linarith)
    have hdp : d ≤ p := by
      rw [hd_def]
      calc Real.sqrt (p ^ 2 - 4 * q) ≤ Real.sqrt (p ^ 2) := Real.sqrt_le_sqrt (by linarith)
        _ = p := Real.sqrt_sq hp
    refine ⟨(p + d) / 2, (p - d) / 2, by linarith, by linarith, ?_⟩
    rw [rootProdCoeff_pair]
    congr 1
    · ring
    · nlinarith
  · rintro ⟨y₁, y₂, hy₁, hy₂, hpq⟩ n r
    rw [hpq]
    exact minorsNonneg_rootProd [y₁, y₂] (by
      intro y hy
      rcases List.mem_cons.mp hy with h | h
      · exact h ▸ hy₁
      · rcases List.mem_cons.mp h with h | h
        · exact h ▸ hy₂
        · exact absurd h (List.not_mem_nil)) r n

end Real

end Shields
