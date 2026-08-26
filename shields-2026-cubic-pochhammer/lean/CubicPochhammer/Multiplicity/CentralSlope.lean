/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import CubicPochhammer.Main
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# The degree-three kernel in the centrality coordinate, and its central slope

Formalizes `shields-2026-cubic-pochhammer.tex`, `sec:threshold` «The sharp
multiplicity threshold», `eq:r-central-slope`, and
`subsec:first-supercritical-case`.

At `m = 3` and constant weights the residue kernel is a function of
`q = p(1-p)` alone, and `ghat` is that function:
`Ĝ^{(r)}_3(q) = C(3r-2,r-1) qʳ E_r(q)`, where `E_r` is the recursion `dickE`
representing `pʳ + (1-p)ʳ` in `q`.  Its slope at the center `q = 1/4` is the
quantity `eq:r-central-slope` computes, and its sign is the threshold: positive
at `r = 2`, exactly zero at `r = 3`, negative for `r ≥ 4`.

At the critical multiplicity the vanishing is not a coincidence of one
derivative.  `ghat_three_center_expansion` writes the kernel at `p = 1/2 + x`
as an exact polynomial whose quadratic term is absent as well, so the maximum
at the center is quartically flat.

## Main definitions

* `dickE` --- `E_0 = 2`, `E_1 = 1`, `E_{n+2} = E_{n+1} - q E_n`, representing
  `pⁿ + (1-p)ⁿ` in `q = p(1-p)` (`dickE_subst`).
* `ghat` --- the degree-three constant-weight kernel in the coordinate `q`.

## Main statements

* `ghat_eq`, `ghat_three_eq_gmw` --- `ghat` is the residue kernel it claims to
  be, at general `r` in the coordinate `q` and at `r = 3` against
  `Kernel.gmw`.
* `ghat_central_slope` --- `eq:r-central-slope`, the closed form of
  `∂_q Ĝ^{(r)}_3(1/4)`.
* `ghat_central_slope_two`, `ghat_central_slope_three`,
  `ghat_central_slope_neg` --- the three signs, which is the threshold.
* `ghat_three_deriv_pos`, `ghat_three_center_expansion` --- at the critical
  multiplicity the center is a maximum, and a quartically flat one.

## References

* `shields-2026-cubic-pochhammer.tex`, `sec:threshold` «The sharp multiplicity
  threshold»: `eq:r-central-slope`, `subsec:first-supercritical-case`,
  `subsec:intro-central-slope`.
-/

open scoped BigOperators

namespace CubicPochhammer

/-! ### `eq:r-central-slope`: the degree-three kernel in `q = p(1-p)` -/

/-- The polynomial recursion representing `pⁿ + (1-p)ⁿ` in `q = p(1-p)`:
`E_0 = 2`, `E_1 = 1`, `E_{n+2} = E_{n+1} - q E_n`. -/
noncomputable def dickE : ℕ → ℝ → ℝ
  | 0, _ => 2
  | 1, _ => 1
  | (n + 2), q => dickE (n + 1) q - q * dickE n q

@[simp] theorem dickE_zero (q : ℝ) : dickE 0 q = 2 := rfl

@[simp] theorem dickE_one (q : ℝ) : dickE 1 q = 1 := rfl

theorem dickE_succ_succ (n : ℕ) (q : ℝ) :
    dickE (n + 2) q = dickE (n + 1) q - q * dickE n q := rfl

theorem dickE_succ_succ_eq (n : ℕ) :
    dickE (n + 2) = fun q => dickE (n + 1) q - q * dickE n q := rfl

/-- `E_n(p(1-p)) = pⁿ + (1-p)ⁿ`: the recursion is the Newton identity for the
two roots of `t² - t + q`. -/
theorem dickE_subst (n : ℕ) (p : ℝ) : dickE n (p * (1 - p)) = p ^ n + (1 - p) ^ n := by
  suffices h : ∀ k : ℕ, dickE k (p * (1 - p)) = p ^ k + (1 - p) ^ k
      ∧ dickE (k + 1) (p * (1 - p)) = p ^ (k + 1) + (1 - p) ^ (k + 1) from (h n).1
  intro k
  induction k with
  | zero =>
      refine ⟨?_, ?_⟩
      · rw [dickE_zero, pow_zero, pow_zero]; norm_num
      · rw [dickE_one, pow_one, pow_one]; ring
  | succ j ih =>
      refine ⟨ih.2, ?_⟩
      rw [show j + 1 + 1 = j + 2 from rfl, dickE_succ_succ, ih.1, ih.2]
      ring

/-- `E_n(1/4) = 2/2ⁿ`, the central value. -/
theorem dickE_center (n : ℕ) : dickE n (1 / 4) = 2 / 2 ^ n := by
  suffices h : ∀ k : ℕ, dickE k (1 / 4) = 2 / 2 ^ k
      ∧ dickE (k + 1) (1 / 4) = 2 / 2 ^ (k + 1) from (h n).1
  intro k
  induction k with
  | zero => constructor <;> norm_num
  | succ j ih =>
      refine ⟨ih.2, ?_⟩
      rw [show j + 1 + 1 = j + 2 from rfl, dickE_succ_succ, ih.1, ih.2]
      have h : (0 : ℝ) < 2 ^ j := by positivity
      field

/-- `E_n'(1/4) = -4n(n-1)/2ⁿ`, the central slope of the recursion.  Only the
linear term in `1-4q` survives at `q = 1/4`, which is what makes the slope
quadratic in `n`. -/
theorem dickE_hasDerivAt (n : ℕ) :
    HasDerivAt (dickE n) (-(4 * (n : ℝ) * ((n : ℝ) - 1)) / 2 ^ n) (1 / 4) := by
  suffices h : ∀ k : ℕ,
      HasDerivAt (dickE k) (-(4 * (k : ℝ) * ((k : ℝ) - 1)) / 2 ^ k) (1 / 4)
      ∧ HasDerivAt (dickE (k + 1))
          (-(4 * ((k : ℝ) + 1) * (((k : ℝ) + 1) - 1)) / 2 ^ (k + 1)) (1 / 4) from (h n).1
  intro k
  induction k with
  | zero =>
      refine ⟨?_, ?_⟩
      · rw [show (-(4 * ((0 : ℕ) : ℝ) * (((0 : ℕ) : ℝ) - 1)) / 2 ^ (0 : ℕ)) = 0 from by norm_num]
        exact hasDerivAt_const (1 / 4 : ℝ) (2 : ℝ)
      · rw [show (-(4 * (((0 : ℕ) : ℝ) + 1) * ((((0 : ℕ) : ℝ) + 1) - 1)) / 2 ^ (0 + 1 : ℕ)) = 0
          from by norm_num]
        exact hasDerivAt_const (1 / 4 : ℝ) (1 : ℝ)
  | succ j ih =>
      refine ⟨by push_cast at ih ⊢; exact ih.2, ?_⟩
      have hstep : HasDerivAt (dickE (j + 2))
          ((-(4 * ((j : ℝ) + 1) * (((j : ℝ) + 1) - 1)) / 2 ^ (j + 1))
            - (1 * dickE j (1 / 4) + (1 / 4) * (-(4 * (j : ℝ) * ((j : ℝ) - 1)) / 2 ^ j)))
          (1 / 4) := by
        rw [dickE_succ_succ_eq]
        exact ih.2.sub ((hasDerivAt_id (1 / 4 : ℝ)).mul ih.1)
      rw [dickE_center j] at hstep
      have hpow : (0 : ℝ) < 2 ^ j := by positivity
      refine hstep.congr_deriv ?_
      push_cast
      field

/-- The degree-three constant-weight kernel of `prop:multiplicity-threshold` in
the coordinate `q = p(1-p)`:
`Ĝ^{(r)}_3(q) = binom(3r-2,r-1) qʳ E_r(q)`. -/
noncomputable def ghat (r : ℕ) (q : ℝ) : ℝ :=
  (Nat.choose (3 * r - 2) (r - 1) : ℝ) * (q ^ r * dickE r q)

/-- **The reparametrization is the paper's kernel**:
`Ĝ^{(r)}_3(p(1-p)) = binom(3r-2,r-1)[p(1-p)]ʳ(pʳ+(1-p)ʳ) = G^{(r)}_3(p)`. -/
theorem ghat_eq (r : ℕ) (p : ℝ) :
    ghat r (p * (1 - p))
      = (Nat.choose (3 * r - 2) (r - 1) : ℝ) * (p * (1 - p)) ^ r * (p ^ r + (1 - p) ^ r) := by
  rw [ghat, dickE_subst]
  ring

/-- **`eq:r-central-slope`**:
`d/dq Ĝ^{(r)}_3(q)|_{q=1/4} = binom(3r-2,r-1) r(3-r) 2^{2-3r}`.

The chain rule cannot deliver this from `G^{(r)}_3(p)`: `q = p(1-p)` has
vanishing derivative at the center, so the slope is read off the `q`-side
polynomial, through `dickE_center` and `dickE_hasDerivAt`. -/
theorem ghat_hasDerivAt_center {r : ℕ} (hr : 1 ≤ r) :
    HasDerivAt (ghat r)
      ((Nat.choose (3 * r - 2) (r - 1) : ℝ) * ((r : ℝ) * (3 - (r : ℝ))) * 4 / 2 ^ (3 * r))
      (1 / 4) := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
  have hcore : HasDerivAt (fun q : ℝ => q ^ (n + 1) * dickE (n + 1) q)
      (4 * ((n : ℝ) + 1) * (3 - ((n : ℝ) + 1)) / 2 ^ (3 * (n + 1))) (1 / 4) := by
    have hmul := (hasDerivAt_pow (n + 1) (1 / 4 : ℝ)).mul (dickE_hasDerivAt (n + 1))
    rw [dickE_center (n + 1)] at hmul
    refine hmul.congr_deriv ?_
    have hp : ((2 : ℝ) ^ n) ≠ 0 := by positivity
    have e2 : (2 : ℝ) ^ (n + 1) = 2 * (2 : ℝ) ^ n := by rw [pow_succ]; ring
    have e4 : ((1 : ℝ) / 4) ^ n = 1 / ((2 : ℝ) ^ n) ^ 2 := by
      rw [div_pow, one_pow, show (4 : ℝ) = 2 * 2 from by norm_num, mul_pow]
      ring
    have e41 : ((1 : ℝ) / 4) ^ (n + 1) = 1 / (4 * ((2 : ℝ) ^ n) ^ 2) := by
      rw [pow_succ, e4]; ring
    have e8 : (2 : ℝ) ^ (3 * (n + 1)) = 8 * ((2 : ℝ) ^ n) ^ 3 := by
      rw [show 3 * (n + 1) = n + n + n + 3 from by ring, pow_add, pow_add, pow_add]
      norm_num
      ring
    simp only [Nat.add_sub_cancel]
    rw [e2, e4, e41, e8]
    push_cast
    field
  have hconst := hcore.const_mul ((Nat.choose (3 * (n + 1) - 2) ((n + 1) - 1) : ℝ))
  refine hconst.congr_deriv ?_
  push_cast
  ring

/-- `eq:r-central-slope` in `deriv` form. -/
theorem ghat_central_slope {r : ℕ} (hr : 1 ≤ r) :
    deriv (ghat r) (1 / 4)
      = (Nat.choose (3 * r - 2) (r - 1) : ℝ) * ((r : ℝ) * (3 - (r : ℝ))) * 4 / 2 ^ (3 * r) :=
  (ghat_hasDerivAt_center hr).deriv

/-- At `r = 2` the central slope is `+1/2`: the center is a quadratic maximum. -/
theorem ghat_central_slope_two : deriv (ghat 2) (1 / 4) = 1 / 2 := by
  rw [ghat_central_slope (by norm_num)]
  norm_num

/-- At `r = 3` the central slope vanishes: the quadratic term cancels exactly and
the center is a quartically flat maximum. -/
theorem ghat_central_slope_three : deriv (ghat 3) (1 / 4) = 0 := by
  rw [ghat_central_slope (by norm_num)]
  norm_num

/-- For every `r ≥ 4` the central slope is negative: the center becomes a
quadratic local minimum, which is the local obstruction behind the threshold. -/
theorem ghat_central_slope_neg {r : ℕ} (hr : 4 ≤ r) : deriv (ghat r) (1 / 4) < 0 := by
  rw [ghat_central_slope (by omega)]
  have hr4 : (4 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hchoose : 0 < Nat.choose (3 * r - 2) (r - 1) := Nat.choose_pos (by omega)
  have hc : (0 : ℝ) < (Nat.choose (3 * r - 2) (r - 1) : ℝ) := by exact_mod_cast hchoose
  have hpow : (0 : ℝ) < 2 ^ (3 * r) := by positivity
  apply div_neg_of_neg_of_pos _ hpow
  have hneg : (r : ℝ) * (3 - (r : ℝ)) < 0 := by nlinarith
  linarith [mul_neg_of_pos_of_neg hc hneg]

/-! ### The critical multiplicity `r = 3` -/

/-- `E_3(q) = 1 - 3q`. -/
theorem dickE_three (q : ℝ) : dickE 3 q = 1 - 3 * q := by
  rw [show (3 : ℕ) = 1 + 2 from rfl, dickE_succ_succ, show (1 : ℕ) + 1 = 0 + 2 from rfl,
    dickE_succ_succ, dickE_zero, dickE_one]
  ring

/-- **`Ĝ^{(3)}_3(q) = 21q³(1-3q)`** (`prop:multiplicity-threshold`, the critical
case). -/
theorem ghat_three_eq (q : ℝ) : ghat 3 q = 21 * q ^ 3 * (1 - 3 * q) := by
  have hc : Nat.choose (3 * 3 - 2) (3 - 1) = 21 := by decide
  rw [ghat, dickE_three, hc]
  push_cast
  ring

/-- The critical kernel is the tree's own cubic constant-weight kernel: at
`m = 3` and unit weights, `Kernel.gmw` is `Ĝ^{(3)}_3` in the coordinate
`q = p(1-p)`.  This is what identifies the object `eq:r-central-slope`
differentiates with the object `thm:kernel` proves monotone. -/
theorem ghat_three_eq_gmw (p : ℝ) : ghat 3 (p * (1 - p)) = gmw 3 (fun _ => 1) p := by
  rw [ghat_eq, gmw, show Finset.Icc 1 (3 - 1) = ({1, 2} : Finset ℕ) from by decide,
    Finset.sum_pair (by norm_num : (1 : ℕ) ≠ 2)]
  norm_num [Nat.choose]
  ring

/-- **`d/dq Ĝ^{(3)}_3 = 63q²(1-4q)`**: strictly positive on `0 < q < 1/4`, so the
critical kernel increases all the way to the center even though its central slope
vanishes. -/
theorem ghat_three_hasDerivAt (q : ℝ) :
    HasDerivAt (ghat 3) (63 * q ^ 2 * (1 - 4 * q)) q := by
  have hfun : ghat 3 = fun t : ℝ => 21 * t ^ 3 - 63 * t ^ 4 := by
    funext t; rw [ghat_three_eq]; ring
  rw [hfun]
  have h := ((hasDerivAt_pow 3 q).const_mul (21 : ℝ)).sub
    ((hasDerivAt_pow 4 q).const_mul (63 : ℝ))
  refine h.congr_deriv ?_
  norm_num
  ring

theorem ghat_three_deriv_pos {q : ℝ} (h0 : 0 < q) (h4 : q < 1 / 4) :
    0 < 63 * q ^ 2 * (1 - 4 * q) := by
  have : 0 < 1 - 4 * q := by linarith
  positivity

/-- **The quartically flat maximum at the center** (`prop:multiplicity-threshold`).
At `p = 1/2 + x` the critical kernel is an exact polynomial in `x` whose
quadratic term vanishes:

  `Ĝ^{(3)}_3(p(1-p)) = 21/256 - (63/8)x⁴ + 42x⁶ - 63x⁸`. -/
theorem ghat_three_center_expansion (x : ℝ) :
    ghat 3 ((1 / 2 + x) * (1 - (1 / 2 + x)))
      = 21 / 256 - (63 / 8) * x ^ 4 + 42 * x ^ 6 - 63 * x ^ 8 := by
  rw [ghat_three_eq]
  ring

end CubicPochhammer
