/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import CubicPochhammer.ResidueSums
import Mathlib.Tactic.Linarith

/-!
# The certificate sum `S_{n,j}` and its nonnegativity

Formalizes `shields-2026-cubic-pochhammer.tex`,
`subsec:constant-weight-kernel` «The constant-weight kernel»,
`eq:S-def`–`eq:S-table`: the sum

  `S_{n,j} = ∑_{k ≡ 2 (3), k ≤ j} C(j,k)·(n-k+1)·(2k+1-j)`

is the numerator of the Bernstein coefficient `b_j = S_{n,j}/(3(n+1))`
(`eq:P-coeff`), and its nonnegativity
for `n ≡ 1 (mod 3)`, `0 ≤ j ≤ n+1` is what certifies `J_m(t) > 0`.

The path: expand `(n-k+1)(2k+1-j)` into a combination of the zeroth, first, and
`k(k-1)` residue-class moments (`snj_eq_residueSum`), substitute the period-6 closed form
`3·residueSum = 2^· + corr` (`three_snj_eq`), collapse the mixed powers `2^{j-1}, 2^{j-2}`
into a single `δ·2^j` (`three_snj_dform`), resolve the three corrections by the residue of
`j` modulo `6` to reach `eq:S-table` itself (`three_snj_table_zero`–`three_snj_table_five`),
and inspect the six lines using the defect bound (`snj_delta_lower`) and the
exponential-vs-polynomial bounds `2^j ≥ …` (`eq:exp-bound-0`, `eq:exp-bound-1`).

Sorry-free, no project axioms.

## Main definitions

* `snj` --- the certificate sum `S_{n,j}` of `eq:S-def`.

## Main statements

* `snj_eq_residueSum` --- `S_{n,j}` in terms of the residue-class moments (`eq:S-R`).
* `three_snj_eq`, `three_snj_dform` --- the period-6 closed form substituted in,
  and the mixed powers collapsed into a single `δ·2^j`.
* `three_snj_table_zero`–`three_snj_table_five` --- the six lines of `eq:S-table`,
  the closed form of `3S_{n,j}` on each residue class of `j` modulo `6`.
* `snj_delta_lower` --- `n ≡ 1 (mod 3)` forces the defect `δ = n+1-j` to `2` when
  `j ≡ 0 (mod 6)` and to `1` when `j ≡ 1 (mod 6)`, the two classes of `eq:S-table`
  whose quadratic term is negative.
* `expb_quad0`, `expb_quad1` --- the exponential-vs-polynomial bounds
  `eq:exp-bound-0` and `eq:exp-bound-1`.
* `snj_nonneg` --- `S_{n,j} ≥ 0` for `n ≡ 1 (mod 3)` and `0 ≤ j ≤ n+1`.

## References

* `shields-2026-cubic-pochhammer.tex`, `subsec:constant-weight-kernel`
  «The constant-weight kernel»: `eq:S-def`, `eq:S-R`, `eq:S-table`,
  `eq:P-coeff`, `eq:exp-bound-0`, `eq:exp-bound-1`.
-/

open scoped BigOperators

namespace CubicPochhammer

/-- `S_{n,j} = ∑_{k ≤ j, k ≡ 2 (3)} (n-k+1)(2k+1-j) C(j,k)` (`eq:S-def`). -/
def snj (n j : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (j + 1),
    if k % 3 = 2 then ((n : ℤ) - (k : ℤ) + 1) * (2 * (k : ℤ) + 1 - (j : ℤ)) * (j.choose k : ℤ)
    else 0

/-- `S_{n,j}` in terms of the residue-class moments (`eq:S-R`), via the ring
identity `(n-k+1)(2k+1-j) = (2n+j-1)k - 2k(k-1) + (n+1)(1-j)`. -/
theorem snj_eq_residueSum (n j : ℕ) :
    snj n j = (2 * (n : ℤ) + (j : ℤ) - 1) * ((j : ℤ) * residueSum 1 (j - 1))
      - 2 * ((j : ℤ) * ((j : ℤ) - 1) * residueSum 0 (j - 2))
      + ((n : ℤ) + 1) * (1 - (j : ℤ)) * residueSum 2 j := by
  unfold snj
  have hsplit : ∀ k ∈ Finset.range (j + 1),
      (if k % 3 = 2 then ((n : ℤ) - (k : ℤ) + 1) * (2 * (k : ℤ) + 1 - (j : ℤ)) * (j.choose k : ℤ)
        else 0)
      = (2 * (n : ℤ) + (j : ℤ) - 1) * ((k : ℤ) * (if k % 3 = 2 then (j.choose k : ℤ) else 0))
        - 2 * ((k : ℤ) * ((k : ℤ) - 1) * (if k % 3 = 2 then (j.choose k : ℤ) else 0))
        + ((n : ℤ) + 1) * (1 - (j : ℤ)) * (if k % 3 = 2 then (j.choose k : ℤ) else 0) := by
    intro k _
    split_ifs with h <;> ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, moment1_c2, moment_kk_c2]
  congr 1

/-- Substituting the period-6 closed form `3·residueSum = 2^· + corr` into `snj_eq_residueSum`. -/
theorem three_snj_eq (n j : ℕ) :
    3 * snj n j
      = (2 * (n : ℤ) + (j : ℤ) - 1) * (j : ℤ) * ((2 : ℤ) ^ (j - 1) + corr 1 (j - 1))
        - 2 * (j : ℤ) * ((j : ℤ) - 1) * ((2 : ℤ) ^ (j - 2) + corr 0 (j - 2))
        + ((n : ℤ) + 1) * (1 - (j : ℤ)) * ((2 : ℤ) ^ j + corr 2 j) := by
  rw [snj_eq_residueSum]
  have e1 := three_residueSum_closed 1 (j - 1)
  have e0 := three_residueSum_closed 0 (j - 2)
  have e2 := three_residueSum_closed 2 j
  linear_combination (2 * (n : ℤ) + (j : ℤ) - 1) * (j : ℤ) * e1
    - 2 * (j : ℤ) * ((j : ℤ) - 1) * e0
    + ((n : ℤ) + 1) * (1 - (j : ℤ)) * e2

/-- The `eq:S-table` form: for `2 ≤ j ≤ n+1`, the mixed powers collapse and
`3·S_{n,j} = d·2^j + d·(polyX) + (polyY)` with `d = n+1-j`. -/
theorem three_snj_dform (n j : ℕ) (hj2 : 2 ≤ j) (hj : j ≤ n + 1) :
    3 * snj n j
      = ((n + 1 - j : ℕ) : ℤ) * (2 : ℤ) ^ j
        + ((n + 1 - j : ℕ) : ℤ) * (2 * (j : ℤ) * corr 1 (j - 1) + (1 - (j : ℤ)) * corr 2 j)
        + (3 * (j : ℤ) * ((j : ℤ) - 1) * corr 1 (j - 1)
           - 2 * (j : ℤ) * ((j : ℤ) - 1) * corr 0 (j - 2)
           + (j : ℤ) * (1 - (j : ℤ)) * corr 2 j) := by
  have hd : ((n + 1 - j : ℕ) : ℤ) = (n : ℤ) + 1 - (j : ℤ) := by
    rw [Nat.cast_sub hj]; push_cast; ring
  have hP1 : (2 : ℤ) ^ (j - 1) = 2 * (2 : ℤ) ^ (j - 2) := by
    rw [show j - 1 = (j - 2) + 1 from by omega, pow_succ]; ring
  have hP2 : (2 : ℤ) ^ j = 4 * (2 : ℤ) ^ (j - 2) := by
    rw [show (4 : ℤ) = 2 ^ 2 from by norm_num, ← pow_add, show 2 + (j - 2) = j from by omega]
  rw [three_snj_eq, hd, hP1, hP2]; ring

/-! ### The period-6 closed form (`eq:S-table`) -/

section PeriodSixTable

variable {n j : ℕ}

/-- `eq:S-table` at `j ≡ 0 (mod 6)`, with the defect `δ = n + 1 - j`:
`3S_{n,j} = δ(2^j - 3j - 1) - 3j(j-1)`.  The quadratic enters negatively and
the linear factor is not itself nonnegative, so this is the one class needing
both exponential bounds together with `δ ≥ 2`. -/
theorem three_snj_table_zero (hj2 : 2 ≤ j) (hj : j ≤ n + 1) (h : j % 6 = 0) :
    3 * snj n j
      = ((n + 1 - j : ℕ) : ℤ) * ((2 : ℤ) ^ j - 3 * (j : ℤ) - 1)
        - 3 * (j : ℤ) * ((j : ℤ) - 1) := by
  have hc2 : corr 2 j = -1 := by rw [corr_eq_corrTab (by norm_num) h]; rfl
  have hc1 : corr 1 (j - 1) = -2 := by
    rw [corr_eq_corrTab (by norm_num) (show (j - 1) % 6 = 5 by omega)]; rfl
  have hc0 : corr 0 (j - 2) = -1 := by
    rw [corr_eq_corrTab (by norm_num) (show (j - 2) % 6 = 4 by omega)]; rfl
  rw [three_snj_dform n j hj2 hj, hc2, hc1, hc0]; ring

/-- `eq:S-table` at `j ≡ 1 (mod 6)`, with the defect `δ = n + 1 - j`:
`3S_{n,j} = δ(2^j - 2) - 3j(j-1)`.  The quadratic enters negatively, so this
class needs `eq:exp-bound-1` together with `δ ≥ 1`. -/
theorem three_snj_table_one (hj2 : 2 ≤ j) (hj : j ≤ n + 1) (h : j % 6 = 1) :
    3 * snj n j
      = ((n + 1 - j : ℕ) : ℤ) * ((2 : ℤ) ^ j - 2)
        - 3 * (j : ℤ) * ((j : ℤ) - 1) := by
  have hc2 : corr 2 j = -2 := by rw [corr_eq_corrTab (by norm_num) h]; rfl
  have hc1 : corr 1 (j - 1) = -1 := by
    rw [corr_eq_corrTab (by norm_num) (show (j - 1) % 6 = 0 by omega)]; rfl
  have hc0 : corr 0 (j - 2) = 1 := by
    rw [corr_eq_corrTab (by norm_num) (show (j - 2) % 6 = 5 by omega)]; rfl
  rw [three_snj_dform n j hj2 hj, hc2, hc1, hc0]; ring

/-- `eq:S-table` at `j ≡ 2 (mod 6)`, with the defect `δ = n + 1 - j`:
`3S_{n,j} = δ(2^j + 3j - 1)`.  The quadratic cancels and the linear factor is
positive for `j ≥ 2`, so `δ ≥ 0` suffices. -/
theorem three_snj_table_two (hj2 : 2 ≤ j) (hj : j ≤ n + 1) (h : j % 6 = 2) :
    3 * snj n j
      = ((n + 1 - j : ℕ) : ℤ) * ((2 : ℤ) ^ j + 3 * (j : ℤ) - 1) := by
  have hc2 : corr 2 j = -1 := by rw [corr_eq_corrTab (by norm_num) h]; rfl
  have hc1 : corr 1 (j - 1) = 1 := by
    rw [corr_eq_corrTab (by norm_num) (show (j - 1) % 6 = 1 by omega)]; rfl
  have hc0 : corr 0 (j - 2) = 2 := by
    rw [corr_eq_corrTab (by norm_num) (show (j - 2) % 6 = 0 by omega)]; rfl
  rw [three_snj_dform n j hj2 hj, hc2, hc1, hc0]; ring

/-- `eq:S-table` at `j ≡ 3 (mod 6)`, with the defect `δ = n + 1 - j`:
`3S_{n,j} = δ(2^j + 3j + 1) + 3j(j-1)`.  Every term is nonnegative for
`j ≥ 2`. -/
theorem three_snj_table_three (hj2 : 2 ≤ j) (hj : j ≤ n + 1) (h : j % 6 = 3) :
    3 * snj n j
      = ((n + 1 - j : ℕ) : ℤ) * ((2 : ℤ) ^ j + 3 * (j : ℤ) + 1)
        + 3 * (j : ℤ) * ((j : ℤ) - 1) := by
  have hc2 : corr 2 j = 1 := by rw [corr_eq_corrTab (by norm_num) h]; rfl
  have hc1 : corr 1 (j - 1) = 2 := by
    rw [corr_eq_corrTab (by norm_num) (show (j - 1) % 6 = 2 by omega)]; rfl
  have hc0 : corr 0 (j - 2) = 1 := by
    rw [corr_eq_corrTab (by norm_num) (show (j - 2) % 6 = 1 by omega)]; rfl
  rw [three_snj_dform n j hj2 hj, hc2, hc1, hc0]; ring

/-- `eq:S-table` at `j ≡ 4 (mod 6)`, with the defect `δ = n + 1 - j`:
`3S_{n,j} = δ(2^j + 2) + 3j(j-1)`.  Every term is nonnegative for `j ≥ 2`. -/
theorem three_snj_table_four (hj2 : 2 ≤ j) (hj : j ≤ n + 1) (h : j % 6 = 4) :
    3 * snj n j
      = ((n + 1 - j : ℕ) : ℤ) * ((2 : ℤ) ^ j + 2)
        + 3 * (j : ℤ) * ((j : ℤ) - 1) := by
  have hc2 : corr 2 j = 2 := by rw [corr_eq_corrTab (by norm_num) h]; rfl
  have hc1 : corr 1 (j - 1) = 1 := by
    rw [corr_eq_corrTab (by norm_num) (show (j - 1) % 6 = 3 by omega)]; rfl
  have hc0 : corr 0 (j - 2) = -1 := by
    rw [corr_eq_corrTab (by norm_num) (show (j - 2) % 6 = 2 by omega)]; rfl
  rw [three_snj_dform n j hj2 hj, hc2, hc1, hc0]; ring

/-- `eq:S-table` at `j ≡ 5 (mod 6)`, with the defect `δ = n + 1 - j`:
`3S_{n,j} = δ(2^j - 3j + 1)`.  The quadratic cancels, and `eq:exp-bound-0`'s
linear companion makes the remaining factor positive. -/
theorem three_snj_table_five (hj2 : 2 ≤ j) (hj : j ≤ n + 1) (h : j % 6 = 5) :
    3 * snj n j
      = ((n + 1 - j : ℕ) : ℤ) * ((2 : ℤ) ^ j - 3 * (j : ℤ) + 1) := by
  have hc2 : corr 2 j = 1 := by rw [corr_eq_corrTab (by norm_num) h]; rfl
  have hc1 : corr 1 (j - 1) = -1 := by
    rw [corr_eq_corrTab (by norm_num) (show (j - 1) % 6 = 4 by omega)]; rfl
  have hc0 : corr 0 (j - 2) = -2 := by
    rw [corr_eq_corrTab (by norm_num) (show (j - 2) % 6 = 3 by omega)]; rfl
  rw [three_snj_dform n j hj2 hj, hc2, hc1, hc0]; ring

end PeriodSixTable

/-- The residue hypothesis `n ≡ 1 (mod 3)` — that is, `n = 3m-2` — puts `n+1`
in class `2` or `5` modulo `6`, so the defect `δ = n + 1 - j` cannot vanish in
the two classes of `eq:S-table` whose quadratic term is negative: `δ ≥ 2` when
`j ≡ 0 (mod 6)`, and `δ ≥ 1` when `j ≡ 1 (mod 6)`.  This is the only place the
residue of `n` is used. -/
theorem snj_delta_lower {n j : ℕ} (hn : n % 3 = 1) (hj : j ≤ n + 1) :
    (j % 6 = 0 → 2 ≤ n + 1 - j) ∧ (j % 6 = 1 → 1 ≤ n + 1 - j) :=
  ⟨fun h => by omega, fun h => by omega⟩

/-! ### Exponential-vs-polynomial bounds (`eq:exp-bound-0`, `eq:exp-bound-1`) -/

/-- `3j + 1 ≤ 2^j` for `j ≥ 5` (linear bound, cases `j ≡ 0,5 (mod 6)`). -/
theorem expb_a : ∀ j : ℕ, 5 ≤ j → 3 * (j : ℤ) + 1 ≤ (2 : ℤ) ^ j := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => norm_num
  | succ j hj ih =>
    have hjz : (5 : ℤ) ≤ (j : ℤ) := by exact_mod_cast hj
    rw [pow_succ]; push_cast; nlinarith [ih, hjz]

/-- `3j(j-1) + 2 ≤ 2^j` for `j ≥ 7` (`eq:exp-bound-1`, case `j ≡ 1 (mod 6)`),
with equality at `j = 7`. -/
theorem expb_quad1 : ∀ j : ℕ, 7 ≤ j → 3 * (j : ℤ) * ((j : ℤ) - 1) + 2 ≤ (2 : ℤ) ^ j := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => norm_num
  | succ j hj ih =>
    have hjz : (7 : ℤ) ≤ (j : ℤ) := by exact_mod_cast hj
    rw [pow_succ]; push_cast; nlinarith [ih, hjz]

/-- `3j(j-1) + 6j + 2 ≤ 2·2^j` for `j ≥ 6` (`eq:exp-bound-0`, case `j ≡ 0 (mod 6)`),
with equality at `j = 6`. -/
theorem expb_quad0 : ∀ j : ℕ, 6 ≤ j →
    3 * (j : ℤ) * ((j : ℤ) - 1) + 6 * (j : ℤ) + 2 ≤ 2 * (2 : ℤ) ^ j := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => norm_num
  | succ j hj ih =>
    have hjz : (6 : ℤ) ≤ (j : ℤ) := by exact_mod_cast hj
    rw [pow_succ]; push_cast; nlinarith [ih, hjz]

/-- **Certificate nonnegativity** (`lem:bernstein` via `eq:S-table`, sign
analysis): for `n ≡ 1 (mod 3)` and `0 ≤ j ≤ n+1`, `S_{n,j} ≥ 0`.

With the six lines of `eq:S-table` in hand the argument is a sign inspection.
Classes `2`, `3` and `4` are nonnegative term by term.  Class `5` needs only
that `2^j - 3j + 1 > 0`.  The two classes carrying a negative `3j(j-1)` are the
work: there the defect `δ = n + 1 - j` is bounded below by `snj_delta_lower`,
and the exponential bounds supply the rest. -/
theorem snj_nonneg (n j : ℕ) (hn : n % 3 = 1) (hj : j ≤ n + 1) : 0 ≤ snj n j := by
  rcases lt_or_ge j 2 with hlt | hge
  · interval_cases j
    · simp [snj]
    · norm_num [snj, Finset.sum_range_succ]
  · have hthree : 0 ≤ 3 * snj n j := by
      have hjz2 : (2 : ℤ) ≤ (j : ℤ) := by exact_mod_cast hge
      have hPpos : (0 : ℤ) < (2 : ℤ) ^ j := by positivity
      have hd0 : (0 : ℤ) ≤ ((n + 1 - j : ℕ) : ℤ) := by positivity
      have hjjnn : (0 : ℤ) ≤ 3 * (j : ℤ) * ((j : ℤ) - 1) := by nlinarith [hjz2]
      have hr : j % 6 = 0 ∨ j % 6 = 1 ∨ j % 6 = 2 ∨ j % 6 = 3 ∨ j % 6 = 4 ∨ j % 6 = 5 := by omega
      rcases hr with h | h | h | h | h | h
      · rw [three_snj_table_zero hge hj h]
        have hd2 : (2 : ℤ) ≤ ((n + 1 - j : ℕ) : ℤ) := by
          exact_mod_cast (snj_delta_lower hn hj).1 h
        have hea := expb_a j (show 5 ≤ j by omega)
        have he0 := expb_quad0 j (show 6 ≤ j by omega)
        nlinarith [mul_nonneg (show (0 : ℤ) ≤ ((n + 1 - j : ℕ) : ℤ) - 2 by linarith)
          (show (0 : ℤ) ≤ (2 : ℤ) ^ j - (3 * (j : ℤ) + 1) by linarith), he0]
      · rw [three_snj_table_one hge hj h]
        have hd1 : (1 : ℤ) ≤ ((n + 1 - j : ℕ) : ℤ) := by
          exact_mod_cast (snj_delta_lower hn hj).2 h
        have he1 := expb_quad1 j (show 7 ≤ j by omega)
        nlinarith [mul_nonneg (show (0 : ℤ) ≤ ((n + 1 - j : ℕ) : ℤ) - 1 by linarith)
          (show (0 : ℤ) ≤ (2 : ℤ) ^ j - 2 by nlinarith [he1, hjjnn]), he1]
      · rw [three_snj_table_two hge hj h]
        exact mul_nonneg hd0 (by linarith)
      · rw [three_snj_table_three hge hj h]
        linarith [mul_nonneg hd0 (show (0 : ℤ) ≤ (2 : ℤ) ^ j + 3 * (j : ℤ) + 1 by positivity)]
      · rw [three_snj_table_four hge hj h]
        linarith [mul_nonneg hd0 (show (0 : ℤ) ≤ (2 : ℤ) ^ j + 2 by positivity)]
      · rw [three_snj_table_five hge hj h]
        have hea := expb_a j (show 5 ≤ j by omega)
        exact mul_nonneg hd0 (by linarith)
    linarith

end CubicPochhammer

