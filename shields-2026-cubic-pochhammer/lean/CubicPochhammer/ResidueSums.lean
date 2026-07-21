/-
# Residue-class binomial sums and their period-6 closed form

Infrastructure for the third-root-of-unity filter of
`shields-2026-cubic-pochhammer.tex`, §4 «The cubic residue kernel»
(`sec:kernel`), supporting the certificate sum `S_{n,j}` (`eq:S-def`,
`eq:S-table`).

Central object: `R a j = ∑_{k ≡ a (3), k ≤ j} C(j,k)`, the count of size-`k`
subsets of a `j`-set with `k` in a fixed residue class mod `3`.  The paper's
root-of-unity evaluation gives `R_a(j) = (2^j + 2cos((j-2a)π/3))/3`; here the
same content is proven over `ℤ` as a **period-6 closed form**

  `3 · R a j = 2^j + corr a j`,

with `corr a j` an explicit integer table depending only on `a mod 3` and
`j mod 6`.  The proof is a single induction on `j` using Pascal's rule
(`R_succ`), with the inductive step reduced to a finite `decide` over the table.

First and second residue-class moments (`sum_moment1`, `sum_moment2`) are then
derived from `k·C(j,k) = j·C(j-1,k-1)`; these feed the closed form of `S_{n,j}`
in `Snj.lean`.

Sorry-free, no project axioms.
-/
import Mathlib.Tactic

open scoped BigOperators

namespace CubicPochhammer

/-- `R a j = ∑_{k ≤ j, k ≡ a (mod 3)} C(j,k)`, over `ℤ`.  The residue is taken
mod `3` internally, so `R (a+2) j` automatically sums the shifted class. -/
def R (a j : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (j + 1), if k % 3 = a % 3 then (j.choose k : ℤ) else 0

/-- **Pascal recurrence** for the residue-class sums:
`R a (j+1) = R a j + R (a+2) j`.  The second term collects the `C(j,k-1)`
half of `C(j+1,k) = C(j,k) + C(j,k-1)`, whose indices lie in the class `a-1 ≡
a+2 (mod 3)`. -/
theorem R_succ (a j : ℕ) : R a (j + 1) = R a j + R (a + 2) j := by
  unfold R
  rw [Finset.sum_range_succ']
  -- f 0 term:  C(j+1,0) = 1
  have hf0 : (if (0 : ℕ) % 3 = a % 3 then ((j + 1).choose 0 : ℤ) else 0)
      = (if (0 : ℕ) % 3 = a % 3 then (j.choose 0 : ℤ) else 0) := by
    simp
  rw [hf0]
  -- expand each shifted summand via Pascal C(j+1,k+1) = C(j,k) + C(j,k+1)
  have hstep : ∀ k ∈ Finset.range (j + 1),
      (if (k + 1) % 3 = a % 3 then ((j + 1).choose (k + 1) : ℤ) else 0)
        = (if (k + 1) % 3 = a % 3 then (j.choose k : ℤ) else 0)
          + (if (k + 1) % 3 = a % 3 then (j.choose (k + 1) : ℤ) else 0) := by
    intro k _
    rw [Nat.choose_succ_succ j k]
    push_cast
    split_ifs <;> ring
  rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib]
  -- Sum1 = R (a+2) j : rewrite predicate (k+1)%3 = a%3  ↔  k%3 = (a+2)%3
  have hSum1 : (∑ k ∈ Finset.range (j + 1),
        if (k + 1) % 3 = a % 3 then (j.choose k : ℤ) else 0)
      = ∑ k ∈ Finset.range (j + 1), if k % 3 = (a + 2) % 3 then (j.choose k : ℤ) else 0 := by
    apply Finset.sum_congr rfl
    intro k _
    have : ((k + 1) % 3 = a % 3) ↔ (k % 3 = (a + 2) % 3) := by omega
    simp only [this]
  -- Sum2 + f0 = R a j : reindex ∑ g(k+1) and reabsorb the endpoint
  have hSum2 : (∑ k ∈ Finset.range (j + 1),
        if (k + 1) % 3 = a % 3 then (j.choose (k + 1) : ℤ) else 0)
        + (if (0 : ℕ) % 3 = a % 3 then (j.choose 0 : ℤ) else 0)
      = ∑ k ∈ Finset.range (j + 1), if k % 3 = a % 3 then (j.choose k : ℤ) else 0 := by
    have hg : (∑ k ∈ Finset.range (j + 1),
          if (k + 1) % 3 = a % 3 then (j.choose (k + 1) : ℤ) else 0)
        + (if (0 : ℕ) % 3 = a % 3 then (j.choose 0 : ℤ) else 0)
        = ∑ k ∈ Finset.range (j + 2), if k % 3 = a % 3 then (j.choose k : ℤ) else 0 := by
      exact (Finset.sum_range_succ'
        (fun k => if k % 3 = a % 3 then (j.choose k : ℤ) else 0) (j + 1)).symm
    rw [hg, Finset.sum_range_succ]
    have hend : (if (j + 1) % 3 = a % 3 then (j.choose (j + 1) : ℤ) else 0) = 0 := by
      rw [Nat.choose_eq_zero_of_lt (Nat.lt_succ_self j)]
      simp
    rw [hend, add_zero]
  rw [hSum1]
  -- assemble
  rw [show (∑ k ∈ Finset.range (j + 1), if k % 3 = (a + 2) % 3 then (j.choose k : ℤ) else 0)
        + (∑ k ∈ Finset.range (j + 1), if (k + 1) % 3 = a % 3 then (j.choose (k + 1) : ℤ) else 0)
        + (if (0 : ℕ) % 3 = a % 3 then (j.choose 0 : ℤ) else 0)
      = (∑ k ∈ Finset.range (j + 1), if k % 3 = (a + 2) % 3 then (j.choose k : ℤ) else 0)
        + ((∑ k ∈ Finset.range (j + 1), if (k + 1) % 3 = a % 3 then (j.choose (k + 1) : ℤ) else 0)
          + (if (0 : ℕ) % 3 = a % 3 then (j.choose 0 : ℤ) else 0)) from by ring]
  rw [hSum2]
  ring

/-- The integer correction table `2cos((j-2a)π/3)` indexed by `(a mod 3, j mod 6)`;
the six values in each row are the period-6 orbit produced by Pascal's rule. -/
def corrTab (a r : ℕ) : ℤ :=
  match a, r with
  | 0, 0 => 2  | 0, 1 => 1  | 0, 2 => -1 | 0, 3 => -2 | 0, 4 => -1 | 0, 5 => 1
  | 1, 0 => -1 | 1, 1 => 1  | 1, 2 => 2  | 1, 3 => 1  | 1, 4 => -1 | 1, 5 => -2
  | 2, 0 => -1 | 2, 1 => -2 | 2, 2 => -1 | 2, 3 => 1  | 2, 4 => 2  | 2, 5 => 1
  | _, _ => 0

/-- The correction term of the closed form `3·R a j = 2^j + corr a j`. -/
def corr (a j : ℕ) : ℤ := corrTab (a % 3) (j % 6)

/-- The table satisfies the same Pascal step as `R`:
`corr a (j+1) = corr a j + corr (a+2) j`.  Finite verification over the
`3 × 6` residue grid. -/
theorem corr_rec (a j : ℕ) : corr a (j + 1) = corr a j + corr (a + 2) j := by
  unfold corr
  have h1 : (j + 1) % 6 = (j % 6 + 1) % 6 := by omega
  have h2 : (a + 2) % 3 = (a % 3 + 2) % 3 := by omega
  rw [h1, h2]
  have hp : a % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hq : j % 6 < 6 := Nat.mod_lt _ (by norm_num)
  interval_cases (a % 3) <;> interval_cases (j % 6) <;> decide

/-- **Period-6 closed form** (root-of-unity evaluation, `eq:S-table` prerequisite):
`3 · R a j = 2^j + corr a j`.  Single induction on `j`; the step is Pascal
(`R_succ`) plus the table recurrence (`corr_rec`), and `2^j + 2^j = 2^{j+1}`. -/
theorem three_R_closed : ∀ (j a : ℕ), 3 * R a j = 2 ^ j + corr a j := by
  intro j
  induction j with
  | zero =>
    intro a
    unfold R corr
    rw [Finset.sum_range_one]
    have hp : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega
    rcases hp with h | h | h <;> simp [h, corrTab]
  | succ j ih =>
    intro a
    rw [R_succ, mul_add, ih a, ih (a + 2), corr_rec, pow_succ]
    ring

/-- `R` depends on its residue only mod `3`. -/
theorem R_mod_eq {a b : ℕ} (j : ℕ) (h : a % 3 = b % 3) : R a j = R b j := by
  unfold R; simp_rw [h]

/-- `(k+1)·C(j+1,k+1) = (j+1)·C(j,k)`, the absorption identity in `ℤ`. -/
theorem choose_mul1 (j k : ℕ) :
    ((k + 1 : ℕ) : ℤ) * ((j + 1).choose (k + 1) : ℤ)
      = ((j + 1 : ℕ) : ℤ) * (j.choose k : ℤ) := by
  have h := Nat.add_one_mul_choose_eq j k
  have h2 : ((j + 1 : ℕ) * j.choose k : ℤ) = ((j + 1).choose (k + 1) * (k + 1 : ℕ) : ℤ) := by
    exact_mod_cast h
  push_cast at h2 ⊢
  linear_combination -h2

/-- **First residue-class moment** (`∑ k·C = shifted R`, `eq:S-R` input):
`∑_{k ≤ j+1} k·[k ≡ a] C(j+1,k) = (j+1)·R (a+2) j`. -/
theorem moment1 (a j : ℕ) :
    (∑ k ∈ Finset.range (j + 2), (k : ℤ) * (if k % 3 = a % 3 then ((j + 1).choose k : ℤ) else 0))
      = ((j + 1 : ℕ) : ℤ) * R (a + 2) j := by
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_mul, add_zero]
  have step : ∀ k ∈ Finset.range (j + 1),
      ((k + 1 : ℕ) : ℤ) * (if (k + 1) % 3 = a % 3 then ((j + 1).choose (k + 1) : ℤ) else 0)
        = ((j + 1 : ℕ) : ℤ) * (if k % 3 = (a + 2) % 3 then (j.choose k : ℤ) else 0) := by
    intro k _
    have hpred : ((k + 1) % 3 = a % 3) ↔ (k % 3 = (a + 2) % 3) := by omega
    by_cases hP : (k + 1) % 3 = a % 3
    · rw [if_pos hP, if_pos (hpred.mp hP)]; exact choose_mul1 j k
    · rw [if_neg hP, if_neg (fun h => hP (hpred.mpr h))]; ring
  rw [Finset.sum_congr rfl step, ← Finset.mul_sum]
  rfl

/-- First moment specialized to the class `k ≡ 2 (mod 3)` at top index `j`, in
the natural form used by `S_{n,j}`:
`∑_{k ≤ j} k·[k ≡ 2] C(j,k) = j·R 1 (j-1)`. -/
theorem moment1_c2 (j : ℕ) :
    (∑ k ∈ Finset.range (j + 1), (k : ℤ) * (if k % 3 = 2 then (j.choose k : ℤ) else 0))
      = (j : ℤ) * R 1 (j - 1) := by
  cases j with
  | zero => simp [R]
  | succ j =>
    have h := moment1 2 j
    rw [R_mod_eq j (show (2 + 2) % 3 = 1 % 3 by norm_num)] at h
    simpa using h

/-- `(k+2)(k+1)·C(j+2,k+2) = (j+2)(j+1)·C(j,k)`; two applications of
`choose_mul1`. -/
theorem choose_mul2 (j k : ℕ) :
    ((k + 2 : ℕ) : ℤ) * ((k + 1 : ℕ) : ℤ) * ((j + 2).choose (k + 2) : ℤ)
      = ((j + 2 : ℕ) : ℤ) * ((j + 1 : ℕ) : ℤ) * (j.choose k : ℤ) := by
  have h1 := choose_mul1 (j + 1) (k + 1)
  have h2 := choose_mul1 j k
  push_cast at h1 h2 ⊢
  linear_combination ((k : ℤ) + 1) * h1 + ((j : ℤ) + 2) * h2

/-- **Second residue-class moment** (`∑ k(k-1)·C = twice-shifted R`):
`∑_{k ≤ j+2} k(k-1)·[k ≡ a] C(j+2,k) = (j+2)(j+1)·R (a+1) j`. -/
theorem moment2 (a j : ℕ) :
    (∑ k ∈ Finset.range (j + 3), (k : ℤ) * ((k : ℤ) - 1) *
        (if k % 3 = a % 3 then ((j + 2).choose k : ℤ) else 0))
      = ((j + 2 : ℕ) : ℤ) * ((j + 1 : ℕ) : ℤ) * R (a + 1) j := by
  set F : ℕ → ℤ := fun k => (k : ℤ) * ((k : ℤ) - 1) *
      (if k % 3 = a % 3 then ((j + 2).choose k : ℤ) else 0) with hFdef
  have hF0 : F 0 = 0 := by simp [hFdef]
  have hF1 : F 1 = 0 := by simp [hFdef]
  have hpeel : (∑ k ∈ Finset.range (j + 3), F k)
      = ∑ l ∈ Finset.range (j + 1), F (l + 2) := by
    rw [Finset.sum_range_succ' F (j + 2), Finset.sum_range_succ' (fun k => F (k + 1)) (j + 1)]
    simp only [hF0, hF1, add_zero]
  rw [hpeel]
  have step : ∀ l ∈ Finset.range (j + 1),
      F (l + 2) = ((j + 2 : ℕ) : ℤ) * ((j + 1 : ℕ) : ℤ) *
        (if l % 3 = (a + 1) % 3 then (j.choose l : ℤ) else 0) := by
    intro l _
    simp only [hFdef]
    have hpred : ((l + 2) % 3 = a % 3) ↔ (l % 3 = (a + 1) % 3) := by omega
    by_cases hP : (l + 2) % 3 = a % 3
    · rw [if_pos hP, if_pos (hpred.mp hP)]
      have hc := choose_mul2 j l
      have h1 : (((l + 2 : ℕ) : ℤ) - 1) = ((l + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [h1]; linear_combination hc
    · rw [if_neg hP, if_neg (fun h => hP (hpred.mpr h))]; ring
  rw [Finset.sum_congr rfl step, ← Finset.mul_sum]
  rfl

/-- Second moment specialized to `k ≡ 2 (mod 3)` at top index `j`:
`∑_{k ≤ j} k(k-1)·[k ≡ 2] C(j,k) = j(j-1)·R 0 (j-2)`. -/
theorem moment_kk_c2 (j : ℕ) :
    (∑ k ∈ Finset.range (j + 1), (k : ℤ) * ((k : ℤ) - 1) *
        (if k % 3 = 2 then (j.choose k : ℤ) else 0))
      = (j : ℤ) * ((j : ℤ) - 1) * R 0 (j - 2) := by
  obtain _ | _ | i := j
  · simp [R]
  · norm_num [Finset.sum_range_succ]
  · have h := moment2 2 i
    rw [R_mod_eq i (show (2 + 1) % 3 = 0 % 3 by norm_num)] at h
    simpa [Nat.add_sub_cancel] using h

end CubicPochhammer
