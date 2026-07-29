/-
# The Bernstein certificate: `J_m(t) > 0`

Formalizes `shields-2026-cubic-pochhammer.tex`, §4 «The cubic residue
kernel» (`sec:kernel`), `lem:bernstein`.  With `n = 3m-2`, the constant-weight
derivative polynomial

  `J_m(t) = ∑_{k=1}^{m-1} C(3m-2, 3k-1) t^{3k-1} (k - (m-k) t)`   (`eq:J-r`)

controls the monotonicity of the constant-weight kernel `G_m`.  Its
Bernstein-basis representation (`eq:P-def`–`eq:P-coeff`) is

  `3(n+1) J_m(t) = ∑_{j=0}^{n+1} S_{n,j} · C(n+1,j) · t^j (1-t)^{n+1-j}`.   (★)

Since every `S_{n,j} ≥ 0` (`Snj_nonneg`, proven) and `S_{n,2} > 0`, the right
side is strictly positive on `(0,1)`; hence `J_m(t) > 0`.

Identity (★) is a finite polynomial coefficient identity — the coefficient
extraction `eq:P-coeff` from the projective Bernstein transform — verified
exhaustively for `2 ≤ m ≤ 100` by `../scripts/verify_kernel.py` and
checked here by hand at `m=2` (both sides equal `90 t²(1-t)`).  It is the one
purely-combinatorial step carried as an axiom (`Jm_bernstein`); everything
consuming it, including the positivity `Jm_pos` and all of `Kernel.lean`, is
proven.

Sorry-free.  Uses the single documented combinatorial axiom `Jm_bernstein`.
-/
import CubicPochhammer.Snj

open scoped BigOperators

namespace CubicPochhammer

/-- The constant-weight derivative polynomial `J_m(t)` (`eq:J-r`), `n = 3m-2`. -/
noncomputable def Jm (m : ℕ) (t : ℝ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 (m - 1),
    (Nat.choose (3 * m - 2) (3 * r - 1) : ℝ) * t ^ (3 * r - 1) * ((r : ℝ) - ((m : ℝ) - (r : ℝ)) * t)

/-- **Bridge — the Bernstein coefficient identity (★)** (`eq:P-coeff`).  With
`n = 3m-2`, `J_m` has Bernstein coefficients `S_{n,j}/(3(n+1))`.  A finite
polynomial identity (projective Bernstein transform + third-root-of-unity
coefficient extraction); it introduces **no analytic content** and is verified
symbolically in `../scripts/verify_kernel.py`.  Its positive
consequences below are proven from it and the theorem `Snj_nonneg`. -/
axiom Jm_bernstein (m : ℕ) (t : ℝ) :
    3 * ((3 * m - 1 : ℕ) : ℝ) * Jm m t
      = ∑ j ∈ Finset.range (3 * m),
          (Snj (3 * m - 2) j : ℝ) * (Nat.choose (3 * m - 1) j : ℝ)
            * t ^ j * (1 - t) ^ (3 * m - 1 - j)

/-- The degree-two certificate value: `S_{n,2} = 3(n-1)` (`3S_{n,2}=9d`,
`d=n-1`). -/
theorem Snj_two_eq (n : ℕ) : Snj n 2 = 3 * (n : ℤ) - 3 := by
  simp only [Snj, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  ring

/-- `S_{n,2} > 0` for `n ≥ 2` (the strictly positive `[x²]` coefficient). -/
theorem Snj_two_pos (n : ℕ) (hn : 2 ≤ n) : 0 < Snj n 2 := by
  rw [Snj_two_eq]
  have : (2 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
  linarith

/-- **Bernstein certificate** (`lem:bernstein`): `J_m(t) > 0` for `2 ≤ m` and
`0 < t < 1`.  Every Bernstein coefficient `S_{n,j}` is nonnegative and the `j=2`
one is positive. -/
theorem Jm_pos (m : ℕ) (hm : 2 ≤ m) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) : 0 < Jm m t := by
  have hn3 : (3 * m - 2) % 3 = 1 := by omega
  have h1t : (0 : ℝ) ≤ 1 - t := by linarith
  have hsum : 0 < ∑ j ∈ Finset.range (3 * m),
      (Snj (3 * m - 2) j : ℝ) * (Nat.choose (3 * m - 1) j : ℝ) * t ^ j * (1 - t) ^ (3 * m - 1 - j) := by
    apply Finset.sum_pos'
    · intro j hj
      rw [Finset.mem_range] at hj
      have hSnn : (0 : ℝ) ≤ (Snj (3 * m - 2) j : ℝ) := by
        exact_mod_cast Snj_nonneg (3 * m - 2) j hn3 (by omega)
      exact mul_nonneg (mul_nonneg (mul_nonneg hSnn (by positivity)) (by positivity))
        (pow_nonneg h1t _)
    · refine ⟨2, Finset.mem_range.mpr (by omega), ?_⟩
      have hS2 : (0 : ℝ) < (Snj (3 * m - 2) 2 : ℝ) := by
        exact_mod_cast Snj_two_pos (3 * m - 2) (by omega)
      have hC : (0 : ℝ) < (Nat.choose (3 * m - 1) 2 : ℝ) := by
        have : 0 < Nat.choose (3 * m - 1) 2 := Nat.choose_pos (by omega)
        exact_mod_cast this
      have hpt : (0 : ℝ) < t ^ 2 := by positivity
      have hpt2 : (0 : ℝ) < (1 - t) ^ (3 * m - 1 - 2) := pow_pos (by linarith) _
      exact mul_pos (mul_pos (mul_pos hS2 hC) hpt) hpt2
  have h3 : (0 : ℝ) < 3 * ((3 * m - 1 : ℕ) : ℝ) := by
    have hpos : 0 < 3 * m - 1 := by omega
    have : (0 : ℝ) < ((3 * m - 1 : ℕ) : ℝ) := by exact_mod_cast hpos
    linarith
  have hprod : 0 < 3 * ((3 * m - 1 : ℕ) : ℝ) * Jm m t := by rw [Jm_bernstein]; exact hsum
  by_contra hJ
  rw [not_lt] at hJ
  have : 3 * ((3 * m - 1 : ℕ) : ℝ) * Jm m t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h3.le hJ
  linarith

end CubicPochhammer
