/-
# The certificate sum `S_{n,j}` and its nonnegativity

Formalizes `shields-2026-cubic-pochhammer.tex`, §4 «The cubic residue
kernel» (`sec:kernel`), `eq:S-def`–`eq:S-table`: the sum

  `S_{n,j} = ∑_{k ≡ 2 (3), k ≤ j} C(j,k)·(n-k+1)·(2k+1-j)`

is the numerator of the Bernstein coefficient `[x^j] 𝒫_m`, and its nonnegativity
for `n ≡ 1 (mod 3)`, `0 ≤ j ≤ n+1` is what certifies `J_m(t) > 0`.

The path: expand `(n-k+1)(2k+1-j)` into a combination of the zeroth, first, and
`k(k-1)` residue-class moments (`Snj_eq_R`), substitute the period-6 closed form
`3·R = 2^· + corr` (`three_Snj_eq`), collapse the mixed powers `2^{j-1}, 2^{j-2}`
into a single `d·2^j` (`three_Snj_dform`, `eq:S-table` in the form
`3S = d·2^j + …`), and finish with a six-way case split on `j mod 6` using the
exponential-vs-polynomial bounds `2^j ≥ …` (`eq:exp-bound-0`, `eq:exp-bound-1`).

Sorry-free, no project axioms.
-/
import CubicPochhammer.ResidueSums

open scoped BigOperators

namespace CubicPochhammer

/-- `S_{n,j} = ∑_{k ≤ j, k ≡ 2 (3)} (n-k+1)(2k+1-j) C(j,k)` (`eq:S-def`). -/
def Snj (n j : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (j + 1),
    if k % 3 = 2 then ((n : ℤ) - (k : ℤ) + 1) * (2 * (k : ℤ) + 1 - (j : ℤ)) * (j.choose k : ℤ)
    else 0

/-- `S_{n,j}` in terms of the residue-class moments (`eq:S-R`), via the ring
identity `(n-k+1)(2k+1-j) = (2n+j-1)k - 2k(k-1) + (n+1)(1-j)`. -/
theorem Snj_eq_R (n j : ℕ) :
    Snj n j = (2 * (n : ℤ) + (j : ℤ) - 1) * ((j : ℤ) * R 1 (j - 1))
      - 2 * ((j : ℤ) * ((j : ℤ) - 1) * R 0 (j - 2))
      + ((n : ℤ) + 1) * (1 - (j : ℤ)) * R 2 j := by
  unfold Snj
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

/-- Substituting the period-6 closed form `3·R = 2^· + corr` into `Snj_eq_R`. -/
theorem three_Snj_eq (n j : ℕ) :
    3 * Snj n j
      = (2 * (n : ℤ) + (j : ℤ) - 1) * (j : ℤ) * ((2 : ℤ) ^ (j - 1) + corr 1 (j - 1))
        - 2 * (j : ℤ) * ((j : ℤ) - 1) * ((2 : ℤ) ^ (j - 2) + corr 0 (j - 2))
        + ((n : ℤ) + 1) * (1 - (j : ℤ)) * ((2 : ℤ) ^ j + corr 2 j) := by
  rw [Snj_eq_R]
  have e1 := three_R_closed (j - 1) 1
  have e0 := three_R_closed (j - 2) 0
  have e2 := three_R_closed j 2
  linear_combination (2 * (n : ℤ) + (j : ℤ) - 1) * (j : ℤ) * e1
    - 2 * (j : ℤ) * ((j : ℤ) - 1) * e0
    + ((n : ℤ) + 1) * (1 - (j : ℤ)) * e2

/-- The `eq:S-table` form: for `2 ≤ j ≤ n+1`, the mixed powers collapse and
`3·S_{n,j} = d·2^j + d·(polyX) + (polyY)` with `d = n+1-j`. -/
theorem three_Snj_dform (n j : ℕ) (hj2 : 2 ≤ j) (hj : j ≤ n + 1) :
    3 * Snj n j
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
  rw [three_Snj_eq, hd, hP1, hP2]; ring

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

/-- **Certificate nonnegativity** (`eq:S-table`, sign analysis): for `n ≡ 1
(mod 3)` and `0 ≤ j ≤ n+1`, `S_{n,j} ≥ 0`.  The residue `n ≡ 1 (mod 3)` is
exactly `n = 3m-2`; it forces `d = n+1-j ≥ 2` when `j ≡ 0 (mod 3)` and `d ≥ 1`
when `j ≡ 1 (mod 3)`, which is what the two exponential bounds need. -/
theorem Snj_nonneg (n j : ℕ) (hn : n % 3 = 1) (hj : j ≤ n + 1) : 0 ≤ Snj n j := by
  rcases lt_or_ge j 2 with hlt | hge
  · interval_cases j
    · simp [Snj]
    · norm_num [Snj, Finset.sum_range_succ]
  · have key : 0 ≤ 3 * Snj n j := by
      rw [three_Snj_dform n j hge hj]
      set P : ℤ := (2 : ℤ) ^ j with hPdef
      set d : ℤ := ((n + 1 - j : ℕ) : ℤ) with hddef
      have hPpos : (0 : ℤ) < P := by rw [hPdef]; positivity
      have hd0 : (0 : ℤ) ≤ d := by rw [hddef]; positivity
      have hjz2 : (2 : ℤ) ≤ (j : ℤ) := by exact_mod_cast hge
      have hjjnn : (0 : ℤ) ≤ 3 * (j : ℤ) * ((j : ℤ) - 1) := by nlinarith [hjz2]
      have hr : j % 6 = 0 ∨ j % 6 = 1 ∨ j % 6 = 2 ∨ j % 6 = 3 ∨ j % 6 = 4 ∨ j % 6 = 5 := by omega
      rcases hr with h | h | h | h | h | h
      · -- j ≡ 0 (mod 6): d ≥ 2, needs both exponential bounds
        have hd2 : (2 : ℤ) ≤ d := by
          rw [hddef]; have : 2 ≤ n + 1 - j := by omega
          exact_mod_cast this
        have hc2 : corr 2 j = -1 := by
          rw [show corr 2 j = corrTab 2 (j % 6) from rfl, h]; rfl
        have hc1 : corr 1 (j - 1) = -2 := by
          rw [show corr 1 (j - 1) = corrTab 1 ((j - 1) % 6) from rfl, show (j - 1) % 6 = 5 from by omega]; rfl
        have hc0 : corr 0 (j - 2) = -1 := by
          rw [show corr 0 (j - 2) = corrTab 0 ((j - 2) % 6) from rfl, show (j - 2) % 6 = 4 from by omega]; rfl
        have hea : 3 * (j : ℤ) + 1 ≤ P := by rw [hPdef]; exact expb_a j (by omega)
        have he0 : 3 * (j : ℤ) * ((j : ℤ) - 1) + 6 * (j : ℤ) + 2 ≤ 2 * P := by
          rw [hPdef]; exact expb_quad0 j (by omega)
        rw [hc2, hc1, hc0]
        nlinarith [mul_nonneg (show (0 : ℤ) ≤ d - 2 by linarith)
          (show (0 : ℤ) ≤ P - (3 * (j : ℤ) + 1) by linarith), he0]
      · -- j ≡ 1 (mod 6): d ≥ 1
        have hd1 : (1 : ℤ) ≤ d := by
          rw [hddef]; have : 1 ≤ n + 1 - j := by omega
          exact_mod_cast this
        have hc2 : corr 2 j = -2 := by
          rw [show corr 2 j = corrTab 2 (j % 6) from rfl, h]; rfl
        have hc1 : corr 1 (j - 1) = -1 := by
          rw [show corr 1 (j - 1) = corrTab 1 ((j - 1) % 6) from rfl, show (j - 1) % 6 = 0 from by omega]; rfl
        have hc0 : corr 0 (j - 2) = 1 := by
          rw [show corr 0 (j - 2) = corrTab 0 ((j - 2) % 6) from rfl, show (j - 2) % 6 = 5 from by omega]; rfl
        have he1 : 3 * (j : ℤ) * ((j : ℤ) - 1) + 2 ≤ P := by
          rw [hPdef]; exact expb_quad1 j (by omega)
        rw [hc2, hc1, hc0]
        nlinarith [mul_nonneg (show (0 : ℤ) ≤ d - 1 by linarith)
          (show (0 : ℤ) ≤ P - 2 by nlinarith [he1, hjjnn]), he1]
      · -- j ≡ 2 (mod 6): d ≥ 0 suffices
        have hc2 : corr 2 j = -1 := by
          rw [show corr 2 j = corrTab 2 (j % 6) from rfl, h]; rfl
        have hc1 : corr 1 (j - 1) = 1 := by
          rw [show corr 1 (j - 1) = corrTab 1 ((j - 1) % 6) from rfl, show (j - 1) % 6 = 1 from by omega]; rfl
        have hc0 : corr 0 (j - 2) = 2 := by
          rw [show corr 0 (j - 2) = corrTab 0 ((j - 2) % 6) from rfl, show (j - 2) % 6 = 0 from by omega]; rfl
        rw [hc2, hc1, hc0]
        nlinarith [mul_nonneg hd0 hPpos.le,
          mul_nonneg hd0 (show (0 : ℤ) ≤ 3 * (j : ℤ) - 1 by linarith)]
      · -- j ≡ 3 (mod 6)
        have hc2 : corr 2 j = 1 := by
          rw [show corr 2 j = corrTab 2 (j % 6) from rfl, h]; rfl
        have hc1 : corr 1 (j - 1) = 2 := by
          rw [show corr 1 (j - 1) = corrTab 1 ((j - 1) % 6) from rfl, show (j - 1) % 6 = 2 from by omega]; rfl
        have hc0 : corr 0 (j - 2) = 1 := by
          rw [show corr 0 (j - 2) = corrTab 0 ((j - 2) % 6) from rfl, show (j - 2) % 6 = 1 from by omega]; rfl
        rw [hc2, hc1, hc0]
        nlinarith [mul_nonneg hd0 hPpos.le,
          mul_nonneg hd0 (show (0 : ℤ) ≤ 3 * (j : ℤ) + 1 by linarith), hjjnn]
      · -- j ≡ 4 (mod 6)
        have hc2 : corr 2 j = 2 := by
          rw [show corr 2 j = corrTab 2 (j % 6) from rfl, h]; rfl
        have hc1 : corr 1 (j - 1) = 1 := by
          rw [show corr 1 (j - 1) = corrTab 1 ((j - 1) % 6) from rfl, show (j - 1) % 6 = 3 from by omega]; rfl
        have hc0 : corr 0 (j - 2) = -1 := by
          rw [show corr 0 (j - 2) = corrTab 0 ((j - 2) % 6) from rfl, show (j - 2) % 6 = 2 from by omega]; rfl
        rw [hc2, hc1, hc0]
        nlinarith [mul_nonneg hd0 hPpos.le, mul_nonneg hd0 (show (0 : ℤ) ≤ (2 : ℤ) by norm_num), hjjnn]
      · -- j ≡ 5 (mod 6): d ≥ 0, needs linear bound
        have hea : 3 * (j : ℤ) + 1 ≤ P := by rw [hPdef]; exact expb_a j (by omega)
        have hc2 : corr 2 j = 1 := by
          rw [show corr 2 j = corrTab 2 (j % 6) from rfl, h]; rfl
        have hc1 : corr 1 (j - 1) = -1 := by
          rw [show corr 1 (j - 1) = corrTab 1 ((j - 1) % 6) from rfl, show (j - 1) % 6 = 4 from by omega]; rfl
        have hc0 : corr 0 (j - 2) = -2 := by
          rw [show corr 0 (j - 2) = corrTab 0 ((j - 2) % 6) from rfl, show (j - 2) % 6 = 3 from by omega]; rfl
        rw [hc2, hc1, hc0]
        nlinarith [mul_nonneg hd0 (show (0 : ℤ) ≤ P - 3 * (j : ℤ) + 1 by linarith)]
    linarith

end CubicPochhammer

