/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import CubicPochhammer.Snj
import CubicPochhammer.BernsteinBasis
import Mathlib.Algebra.BigOperators.Field

/-!
# The Bernstein certificate: `J_m(t) > 0`

Formalizes `shields-2026-cubic-pochhammer.tex`,
`subsec:constant-weight-kernel` «The constant-weight kernel», `lem:bernstein`.
With `n = 3m-2`, the constant-weight derivative polynomial

  `J_m(t) = ∑_{k=1}^{m-1} C(3m-2, 3k-1) t^{3k-1} (k - (m-k) t)`   (`eq:J-k`)

controls the monotonicity of the constant-weight kernel `G_m`.  Its
Bernstein-basis representation (`eq:P-def`–`eq:P-coeff`) is

  `3(n+1) J_m(t) = ∑_{j=0}^{n+1} S_{n,j} · C(n+1,j) · t^j (1-t)^{n+1-j}`.   (★)

Since every `S_{n,j} ≥ 0` (`snj_nonneg`, proven) and `S_{n,2} > 0`, the right
side is strictly positive on `(0,1)`; hence `J_m(t) > 0`.

Identity (★) is proven here, as `jm_bernstein`, from the division-free form of
the projective Bernstein transform (`BernsteinBasis.bernstein_reconstruction`)
and the two binomial revision identities (`revision_one`, `revision_two`): the
`ν`-reindexing `eq:J-k → eq:P-sum` is `three_jm_nu` and `three_jm_monomial`, and
the coefficient extraction `eq:P-coeff` is `pcoef_transform`.  It is
cross-checked symbolically in `../../scripts/verify_kernel.py` and by hand at
`m=2` (both sides equal `90 t²(1-t)`).

Sorry-free, no project axioms.

## Main definitions

* `jm` --- the constant-weight derivative polynomial `J_m` of `eq:J-k`, at `n = 3m-2`.
* `avc`, `bvc`, `pcoef` --- the two `ν`-indexed families the reindexing
  `eq:J-k → eq:P-sum` splits `3 J_m` into, and their combination into the
  monomial coefficients of `3 J_m`.
* `bcoeff` --- the Bernstein coefficient `b_j = S_{n,j}/(3(n+1))` (`eq:P-coeff`).

## Main statements

* `avc_transform`, `bvc_transform` --- the two revision identities applied
  under the sum, which is what `eq:P-coeff` is.
* `pcoef_transform` --- the two halves combined into `S_{n,j} C(n+1,j)/(n+1)`.
* `jm_bernstein` --- the Bernstein representation (★) of `3(n+1) J_m`.
* `jm_eq_bcoeff_sum` --- the same identity with the normalization cleared.
* `bcoeff_two_pos` --- the coefficient at `j = 2` is strictly positive, which is
  what makes the nonnegative representation give a strict conclusion.
* `bernstein_sum_pos` --- the Bernstein sum itself is positive on `(0,1)`.
* `jm_pos` --- `lem:bernstein`: `J_m(t) > 0` for `0 < t < 1` and `m ≥ 2`.

## References

* `shields-2026-cubic-pochhammer.tex`, `subsec:constant-weight-kernel`
  «The constant-weight kernel»: `lem:bernstein`, `eq:J-k`, `eq:P-def`,
  `eq:P-sum`, `eq:P-coeff`.
-/

open scoped BigOperators

namespace CubicPochhammer

/-- The constant-weight derivative polynomial `J_m(t)` (`eq:J-k`), `n = 3m-2`. -/
noncomputable def jm (m : ℕ) (t : ℝ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 (m - 1),
    (Nat.choose (3 * m - 2) (3 * r - 1) : ℝ) * t ^ (3 * r - 1) * ((r : ℝ) - ((m : ℝ) - (r : ℝ)) * t)

/-! ### The monomial coefficients of `3 J_m` -/

/-- The `t^ν` family of `3 J_m` in the ν-form of `lem:bernstein`'s proof:
`3 J_m(t) = ∑_{ν≡2 (3)} C(n,ν) t^ν ((ν+1) - (n-ν+1)t)`, `n = 3m-2`. -/
noncomputable def avc (n i : ℕ) : ℝ :=
  if i % 3 = 2 then (Nat.choose n i : ℝ) * ((i : ℝ) + 1) else 0

/-- The `t^{ν+1}` family of the same expansion. -/
noncomputable def bvc (n i : ℕ) : ℝ :=
  if i % 3 = 2 then (Nat.choose n i : ℝ) * ((n : ℝ) - (i : ℝ) + 1) else 0

/-- The monomial coefficients of `3 J_m`, the two families combined by the shift. -/
noncomputable def pcoef (n i : ℕ) : ℝ :=
  avc n i - (if 1 ≤ i then bvc n (i - 1) else 0)

/-- Reindexing `eq:J-k` by `ν = 3k-1`: `3 J_m(t) = ∑_{ν≤n, ν≡2 (3)} C(n,ν) t^ν
((ν+1) - (n-ν+1)t)`, over the filtered range. -/
theorem three_jm_nu (m : ℕ) (hm : 1 ≤ m) (t : ℝ) :
    3 * jm m t = ∑ ν ∈ (Finset.range (3 * m - 1)).filter (fun ν => ν % 3 = 2),
      (Nat.choose (3 * m - 2) ν : ℝ) * t ^ ν
        * (((ν : ℝ) + 1) - ((((3 * m - 2 : ℕ)) : ℝ) - (ν : ℝ) + 1) * t) := by
  unfold jm
  rw [Finset.mul_sum]
  refine Finset.sum_nbij' (fun r => 3 * r - 1) (fun ν => (ν + 1) / 3) ?_ ?_ ?_ ?_ ?_
  · intro r hr
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hr
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  · intro ν hν
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hν
    rw [Finset.mem_range] at h1
    simp only [Finset.mem_Icc]
    omega
  · intro r hr
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hr
    dsimp only; omega
  · intro ν hν
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hν
    rw [Finset.mem_range] at h1
    dsimp only; omega
  · intro r hr
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hr
    dsimp only
    have hc1 : ((3 * r - 1 : ℕ) : ℝ) = 3 * (r : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have hc2 : ((3 * m - 2 : ℕ) : ℝ) = 3 * (m : ℝ) - 2 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [hc1, hc2]
    ring

/-- `3 J_m` in the monomial basis, degree at most `n+1 = 3m-1`. -/
theorem three_jm_monomial (m : ℕ) (hm : 1 ≤ m) (t : ℝ) :
    3 * jm m t = ∑ i ∈ Finset.range (3 * m), pcoef (3 * m - 2) i * t ^ i := by
  obtain ⟨M, hM⟩ : ∃ M, 3 * m = M + 1 := ⟨3 * m - 1, by omega⟩
  have hM1 : 3 * m - 1 = M := by omega
  have hR : ∑ i ∈ Finset.range (3 * m), pcoef (3 * m - 2) i * t ^ i
      = (∑ ν ∈ Finset.range M, avc (3 * m - 2) ν * t ^ ν)
        - ∑ ν ∈ Finset.range M, bvc (3 * m - 2) ν * t ^ (ν + 1) := by
    have hterm : ∀ i ∈ Finset.range (3 * m),
        pcoef (3 * m - 2) i * t ^ i
          = avc (3 * m - 2) i * t ^ i
            - (if 1 ≤ i then bvc (3 * m - 2) (i - 1) else 0) * t ^ i := by
      intro i _; unfold pcoef; ring
    have hrange : Finset.range (3 * m) = Finset.range (M + 1) := by rw [hM]
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, hrange]
    congr 1
    · rw [Finset.sum_range_succ]
      have hz : avc (3 * m - 2) M = 0 := by
        unfold avc
        rw [if_pos (by omega), Nat.choose_eq_zero_of_lt (by omega)]
        simp
      rw [hz]; ring
    · rw [Finset.sum_range_succ']
      simp
  rw [hR, three_jm_nu m hm t, hM1, Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun ν _ => ?_
  unfold avc bvc
  by_cases h : ν % 3 = 2
  · rw [if_pos h, if_pos h, if_pos h, pow_succ]; ring
  · rw [if_neg h, if_neg h, if_neg h]; ring

/-- `S_{n,j}` cast into `ℝ`, termwise. -/
theorem snj_cast (n j : ℕ) :
    (snj n j : ℝ) = ∑ k ∈ Finset.range (j + 1),
      (if k % 3 = 2 then ((n : ℝ) - (k : ℝ) + 1) * (2 * (k : ℝ) + 1 - (j : ℝ))
        * (Nat.choose j k : ℝ) else 0) := by
  unfold snj
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> ring

/-- **The `a`-family under the Bernstein transform.**  `revision_one` applied term by
term: it replaces `(n+1)C(n,ν)C(n+1-ν,j-ν)` by `C(n+1,j)C(j,ν)(n+1-ν)`, which pulls the
`j`-dependent binomial out of the sum and leaves `eq:S-def`'s first factor. -/
theorem avc_transform (n j : ℕ) (hj : j ≤ n + 1) :
    ((n + 1 : ℕ) : ℝ)
        * (∑ i ∈ Finset.range (j + 1), avc n i * (Nat.choose (n + 1 - i) (j - i) : ℝ))
      = (Nat.choose (n + 1) j : ℝ) * ∑ i ∈ Finset.range (j + 1),
          (if i % 3 = 2 then (Nat.choose j i : ℝ) * ((n : ℝ) - (i : ℝ) + 1) * ((i : ℝ) + 1)
            else 0) := by
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  have hij : i ≤ j := by omega
  have hrevR : ((n + 1 : ℕ) : ℝ)
      * ((Nat.choose n i : ℝ) * (Nat.choose (n + 1 - i) (j - i) : ℝ))
      = (Nat.choose (n + 1) j : ℝ) * (Nat.choose j i : ℝ) * ((n + 1 - i : ℕ) : ℝ) := by
    exact_mod_cast congrArg (fun x : ℕ => (x : ℝ)) (revision_one n hij)
  have hcast : ((n + 1 - i : ℕ) : ℝ) = (n : ℝ) - (i : ℝ) + 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [hcast] at hrevR
  unfold avc
  by_cases h : i % 3 = 2
  · rw [if_pos h, if_pos h]
    linear_combination ((i : ℝ) + 1) * hrevR
  · rw [if_neg h, if_neg h]; ring

/-- **The `b`-family under the Bernstein transform.**  `revision_two` applied term by
term: `(n+1)C(n,ν)C(n-ν,j-1-ν) = C(n+1,j)C(j,ν)(j-ν)`, leaving `eq:S-def`'s second
factor.  The sum runs over `ν < j`, which is where `revision_two` is valid. -/
theorem bvc_transform (n j : ℕ) :
    ((n + 1 : ℕ) : ℝ)
        * (∑ ν ∈ Finset.range j, bvc n ν * (Nat.choose (n - ν) (j - 1 - ν) : ℝ))
      = (Nat.choose (n + 1) j : ℝ) * ∑ ν ∈ Finset.range j,
          (if ν % 3 = 2 then (Nat.choose j ν : ℝ) * ((n : ℝ) - (ν : ℝ) + 1)
            * ((j : ℝ) - (ν : ℝ)) else 0) := by
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ν hν => ?_
  rw [Finset.mem_range] at hν
  have hrevR : ((n + 1 : ℕ) : ℝ)
      * ((Nat.choose n ν : ℝ) * (Nat.choose (n - ν) (j - 1 - ν) : ℝ))
      = (Nat.choose (n + 1) j : ℝ) * (Nat.choose j ν : ℝ) * ((j - ν : ℕ) : ℝ) := by
    exact_mod_cast congrArg (fun x : ℕ => (x : ℝ)) (revision_two n (by omega) (by omega))
  have hcast : ((j - ν : ℕ) : ℝ) = (j : ℝ) - (ν : ℝ) := by
    rw [Nat.cast_sub (by omega)]
  rw [hcast] at hrevR
  unfold bvc
  by_cases h : ν % 3 = 2
  · rw [if_pos h, if_pos h]
    linear_combination ((n : ℝ) - (ν : ℝ) + 1) * hrevR
  · rw [if_neg h, if_neg h]; ring

/-- **`eq:P-coeff`**: the `ξ`-coefficients of the transform of `3 J_m` are
`S_{n,j} C(n+1,j)/(n+1)`.  The two revision identities `revision_one` and
`revision_two` turn the two families of `pcoef` into the two halves of `S_{n,j}`,
which combine because both carry the same factor `n-ν+1`:
`(ν+1) - (j-ν) = 2ν+1-j`.

The second half is summed over `ν < j`, which is where `revision_two` is valid
(its `ℕ`-truncated `j-1-ν` fails at `ν = j`; see its docstring).  The missing
`ν = j` term is restored in `hext`, after the transport into `ℝ`, where it
carries the real factor `(j : ℝ) - (j : ℝ)` and is zero outright. -/
theorem pcoef_transform (n j : ℕ) (hj : j ≤ n + 1) :
    ((n + 1 : ℕ) : ℝ) * (∑ i ∈ Finset.range (n + 2),
        (if i ≤ j then pcoef n i * (Nat.choose (n + 1 - i) (j - i) : ℝ) else 0))
      = (snj n j : ℝ) * (Nat.choose (n + 1) j : ℝ) := by
  have hcollapse : ∑ i ∈ Finset.range (n + 2),
        (if i ≤ j then pcoef n i * (Nat.choose (n + 1 - i) (j - i) : ℝ) else 0)
      = ∑ i ∈ Finset.range (j + 1), pcoef n i * (Nat.choose (n + 1 - i) (j - i) : ℝ) := by
    rw [← Finset.sum_filter]
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  have hsplit : ∑ i ∈ Finset.range (j + 1), pcoef n i * (Nat.choose (n + 1 - i) (j - i) : ℝ)
      = (∑ i ∈ Finset.range (j + 1), avc n i * (Nat.choose (n + 1 - i) (j - i) : ℝ))
        - ∑ i ∈ Finset.range (j + 1),
            (if 1 ≤ i then bvc n (i - 1) else 0) * (Nat.choose (n + 1 - i) (j - i) : ℝ) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by unfold pcoef; ring
  have hshift : ∑ i ∈ Finset.range (j + 1),
        (if 1 ≤ i then bvc n (i - 1) else 0) * (Nat.choose (n + 1 - i) (j - i) : ℝ)
      = ∑ ν ∈ Finset.range j, bvc n ν * (Nat.choose (n - ν) (j - 1 - ν) : ℝ) := by
    rw [Finset.sum_range_succ']
    have hterm : ∀ ν ∈ Finset.range j,
        (if 1 ≤ ν + 1 then bvc n (ν + 1 - 1) else 0)
            * (Nat.choose (n + 1 - (ν + 1)) (j - (ν + 1)) : ℝ)
          = bvc n ν * (Nat.choose (n - ν) (j - 1 - ν) : ℝ) := by
      intro ν _
      rw [if_pos (by omega), show ν + 1 - 1 = ν from by omega,
        show n + 1 - (ν + 1) = n - ν from by omega, show j - (ν + 1) = j - 1 - ν from by omega]
    rw [Finset.sum_congr rfl hterm]
    simp
  have hone := avc_transform n j hj
  have htwo := bvc_transform n j
  have hext : ∑ ν ∈ Finset.range j,
        (if ν % 3 = 2 then (Nat.choose j ν : ℝ) * ((n : ℝ) - (ν : ℝ) + 1)
          * ((j : ℝ) - (ν : ℝ)) else 0)
      = ∑ ν ∈ Finset.range (j + 1),
        (if ν % 3 = 2 then (Nat.choose j ν : ℝ) * ((n : ℝ) - (ν : ℝ) + 1)
          * ((j : ℝ) - (ν : ℝ)) else 0) := by
    rw [Finset.sum_range_succ]
    have hzero : (if j % 3 = 2 then (Nat.choose j j : ℝ) * ((n : ℝ) - (j : ℝ) + 1)
        * ((j : ℝ) - (j : ℝ)) else 0) = 0 := by
      split_ifs <;> simp
    rw [hzero, add_zero]
  rw [hcollapse, hsplit, hshift, mul_sub, hone, htwo, hext, ← mul_sub,
    ← Finset.sum_sub_distrib, mul_comm]
  congr 1
  rw [snj_cast]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases h : k % 3 = 2
  · rw [if_pos h, if_pos h, if_pos h]; ring
  · rw [if_neg h, if_neg h, if_neg h]; ring

/-- **The Bernstein coefficient identity (★)** (`eq:P-coeff`).  With `n = 3m-2`,
`J_m` has Bernstein coefficients `S_{n,j}/(3(n+1))`:

  `3(n+1) J_m(t) = ∑_{j=0}^{n+1} S_{n,j} C(n+1,j) t^j (1-t)^{n+1-j}`.

`three_jm_monomial` puts `3 J_m` in the monomial basis, `pcoef_transform`
identifies the `ξ`-coefficients of its Bernstein transform with
`S_{n,j}C(n+1,j)/(n+1)`, and `bernstein_reconstruction` reads them back. -/
theorem jm_bernstein (m : ℕ) (t : ℝ) :
    3 * ((3 * m - 1 : ℕ) : ℝ) * jm m t
      = ∑ j ∈ Finset.range (3 * m),
          (snj (3 * m - 2) j : ℝ) * (Nat.choose (3 * m - 1) j : ℝ)
            * t ^ j * (1 - t) ^ (3 * m - 1 - j) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp [jm]
  obtain ⟨n, hn⟩ : ∃ n, 3 * m = n + 2 := ⟨3 * m - 2, by omega⟩
  have hn1 : 3 * m - 1 = n + 1 := by omega
  have hn2 : 3 * m - 2 = n := by omega
  rw [hn1, hn2, hn]
  have hmono : 3 * jm m t = ∑ i ∈ Finset.range (n + 2), pcoef n i * t ^ i := by
    rw [three_jm_monomial m hm t, hn2, hn]
  calc 3 * ((n + 1 : ℕ) : ℝ) * jm m t
      = ((n + 1 : ℕ) : ℝ) * (3 * jm m t) := by ring
    _ = ((n + 1 : ℕ) : ℝ) * ∑ i ∈ Finset.range (n + 1 + 1), pcoef n i * t ^ i := by
        rw [hmono]
    _ = ((n + 1 : ℕ) : ℝ) * ∑ j ∈ Finset.range (n + 1 + 1),
          (∑ i ∈ Finset.range (n + 1 + 1),
            (if i ≤ j then pcoef n i * (Nat.choose (n + 1 - i) (j - i) : ℝ) else 0))
            * t ^ j * (1 - t) ^ (n + 1 - j) := by
        rw [bernstein_reconstruction]
    _ = ∑ j ∈ Finset.range (n + 2),
          (snj n j : ℝ) * (Nat.choose (n + 1) j : ℝ) * t ^ j * (1 - t) ^ (n + 1 - j) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [Finset.mem_range] at hj
        have hpt := pcoef_transform n j (by omega)
        calc ((n + 1 : ℕ) : ℝ) * ((∑ i ∈ Finset.range (n + 1 + 1),
              (if i ≤ j then pcoef n i * (Nat.choose (n + 1 - i) (j - i) : ℝ) else 0))
              * t ^ j * (1 - t) ^ (n + 1 - j))
            = (((n + 1 : ℕ) : ℝ) * ∑ i ∈ Finset.range (n + 2),
                (if i ≤ j then pcoef n i * (Nat.choose (n + 1 - i) (j - i) : ℝ) else 0))
                * t ^ j * (1 - t) ^ (n + 1 - j) := by ring
          _ = (snj n j : ℝ) * (Nat.choose (n + 1) j : ℝ) * t ^ j * (1 - t) ^ (n + 1 - j) := by
              rw [hpt]

/-- The degree-two certificate value: `S_{n,2} = 3(n-1)` (`3S_{n,2}=9d`,
`d=n-1`). -/
theorem snj_two_eq (n : ℕ) : snj n 2 = 3 * (n : ℤ) - 3 := by
  simp only [snj, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  ring

/-- `S_{n,2} > 0` for `n ≥ 2` (the strictly positive `[x²]` coefficient). -/
theorem snj_two_pos (n : ℕ) (hn : 2 ≤ n) : 0 < snj n 2 := by
  rw [snj_two_eq]
  have : (2 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
  linarith

/-- The Bernstein coefficient of `lem:bernstein`, `b_j = S_{n,j}/(3(n+1))`
(`eq:P-coeff`). -/
noncomputable def bcoeff (n j : ℕ) : ℝ := (snj n j : ℝ) / (3 * ((n : ℝ) + 1))

/-- `J_m` expanded in the degree-`(n+1)` Bernstein basis with the coefficients
`b_j` of `lem:bernstein`, `n = 3m-2`.  This is `jm_bernstein` divided by
`3(n+1)`. -/
theorem jm_eq_bcoeff_sum (m : ℕ) (hm : 1 ≤ m) (t : ℝ) :
    jm m t = ∑ j ∈ Finset.range (3 * m),
      bcoeff (3 * m - 2) j * (Nat.choose (3 * m - 1) j : ℝ)
        * t ^ j * (1 - t) ^ (3 * m - 1 - j) := by
  have hcast : ((3 * m - 2 : ℕ) : ℝ) + 1 = ((3 * m - 1 : ℕ) : ℝ) := by
    rw [show 3 * m - 1 = (3 * m - 2) + 1 from by omega]; push_cast; ring
  have hne : (3 : ℝ) * ((3 * m - 1 : ℕ) : ℝ) ≠ 0 := by
    have : 0 < 3 * m - 1 := by omega
    have : (0 : ℝ) < ((3 * m - 1 : ℕ) : ℝ) := by exact_mod_cast this
    positivity
  have hb := jm_bernstein m t
  have hterm : ∀ j ∈ Finset.range (3 * m),
      bcoeff (3 * m - 2) j * (Nat.choose (3 * m - 1) j : ℝ) * t ^ j * (1 - t) ^ (3 * m - 1 - j)
        = ((snj (3 * m - 2) j : ℝ) * (Nat.choose (3 * m - 1) j : ℝ) * t ^ j
            * (1 - t) ^ (3 * m - 1 - j)) / (3 * ((3 * m - 1 : ℕ) : ℝ)) := by
    intro j _
    rw [bcoeff, hcast]; ring
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, ← hb,
    mul_div_cancel_left₀ _ hne]

/-- **The degree-two Bernstein coefficient** (`lem:bernstein`):
`b_2 = (n-1)/(n+1)`. -/
theorem bcoeff_two_eq (n : ℕ) : bcoeff n 2 = ((n : ℝ) - 1) / ((n : ℝ) + 1) := by
  have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
  rw [bcoeff, snj_two_eq]
  push_cast
  rw [div_eq_div_iff (by positivity) hne]
  ring

/-- `b_2 > 0` for `n ≥ 2`, the strictly positive Bernstein coefficient of
`lem:bernstein`. -/
theorem bcoeff_two_pos (n : ℕ) (hn : 2 ≤ n) : 0 < bcoeff n 2 := by
  have hn' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [bcoeff_two_eq]
  apply div_pos <;> linarith

/-- **The Bernstein sum is positive on `(0,1)`.**  This is the right-hand side of
`jm_bernstein`: every term is nonnegative by `snj_nonneg`, since `n = 3m-2` has residue
`1` mod `3`, and the `j = 2` term is strictly positive by `snj_two_pos`. -/
theorem bernstein_sum_pos (m : ℕ) (hm : 2 ≤ m) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    0 < ∑ j ∈ Finset.range (3 * m),
      (snj (3 * m - 2) j : ℝ) * (Nat.choose (3 * m - 1) j : ℝ) * t ^ j
        * (1 - t) ^ (3 * m - 1 - j) := by
  have hn3 : (3 * m - 2) % 3 = 1 := by omega
  have hsubt : (0 : ℝ) ≤ 1 - t := by linarith
  apply Finset.sum_pos'
  · intro j hj
    rw [Finset.mem_range] at hj
    have hSnn : (0 : ℝ) ≤ (snj (3 * m - 2) j : ℝ) := by
      exact_mod_cast snj_nonneg (3 * m - 2) j hn3 (by omega)
    exact mul_nonneg (mul_nonneg (mul_nonneg hSnn (by positivity)) (by positivity))
      (pow_nonneg hsubt _)
  · refine ⟨2, Finset.mem_range.mpr (by omega), ?_⟩
    have hS2 : (0 : ℝ) < (snj (3 * m - 2) 2 : ℝ) := by
      exact_mod_cast snj_two_pos (3 * m - 2) (by omega)
    have hC : (0 : ℝ) < (Nat.choose (3 * m - 1) 2 : ℝ) := by
      have : 0 < Nat.choose (3 * m - 1) 2 := Nat.choose_pos (by omega)
      exact_mod_cast this
    have hpt : (0 : ℝ) < t ^ 2 := by positivity
    have hpt2 : (0 : ℝ) < (1 - t) ^ (3 * m - 1 - 2) := pow_pos (by linarith) _
    exact mul_pos (mul_pos (mul_pos hS2 hC) hpt) hpt2

/-- **`lem:bernstein`**: `J_m(t) > 0` for `0 < t < 1` and `m ≥ 2`.  Divide the positive
Bernstein sum by the positive constant `3(n+1)` of `jm_bernstein`. -/
theorem jm_pos (m : ℕ) (hm : 2 ≤ m) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) : 0 < jm m t := by
  have hpos : (0 : ℝ) < 3 * ((3 * m - 1 : ℕ) : ℝ) := by
    have hnat : 0 < 3 * m - 1 := by omega
    have : (0 : ℝ) < ((3 * m - 1 : ℕ) : ℝ) := by exact_mod_cast hnat
    linarith
  have hprod : 0 < 3 * ((3 * m - 1 : ℕ) : ℝ) * jm m t := by
    rw [jm_bernstein]; exact bernstein_sum_pos m hm ht0 ht1
  by_contra hJ
  rw [not_lt] at hJ
  have : 3 * ((3 * m - 1 : ℕ) : ℝ) * jm m t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hpos.le hJ
  linarith

end CubicPochhammer
