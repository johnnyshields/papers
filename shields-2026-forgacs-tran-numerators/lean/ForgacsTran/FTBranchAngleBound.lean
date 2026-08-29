/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.FTBranchSine
import ForgacsTran.PencilIndex

/-!
# The angle-sum inequality behind the monotonicity of `τ`

`Forgacs2017RationalDenominator` (15): along the branch, `A(θ) > 0`.  Written
out with `sin θ_k cos(θ_k - θ) = (sin (2θ_k - θ) + sin θ)/2`, that inequality is
`∑_k sin (2θ_k - θ) < (2r - n) sin θ`, which is what this module proves — in the
paper's own exclusion `(r, n) ≠ (1, 2)`, and no other restriction.

## Main statements

* `card_le_one_of_lt_pi` — at most one of the angles `2θ_k - θ` lies below `π`,
  a consequence of the angle sum alone.
* `ftPhaseWeight` and `ftPhaseWeight_merge` — the merge identity that replaces
  the paper's two-case split.
* `sin_two_mul_sub_eq_ftPhaseWeight`, `sum_sin_two_mul_sub_eq` — the change of
  variable `ψ = π - φ` that puts (15) in the form the merge argument acts on.
* `sum_sin_two_mul_sub_lt` — the inequality, for `(r, n) ≠ (1, 2)`.

## Implementation notes

**Differs from the paper's route.**  The paper proves (15) in two cases, `r ≥ n/2`
and `n > 2r`, the second by peeling their (18)--(20) one term at a time.  Both
are replaced here by one computation.  In the reflected angles `ψ_k = π - θ_k`,
which are positive and sum to `π - rθ`, the identity
`F(x) + F(y) - F(x + y) = 2 sin x sin y sin (x + y + θ)` for
`F_θ(x) = sin x cos (x + θ)` says that merging two angles never increases
`∑_k F(ψ_k)`; merging all of them leaves a value that is positive for `r ≥ 2` and
exactly zero for `r = 1`, where the strictness of one merge finishes it.  The
paper's `(r, n) ≠ (1, 2)` then appears not as a special case but as the one
configuration in which no strict merge is available.

Sorry-free.

## References

Formalizes `Forgacs2017RationalDenominator` Lemmas 2--5, the branch
`thm:FT-geometry` imports.

## Tags

angle sum, monotonicity, branch radius
-/

namespace ForgacsTran

open Real Set

theorem sin_two_pi_sub (x : ℝ) : Real.sin (2 * π - x) = -Real.sin x := by
  rw [Real.sin_sub, Real.sin_two_pi, Real.cos_two_pi]
  ring

/-- At most one of the angles `2θ_k - θ` lies below `π`.  This uses only
`θ < θ_k < π`, the angle sum, and `r ≥ 1`. -/
theorem card_le_one_of_lt_pi {n r : ℕ} {θ : ℝ} {φ : Fin n → ℝ} (hr : 1 ≤ r)
    (hθ0 : 0 < θ) (hφ : ∀ k, φ k ∈ Ioo θ π)
    (hsum : ∑ k, φ k = r * θ + ((n - 1 : ℕ) : ℝ) * π) :
    ∀ j j' : Fin n, 2 * φ j - θ < π → 2 * φ j' - θ < π → j = j' := by
  classical
  intro j j' hj hj'
  by_contra hjj
  have hn : 1 ≤ n := Fin.pos_iff_nonempty.2 ⟨j⟩
  have hn2 : 2 ≤ n := by
    by_contra h
    have : n = 1 := by omega
    exact hjj (Fin.ext (by omega : (j : ℕ) = (j' : ℕ)))
  have hn1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := cast_pred_eq_sub_one hn
  set g : Fin n → ℝ := fun k => 2 * π - θ - (2 * φ k - θ) with hg
  have hgpos : ∀ k, 0 < g k := by
    intro k
    have := (hφ k).2
    simp only [hg]
    linarith
  have hgj : π - θ < g j := by simp only [hg]; linarith
  have hgj' : π - θ < g j' := by simp only [hg]; linarith
  have hpair : g j + g j' ≤ ∑ k, g k := by
    have hsub : ({j, j'} : Finset (Fin n)) ⊆ Finset.univ := Finset.subset_univ _
    have := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun i _ _ => (hgpos i).le)
    rwa [Finset.sum_pair hjj] at this
  have hgsum : ∑ k, g k = (n : ℝ) * (2 * π - θ) - (2 * (∑ k, φ k) - n * θ) := by
    simp only [hg, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum]
    ring
  rw [hsum, hn1] at hgsum
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  rw [hgsum] at hpair
  nlinarith [hgj, hgj', hθ0, hr1]

/-! ### The merge argument

`Forgacs2017RationalDenominator` proves (15) in two cases, `r ≥ n/2` and
`n > 2r`, the second by peeling their (18)--(20) one term at a time.  Both are
replaced here by a single computation.  In the reflected angles
`ψ_k = π - θ_k`, which are positive and sum to `π - rθ`, the quantity to bound
is `∑_k F(ψ_k) + r sin θ` with `F_θ(x) = sin x cos (x + θ)`, and `F` satisfies

  `F(x) + F(y) - F(x + y) = 2 sin x sin y sin (x + y + θ)`,

so merging two angles never increases the sum.  Merging all of them leaves
`F(π - rθ) + r sin θ = ((2r-1) sin θ - sin((2r-1)θ))/2`, which is positive for
`r ≥ 2` and exactly zero for `r = 1` — where the strictness of a single merge
supplies what is missing, and where `n = 2` is precisely the paper's excluded
case. -/

/-- `F_θ(x) = sin x cos (x + θ)`, the summand of `Forgacs2017RationalDenominator`
(15) in the reflected angles. -/
noncomputable def ftPhaseWeight (θ x : ℝ) : ℝ := Real.sin x * Real.cos (x + θ)

@[simp] theorem ftPhaseWeight_zero (θ : ℝ) : ftPhaseWeight θ 0 = 0 := by
  simp [ftPhaseWeight]

/-- **The merge identity.**  Replacing two angles by their sum changes the weight
by `2 sin x sin y sin (x + y + θ)`. -/
theorem ftPhaseWeight_merge (θ x y : ℝ) :
    ftPhaseWeight θ x + ftPhaseWeight θ y - ftPhaseWeight θ (x + y)
      = 2 * Real.sin x * Real.sin y * Real.sin (x + y + θ) := by
  simp only [ftPhaseWeight, Real.sin_add, Real.cos_add]
  linear_combination
    (Real.sin x ^ 2 * Real.sin θ - Real.sin x * Real.cos x * Real.cos θ)
      * (Real.sin_sq_add_cos_sq y)
    + (Real.sin y ^ 2 * Real.sin θ - Real.sin y * Real.cos y * Real.cos θ)
      * (Real.sin_sq_add_cos_sq x)

/-- Merging never increases the weight sum. -/
theorem ftPhaseWeight_sum_le {ι : Type*} {θ : ℝ} (hθ : 0 < θ) (φ : ι → ℝ)
    (s : Finset ι) (hpos : ∀ k ∈ s, 0 < φ k) (hle : (∑ k ∈ s, φ k) + θ ≤ π) :
    ftPhaseWeight θ (∑ k ∈ s, φ k) ≤ ∑ k ∈ s, ftPhaseWeight θ (φ k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i t hi ih =>
      rw [Finset.sum_insert hi] at hle ⊢
      rw [Finset.sum_insert hi]
      have hposi : 0 < φ i := hpos i (Finset.mem_insert_self i t)
      have hpost : ∀ k ∈ t, 0 < φ k := fun k hk => hpos k (Finset.mem_insert_of_mem hk)
      have htsum : 0 ≤ ∑ k ∈ t, φ k := Finset.sum_nonneg fun k hk => (hpost k hk).le
      have hlet : (∑ k ∈ t, φ k) + θ ≤ π := by linarith
      have hih := ih hpost hlet
      have hmerge := ftPhaseWeight_merge θ (φ i) (∑ k ∈ t, φ k)
      have hspi : 0 ≤ Real.sin (φ i) :=
        Real.sin_nonneg_of_nonneg_of_le_pi hposi.le (by linarith)
      have hspt : 0 ≤ Real.sin (∑ k ∈ t, φ k) :=
        Real.sin_nonneg_of_nonneg_of_le_pi htsum (by linarith)
      have hsps : 0 ≤ Real.sin (φ i + (∑ k ∈ t, φ k) + θ) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
      nlinarith [mul_nonneg (mul_nonneg hspi hspt) hsps]

/-- Two or more angles, with room to spare at `π`: the merge is strict. -/
theorem ftPhaseWeight_sum_lt {ι : Type*} {θ : ℝ} (hθ : 0 < θ) (φ : ι → ℝ)
    {s : Finset ι} (h2 : 2 ≤ s.card) (hpos : ∀ k ∈ s, 0 < φ k)
    (hlt : (∑ k ∈ s, φ k) + θ < π) :
    ftPhaseWeight θ (∑ k ∈ s, φ k) < ∑ k ∈ s, ftPhaseWeight θ (φ k) := by
  classical
  obtain ⟨i, hi⟩ : s.Nonempty := Finset.card_pos.1 (by omega)
  have hterase : (s.erase i).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem hi]; omega
  have hsplit : ∑ k ∈ s, φ k = φ i + ∑ k ∈ s.erase i, φ k :=
    (Finset.add_sum_erase _ _ hi).symm
  have hsplitF : ∑ k ∈ s, ftPhaseWeight θ (φ k)
      = ftPhaseWeight θ (φ i) + ∑ k ∈ s.erase i, ftPhaseWeight θ (φ k) :=
    (Finset.add_sum_erase _ _ hi).symm
  have hposi : 0 < φ i := hpos i hi
  have hpost : ∀ k ∈ s.erase i, 0 < φ k := fun k hk => hpos k (Finset.mem_of_mem_erase hk)
  have htpos : 0 < ∑ k ∈ s.erase i, φ k := Finset.sum_pos hpost hterase
  have hlet : (∑ k ∈ s.erase i, φ k) + θ ≤ π := by rw [hsplit] at hlt; linarith
  have hih := ftPhaseWeight_sum_le hθ φ (s.erase i) hpost hlet
  have hmerge := ftPhaseWeight_merge θ (φ i) (∑ k ∈ s.erase i, φ k)
  have hspi : 0 < Real.sin (φ i) := by
    refine sin_pos_of_pos_of_lt_pi hposi ?_
    rw [hsplit] at hlt; linarith
  have hspt : 0 < Real.sin (∑ k ∈ s.erase i, φ k) := by
    refine sin_pos_of_pos_of_lt_pi htpos ?_
    rw [hsplit] at hlt; linarith
  have hsps : 0 < Real.sin (φ i + (∑ k ∈ s.erase i, φ k) + θ) := by
    refine sin_pos_of_pos_of_lt_pi (by linarith) ?_
    rw [hsplit] at hlt; linarith
  rw [hsplit, hsplitF]
  nlinarith [mul_pos (mul_pos hspi hspt) hsps]

/-- Three or more angles: the merge is strict even when the total reaches `π`,
which is the case `r = 1`. -/
theorem ftPhaseWeight_sum_lt' {ι : Type*} {θ : ℝ} (hθ : 0 < θ) (φ : ι → ℝ)
    {s : Finset ι} (h3 : 3 ≤ s.card) (hpos : ∀ k ∈ s, 0 < φ k)
    (hle : (∑ k ∈ s, φ k) + θ ≤ π) :
    ftPhaseWeight θ (∑ k ∈ s, φ k) < ∑ k ∈ s, ftPhaseWeight θ (φ k) := by
  classical
  obtain ⟨i, hi⟩ : s.Nonempty := Finset.card_pos.1 (by omega)
  have hcard : 2 ≤ (s.erase i).card := by
    rw [Finset.card_erase_of_mem hi]; omega
  have hsplit : ∑ k ∈ s, φ k = φ i + ∑ k ∈ s.erase i, φ k :=
    (Finset.add_sum_erase _ _ hi).symm
  have hsplitF : ∑ k ∈ s, ftPhaseWeight θ (φ k)
      = ftPhaseWeight θ (φ i) + ∑ k ∈ s.erase i, ftPhaseWeight θ (φ k) :=
    (Finset.add_sum_erase _ _ hi).symm
  have hposi : 0 < φ i := hpos i hi
  have hpost : ∀ k ∈ s.erase i, 0 < φ k := fun k hk => hpos k (Finset.mem_of_mem_erase hk)
  have htpos : 0 < ∑ k ∈ s.erase i, φ k :=
    Finset.sum_pos hpost (Finset.card_pos.1 (by omega))
  have hltt : (∑ k ∈ s.erase i, φ k) + θ < π := by rw [hsplit] at hle; linarith
  have hih := ftPhaseWeight_sum_lt hθ φ hcard hpost hltt
  have hmerge := ftPhaseWeight_merge θ (φ i) (∑ k ∈ s.erase i, φ k)
  have hspi : 0 ≤ Real.sin (φ i) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hposi.le (by rw [hsplit] at hle; linarith)
  have hspt : 0 ≤ Real.sin (∑ k ∈ s.erase i, φ k) :=
    Real.sin_nonneg_of_nonneg_of_le_pi htpos.le (by linarith)
  have hsps : 0 ≤ Real.sin (φ i + (∑ k ∈ s.erase i, φ k) + θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by rw [hsplit] at hle; linarith)
  rw [hsplit, hsplitF]
  nlinarith [mul_nonneg (mul_nonneg hspi hspt) hsps]

/-- The fully merged value: `F(π - mθ) + m sin θ = ((2m-1) sin θ - sin((2m-1)θ))/2`. -/
theorem ftPhaseWeight_pi_sub (m θ : ℝ) :
    ftPhaseWeight θ (π - m * θ) + m * Real.sin θ
      = ((2 * m - 1) * Real.sin θ - Real.sin ((2 * m - 1) * θ)) / 2 := by
  have h1 : π - m * θ + θ = π - (m - 1) * θ := by ring
  have h2 : (2 * m - 1) * θ = m * θ + (m - 1) * θ := by ring
  rw [ftPhaseWeight, h1, h2, Real.sin_pi_sub, Real.cos_pi_sub, Real.sin_add]
  have h3 : (m - 1) * θ = m * θ - θ := by ring
  rw [h3, Real.sin_sub, Real.cos_sub]
  linear_combination (-(Real.sin θ / 2)) * (Real.sin_sq_add_cos_sq (m * θ))

/-- **The derivative sum in the reflected angle.**  With `ψ = π - φ`,
`sin(2φ - θ) = -(2F_θ(ψ) + sin θ)`, where `F_θ` is `ftPhaseWeight`.  This is the
change of variable that turns `Forgacs2017RationalDenominator` (15) into the
merge argument's objective: what has to be shown positive is a sum of phase
weights over positive angles with a fixed total, and merging is available there
and not on the `φ`. -/
theorem sin_two_mul_sub_eq_ftPhaseWeight (θ φ : ℝ) :
    Real.sin (2 * φ - θ) = -(2 * ftPhaseWeight θ (π - φ) + Real.sin θ) := by
  simp only [ftPhaseWeight]
  rw [show π - φ + θ = π - (φ - θ) by ring, Real.sin_pi_sub, Real.cos_pi_sub,
    show 2 * φ - θ = φ + (φ - θ) by ring, Real.sin_add, Real.sin_sub, Real.cos_sub]
  linear_combination (-(Real.sin θ)) * (Real.sin_sq_add_cos_sq φ)

/-- The sum form of `sin_two_mul_sub_eq_ftPhaseWeight`. -/
theorem sum_sin_two_mul_sub_eq {n : ℕ} (θ : ℝ) (φ : Fin n → ℝ) :
    ∑ k, Real.sin (2 * φ k - θ)
      = -(2 * (∑ k, ftPhaseWeight θ (π - φ k)) + n * Real.sin θ) := by
  rw [Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) =>
    sin_two_mul_sub_eq_ftPhaseWeight θ (φ k)]
  rw [Finset.sum_neg_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **`Forgacs2017RationalDenominator` (15).**  The quantity `A(θ)` of their (15)
is positive, in the equivalent form `∑_k sin (2θ_k - θ) < (2r - n) sin θ`.

**Differs from the paper's route.**  They split into `r ≥ n/2` and `n > 2r` and
prove the second by peeling (18)--(20).  Both cases are handled here at once by
`ftPhaseWeight_merge`: in the reflected angles `ψ_k = π - θ_k`, which are
positive and sum to `π - rθ`, merging any two angles never increases
`∑_k F(ψ_k)`, and the fully merged value `F(π - rθ) + r sin θ` is
`((2r-1) sin θ - sin((2r-1)θ))/2`.  That is positive for `r ≥ 2`; for `r = 1` it
is exactly zero and the strictness of one merge supplies the rest, which needs
three angles — so `(r, n) = (1, 2)` is excluded not as a special case but as the
one configuration where no strict merge is available. -/
theorem sum_sin_two_mul_sub_lt {n r : ℕ} {θ : ℝ} {φ : Fin n → ℝ} (hn : 0 < n) (hr : 1 ≤ r)
    (hne : ¬(r = 1 ∧ n = 2)) (hθ0 : 0 < θ) (hθr : θ < π / r)
    (hφ : ∀ k, φ k ∈ Ioo θ π) (hsum : ∑ k, φ k = r * θ + ((n - 1 : ℕ) : ℝ) * π) :
    ∑ k, Real.sin (2 * φ k - θ) < (2 * r - n : ℝ) * Real.sin θ := by
  classical
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hrθ : (r : ℝ) * θ < π := by rw [lt_div_iff₀ hr0] at hθr; linarith
  have hθπ : θ < π := by nlinarith
  have hsθ : 0 < Real.sin θ := sin_pos_of_pos_of_lt_pi hθ0 hθπ
  have hn1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := cast_pred_eq_sub_one hn
  have hUne : (Finset.univ : Finset (Fin n)).Nonempty :=
    Finset.univ_nonempty_iff.2 (Fin.pos_iff_nonempty.1 hn)
  -- the range condition clause (i) forces
  have hrange : (n : ℝ) * θ < r * θ + ((n : ℝ) - 1) * π := by
    have h := Finset.sum_lt_sum_of_nonempty hUne fun k (_ : k ∈ Finset.univ) => (hφ k).1
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hsum,
      hn1] at h
    linarith
  -- the reflected angles: positive, summing to `π - rθ`
  set ψ : Fin n → ℝ := fun k => π - φ k with hψdef
  have hψpos : ∀ k, 0 < ψ k := fun k => by simp only [hψdef]; linarith [(hφ k).2]
  have hψsum : ∑ k, ψ k = π - r * θ := by
    simp only [hψdef, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, hsum, hn1]
    ring
  have hψle : (∑ k, ψ k) + θ ≤ π := by rw [hψsum]; nlinarith
  -- the reduction to the phase weights
  have hred : ∑ k, Real.sin (2 * φ k - θ)
      = -(2 * (∑ k, ftPhaseWeight θ (ψ k)) + n * Real.sin θ) :=
    sum_sin_two_mul_sub_eq θ φ
  suffices hkey : 0 < (∑ k, ftPhaseWeight θ (ψ k)) + r * Real.sin θ by
    rw [hred]; linarith
  have hmerged : ftPhaseWeight θ (∑ k, ψ k) + r * Real.sin θ
      = ((2 * (r : ℝ) - 1) * Real.sin θ - Real.sin ((2 * (r : ℝ) - 1) * θ)) / 2 := by
    rw [hψsum]; exact ftPhaseWeight_pi_sub (r : ℝ) θ
  rcases le_or_gt 2 r with hr2 | hrlt
  · -- `r ≥ 2`: the merged value is already positive
    have hle := ftPhaseWeight_sum_le hθ0 ψ Finset.univ (fun k _ => hψpos k) hψle
    have hm : (2 : ℕ) ≤ 2 * r - 1 := by omega
    have hcast : ((2 * r - 1 : ℕ) : ℝ) = 2 * (r : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_two, Nat.cast_one]
    have hlt := abs_sin_nat_mul_lt (x := θ) hm ⟨hθ0, hθπ⟩
    rw [hcast] at hlt
    have hlt' : Real.sin ((2 * (r : ℝ) - 1) * θ) < (2 * (r : ℝ) - 1) * Real.sin θ :=
      lt_of_le_of_lt (le_abs_self _) hlt
    linarith
  · -- `r = 1`: the merged value is zero, and a strict merge supplies the rest
    have hreq : r = 1 := by omega
    have hn3 : 3 ≤ n := by
      by_contra hlt3
      have : n = 1 ∨ n = 2 := by omega
      rcases this with h1 | h2
      · rw [hreq, h1] at hrange
        norm_num at hrange
      · exact hne ⟨hreq, h2⟩
    have hcard : 3 ≤ (Finset.univ : Finset (Fin n)).card := by
      rw [Finset.card_univ, Fintype.card_fin]; exact hn3
    have hstrict := ftPhaseWeight_sum_lt' hθ0 ψ hcard (fun k _ => hψpos k) hψle
    rw [hreq] at hmerged
    norm_num at hmerged
    rw [hreq]
    push_cast
    linarith


end ForgacsTran
