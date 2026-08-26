/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic.Common

/-!
# Hankel matrices and linear recurrences

The **Hankel matrix** of a sequence `\varpi` is `[\varpi_{s+t}]`: constant along antidiagonals,
as the Toeplitz matrix is constant along diagonals.  Its determinants detect linear recurrences.

If the sequence satisfies a linear recurrence of order `d` — some nonzero vector annihilates every
window — then every Hankel minor of size above `d` vanishes, because the recurrence exhibits a
null vector of the matrix.  Conversely a nonvanishing minor at size `d` witnesses that no shorter
recurrence holds, so the least order is read off the determinants.

## Main results

* `Shields.hankel` — the matrix
* `Shields.nullVec`, `Shields.recurrence_of_annihilates`, `Shields.sum_nullVec`
* `Shields.hankel_det_eq_zero` — **a recurrence of order `d` kills every larger minor**
* `Shields.hankel_det_ne_zero_at_order` — and a nonvanishing minor bounds the order below

## Implementation notes

The recurrence is taken as the hypothesis that a nonzero coefficient vector annihilates the
windows, rather than as a statement about a generating function, so that nothing is assumed about
convergence or about the ring beyond commutativity.

## References

* A. Hankel, *Über eine besondere Classe der symmetrischen Determinanten*, 1861.
* G. Heinig and K. Rost, *Algebraic methods for Toeplitz-like matrices and operators*, 1984.

## Tags

hankel matrix, linear recurrence, determinant, moment matrix
-/

namespace Shields

open Polynomial Matrix BigOperators

variable {R : Type*} [CommRing R]

/-- The Hankel (moment) matrix `[ϖ_{s+t}]` of a sequence. -/
def hankel (μ : ℕ → R) (k : ℕ) : Matrix (Fin k) (Fin k) R :=
  Matrix.of fun i j => μ (i.val + j.val)

/-- Coefficients of the recurrence, with `1` in slot `d`: the null vector of the moment
matrix once the recurrence holds. -/
noncomputable def nullVec (c : ℕ → R) (d : ℕ) : ℕ → R :=
  fun j => if j = d then 1 else if j < d then -c j else 0

/-- The paper's step "`L` annihilates the ideal `(P₁)`, so it factors through
`R[z]/(P₁)`", in the form the Hankel argument consumes: a functional killing every
multiple of the monic `P₁ = X^d - Σ_{l<d} c_l X^l` has moments obeying that recurrence. -/
theorem recurrence_of_annihilates {L : Polynomial R →ₗ[R] R} {d : ℕ} {c : ℕ → R}
    (hann : ∀ q : Polynomial R,
      L ((X ^ d - ∑ l ∈ Finset.range d, C (c l) * X ^ l) * q) = 0) (s : ℕ) :
    L (X ^ (s + d)) = ∑ l ∈ Finset.range d, c l * L (X ^ (s + l)) := by
  have h := hann (X ^ s)
  rw [sub_mul, Finset.sum_mul] at h
  rw [map_sub, map_sum] at h
  have e1 : (X : Polynomial R) ^ d * X ^ s = X ^ (s + d) := by ring
  have e2 : ∀ l, (C (c l) * X ^ l : Polynomial R) * X ^ s = C (c l) * X ^ (s + l) := by
    intro l; ring
  rw [e1] at h
  simp_rw [e2] at h
  have e3 : ∀ l, L (C (c l) * X ^ (s + l)) = c l * L (X ^ (s + l)) := by
    intro l
    rw [← Polynomial.smul_eq_C_mul, map_smul, smul_eq_mul]
  simp_rw [e3] at h
  exact sub_eq_zero.mp h

/-- The null vector contracts the moment row to the recurrence's defect. -/
theorem sum_nullVec {μ : ℕ → R} {d : ℕ} {c : ℕ → R} {k : ℕ} (hk : d < k) (i : ℕ) :
    ∑ j ∈ Finset.range k, μ (i + j) * nullVec c d j
      = μ (i + d) - ∑ l ∈ Finset.range d, c l * μ (i + l) := by
  have hsub : Finset.range (d + 1) ⊆ Finset.range k := Finset.range_mono (by omega)
  have hzero : ∀ j ∈ Finset.range k, j ∉ Finset.range (d + 1) →
      μ (i + j) * nullVec c d j = 0 := by
    intro j _ hj
    rw [Finset.mem_range, Nat.lt_succ_iff, not_le] at hj
    simp [nullVec, Nat.ne_of_gt hj, Nat.not_lt_of_gt hj]
  rw [← Finset.sum_subset hsub hzero, Finset.sum_range_succ]
  have hlt : ∀ j ∈ Finset.range d, μ (i + j) * nullVec c d j = -(c j * μ (i + j)) := by
    intro j hj
    rw [Finset.mem_range] at hj
    simp [nullVec, Nat.ne_of_lt hj, hj]
    ring
  rw [Finset.sum_congr rfl hlt, Finset.sum_neg_distrib]
  simp [nullVec]
  ring

/-- Moments obeying an order-`d` linear
recurrence have every Hankel determinant of size `k > d` equal to zero.  With
`d = r_eff` this is "`r_eff < k` forces `J_k ≡ 0`", and no property of the
multiplicities enters. -/
theorem hankel_det_eq_zero [IsDomain R] {μ : ℕ → R} {d : ℕ} {c : ℕ → R}
    (hrec : ∀ s, μ (s + d) = ∑ l ∈ Finset.range d, c l * μ (s + l))
    {k : ℕ} (hk : d < k) : (hankel μ k).det = 0 := by
  refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨fun j => nullVec c d j.val, ?_, ?_⟩
  · intro h
    have := congrFun h ⟨d, hk⟩
    simp [nullVec] at this
  · funext i
    change (fun j : Fin k => μ (i.val + j.val)) ⬝ᵥ (fun j : Fin k => nullVec c d j.val) = 0
    rw [dotProduct]
    rw [Fin.sum_univ_eq_sum_range (fun j => μ (i.val + j) * nullVec c d j) k,
        sum_nullVec hk i.val, hrec i.val, sub_self]

/-- The bound `k > d` is sharp, so `hankel_det_eq_zero` is not vacuous: at `k = d` the
determinant can be nonzero.  Witness `d = 1`, `μ ≡ 1`, `c 0 = 1`: the recurrence holds,
the `1×1` determinant is `1`, and the `2×2` one is `0`. -/
theorem hankel_det_ne_zero_at_order :
    ∃ (μ : ℕ → ℤ) (c : ℕ → ℤ),
      (∀ s, μ (s + 1) = ∑ l ∈ Finset.range 1, c l * μ (s + l)) ∧
      (hankel μ 1).det ≠ 0 ∧ (hankel μ 2).det = 0 := by
  refine ⟨fun _ => 1, fun _ => 1, by intro s; simp, ?_, ?_⟩
  · simp [hankel]
  · simp [hankel, Matrix.det_fin_two]

end Shields
