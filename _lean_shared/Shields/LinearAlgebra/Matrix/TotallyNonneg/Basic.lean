/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Shields.LinearAlgebra.Matrix.CauchyBinet
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Matrices all of whose minors are nonnegative

The predicate `MinorsNonneg` and its first inhabitant, the bidiagonal Toeplitz matrix of a single
root factor `1 + x t` with `x ≥ 0`.

## Main results

* `Shields.MinorsNonneg`: every `r × r` minor on increasing row and column selections is `≥ 0`.
* `Shields.MinorsNonneg.mul`: the predicate is closed under products, by Cauchy--Binet.
* `Shields.minorsNonneg_one`: the identity satisfies it.
* `Shields.minorsNonneg_rootFactor`: the bidiagonal matrix of `1 + x t`, `x ≥ 0`, satisfies it at
  every order -- its minors are each `0` or a power of `x`.

## Implementation notes

`MinorsNonneg` is stated on strictly monotone selections `Fin r → Fin n` rather than on `Finset`s,
matching `Shields.det_mul_eq_sum_increasing`, which is what makes closure under products immediate.

Mathlib has no total-positivity class at the pinned revision. One is in flight as
`feat(LinearAlgebra): totally nonnegative matrices` (#41813), defining the class and a basic API but
none of the results here. `Matrix.TotallyUnimodular` is a different notion -- entries in `{0, ±1}`.

## Tags

total positivity, totally nonnegative, minor, bidiagonal, Toeplitz
-/

namespace Shields

variable {R : Type*} [CommRing R]

/-- The Toeplitz matrix of the single factor `1 + x t`: `1` on the diagonal, `x`
directly below it, `0` elsewhere.  This is the bidiagonal building block a finite
Laguerre–Pólya symbol factors into. -/
def rootFactor (x : R) (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => if (i : ℕ) = j then 1 else if (i : ℕ) = j + 1 then x else 0

@[simp] theorem rootFactor_diag (x : R) (n : ℕ) (i : Fin n) :
    rootFactor x n i i = 1 := by simp [rootFactor]

/-- The determinant of the full bidiagonal block is `1`: it is lower triangular
with unit diagonal. -/
theorem det_rootFactor (x : R) (n : ℕ) : (rootFactor x n).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · simp
  · intro i j hij
    have hij' : (i : ℕ) < (j : ℕ) := hij
    have h1 : ¬ (i : ℕ) = (j : ℕ) := by omega
    have h2 : ¬ (i : ℕ) = (j : ℕ) + 1 := by omega
    simp [rootFactor, h1, h2]

section Ordered

variable [PartialOrder R] [IsOrderedRing R]

/-- **The `2×2` minors of a root factor are nonnegative** when `x ≥ 0`.  Taking
rows `i₀ < i₁` and columns `j₀ < j₁`, the determinant is `1`, `x`, `−x·0`, or `0`
by cases on how the two bands meet — never negative.

Stated on an explicit `2×2` selection so the case analysis is finite; this is the
shape Cauchy–Binet consumes. -/
theorem rootFactor_two_minor_nonneg {x : R} (hx : 0 ≤ x) (n : ℕ)
    (i₀ i₁ j₀ j₁ : Fin n) (hi : (i₀ : ℕ) < i₁) (hj : (j₀ : ℕ) < j₁) :
    0 ≤ rootFactor x n i₀ j₀ * rootFactor x n i₁ j₁
      - rootFactor x n i₀ j₁ * rootFactor x n i₁ j₀ := by
  -- The anti-diagonal product vanishes: `i₀ < i₁` and `j₀ < j₁` cannot both put
  -- `(i₀, j₁)` and `(i₁, j₀)` on a band.
  have hz : rootFactor x n i₀ j₁ * rootFactor x n i₁ j₀ = 0 := by
    rcases eq_or_ne (i₁ : ℕ) (j₀ : ℕ) with h | h
    · -- then `i₀ < j₀`, so `(i₀, j₁)` is strictly above both bands
      have h1 : ¬ (i₀ : ℕ) = (j₁ : ℕ) := by omega
      have h2 : ¬ (i₀ : ℕ) = (j₁ : ℕ) + 1 := by omega
      simp [rootFactor, h1, h2]
    · rcases eq_or_ne (i₁ : ℕ) ((j₀ : ℕ) + 1) with h' | h'
      · have h1 : ¬ (i₀ : ℕ) = (j₁ : ℕ) := by omega
        have h2 : ¬ (i₀ : ℕ) = (j₁ : ℕ) + 1 := by omega
        simp [rootFactor, h1, h2]
      · simp [rootFactor, h, h']
  rw [hz, sub_zero]
  -- Each surviving entry is `1`, `x` or `0`, all nonnegative.
  have hent : ∀ a b : Fin n, 0 ≤ rootFactor x n a b := by
    intro a b
    by_cases h1 : (a : ℕ) = b
    · simp [rootFactor, h1]
    · by_cases h2 : (a : ℕ) = (b : ℕ) + 1
      · simp [rootFactor, h2, hx]
      · simp [rootFactor, h1, h2]
  exact mul_nonneg (hent i₀ j₀) (hent i₁ j₁)

/-- Every entry of a root factor is nonnegative for `x ≥ 0` — the `1×1` minors. -/
theorem rootFactor_entry_nonneg {x : R} (hx : 0 ≤ x) (n : ℕ) (i j : Fin n) :
    0 ≤ rootFactor x n i j := by
  by_cases h1 : (i : ℕ) = j
  · simp [rootFactor, h1]
  · by_cases h2 : (i : ℕ) = (j : ℕ) + 1
    · simp [rootFactor, h2, hx]
    · simp [rootFactor, h1, h2]

/-- A matrix all of whose `k×k` increasing-selection minors are nonnegative.
This is the total-nonnegativity property Cauchy–Binet propagates. -/
def MinorsNonneg (k : ℕ) {n : ℕ} (A : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ f g : Fin k → Fin n, f ∈ increasingSelections k n → g ∈ increasingSelections k n →
    0 ≤ (A.submatrix f g).det

/-- **Cauchy–Binet propagates nonnegative minors across a product.**  This is the
closure property that makes total nonnegativity survive the factorization of a
finite Pólya-frequency symbol into root factors. -/
theorem MinorsNonneg.mul {k n : ℕ} {A B : Matrix (Fin n) (Fin n) R}
    (hA : MinorsNonneg k A) (hB : MinorsNonneg k B) : MinorsNonneg k (A * B) := by
  intro f g hf hg
  have hsub : (A * B).submatrix f g = A.submatrix f id * B.submatrix id g := by
    ext a b
    simp [Matrix.mul_apply, Matrix.submatrix_apply]
  rw [hsub, det_mul_eq_sum_increasing]
  refine Finset.sum_nonneg fun h hh => ?_
  refine mul_nonneg ?_ ?_
  · have : (A.submatrix f id).submatrix id h = A.submatrix f h := rfl
    rw [this]; exact hA f h hf hh
  · have : (B.submatrix id g).submatrix h id = B.submatrix h g := rfl
    rw [this]; exact hB h g hh hg

omit [IsOrderedRing R] in
/-- **`MinorsNonneg` is insensitive to transposition.**  A minor of `Aᵀ` on rows `f` and
columns `g` is the transpose of the minor of `A` on rows `g` and columns `f`, so it has the
same determinant, and the predicate quantifies over both index families. -/
theorem MinorsNonneg.transpose {k n : ℕ} {A : Matrix (Fin n) (Fin n) R}
    (h : MinorsNonneg k A) : MinorsNonneg k A.transpose := by
  intro f g hf hg
  rw [show A.transpose.submatrix f g = (A.submatrix g f).transpose by
      rw [Matrix.transpose_submatrix], Matrix.det_transpose]
  exact h g f hg hf

/-- Two strictly monotone maps `Fin k → Fin n` with the same image are equal: each
is the unique increasing enumeration of that image. -/
theorem strictMono_eq_of_image_eq {k n : ℕ} {f g : Fin k → Fin n}
    (hf : StrictMono f) (hg : StrictMono g)
    (h : Finset.univ.image f = Finset.univ.image g) : f = g := by
  refine Set.range_injOn_strictMono hf hg ?_
  have hcoe : ∀ p : Fin k → Fin n, Set.range p = ↑(Finset.univ.image p) := fun p => by
    simp [Finset.coe_image, Set.image_univ]
  rw [hcoe f, hcoe g, h]

/-- **The identity has nonnegative minors.**  An increasing-selection minor of `1`
is `1` when the two selections agree and `0` otherwise — never `-1`, because two
strictly monotone selections with the same image coincide.  This is the base case
of the induction over root factors. -/
theorem minorsNonneg_one (k n : ℕ) :
    MinorsNonneg k (1 : Matrix (Fin n) (Fin n) R) := by
  intro f g hf hg
  rw [mem_increasingSelections] at hf hg
  by_cases h : f = g
  · subst h
    rw [Matrix.submatrix_one f hf.injective, Matrix.det_one]
    exact zero_le_one
  · -- The images differ, so some row of the selection is entirely zero.
    have himg : Finset.univ.image f ≠ Finset.univ.image g := fun hc =>
      h (strictMono_eq_of_image_eq hf hg hc)
    obtain ⟨a, ha⟩ : ∃ a : Fin k, ∀ b : Fin k, f a ≠ g b := by
      by_contra hc
      push Not at hc
      refine himg (Finset.eq_of_subset_of_card_le ?_ ?_)
      · intro y hy
        obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hy
        obtain ⟨b, hb⟩ := hc a
        exact hb ▸ Finset.mem_image_of_mem g (Finset.mem_univ b)
      · rw [Finset.card_image_of_injective _ hf.injective,
          Finset.card_image_of_injective _ hg.injective]
    rw [Matrix.det_eq_zero_of_row_eq_zero a fun b => by
      simp [ha b]]

/-- A permutation of `Fin k` with no inversions is the identity: it is strictly
monotone, and a strictly monotone self-map of `Fin k` has the same image as the
identity, so `strictMono_eq_of_image_eq` applies. -/
theorem perm_eq_one_of_strictMono {k : ℕ} {σ : Equiv.Perm (Fin k)}
    (h : StrictMono σ) : σ = 1 := by
  have hrange : Set.range (σ : Fin k → Fin k) = Set.range (id : Fin k → Fin k) := by
    simp [Set.range_id, Set.range_eq_univ.mpr σ.surjective]
  exact Equiv.ext fun a => congrFun (Set.range_injOn_strictMono h strictMono_id hrange) a

/-- **Every increasing-selection minor of a root factor is nonnegative.**  Only the
identity permutation contributes: if `σ` had an inversion `a < b`, `σ a > σ b`,
then the two band conditions `f(σ a) − g a, f(σ b) − g b ∈ {0,1}` would force
`g a ≥ g b`, contradicting `a < b`.  The determinant is therefore the product of
the diagonal entries, each `1`, `x` or `0`. -/
theorem rootFactor_minor_nonneg {x : R} (hx : 0 ≤ x) {k n : ℕ} (f g : Fin k → Fin n)
    (hf : StrictMono f) (hg : StrictMono g) :
    0 ≤ ((rootFactor x n).submatrix f g).det := by
  have hdiag : ((rootFactor x n).submatrix f g).det
      = ∏ a, rootFactor x n (f a) (g a) := by
    rw [Matrix.det_apply]
    rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin k))]
    · simp
    · intro σ _ hσ
      -- `σ ≠ 1` has an inversion; the band conditions then contradict it.
      have hinv : ∃ a b, a < b ∧ σ b < σ a := by
        by_contra hc
        push Not at hc
        exact hσ (perm_eq_one_of_strictMono (fun a b hab => lt_of_le_of_ne (hc a b hab)
          (fun he => absurd (σ.injective he) (ne_of_lt hab))))
      obtain ⟨a, b, hab, hba⟩ := hinv
      -- A nonzero entry forces a band condition.
      have hband : ∀ i : Fin k, ((rootFactor x n).submatrix f g) (σ i) i ≠ 0 →
          (f (σ i) : ℕ) = (g i : ℕ) ∨ (f (σ i) : ℕ) = (g i : ℕ) + 1 := by
        intro i hi
        by_contra hc
        push Not at hc
        exact hi (by simp [Matrix.submatrix_apply, rootFactor, hc.1, hc.2])
      -- One of the two inverted factors must vanish: `σ b < σ a` raises `f` while
      -- `a < b` raises `g`, and the bands cannot accommodate both.
      by_cases ha : ((rootFactor x n).submatrix f g) (σ a) a = 0
      · exact smul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ a) ha)
      · by_cases hb : ((rootFactor x n).submatrix f g) (σ b) b = 0
        · exact smul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ b) hb)
        · exfalso
          have hfba : (f (σ b) : ℕ) < (f (σ a) : ℕ) := hf hba
          have hgab : (g a : ℕ) < (g b : ℕ) := hg hab
          rcases hband a ha with h1 | h1 <;> rcases hband b hb with h2 | h2 <;> omega
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hdiag]
  exact Finset.prod_nonneg fun a _ => rootFactor_entry_nonneg hx n (f a) (g a)

/-- A root factor is totally nonnegative in the sense `MinorsNonneg` uses. -/
theorem minorsNonneg_rootFactor {x : R} (hx : 0 ≤ x) (k n : ℕ) :
    MinorsNonneg k (rootFactor x n) := by
  intro f g hf hg
  rw [mem_increasingSelections] at hf hg
  exact rootFactor_minor_nonneg hx f g hf hg

end Ordered

end Shields
