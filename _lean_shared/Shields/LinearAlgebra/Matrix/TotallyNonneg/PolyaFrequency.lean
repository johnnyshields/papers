/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Shields.LinearAlgebra.Matrix.ToeplitzLower

/-!
# The Toeplitz matrix of a finite Pólya-frequency symbol is totally nonnegative

A **finite Pólya-frequency symbol** is a product of linear factors with nonnegative roots,
`\prod_{y \in ys}(1 + y t)` with every `y \ge 0`.  Its lower-triangular Toeplitz matrix has every
increasing-selection minor nonnegative, at every order and every size.

The proof is the classical one and it is three moves.  The symbol factors, so its Toeplitz matrix
is a product of bidiagonal root factors (`Shields.toeplitzLower_rootProd`).  A bidiagonal root
factor with nonnegative subdiagonal is totally nonnegative, because each of its minors is either
`0` or a power of the subdiagonal entry (`Shields.minorsNonneg_rootFactor`).  And Cauchy--Binet
expands a minor of a product as a sum of products of minors, so nonnegativity propagates across
the product from the identity (`Shields.MinorsNonneg.mul`, `Shields.minorsNonneg_one`).

## Main results

* `Shields.MinorsNonneg.listProd`: nonnegative minors are closed under a list product.
* `Shields.minorsNonneg_rootProd`: the Toeplitz matrix of `\prod_{y \in ys}(1 + y t)`, every
  `y \ge 0`, has every increasing-selection minor nonnegative.

## Implementation notes

The list product form is the one the induction wants: `List.prod_cons` peels one factor and
`MinorsNonneg.mul` consumes it, so no size bookkeeping is needed and the base case is the
identity.  `Shields.minorsNonneg_rootProd` is stated on `Shields.rootProdCoeff`, the coefficient
sequence built by convolving one factor at a time, rather than on a `Polynomial`, so that the
statement holds at every truncation size `n` for one fixed sequence.

The converse -- that total nonnegativity of the Toeplitz matrix forces such a factorization -- is
not proved here; it needs the zero-localization half of the Aissen--Schoenberg--Whitney theorem.

## References

* M. Aissen, I. J. Schoenberg and A. M. Whitney, *On the generating functions of totally positive
  sequences I*, J. Analyze Math. **2** (1952), 93--103.
* A. Pinkus, *Totally Positive Matrices*, Cambridge Univ. Press, 2010, Ch. 4.

## Tags

polya frequency sequence, totally nonnegative, toeplitz matrix, cauchy binet, aissen schoenberg
whitney
-/

namespace Shields

variable {R : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R]

/-- Nonnegative minors are closed under a list product: Cauchy--Binet at each step, with the
identity as base case. -/
theorem MinorsNonneg.listProd {r n : ℕ} {L : List (Matrix (Fin n) (Fin n) R)}
    (h : ∀ M ∈ L, MinorsNonneg r M) : MinorsNonneg r L.prod := by
  induction L with
  | nil => simpa using minorsNonneg_one (R := R) r n
  | cons M Ms ih =>
      rw [List.prod_cons]
      exact (h M (List.mem_cons_self ..)).mul (ih fun N hN => h N (List.mem_cons_of_mem M hN))

/-- **The Toeplitz matrix of a finite Pólya-frequency symbol is totally nonnegative.**  For
`\prod_{y \in ys}(1 + y t)` with every `y \ge 0`, every `k \times k` increasing-selection minor of
the `n \times n` lower-triangular Toeplitz matrix of the coefficient sequence is nonnegative.

The matrix is the product of the bidiagonal root factors, each of which is totally nonnegative,
and Cauchy--Binet carries the property across the product. -/
theorem minorsNonneg_rootProd (ys : List R) (hy : ∀ y ∈ ys, 0 ≤ y) (k n : ℕ) :
    MinorsNonneg k (toeplitzLower (rootProdCoeff ys) n) := by
  rw [toeplitzLower_rootProd]
  refine MinorsNonneg.listProd fun M hM => ?_
  obtain ⟨y, hy', rfl⟩ := List.mem_map.mp hM
  exact minorsNonneg_rootFactor (hy y hy') k n

end Shields
