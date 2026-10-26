/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
-- TODO-COPIED: skew-jacobi-negative/lean/SkewJacobiNegative/StrictTriangularPaths.lean

-- TODO-COPIED:
--   skew-cofactor-independence/lean/SkewCofactorIndependence/StrictTriangularPaths.lean
import SkewJacobiNegative.RestorationPaths
import SkewJacobiNegative.CompleteAlgebra
import SkewJacobiNegative.PositiveEntries

/-!
# Strict common-beta chains

Explicit finite ordered paths for `prop:path-expansion` and `eq:path-entry` of
`shields-2026-skew-cofactor-independence.tex`.  An index is a nested tuple of
common-beta positions, one for each intermediate vertex.  A separate strict
chain predicate discards repetitions and all nondecreasing steps.  Equality
has value zero in the auxiliary matrix, even though `complete 0 = 1`.

These are matrix and path producers.  Sorting restored beta lists, their
Jacobi--Trudi identification, and connectedness are separate coordinate results.
-/

namespace SkewJacobiNegative
namespace StrictTriangularPaths

open scoped BigOperators Polynomial
open Matrix

variable {R : Type*} [CommRing R] {k m : ℕ}


/-- Nested tuples give an explicit finite indexing type for paths of every length. -/
def ChainIndex (m : ℕ) : ℕ → Type
  | 0 => Unit
  | r + 1 => Fin m × ChainIndex m r

instance chainIndexFintype (m r : ℕ) : Fintype (ChainIndex m r) := by
  induction r with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ r ih =>
      letI : Fintype (ChainIndex m r) := ih
      exact inferInstanceAs (Fintype (Fin m × ChainIndex m r))

noncomputable instance chainIndexDecidableEq (m r : ℕ) : DecidableEq (ChainIndex m r) :=
  Classical.decEq _

/-- Strict decreasing chains `a > z₁ > ⋯ > zᵣ > b`. -/
def IsStrictChain (Z : Fin m → ℤ) (a b : ℤ) :
    (r : ℕ) → ChainIndex m r → Prop
  | 0, _ => b < a
  | r + 1, p => Z p.1 < a ∧ IsStrictChain Z (Z p.1) b r p.2

noncomputable instance strictChainDecidable (Z : Fin m → ℤ) (a b : ℤ)
    (r : ℕ) (p : ChainIndex m r) : Decidable (IsStrictChain Z a b r p) :=
  Classical.propDecidable _

/-- The product of actual complete-gap values, without any path guard. -/
def chainProduct (h : ℤ → R) (Z : Fin m → ℤ) (a b : ℤ) :
    (r : ℕ) → ChainIndex m r → R
  | 0, _ => h (a - b)
  | r + 1, p => h (a - Z p.1) * chainProduct h Z (Z p.1) b r p.2

/-- A path weight using the positive-entry convention at every edge. -/
noncomputable def chainWeight (h : ℤ → R) (Z : Fin m → ℤ) (a b : ℤ) :
    (r : ℕ) → ChainIndex m r → R
  | 0, _ => positiveGap h a b
  | r + 1, p => positiveGap h a (Z p.1) * chainWeight h Z (Z p.1) b r p.2

/-- Every surviving term is an actual strict chain, not a heuristic walk. -/
theorem chainWeight_eq_guard (h : ℤ → R) (Z : Fin m → ℤ) (a b : ℤ)
    (r : ℕ) (p : ChainIndex m r) :
    chainWeight h Z a b r p =
      if IsStrictChain Z a b r p then chainProduct h Z a b r p else 0 := by
  classical
  induction r generalizing a with
  | zero =>
      by_cases hab : b < a <;>
        simp [chainWeight, chainProduct, IsStrictChain, positiveGap, hab]
  | succ r ih =>
      rcases p with ⟨z, p⟩
      by_cases hz : Z z < a
      · by_cases hp : IsStrictChain Z (Z z) b r p
        · simp [chainWeight, chainProduct, IsStrictChain, positiveGap, hz, hp, ih]
        · simp [chainWeight, IsStrictChain, positiveGap, hz, hp, ih]
      · simp [chainWeight, IsStrictChain, positiveGap, hz]

/-- Sum over all finite tuples, with invalid chains assigned weight zero. -/
noncomputable def orderedPathSum (h : ℤ → R) (Z : Fin m → ℤ)
    (r : ℕ) (a b : ℤ) : R :=
  ∑ p : ChainIndex m r, chainWeight h Z a b r p

/-- A ring homomorphism transports the finite path products and sums. -/
theorem chainWeight_map {S : Type*} [CommRing S] (f : R →+* S)
    (h : ℤ → R) (Z : Fin m → ℤ) (a b : ℤ)
    (r : ℕ) (p : ChainIndex m r) :
    chainWeight (fun d => f (h d)) Z a b r p = f (chainWeight h Z a b r p) := by
  induction r generalizing a with
  | zero => exact positiveGap_map f h a b
  | succ r ih =>
      rcases p with ⟨z, p⟩
      simp only [chainWeight, positiveGap_map, ih, map_mul]

theorem orderedPathSum_map {S : Type*} [CommRing S] (f : R →+* S)
    (h : ℤ → R) (Z : Fin m → ℤ) (r : ℕ) (a b : ℤ) :
    orderedPathSum (fun d => f (h d)) Z r a b = f (orderedPathSum h Z r a b) := by
  simp only [orderedPathSum, map_sum, chainWeight_map]

/-- The same sum indexed literally by the strict chains in `eq:path-entry`. -/
theorem orderedPathSum_eq_strict_sum (h : ℤ → R) (Z : Fin m → ℤ)
    (r : ℕ) (a b : ℤ) :
    orderedPathSum h Z r a b =
      ∑ p ∈ Finset.univ.filter (IsStrictChain Z a b r), chainProduct h Z a b r p := by
  classical
  simp only [orderedPathSum, chainWeight_eq_guard, Finset.sum_filter]

@[simp]
theorem orderedPathSum_zero (h : ℤ → R) (Z : Fin m → ℤ) (a b : ℤ) :
    orderedPathSum h Z 0 a b = positiveGap h a b := by
  change (∑ _p : Unit, positiveGap h a b) = positiveGap h a b
  simp only [Fintype.sum_unique]

/-- Removing the first intermediate vertex partitions the finite strict-chain sum. -/
theorem orderedPathSum_succ (h : ℤ → R) (Z : Fin m → ℤ)
    (r : ℕ) (a b : ℤ) :
    orderedPathSum h Z (r + 1) a b =
      ∑ z : Fin m, positiveGap h a (Z z) * orderedPathSum h Z r (Z z) b := by
  change (∑ p : Fin m × ChainIndex m r,
      positiveGap h a (Z p.1) * chainWeight h Z (Z p.1) b r p.2) =
    ∑ z : Fin m, positiveGap h a (Z z) *
      ∑ p : ChainIndex m r, chainWeight h Z (Z z) b r p
  rw [Fintype.sum_prod_type]
  simp only [Finset.mul_sum]

/-- Strictly decreasing common-beta coordinates produce a strictly upper triangular block. -/
theorem positiveMatrix_strictUpper (h : ℤ → R) (Z : Fin m → ℤ)
    (hZ : StrictAnti Z) : RestorationPaths.StrictUpper (positiveMatrix h Z Z) := by
  intro i j hij
  apply positiveGap_of_le h
  exact hZ.antitone (le_of_not_gt hij)

/-- Nilpotence is produced from the common-beta order rather than assumed. -/
theorem common_beta_nilpotent (h : ℤ → R) (Z : Fin m → ℤ)
    (hZ : StrictAnti Z) : (positiveMatrix h Z Z) ^ m = 0 :=
  RestorationPaths.strict_upper_pow_eq_zero _ (positiveMatrix_strictUpper h Z hZ)

/-- Powers followed by the terminal gap enumerate exactly the finite strict chains. -/
theorem power_mul_terminal_entry {β : Type*}
    (h : ℤ → R) (Z : Fin m → ℤ) (B : β → ℤ) (r : ℕ)
    (i : Fin m) (j : β) :
    ((positiveMatrix h Z Z) ^ r * positiveMatrix h Z B) i j =
      orderedPathSum h Z r (Z i) (B j) := by
  induction r generalizing i with
  | zero => simp [positiveMatrix]
  | succ r ih =>
      rw [pow_succ', Matrix.mul_assoc, Matrix.mul_apply, orderedPathSum_succ]
      apply Finset.sum_congr rfl
      intro z hz
      rw [ih]
      rfl

/-- The length-zero common-block walk is the matrix identity. -/
theorem strict_power_zero_entry (h : ℤ → R) (Z : Fin m → ℤ) (i j : Fin m) :
    ((positiveMatrix h Z Z) ^ 0) i j = if i = j then 1 else 0 := by
  simp [Matrix.one_apply]

/-- Entries of `T^(r+1)` are the sums over `r` intermediate common-beta vertices. -/
theorem strict_power_entry (h : ℤ → R) (Z : Fin m → ℤ) (r : ℕ)
    (i j : Fin m) :
    ((positiveMatrix h Z Z) ^ (r + 1)) i j =
      ∑ p ∈ Finset.univ.filter (IsStrictChain Z (Z i) (Z j) r),
        chainProduct h Z (Z i) (Z j) r p := by
  classical
  rw [pow_succ, power_mul_terminal_entry, orderedPathSum_eq_strict_sum]

/-- Entry formula for `P T^r Q`, with exactly `r+1` intermediate vertices. -/
theorem exterior_power_entry {α β : Type*}
    (h : ℤ → R) (A : α → ℤ) (Z : Fin m → ℤ) (B : β → ℤ)
    (r : ℕ) (i : α) (j : β) :
    (positiveMatrix h A Z * (positiveMatrix h Z Z) ^ r * positiveMatrix h Z B) i j =
      orderedPathSum h Z (r + 1) (A i) (B j) := by
  rw [Matrix.mul_assoc, Matrix.mul_apply, orderedPathSum_succ]
  apply Finset.sum_congr rfl
  intro z hz
  rw [power_mul_terminal_entry]
  rfl

/-- The finite reduced-entry formula, including its length-zero positive gap. -/
theorem reduced_entry (h : ℤ → R) (t : R) (A B : Fin k → ℤ)
    (Z : Fin m → ℤ) (i j : Fin k) :
    RestorationPaths.reduced t (positiveMatrix h A B) (positiveMatrix h A Z)
      (positiveMatrix h Z B) (positiveMatrix h Z Z) i j =
      positiveGap h (A i) (B j) +
        ∑ r ∈ Finset.range m, (-t) ^ (r + 1) *
          orderedPathSum h Z (r + 1) (A i) (B j) := by
  rw [RestorationPaths.reduced_eq_sum]
  rw [Matrix.add_apply, Matrix.sum_apply]
  change positiveGap h (A i) (B j) +
      (∑ r ∈ Finset.range m, (-t) ^ (r + 1) *
        (positiveMatrix h A Z * (positiveMatrix h Z Z) ^ r *
          positiveMatrix h Z B) i j) = _
  simp only [exterior_power_entry]

/-- Literal strict-chain version of the terminating ordered-path formula (`eq:path-entry`). -/
theorem reduced_entry_strict_paths (h : ℤ → R) (t : R) (A B : Fin k → ℤ)
    (Z : Fin m → ℤ) (i j : Fin k) :
    RestorationPaths.reduced t (positiveMatrix h A B) (positiveMatrix h A Z)
      (positiveMatrix h Z B) (positiveMatrix h Z Z) i j =
      positiveGap h (A i) (B j) +
        ∑ r ∈ Finset.range m, (-t) ^ (r + 1) *
          ∑ p ∈ Finset.univ.filter (IsStrictChain Z (A i) (B j) (r + 1)),
            chainProduct h Z (A i) (B j) (r + 1) p := by
  classical
  rw [reduced_entry]
  simp only [orderedPathSum_eq_strict_sum]

/-- Polynomial marking uses the same path products, embedded as constant coefficients. -/
theorem polynomial_reduced_entry (h : ℤ → R) (A B : Fin k → ℤ)
    (Z : Fin m → ℤ) (i j : Fin k) :
    RestorationPaths.reduced (Polynomial.X : R[X])
      ((positiveMatrix h A B).map Polynomial.C)
      ((positiveMatrix h A Z).map Polynomial.C)
      ((positiveMatrix h Z B).map Polynomial.C)
      ((positiveMatrix h Z Z).map Polynomial.C) i j =
      Polynomial.C (positiveGap h (A i) (B j)) +
        ∑ r ∈ Finset.range m, (-(Polynomial.X : R[X])) ^ (r + 1) *
          Polynomial.C (orderedPathSum h Z (r + 1) (A i) (B j)) := by
  rw [← positiveMatrix_map Polynomial.C h A B,
    ← positiveMatrix_map Polynomial.C h A Z,
    ← positiveMatrix_map Polynomial.C h Z B,
    ← positiveMatrix_map Polynomial.C h Z Z, reduced_entry]
  simp only [positiveGap_map, orderedPathSum_map]

/-- Paths beyond the common-beta cardinality vanish, so extending the series adds nothing. -/
theorem orderedPathSum_eq_zero_of_card_le (h : ℤ → R)
    (A B : Fin k → ℤ) (Z : Fin m → ℤ) (hZ : StrictAnti Z)
    (r : ℕ) (hr : m ≤ r) (i j : Fin k) :
    orderedPathSum h Z (r + 1) (A i) (B j) = 0 := by
  rw [← exterior_power_entry h A Z B r i j]
  have hpow : (positiveMatrix h Z Z) ^ r = 0 := by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hr
    rw [pow_add, common_beta_nilpotent h Z hZ, Matrix.zero_mul]
  rw [hpow, Matrix.mul_zero, Matrix.zero_mul]
  rfl

/-- The complete algebra really uses a positive generator at every permitted edge. -/
theorem positiveGap_complete_generator {a b : ℤ} (hab : b < a) :
    positiveGap complete a b =
      MvPolynomial.X ⟨(a - b).toNat, by omega⟩ := by
  rw [positiveGap_of_lt complete hab, complete_of_pos (by omega)]

/-- The polynomial marking block and the first two coefficients use the actual common-beta sums. -/
theorem path_marking_first_coefficients (h : ℤ → R) (A B : Fin k → ℤ)
    (Z : Fin m → ℤ) (hZ : StrictAnti Z) :
    let L := positiveMatrix h A B
    let P := positiveMatrix h A Z
    let Q := positiveMatrix h Z B
    let T := positiveMatrix h Z Z
    let G := (Matrix.fromBlocks ((Polynomial.X : R[X]) • L.map Polynomial.C)
      ((Polynomial.X : R[X]) • P.map Polynomial.C)
      ((Polynomial.X : R[X]) • Q.map Polynomial.C)
      ((1 : Matrix (Fin m) (Fin m) R[X]) +
        (Polynomial.X : R[X]) • T.map Polynomial.C)).det
    G.coeff k = L.det ∧
      G.coeff (k + 1) = -∑ z : Fin m, ∑ j : Fin k, ∑ i : Fin k,
        L.adjugate j i * positiveGap h (A i) (Z z) * positiveGap h (Z z) (B j) := by
  simpa only [positiveMatrix, Matrix.of_apply] using
    RestorationPaths.marked_block_first_coefficients
      (positiveMatrix h A B) (positiveMatrix h A Z) (positiveMatrix h Z B)
      (positiveMatrix h Z Z) (positiveMatrix_strictUpper h Z hZ)

/-- The single-insertion contraction is an actual signed-minor contraction. -/
theorem path_marking_first_coefficients_cofactors (h : ℤ → R)
    (A B : Fin (k + 1) → ℤ) (Z : Fin m → ℤ) (hZ : StrictAnti Z) :
    let L := positiveMatrix h A B
    let P := positiveMatrix h A Z
    let Q := positiveMatrix h Z B
    let T := positiveMatrix h Z Z
    let G := (Matrix.fromBlocks ((Polynomial.X : R[X]) • L.map Polynomial.C)
      ((Polynomial.X : R[X]) • P.map Polynomial.C)
      ((Polynomial.X : R[X]) • Q.map Polynomial.C)
      ((1 : Matrix (Fin m) (Fin m) R[X]) +
        (Polynomial.X : R[X]) • T.map Polynomial.C)).det
    G.coeff (k + 1) = L.det ∧
      G.coeff (k + 2) = -∑ z : Fin m, ∑ j : Fin (k + 1), ∑ i : Fin (k + 1),
        ((-1) ^ (i.val + j.val) * (L.submatrix i.succAbove j.succAbove).det) *
          positiveGap h (A i) (Z z) * positiveGap h (Z z) (B j) := by
  simpa only [RestorationPaths.adjugate_cofactor, Nat.add_assoc] using
    path_marking_first_coefficients h A B Z hZ

end StrictTriangularPaths
end SkewJacobiNegative
