/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fin.Tuple.Sort

/-!
# The Cauchy--Binet formula and the discrete Andréief identity

Two determinant expansions over the `k`-element column selections of a rectangular matrix.

## Main results

* `Shields.increasingSelections_nonempty`: the increasing selections of `r` out of `n` are
  nonempty when `r ≤ n`.
* `Shields.det_mul_eq_sum_increasing`: **Cauchy--Binet**, `det (A * B) = ∑_S det A_{•,S} * det
  B_{S,•}`, the sum over strictly monotone `S : Fin k → Fin n`.
* `Shields.det_gram_eq_sum_increasing`: the **Andréief** (Gram--Heine) expansion of the `k × k`
  Gram determinant of a bilinear pairing given by a finite sum.
* `Shields.factorial_mul_det_gram`: the `k!`-symmetrized form, the discrete counterpart of the
  `1 / k!` in front of a `k`-fold contour integral.

## Implementation notes

**`import Mathlib` is retained deliberately, and the specific list beneath it is exact.** This
file builds against those modules alone.  What the blanket import still carries is the transitive
Mathlib that *consumers* of this file rely on: dropping it here leaves the shared tree green and
breaks a paper that imports it.  Removing it therefore belongs to a pass that sweeps every
consuming tree's imports in the same change, and a Mathlib PR would carry the specific list only.

A `k`-element selection is carried as a strictly monotone map `Fin k → Fin n` rather than as a
`Finset (Fin n)` of cardinality `k`. The two are in bijection, and the map form keeps every
statement free of dependent cardinality proofs. No hypothesis `k ≤ n` is needed: for `k > n` there
is no strictly monotone map, the sum is empty, and the identity records `det (A * B) = 0`.

Mathlib carries only the square case, `Matrix.det_mul`. The rectangular formula is in flight
upstream as `feat(LinearAlgebra/Matrix): the Cauchy-Binet formula` (#40473), which states it over
`Finset` selections rather than monotone maps.

## Tags

determinant, Cauchy-Binet, Andreief, Gram matrix, minor
-/

open scoped BigOperators
open scoped Matrix

namespace Shields

/-! ### Index selections

`increasingSelections k n` enumerates the `k`-element subsets of `Fin n` in
increasing order; `injectiveSelections k n` is the intermediate set on which the
sorting bijection is built. -/

/-- The strictly monotone maps `Fin k → Fin n`, one for each `k`-element subset
of `Fin n` listed in increasing order. -/
def increasingSelections (k n : ℕ) : Finset (Fin k → Fin n) :=
  Finset.univ.filter (fun f => StrictMono f)

@[simp] theorem mem_increasingSelections {k n : ℕ} {f : Fin k → Fin n} :
    f ∈ increasingSelections k n ↔ StrictMono f := by
  simp [increasingSelections]

/-- There is at least one increasing selection of `r` out of `n` when `r ≤ n`. -/
theorem increasingSelections_nonempty {r n : ℕ} (h : r ≤ n) :
    Nonempty (increasingSelections r n) :=
  ⟨⟨fun i => ⟨(i : ℕ), lt_of_lt_of_le i.isLt h⟩,
    mem_increasingSelections.mpr fun _ _ hab => hab⟩⟩

/-- The injective maps `Fin k → Fin n`, i.e. the `k`-element subsets of `Fin n`
listed in every order. -/
private def injectiveSelections (k n : ℕ) : Finset (Fin k → Fin n) :=
  Finset.univ.filter (fun f => Function.Injective f)

@[simp] private theorem mem_injectiveSelections {k n : ℕ} {g : Fin k → Fin n} :
    g ∈ injectiveSelections k n ↔ Function.Injective g := by
  simp [injectiveSelections]

/-! ### Leibniz expansion of a rectangular product -/

variable {k n : ℕ} {R : Type*} [CommRing R]

/-- Leibniz expansion of `det (A * B)` over all index maps `Fin k → Fin n`. -/
private theorem det_mul_expand (A : Matrix (Fin k) (Fin n) R)
    (B : Matrix (Fin n) (Fin k) R) :
    (A * B).det
      = ∑ g : Fin k → Fin n, ∑ σ : Equiv.Perm (Fin k),
          ((Equiv.Perm.sign σ : ℤ) : R) * ∏ i, A (σ i) (g i) * B (g i) i := by
  simp only [Matrix.det_apply', Matrix.mul_apply, Finset.prod_univ_sum, Finset.mul_sum,
    Fintype.piFinset_univ]
  rw [Finset.sum_comm]

/-- At a fixed index map the permutation sum is a minor of `A` times the
corresponding product of entries of `B`. -/
private theorem sum_sign_prod_eq (A : Matrix (Fin k) (Fin n) R)
    (B : Matrix (Fin n) (Fin k) R) (g : Fin k → Fin n) :
    (∑ σ : Equiv.Perm (Fin k),
        ((Equiv.Perm.sign σ : ℤ) : R) * ∏ i, A (σ i) (g i) * B (g i) i)
      = (A.submatrix id g).det * ∏ a, B (g a) a := by
  rw [Matrix.det_apply', Finset.sum_mul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.prod_mul_distrib]
  simp only [Matrix.submatrix_apply, id_eq]
  ring

/-- `det (A * B)` as a sum over all index maps of a `k × k` minor of `A` against
a product of entries of `B`. -/
private theorem det_mul_eq_sum_over_maps (A : Matrix (Fin k) (Fin n) R)
    (B : Matrix (Fin n) (Fin k) R) :
    (A * B).det = ∑ g : Fin k → Fin n, (A.submatrix id g).det * ∏ a, B (g a) a := by
  rw [det_mul_expand A B]
  exact Finset.sum_congr rfl fun g _ => sum_sign_prod_eq A B g

/-- A repeated column kills the minor, so non-injective index maps contribute
nothing. -/
private theorem det_submatrix_eq_zero_of_not_injective (A : Matrix (Fin k) (Fin n) R)
    {g : Fin k → Fin n} (hg : ¬ Function.Injective g) :
    (A.submatrix id g).det = 0 := by
  obtain ⟨a, b, hab, hne⟩ := Function.not_injective_iff.mp hg
  exact Matrix.det_zero_of_column_eq hne fun i => by
    simp only [Matrix.submatrix_apply, id_eq, hab]

/-! ### Sorting an injective selection

Every injective `g : Fin k → Fin n` factors uniquely as `f ∘ τ` with `f`
strictly monotone and `τ` a permutation of `Fin k`; the factorization is
supplied by `Tuple.sort`. -/

/-- Composing with a permutation and then undoing it. -/
private theorem comp_perm_comp_inv (u : Fin k → Fin n) (σ : Equiv.Perm (Fin k)) :
    (u ∘ ⇑σ) ∘ ⇑σ⁻¹ = u := by
  rw [Function.comp_assoc, ← Equiv.Perm.coe_mul, mul_inv_cancel, Equiv.Perm.coe_one,
    Function.comp_id]

/-- The sorting permutation of `f ∘ τ`, for `f` strictly monotone, is `τ⁻¹`: undoing `τ` is what
puts `f ∘ τ` back in increasing order, and an injective tuple has only one such permutation. -/
private theorem sort_comp_perm {f : Fin k → Fin n} (hf : StrictMono f) (τ : Equiv.Perm (Fin k)) :
    Tuple.sort (f ∘ ⇑τ) = τ⁻¹ := by
  have h1 : (f ∘ ⇑τ) ∘ ⇑(Tuple.sort (f ∘ ⇑τ)) = f := by
    rw [Tuple.comp_perm_comp_sort_eq_comp_sort,
      Tuple.sort_eq_refl_iff_monotone.mpr hf.monotone, Equiv.coe_refl, Function.comp_id]
  exact Equiv.ext fun a => (hf.injective.comp τ.injective)
    (congrFun (h1.trans (comp_perm_comp_inv f τ).symm) a)

/-- Reindexing an injective selection as (increasing selection, permutation). -/
private theorem sum_injective_eq_sum_increasing_perm (Φ : (Fin k → Fin n) → R) :
    (∑ g ∈ injectiveSelections k n, Φ g)
      = ∑ p ∈ (increasingSelections k n) ×ˢ (Finset.univ : Finset (Equiv.Perm (Fin k))),
          Φ (p.1 ∘ ⇑p.2) := by
  -- `Tuple.sort g` is the permutation of `Fin k` that puts `g` in increasing order.
  refine Finset.sum_nbij'
    (fun g => (g ∘ ⇑(Tuple.sort g), (Tuple.sort g)⁻¹))
    (fun p => p.1 ∘ ⇑p.2) ?_ ?_ ?_ ?_ ?_
  · intro g hg
    rw [mem_injectiveSelections] at hg
    rw [Finset.mem_product]
    refine ⟨?_, Finset.mem_univ _⟩
    rw [mem_increasingSelections]
    exact (Tuple.monotone_sort g).strictMono_of_injective
      (hg.comp (Tuple.sort g).injective)
  · rintro ⟨f, τ⟩ hp
    rw [Finset.mem_product, mem_increasingSelections] at hp
    rw [mem_injectiveSelections]
    exact hp.1.injective.comp τ.injective
  · intro g _
    exact comp_perm_comp_inv g (Tuple.sort g)
  · rintro ⟨f, τ⟩ hp
    rw [Finset.mem_product, mem_increasingSelections] at hp
    rw [sort_comp_perm hp.1 τ, comp_perm_comp_inv f τ, inv_inv]
  · intro g _
    rw [comp_perm_comp_inv g (Tuple.sort g)]

/-- Collapsing the permutation sum at a fixed increasing selection produces the
pair of complementary minors. -/
private theorem sum_perm_det_prod (A : Matrix (Fin k) (Fin n) R)
    (B : Matrix (Fin n) (Fin k) R) (f : Fin k → Fin n) :
    (∑ τ : Equiv.Perm (Fin k), (A.submatrix id (f ∘ ⇑τ)).det * ∏ a, B ((f ∘ ⇑τ) a) a)
      = (A.submatrix id f).det * (B.submatrix f id).det := by
  have hA : ∀ τ : Equiv.Perm (Fin k),
      (A.submatrix id (f ∘ ⇑τ)).det
        = ((Equiv.Perm.sign τ : ℤ) : R) * (A.submatrix id f).det := by
    intro τ
    have hsub : A.submatrix id (f ∘ ⇑τ) = (A.submatrix id f).submatrix id ⇑τ :=
      Matrix.ext fun _ _ => rfl
    rw [hsub]
    exact Matrix.det_permute' τ (A.submatrix id f)
  rw [Matrix.det_apply' (B.submatrix f id), Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [hA τ]
  simp only [Matrix.submatrix_apply, id_eq, Function.comp_apply]
  ring

/-! ### Cauchy–Binet -/

/-- **Cauchy–Binet.**  For `A` of size `k × n` and `B` of size `n × k`,
\[
  \det(AB)=\sum_{S}\det A_{\bullet,S}\,\det B_{S,\bullet},
\]
the sum running over the `k`-element column selections `S` of `A`, each carried
by the strictly monotone map `f : Fin k → Fin n` that lists it in increasing
order.  For `k > n` the index set is empty and the identity states that
`det (A * B) = 0`. -/
theorem det_mul_eq_sum_increasing (A : Matrix (Fin k) (Fin n) R)
    (B : Matrix (Fin n) (Fin k) R) :
    (A * B).det
      = ∑ f ∈ increasingSelections k n,
          (A.submatrix id f).det * (B.submatrix f id).det := by
  calc (A * B).det
      = ∑ g : Fin k → Fin n, (A.submatrix id g).det * ∏ a, B (g a) a :=
        det_mul_eq_sum_over_maps A B
    _ = ∑ g ∈ injectiveSelections k n, (A.submatrix id g).det * ∏ a, B (g a) a := by
        refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
        intro g _ hg
        rw [mem_injectiveSelections] at hg
        rw [det_submatrix_eq_zero_of_not_injective A hg, zero_mul]
    _ = ∑ p ∈ (increasingSelections k n) ×ˢ (Finset.univ : Finset (Equiv.Perm (Fin k))),
          (A.submatrix id (p.1 ∘ ⇑p.2)).det * ∏ a, B ((p.1 ∘ ⇑p.2) a) a :=
        sum_injective_eq_sum_increasing_perm
          (fun g => (A.submatrix id g).det * ∏ a, B (g a) a)
    _ = ∑ f ∈ increasingSelections k n, ∑ τ : Equiv.Perm (Fin k),
          (A.submatrix id (f ∘ ⇑τ)).det * ∏ a, B ((f ∘ ⇑τ) a) a :=
        Finset.sum_product _ _ _
    _ = ∑ f ∈ increasingSelections k n,
          (A.submatrix id f).det * (B.submatrix f id).det :=
        Finset.sum_congr rfl fun f _ => sum_perm_det_prod A B f

/-! ### Andréief

`F i` and `G j` are two families of `Fin n`-indexed data paired by the sum
`⟨F i, G j⟩ = ∑ x, F i x * G j x`.  The Gram determinant of the pairing expands
over increasing `k`-tuples; symmetrizing over the `k!` orderings of a tuple
gives the unordered form. -/

/-- **Andréief (Gram–Heine) expansion.**  The `k × k` Gram determinant of the pairing
`⟨F i, G j⟩ = ∑_x F i x * G j x` expands over increasing `k`-tuples `f` as the
product of the two sampled `k × k` determinants:
\[
  \det\bigl[\langle F_i,G_j\rangle\bigr]_{i,j}
    =\sum_{f}\det\bigl[F_i(f_a)\bigr]\,\det\bigl[G_j(f_a)\bigr].
\] -/
theorem det_gram_eq_sum_increasing (F G : Fin k → Fin n → R) :
    (Matrix.of fun i j => ∑ x : Fin n, F i x * G j x).det
      = ∑ f ∈ increasingSelections k n,
          (Matrix.of fun i a => F i (f a)).det * (Matrix.of fun j a => G j (f a)).det := by
  have hmul : (Matrix.of fun (i j : Fin k) => ∑ x : Fin n, F i x * G j x)
      = Matrix.of F * Matrix.of (fun (x : Fin n) (j : Fin k) => G j x) :=
    Matrix.ext fun _ _ => rfl
  rw [hmul, det_mul_eq_sum_increasing]
  refine Finset.sum_congr rfl fun f _ => ?_
  have h1 : (Matrix.of F).submatrix id f = Matrix.of fun (i a : Fin k) => F i (f a) :=
    Matrix.ext fun _ _ => rfl
  have h2 : (Matrix.of (fun (x : Fin n) (j : Fin k) => G j x)).submatrix f id
      = (Matrix.of fun (j a : Fin k) => G j (f a))ᵀ :=
    Matrix.ext fun _ _ => rfl
  rw [h1, h2, Matrix.det_transpose]

/-- Symmetrization: a function of index tuples that vanishes on repeated tuples
and is invariant under permuting a tuple sums over all tuples to `k!` times its
sum over increasing tuples. -/
private theorem sum_eq_factorial_mul_sum_increasing (Ψ : (Fin k → Fin n) → R)
    (hvanish : ∀ g : Fin k → Fin n, ¬ Function.Injective g → Ψ g = 0)
    (hinv : ∀ (f : Fin k → Fin n) (τ : Equiv.Perm (Fin k)), Ψ (f ∘ ⇑τ) = Ψ f) :
    (∑ g : Fin k → Fin n, Ψ g)
      = (Nat.factorial k : R) * ∑ f ∈ increasingSelections k n, Ψ f := by
  calc (∑ g : Fin k → Fin n, Ψ g)
      = ∑ g ∈ injectiveSelections k n, Ψ g := by
        refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
        intro g _ hg
        rw [mem_injectiveSelections] at hg
        exact hvanish g hg
    _ = ∑ p ∈ (increasingSelections k n) ×ˢ (Finset.univ : Finset (Equiv.Perm (Fin k))),
          Ψ (p.1 ∘ ⇑p.2) := sum_injective_eq_sum_increasing_perm Ψ
    _ = ∑ f ∈ increasingSelections k n, ∑ τ : Equiv.Perm (Fin k), Ψ (f ∘ ⇑τ) :=
        Finset.sum_product _ _ _
    _ = ∑ f ∈ increasingSelections k n, (Nat.factorial k : R) * Ψ f := by
        refine Finset.sum_congr rfl fun f _ => ?_
        have hcong : (∑ τ : Equiv.Perm (Fin k), Ψ (f ∘ ⇑τ))
            = ∑ _τ : Equiv.Perm (Fin k), Ψ f :=
          Finset.sum_congr rfl fun τ _ => hinv f τ
        rw [hcong, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
          nsmul_eq_mul]
    _ = (Nat.factorial k : R) * ∑ f ∈ increasingSelections k n, Ψ f :=
        (Finset.mul_sum _ _ _).symm

/-- A repeated index gives both minors a repeated column, so a non-injective selection
contributes nothing. -/
private theorem det_mul_det_eq_zero_of_not_injective (F G : Fin k → Fin n → R)
    {g : Fin k → Fin n} (hg : ¬ Function.Injective g) :
    (Matrix.of fun (i a : Fin k) => F i (g a)).det
      * (Matrix.of fun (j a : Fin k) => G j (g a)).det = 0 := by
  obtain ⟨a, b, hab, hne⟩ := Function.not_injective_iff.mp hg
  rw [Matrix.det_zero_of_column_eq hne fun i => by simp only [Matrix.of_apply, hab], zero_mul]

/-- Precomposing the selection with a permutation of the index leaves the product of the two
minors alone: each determinant picks up the sign of the permutation, and the two signs cancel. -/
private theorem det_mul_det_comp_perm (F G : Fin k → Fin n → R) (f : Fin k → Fin n)
    (τ : Equiv.Perm (Fin k)) :
    (Matrix.of fun (i a : Fin k) => F i ((f ∘ ⇑τ) a)).det
        * (Matrix.of fun (j a : Fin k) => G j ((f ∘ ⇑τ) a)).det
      = (Matrix.of fun (i a : Fin k) => F i (f a)).det
        * (Matrix.of fun (j a : Fin k) => G j (f a)).det := by
  rw [show (Matrix.of fun (i a : Fin k) => F i ((f ∘ ⇑τ) a))
        = (Matrix.of fun (i a : Fin k) => F i (f a)).submatrix id ⇑τ from
      Matrix.ext fun _ _ => rfl,
    show (Matrix.of fun (j a : Fin k) => G j ((f ∘ ⇑τ) a))
        = (Matrix.of fun (j a : Fin k) => G j (f a)).submatrix id ⇑τ from
      Matrix.ext fun _ _ => rfl,
    Matrix.det_permute', Matrix.det_permute', mul_mul_mul_comm]
  simp only [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one,
    Int.cast_one, one_mul]

/-- **Symmetrized Andréief.**  Summing the sampled determinant product over
*all* index tuples, rather than the increasing
ones, multiplies the Gram determinant by `k!` — the division-free form of the
`1/k!` prefactor of the `k`-fold integral. -/
theorem factorial_mul_det_gram (F G : Fin k → Fin n → R) :
    (Nat.factorial k : R) * (Matrix.of fun i j => ∑ x : Fin n, F i x * G j x).det
      = ∑ g : Fin k → Fin n,
          (Matrix.of fun i a => F i (g a)).det * (Matrix.of fun j a => G j (g a)).det := by
  rw [det_gram_eq_sum_increasing F G,
    ← sum_eq_factorial_mul_sum_increasing
      (fun g => (Matrix.of fun i a => F i (g a)).det
        * (Matrix.of fun j a => G j (g a)).det)
      (fun _ hg => det_mul_det_eq_zero_of_not_injective F G hg)
      (det_mul_det_comp_perm F G)]


/-! ### Axiom footprint -/

/-- info: 'Shields.increasingSelections_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms increasingSelections_nonempty

/-- info: 'Shields.factorial_mul_det_gram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms factorial_mul_det_gram

end Shields
