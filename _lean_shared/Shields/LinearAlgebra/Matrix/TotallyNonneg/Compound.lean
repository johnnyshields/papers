/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Analysis.Complex.Polynomial.Basic
import Shields.LinearAlgebra.Matrix.TotallyNonneg.Basic
import Vendor.MathlibPR.PR39837.MatrixSchurTriangulation

/-!
# Compound matrices, and the spectrum of a matrix with nonnegative minors

The `r`-th compound `∧^r A`, whose entries are the `r × r` minors of `A`, and what it gives about
the eigenvalues of a matrix all of whose minors are nonnegative.

## Main results

* `Shields.compound`: the `r`-th compound matrix, indexed by increasing selections.
* `Shields.compound_mul`: `∧^r (A * B) = (∧^r A) * (∧^r B)`, which is Cauchy--Binet.
* `Shields.charpoly_roots_nonneg`: the real eigenvalues of a matrix with nonnegative minors are
  nonnegative. The coefficients of `det (1 + s A)` are sums of principal minors, so `det (t I + A)`
  is positive for `t > 0` and `-t` is never a root.
* `Shields.charpoly_compound_of_upperTriangular`, `Shields.charpoly_compound_complex`: the spectrum
  of `∧^r A` consists of the `r`-fold products of the eigenvalues of `A`.

## Implementation notes

Mathlib carries no compound matrix at the pinned revision, and none is in flight.

`charpoly_compound_complex` needs triangularization over `ℂ` as similarity to an upper-triangular
matrix, which the pinned Mathlib revision has only in generalized-eigenspace form
(`Mathlib/LinearAlgebra/Eigenspace/Triangularizable.lean`, whose own TODO names the gap). It is
taken from the vendored PR chain; see `_lean_shared/Vendor/README.md`.

`det_eq_prod_diag_of_selection_triangular` deliberately avoids transporting the componentwise order
on selections to a `LinearOrder`.

## References

* [A. Pinkus, *Totally Positive Matrices*][Pinkus2010], Cor. 5.5

## Tags

compound matrix, exterior power, total positivity, characteristic polynomial, eigenvalue
-/

open scoped BigOperators

namespace Shields

variable {n : ℕ}

/-! ### Principal minors

`MinorsNonneg` is indexed by strictly monotone selections `Fin k → Fin n`;
Mathlib's principal-minor expansion of the characteristic polynomial is indexed
by `Finset`s.  `orderEmbOfFin` is the bridge, and `det_submatrix_equiv_self`
makes the reindexing free. -/

/-- Every principal minor of a totally nonnegative matrix is nonnegative.  This
is `MinorsNonneg` transported from strictly monotone selections to `Finset`
indexing, which is the form Mathlib's charpoly expansion consumes. -/
theorem principal_det_nonneg {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ k, MinorsNonneg k A) (s : Finset (Fin n)) :
    0 ≤ (A.submatrix (Subtype.val : s → Fin n) Subtype.val).det := by
  have hiso : ∀ i : Fin s.card,
      ((s.orderIsoOfFin rfl i : Fin n)) = s.orderEmbOfFin rfl i := fun _ => rfl
  have hre : (A.submatrix (Subtype.val : s → Fin n) Subtype.val).det
      = (A.submatrix (s.orderEmbOfFin rfl) (s.orderEmbOfFin rfl)).det := by
    rw [← Matrix.det_submatrix_equiv_self (s.orderIsoOfFin rfl).toEquiv
      (A.submatrix (Subtype.val : s → Fin n) Subtype.val)]
    rfl
  rw [hre]
  exact hA s.card _ _ (mem_increasingSelections.mpr (s.orderEmbOfFin rfl).strictMono)
    (mem_increasingSelections.mpr (s.orderEmbOfFin rfl).strictMono)

/-! ### `det(1 + sA)` and the absence of negative eigenvalues -/

/-- The polynomial `det(1 + XA)`, whose `k`-th coefficient is the sum of the
`k × k` principal minors of `A`. -/
noncomputable def princPoly (A : Matrix (Fin n) (Fin n) ℝ) : Polynomial ℝ :=
  Matrix.det (1 + (Polynomial.X : Polynomial ℝ) • A.map Polynomial.C)

theorem princPoly_eval (A : Matrix (Fin n) (Fin n) ℝ) (s : ℝ) :
    (princPoly A).eval s = (1 + s • A).det := by
  rw [princPoly, ← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  by_cases h : i = j <;> simp [h] <;> ring

theorem princPoly_coeff_nonneg {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ k, MinorsNonneg k A) (k : ℕ) : 0 ≤ (princPoly A).coeff k := by
  rw [princPoly, Matrix.coeff_det_one_add_X_smul_eq_sum_minors]
  exact Finset.sum_nonneg fun s _ => principal_det_nonneg hA s

theorem princPoly_coeff_zero (A : Matrix (Fin n) (Fin n) ℝ) :
    (princPoly A).coeff 0 = 1 := by
  rw [princPoly, Matrix.coeff_det_one_add_X_smul_eq_sum_minors,
    Finset.powersetCard_zero, Finset.sum_singleton]
  exact Matrix.det_isEmpty

/-- **`det(1 + sA) ≥ 1` for `s ≥ 0`.**  Every coefficient of `det(1 + XA)` is a
sum of principal minors, hence nonnegative, and the constant term is `1`. -/
theorem one_le_det_one_add_smul {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ k, MinorsNonneg k A) {s : ℝ} (hs : 0 ≤ s) :
    1 ≤ (1 + s • A).det := by
  rw [← princPoly_eval A s,
    Polynomial.eval_eq_sum_range (p := princPoly A) (x := s)]
  have hmem : 0 ∈ Finset.range ((princPoly A).natDegree + 1) :=
    Finset.mem_range.mpr (Nat.succ_pos _)
  have hterms : ∀ i ∈ Finset.range ((princPoly A).natDegree + 1),
      0 ≤ (princPoly A).coeff i * s ^ i :=
    fun i _ => mul_nonneg (princPoly_coeff_nonneg hA i) (pow_nonneg hs i)
  have hle := Finset.single_le_sum (f := fun i => (princPoly A).coeff i * s ^ i)
    hterms hmem
  rwa [pow_zero, mul_one, princPoly_coeff_zero] at hle

/-- **`det(tI + A) > 0` for `t > 0`** when `A` is totally nonnegative. -/
theorem det_smul_one_add_pos {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ k, MinorsNonneg k A) {t : ℝ} (ht : 0 < t) :
    0 < (t • (1 : Matrix (Fin n) (Fin n) ℝ) + A).det := by
  have hfac : t • (1 : Matrix (Fin n) (Fin n) ℝ) + A
      = t • (1 + t⁻¹ • A) := by
    rw [smul_add, smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
  rw [hfac, Matrix.det_smul, Fintype.card_fin]
  exact mul_pos (pow_pos ht n)
    (lt_of_lt_of_le zero_lt_one (one_le_det_one_add_smul hA (inv_nonneg.mpr ht.le)))

/-- **A matrix with nonnegative minors has no negative eigenvalue.**  This is the
nonnegativity half of Cor. 5.5 of [Pinkus2010].

Proved outright: it needs only that the principal minors are nonnegative, so no
approximation argument and no Perron–Frobenius enter.  The *reality* half is the
one that does. -/
theorem charpoly_roots_nonneg {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ k, MinorsNonneg k A) {r : ℝ} (hr : r ∈ A.charpoly.roots) :
    0 ≤ r := by
  by_contra hneg
  push Not at hneg
  have heval : A.charpoly.eval r = 0 := (Polynomial.mem_roots'.mp hr).2
  have hs1 : Matrix.scalar (Fin n) r = r • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    by_cases h : i = j <;> simp [h, Matrix.scalar_apply]
  have hscal : Matrix.scalar (Fin n) r - A = -((-r) • (1 : Matrix (Fin n) (Fin n) ℝ) + A) := by
    rw [hs1, neg_add, ← neg_smul, neg_neg, ← sub_eq_add_neg]
  rw [Matrix.eval_charpoly, hscal, Matrix.det_neg, Fintype.card_fin] at heval
  have hpos := det_smul_one_add_pos hA (neg_pos.mpr hneg)
  rcases mul_eq_zero.mp heval with h | h
  · exact absurd h (pow_ne_zero n (by norm_num))
  · exact absurd h hpos.ne'

/-! ### Compound matrices

The `r`-th compound `∧^r A` has the `r × r` minors of `A` as its entries, and is
multiplicative in `A` — which is Cauchy–Binet, already proved in `Andreief`.
This is the object the reality half of `\cite[Cor.~5.5]{Pinkus2010}` runs
Perron–Frobenius on.  The pinned Mathlib revision carries no compound matrix, and
none is in flight; Cauchy–Binet itself is in flight as
`feat(LinearAlgebra/Matrix): the Cauchy-Binet formula` (#40473). -/

/-- The `r`-th **compound matrix**: rows and columns indexed by the strictly
monotone selections `Fin r → Fin n`, entries the corresponding `r × r` minors. -/
noncomputable def compound {R : Type*} [CommRing R] (r : ℕ) (A : Matrix (Fin n) (Fin n) R) :
    Matrix (increasingSelections r n) (increasingSelections r n) R :=
  Matrix.of fun f g => (A.submatrix f.1 g.1).det

@[simp] theorem compound_apply {R : Type*} [CommRing R] (r : ℕ)
    (A : Matrix (Fin n) (Fin n) R) (f g : increasingSelections r n) :
    compound r A f g = (A.submatrix f.1 g.1).det := rfl

/-- **The compound is multiplicative**, `∧^r(AB) = (∧^r A)(∧^r B)`.  This is
exactly Cauchy–Binet, and it is what makes total nonnegativity a closed property
under products. -/
theorem compound_mul {R : Type*} [CommRing R] (r : ℕ) (A B : Matrix (Fin n) (Fin n) R) :
    compound r (A * B) = compound r A * compound r B := by
  ext f g
  have hsub : ((A * B).submatrix f.1 g.1)
      = A.submatrix f.1 id * B.submatrix id g.1 := by
    ext a b
    simp [Matrix.mul_apply, Matrix.submatrix_apply]
  rw [compound_apply, hsub, det_mul_eq_sum_increasing, Matrix.mul_apply]
  exact (Finset.sum_attach (increasingSelections r n)
    fun h => (A.submatrix f.1 h).det * (B.submatrix h g.1).det).symm

/-- **The compound of a totally nonnegative matrix has nonnegative entries.**
In the totally *positive* case the entries are strictly positive, which is the
hypothesis Perron–Frobenius would be applied under. -/
theorem compound_entry_nonneg {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ k, MinorsNonneg k A) (r : ℕ)
    (f g : increasingSelections r n) : 0 ≤ compound r A f g :=
  hA r f.1 g.1 f.2 g.2

/-! ### Reality at `n ≤ 2`

The smallest genuine instance of the missing half.  For `[[a,b],[c,d]]` with
`b, c ≥ 0` the discriminant is `(a-d)² + 4bc ≥ 0`, so the eigenvalues are real —
no compound matrix and no Perron–Frobenius needed at this size. -/

/-- **Reality of the spectrum at `n = 2`.**  A `2 × 2` matrix whose off-diagonal
product is nonnegative — in particular any totally nonnegative one — has a
characteristic polynomial that splits over `ℝ`. -/
theorem charpoly_roots_card_two {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hbc : 0 ≤ A 0 1 * A 1 0) :
    Multiset.card A.charpoly.roots = 2 := by
  set a := A 0 0; set b := A 0 1; set c := A 1 0; set d := A 1 1
  have hdisc : 0 ≤ (a + d) ^ 2 - 4 * (a * d - b * c) := by nlinarith [sq_nonneg (a - d)]
  set D := Real.sqrt ((a + d) ^ 2 - 4 * (a * d - b * c)) with hD
  have hD2 : D ^ 2 = (a + d) ^ 2 - 4 * (a * d - b * c) := Real.sq_sqrt hdisc
  have htr : A.trace = a + d := by
    rw [Matrix.trace_fin_two]
  have hdet : A.det = a * d - b * c := Matrix.det_fin_two A
  have hexp : ((a + d + D) / 2) * ((a + d - D) / 2) = a * d - b * c := by
    field_simp
    nlinarith [hD2]
  have hsum : ((a + d + D) / 2) + ((a + d - D) / 2) = a + d := by ring
  have hchar : A.charpoly
      = (Polynomial.X - Polynomial.C ((a + d + D) / 2))
        * (Polynomial.X - Polynomial.C ((a + d - D) / 2)) := by
    have hprod : (Polynomial.X - Polynomial.C ((a + d + D) / 2))
          * (Polynomial.X - Polynomial.C ((a + d - D) / 2))
        = Polynomial.X ^ 2
          - Polynomial.C ((a + d + D) / 2 + (a + d - D) / 2) * Polynomial.X
          + Polynomial.C ((a + d + D) / 2 * ((a + d - D) / 2)) := by
      simp only [Polynomial.C_add, Polynomial.C_mul]
      ring
    rw [Matrix.charpoly_of_card_eq_two (M := A) (by simp), htr, hdet, hprod, hsum, hexp]
  rw [hchar, Polynomial.roots_mul (by
    refine mul_ne_zero ?_ ?_ <;> exact Polynomial.X_sub_C_ne_zero _),
    Polynomial.roots_X_sub_C, Polynomial.roots_X_sub_C]
  rfl

/-! ### Compounds of triangular matrices

The step the reality argument needs after Perron–Frobenius: the eigenvalues of
`∧^r A` are the `r`-fold products of the eigenvalues of `A`.  The classical proof
triangularizes `A` over `ℂ` and observes that `∧^r` of a triangular matrix is
again triangular, with the products on its diagonal.  Both halves of that
observation are proved here, and the assembly is completed below:
`det_eq_prod_diag_of_selection_triangular` avoids transporting the componentwise
order on selections to a `LinearOrder`, and `charpoly_compound_complex` supplies
the triangularization from the vendored PR chain — the pinned Mathlib revision
carries it only in generalized-eigenspace form
(`LinearAlgebra/Eigenspace/Triangularizable.lean`, whose own TODO names it). -/

/-- **Off-diagonal minors of a triangular matrix vanish.**  If `T` is upper
triangular and some selected row index exceeds its column partner, every term of
the Leibniz expansion is zero: the surviving permutations would have to embed
`{a : a ≤ a₀}` into `{b : b < a₀}`. -/
theorem det_submatrix_eq_zero_of_lt {R : Type*} [CommRing R] {k : ℕ}
    {T : Matrix (Fin n) (Fin n) R} (hT : ∀ i j, j < i → T i j = 0)
    {f g : Fin k → Fin n} (hf : StrictMono f) (hg : Monotone g)
    {a₀ : Fin k} (ha₀ : g a₀ < f a₀) :
    (T.submatrix f g).det = 0 := by
  rw [Matrix.det_apply]
  refine Finset.sum_eq_zero fun σ _ => ?_
  obtain ⟨a, ha⟩ : ∃ a : Fin k, (T.submatrix f g) (σ a) a = 0 := by
    by_contra hc
    push Not at hc
    -- Every factor nonzero forces `f (σ a) ≤ g a` for all `a`.
    have hall : ∀ a : Fin k, f (σ a) ≤ g a := by
      intro a
      by_contra hlt
      push Not at hlt
      exact hc a (by simpa [Matrix.submatrix_apply] using hT _ _ hlt)
    -- Then `σ` injects `Iic a₀` into `Iio a₀`, which is one element smaller.
    have hmaps : ∀ a ∈ Finset.Iic a₀, σ a ∈ Finset.Iio a₀ := by
      intro a ha'
      have hale : a ≤ a₀ := Finset.mem_Iic.mp ha'
      have h3 : f (σ a) < f a₀ := lt_of_le_of_lt ((hall a).trans (hg hale)) ha₀
      exact Finset.mem_Iio.mpr (hf.lt_iff_lt.mp h3)
    have hcard := Finset.card_le_card_of_injOn σ hmaps
      (fun a _ b _ hab => σ.injective hab)
    rw [Fin.card_Iic, Fin.card_Iio] at hcard
    omega
  exact smul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ a) ha)

/-- **The diagonal minors of a triangular matrix are the products.**  A strictly
monotone selection preserves the triangular shape, so the principal minor at `f`
is `∏_a T (f a) (f a)`. -/
theorem det_submatrix_diag_of_upperTriangular {R : Type*} [CommRing R] {k : ℕ}
    {T : Matrix (Fin n) (Fin n) R} (hT : ∀ i j, j < i → T i j = 0)
    {f : Fin k → Fin n} (hf : StrictMono f) :
    (T.submatrix f f).det = ∏ a, T (f a) (f a) := by
  have hblock : (T.submatrix f f).BlockTriangular id := by
    intro i j hij
    exact hT _ _ (hf hij)
  rw [Matrix.det_of_upperTriangular hblock]
  rfl

/-- **The compound of a triangular matrix is triangular**, in the componentwise
order on selections, with the `r`-fold products of the diagonal on its own
diagonal.  This is the whole of what the eigenvalue statement needs from the
triangular form; the rest is the triangularization and the order transport. -/
theorem compound_upperTriangular {R : Type*} [CommRing R] {r : ℕ}
    {T : Matrix (Fin n) (Fin n) R} (hT : ∀ i j, j < i → T i j = 0)
    (f g : increasingSelections r n) :
    (∃ a, g.1 a < f.1 a) → compound r T f g = 0 := by
  rintro ⟨a₀, ha₀⟩
  have hf : StrictMono f.1 := mem_increasingSelections.mp f.2
  have hg : Monotone g.1 := (mem_increasingSelections.mp g.2).monotone
  exact det_submatrix_eq_zero_of_lt hT hf hg ha₀

theorem compound_diag {R : Type*} [CommRing R] {r : ℕ}
    {T : Matrix (Fin n) (Fin n) R} (hT : ∀ i j, j < i → T i j = 0)
    (f : increasingSelections r n) :
    compound r T f f = ∏ a, T (f.1 a) (f.1 a) :=
  det_submatrix_diag_of_upperTriangular hT (mem_increasingSelections.mp f.2)

/-! ### The spectrum of a triangular compound

`det_of_upperTriangular` wants a `LinearOrder` on the index type, and selections
carry only the componentwise partial order.  The order transport is avoidable:
the same counting argument that killed the off-diagonal minors also kills every
non-identity permutation in the Leibniz expansion of the compound itself.  If
`σ f ≤ f` componentwise for every selection `f`, then the index sums satisfy
`S(σf) ≤ S(f)`, and summing over all `f` — where `σ` merely permutes the terms —
forces equality throughout, hence `σ = 1`. -/

/-- A matrix indexed by increasing selections that vanishes whenever a selected
row index exceeds its column partner has determinant the product of its
diagonal. -/
theorem det_eq_prod_diag_of_selection_triangular {R : Type*} [CommRing R] {r : ℕ}
    (M : Matrix (increasingSelections r n) (increasingSelections r n) R)
    (hM : ∀ f g : increasingSelections r n, (∃ a, g.1 a < f.1 a) → M f g = 0) :
    M.det = ∏ f, M f f := by
  rw [Matrix.det_apply]
  rw [Finset.sum_eq_single (1 : Equiv.Perm (increasingSelections r n))]
  · simp
  · intro σ _ hσ
    refine smul_eq_zero_of_right _ ?_
    obtain ⟨f, hf⟩ : ∃ f, M (σ f) f = 0 := by
      by_contra hc
      push Not at hc
      -- Every factor nonzero forces `σ f ≤ f` componentwise, for every `f`.
      have hle : ∀ f : increasingSelections r n, ∀ a, ((σ f).1 a : ℕ) ≤ (f.1 a : ℕ) := by
        intro f a
        by_contra h
        push Not at h
        exact hc f (hM (σ f) f ⟨a, by exact_mod_cast h⟩)
      -- Index sums then decrease weakly, but `σ` only permutes them.
      set S : increasingSelections r n → ℕ := fun f => ∑ a, ((f.1 a : Fin n) : ℕ) with hS
      have hSle : ∀ f, S (σ f) ≤ S f := fun f =>
        Finset.sum_le_sum fun a _ => hle f a
      have htot : ∑ f, S (σ f) = ∑ f, S f := Equiv.sum_comp σ S
      have hSeq : ∀ f, S (σ f) = S f :=
        fun f => (Finset.sum_eq_sum_iff_of_le (fun f _ => hSle f)).1 htot f (Finset.mem_univ f)
      -- Weak decrease with equal totals is equality in each coordinate.
      have hfix : ∀ f, σ f = f := by
        intro f
        refine Subtype.ext (funext fun a => ?_)
        have := (Finset.sum_eq_sum_iff_of_le (fun a _ => hle f a)).1 (hSeq f) a
          (Finset.mem_univ a)
        exact Fin.ext this
      exact hσ (Equiv.ext hfix)
    exact Finset.prod_eq_zero (Finset.mem_univ f) hf
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The characteristic polynomial of such a matrix splits with the diagonal
entries as its roots. -/
theorem charpoly_of_selection_triangular {R : Type*} [CommRing R] {r : ℕ}
    (M : Matrix (increasingSelections r n) (increasingSelections r n) R)
    (hM : ∀ f g : increasingSelections r n, (∃ a, g.1 a < f.1 a) → M f g = 0) :
    M.charpoly = ∏ f, (Polynomial.X - Polynomial.C (M f f)) := by
  have hchar : ∀ f g : increasingSelections r n, (∃ a, g.1 a < f.1 a) →
      Matrix.charmatrix M f g = 0 := by
    intro f g hfg
    have hne : f ≠ g := by
      rintro rfl
      obtain ⟨a, ha⟩ := hfg
      exact lt_irrefl _ ha
    rw [Matrix.charmatrix_apply_ne _ _ _ hne, hM f g hfg, map_zero, neg_zero]
  rw [Matrix.charpoly, det_eq_prod_diag_of_selection_triangular _ hchar]
  exact Finset.prod_congr rfl fun f _ => Matrix.charmatrix_apply_eq M f

/-- **The spectrum of the compound of a triangular matrix.**  The characteristic
polynomial of `∧^r T` splits with the `r`-fold products of the diagonal of `T` as
its roots — one root per increasing selection.

This is the eigenvalue statement the Gantmacher–Krein reality argument runs on,
for a matrix already in triangular form.  Applying it to a general complex matrix
needs triangularization, which the pinned Mathlib revision does not carry as
similarity to an upper-triangular matrix; `charpoly_compound_complex` below takes
it from the vendored PR chain. -/
theorem charpoly_compound_of_upperTriangular {R : Type*} [CommRing R] {r : ℕ}
    {T : Matrix (Fin n) (Fin n) R} (hT : ∀ i j, j < i → T i j = 0) :
    (compound r T).charpoly
      = ∏ f : increasingSelections r n,
          (Polynomial.X - Polynomial.C (∏ a, T (f.1 a) (f.1 a))) := by
  rw [charpoly_of_selection_triangular _ (fun f g hfg => compound_upperTriangular hT f g hfg)]
  exact Finset.prod_congr rfl fun f _ => by rw [compound_diag hT f]

/-! ### The compound is a monoid map, so it respects similarity

With `compound_mul` and `compound_one` the compound carries a conjugation
`P A P⁻¹` to a conjugation, so `charpoly (∧^r A)` is a similarity invariant.
Together with `charpoly_compound_of_upperTriangular` that reduces the eigenvalue
statement to putting `A` in triangular form — and nothing else. -/

/-- An increasing-selection minor of the identity is `1` on the diagonal and `0`
off it: two strictly monotone selections with the same image coincide, so a
mismatch leaves an entirely zero row. -/
theorem det_submatrix_one {R : Type*} [CommRing R] {k : ℕ} {f g : Fin k → Fin n}
    (hf : StrictMono f) (hg : StrictMono g) :
    ((1 : Matrix (Fin n) (Fin n) R).submatrix f g).det = if f = g then 1 else 0 := by
  by_cases h : f = g
  · subst h
    rw [Matrix.submatrix_one f hf.injective, Matrix.det_one, if_pos rfl]
  · rw [if_neg h]
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
    exact Matrix.det_eq_zero_of_row_eq_zero a fun b => by simp [ha b]

@[simp] theorem compound_one {R : Type*} [CommRing R] (r : ℕ) :
    compound r (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  ext f g
  rw [compound_apply, det_submatrix_one (mem_increasingSelections.mp f.2)
    (mem_increasingSelections.mp g.2), Matrix.one_apply]
  by_cases h : f = g
  · rw [if_pos (congrArg Subtype.val h), if_pos h]
  · rw [if_neg (fun hc => h (Subtype.ext hc)), if_neg h]

/-- The compound of a unit is a unit, with the compound of the inverse as its
inverse — immediate from `compound_mul` and `compound_one`. -/
noncomputable def compoundUnit {R : Type*} [CommRing R] (r : ℕ)
    (P : (Matrix (Fin n) (Fin n) R)ˣ) :
    (Matrix (increasingSelections r n) (increasingSelections r n) R)ˣ where
  val := compound r (P : Matrix (Fin n) (Fin n) R)
  inv := compound r (↑P⁻¹ : Matrix (Fin n) (Fin n) R)
  val_inv := by rw [← compound_mul, P.mul_inv, compound_one]
  inv_val := by rw [← compound_mul, P.inv_mul, compound_one]

/-- **The compound respects similarity.**  Conjugating `A` conjugates `∧^r A`, so
the characteristic polynomial of the compound depends only on the similarity
class of `A`.  With `charpoly_compound_of_upperTriangular` this reduces the
eigenvalue statement to putting `A` in triangular form, and to nothing else. -/
theorem charpoly_compound_conj {R : Type*} [CommRing R] (r : ℕ)
    (P : (Matrix (Fin n) (Fin n) R)ˣ) (A : Matrix (Fin n) (Fin n) R) :
    (compound r ((P : Matrix (Fin n) (Fin n) R) * A
        * (↑P⁻¹ : Matrix (Fin n) (Fin n) R))).charpoly
      = (compound r A).charpoly := by
  have hinv : ((compoundUnit r P) : Matrix (increasingSelections r n)
      (increasingSelections r n) R)⁻¹
      = compound r (↑P⁻¹ : Matrix (Fin n) (Fin n) R) := by
    rw [← Matrix.coe_units_inv]
    rfl
  have hcomp : compound r ((P : Matrix (Fin n) (Fin n) R) * A
        * (↑P⁻¹ : Matrix (Fin n) (Fin n) R))
      = ((compoundUnit r P) : Matrix _ _ R) * compound r A
        * ((compoundUnit r P) : Matrix _ _ R)⁻¹ := by
    rw [compound_mul, compound_mul, hinv]
    rfl
  rw [hcomp, Matrix.charpoly_units_conj]

/-! ### The spectrum of a compound over `ℂ`

With Schur triangulation the two ends meet.  `charpoly (∧^r A)` is a similarity
invariant, and for a triangular matrix it splits with the `r`-fold products of
the diagonal as its roots; every complex matrix is unitarily similar to a
triangular one.  The triangularization is vendored from an unmerged Mathlib PR
(`Vendor.MathlibPR.PR39837.MatrixSchurTriangulation`), not proved here. -/

/-- **The spectrum of the compound of a complex matrix.**  `A` is similar to a
triangular `T` with the same characteristic polynomial, and `charpoly (∧^r A)`
splits with the `r`-fold products of `T`'s diagonal as its roots — one root per
increasing selection.  **One `T` serves every order `r`**, which is what an
argument comparing different orders against each other needs: the
triangularization does not depend on `r`, so the quantifier belongs inside the
existential.

This is the eigenvalue statement the Gantmacher–Krein reality argument runs on;
`GantmacherKrein` turns it into reality of totally nonnegative spectra. -/
theorem charpoly_compound_complex (A : Matrix (Fin n) (Fin n) ℂ) :
    ∃ T : Matrix (Fin n) (Fin n) ℂ, (∀ i j, j < i → T i j = 0) ∧
      A.charpoly = T.charpoly ∧
      ∀ r : ℕ, (compound r A).charpoly
        = ∏ f : increasingSelections r n,
            (Polynomial.X - Polynomial.C (∏ a, T (f.1 a) (f.1 a))) := by
  obtain ⟨U, T, hT, hA⟩ := Matrix.exists_unitaryGroup_blockTriangular A
  set P : (Matrix (Fin n) (Fin n) ℂ)ˣ :=
    ⟨(U : Matrix (Fin n) (Fin n) ℂ), star (U : Matrix (Fin n) (Fin n) ℂ), U.2.2, U.2.1⟩
    with hP
  have hAP : A = (P : Matrix (Fin n) (Fin n) ℂ) * T * (↑P⁻¹ : Matrix (Fin n) (Fin n) ℂ) := hA
  refine ⟨T, fun i j hij => hT hij, ?_, fun r => ?_⟩
  · rw [hAP, Matrix.coe_units_inv, Matrix.charpoly_units_conj]
  · rw [hAP, charpoly_compound_conj, charpoly_compound_of_upperTriangular
      (fun i j hij => hT hij)]

end Shields
