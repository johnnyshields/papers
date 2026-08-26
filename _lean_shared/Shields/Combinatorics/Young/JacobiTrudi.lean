/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Shields.Combinatorics.Young.SkewSchurPolynomial
import Mathlib.Data.Nat.Nth
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace Shields

open Finset

variable {R : Type*} [CommRing R]

/-! ## The increasing enumeration of an index set

Selecting rows and columns "in increasing order" means the minor needs `i_u`, the `u`-th smallest
element of `I`.  `Nat.nth (· ∈ I)` is that element for `u < I.card` and a junk value beyond, which
keeps the minor a total function of `I` and `m`; every lemma below that says anything about
`nthElem` carries the bound `u < I.card`.
-/

/-- The `v`-th smallest element of `I`, counting from `0`: the `i_{v+1}` of, whose enumeration
starts at `1`. -/
noncomputable def nthElem (I : Finset ℕ) (v : ℕ) : ℕ := Nat.nth (· ∈ I) v

/-- `Set.Finite.toFinset` of the membership set recovers the finset, for *any* finiteness proof.
Mathlib's `Finset.finite_toSet_toFinset` fixes the canonical proof. -/
@[simp]
theorem toFinset_setOf_mem {I : Finset ℕ} (h : {x : ℕ | x ∈ I}.Finite) : h.toFinset = I := by
  ext x
  simp

theorem nthElem_mem {I : Finset ℕ} {v : ℕ} (hv : v < I.card) : nthElem I v ∈ I := by
  have hfin := Set.finite_mem_finset I
  exact Nat.nth_mem_of_lt_card hfin (by rwa [toFinset_setOf_mem])

theorem nthElem_lt {I : Finset ℕ} {n v : ℕ} (hIn : I ⊆ Finset.range n) (hv : v < I.card) :
    nthElem I v < n :=
  Finset.mem_range.mp (hIn (nthElem_mem hv))

/-- `belowCount` of `Shields.SuperSchur` is `Nat.count`, which is what
carries the enumeration lemmas. -/
theorem belowCount_eq_count (I : Finset ℕ) (y : ℕ) : belowCount I y = Nat.count (· ∈ I) y := by
  rw [Nat.count_eq_card_filter_range, belowCount]
  apply Finset.card_nbij id <;>
    simp +contextual [Set.MapsTo, Set.InjOn, Set.SurjOn, and_comm]

/-- **The below-count dictionary.**  Every statement of the appendix phrased
with the sorted enumeration `i_1 < ⋯ < i_m` is a statement about below-counts,
and this is the translation. -/
theorem lt_belowCount_iff {I : Finset ℕ} {v y : ℕ} (hv : v < I.card) :
    v < belowCount I y ↔ nthElem I v < y := by
  have hfin := Set.finite_mem_finset I
  have hcard : v < hfin.toFinset.card := by rwa [toFinset_setOf_mem]
  rw [belowCount_eq_count]
  refine ⟨fun h => Nat.nth_lt_of_lt_count h, fun h => ?_⟩
  have hmem : nthElem I v ∈ I := nthElem_mem hv
  have hcount : Nat.count (· ∈ I) (nthElem I v) = v :=
    Nat.count_nth_of_lt_card_finite hfin hcard
  have hmono := Nat.count_monotone (· ∈ I) (show nthElem I v + 1 ≤ y by omega)
  rw [Nat.count_succ, hcount, if_pos hmem] at hmono
  omega

/-! ## read off the shape

`betaDiagram I L` is defined in `Shields.SuperSchur` by a membership rule
that never sorts `I`.  These two lemmas say it is the shape of, with the rows past the last one
included.
-/

/-- **.**  Row `v` of `betaDiagram I L` has length
`L - i_v + v`, written `L + v + 1 - i_v` for the enumeration starting at `0`. -/
theorem rowLen_betaDiagram {I : Finset ℕ} {L v : ℕ} (hv : v < I.card) :
    (betaDiagram I L).rowLen v = L + v + 1 - nthElem I v := by
  have key : ∀ j : ℕ, (v, j) ∈ betaDiagram I L ↔ j < L + v + 1 - nthElem I v := by
    intro j
    rw [mem_betaDiagram, lt_belowCount_iff hv]
    omega
  have h1 := key ((betaDiagram I L).rowLen v)
  have h2 := key (L + v + 1 - nthElem I v)
  rw [YoungDiagram.mem_iff_lt_rowLen] at h1 h2
  omega

/-- `betaDiagram I L` has exactly `I.card` rows, so a Jacobi--Trudi determinant
of size `I.card` sees all of it. -/
theorem rowLen_betaDiagram_of_card_le {I : Finset ℕ} {L v : ℕ} (hv : I.card ≤ v) :
    (betaDiagram I L).rowLen v = 0 := by
  by_contra h
  have hmem : (v, 0) ∈ betaDiagram I L :=
    YoungDiagram.mem_iff_lt_rowLen.mpr (Nat.pos_of_ne_zero h)
  rw [mem_betaDiagram] at hmem
  have := belowCount_le_card I (L + v + 1 - 0)
  omega

/-- **The Jacobi--Trudi index is the Toeplitz index.**  With `λ` and `μ` the
shapes of built from `I` and `J = tailSet n k I`,

`λ_u - μ_v - u + v = k + j_v - i_u`,

which is the entry of.  Stated additively, since both sides are
differences that a truncated subtraction would misreport. -/
theorem rowLen_betaDiagram_add {n k L Lk : ℕ} (hL : Lk + k = L) (hkn : k ≤ n) (hnL : n ≤ Lk)
    {I : Finset ℕ} (hIn : I ⊆ Finset.range n) (hkI : ∀ x, x < k → x ∈ I) {u v : ℕ}
    (hu : u < I.card) (hv : v < I.card) :
    (betaDiagram I L).rowLen u + v + nthElem I u
      = (betaDiagram (tailSet n k I) Lk).rowLen v + u + nthElem (tailSet n k I) v + k := by
  have hcard := card_tailSet hIn hkI hkn
  rw [rowLen_betaDiagram hu, rowLen_betaDiagram (show v < (tailSet n k I).card by omega)]
  have h1 : nthElem I u < n := nthElem_lt hIn hu
  have h2 : nthElem (tailSet n k I) v < n :=
    nthElem_lt (tailSet_subset_range hIn) (by omega)
  omega

/-! ## The minor and the Jacobi--Trudi determinant -/

/-- The Toeplitz entry `d_{k + j - i}` of, zero where the index
would be negative. -/
def shiftedCoeff (d : ℕ → R) (k i j : ℕ) : R := if i ≤ k + j then d (k + j - i) else 0

/-- **.**  The minor `Δ_C = det[d_{k + j - i}]_{i ∈ I, j ∈ J}` of
the Toeplitz matrix of `d`, rows and columns taken in increasing order.  `m` is
the common size `m_C` of. -/
noncomputable def toeplitzMinor (d : ℕ → R) (k m : ℕ) (I J : Finset ℕ) : R :=
  (Matrix.of fun u v : Fin m => shiftedCoeff d k (nthElem I u) (nthElem J v)).det

/-- The Jacobi--Trudi entry `h_{p - q}`, zero where the index would be
negative. -/
def jtCoeff (d : ℕ → R) (p q : ℕ) : R := if q ≤ p then d (p - q) else 0

/-- The right-hand determinant of skew Jacobi--Trudi,
`det [h_{λ_u - μ_v - u + v}]_{u,v ≤ m}`, for a pair of shapes and a size. -/
noncomputable def jacobiTrudiDet (d : ℕ → R) (lam mu : YoungDiagram) (m : ℕ) : R :=
  (Matrix.of fun u v : Fin m => jtCoeff d (lam.rowLen u + v) (mu.rowLen v + u)).det

theorem jtCoeff_eq_shiftedCoeff {d : ℕ → R} {k i j p q : ℕ} (h : p + i = q + j + k) :
    jtCoeff d p q = shiftedCoeff d k i j := by
  unfold jtCoeff shiftedCoeff
  split_ifs with h1 h2 h2
  · congr 1
    omega
  · omega
  · omega
  · rfl

/-- **Half of, proved.**  The Toeplitz minor of is the Jacobi--Trudi determinant of the shapes
builds from its row and column sets.  No positivity, no
alphabet, no hypothesis on `d`: this is the index bookkeeping alone, and it
leaves as a statement about a pair of Young diagrams. -/
theorem toeplitzMinor_eq_jacobiTrudiDet {d : ℕ → R} {n k L Lk : ℕ} (hL : Lk + k = L)
    (hkn : k ≤ n) (hnL : n ≤ Lk) {I : Finset ℕ} (hIn : I ⊆ Finset.range n)
    (hkI : ∀ x, x < k → x ∈ I) :
    toeplitzMinor d k I.card I (tailSet n k I)
      = jacobiTrudiDet d (betaDiagram I L) (betaDiagram (tailSet n k I) Lk) I.card := by
  unfold toeplitzMinor jacobiTrudiDet
  congr 1
  ext u v
  exact (jtCoeff_eq_shiftedCoeff (rowLen_betaDiagram_add hL hkn hnL hIn hkI u.isLt v.isLt)).symm

/-! ## The remaining input

Everything above is bookkeeping.  What still asserts is the
skew Jacobi--Trudi identity itself, for the two-alphabet function of over the alphabet `ρ_D`.  It
is stated here for an arbitrary pair of shapes, so nothing about index sets, Toeplitz matrices or
is left inside it.
-/

/-- ** as an identity of shapes.**  For every pair `μ ⊆ λ`
with `λ` inside `m` rows,

`det [h_{λ_u - μ_v - u + v}]_{u,v ≤ m} = s_{λ/μ}(ρ_D)`,

the right side being the branching sum of in `b` even
and `a` odd variables.

This is not proved here.
`jacobiTrudiDet_eq_superSkewSchur_of_le_one` proves it at `m ≤ 1`, which also
pins down which alphabet `d` has to be: `d m = superHom b a m β α`.  Beyond one
row it is a theorem of Lindström--Gessel--Viennot type that Mathlib carries no
ingredient of — it has no Schur polynomials, no Jacobi--Trudi, no
Lindström--Gessel--Viennot, and no Cauchy--Binet, so both the tableau route and
the linear-algebra route have to be built from `Matrix.det` upward.

That is done, for the even alphabet, over `LGV`, `LGVInvolution`, `LGVTableau`
and `LGVTableauM`: `LGVTableauM.skewJacobiTrudi_even` is this predicate at
`a = 0`, for every commutative ring, every `b`, every `β α`, every `mu ≤ lam`
and every `m`.

With an odd alphabet it is reached too, at every `m`:
`LGVOddTableauM.skewJacobiTrudi`, over `LGVOdd`'s geometry and splice,
`LGVOddTableau`'s tableau bijection, `LGVMixed`'s cancellation for the mixed
crossing predicate, and `LGVOddTableauM`'s lift of the odd tableau side.  So
`endpoint_order_of_skewJacobiTrudi` below is discharged
(`LGVOddTableauM.endpoint_order_uncond`), and with it on the
appendix's own index sets. -/
def SkewJacobiTrudi (d : ℕ → R) (b a : ℕ) (β α : ℕ → R) : Prop :=
  ∀ (lam mu : YoungDiagram) (m : ℕ), mu ≤ lam → (∀ i, m ≤ i → lam.rowLen i = 0) →
    jacobiTrudiDet d lam mu m = superSkewSchur lam mu b a β α

/-- ** on the appendix's own shapes**, given the identity for
shapes.  The Toeplitz minor `Δ_C` is the two-alphabet skew Schur function of. -/
theorem toeplitzMinor_eq_superSkewSchur {d : ℕ → R} {b a : ℕ} {β α : ℕ → R}
    (hJT : SkewJacobiTrudi d b a β α) {n k L Lk : ℕ} (hL : Lk + k = L) (hkn : k ≤ n)
    (hnL : n ≤ Lk) {I : Finset ℕ} (hIn : I ⊆ Finset.range n) (hkI : ∀ x, x < k → x ∈ I) :
    toeplitzMinor d k I.card I (tailSet n k I)
      = superSkewSchur (betaDiagram I L) (betaDiagram (tailSet n k I) Lk) b a β α := by
  rw [toeplitzMinor_eq_jacobiTrudiDet hL hkn hnL hIn hkI]
  exact hJT _ _ _ (betaDiagram_tailSet_le hL hkn hIn hkI) fun _ hi =>
    rowLen_betaDiagram_of_card_le hi

/-- ** and on the minor.**  `Δ_C`
is positive exactly when `I` satisfies the packing rule
— the form the endpoint-order argument consumes. -/
theorem toeplitzMinor_pos_iff {d : ℕ → ℝ} {b a : ℕ} {β α : ℕ → ℝ}
    (hJT : SkewJacobiTrudi d b a β α) {n k L Lk : ℕ} (hL : Lk + k = L) (hkn : k ≤ n)
    (hnL : n ≤ Lk) (hba : b < a) (hka : k ≤ a) (hβ : ∀ i, i < b → 0 < β i)
    (hα : ∀ i, i < a → 0 < α i) {I : Finset ℕ} (hIn : I ⊆ Finset.range n)
    (hkI : ∀ x, x < k → x ∈ I) :
    0 < toeplitzMinor d k I.card I (tailSet n k I) ↔ BlockCondition n k a b I := by
  rw [toeplitzMinor_eq_superSkewSchur hJT hL hkn hnL hIn hkI,
    superSkewSchur_betaDiagram_pos_iff hL hkn hnL hba hka hIn hkI hβ hα]

/-! ## Translating a skew shape

A skew shape and any translate of it carry the same tableaux, because the row
and column conditions of `SkewSSYT` see only the cells.  This is the one
geometric input the one-row case needs: it turns a skew row `(l) / (t)` sitting
in columns `t, …, l-1` into the straight row `(l - t)`, and its conjugate turns
a skew column into a straight one.
-/

section Translate

variable {lam mu lam' mu' : YoungDiagram} {di dj n : ℕ}

/-- Both cells of a row comparison lie in the skew shape: the left one by
hypothesis, the right one because `mu` is a lower set. -/
theorem mem_skewCells_of_row {i j₁ j₂ : ℕ} (hj : j₁ < j₂) (hlam : (i, j₂) ∈ lam)
    (hmu : (i, j₁) ∉ mu) :
    (i, j₁) ∈ skewCells lam mu ∧ (i, j₂) ∈ skewCells lam mu :=
  ⟨mem_skewCells.mpr ⟨lam.up_left_mem le_rfl hj.le hlam, hmu⟩,
    mem_skewCells.mpr ⟨hlam, notMem_of_col_le hj.le hmu⟩⟩

/-- Both cells of a column comparison lie in the skew shape. -/
theorem mem_skewCells_of_col {i₁ i₂ j : ℕ} (hi : i₁ < i₂) (hlam : (i₂, j) ∈ lam)
    (hmu : (i₁, j) ∉ mu) :
    (i₁, j) ∈ skewCells lam mu ∧ (i₂, j) ∈ skewCells lam mu :=
  ⟨mem_skewCells.mpr ⟨lam.up_left_mem hi.le le_rfl hlam, hmu⟩,
    mem_skewCells.mpr ⟨hlam, notMem_of_row_le hi.le hmu⟩⟩

variable (h : ∀ i j, (i, j) ∈ skewCells lam' mu' ↔ (i + di, j + dj) ∈ skewCells lam mu)
  (hlow : ∀ i j, (i, j) ∈ skewCells lam mu → di ≤ i ∧ dj ≤ j)

include h hlow in
theorem mem_skewCells_sub {i j : ℕ} (hc : (i, j) ∈ skewCells lam mu) :
    (i - di, j - dj) ∈ skewCells lam' mu' := by
  obtain ⟨hi, hj⟩ := hlow i j hc
  rw [h, Nat.sub_add_cancel hi, Nat.sub_add_cancel hj]
  exact hc

include h in
/-- Reading a tableau of `lam / mu` at the translated cells. -/
def translateFwd (T : BoundedSkewSSYT lam mu n) : BoundedSkewSSYT lam' mu' n :=
  ⟨{ entry := fun i j => T (i + di) (j + dj)
     row_weak' := by
       intro i j₁ j₂ hj hlam hmu
       obtain ⟨hc1, hc2⟩ := mem_skewCells_of_row hj hlam hmu
       exact T.1.row_weak (by omega) (mem_skewCells.mp ((h i j₂).mp hc2)).1
         (mem_skewCells.mp ((h i j₁).mp hc1)).2
     col_strict' := by
       intro i₁ i₂ j hi hlam hmu
       obtain ⟨hc1, hc2⟩ := mem_skewCells_of_col hi hlam hmu
       exact T.1.col_strict (by omega) (mem_skewCells.mp ((h i₂ j).mp hc2)).1
         (mem_skewCells.mp ((h i₁ j).mp hc1)).2
     zeros' := fun {i j} hc => T.zeros fun hc' => hc ((h i j).mpr hc') },
   fun i j hc => T.2 _ _ ((h i j).mp hc)⟩

include h hlow in
/-- Placing a tableau of the translated shape back on `lam / mu`. -/
def translateBwd (S : BoundedSkewSSYT lam' mu' n) : BoundedSkewSSYT lam mu n :=
  ⟨{ entry := fun i j => if di ≤ i ∧ dj ≤ j then S (i - di) (j - dj) else 0
     row_weak' := by
       intro i j₁ j₂ hj hlam hmu
       obtain ⟨hc1, hc2⟩ := mem_skewCells_of_row hj hlam hmu
       obtain ⟨hi, hj₁⟩ := hlow i j₁ hc1
       obtain ⟨-, hj₂⟩ := hlow i j₂ hc2
       rw [if_pos ⟨hi, hj₁⟩, if_pos ⟨hi, hj₂⟩]
       exact S.1.row_weak (by omega)
         (mem_skewCells.mp (mem_skewCells_sub h hlow hc2)).1
         (mem_skewCells.mp (mem_skewCells_sub h hlow hc1)).2
     col_strict' := by
       intro i₁ i₂ j hi hlam hmu
       obtain ⟨hc1, hc2⟩ := mem_skewCells_of_col hi hlam hmu
       obtain ⟨hi₁, hj⟩ := hlow i₁ j hc1
       obtain ⟨hi₂, -⟩ := hlow i₂ j hc2
       rw [if_pos ⟨hi₁, hj⟩, if_pos ⟨hi₂, hj⟩]
       exact S.1.col_strict (by omega)
         (mem_skewCells.mp (mem_skewCells_sub h hlow hc2)).1
         (mem_skewCells.mp (mem_skewCells_sub h hlow hc1)).2
     zeros' := by
       intro i j hc
       split_ifs with hd
       · refine S.zeros fun hc' => hc ?_
         rw [h, Nat.sub_add_cancel hd.1, Nat.sub_add_cancel hd.2] at hc'
         exact hc'
       · rfl },
   by
     intro i j hc
     change (if di ≤ i ∧ dj ≤ j then S (i - di) (j - dj) else 0) < n
     rw [if_pos (hlow i j hc)]
     exact S.2 _ _ (mem_skewCells_sub h hlow hc)⟩

include h hlow in
/-- The tableaux of a skew shape and of its translate correspond. -/
def translateEquiv : BoundedSkewSSYT lam mu n ≃ BoundedSkewSSYT lam' mu' n where
  toFun := translateFwd h
  invFun := translateBwd h hlow
  left_inv T := by
    refine BoundedSkewSSYT.ext fun i j => ?_
    change (if di ≤ i ∧ dj ≤ j then T (i - di + di) (j - dj + dj) else 0) = T i j
    split_ifs with hd
    · rw [Nat.sub_add_cancel hd.1, Nat.sub_add_cancel hd.2]
    · exact (T.zeros fun hc => hd (hlow i j hc)).symm
  right_inv S := by
    refine BoundedSkewSSYT.ext fun i j => ?_
    change (if di ≤ i + di ∧ dj ≤ j + dj then S (i + di - di) (j + dj - dj) else 0) = S i j
    rw [if_pos ⟨Nat.le_add_left _ _, Nat.le_add_left _ _⟩, Nat.add_sub_cancel,
      Nat.add_sub_cancel]

include h hlow in
/-- **Translation invariance of the skew Schur polynomial.**  A skew shape and
a translate of it have the same generating function. -/
theorem skewSchur_translate (x : ℕ → R) : skewSchur lam mu n x = skewSchur lam' mu' n x := by
  refine Fintype.sum_equiv (translateEquiv h hlow) _ _ fun T => ?_
  refine Finset.prod_nbij' (fun c => (c.1 - di, c.2 - dj)) (fun c => (c.1 + di, c.2 + dj))
    (fun c hc => mem_skewCells_sub h hlow hc) (fun c hc => (h c.1 c.2).mp hc)
    (fun c hc => ?_) (fun _ _ => by simp) (fun c hc => ?_)
  · obtain ⟨h1, h2⟩ := hlow c.1 c.2 hc
    simp [Nat.sub_add_cancel h1, Nat.sub_add_cancel h2]
  · obtain ⟨h1, h2⟩ := hlow c.1 c.2 hc
    change x (T c.1 c.2) = x (T (c.1 - di + di) (c.2 - dj + dj))
    rw [Nat.sub_add_cancel h1, Nat.sub_add_cancel h2]

end Translate

/-! ## Rectangles of one row and one column on a one-row skew shape needs the interval of Young
diagrams between two one-row shapes, which is an interval of naturals.  These
lemmas are the dictionary.
-/

theorem rowLen_rect_of_lt {n k i : ℕ} (hi : i < n) : (rect n k).rowLen i = k := by
  have key : ∀ j : ℕ, (i, j) ∈ rect n k ↔ j < k := by
    intro j
    rw [mem_rect]
    omega
  have h1 := key ((rect n k).rowLen i)
  have h2 := key k
  rw [YoungDiagram.mem_iff_lt_rowLen] at h1 h2
  omega

theorem rowLen_rect_of_le {n k i : ℕ} (hi : n ≤ i) : (rect n k).rowLen i = 0 := by
  by_contra hc
  have hmem : (i, 0) ∈ rect n k := YoungDiagram.mem_iff_lt_rowLen.mpr (Nat.pos_of_ne_zero hc)
  exact absurd (mem_rect.mp hmem).1 (by omega)

theorem transpose_rect (n k : ℕ) : (rect n k).transpose = rect k n := by
  refine cells_injective (Finset.ext fun c => ?_)
  obtain ⟨i, j⟩ := c
  simp only [YoungDiagram.mem_cells, YoungDiagram.mem_transpose, Prod.swap_prod_mk, mem_rect]
  omega

theorem rect_mono_right {n k₁ k₂ : ℕ} (h : k₁ ≤ k₂) : rect n k₁ ≤ rect n k₂ := by
  intro c hc
  obtain ⟨i, j⟩ := c
  obtain ⟨hi, hj⟩ := mem_rect.mp hc
  exact mem_rect.mpr ⟨hi, by omega⟩

theorem colLen_bot (j : ℕ) : (⊥ : YoungDiagram).colLen j = 0 := by
  by_contra hc
  exact YoungDiagram.notMem_bot (0, j)
    (YoungDiagram.mem_iff_lt_colLen.mpr (Nat.pos_of_ne_zero hc))

/-- Row lengths are monotone in the diagram. -/
theorem rowLen_mono {mu lam : YoungDiagram} (h : mu ≤ lam) (i : ℕ) :
    mu.rowLen i ≤ lam.rowLen i := by
  by_contra hc
  have hmem : (i, lam.rowLen i) ∈ mu := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
  exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp (h hmem)) (by omega)

theorem eq_bot_of_rowLen {lam : YoungDiagram} (h : ∀ i, lam.rowLen i = 0) : lam = ⊥ := by
  refine cells_injective (Finset.ext fun c => ?_)
  obtain ⟨i, j⟩ := c
  simp only [YoungDiagram.mem_cells]
  constructor
  · intro hc
    rw [YoungDiagram.mem_iff_lt_rowLen, h i] at hc
    omega
  · intro hc
    exact absurd hc (YoungDiagram.notMem_bot _)

theorem rect_zero_right (n : ℕ) : rect n 0 = ⊥ :=
  eq_bot_of_rowLen fun i => by
    rcases lt_or_ge i n with hi | hi
    · exact rowLen_rect_of_lt hi
    · exact rowLen_rect_of_le hi

theorem rect_zero_left (k : ℕ) : rect 0 k = ⊥ :=
  eq_bot_of_rowLen fun i => rowLen_rect_of_le (Nat.zero_le i)

/-- A diagram with only its first row nonempty is a one-row rectangle. -/
theorem eq_rect_one {lam : YoungDiagram} (h : ∀ i, 1 ≤ i → lam.rowLen i = 0) :
    lam = rect 1 (lam.rowLen 0) := by
  refine cells_injective (Finset.ext fun c => ?_)
  obtain ⟨i, j⟩ := c
  rw [YoungDiagram.mem_cells, YoungDiagram.mem_cells, mem_rect, YoungDiagram.mem_iff_lt_rowLen]
  constructor
  · intro hc
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · exact ⟨Nat.zero_lt_one, hc⟩
    · rw [h i hi] at hc
      omega
  · rintro ⟨hi, hj⟩
    obtain rfl : i = 0 := by omega
    exact hj

/-- A diagram squeezed between two one-row rectangles is a one-row rectangle
with the intermediate length. -/
theorem eq_rect_one_of_le {t l : ℕ} {nu : YoungDiagram} (h1 : rect 1 t ≤ nu)
    (h2 : nu ≤ rect 1 l) : nu = rect 1 (nu.rowLen 0) ∧ t ≤ nu.rowLen 0 ∧ nu.rowLen 0 ≤ l := by
  have hrow : ∀ i, 1 ≤ i → nu.rowLen i = 0 := by
    intro i hi
    by_contra hc
    have hmem : (i, 0) ∈ nu := YoungDiagram.mem_iff_lt_rowLen.mpr (Nat.pos_of_ne_zero hc)
    exact absurd (mem_rect.mp (h2 hmem)).1 (by omega)
  refine ⟨eq_rect_one hrow, ?_, ?_⟩
  · have := rowLen_mono h1 0
    rwa [rowLen_rect_of_lt Nat.zero_lt_one] at this
  · have := rowLen_mono h2 0
    rwa [rowLen_rect_of_lt Nat.zero_lt_one] at this

/-! ## The alphabet of

`ρ_D` is fixed by `∑_m h_m(ρ_D) z^m = D(z)`.  With `D` rational and normalized,
`h_m(ρ_D) = ∑_{p+q=m} h_p(β) e_q(α)`; `superHom` is that sum, `completeHom` and
`elemHom` its factors, each defined as the skew Schur function it is.
-/

/-- `h_p(β_0, …, β_{b-1})`, the one-row Schur polynomial. -/
noncomputable def completeHom (b p : ℕ) (β : ℕ → R) : R := skewSchur (rect 1 p) ⊥ b β

/-- `e_q(α_0, …, α_{a-1})`, the one-column Schur polynomial. -/
noncomputable def elemHom (a q : ℕ) (α : ℕ → R) : R := skewSchur (rect q 1) ⊥ a α

/-- `h_m(ρ_D) = ∑_{p+q=m} h_p(β) e_q(α)`, the coefficient `d_m` of the two-alphabet
specialization in `b` even and `a` odd variables. -/
noncomputable def superHom (b a m : ℕ) (β α : ℕ → R) : R :=
  ∑ p ∈ Finset.range (m + 1), completeHom b p β * elemHom a (m - p) α

/-- An empty skew shape has one tableau and it contributes the empty product. -/
theorem skewSchur_of_skewCells_eq_empty {lam mu : YoungDiagram} (h : skewCells lam mu = ∅)
    (n : ℕ) (x : ℕ → R) : skewSchur lam mu n x = 1 := by
  haveI : Unique (BoundedSkewSSYT lam mu n) :=
    { default := BoundedSkewSSYT.ofEmpty lam mu n h
      uniq := fun T => BoundedSkewSSYT.eq_of_skewCells_eq_empty h T _ }
  unfold skewSchur
  rw [Finset.sum_congr rfl fun T _ =>
    Finset.prod_eq_one fun c hc => absurd (h ▸ hc) (Finset.notMem_empty c)]
  simp

theorem completeHom_zero (b : ℕ) (β : ℕ → R) : completeHom b 0 β = 1 := by
  rw [completeHom, rect_zero_right,
    skewSchur_of_skewCells_eq_empty (skewCells_eq_empty_iff.mpr le_rfl)]

theorem elemHom_zero (a : ℕ) (α : ℕ → R) : elemHom a 0 α = 1 := by
  rw [elemHom, rect_zero_left,
    skewSchur_of_skewCells_eq_empty (skewCells_eq_empty_iff.mpr le_rfl)]

theorem superHom_zero (b a : ℕ) (β α : ℕ → R) : superHom b a 0 β α = 1 := by
  rw [superHom]
  simp [completeHom_zero, elemHom_zero]

/-- In one even variable `h_p` is a power: a recognizability check on
`completeHom`. -/
theorem completeHom_one_var (p : ℕ) (β : ℕ → R) : completeHom 1 p β = β 0 ^ p := by
  rw [completeHom, skewSchur_bot, schur_rect]
  simp

/-- The top elementary symmetric polynomial is the full product: a
recognizability check on `elemHom`. -/
theorem elemHom_full (a : ℕ) (α : ℕ → R) : elemHom a a α = ∏ i ∈ Finset.range a, α i := by
  rw [elemHom, skewSchur_bot, schur_rect, pow_one]

/-- `e_q` in fewer than `q` variables vanishes: the odd alphabet is exhausted at
`q = a`, which is what makes `superHom` a finite sum in `α`. -/
theorem elemHom_eq_zero_of_lt {a q : ℕ} (h : a < q) (α : ℕ → R) : elemHom a q α = 0 := by
  refine skewSchur_eq_zero_of_lt_skewColLen (j := 0) α ?_
  rw [skewColLen, colLen_rect_of_lt Nat.zero_lt_one, colLen_bot]
  omega

/-! ## The one-row case of skew Jacobi--Trudi

On a skew shape of one row the Jacobi--Trudi determinant is its single entry
`d_{λ_0 - μ_0}`, and the branching sum runs over the
one-row shapes between `μ` and `λ`.  Matching them is the identity
`h_m(ρ_D) = ∑_{p+q=m} h_p(β) e_q(α)`, which is how `superHom` is defined.
-/

/-- A skew row `(l) / (t)` is a straight row `(l - t)` moved `t` columns right. -/
theorem skewSchur_rect_row {l t b : ℕ} (htl : t ≤ l) (β : ℕ → R) :
    skewSchur (rect 1 l) (rect 1 t) b β = completeHom b (l - t) β := by
  refine skewSchur_translate (di := 0) (dj := t) (fun i j => ?_) (fun i j hc => ?_) β
  · simp only [mem_skewCells, mem_rect, YoungDiagram.notMem_bot, not_false_eq_true, and_true,
      Nat.add_zero, not_and, not_lt]
    omega
  · simp only [mem_skewCells, mem_rect, not_and, not_lt] at hc
    omega

/-- A skew column `(1^l) / (1^t)` is a straight column `(1^{l-t})` moved `t`
rows down. -/
theorem skewSchur_rect_col {l t a : ℕ} (htl : t ≤ l) (α : ℕ → R) :
    skewSchur (rect l 1) (rect t 1) a α = elemHom a (l - t) α := by
  refine skewSchur_translate (di := t) (dj := 0) (fun i j => ?_) (fun i j hc => ?_) α
  · simp only [mem_skewCells, mem_rect, YoungDiagram.notMem_bot, not_false_eq_true, and_true,
      Nat.add_zero, not_and, not_lt]
    omega
  · simp only [mem_skewCells, mem_rect, not_and, not_lt] at hc
    omega

/-- **The branching sum on a one-row skew shape.**  The sum over `(t) ⊆ ν ⊆ (l)` is
`∑_{p+q=l-t} h_p(β) e_q(α)`, the coefficient `d_{l-t}` of the super alphabet. -/
theorem superSkewSchur_rect_row {l t b a : ℕ} (htl : t ≤ l) (β α : ℕ → R) :
    superSkewSchur (rect 1 l) (rect 1 t) b a β α = superHom b a (l - t) β α := by
  rw [superSkewSchur_eq_branching _ _ _ _ _ _ (rect_mono_right htl), superHom]
  refine Finset.sum_nbij' (fun nu => nu.rowLen 0 - t) (fun p => rect 1 (t + p))
    (fun nu hnu => ?_) (fun p hp => ?_) (fun nu hnu => ?_) (fun p hp => ?_) (fun nu hnu => ?_)
  · obtain ⟨h1, h2⟩ := mem_youngIcc.mp hnu
    obtain ⟨-, -, hsl⟩ := eq_rect_one_of_le h1 h2
    exact Finset.mem_range.mpr (by omega)
  · refine mem_youngIcc.mpr ⟨rect_mono_right (by omega), rect_mono_right ?_⟩
    have := Finset.mem_range.mp hp
    omega
  · obtain ⟨h1, h2⟩ := mem_youngIcc.mp hnu
    obtain ⟨hnu', hts, -⟩ := eq_rect_one_of_le h1 h2
    rw [Nat.add_sub_cancel' hts, ← hnu']
  · rw [rowLen_rect_of_lt Nat.zero_lt_one, Nat.add_sub_cancel_left]
  · obtain ⟨h1, h2⟩ := mem_youngIcc.mp hnu
    obtain ⟨hnu', hts, hsl⟩ := eq_rect_one_of_le h1 h2
    rw [hnu', rowLen_rect_of_lt Nat.zero_lt_one, transpose_rect, transpose_rect,
      skewSchur_rect_row hts, skewSchur_rect_col hsl,
      show l - t - (nu.rowLen 0 - t) = l - nu.rowLen 0 by omega]

theorem jacobiTrudiDet_zero (d : ℕ → R) (lam mu : YoungDiagram) :
    jacobiTrudiDet d lam mu 0 = 1 :=
  Matrix.det_isEmpty

theorem jacobiTrudiDet_one (d : ℕ → R) (lam mu : YoungDiagram) :
    jacobiTrudiDet d lam mu 1 = jtCoeff d (lam.rowLen 0) (mu.rowLen 0) := by
  simp [jacobiTrudiDet]

theorem superSkewSchur_bot_bot (b a : ℕ) (β α : ℕ → R) :
    superSkewSchur (⊥ : YoungDiagram) ⊥ b a β α = 1 := by
  rw [superSkewSchur_eq_branching _ _ _ _ _ _ le_rfl,
    Finset.sum_eq_single_of_mem ⊥ (mem_youngIcc.mpr ⟨le_rfl, le_rfl⟩)]
  · rw [skewSchur_of_skewCells_eq_empty (skewCells_eq_empty_iff.mpr le_rfl),
      skewSchur_of_skewCells_eq_empty (skewCells_eq_empty_iff.mpr le_rfl), one_mul]
  · intro nu hnu hne
    exact absurd (le_antisymm (mem_youngIcc.mp hnu).2 (mem_youngIcc.mp hnu).1) hne

/-- **`SkewJacobiTrudi` at one row, proved.**  For a skew shape inside one row
the determinant of is its single entry `d_{λ_0 - μ_0}`, and
the branching sum is `superHom b a (λ_0 - μ_0) β α`.  So the identity holds
exactly when `d` is the alphabet `ρ_D` of the appendix, `d_m = ∑_{p+q=m} h_p(β)
e_q(α)`; that hypothesis is what `hd` says.

This is the rung the general statement is built from, and it also settles what
the general statement is *about*: no other sequence `d` can satisfy
`SkewJacobiTrudi`, since one-row shapes already force `d`. -/
theorem jacobiTrudiDet_eq_superSkewSchur_of_le_one {d : ℕ → R} {b a : ℕ} {β α : ℕ → R}
    (hd : ∀ m, d m = superHom b a m β α) {lam mu : YoungDiagram} {m : ℕ} (hm : m ≤ 1)
    (hmu : mu ≤ lam) (hrow : ∀ i, m ≤ i → lam.rowLen i = 0) :
    jacobiTrudiDet d lam mu m = superSkewSchur lam mu b a β α := by
  interval_cases m
  · obtain rfl : lam = ⊥ := eq_bot_of_rowLen fun i => hrow i (Nat.zero_le i)
    obtain rfl : mu = ⊥ := le_bot_iff.mp hmu
    rw [jacobiTrudiDet_zero, superSkewSchur_bot_bot]
  · have hmrow : ∀ i, 1 ≤ i → mu.rowLen i = 0 := fun i hi =>
      Nat.le_zero.mp (hrow i hi ▸ rowLen_mono hmu i)
    have hlam : lam = rect 1 (lam.rowLen 0) := eq_rect_one hrow
    have hmu2 : mu = rect 1 (mu.rowLen 0) := eq_rect_one hmrow
    have htl : mu.rowLen 0 ≤ lam.rowLen 0 := rowLen_mono hmu 0
    calc jacobiTrudiDet d lam mu 1
        = superHom b a (lam.rowLen 0 - mu.rowLen 0) β α := by
          rw [jacobiTrudiDet_one, jtCoeff, if_pos htl, hd]
      _ = superSkewSchur (rect 1 (lam.rowLen 0)) (rect 1 (mu.rowLen 0)) b a β α :=
          (superSkewSchur_rect_row htl β α).symm
      _ = superSkewSchur lam mu b a β α := by rw [← hlam, ← hmu2]

/-- ** at `m_C ≤ 1`, unconditionally.**  A row set of at most
one element gives a `1 × 1` minor `d_{k + j - i}`, and that is the skew Schur
function of the shapes builds.  No `SkewJacobiTrudi`
hypothesis is carried. -/
theorem toeplitzMinor_eq_superSkewSchur_of_card_le_one {d : ℕ → R} {b a : ℕ} {β α : ℕ → R}
    (hd : ∀ m, d m = superHom b a m β α) {n k L Lk : ℕ} (hL : Lk + k = L) (hkn : k ≤ n)
    (hnL : n ≤ Lk) {I : Finset ℕ} (hIn : I ⊆ Finset.range n) (hkI : ∀ x, x < k → x ∈ I)
    (hcard : I.card ≤ 1) :
    toeplitzMinor d k I.card I (tailSet n k I)
      = superSkewSchur (betaDiagram I L) (betaDiagram (tailSet n k I) Lk) b a β α := by
  rw [toeplitzMinor_eq_jacobiTrudiDet hL hkn hnL hIn hkI]
  exact jacobiTrudiDet_eq_superSkewSchur_of_le_one hd hcard
    (betaDiagram_tailSet_le hL hkn hIn hkI) fun _ hi => rowLen_betaDiagram_of_card_le hi

/-! ## Non-vacuity -/

/-- A `1 × 1` minor of is the entry itself. -/
theorem toeplitzMinor_one (d : ℕ → R) (k : ℕ) (I J : Finset ℕ) :
    toeplitzMinor d k 1 I J = shiftedCoeff d k (nthElem I 0) (nthElem J 0) := by
  simp [toeplitzMinor]

theorem nthElem_singleton (i : ℕ) : nthElem {i} 0 = i := by
  have hmem := nthElem_mem (I := ({i} : Finset ℕ)) (v := 0) (by simp)
  simpa using hmem

/-- The smallest instance of, evaluated: the `1 × 1` minor
on rows `{i}` and columns `{j}` is `d_{k + j - i}`. -/
theorem toeplitzMinor_singleton (d : ℕ → R) (k i j : ℕ) (hij : i ≤ k + j) :
    toeplitzMinor d k 1 {i} {j} = d (k + j - i) := by
  rw [toeplitzMinor_one, nthElem_singleton, nthElem_singleton, shiftedCoeff, if_pos hij]

end Shields
