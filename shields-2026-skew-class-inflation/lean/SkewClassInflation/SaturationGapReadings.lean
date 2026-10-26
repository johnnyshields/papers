/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.SaturationChains
import SkewClassInflation.JoinGapProducts

/-!
# Full gap readings of arbitrary repeated-inner sources

The gap multiplicities and maximal-cofactor clauses of
`eq:saturation-readings` in `shields-2026-skew-class-inflation.tex`.
The distinguished larger seam is retained at each outer cut; the internal
gap may be zero.  Sorry-free.
-/

namespace SkewClassInflation.SaturationInner

open SkewJacobiNegative
open scoped BigOperators

variable (A : SaturationInner)

/-- Every multiplicative reading separates the actual internal gaps from the outer seams. -/
theorem chain_gap_product {R : Type*} [CommMonoid R] (f : ℕ → R)
    (a : ℕ) (ha : 0 < a) (l : List ℕ) (hl : ∀ b ∈ l, 0 < b) :
    (∏ j : Fin (A.chain a ha l hl).1, f ((A.chain a ha l hl).2.g j)) =
      f A.c ^ ((a + l.sum) * A.k) * f A.d ^ l.length := by
  induction l generalizing a with
  | nil =>
    change (∏ _ : Fin (a * A.k), f A.c) = _
    simp
  | cons b l ih =>
    let P := A.power a ha
    let Q := A.chain b (hl b List.mem_cons_self) l
      (fun j hj => hl j (List.mem_cons_of_mem _ hj))
    have hp : A.d < P.r (Fin.last (a * A.k)) := A.power_rows_above_seam a ha _
    have hq : A.d < Q.2.r 0 := by
      rw [A.chain_first]
      have := A.first_bound
      omega
    change (∏ j, f ((Profile.join P Q.2 A.d hp hq).g j)) = _
    rw [Profile.prod_join_gaps]
    have hleft : (∏ j : Fin (a * A.k), f (P.g j)) = f A.c ^ (a * A.k) := by
      simp [P, power]
    have hright := ih b (hl b List.mem_cons_self)
      (fun j hj => hl j (List.mem_cons_of_mem _ hj))
    change (∏ j : Fin Q.1, f (Q.2.g j)) = _ at hright
    rw [hleft, hright]
    simp only [List.sum_cons, List.length_cons]
    have he : (a + (b + l.sum)) * A.k = a * A.k + (b + l.sum) * A.k := by ring
    rw [he, pow_add, pow_succ]
    ac_rfl

/-- Additive readings retain the two gap multiplicities, including all zero internal gaps. -/
theorem chain_gap_sum {R : Type*} [AddCommMonoid R] (f : ℕ → R)
    (a : ℕ) (ha : 0 < a) (l : List ℕ) (hl : ∀ b ∈ l, 0 < b) :
    (∑ j : Fin (A.chain a ha l hl).1, f ((A.chain a ha l hl).2.g j)) =
      ((a + l.sum) * A.k) • f A.c + l.length • f A.d := by
  let g : ℕ → Multiplicative R := fun j => Multiplicative.ofAdd (f j)
  have he := A.chain_gap_product g a ha l hl
  exact congrArg Multiplicative.toAdd he

/-- The complete source gap multiset is read directly from its actual ordered profile. -/
theorem diagram_gap_product {R : Type*} [CommMonoid R] (f : ℕ → R)
    {M : ℕ} (α : Composition M) (hM : 0 < M) :
    (∏ j : Fin (A.diagram α hM).1, f ((A.diagram α hM).2.g j)) =
      f A.c ^ (M * A.k) * f A.d ^ (α.length - 1) := by
  unfold diagram
  split
  · rename_i he
    have hs := α.blocks_sum
    rw [he] at hs
    simp only [List.sum_nil] at hs
    omega
  · rename_i a l he
    have hs : a + l.sum = M := by simpa only [he, List.sum_cons] using α.blocks_sum
    rw [A.chain_gap_product, hs]
    simp only [Composition.length, he, List.length_cons, Nat.add_sub_cancel]

/-- The source's full internal and distinguished gap sum is independent of the outer order. -/
theorem diagram_gap_sum {R : Type*} [AddCommMonoid R] (f : ℕ → R)
    {M : ℕ} (α : Composition M) (hM : 0 < M) :
    (∑ j : Fin (A.diagram α hM).1, f ((A.diagram α hM).2.g j)) =
      (M * A.k) • f A.c + (α.length - 1) • f A.d := by
  let g : ℕ → Multiplicative R := fun j => Multiplicative.ofAdd (f j)
  exact congrArg Multiplicative.toAdd (A.diagram_gap_product g α hM)

/-- The exact number of small gaps includes the zero-gap boundary of the standing domain. -/
theorem diagram_small_gap_count {M : ℕ} (α : Composition M) (hM : 0 < M) :
    (Finset.univ.filter (fun j => (A.diagram α hM).2.g j = A.c)).card = M * A.k := by
  classical
  have he := A.diagram_gap_sum (fun j => if j = A.c then 1 else 0) α hM
  have hdc : A.d ≠ A.c := ne_of_gt A.c_lt_d
  simpa only [Finset.card_filter, hdc, ite_true, ite_false, smul_eq_mul, mul_one,
    mul_zero, add_zero] using he

/-- Every outer cut contributes exactly one larger distinguished seam. -/
theorem diagram_large_gap_count {M : ℕ} (α : Composition M) (hM : 0 < M) :
    (Finset.univ.filter (fun j => (A.diagram α hM).2.g j = A.d)).card = α.length - 1 := by
  classical
  have he := A.diagram_gap_sum (fun j => if j = A.d then 1 else 0) α hM
  have hcd : A.c ≠ A.d := ne_of_lt A.c_lt_d
  simpa only [Finset.card_filter, hcd, ite_true, ite_false, smul_eq_mul, mul_one,
    mul_zero, zero_add] using he

/-- The actual unsigned maximal cofactor reads every original overlap strip and larger seam. -/
theorem diagram_cofactor {M : ℕ} (α : Composition M) (hM : 0 < M) :
    (A.diagram α hM).2.toBetaDiagram.cornerPolynomial =
      complete A.c ^ (M * A.k) * complete A.d ^ (α.length - 1) := by
  rw [Staircase.cornerPolynomial_eq_gapMonomial (A.diagram_thick α hM)]
  exact A.diagram_gap_product (fun j => complete (j : ℤ)) α hM

/-- The signed maximal-generator coefficient has the exact parity of the full source row count. -/
theorem diagram_corner_coefficient {M : ℕ} (α : Composition M) (hM : 0 < M) :
    (-1 : CompleteRing) ^ (A.diagram α hM).1 *
      (A.diagram α hM).2.toBetaDiagram.cornerCoefficient =
      complete A.c ^ (M * A.k) * complete A.d ^ (α.length - 1) := by
  rw [BetaDiagram.cornerCoefficient, A.diagram_cofactor, ← mul_assoc, ← pow_add,
    ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

end SkewClassInflation.SaturationInner
