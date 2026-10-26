/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.JoinGapProducts
import SkewClassInflation.ThinBetaSets
import SkewClassInflation.CellProfiles

/-!
# Complete weight and maximal-cofactor readings of the thin source

Formalizes the remaining weight and cofactor clauses of
`eq:thin-readings` in `shields-2026-skew-class-inflation.tex`.
The full gap sum and product are produced from the literal ordered
source construction, including all zero seams.  The full span then
recovers the actual total number of cells.  Sorry-free.
-/

namespace SkewClassInflation.ThinParameters

open SkewJacobiNegative
open scoped BigOperators

variable (B : ThinParameters)

/-- Every original internal gap contributes its copy multiplicity to the full gap sum. -/
theorem chain_gap_sum (a : ℕ) (ha : 0 < a) (l : List ℕ) (hl : ∀ b ∈ l, 0 < b) :
    (∑ j : Fin (B.chain a ha l hl).1, ((B.chain a ha l hl).2.g j : ℤ)) =
      ((a + l.sum : ℕ) : ℤ) * B.c := by
  induction l generalizing a with
  | nil =>
    change (∑ _j : Fin a, (B.c : ℤ)) = ((a + [].sum : ℕ) : ℤ) * B.c
    simp
  | cons b l ih =>
    let R := B.chain b (hl b List.mem_cons_self) l
      (fun j hj => hl j (List.mem_cons_of_mem _ hj))
    change (∑ j, ((Profile.join (B.innerPower a ha) R.2 0
      ((B.innerPower a ha).r_pos _) (R.2.r_pos _)).g j : ℤ)) = _
    rw [Profile.sum_join_gaps]
    have hleft : (∑ j : Fin a, ((B.innerPower a ha).g j : ℤ)) = (a : ℤ) * B.c := by
      simp [innerPower]
    have hright := ih b (hl b List.mem_cons_self)
      (fun j hj => hl j (List.mem_cons_of_mem _ hj))
    change (∑ j : Fin R.1, (R.2.g j : ℤ)) = ((b + l.sum : ℕ) : ℤ) * B.c at hright
    rw [hleft, hright]
    simp only [Nat.cast_zero, add_zero, List.sum_cons, Nat.cast_add]
    ring

/-- The actual full gap sum is independent of the chosen outer order and length. -/
theorem diagram_gap_sum {M : ℕ} (α : Composition M) (hM : 0 < M) :
    (∑ j : Fin (B.diagram α hM).1, ((B.diagram α hM).2.g j : ℤ)) = (M : ℤ) * B.c := by
  unfold diagram
  split
  · rename_i he
    have hs := α.blocks_sum
    rw [he] at hs
    simp only [List.sum_nil] at hs
    omega
  · rename_i a l he
    have hs : a + l.sum = M := by simpa only [he, List.sum_cons] using α.blocks_sum
    rw [B.chain_gap_sum, hs]

/-- The full actual diagram has exactly the manuscript's total cell weight. -/
theorem diagram_row_weight {M : ℕ} (α : Composition M) (hM : 0 < M) :
    (∑ i : Fin ((B.diagram α hM).1 + 1), ((B.diagram α hM).2.r i : ℤ)) =
      (M : ℤ) * ((B.a : ℤ) + B.b) := by
  have he := profile_span_sum (B.diagram α hM).2
  rw [B.diagram_span, B.diagram_gap_sum] at he
  have hq := B.boundary_q_eq
  nlinarith

/-- Zero joins retain every original positive gap factor and contribute only the unit. -/
theorem chain_gap_monomial (a : ℕ) (ha : 0 < a) (l : List ℕ) (hl : ∀ b ∈ l, 0 < b) :
    Staircase.gapMonomial (B.chain a ha l hl).2 = complete B.c ^ (a + l.sum) := by
  induction l generalizing a with
  | nil =>
    change (∏ _j : Fin a, complete B.c) = complete B.c ^ (a + [].sum)
    simp
  | cons b l ih =>
    let R := B.chain b (hl b List.mem_cons_self) l
      (fun j hj => hl j (List.mem_cons_of_mem _ hj))
    change (∏ j, complete ((Profile.join (B.innerPower a ha) R.2 0
      ((B.innerPower a ha).r_pos _) (R.2.r_pos _)).g j)) = _
    rw [Profile.prod_join_gaps (B.innerPower a ha) R.2 0
      ((B.innerPower a ha).r_pos _) (R.2.r_pos _) (fun u : ℕ => complete (u : ℤ))]
    have hleft : (∏ j : Fin a, complete ((B.innerPower a ha).g j)) = complete B.c ^ a := by
      simp [innerPower]
    have hright := ih b (hl b List.mem_cons_self)
      (fun j hj => hl j (List.mem_cons_of_mem _ hj))
    change (∏ j : Fin R.1, complete (R.2.g j)) = complete B.c ^ (b + l.sum) at hright
    rw [hleft, hright, Nat.cast_zero, complete_zero, mul_one, ← pow_add]
    congr 1

/-- The actual unsigned maximal cofactor records precisely the total copy multiplicity. -/
theorem diagram_cofactor {M : ℕ} (α : Composition M) (hM : 0 < M) :
    (B.diagram α hM).2.toBetaDiagram.cornerPolynomial = complete B.c ^ M := by
  rw [Staircase.cornerPolynomial_eq_gapMonomial (B.diagram_thick α hM)]
  unfold diagram
  split
  · rename_i he
    have hs := α.blocks_sum
    rw [he] at hs
    simp only [List.sum_nil] at hs
    omega
  · rename_i a l he
    have hs : a + l.sum = M := by simpa only [he, List.sum_cons] using α.blocks_sum
    rw [B.chain_gap_monomial, hs]

/-- The signed maximal-label coefficient has exactly the sign and power displayed in the paper. -/
theorem diagram_corner_coefficient {M : ℕ} (α : Composition M) (hM : 0 < M) :
    (-1 : CompleteRing) ^ (B.diagram α hM).1 *
      (B.diagram α hM).2.toBetaDiagram.cornerCoefficient = complete B.c ^ M := by
  rw [BetaDiagram.cornerCoefficient, B.diagram_cofactor, ← mul_assoc, ← pow_add, ← two_mul,
    pow_mul, neg_one_sq, one_pow, one_mul]

/-- The actual largest generator index is the full total copy span. -/
theorem diagram_largest_label {M : ℕ} (α : Composition M) (hM : 0 < M) :
    (B.diagram α hM).2.toBetaDiagram.largestLabel = (M : ℤ) * B.boundary.q := by
  change (B.diagram α hM).2.xi 0 -
    (B.diagram α hM).2.zeta (Fin.last (B.diagram α hM).1) = _
  rw [Gluing.Profile.zeta_last, sub_zero, B.diagram_span]

/-- Differentiation extracts the entire maximal-generator coefficient, with the displayed sign. -/
theorem diagram_maximal_derivative {M : ℕ} (α : Composition M) (hM : 0 < M) :
    let D := (B.diagram α hM).2.toBetaDiagram
    let j : ℕ+ := ⟨D.largestLabel.toNat, by have := D.largestLabel_pos; omega⟩
    (-1 : CompleteRing) ^ (B.diagram α hM).1 *
      (MvPolynomial.pderiv j D.schur : CompleteRing) = complete B.c ^ M := by
  intro D j
  have hderiv : (MvPolynomial.pderiv j D.schur : CompleteRing) = D.cornerCoefficient :=
    D.pderiv_schur_largest
  rw [hderiv]
  exact B.diagram_corner_coefficient α hM

end SkewClassInflation.ThinParameters
