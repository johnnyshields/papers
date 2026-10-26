/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.SaturationSubstitution

/-!
# Actual total larger-seam contraction of general source mates

The full determinant identity `eq:total-contraction` in
`shields-2026-skew-class-inflation.tex`.  The top larger-generator
coefficient is computed from the literal source recurrence and compared
with the actual contracted full board.  No power-rigidity premise is assumed.
Sorry-free.
-/

namespace SkewClassInflation.SaturationInner

open SkewJacobiNegative SkewJacobiNegative.Staircase

variable (A : SaturationInner)

private theorem power_schur_congr (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (h : m = n) :
    (A.power m hm).toBetaDiagram.schur = (A.power n hn).toBetaDiagram.schur := by
  cases h
  rfl

/-- The distinguished multiplicity counts all and only the actual outer cuts. -/
theorem chain_large_multiplicity (a : ℕ) (ha : 0 < a) (l : List ℕ)
    (hl : ∀ m ∈ l, 0 < m) : minimumMultiplicity (A.chain a ha l hl).2 A.largeLabel = l.length := by
  change (∑ j, if (A.chain a ha l hl).2.g j = A.d then 1 else 0) = _
  have he := A.chain_gap_sum (fun j => if j = A.d then (1 : ℕ) else 0) a ha l hl
  have hcd : A.c ≠ A.d := ne_of_lt A.c_lt_d
  simpa only [hcd, ite_false, ite_true, smul_eq_mul, mul_zero, mul_one, zero_add] using he

/-- The actual polynomial degree is the exact outer-cut multiplicity. -/
theorem chain_large_degree (a : ℕ) (ha : 0 < a) (l : List ℕ) (hl : ∀ m ∈ l, 0 < m) :
    (minimumPolynomial A.largeLabel (A.chain a ha l hl).2.toBetaDiagram.schur).natDegree =
      l.length := by
  rw [distinguished_degree_exact _ (A.chain_thick a ha l hl) A.largeLabel
    (A.chain_rows_above_seam a ha l hl), A.chain_large_multiplicity]

/-- The top source coefficient is the signed actual full power of the total copy order. -/
theorem chain_highest_coefficient (a : ℕ) (ha : 0 < a)
    (l : List ℕ) (hl : ∀ m ∈ l, 0 < m) :
    (minimumPolynomial A.largeLabel (A.chain a ha l hl).2.toBetaDiagram.schur).coeff l.length =
      (-1 : CompleteRing) ^ l.length *
        (A.power (a + l.sum) (by omega)).toBetaDiagram.schur := by
  induction l generalizing a with
  | nil =>
    change (minimumPolynomial A.largeLabel (A.power a ha).toBetaDiagram.schur).coeff 0 = _
    rw [minimumPolynomial_eq_C_of_not_mem _ _ (A.power_excludes_large_label a ha),
      Polynomial.coeff_C_zero]
    simp only [List.length_nil, List.sum_nil, Nat.add_zero, pow_zero, one_mul]
  | cons b l ih =>
    have hb := hl b List.mem_cons_self
    have ht : ∀ m ∈ l, 0 < m := fun m hm => hl m (List.mem_cons_of_mem _ hm)
    have hd : minimumPolynomial A.largeLabel (complete A.d) = Polynomial.X := by
      rw [minimumPolynomial_complete]
      change (if (A.d : ℤ) = (A.d : ℤ) then Polynomial.X else Polynomial.C (complete A.d)) = _
      rw [ite_eq_left rfl]
    have hz : (minimumPolynomial A.largeLabel
        (A.chain b hb l ht).2.toBetaDiagram.schur).coeff (l.length + 1) = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      rw [A.chain_large_degree]
      omega
    rw [A.chain_schur_recurrence a b ha hb l hl, map_sub, map_mul, map_mul,
      minimumPolynomial_eq_C_of_not_mem _ _ (A.power_excludes_large_label a ha), hd]
    simp only [List.length_cons, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_mul]
    rw [hz, ih (a + b) (by omega) ht]
    have hpow := power_schur_congr A (a + b + l.sum) (a + (b :: l).sum)
      (by omega) (by simp only [List.sum_cons]; omega)
      (by simp only [List.sum_cons, Nat.add_assoc])
    rw [hpow, mul_zero, zero_sub, pow_succ]
    ring

/-- The source coefficient has exactly the sign and total power displayed in the manuscript. -/
theorem diagram_highest_coefficient {M : ℕ} (α : Composition M) (hM : 0 < M) :
    (minimumPolynomial A.largeLabel (A.diagram α hM).2.toBetaDiagram.schur).coeff (α.length - 1) =
      (-1 : CompleteRing) ^ (α.length - 1) * (A.power M hM).toBetaDiagram.schur := by
  unfold diagram
  split
  · rename_i he
    have hs := α.blocks_sum
    rw [he] at hs
    simp only [List.sum_nil] at hs
    omega
  · rename_i a l he
    have ha := α.blocks_pos (by rw [he]; exact List.mem_cons_self)
    have hl : ∀ m ∈ l, 0 < m := fun m hm =>
      α.blocks_pos (by rw [he]; exact List.mem_cons_of_mem _ hm)
    have hs : a + l.sum = M := by simpa only [he, List.sum_cons] using α.blocks_sum
    subst M
    simpa only [Composition.length, he, List.length_cons, Nat.add_sub_cancel] using
      A.chain_highest_coefficient a ha l hl

/-- Every actual connected mate contracts to the total power's full Schur function. -/
theorem arbitrary_mate_total_contraction {M n : ℕ} (α : Composition M) (hM : 0 < M)
    (P : Profile n)
    (he : P.toBetaDiagram.schur = (A.diagram α hM).2.toBetaDiagram.schur) :
    (contractAllMinimum P A.largeLabel).2.toBetaDiagram.schur =
      (A.power M hM).toBetaDiagram.schur := by
  have hdata := A.source_mate_reduction α hM P he
  have hm : minimumMultiplicity P A.largeLabel = α.length - 1 := by
    change (∑ j, if P.g j = A.d then 1 else 0) = _
    simpa only [Finset.card_filter] using hdata.2.2.2.2.2
  have ht := distinguished_highest_layer P hdata.2.1 A.largeLabel hdata.2.2.1
  rw [hm, he, A.diagram_highest_coefficient] at ht
  exact mul_left_cancel₀ (pow_ne_zero _ (by norm_num : (-1 : CompleteRing) ≠ 0)) ht.symm

end SkewClassInflation.SaturationInner
