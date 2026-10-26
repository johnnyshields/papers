/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCofactorIndependence.SymmetricCofactors
import SkewCofactorIndependence.FirstVariations
import SkewCofactorIndependence.PrivateEntries
import SkewCofactorIndependence.QuadraticReturns

/-!
# Symmetric first variations

The reflection and representative-independence assertions of
`prop:symmetric-unit-kernel`.  The induction uses the actual normalized
corner diagram, the private largest generator, and the nonzero corner
minor.  In particular it does not assume independence of symmetric cofactors.
-/

noncomputable section
namespace SkewCofactorIndependence
open scoped BigOperators
open StrictTriangularPaths MvPolynomial

/-- A dependent finite sum over a predicate, extended by zero to the ambient type. -/
theorem unit_sum_subtype {ι V : Type*} [Fintype ι] [AddCommMonoid V]
    (P : ι → Prop) [DecidablePred P] (f : {x // P x} → V) :
    (∑ x, if hx : P x then f ⟨x, hx⟩ else 0) = ∑ x : {x // P x}, f x := by
  classical
  let F (x : ι) := if hx : P x then f ⟨x, hx⟩ else 0
  calc
    (∑ x, F x) = ∑ x ∈ Finset.univ.filter P, F x := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro x _ hx
      have hp : ¬ P x := by simpa using hx
      simp [F, hp]
    _ = ∑ x : {x // P x}, f x := by
      apply Finset.sum_bij (fun x hx => ⟨x, (Finset.mem_filter.mp hx).2⟩)
      · intro x hx; exact Finset.mem_univ _
      · intro x hx y hy he; exact congrArg Subtype.val he
      · intro y _
        exact ⟨y.val, by simp [y.property], by apply Subtype.ext; rfl⟩
      · intro x hx
        simp [F, (Finset.mem_filter.mp hx).2]

namespace BetaDiagram
variable {n : ℕ}

/-- The span of a normalized diagram is its first row beta. -/
def unitSpan (D : BetaDiagram (n + 1)) : ℤ := D.row 0

/-- The last column beta is zero in the concrete `Fin` presentation. -/
theorem normalized_last (D : BetaDiagram (n + 1)) (hn : D.Normalized) :
    D.col (Fin.last n) = 0 := by
  have h := hn (by omega)
  have he : (⟨n + 1 - 1, by omega⟩ : Fin (n + 1)) = Fin.last n := by
    apply Fin.ext
    simp
  change D.col ⟨n + 1 - 1, by omega⟩ = 0 at h
  rw [he] at h
  exact h

/-- Normalization identifies the reflection center with the span. -/
theorem normalized_symmetric_betas (D : BetaDiagram (n + 1))
    (hn : D.Normalized) (hs : D.Symmetric) :
    (∀ i, D.row i = D.unitSpan - D.col i.rev) ∧
      (∀ j, D.col j = D.unitSpan - D.row j.rev) := by
  obtain ⟨c, hr, hc⟩ := hs
  have hlast := hc (Fin.last n)
  have hz := D.normalized_last hn
  have hcenter : c = D.unitSpan := by
    simp only [Fin.rev_last] at hlast
    dsimp [unitSpan]
    omega
  simpa [hcenter] using And.intro hr hc

/-- Available positions, with all endpoint exclusions made explicit. -/
theorem mem_availablePositions_iff (D : BetaDiagram (n + 1))
    (hn : D.Normalized) (z : ℤ) :
    z ∈ D.availablePositions ↔
      0 < z ∧ z < D.unitSpan ∧ (∀ i, z ≠ D.row i) ∧ (∀ j, z ≠ D.col j) := by
  classical
  simp [availablePositions, D.normalized_last hn, unitSpan, Finset.mem_image,
    not_exists, and_assoc, eq_comm]

/-- Reflection preserves the actual available-position set. -/
theorem symmetric_available_reflection (D : BetaDiagram (n + 1))
    (hn : D.Normalized) (hs : D.Symmetric) (z : ℤ) :
    D.unitSpan - z ∈ D.availablePositions ↔ z ∈ D.availablePositions := by
  rw [D.mem_availablePositions_iff hn, D.mem_availablePositions_iff hn]
  obtain ⟨hr, hc⟩ := D.normalized_symmetric_betas hn hs
  constructor
  · rintro ⟨h₁, h₂, ha, hb⟩
    refine ⟨by omega, by omega, ?_, ?_⟩
    · intro i he
      apply hb i.rev
      rw [hc, Fin.rev_rev, he]
    · intro j he
      apply ha j.rev
      rw [hr, Fin.rev_rev, he]
  · rintro ⟨h₁, h₂, ha, hb⟩
    refine ⟨by omega, by omega, ?_, ?_⟩
    · intro i he
      apply hb i.rev
      rw [hc, Fin.rev_rev]
      omega
    · intro j he
      apply ha j.rev
      rw [hr, Fin.rev_rev]
      omega

/-- The actual finite position reflection, including a possible midpoint. -/
def availableReflection (D : BetaDiagram (n + 1)) (hn : D.Normalized)
    (hs : D.Symmetric) : D.Available ≃ D.Available where
  toFun z := ⟨D.unitSpan - z.val, (D.symmetric_available_reflection hn hs _).2 z.property⟩
  invFun z := ⟨D.unitSpan - z.val, (D.symmetric_available_reflection hn hs _).2 z.property⟩
  left_inv z := by apply Subtype.ext; dsimp; omega
  right_inv z := by apply Subtype.ext; dsimp; omega

@[simp] theorem availableReflection_val (D : BetaDiagram (n + 1))
    (hn : D.Normalized) (hs : D.Symmetric) (z : D.Available) :
    (D.availableReflection hn hs z).val = D.unitSpan - z.val := rfl

/-- Fixed points are precisely the available midpoint. -/
theorem availableReflection_fixed_iff (D : BetaDiagram (n + 1))
    (hn : D.Normalized) (hs : D.Symmetric) (z : D.Available) :
    D.availableReflection hn hs z = z ↔ 2 * z.val = D.unitSpan := by
  rw [Subtype.ext_iff]
  simp only [availableReflection_val]
  omega

/-- One unit per reflection orbit; the midpoint is included, not discarded. -/
abbrev UnitRepresentative (D : BetaDiagram (n + 1)) :=
  {z : D.Available // 2 * z.val ≤ D.unitSpan}

/-- Reflection agrees on actual first-variation polynomials at every integer position. -/
theorem symmetric_unitVariation (D : BetaDiagram (n + 1))
    (hn : D.Normalized) (hs : D.Symmetric) (z : ℤ) :
    D.unitVariation (D.unitSpan - z) = D.unitVariation z := by
  classical
  obtain ⟨hr, hc⟩ := D.normalized_symmetric_betas hn hs
  unfold unitVariation
  rw [Finset.sum_comm]
  rw [← Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin (n + 1)))]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin (n + 1)))]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Fin.revPerm_apply]
  rw [D.symmetric_cofactor_eq hs i.rev j.rev, Fin.rev_rev, Fin.rev_rev]
  have h₁ : positiveGap complete (D.row i.rev) (D.unitSpan - z) =
      positiveGap complete z (D.col i) := by
    rw [hr, Fin.rev_rev]
    by_cases h : D.col i < z
    · rw [positiveGap_of_lt complete h,
        positiveGap_of_lt complete (show D.unitSpan - z < D.unitSpan - D.col i by omega)]
      congr 1
      ring
    · rw [positiveGap_of_le complete (show z ≤ D.col i by omega),
        positiveGap_of_le complete (show D.unitSpan - D.col i ≤ D.unitSpan - z by omega)]
  have h₂ : positiveGap complete (D.unitSpan - z) (D.col j.rev) =
      positiveGap complete (D.row j) z := by
    rw [hc, Fin.rev_rev]
    by_cases h : z < D.row j
    · rw [positiveGap_of_lt complete h,
        positiveGap_of_lt complete (show D.unitSpan - D.row j < D.unitSpan - z by omega)]
      congr 1
      ring
    · rw [positiveGap_of_le complete (show D.row j ≤ z by omega),
        positiveGap_of_le complete (show D.unitSpan - z ≤ D.unitSpan - D.row j by omega)]
  rw [h₁, h₂]
  ring

/-- The positive generator belonging to a positive integer index. -/
def unitGenerator (k : ℤ) (hk : 0 < k) : ℕ+ := ⟨k.toNat, by omega⟩

@[simp] theorem unitGenerator_cast (k : ℤ) (hk : 0 < k) :
    ((unitGenerator k hk).val : ℤ) = k := by simp [unitGenerator]; omega

/-- A different complete-generator label differentiates to zero. -/
theorem pderiv_complete_of_ne (v : ℕ+) (k : ℤ) (h : k ≠ (v.val : ℤ)) :
    pderiv v (complete k) = 0 := by
  apply pderiv_eq_zero_of_notMem_vars
  rw [mem_vars_complete_iff]
  exact Ne.symm h

/-- A strict return differentiates to zero if its positive label is not the variable. -/
theorem pderiv_positiveGap_of_ne (v : ℕ+) (a b : ℤ)
    (h : a - b ≠ (v.val : ℤ)) : pderiv v (positiveGap complete a b) = 0 := by
  unfold positiveGap
  split_ifs
  · exact pderiv_complete_of_ne v _ h
  · exact map_zero _

set_option backward.isDefEq.respectTransparency false in
/-- The one-row formula contains the actual empty cofactor, equal to one. -/
theorem unitVariation_order_one (D : BetaDiagram 1) (hn : D.Normalized)
    (z : D.Available) :
    D.unitVariation z.val = complete (D.unitSpan - z.val) * complete z.val := by
  have hz := (D.mem_availablePositions_iff hn z.val).1 z.property
  have hcol : D.col 0 = 0 := by
    have hh := D.normalized_last hn
    have he : (Fin.last 0 : Fin 1) = 0 := by apply Fin.ext; rfl
    rw [he] at hh
    exact hh
  have hrow : z.val < D.row 0 := hz.2.1
  unfold unitVariation
  rw [Fin.sum_univ_one (fun i : Fin 1 =>
    ∑ j : Fin 1, D.cofactor i j * positiveGap complete (D.row i) z.val *
      positiveGap complete z.val (D.col j))]
  rw [Fin.sum_univ_one (fun j : Fin 1 =>
    D.cofactor 0 j * positiveGap complete (D.row 0) z.val *
      positiveGap complete z.val (D.col j))]
  rw [D.cofactor_order_one, one_mul]
  rw [hcol, positiveGap_of_lt complete hrow, positiveGap_of_lt complete hz.1,
    sub_zero]; rfl

/-- Distinct representatives of a one-row core give distinct actual monomials. -/
theorem one_row_returnExponent_injective (D : BetaDiagram 1) (hn : D.Normalized) :
    Function.Injective (fun z : D.UnitRepresentative =>
      returnExponent 0 D.unitSpan z.val.val
        ⟨((D.mem_availablePositions_iff hn _).1 z.val.property).1,
          ((D.mem_availablePositions_iff hn _).1 z.val.property).2.1⟩) := by
  intro z w he
  have hz := (D.mem_availablePositions_iff hn _).1 z.val.property
  have hw := (D.mem_availablePositions_iff hn _).1 w.val.property
  have hh := (returnExponent_eq_iff 0 D.unitSpan z.val.val w.val.val
    ⟨hz.1, hz.2.1⟩ ⟨hw.1, hw.2.1⟩).1 he
  apply Subtype.ext
  apply Subtype.ext
  rcases hh with hh | hh
  · exact hh.symm
  · have hzrep := z.property
    have hwrep := w.property
    omega

/-- Rational independence in the order-one auxiliary case, including its midpoint. -/
theorem symmetric_units_order_one_independent (D : BetaDiagram 1)
    (hn : D.Normalized) :
    LinearIndependent ℚ (fun z : D.UnitRepresentative => D.unitVariation z.val.val) := by
  classical
  apply Fintype.linearIndependent_iff.2
  intro c he z
  let d (w : D.UnitRepresentative) := returnExponent 0 D.unitSpan w.val.val
    ⟨((D.mem_availablePositions_iff hn _).1 w.val.property).1,
      ((D.mem_availablePositions_iff hn _).1 w.val.property).2.1⟩
  have term (w : D.UnitRepresentative) :
      c w • D.unitVariation w.val.val = monomial (d w) (c w) := by
    rw [D.unitVariation_order_one hn]
    have hw := (D.mem_availablePositions_iff hn _).1 w.val.property
    rw [complete_of_pos (by omega), complete_of_pos hw.1]
    change c w • ((monomial (Finsupp.single _ 1) 1 : CompleteRing) *
      monomial (Finsupp.single _ 1) 1) = _
    rw [monomial_mul_monomial, smul_monomial]
    simp [d, returnExponent]
  have hd := D.one_row_returnExponent_injective hn
  have hh := congrArg (fun p : CompleteRing => p.coeff (d z)) he
  simp only [coeff_sum, term, coeff_monomial, AddMonoidAlgebra.coeff_zero,
    Finsupp.zero_apply] at hh
  have hcollision : ∀ w, d w = d z ↔ w = z := fun w => hd.eq_iff
  simp only [hcollision] at hh
  simpa using hh

/-- The translation removed from the dense symmetric corner. -/
def symmetricStep (D : BetaDiagram (n + 2)) : ℤ := D.col (Fin.last n).castSucc

/-- The actual corner child, normalized by subtracting its last column beta. -/
def symmetricChild (D : BetaDiagram (n + 2)) (hd : D.Dense) : BetaDiagram (n + 1) where
  row i := D.row i.succ - D.symmetricStep
  col j := D.col j.castSucc - D.symmetricStep
  row_strictAnti := by
    intro i j hij
    have hh := D.row_strictAnti (Fin.strictMono_succ hij)
    dsimp
    omega
  col_strictAnti := by
    intro i j hij
    have hh := D.col_strictAnti (Fin.strictMono_castSucc hij)
    dsimp
    omega
  row_nonempty i := by have hh := hd i.succ i.castSucc; omega

/-- Density passes to the actual corner child. -/
theorem symmetricChild_dense (D : BetaDiagram (n + 2)) (hd : D.Dense) :
    (D.symmetricChild hd).Dense := by
  intro i j
  have hh := hd i.succ j.castSucc
  dsimp [symmetricChild]
  omega

/-- Subtracting the penultimate column is exactly the child's normalization. -/
theorem symmetricChild_normalized (D : BetaDiagram (n + 2)) (hd : D.Dense) :
    (D.symmetricChild hd).Normalized := by
  intro hm
  have he : (⟨n + 1 - 1, by omega⟩ : Fin (n + 1)) = Fin.last n := by
    apply Fin.ext; simp
  change (D.symmetricChild hd).col ⟨n + 1 - 1, by omega⟩ = 0
  rw [he]
  simp only [symmetricChild, symmetricStep, sub_self]

/-- The child inherits reflection about the shifted span. -/
theorem symmetricChild_symmetric (D : BetaDiagram (n + 2)) (hd : D.Dense)
    (hn : D.Normalized) (hs : D.Symmetric) : (D.symmetricChild hd).Symmetric := by
  obtain ⟨hr, hc⟩ := D.normalized_symmetric_betas hn hs
  refine ⟨D.unitSpan - 2 * D.symmetricStep, ?_, ?_⟩
  · intro i
    have hh := hr i.succ
    have hf : i.succ.rev = i.rev.castSucc := by
      apply Fin.ext
      simp [Fin.rev]
    rw [hf] at hh
    dsimp [symmetricChild]
    omega
  · intro j
    have hh := hc j.castSucc
    have hf : j.castSucc.rev = j.rev.succ := by
      apply Fin.ext
      simp [Fin.rev]; omega
    rw [hf] at hh
    dsimp [symmetricChild]
    omega

/-- The step is positive and strictly below half the span. -/
theorem symmetricStep_bounds (D : BetaDiagram (n + 2)) (hd : D.Dense)
    (hn : D.Normalized) (hs : D.Symmetric) :
    0 < D.symmetricStep ∧ 2 * D.symmetricStep < D.unitSpan := by
  obtain ⟨hr, hc⟩ := D.normalized_symmetric_betas hn hs
  have hz := D.normalized_last hn
  have hcol := D.col_strictAnti
    (show (Fin.last n).castSucc < Fin.last (n + 1) by simp [Fin.lt_def])
  have hrow := hr (0 : Fin (n + 1)).succ
  have hf : (0 : Fin (n + 1)).succ.rev = (Fin.last n).castSucc := by
    apply Fin.ext
    simp [Fin.rev]
  rw [hf] at hrow
  have hden := hd (0 : Fin (n + 1)).succ (Fin.last n).castSucc
  dsimp [symmetricStep] at *
  omega

/-- The shifted span is the geometric span in the child's own beta data. -/
theorem symmetricChild_span (D : BetaDiagram (n + 2)) (hd : D.Dense)
    (hn : D.Normalized) (hs : D.Symmetric) :
    (D.symmetricChild hd).unitSpan = D.unitSpan - 2 * D.symmetricStep := by
  obtain ⟨hr, _⟩ := D.normalized_symmetric_betas hn hs
  have hh := hr (0 : Fin (n + 1)).succ
  have hf : (0 : Fin (n + 1)).succ.rev = (Fin.last n).castSucc := by
    apply Fin.ext
    simp [Fin.rev]
  rw [hf] at hh
  dsimp [symmetricChild, unitSpan, symmetricStep] at *
  omega

set_option backward.isDefEq.respectTransparency false in
/-- The child's matrix is precisely the maximal-corner submatrix, not a surrogate board. -/
theorem symmetricChild_matrix (D : BetaDiagram (n + 2)) (hd : D.Dense) :
    (D.symmetricChild hd).matrix = D.matrix.submatrix Fin.succ Fin.castSucc := by
  apply Matrix.ext
  intro i j
  simp only [matrix, symmetricChild, Matrix.of_apply, Matrix.submatrix_apply]
  congr 1
  ring

/-- Deleting a successor and then the first index commutes with the child embedding. -/
private theorem succAbove_succ (i : Fin (n + 1)) (a : Fin n) :
    i.succ.succAbove a.succ = (i.succAbove a).succ := by
  apply Fin.ext
  simp only [Fin.succAbove]
  split_ifs <;> simp_all [Fin.lt_def]; omega

/-- Deleting a cast index and then the last index commutes with the child embedding. -/
private theorem succAbove_castSucc (j : Fin (n + 1)) (b : Fin n) :
    j.castSucc.succAbove b.castSucc = (j.succAbove b).castSucc := by
  apply Fin.ext
  simp only [Fin.succAbove]
  split_ifs <;> simp_all [Fin.lt_def]; omega

set_option backward.isDefEq.respectTransparency false in
/-- The unique largest generator differentiates each surviving actual cofactor to
its child cofactor with the common sign from `eq:private-derivative`. -/
theorem symmetric_cofactor_private_derivative (D : BetaDiagram (n + 2))
    (hd : D.Dense) (hn : D.Normalized) (i j : Fin (n + 1)) :
    pderiv (unitGenerator D.unitSpan (by
      have := D.largestLabel_pos
      simpa [largestLabel, unitSpan, D.normalized_last hn] using this))
      (D.cofactor i.succ j.castSucc) =
      (-1) ^ (n + 1) * (D.symmetricChild hd).cofactor i j := by
  classical
  have hN : 0 < D.unitSpan := by
    have hh := D.row_nonempty (Fin.last (n + 1))
    have hm := D.row_strictAnti.antitone (Fin.zero_le (Fin.last (n + 1)))
    rw [D.normalized_last hn] at hh
    dsimp [unitSpan]; omega
  let v := unitGenerator D.unitSpan hN
  let M := D.matrix.submatrix i.succ.succAbove j.castSucc.succAbove
  have he : M 0 (Fin.last n) = X v := by
    have h₁ : i.succ.succAbove 0 = 0 := by
      simp [Fin.succAbove, Fin.lt_def]
    have h₂ : j.castSucc.succAbove (Fin.last n) = Fin.last (n + 1) :=
      Fin.succAbove_ne_last_last (by
        intro h
        have hh := congrArg Fin.val h
        simp only [Fin.val_castSucc, Fin.val_last] at hh
        omega)
    simp only [M, Matrix.submatrix_apply, h₁, h₂, matrix, Matrix.of_apply,
      D.normalized_last hn, sub_zero]
    exact complete_of_pos hN
  have hp : ∀ a b, a ≠ 0 ∨ b ≠ Fin.last n → pderiv v (M a b) = 0 := by
    intro a b hab
    apply pderiv_complete_of_ne
    have hab' : i.succ.succAbove a ≠ 0 ∨
        j.castSucc.succAbove b ≠ Fin.last (n + 1) := by
      rcases hab with ha | hb
      · left
        intro hh
        have hzero : i.succ.succAbove 0 = 0 := by simp [Fin.succAbove, Fin.lt_def]
        exact ha (Fin.succAbove_right_injective (hh.trans hzero.symm))
      · right
        intro hh
        have hlast : j.castSucc.succAbove (Fin.last n) = Fin.last (n + 1) :=
          Fin.succAbove_ne_last_last (by
            intro h
            have hh := congrArg Fin.val h
            simp only [Fin.val_castSucc, Fin.val_last] at hh
            omega)
        exact hb (Fin.succAbove_right_injective (hh.trans hlast.symm))
    have hh := D.index_lt_largestLabel _ _ hab'
    simp only [largestLabel, D.normalized_last hn, sub_zero] at hh
    simp only [v, unitGenerator_cast]
    dsimp [unitSpan] at hh ⊢
    omega
  have hm : M.submatrix (0 : Fin (n + 1)).succAbove (Fin.last n).succAbove =
      (D.symmetricChild hd).matrix.submatrix i.succAbove j.succAbove := by
    ext a b
    rw [D.symmetricChild_matrix]
    simp [M, Matrix.submatrix_apply, Fin.succAbove_last]
  have hsign : pderiv v ((-1 : CompleteRing) ^ (i.succ.val + j.castSucc.val)) = 0 := by
    have hc : (-1 : CompleteRing) ^ (i.succ.val + j.castSucc.val) =
        C ((-1 : ℚ) ^ (i.succ.val + j.castSucc.val)) := by simp
    rw [hc]; exact pderiv_C
  change pderiv v ((-1) ^ (i.succ.val + j.castSucc.val) * M.det) = _
  rw [pderiv_mul, hsign, pderiv_det_private_of_derivative_zero M v 0
    (Fin.last n) he hp, hm]
  simp only [cofactor, Fin.val_zero, Fin.val_last, Fin.val_succ, Fin.val_castSucc,
    zero_add, zero_mul, zero_add, pow_add, pow_one]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- Cofactors in the deleted first row or last column contain no largest generator. -/
theorem symmetric_cofactor_private_derivative_boundary (D : BetaDiagram (n + 2))
    (hn : D.Normalized) (i j : Fin (n + 2)) (h : i = 0 ∨ j = Fin.last (n + 1))
    (hN : 0 < D.unitSpan) :
    pderiv (unitGenerator D.unitSpan hN) (D.cofactor i j) = 0 := by
  let v := unitGenerator D.unitSpan hN
  have hm : pderiv v (D.matrix.submatrix i.succAbove j.succAbove).det = 0 := by
    apply pderiv_det_eq_zero
    intro a b
    apply pderiv_complete_of_ne
    have hab : i.succAbove a ≠ 0 ∨ j.succAbove b ≠ Fin.last (n + 1) := by
      rcases h with rfl | rfl
      · exact Or.inl (Fin.succAbove_ne _ _)
      · exact Or.inr (Fin.succAbove_ne _ _)
    have hh := D.index_lt_largestLabel _ _ hab
    simp only [largestLabel, D.normalized_last hn, sub_zero] at hh
    simp only [v, unitGenerator_cast]
    dsimp [unitSpan] at hh ⊢
    omega
  have hc : (-1 : CompleteRing) ^ (i.val + j.val) =
      C ((-1 : ℚ) ^ (i.val + j.val)) := by simp
  rw [cofactor, hc, pderiv_mul, pderiv_C, hm]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- Exact private-largest-generator derivative of an actual unit.  The child
unit is meaningful at every integer position, so unavailable endpoints cause
no exception to the formula. -/
theorem symmetric_unit_private_derivative (D : BetaDiagram (n + 2))
    (hd : D.Dense) (hn : D.Normalized) (z : ℤ)
    (hz : 0 < z ∧ z < D.unitSpan) :
    pderiv (unitGenerator D.unitSpan (by
      have hh := D.row_nonempty (Fin.last (n + 1))
      have hm := D.row_strictAnti.antitone (Fin.zero_le (Fin.last (n + 1)))
      rw [D.normalized_last hn] at hh
      dsimp [unitSpan]; omega)) (D.unitVariation z) =
      (-1) ^ (n + 1) * (D.symmetricChild hd).unitVariation (z - D.symmetricStep) := by
  classical
  have hN : 0 < D.unitSpan := by omega
  let v := unitGenerator D.unitSpan hN
  have hreturn₁ (i : Fin (n + 2)) :
      pderiv v (positiveGap complete (D.row i) z) = 0 := by
    apply pderiv_positiveGap_of_ne
    have hh := D.row_strictAnti.antitone (Fin.zero_le i)
    simp only [v, unitGenerator_cast]
    dsimp [unitSpan] at *
    omega
  have hreturn₂ (j : Fin (n + 2)) :
      pderiv v (positiveGap complete z (D.col j)) = 0 := by
    apply pderiv_positiveGap_of_ne
    have hh := D.col_strictAnti.antitone (Fin.le_last j)
    rw [D.normalized_last hn] at hh
    simp only [v, unitGenerator_cast]
    omega
  have term (i j : Fin (n + 2)) :
      pderiv v (D.cofactor i j * positiveGap complete (D.row i) z *
        positiveGap complete z (D.col j)) =
      pderiv v (D.cofactor i j) * positiveGap complete (D.row i) z *
        positiveGap complete z (D.col j) := by
    rw [pderiv_mul, pderiv_mul, hreturn₁, hreturn₂]
    ring
  change pderiv v (D.unitVariation z) =
    (-1) ^ (n + 1) * (D.symmetricChild hd).unitVariation (z - D.symmetricStep)
  simp only [unitVariation, map_sum]
  simp_rw [term]
  rw [Fin.sum_univ_succ]
  have hfirst : (∑ j, pderiv v (D.cofactor 0 j) * positiveGap complete (D.row 0) z *
      positiveGap complete z (D.col j)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [D.symmetric_cofactor_private_derivative_boundary hn 0 j (Or.inl rfl) hN]
    ring
  rw [hfirst, zero_add]
  have hsplit (i : Fin (n + 1)) :
      (∑ j : Fin (n + 2), pderiv v (D.cofactor i.succ j) *
        positiveGap complete (D.row i.succ) z * positiveGap complete z (D.col j)) =
      (∑ j : Fin (n + 1), pderiv v (D.cofactor i.succ j.castSucc) *
        positiveGap complete (D.row i.succ) z *
        positiveGap complete z (D.col j.castSucc)) +
      pderiv v (D.cofactor i.succ (Fin.last (n + 1))) *
        positiveGap complete (D.row i.succ) z *
        positiveGap complete z (D.col (Fin.last (n + 1))) :=
    Fin.sum_univ_castSucc _
  simp_rw [hsplit]
  have hlast (i : Fin (n + 1)) :
      pderiv v (D.cofactor i.succ (Fin.last (n + 1))) = 0 :=
    D.symmetric_cofactor_private_derivative_boundary hn _ _ (Or.inr rfl) hN
  simp only [hlast, zero_mul, add_zero]
  have hchild (i j : Fin (n + 1)) :
      pderiv v (D.cofactor i.succ j.castSucc) =
        (-1) ^ (n + 1) * (D.symmetricChild hd).cofactor i j :=
    D.symmetric_cofactor_private_derivative hd hn i j
  simp_rw [hchild]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have h₁ : positiveGap complete (D.row i.succ) z =
      positiveGap complete ((D.symmetricChild hd).row i) (z - D.symmetricStep) := by
    change positiveGap complete (D.row i.succ) z =
      positiveGap complete (D.row i.succ - D.symmetricStep) (z - D.symmetricStep)
    by_cases h : z < D.row i.succ
    · rw [positiveGap_of_lt complete h,
        positiveGap_of_lt complete (show z - D.symmetricStep <
          D.row i.succ - D.symmetricStep by omega)]
      congr 1
      ring
    · rw [positiveGap_of_le complete (show D.row i.succ ≤ z by omega),
        positiveGap_of_le complete (show D.row i.succ - D.symmetricStep ≤
          z - D.symmetricStep by omega)]
  have h₂ : positiveGap complete z (D.col j.castSucc) =
      positiveGap complete (z - D.symmetricStep) ((D.symmetricChild hd).col j) := by
    change positiveGap complete z (D.col j.castSucc) =
      positiveGap complete (z - D.symmetricStep) (D.col j.castSucc - D.symmetricStep)
    by_cases h : D.col j.castSucc < z
    · rw [positiveGap_of_lt complete h,
        positiveGap_of_lt complete (show D.col j.castSucc - D.symmetricStep <
          z - D.symmetricStep by omega)]
      congr 1
      ring
    · rw [positiveGap_of_le complete (show z ≤ D.col j.castSucc by omega),
        positiveGap_of_le complete (show z - D.symmetricStep ≤
          D.col j.castSucc - D.symmetricStep by omega)]
  rw [h₁, h₂]
  ring

/-- The child's unit vanishes below the step: every child column is nonnegative. -/
theorem symmetricChild_unit_below (D : BetaDiagram (n + 2)) (hd : D.Dense)
    (z : ℤ) (hz : z < D.symmetricStep) :
    (D.symmetricChild hd).unitVariation (z - D.symmetricStep) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  have h : z - D.symmetricStep ≤ (D.symmetricChild hd).col j := by
    dsimp [symmetricChild, symmetricStep] at *
    have hj := D.col_strictAnti.antitone
      (Fin.strictMono_castSucc.monotone (Fin.le_last j))
    omega
  rw [positiveGap_of_le complete h]
  ring

/-- Above the step, available representative positions are exactly the shifted
child representatives.  This equivalence includes the midpoint on both sides. -/
def symmetricChildRepresentativeEquiv (D : BetaDiagram (n + 2))
    (hd : D.Dense) (hn : D.Normalized) (hs : D.Symmetric) :
    {z : D.UnitRepresentative // D.symmetricStep < z.val.val} ≃
      (D.symmetricChild hd).UnitRepresentative := by
  classical
  let E := D.symmetricChild hd
  have hEn := D.symmetricChild_normalized hd
  have hspan := D.symmetricChild_span hd hn hs
  have hbounds := D.symmetricStep_bounds hd hn hs
  have hmem (z : ℤ) (hrep : 2 * z ≤ D.unitSpan) :
      (z ∈ D.availablePositions ∧ D.symmetricStep < z) ↔
        z - D.symmetricStep ∈ E.availablePositions := by
    rw [D.mem_availablePositions_iff hn, E.mem_availablePositions_iff hEn]
    dsimp [E, symmetricChild]
    constructor
    · rintro ⟨⟨hz, hzN, ha, hb⟩, hu⟩
      refine ⟨by omega, ?_, ?_, ?_⟩
      · have hrow : D.row (0 : Fin (n + 1)).succ =
            D.unitSpan - D.symmetricStep := by
          have hh := hspan
          change D.row (0 : Fin (n + 1)).succ - D.symmetricStep =
            D.unitSpan - 2 * D.symmetricStep at hh
          omega
        change z - D.symmetricStep < D.row (0 : Fin (n + 1)).succ - D.symmetricStep
        rw [hrow]
        omega
      · intro i he; exact ha i.succ (by omega)
      · intro j he; exact hb j.castSucc (by omega)
    · rintro ⟨hz, hzN, ha, hb⟩
      refine ⟨⟨by omega, by omega, ?_, ?_⟩, by omega⟩
      · intro i
        refine Fin.cases ?_ (fun k => ?_) i
        · change z ≠ D.row 0
          dsimp [unitSpan] at hrep
          omega
        · change z ≠ D.row k.succ
          intro h
          exact ha k (by omega)
      · intro j
        refine Fin.lastCases ?_ (fun k => ?_) j
        · change z ≠ D.col (Fin.last (n + 1))
          rw [D.normalized_last hn]
          omega
        · change z ≠ D.col k.castSucc
          intro h
          exact hb k (by omega)
  refine
    { toFun := fun z => ⟨⟨z.val.val.val - D.symmetricStep,
          (hmem _ z.val.property).1 ⟨z.val.val.property, z.property⟩⟩, ?_⟩
      invFun := fun w => ⟨⟨⟨w.val.val + D.symmetricStep, ?_⟩, ?_⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · change 2 * (z.val.val.val - D.symmetricStep) ≤ E.unitSpan
    rw [hspan]
    have hh : 2 * z.val.val.val ≤ D.unitSpan := z.val.property
    omega
  · have hw := (E.mem_availablePositions_iff hEn _).1 w.val.property
    let zv : ℤ := w.val.val
    have hwrep : 2 * zv ≤ E.unitSpan := w.property
    rw [hspan] at hwrep
    have hh : 2 * (w.val.val + D.symmetricStep) ≤ D.unitSpan := by
      change 2 * (zv + D.symmetricStep) ≤ D.unitSpan
      omega
    exact ((hmem _ hh).2 (by simp)).1
  · let zv : ℤ := w.val.val
    have hh : 2 * zv ≤ E.unitSpan := w.property
    rw [hspan] at hh
    change 2 * (zv + D.symmetricStep) ≤ D.unitSpan
    omega
  · change D.symmetricStep < w.val.val + D.symmetricStep
    have hw := (E.mem_availablePositions_iff hEn _).1 w.val.property
    omega
  · intro z; apply Subtype.ext; apply Subtype.ext; apply Subtype.ext; dsimp; omega
  · intro w; apply Subtype.ext; apply Subtype.ext; dsimp; omega

/-- Below the step only the last-column return survives. -/
theorem unitVariation_below_step (D : BetaDiagram (n + 2))
    (hn : D.Normalized) (z : ℤ) (hz : 0 < z ∧ z < D.symmetricStep) :
    D.unitVariation z = complete z *
      ∑ i, D.cofactor i (Fin.last (n + 1)) * positiveGap complete (D.row i) z := by
  classical
  unfold unitVariation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single (Fin.last (n + 1))]
  · rw [D.normalized_last hn, positiveGap_of_lt complete hz.1, sub_zero]
    ring
  · intro j _ hj
    have hj' : j ≤ (Fin.last n).castSucc := by simp [Fin.le_def, Fin.ext_iff] at *; omega
    have hc := D.col_strictAnti.antitone hj'
    have hh : z ≤ D.col j := by dsimp [symmetricStep] at hz; omega
    rw [positiveGap_of_le complete hh]
    ring
  · intro h; exact (h (Finset.mem_univ _)).elim

set_option backward.isDefEq.respectTransparency false in
/-- The last-column complementary determinants use no label above the second row beta. -/
theorem last_cofactor_pderiv_large (D : BetaDiagram (n + 2))
    (v : ℕ+) (hv : D.row 0 - D.symmetricStep < (v.val : ℤ))
    (i : Fin (n + 2)) : pderiv v (D.cofactor i (Fin.last (n + 1))) = 0 := by
  have hm : pderiv v (D.matrix.submatrix i.succAbove
      (Fin.last (n + 1)).succAbove).det = 0 := by
    apply pderiv_det_eq_zero
    intro a b
    apply pderiv_complete_of_ne
    have hr := D.row_strictAnti.antitone (Fin.zero_le (i.succAbove a))
    have hc := D.col_strictAnti.antitone
      (show b.castSucc ≤ (Fin.last n).castSucc from
        Fin.strictMono_castSucc.monotone (Fin.le_last b))
    simp only [Fin.succAbove_last]
    dsimp [symmetricStep] at *
    omega
  have hs : (-1 : CompleteRing) ^ (i.val + (Fin.last (n + 1)).val) =
      C ((-1 : ℚ) ^ (i.val + (Fin.last (n + 1)).val)) := by simp
  rw [cofactor, hs, pderiv_mul, pderiv_C, hm]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- The private large return label has coefficient exactly the actual nonzero
corner cofactor times `h_z`, as used in `prop:symmetric-unit-kernel`. -/
theorem unitVariation_below_private (D : BetaDiagram (n + 2))
    (hd : D.Dense) (hn : D.Normalized) (hs : D.Symmetric) (z : ℤ)
    (hz : 0 < z ∧ z < D.symmetricStep) :
    pderiv (unitGenerator (D.unitSpan - z) (by
      have := D.symmetricStep_bounds hd hn hs; omega)) (D.unitVariation z) =
      complete z * D.cofactor 0 (Fin.last (n + 1)) := by
  classical
  have hb := D.symmetricStep_bounds hd hn hs
  let v := unitGenerator (D.unitSpan - z) (by omega)
  have hv : D.row 0 - D.symmetricStep < (v.val : ℤ) := by
    simp only [v, unitGenerator_cast]; dsimp [unitSpan]; omega
  have hcz : pderiv v (complete z) = 0 := by
    apply pderiv_complete_of_ne
    simp only [v, unitGenerator_cast]
    omega
  obtain ⟨hr, _⟩ := D.normalized_symmetric_betas hn hs
  have ha₂ : D.row (0 : Fin (n + 1)).succ = D.unitSpan - D.symmetricStep := by
    have hh := hr (0 : Fin (n + 1)).succ
    have hf : (0 : Fin (n + 1)).succ.rev = (Fin.last n).castSucc := by
      apply Fin.ext
      simp [Fin.rev]
    rw [hf] at hh
    exact hh
  change pderiv v (D.unitVariation z) = complete z * D.cofactor 0 (Fin.last (n + 1))
  rw [D.unitVariation_below_step hn z hz, pderiv_mul, hcz, zero_mul, zero_add,
    map_sum]
  have hterm (i : Fin (n + 2)) :
      pderiv v (D.cofactor i (Fin.last (n + 1)) * positiveGap complete (D.row i) z) =
      if i = 0 then D.cofactor 0 (Fin.last (n + 1)) else 0 := by
    rw [pderiv_mul, D.last_cofactor_pderiv_large v hv, zero_mul, zero_add]
    by_cases hi : i = 0
    · subst i
      have hzN : z < D.unitSpan := by omega
      have hrow0 : D.row 0 = D.unitSpan := rfl
      rw [hrow0, positiveGap_of_lt complete hzN]
      have hg : complete (D.unitSpan - z) = (X v : CompleteRing) :=
        complete_of_pos (by omega)
      rw [hg, pderiv_X_self, mul_one]; simp only [ite_true]
    · have hi' : (0 : Fin (n + 1)).succ ≤ i := by
        have hfin : (0 : Fin (n + 2)) < i := Fin.pos_iff_ne_zero.mpr hi
        have hval : 0 < i.val := by simpa only [Fin.lt_def, Fin.val_zero] using hfin
        change 1 ≤ i.val
        omega
      have hh := D.row_strictAnti.antitone hi'
      have hne : D.row i - z ≠ (v.val : ℤ) := by
        simp only [v, unitGenerator_cast]; omega
      rw [pderiv_positiveGap_of_ne v _ _ hne]
      simp [hi]
  simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

set_option backward.isDefEq.respectTransparency false in
/-- A later low position cannot contain the earlier position's private large return label. -/
theorem unitVariation_below_later_derivative (D : BetaDiagram (n + 2))
    (hd : D.Dense) (hn : D.Normalized) (hs : D.Symmetric) (z w : ℤ)
    (hz : 0 < z) (hzw : z < w) (hw : w < D.symmetricStep) :
    pderiv (unitGenerator (D.unitSpan - z) (by
      have := D.symmetricStep_bounds hd hn hs; omega)) (D.unitVariation w) = 0 := by
  classical
  have hb := D.symmetricStep_bounds hd hn hs
  let v := unitGenerator (D.unitSpan - z) (by omega)
  have hv : D.row 0 - D.symmetricStep < (v.val : ℤ) := by
    simp only [v, unitGenerator_cast]; dsimp [unitSpan]; omega
  change pderiv v (D.unitVariation w) = 0
  rw [D.unitVariation_below_step hn w ⟨by omega, hw⟩, pderiv_mul]
  have hcw : pderiv v (complete w) = 0 := by
    apply pderiv_complete_of_ne
    simp only [v, unitGenerator_cast]
    omega
  rw [hcw, zero_mul, zero_add, map_sum]
  have ht : ∀ i, pderiv v
      (D.cofactor i (Fin.last (n + 1)) * positiveGap complete (D.row i) w) = 0 := by
    intro i
    rw [pderiv_mul, D.last_cofactor_pderiv_large v hv, zero_mul, zero_add]
    have hi := D.row_strictAnti.antitone (Fin.zero_le i)
    have hne : D.row i - w ≠ (v.val : ℤ) := by
      simp only [v, unitGenerator_cast]
      dsimp [unitSpan] at *
      omega
    rw [pderiv_positiveGap_of_ne v _ _ hne]
    ring
  simp only [ht, Finset.sum_const_zero, mul_zero]

set_option backward.isDefEq.respectTransparency false in
/-- The signed exterior corner cofactor is nonzero on a dense core. -/
theorem dense_corner_cofactor_ne_zero (D : BetaDiagram (n + 2)) (hd : D.Dense) :
    D.cofactor 0 (Fin.last (n + 1)) ≠ 0 := by
  have hp := D.cornerPolynomial_ne_zero (hd.connected (by omega))
  have hm : (D.matrix.submatrix (0 : Fin (n + 2)).succAbove
      (Fin.last (n + 1)).succAbove).det = D.cornerPolynomial := by
    unfold cornerPolynomial
    congr 1
    apply Matrix.ext
    intro i j
    simp only [cornerBoard, betaBoard, matrix, Matrix.of_apply, Matrix.submatrix_apply,
      Fin.zero_succAbove, Fin.succAbove_last]
  rw [cofactor, hm]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hp

set_option backward.isDefEq.respectTransparency false in
/-- Representative unit polynomials are rational-linearly independent at every
positive order.  The order-one statement is the auxiliary induction base of
`prop:symmetric-unit-kernel`. -/
theorem symmetric_units_independent : ∀ n (D : BetaDiagram (n + 1)),
    D.Dense → D.Normalized → D.Symmetric →
    LinearIndependent ℚ (fun z : D.UnitRepresentative => D.unitVariation z.val.val) := by
  intro n
  induction n with
  | zero =>
      intro D hd hn hs
      exact D.symmetric_units_order_one_independent hn
  | succ n ih =>
      intro D hd hn hs
      classical
      apply Fintype.linearIndependent_iff.2
      intro c hc
      let E := D.symmetricChild hd
      have hEn := D.symmetricChild_normalized hd
      have hEs := D.symmetricChild_symmetric hd hn hs
      have hEd := D.symmetricChild_dense hd
      have hEi := ih E hEd hEn hEs
      let e := D.symmetricChildRepresentativeEquiv hd hn hs
      let high := {z : D.UnitRepresentative // D.symmetricStep < z.val.val}
      have hb := D.symmetricStep_bounds hd hn hs
      have hN : 0 < D.unitSpan := by omega
      let v := unitGenerator D.unitSpan hN
      have hdiff := congrArg (fun p : CompleteRing => pderiv v p) hc
      simp only [map_sum, Derivation.map_smul, map_zero] at hdiff
      have hterm (z : D.UnitRepresentative) :
          pderiv v (D.unitVariation z.val.val) =
          if hu : D.symmetricStep < z.val.val then
            (-1) ^ (n + 1) * E.unitVariation (e ⟨z, hu⟩).val.val else 0 := by
        have hz := (D.mem_availablePositions_iff hn _).1 z.val.property
        rw [D.symmetric_unit_private_derivative hd hn _ ⟨hz.1, hz.2.1⟩]
        by_cases hu : D.symmetricStep < z.val.val
        · simp only [hu, dite_true]
          rfl
        · have hne : z.val.val ≠ D.symmetricStep := by
            exact hz.2.2.2 (Fin.last n).castSucc
          have hlt : z.val.val < D.symmetricStep := by omega
          rw [D.symmetricChild_unit_below hd _ hlt]
          simp [hu]
      simp only [hterm] at hdiff
      have hsum : (∑ w : E.UnitRepresentative,
          c (e.symm w).val • E.unitVariation w.val.val) = 0 := by
        have hh : (-1 : CompleteRing) ^ (n + 1) *
            (∑ w : E.UnitRepresentative, c (e.symm w).val • E.unitVariation w.val.val) = 0 := by
          calc
            _ = ∑ z : D.UnitRepresentative, c z •
                (if hu : D.symmetricStep < z.val.val then
                  (-1 : CompleteRing) ^ (n + 1) * E.unitVariation (e ⟨z, hu⟩).val.val
                 else 0) := by
              rw [Finset.mul_sum, ← Equiv.sum_comp e]
              simp only [Equiv.symm_apply_apply]
              rw [← unit_sum_subtype (fun z : D.UnitRepresentative =>
                D.symmetricStep < z.val.val)]
              apply Finset.sum_congr rfl
              intro z _
              split_ifs <;> simp
            _ = 0 := hdiff
        exact (mul_eq_zero.mp hh).resolve_left (pow_ne_zero _ (by norm_num))
      have hhigh : ∀ z : D.UnitRepresentative, D.symmetricStep < z.val.val → c z = 0 := by
        intro z hz
        have hh := (Fintype.linearIndependent_iff.mp hEi) _ hsum (e ⟨z, hz⟩)
        simpa using hh
      intro z
      by_contra hcz
      let S : Finset D.UnitRepresentative := Finset.univ.filter (fun w => c w ≠ 0)
      have hzS : z ∈ S := by simp [S, hcz]
      obtain ⟨w, hw, hmin⟩ := Finset.exists_min_image S (fun w => w.val.val) ⟨z, hzS⟩
      have hwc : c w ≠ 0 := (Finset.mem_filter.mp hw).2
      have hwpos := (D.mem_availablePositions_iff hn _).1 w.val.property
      have hwlow : w.val.val < D.symmetricStep := by
        have hnot : ¬ D.symmetricStep < w.val.val := by
          intro h; exact hwc (hhigh w h)
        have hne := hwpos.2.2.2 (Fin.last n).castSucc
        dsimp [symmetricStep] at hnot ⊢
        omega
      let q := unitGenerator (D.unitSpan - w.val.val) (by omega)
      have hsmall := congrArg (fun p : CompleteRing => pderiv q p) hc
      simp only [map_sum, Derivation.map_smul, map_zero] at hsmall
      have hterms (x : D.UnitRepresentative) (hx : x ≠ w) :
          c x • pderiv q (D.unitVariation x.val.val) = 0 := by
        by_cases hcx : c x = 0
        · simp [hcx]
        · have hxS : x ∈ S := by simp [S, hcx]
          have hle := hmin x hxS
          have hne : x.val.val ≠ w.val.val := by
            intro he
            apply hx
            apply Subtype.ext; apply Subtype.ext; exact he
          have hlt : w.val.val < x.val.val := by omega
          have hxpos := (D.mem_availablePositions_iff hn _).1 x.val.property
          have hxlow : x.val.val < D.symmetricStep := by
            have hnot : ¬ D.symmetricStep < x.val.val := by
              intro h; exact hcx (hhigh x h)
            have he := hxpos.2.2.2 (Fin.last n).castSucc
            dsimp [symmetricStep] at *; omega
          rw [D.unitVariation_below_later_derivative hd hn hs _ _ hwpos.1 hlt hxlow]
          simp
      rw [Finset.sum_eq_single w] at hsmall
      · rw [D.unitVariation_below_private hd hn hs _ ⟨hwpos.1, hwlow⟩] at hsmall
        have hp : complete w.val.val * D.cofactor 0 (Fin.last (n + 1)) ≠ 0 :=
          mul_ne_zero ((complete_ne_zero_iff _).2 hwpos.1.le)
            (D.dense_corner_cofactor_ne_zero hd)
        exact hwc ((smul_eq_zero.mp hsmall).resolve_right hp)
      · intro x _ hx; exact hterms x hx
      · intro h; exact (h (Finset.mem_univ _)).elim

end BetaDiagram
end SkewCofactorIndependence
