/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.ZeroSeamAlgebra

/-!
# Extreme coefficients at zero seams

Formalizes `eq:unit-extremes` and the zero-seam part of
`lem:seam-coefficients` in `shields-2026-skew-class-inflation.tex`.
The cut components and total contraction are actual connected profiles.
The two-one lift is used only to reuse the proved positive-seam determinant
calculus; its inverse substitution is applied explicitly.  Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative SkewJacobiNegative.Gluing SkewJacobiNegative.Staircase
open SkewJacobiNegative.GeneralHessenberg
open scoped BigOperators

/-- The multiplicity counts zero-valued seam positions, not distinct numerical labels. -/
def zeroSeamCount {n : ℕ} (P : Profile n) : ℕ :=
  ∑ j : Fin n, if P.g j = 0 then 1 else 0

/-- Zero seams become precisely the generator-one seams of the faithful affine lift. -/
theorem zeroSeamCount_eq_lift {n : ℕ} (P : Profile n) :
    zeroSeamCount P = minimumMultiplicity (P.lift rowShiftTwoOne) 1 := by
  unfold zeroSeamCount minimumMultiplicity
  apply Finset.sum_congr rfl
  intro i _
  simp [Profile.lift, rowShiftTwoOne]

/-- The actual zero-seam total contraction.  The predicate is written in lifted coordinates
so the recursive choice agrees literally with the existing positive-seam construction. -/
noncomputable def contractAllZeros : {n : ℕ} → Profile n → Σ k, Profile k
  | 0, P => ⟨0, P⟩
  | n + 1, P =>
      if h : ∃ c : Fin (n + 1), (P.lift rowShiftTwoOne).g c = (1 : ℕ+).val then
        contractAllZeros (contract P (Classical.choose h))
      else ⟨n + 1, P⟩

/-- The recursive zero contractions commute with the genuine affine profile lift. -/
theorem lift_contractAllZeros {n : ℕ} (P : Profile n) :
    contractAllMinimum (P.lift rowShiftTwoOne) 1 =
      let C := contractAllZeros P
      ⟨C.1, C.2.lift rowShiftTwoOne⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases h : ∃ c : Fin (n + 1), (P.lift rowShiftTwoOne).g c = (1 : ℕ+).val
    · rw [show contractAllZeros P = contractAllZeros (contract P (Classical.choose h)) by
          simp only [contractAllZeros, dite_eq_left h]]
      rw [show contractAllMinimum (P.lift rowShiftTwoOne) 1 =
          contractAllMinimum (contract (P.lift rowShiftTwoOne) (Classical.choose h)) 1 by
            simp only [contractAllMinimum, dite_eq_left h]]
      rw [contract_lift, ih]
    · rw [show contractAllZeros P = ⟨n + 1, P⟩ by
          simp only [contractAllZeros, dite_eq_right h]]
      simp only [contractAllMinimum, dite_eq_right h]

/-- Thick profiles remain thick under the two-one affine lift. -/
theorem twoOne_thick {n : ℕ} (P : Profile n) (hP : Thick P) :
    Thick (P.lift rowShiftTwoOne) := by
  intro j k hjk
  have h := hP j k hjk
  change (2 * P.g j + 1) + (2 * P.g k + 1) < 2 * P.r j.succ + 1
  omega

/-- Every lifted row is strictly above the distinguished generator one. -/
theorem twoOne_rows_above {n : ℕ} (P : Profile n) :
    ∀ i, (1 : ℕ+).val < (P.lift rowShiftTwoOne).r i := by
  intro i
  have h := P.r_pos i
  change 1 < 2 * P.r i + 1
  omega

/-- The row loss is the exact number of zero seam positions. -/
theorem contractAllZeros_size {n : ℕ} (P : Profile n) :
    (contractAllZeros P).1 + zeroSeamCount P = n := by
  have h := contractAllMinimum_size (P.lift rowShiftTwoOne) 1
  rwa [lift_contractAllZeros, ← zeroSeamCount_eq_lift] at h

/-- No zero seam survives the actual total contraction. -/
theorem contractAllZeros_gap_pos {n : ℕ} (P : Profile n)
    (j : Fin (contractAllZeros P).1) : 0 < (contractAllZeros P).2.g j := by
  have h : ∀ i : Fin (contractAllMinimum (P.lift rowShiftTwoOne) 1).1,
      (contractAllMinimum (P.lift rowShiftTwoOne) 1).2.g i ≠ (1 : ℕ+).val :=
    contractAllMinimum_gap_ne _ _
  rw [lift_contractAllZeros] at h
  have hh := h j
  change 2 * (contractAllZeros P).2.g j + 1 ≠ 1 at hh
  omega

/-- The original, unlifted rows and gaps in each simultaneous zero-cut interval. -/
noncomputable def zeroCutComponent {n : ℕ} (P : Profile n)
    (b : CutBlock (P.lift rowShiftTwoOne) 1) :
    Profile (blockSize (P.lift rowShiftTwoOne) 1 b) where
  r i := P.r (blockEmbedding (P.lift rowShiftTwoOne) 1 b i)
  g j := P.g (blockGap (P.lift rowShiftTwoOne) 1 b j)
  r_pos i := P.r_pos _
  g_lt_castSucc j := by
    have h := P.g_lt_castSucc (blockGap (P.lift rowShiftTwoOne) 1 b j)
    rw [(blockGap_rows (P.lift rowShiftTwoOne) 1 b j).1] at h
    exact h
  g_lt_succ j := by
    have h := P.g_lt_succ (blockGap (P.lift rowShiftTwoOne) 1 b j)
    rw [(blockGap_rows (P.lift rowShiftTwoOne) 1 b j).2] at h
    exact h

/-- Zero-cut geometry is exactly the inverse affine image of the lifted positive-seam geometry. -/
theorem zeroCutComponent_lift {n : ℕ} (P : Profile n)
    (b : CutBlock (P.lift rowShiftTwoOne) 1) :
    (zeroCutComponent P b).lift rowShiftTwoOne = cutComponent (P.lift rowShiftTwoOne) 1 b := by
  apply Profile.ext
  · funext i
    rw [Profile.lift_r, cutComponent_row]
    rfl
  · funext j
    rw [Profile.lift_g, cutComponent_gap]
    rfl

/-- A lifted cut cannot retain any original zero seam. -/
theorem zeroCutComponent_gap_pos {n : ℕ} (P : Profile n)
    (b : CutBlock (P.lift rowShiftTwoOne) 1)
    (j : Fin (blockSize (P.lift rowShiftTwoOne) 1 b)) :
    0 < (zeroCutComponent P b).g j := by
  have h := blockGap_ne (P.lift rowShiftTwoOne) 1 b j
  change 2 * P.g (blockGap (P.lift rowShiftTwoOne) 1 b j) + 1 ≠ 1 at h
  change 0 < P.g (blockGap (P.lift rowShiftTwoOne) 1 b j)
  omega

/-- Constant coefficient in a generator coordinate is exactly generator erasure. -/
theorem minimumPolynomial_coeff_zero (z : ℕ+) (p : CompleteRing) :
    (minimumPolynomial z p).coeff 0 = eraseGenerator z p := by
  have he : Polynomial.constantCoeff.comp (minimumPolynomial z) = eraseGenerator z := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [minimumPolynomial, eraseGenerator]
    · intro i
      by_cases h : i = z <;> simp [minimumPolynomial, eraseGenerator, h]
  exact congrArg (fun f : CompleteRing →+* CompleteRing => f p) he

/-- The unit constant coefficient is the product of the actual unspecialized cut components. -/
theorem zero_seam_constant_coefficient {n : ℕ} (P : Profile n) (hP : Thick P) :
    (unitSchur P).coeff 0 =
      ∏ b : CutBlock (P.lift rowShiftTwoOne) 1, (zeroCutComponent P b).toBetaDiagram.schur := by
  rw [unitSchur_eq_lifted_minimum, Polynomial.coeff_map, minimumPolynomial_coeff_zero,
    distinguished_cut_product _ (twoOne_thick P hP) 1 (twoOne_rows_above P), map_prod]
  apply Finset.prod_congr rfl
  intro b _
  rw [← zeroCutComponent_lift, undoOdd_lifted_schur]

/-- The retained-unit top coefficient is exactly the signed actual total zero-seam contraction. -/
theorem zero_seam_highest_coefficient {n : ℕ} (P : Profile n) (hP : Thick P) :
    (unitSchur P).coeff (zeroSeamCount P) =
      (-1 : CompleteRing) ^ zeroSeamCount P * (contractAllZeros P).2.toBetaDiagram.schur := by
  rw [unitSchur_eq_lifted_minimum, Polynomial.coeff_map, zeroSeamCount_eq_lift,
    distinguished_highest_layer _ (twoOne_thick P hP) 1 (twoOne_rows_above P),
    map_mul, map_pow, map_neg, map_one, lift_contractAllZeros]
  rw [undoOdd_lifted_schur, ← zeroSeamCount_eq_lift]

end SkewClassInflation
