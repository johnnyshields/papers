/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.ConstantGapRibbons
import Mathlib.RingTheory.Localization.FractionRing

/-!
# The exact constant-gap localized ribbon identity

Formalizes `eq:constant-gap-substitution` of
`shields-2026-skew-class-inflation.tex`.  The actual determinant is
computed from its first seam, and contraction produces the actual
merged deflated word.  The denominator is nonzero even at zero gap.
Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative SkewJacobiNegative.GeneralHessenberg

/-- The constant-gap ribbon substitution into the genuine full fraction field. -/
noncomputable def constantGapSubstitution (c : ℕ) :
    CompleteRing →+* FractionRing CompleteRing :=
  MvPolynomial.eval₂Hom (algebraMap ℚ (FractionRing CompleteRing)) (fun j : ℕ+ =>
    algebraMap CompleteRing (FractionRing CompleteRing) (complete ((c + j.val : ℕ) : ℤ)) /
      algebraMap CompleteRing (FractionRing CompleteRing) (complete c))

/-- Every nonnegative complete generator remains nonzero in the actual fraction field. -/
theorem constantGap_denominator_ne_zero (c : ℕ) :
    algebraMap CompleteRing (FractionRing CompleteRing) (complete c) ≠ 0 := by
  intro he
  apply (complete_ne_zero_iff (c : ℤ)).mpr (by positivity)
  apply IsFractionRing.injective CompleteRing (FractionRing CompleteRing)
  simpa only [map_zero] using he

/-- Every positive deflated generator has exactly the displayed shifted-generator ratio. -/
theorem constantGapSubstitution_complete (c a : ℕ) (ha : 0 < a) :
    constantGapSubstitution c (complete a) =
      algebraMap CompleteRing (FractionRing CompleteRing) (complete ((c + a : ℕ) : ℤ)) /
        algebraMap CompleteRing (FractionRing CompleteRing) (complete c) := by
  let j : ℕ+ := ⟨a, ha⟩
  have he : complete (a : ℤ) = MvPolynomial.X j := complete_nat j
  rw [he, constantGapSubstitution, MvPolynomial.eval₂Hom_X']
  rfl

/-- First-seam contraction retains all rows after the merged endpoint in their literal positions. -/
theorem contract_first_deflated_word {n : ℕ} (P : Profile (n + 1)) (c : ℕ)
    (hg : P.g 0 = c) (hr : ∀ i, c < P.r i) :
    List.ofFn (fun i => (contract P 0).r i - c) =
      (P.r 0 - c + (P.r (0 : Fin (n + 1)).succ - c)) ::
        List.ofFn (fun i : Fin n => P.r i.succ.succ - c) := by
  rw [List.ofFn_succ]
  congr 1
  · have he := contract_joined_row P 0
    rw [hg] at he
    simp only [Fin.castSucc_zero] at he
    have h0 := hr 0
    have h1 := hr (0 : Fin (n + 1)).succ
    omega
  · apply congrArg List.ofFn
    funext i
    rw [contract_row_of_ne P 0 i.succ (by simp),
      Fin.succAbove_of_le_castSucc _ _ (by change 1 ≤ i.val + 1; omega)]

/-- Every contracted row is still strictly above the constant internal gap. -/
theorem contract_first_rows_above_gap {n : ℕ} (P : Profile (n + 1)) (c : ℕ)
    (hg : P.g 0 = c) (hr : ∀ i, c < P.r i) : ∀ i, c < (contract P 0).r i := by
  intro i
  by_cases hi : i = 0
  · subst i
    have he := contract_joined_row P 0
    rw [hg] at he
    simp only [Fin.castSucc_zero] at he
    have h0 := hr 0
    have h1 := hr (0 : Fin (n + 1)).succ
    omega
  · have hiv : i.val ≠ 0 := fun he => hi (Fin.ext he)
    rw [contract_row_of_ne P 0 i (by exact hiv)]
    exact hr _

/-- The displayed identity for every actual constant-gap Hessenberg profile. -/
theorem constant_gap_substitution {n : ℕ} (P : Profile n) (c : ℕ)
    (hP : Staircase.Thick P) (hg : ∀ j, P.g j = c) (hr : ∀ i, c < P.r i) :
    algebraMap CompleteRing (FractionRing CompleteRing) P.toBetaDiagram.schur =
      algebraMap CompleteRing (FractionRing CompleteRing) (complete c) ^ (n + 1) *
        constantGapSubstitution c (ribbonWord (List.ofFn (fun i => P.r i - c))) := by
  induction n with
  | zero =>
    have hbase : P.toBetaDiagram.schur = complete (P.r 0) := by
      rw [BetaDiagram.schur, Matrix.det_fin_one]
      change complete (P.xi 0 - P.zeta 0) = complete (P.r 0)
      rw [P.xi_sub_zeta]
    rw [hbase, List.ofFn_succ, List.ofFn_zero, ribbonWord, ribbonTail]
    rw [constantGapSubstitution_complete c (P.r 0 - c) (Nat.sub_pos_of_lt (hr 0))]
    have hs : c + (P.r 0 - c) = P.r 0 := Nat.add_sub_of_le (hr 0).le
    rw [hs]
    simp only [Nat.zero_add, pow_one]
    field_simp [constantGap_denominator_ne_zero c]
  | succ n ih =>
    let R : Profile n := rightOfSeam P (0 : Fin (n + 1))
    have hR : Staircase.Thick R := slice_thick hP 1 n (by omega)
    have hgR : ∀ j, R.g j = c := fun j => hg _
    have hrR : ∀ i, c < R.r i := fun i => hr _
    have hgC : ∀ j, (contract P 0).g j = c := by intro j; rw [contract_gap, hg]
    have hrC := contract_first_rows_above_gap P c (hg 0) hr
    have hrows : List.ofFn (fun i => R.r i - c) =
        List.ofFn (fun i : Fin (n + 1) => P.r i.succ - c) := by
      apply congrArg List.ofFn
      funext i
      change P.r (sliceEmbedding 1 n (by omega) i) - c = P.r i.succ - c
      congr 2
      apply Fin.ext
      change 1 + i.val = i.val + 1
      omega
    have hleft : (leftOfSeam P (0 : Fin (n + 1))).toBetaDiagram.schur = complete (P.r 0) := by
      let L : Profile 0 := leftOfSeam P (0 : Fin (n + 1))
      change L.toBetaDiagram.schur = complete (P.r 0)
      rw [BetaDiagram.schur, Matrix.det_fin_one]
      change complete (L.xi 0 - L.zeta 0) = complete (P.r 0)
      rw [L.xi_sub_zeta]
      rfl
    have he := schur_join_formula P hP 0
    rw [hleft, hg 0] at he
    change P.toBetaDiagram.schur = complete (P.r 0) * R.toBetaDiagram.schur -
      complete c * (contract P 0).toBetaDiagram.schur at he
    rw [he, map_sub, map_mul, map_mul,
      ih R hR hgR hrR, ih (contract P 0) (contract_thick hP 0) hgC hrC,
      hrows, contract_first_deflated_word P c (hg 0) hr]
    have htail : List.ofFn (fun i : Fin (n + 1) => P.r i.succ - c) =
        (P.r (0 : Fin (n + 1)).succ - c) ::
          List.ofFn (fun i : Fin n => P.r i.succ.succ - c) := by
      rw [List.ofFn_succ]
    have hfull : List.ofFn (fun i => P.r i - c) =
        (P.r 0 - c) :: (P.r (0 : Fin (n + 1)).succ - c) ::
          List.ofFn (fun i : Fin n => P.r i.succ.succ - c) := by
      rw [List.ofFn_succ, htail]
    rw [htail, hfull]
    simp only [ribbonWord, ribbonTail, map_sub, map_mul]
    rw [constantGapSubstitution_complete c (P.r 0 - c) (Nat.sub_pos_of_lt (hr 0))]
    have hs : c + (P.r 0 - c) = P.r 0 := Nat.add_sub_of_le (hr 0).le
    rw [hs]
    simp only [pow_succ]
    field_simp [constantGap_denominator_ne_zero c]

end SkewClassInflation
