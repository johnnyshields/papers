/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
-- TODO-COPIED: skew-jacobi-negative/lean/SkewJacobiNegative/HessenbergExpansion.lean

import SkewJacobiNegative.Gluing.Homogenization
import SkewJacobiNegative.RepresentationBridges
import Mathlib

/-!
# Four-row interval expansion

The actual Jacobi--Trudi determinant in `eq:interval-expansion` and the
coefficient tables in `app:four` of
`shields-2026-skew-jacobi-negative.tex`.  The homogenized statements keep
`hTilde 0` independent.  Every algebraic table is valid with coincident labels.
-/

namespace SkewJacobiNegative
namespace HessenbergExpansion

open Gluing

/-- The eight signed interval partitions of four rows. -/
def fourInterval {R : Type*} [CommRing R] (h : ℤ → R)
    (p q r s a b d : ℤ) : R :=
  h p * h q * h r * h s
    - h (p + q - a) * h a * h r * h s
    - h p * h (q + r - b) * h b * h s
    - h p * h q * h (r + s - d) * h d
    + h (p + q + r - a - b) * h a * h b * h s
    + h (p + q - a) * h a * h (r + s - d) * h d
    + h p * h (q + r + s - b - d) * h b * h d
    - h (p + q + r + s - a - b - d) * h a * h b * h d

/-- Laplace expansion, with precisely the three forbidden lower entries zero. -/
theorem det_four_hessenberg {R : Type*} [CommRing R]
    (A : Matrix (Fin 4) (Fin 4) R)
    (h20 : A 2 0 = 0) (h30 : A 3 0 = 0) (h31 : A 3 1 = 0) :
    A.det =
      A 0 0 * A 1 1 * A 2 2 * A 3 3
      - A 0 1 * A 1 0 * A 2 2 * A 3 3
      - A 0 0 * A 1 2 * A 2 1 * A 3 3
      - A 0 0 * A 1 1 * A 2 3 * A 3 2
      + A 0 2 * A 1 0 * A 2 1 * A 3 3
      + A 0 1 * A 1 0 * A 2 3 * A 3 2
      + A 0 0 * A 1 3 * A 2 1 * A 3 2
      - A 0 3 * A 1 0 * A 2 1 * A 3 2 := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix_apply,
    Fin.succAbove, h20, h30, h31]
  <;> ring

/-- The actual signed index array of a four-row profile. -/
def fourIndices (p q r s a b d : ℤ) : Matrix (Fin 4) (Fin 4) ℤ :=
  !![p, p + q - a, p + q + r - a - b, p + q + r + s - a - b - d;
     a, q, q + r - b, q + r + s - b - d;
     a + b - q, b, r, r + s - d;
     a + b + d - q - r, b + d - r, d, s]

/-- The intrinsic property of an actual beta array, not a mask certificate. -/
def IntrinsicHessenberg {n : ℕ} (x z : Fin n → ℤ) : Prop :=
  ∀ i j, j.val + 1 < i.val → x i - z j < 0

/-- The four-row strict domain, allowing zero gaps and all index ties. -/
def FourDomain (p q r s a b d : ℤ) : Prop :=
  0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ d ∧ a < p ∧ a + b < q ∧ b + d < r ∧ d < s

/-- In the strict domain every forbidden lower entry is genuinely negative. -/
theorem domain_lower_negative {p q r s a b d : ℤ}
    (h : FourDomain p q r s a b d) :
    a + b - q < 0 ∧ a + b + d - q - r < 0 ∧ b + d - r < 0 := by
  rcases h with ⟨ha, hb, hd, hp, hq, hr, hs⟩
  omega

/-- The general eight-term formula for an indexed complete-generator convention. -/
theorem four_indices_det {R : Type*} [CommRing R] (h : ℤ → R)
    (hneg : ∀ k : ℤ, k < 0 → h k = 0)
    {p q r s a b d : ℤ} (hdom : FourDomain p q r s a b d) :
    ((fourIndices p q r s a b d).map h).det = fourInterval h p q r s a b d := by
  obtain ⟨h20, h30, h31⟩ := domain_lower_negative hdom
  rw [det_four_hessenberg _ (by simpa [fourIndices] using hneg _ h20)
    (by simpa [fourIndices] using hneg _ h30)
    (by simpa [fourIndices] using hneg _ h31)]
  simp [fourIndices, fourInterval]

/-- Reversal acts on rows and gaps simultaneously. -/
theorem fourInterval_reverse {R : Type*} [CommRing R] (h : ℤ → R)
    (p q r s a b d : ℤ) :
    fourInterval h s r q p d b a = fourInterval h p q r s a b d := by
  have h1 : s + r - d = r + s - d := by omega
  have h2 : r + q - b = q + r - b := by omega
  have h3 : q + p - a = p + q - a := by omega
  have h4 : s + r + q - d - b = q + r + s - b - d := by omega
  have h5 : r + q + p - b - a = p + q + r - a - b := by omega
  have h6 : s + r + q + p - d - b - a = p + q + r + s - a - b - d := by omega
  simp only [fourInterval, h1, h2, h3, h4, h5, h6]
  ring

/-- Three-row connected block determinant. -/
def threeInterval {R : Type*} [CommRing R] (h : ℤ → R)
    (p q r a b : ℤ) : R :=
  h p * h q * h r - h (p + q - a) * h a * h r
    - h p * h (q + r - b) * h b
    + h (p + q + r - a - b) * h a * h b

/-- The recovered three-row block polynomial is unchanged by reversing its profile. -/
theorem threeInterval_reverse {R : Type*} [CommRing R] (h : ℤ → R)
    (p q r a b : ℤ) :
    threeInterval h r q p b a = threeInterval h p q r a b := by
  have h1 : r + q - b = q + r - b := by omega
  have h2 : q + p - a = p + q - a := by omega
  have h3 : r + q + p - b - a = p + q + r - a - b := by omega
  simp only [threeInterval, h1, h2, h3]
  ring

/-- An end minimum produces the exact singleton times three-row cut. -/
theorem end_cut {R : Type*} [CommRing R] (h : ℤ → R)
    (p q r s c a b : ℤ) (hc : h c = 0) :
    fourInterval h p q r s c a b = h p * threeInterval h q r s a b := by
  simp only [fourInterval, threeInterval, hc]
  ring

/-- A middle minimum produces the exact two-row times two-row cut. -/
theorem middle_cut {R : Type*} [CommRing R] (h : ℤ → R)
    (p q r s a c b : ℤ) (hc : h c = 0) :
    fourInterval h p q r s a c b =
      (h p * h q - h (p + q - a) * h a) *
      (h r * h s - h (r + s - b) * h b) := by
  simp only [fourInterval, hc]
  ring

/-- The linear coefficient at an end minimum, including all merge-label ties. -/
theorem end_minimum_table {R : Type*} [CommRing R] (h : ℤ → R)
    (p q r s c a b : ℤ) :
    fourInterval h p q r s c a b = h p * threeInterval h q r s a b - h c *
      (h (p + q - c) * h r * h s
        - h (p + q + r - c - a) * h a * h s
        - h (p + q - c) * h (r + s - b) * h b
        + h (p + q + r + s - c - a - b) * h a * h b) := by
  simp only [fourInterval, threeInterval]
  ring

/-- The linear coefficient at an interior minimum. -/
theorem middle_minimum_table {R : Type*} [CommRing R] (h : ℤ → R)
    (p q r s a c b : ℤ) :
    fourInterval h p q r s a c b =
      (h p * h q - h (p + q - a) * h a) *
        (h r * h s - h (r + s - b) * h b) - h c *
      (h (q + r - c) * h p * h s
        - h (p + q + r - a - c) * h a * h s
        - h (q + r + s - b - c) * h b * h p
        + h (p + q + r + s - a - c - b) * h a * h b) := by
  have hindex : q + r + s - c - b = q + r + s - b - c := by omega
  simp only [fourInterval, hindex]
  ring

/-- The L table: constant, linear, and quadratic coefficients of a repeated minimum. -/
theorem two_minimum_L_table {R : Type*} [CommRing R] (h : ℤ → R)
    (p q a b c d : ℤ) :
    fourInterval h p q a b c c d =
      h p * h q * (h a * h b - h (a + b - d) * h d)
      + h c * (-h (p + q - c) * h a * h b
        + h (p + q - c) * h (a + b - d) * h d
        - h p * h (q + a - c) * h b
        + h p * h (q + a + b - c - d) * h d)
      + h c ^ 2 * (h (p + q + a - 2 * c) * h b
        - h (p + q + a + b - 2 * c - d) * h d) := by
  have h1 : p + q + a - c - c = p + q + a - 2 * c := by omega
  have h2 : p + q + a + b - c - c - d = p + q + a + b - 2 * c - d := by omega
  simp only [fourInterval, h1, h2]
  ring

/-- The M table, with the same recovered constant block product as L. -/
theorem two_minimum_M_table {R : Type*} [CommRing R] (h : ℤ → R)
    (p q a b c d : ℤ) :
    fourInterval h p a b q c d c =
      h p * h q * (h a * h b - h (a + b - d) * h d)
      + h c * (-h (p + a - c) * h b * h q
        - h p * h a * h (q + b - c)
        + h (p + a + b - c - d) * h d * h q
        + h p * h (q + a + b - c - d) * h d)
      + h c ^ 2 * (h (p + a - c) * h (q + b - c)
        - h (p + q + a + b - 2 * c - d) * h d) := by
  have h1 : b + q - c = q + b - c := by omega
  have h2 : a + b + q - d - c = q + a + b - c - d := by omega
  have h3 : p + a + b + q - c - d - c = p + q + a + b - 2 * c - d := by omega
  simp only [fourInterval, h1, h2, h3]
  ring

/-- The actual three-row index array used by the smaller cut blocks. -/
def threeIndices (p q r a b : ℤ) : Matrix (Fin 3) (Fin 3) ℤ :=
  !![p, p + q - a, p + q + r - a - b;
     a, q, q + r - b;
     a + b - q, b, r]

/-- The three-row Hessenberg determinant of a genuine cut block. -/
theorem three_indices_det {R : Type*} [CommRing R] (h : ℤ → R)
    (hneg : ∀ k : ℤ, k < 0 → h k = 0)
    (p q r a b : ℤ) (hq : a + b < q) :
    ((threeIndices p q r a b).map h).det = threeInterval h p q r a b := by
  rw [Matrix.det_fin_three]
  change h p * h q * h r - h p * h (q + r - b) * h b -
    h (p + q - a) * h a * h r +
    h (p + q - a) * h (q + r - b) * h (a + b - q) +
    h (p + q + r - a - b) * h a * h b -
    h (p + q + r - a - b) * h q * h (a + b - q) = _
  rw [hneg (a + b - q) (by omega)]
  simp only [threeInterval]
  ring

end HessenbergExpansion

namespace Gluing.Profile

open HessenbergExpansion

/-- Intrinsic upper Hessenberg condition on the actual Jacobi--Trudi indices. -/
def Hessenberg {n : ℕ} (P : Profile n) : Prop :=
  IntrinsicHessenberg P.xi P.zeta

/-- The interval index is the sum of its rows minus its internal gaps. -/
def intervalLabel {n : ℕ} (P : Profile n) (a b : Fin (n + 1)) : ℤ :=
  (∑ i : Fin (n + 1), if a.val ≤ i.val ∧ i.val ≤ b.val then (P.r i : ℤ) else 0)
    - ∑ j : Fin n, if a.val ≤ j.val ∧ j.val < b.val then (P.g j : ℤ) else 0

/-- Explicit beta arithmetic identifies the interval expansion with the actual matrix. -/
theorem indices_four (P : Profile 3) :
    (Matrix.of fun i j : Fin 4 => P.xi i - P.zeta j) =
      fourIndices (P.r 0) (P.r 1) (P.r 2) (P.r 3) (P.g 0) (P.g 1) (P.g 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fourIndices, xi, zeta, Fin.sum_univ_succ] <;> ring

/-- Four-row intrinsic Hessenberg boards are exactly the legitimate strict domain. -/
theorem hessenberg_four_iff (P : Profile 3) :
    P.Hessenberg ↔ P.g 0 + P.g 1 < P.r 1 ∧ P.g 1 + P.g 2 < P.r 2 := by
  have hi (i j : Fin 4) := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℤ => M i j)
    P.indices_four
  constructor
  · intro h
    have h20 := h 2 0 (by decide)
    have h31 := h 3 1 (by decide)
    have hi20 := hi 2 0
    have hi31 := hi 3 1
    norm_num [fourIndices] at hi20 hi31
    omega
  · rintro ⟨hq, hr⟩ i j hij
    change P.xi i - P.zeta j < 0
    have hij' := hi i j
    fin_cases i <;> fin_cases j
    all_goals norm_num [fourIndices] at hij'
    all_goals norm_num at hij
    all_goals first
      | change P.xi 2 - P.zeta 0 < 0
      | change P.xi 3 - P.zeta 0 < 0
      | change P.xi 3 - P.zeta 1 < 0
    all_goals omega

/-- The strict endpoint bounds come from the profile, not extra proof hypotheses. -/
theorem four_domain (P : Profile 3) (hP : P.Hessenberg) :
    FourDomain (P.r 0) (P.r 1) (P.r 2) (P.r 3) (P.g 0) (P.g 1) (P.g 2) := by
  have hp := P.g_lt_castSucc 0
  have hs := P.g_lt_succ 2
  obtain ⟨hq, hr⟩ := P.hessenberg_four_iff.mp hP
  dsimp [FourDomain]
  norm_num at hp hs
  omega

/-- The eight-term formula for the full Schur polynomial, including `h_0 = 1`. -/
theorem schur_four_interval (P : Profile 3) (hP : P.Hessenberg) :
    P.schur = fourInterval hh (P.r 0) (P.r 1) (P.r 2) (P.r 3)
      (P.g 0) (P.g 1) (P.g 2) := by
  have hm : (Matrix.of fun i j : Fin 4 => hh (P.xi i - P.zeta j)) =
      (fourIndices (P.r 0) (P.r 1) (P.r 2) (P.r 3) (P.g 0) (P.g 1) (P.g 2)).map hh := by
    rw [← P.indices_four]
    rfl
  rw [schur, hm]
  exact four_indices_det hh (fun k hk => hh_of_neg hk) (P.four_domain hP)

/-- The same actual expansion before specializing the independent unit variable. -/
theorem schurHom_four_interval (P : Profile 3) (hP : P.Hessenberg) :
    P.schurHom = fourInterval hTilde (P.r 0) (P.r 1) (P.r 2) (P.r 3)
      (P.g 0) (P.g 1) (P.g 2) := by
  have hm : (Matrix.of fun i j : Fin 4 => hTilde (P.xi i - P.zeta j)) =
      (fourIndices (P.r 0) (P.r 1) (P.r 2) (P.r 3) (P.g 0) (P.g 1) (P.g 2)).map hTilde := by
    rw [← P.indices_four]
    rfl
  rw [schurHom, hm]
  exact four_indices_det hTilde (fun k hk => by simp [hTilde, hk]) (P.four_domain hP)

/-- The two-row determinant is the actual row product minus the merged-row term. -/
theorem det_two_interval {R : Type*} [CommRing R] (P : Profile 1) (h : ℤ → R) :
    (Matrix.of fun i j : Fin 2 => h (P.xi i - P.zeta j)).det =
      h (P.r 0) * h (P.r 1) - h ((P.r 0 : ℤ) + P.r 1 - P.g 0) * h (P.g 0) := by
  have h00 := P.xi_sub_zeta (0 : Fin 2)
  have h11 := P.xi_sub_zeta (1 : Fin 2)
  have h10 := P.xi_succ_sub_zeta_castSucc (0 : Fin 1)
  change P.xi 1 - P.zeta 0 = (P.g 0 : ℤ) at h10
  have h01 : P.xi 0 - P.zeta 1 = (P.r 0 : ℤ) + P.r 1 - P.g 0 := by
    have hz := P.zeta_castSucc (0 : Fin 1)
    norm_num at hz
    simp only [xi]
    omega
  rw [Matrix.det_fin_two]
  simp only [Matrix.of_apply, h00, h11, h10, h01]

theorem schurHom_two_interval (P : Profile 1) :
    P.schurHom = hTilde (P.r 0) * hTilde (P.r 1) -
      hTilde ((P.r 0 : ℤ) + P.r 1 - P.g 0) * hTilde (P.g 0) :=
  P.det_two_interval hTilde

theorem schur_two_interval (P : Profile 1) :
    P.schur = hh (P.r 0) * hh (P.r 1) -
      hh ((P.r 0 : ℤ) + P.r 1 - P.g 0) * hh (P.g 0) :=
  P.det_two_interval hh

/-- Smaller-block beta arithmetic retains the actual third lower index. -/
theorem indices_three (P : Profile 2) :
    (Matrix.of fun i j : Fin 3 => P.xi i - P.zeta j) =
      threeIndices (P.r 0) (P.r 1) (P.r 2) (P.g 0) (P.g 1) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [threeIndices, xi, zeta, Fin.sum_univ_succ] <;> ring

theorem schurHom_three_interval (P : Profile 2)
    (hq : P.g 0 + P.g 1 < P.r 1) :
    P.schurHom = threeInterval hTilde (P.r 0) (P.r 1) (P.r 2) (P.g 0) (P.g 1) := by
  have hm : (Matrix.of fun i j : Fin 3 => hTilde (P.xi i - P.zeta j)) =
      (threeIndices (P.r 0) (P.r 1) (P.r 2) (P.g 0) (P.g 1)).map hTilde := by
    rw [← P.indices_three]
    rfl
  rw [schurHom, hm]
  apply three_indices_det hTilde (fun k hk => by simp [hTilde, hk])
  omega

/-- A literal interval of rows, preserving every internal seam and its actual determinant. -/
def slice {n : ℕ} (P : Profile n) (a m : ℕ) (ham : a + m ≤ n) : Profile m where
  r i := P.r ⟨a + i.val, by omega⟩
  g j := P.g ⟨a + j.val, by omega⟩
  r_pos i := P.r_pos _
  g_lt_castSucc j := P.g_lt_castSucc ⟨a + j.val, by omega⟩
  g_lt_succ j := by
    have h := P.g_lt_succ ⟨a + j.val, by omega⟩
    have he : (⟨a + j.val, by omega⟩ : Fin n).succ =
        (⟨a + j.succ.val, by omega⟩ : Fin (n + 1)) := by
      apply Fin.ext
      simp only [Fin.val_succ, Nat.add_assoc]
    rw [he] at h
    exact h

theorem schurHom_single_interval (P : Profile 0) : P.schurHom = hTilde (P.r 0) := by
  rw [schurHom, Matrix.det_fin_one]
  simp [xi_sub_zeta]

theorem schur_single_interval (P : Profile 0) : P.schur = hh (P.r 0) := by
  rw [schur, Matrix.det_fin_one]
  simp [xi_sub_zeta]

/-- Every upper-triangular four-row index is its intrinsic interval label. -/
theorem intervalLabel_four_eq_index (P : Profile 3) (i j : Fin 4) (hij : i ≤ j) :
    P.intervalLabel i j = P.xi i - P.zeta j := by
  fin_cases i <;> fin_cases j
  all_goals norm_num [intervalLabel, xi, zeta, Fin.sum_univ_succ]
  all_goals norm_num at hij
  all_goals ring

/-- Rotation preserves the actual strict Hessenberg domain. -/
theorem hessenberg_rotate (P : Profile 3) (hP : P.Hessenberg) :
    P.rotate.Hessenberg := by
  rw [hessenberg_four_iff]
  obtain ⟨hq, hr⟩ := P.hessenberg_four_iff.mp hP
  simp [rotate]
  omega

/-- The same full expansion in the root complete-generator representation. -/
theorem schur_four_complete (P : Profile 3) (hP : P.Hessenberg) :
    P.schur = fourInterval complete (P.r 0) (P.r 1) (P.r 2) (P.r 3)
      (P.g 0) (P.g 1) (P.g 2) := by
  rw [P.schur_four_interval hP]
  simp only [fourInterval, complete_eq_hh]

end Gluing.Profile
end SkewJacobiNegative
