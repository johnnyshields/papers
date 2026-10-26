/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.ElementaryAlphabetBridge
import Shields.Combinatorics.Young.LGVOddTableau

/-!
# Universal omega on the full profile determinant

Supports `shields-2026-skew-corner-descent.tex` (`cor:row-pencil`).
Elementary specialization of the complete original profile determinant is the
Schur function of the transposed skew shape. Sorry-free.
-/

namespace SkewCornerDescent

open SkewGluing MvPolynomial

/-- A positive row cannot be filled from an empty alphabet. -/
theorem completeHom_empty_of_pos {R : Type*} [CommRing R] (x : ℕ → R)
    {p : ℕ} (hp : 0 < p) : Shields.completeHom 0 p x = 0 := by
  unfold Shields.completeHom
  apply Shields.skewSchur_eq_zero_of_lt_skewColLen (j := 0)
  rw [Shields.skewColLen, Shields.colLen_rect_of_lt hp, Shields.colLen_bot]
  decide

/-- With no even variables, the full mixed coefficient is the elementary one. -/
theorem superHom_empty_even {R : Type*} [CommRing R] (a p : ℕ) (x : ℕ → R) :
    Shields.superHom 0 a p x x = Shields.elemHom a p x := by
  rw [Shields.superHom, Finset.sum_eq_single 0]
  · rw [Shields.completeHom_zero, one_mul, Nat.sub_zero]
  · intro b _ hb
    rw [completeHom_empty_of_pos x (Nat.pos_of_ne_zero hb), zero_mul]
  · intro h
    exact (h (Finset.mem_range.mpr (Nat.succ_pos p))).elim

/-- The original integer-indexed complete generator specializes to the
integer-indexed elementary coefficient, including zero and negative indices. -/
theorem aeval_elementary_hh {R : Type*} [CommRing R] [Algebra ℚ R]
    (a : ℕ) (x : ℕ → R) (j : ℤ) :
    aeval (fun n : ℕ+ => Shields.elemHom a n x) (hh j) =
      if j < 0 then 0 else Shields.elemHom a j.toNat x := by
  unfold hh
  split_ifs with h
  · simp only [map_zero]
  · by_cases h0 : 0 < j.toNat
    · have hp := hPos_pnat ⟨j.toNat, h0⟩
      simp only [PNat.mk_coe] at hp
      rw [hp]
      exact aeval_X _ _
    · have hj : j.toNat = 0 := by omega
      rw [hj]
      simp only [hPos_zero, map_one, Shields.elemHom_zero]

/-- Elementary specialization of every complete profile determinant gives
its actual transposed tableau shape, not an independently substituted row model. -/
theorem aeval_elementary_profile_schur {n : ℕ} {R : Type*} [CommRing R]
    [Algebra ℚ R] (a : ℕ) (x : ℕ → R) (P : Profile n) :
    aeval (fun k : ℕ+ => Shields.elemHom a k x) P.schur =
      Shields.skewSchur P.lam.transpose P.mu.transpose a x := by
  rw [← Shields.superSkewSchur_zero_even x x P.mu_le_lam,
    ← Shields.jacobiTrudiDet_eq_superSkewSchur
      (fun k => (superHom_empty_even a k x).symm) P.mu_le_lam
      (fun i hi => P.rowLen_lam_of_le hi)]
  rw [Profile.schur, AlgHom.map_det, Shields.jacobiTrudiDet]
  congr 1
  ext u v
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
    aeval_elementary_hh, Shields.jtCoeff, Profile.rowLen_lam, Profile.rowLen_mu]
  have h1 := P.xi_pos u
  have h2 := P.zeta_nonneg v
  have h3 := P.zeta_nonneg u
  split_ifs with ha hb hb
  · omega
  · rfl
  · congr 2
    omega
  · omega

/-- Full universal omega of the profile Schur polynomial evaluates to the
transposed shape on every independent finite alphabet. -/
theorem evalComplete_schurInvolution_profile {n : ℕ} (a : ℕ) (P : Profile n) :
    evalComplete a (varAlphabet a) (schurInvolution P.schur) =
      Shields.skewSchur P.lam.transpose P.mu.transpose a (varAlphabet a) := by
  have h := AlgHom.congr_fun (evalComplete_comp_schurInvolution_elemHom a) P.schur
  change evalComplete a (varAlphabet a) (schurInvolution P.schur) =
    aeval (fun k : ℕ+ => Shields.elemHom a k (varAlphabet a)) P.schur at h
  rw [h, aeval_elementary_profile_schur]

end SkewCornerDescent
