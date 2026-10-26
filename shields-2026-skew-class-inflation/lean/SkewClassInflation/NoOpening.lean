/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.NoEscape
import SkewJacobiNegative.Gluing.Homogenization

/-!
# Equality transport before the first opening

Formalizes the homogeneous substitution in `eq:subthreshold-shift` of
`shields-2026-skew-class-inflation.tex`.  The negative-depth bound is a
property of the full board, not just its second subdiagonal.  The forward
transport and unrestricted lowering give both directions.  Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative

/-- None of the originally negative entries has reached a unit or a positive label. -/
def NoOpening {n : ℕ} (t : ℕ) (P : Profile n) : Prop :=
  ∀ i j, P.xi i - P.zeta j < 0 → P.xi i - P.zeta j + t < 0

/-- Substitute every homogenized generator, including the retained unit variable. -/
noncomputable def shiftHom (t : ℕ) : Gluing.HomLambda →ₐ[ℚ] CompleteRing :=
  MvPolynomial.aeval fun k : ℕ => complete ((k : ℤ) + t)

/-- The shifted homogeneous entry agrees with the actual inflated entry exactly off openings. -/
theorem shiftHom_entry (t : ℕ) (k : ℤ) (h : k < 0 → k + t < 0) :
    shiftHom t (Gluing.hTilde k) = complete (k + t) := by
  by_cases hk : k < 0
  · simp only [Gluing.hTilde, ite_eq_left hk, map_zero, complete_of_neg (h hk)]
  · rw [Gluing.hTilde, ite_eq_right hk, shiftHom, MvPolynomial.aeval_X]
    congr 1
    omega

/-- No-opening transport is an actual polynomial substitution of the retained-unit determinant. -/
theorem profileSchur_inflate_eq_shiftHom {n : ℕ} (t : ℕ) (P : Profile n)
    (h : NoOpening t P) :
    profileSchur (Profile.inflate t P) = shiftHom t P.schurHom := by
  rw [Gluing.Profile.schurHom, AlgHom.map_det]
  apply congrArg Matrix.det
  apply Matrix.ext
  intro i j
  simp only [Matrix.of_apply, Profile.index_inflate]
  exact (shiftHom_entry t _ (h i j)).symm

/-- Equal original functions remain equal whenever neither board has opened a negative entry. -/
theorem inflate_eq_of_noOpening {n : ℕ} (P Q : Profile n) (t : ℕ)
    (hP : NoOpening t P) (hQ : NoOpening t Q)
    (h : profileSchur P = profileSchur Q) :
    profileSchur (Profile.inflate t P) = profileSchur (Profile.inflate t Q) := by
  have hh : P.schurHom = Q.schurHom :=
    (Gluing.Profile.schur_eq_iff_schurHom_eq P Q).mp
      (by simpa only [profileSchur_eq_inherited] using h)
  rw [profileSchur_inflate_eq_shiftHom t P hP,
    profileSchur_inflate_eq_shiftHom t Q hQ, hh]

/-- Before openings, inflation preserves and reflects actual full Schur equality. -/
theorem inflate_eq_iff_of_noOpening {n : ℕ} (P Q : Profile n) (t : ℕ)
    (hP : NoOpening t P) (hQ : NoOpening t Q) :
    profileSchur (Profile.inflate t P) = profileSchur (Profile.inflate t Q) ↔
      profileSchur P = profileSchur Q :=
  ⟨profileSchur_eq_of_inflate_eq P Q t, inflate_eq_of_noOpening P Q t hP hQ⟩

/-- A uniform positive negative-depth margin prevents every opening below it. -/
theorem noOpening_of_depth {n : ℕ} (P : Profile n) {p t : ℕ} (ht : t < p)
    (h : ∀ i j, P.xi i - P.zeta j < 0 → P.xi i - P.zeta j ≤ -(p : ℤ)) :
    NoOpening t P := by
  intro i j hij
  have := h i j hij
  omega

end SkewClassInflation
