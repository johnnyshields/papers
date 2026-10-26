/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.ThinProjection

/-!
# Faithfulness of the thin-power substitution

Formalizes the injective substitution used in `eq:thin-substitution`
of `shields-2026-skew-class-inflation.tex` by an explicit section.
The actual specialized matrix has only its corner in the first row;
its complementary minor is the identity.  Sorry-free.
-/

namespace SkewClassInflation.ThinParameters

open SkewJacobiNegative

variable (B : ThinParameters)

/-- Every noncorner first-row entry vanishes under the explicit specialization. -/
theorem projection_power_first_row (m : ℕ) (hm : 0 < m) (j : Fin m) :
    B.projection (complete ((B.innerPower m hm).xi 0 -
      (B.innerPower m hm).zeta j.castSucc)) = 0 := by
  obtain ⟨hx, hz⟩ := B.innerPower_beta m hm
  rw [congrFun hx 0, congrFun hz j.castSucc]
  have hi : B.powerUpper m 0 - B.powerLower m j.castSucc =
      B.a + (j.val : ℤ) * B.boundary.q := by
    have hq := B.boundary_q_eq
    have hj := j.isLt
    simp only [powerUpper, Fin.val_zero, ite_true, powerLower, Fin.val_castSucc,
      ite_eq_right (show j.val ≠ m by omega)]
    nlinarith
  rw [hi, B.projection_residue B.a (by have := B.c_lt_a; omega)
    (by have := B.boundary_q_eq; have := B.a_lt_b; have := B.c_lt_a; omega)]
  rw [ite_eq_right (by intro h; exact (Nat.ne_of_gt B.c_lt_a) h.1)]

/-- The complementary corner minor becomes the identity at every positive power order. -/
theorem projection_power_minor (m : ℕ) (hm : 0 < m) (i j : Fin m) :
    B.projection (complete ((B.innerPower m hm).xi i.succ -
      (B.innerPower m hm).zeta j.castSucc)) = (1 : Matrix (Fin m) (Fin m) CompleteRing) i j := by
  obtain ⟨hx, hz⟩ := B.innerPower_beta m hm
  rw [congrFun hx i.succ, congrFun hz j.castSucc]
  have hi : B.powerUpper m i.succ - B.powerLower m j.castSucc =
      B.c + ((j.val : ℤ) - i.val) * B.boundary.q := by
    have hj := j.isLt
    simp only [powerUpper, Fin.val_succ, ite_eq_right (show i.val + 1 ≠ 0 by omega),
      powerLower, Fin.val_castSucc, ite_eq_right (show j.val ≠ m by omega),
      Nat.cast_add, Nat.cast_one]
    ring
  rw [hi, B.projection_residue B.c B.c_pos
    (by have := B.boundary_q_eq; have := B.a_lt_b; have := B.c_lt_a; omega)]
  by_cases hij : i = j
  · subst j
    simp
  · have hne : (j.val : ℤ) - i.val ≠ 0 := by
      intro he
      apply hij
      apply Fin.ext
      omega
    simp [hne, hij]

/-- The actual power functions have an explicit algebraic section.

**Differs from the paper's route.** A residue specialization gives a left inverse
on the power generators instead of the general triangular-substitution lemma. -/
theorem projection_innerPower (m : ℕ) (hm : 0 < m) :
    B.projection (B.innerPower m hm).toBetaDiagram.schur =
      MvPolynomial.X (⟨m, hm⟩ : ℕ+) := by
  classical
  let A : Matrix (Fin (m + 1)) (Fin (m + 1)) CompleteRing :=
    Matrix.of fun i j => B.projection
      (complete ((B.innerPower m hm).xi i - (B.innerPower m hm).zeta j))
  have he : B.projection (B.innerPower m hm).toBetaDiagram.schur = A.det :=
    B.projection.map_det _
  rw [he, Matrix.det_succ_row_zero, Finset.sum_eq_single (Fin.last m)]
  · have hcorner : A 0 (Fin.last m) =
        (-1 : CompleteRing) ^ m * MvPolynomial.X (⟨m, hm⟩ : ℕ+) := by
      change B.projection (complete ((B.innerPower m hm).xi 0 -
        (B.innerPower m hm).zeta (Fin.last m))) = _
      rw [Gluing.Profile.zeta_last, sub_zero, B.innerPower_span, B.projection_multiple]
    have hminor : A.submatrix Fin.succ (Fin.last m).succAbove = 1 := by
      rw [Fin.succAbove_last]
      apply Matrix.ext
      intro i j
      exact B.projection_power_minor m hm i j
    rw [hcorner, hminor, Matrix.det_one, Fin.val_last, mul_one]
    change (-1 : CompleteRing) ^ m *
      ((-1 : CompleteRing) ^ m * (MvPolynomial.X (⟨m, hm⟩ : ℕ+) : CompleteRing)) = _
    rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]
    rfl
  · intro j _ hj
    have hjm : j.val < m := by
      have hh : j.val ≠ m := fun he => hj (Fin.ext he)
      have := j.isLt
      omega
    have hh : A 0 j = 0 := B.projection_power_first_row m hm ⟨j.val, hjm⟩
    rw [hh, mul_zero, zero_mul]
  · simp

/-- Substitution by actual thin-power functions is injective, not merely formally triangular. -/
theorem power_substitution_injective :
    Function.Injective (MvPolynomial.aeval
      (fun m : ℕ+ => (B.innerPower m.val m.pos).toBetaDiagram.schur) :
        CompleteRing →ₐ[ℚ] CompleteRing) := by
  let f : CompleteRing →ₐ[ℚ] CompleteRing := MvPolynomial.aeval
    (fun m : ℕ+ => (B.innerPower m.val m.pos).toBetaDiagram.schur)
  have hsection : B.projection.comp f = AlgHom.id ℚ CompleteRing := by
    apply MvPolynomial.algHom_ext
    intro m
    simp only [AlgHom.comp_apply, f, MvPolynomial.aeval_X, AlgHom.id_apply,
      B.projection_innerPower]
    rfl
  have hleft : Function.LeftInverse B.projection f := fun p =>
    DFunLike.congr_fun hsection p
  exact hleft.injective

end SkewClassInflation.ThinParameters
