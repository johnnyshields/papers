/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.ZeroSeamCoefficients
import SkewClassInflation.ProfileJoinBetas
import SkewJacobiNegative.FirstVariations

/-!
# Constant retained-unit coefficients along literal zero joins

Formalizes the source product reading used in `thm:two-row-thin-class`
of `shields-2026-skew-class-inflation.tex`.  Setting the unit coordinate
to zero makes the actual joined full matrix block triangular.  This
constant-coefficient identity needs no Hessenberg assumption.  Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative

/-- A nonpositive original index vanishes when the retained-unit variable is set to zero. -/
theorem unitEntry_coeff_zero_of_nonpos (k : ℤ) (hk : k ≤ 0) : (unitEntry k).coeff 0 = 0 := by
  rcases lt_or_eq_of_le hk with hk | rfl
  · simp [unitEntry, ne_of_lt hk, complete_of_neg hk]
  · simp [unitEntry]

/-- The whole actual zero-joined matrix factors at the retained-unit constant coefficient. -/
theorem unitSchur_zeroJoin_constant {n m : ℕ} (P : Profile n) (Q : Profile m) :
    (unitSchur (Profile.zeroJoin P Q)).coeff 0 = (unitSchur P).coeff 0 * (unitSchur Q).coeff 0 := by
  classical
  let J := Profile.zeroJoin P Q
  let e : Fin (n + 1) ⊕ Fin (m + 1) ≃ Fin (n + m + 2) :=
    finSumFinEquiv.trans (finCongr (by omega))
  let M : Matrix (Fin (n + m + 2)) (Fin (n + m + 2)) CompleteRing :=
    Matrix.of fun i j => (unitEntry (J.xi i - J.zeta j)).coeff 0
  let A : Matrix (Fin (n + 1)) (Fin (n + 1)) CompleteRing :=
    Matrix.of fun i j => (unitEntry (P.xi i - P.zeta j)).coeff 0
  let C : Matrix (Fin (m + 1)) (Fin (m + 1)) CompleteRing :=
    Matrix.of fun i j => (unitEntry (Q.xi i - Q.zeta j)).coeff 0
  let f : Polynomial CompleteRing →+* CompleteRing := Polynomial.constantCoeff
  let B := M.submatrix (fun i => e (Sum.inl i)) (fun j => e (Sum.inr j))
  have hxl (i : Fin (n + 1)) : J.xi (e (Sum.inl i)) = P.xi i + Q.xi 0 := by
    change (Profile.join P Q 0 (P.r_pos _) (Q.r_pos _)).xi
      ⟨i.val, by have := i.isLt; omega⟩ = P.xi i + Q.xi 0
    simpa only [Nat.cast_zero, sub_zero] using
      Profile.join_xi_left P Q 0 (P.r_pos _) (Q.r_pos _) i
  have hzl (i : Fin (n + 1)) : J.zeta (e (Sum.inl i)) = P.zeta i + Q.xi 0 := by
    change (Profile.join P Q 0 (P.r_pos _) (Q.r_pos _)).zeta
      ⟨i.val, by have := i.isLt; omega⟩ = P.zeta i + Q.xi 0
    simpa only [Nat.cast_zero, sub_zero] using
      Profile.join_zeta_left P Q 0 (P.r_pos _) (Q.r_pos _) i
  have hxr (i : Fin (m + 1)) : J.xi (e (Sum.inr i)) = Q.xi i :=
    Profile.join_xi_right P Q 0 (P.r_pos _) (Q.r_pos _) i
  have hzr (i : Fin (m + 1)) : J.zeta (e (Sum.inr i)) = Q.zeta i :=
    Profile.join_zeta_right P Q 0 (P.r_pos _) (Q.r_pos _) i
  have hb : M.submatrix e e = Matrix.fromBlocks A B 0 C := by
    apply Matrix.ext
    intro i j
    rcases i with i | i <;> rcases j with j | j
    · change (unitEntry (J.xi (e (Sum.inl i)) - J.zeta (e (Sum.inl j)))).coeff 0 =
        (unitEntry (P.xi i - P.zeta j)).coeff 0
      rw [hxl, hzl]
      apply congrArg (fun k : ℤ => (unitEntry k).coeff 0)
      ring
    · rfl
    · change (unitEntry (J.xi (e (Sum.inr i)) - J.zeta (e (Sum.inl j)))).coeff 0 = 0
      rw [hxr, hzl]
      apply unitEntry_coeff_zero_of_nonpos
      have hx := Q.xi_strictAnti.antitone (Fin.zero_le i)
      have hz := P.zeta_nonneg j
      omega
    · change (unitEntry (J.xi (e (Sum.inr i)) - J.zeta (e (Sum.inr j)))).coeff 0 =
        (unitEntry (Q.xi i - Q.zeta j)).coeff 0
      rw [hxr, hzr]
  have hd := Matrix.det_submatrix_equiv_self e M
  rw [hb, Matrix.det_fromBlocks_zero₂₁] at hd
  have hM : (unitSchur J).coeff 0 = M.det := by
    change f
      (Matrix.of fun i j : Fin (n + m + 2) => unitEntry (J.xi i - J.zeta j)).det = M.det
    exact f.map_det _
  have hA : (unitSchur P).coeff 0 = A.det := by
    change f (Matrix.of fun i j : Fin (n + 1) => unitEntry (P.xi i - P.zeta j)).det = A.det
    exact f.map_det _
  have hC : (unitSchur Q).coeff 0 = C.det := by
    change f (Matrix.of fun i j : Fin (m + 1) => unitEntry (Q.xi i - Q.zeta j)).det = C.det
    exact f.map_det _
  rw [hM, hA, hC]
  exact hd.symm

/-- A thick full board with positive gaps has no unit entry anywhere. -/
theorem thick_positive_gaps_zeroFree {n : ℕ} (P : Profile n)
    (hP : Staircase.Thick P) (hg : ∀ j, 0 < P.g j) : P.toBetaDiagram.ZeroFree := by
  intro i j he
  have hx : P.xi i - P.zeta j = 0 := sub_eq_zero.mpr he
  by_cases hij : i ≤ j
  · have hc := P.zeta_strictAnti.antitone hij
    have hr := P.xi_sub_zeta i
    have hp := P.r_pos i
    omega
  · have hji : j < i := lt_of_not_ge hij
    by_cases hf : j.val + 1 < i.val
    · have hn := hP.hessenberg i j hf
      omega
    · let s : Fin n := ⟨j.val, by have := i.isLt; change j.val < i.val at hji; omega⟩
      have hs0 : s.castSucc = j := Fin.ext rfl
      have hs1 : s.succ = i := by
        apply Fin.ext
        change s.val + 1 = i.val
        dsimp [s]
        change j.val < i.val at hji
        omega
      have h := P.xi_succ_sub_zeta_castSucc s
      rw [hs0, hs1, hx] at h
      have hp := hg s
      omega

/-- With no unit entries, the retained-unit polynomial is literally constant. -/
theorem unitSchur_eq_C_of_zeroFree {n : ℕ} (P : Profile n) (hP : P.toBetaDiagram.ZeroFree) :
    unitSchur P = Polynomial.C P.toBetaDiagram.schur := by
  rw [BetaDiagram.schur, Polynomial.C.map_det]
  apply congrArg Matrix.det
  apply Matrix.ext
  intro i j
  change unitEntry (P.xi i - P.zeta j) = Polynomial.C (complete (P.xi i - P.zeta j))
  have hn : P.xi i ≠ P.zeta j := hP i j
  rw [unitEntry, ite_eq_right (sub_ne_zero.mpr hn)]

end SkewClassInflation
