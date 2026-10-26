/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.ThinMarkedCells
import SkewGluing.Composition

/-!
# Literal composition by a horizontal outer ribbon

The one-part outer case of `lem:subthreshold-transport` in
`shields-2026-skew-class-inflation.tex`.  Composition is the actual
finite union of translated inner cells, not a Schur-function surrogate.
Sorry-free.
-/

namespace SkewClassInflation.ThinParameters

open SkewJacobiNegative SkewGluing

variable (B : ThinParameters)

/-- The horizontal outer places its successive inner copies along the specified displacement. -/
theorem mem_row_compose (m t : ℕ) (hm : 0 < m) (a b : ℤ) :
    (a, b) ∈ (B.inflationMark t).compose (rowCells 0 m) ↔
      ∃ k : ℤ, 0 ≤ k ∧ k < m ∧
        ((a + k = 0 ∧ (B.b : ℤ) - B.c - 1 ≤ b - k * (B.boundary.q - 1) ∧
            b - k * (B.boundary.q - 1) < (B.boundary.q : ℤ) + t - 1) ∨
          (a + k = 1 ∧ 0 ≤ b - k * (B.boundary.q - 1) ∧
            b - k * (B.boundary.q - 1) < (B.b : ℤ) + t)) := by
  rw [MarkedInner.compose_of_ordinary (rowCells_nonempty (by exact_mod_cast hm))
    (show ¬ (B.inflationMark t).case.IsMixed from by
      change ¬ AttachCase.a.IsMixed
      decide)]
  simp only [Prod.exists, mem_rowCells]
  constructor
  · rintro ⟨i, k, ⟨rfl, hk0, hkm⟩, hx⟩
    refine ⟨k, hk0, hkm, ?_⟩
    have horigin : (B.inflationMark t).origin (rowCells 0 m) (0, k) =
        (-k, k * (B.boundary.q - 1)) := by
      simp [MarkedInner.origin, inflationMark, content, eCell]
    rw [horigin, mem_translate] at hx
    simp only [Prod.mk_sub_mk, sub_neg_eq_add] at hx
    change (a + k, b - k * (B.boundary.q - 1)) ∈ B.innerCells t at hx
    exact (B.mem_innerCells t _ _).mp hx
  · rintro ⟨k, hk0, hkm, hx⟩
    refine ⟨0, k, ⟨rfl, hk0, hkm⟩, ?_⟩
    have horigin : (B.inflationMark t).origin (rowCells 0 m) (0, k) =
        (-k, k * (B.boundary.q - 1)) := by
      simp [MarkedInner.origin, inflationMark, content, eCell]
    rw [horigin, mem_translate]
    simp only [Prod.mk_sub_mk, sub_neg_eq_add]
    change (a + k, b - k * (B.boundary.q - 1)) ∈ B.innerCells t
    exact (B.mem_innerCells t _ _).mpr hx

/-- A one-part outer ribbon gives the literal inflated overlapped power, up to its fixed origin. -/
theorem row_compose_eq_innerPower (m t : ℕ) (hm : 0 < m) :
    (B.inflationMark t).compose (rowCells 0 m) =
      translate (1 - (m : ℤ), -(m : ℤ))
        (profileCells (Profile.inflate t (B.innerPower m hm))) := by
  ext x
  rcases x with ⟨a, b⟩
  rw [B.mem_row_compose m t hm, mem_translate]
  simp only [Prod.mk_sub_mk, sub_neg_eq_add, mem_profileCells,
    Profile.zeta_inflate, Profile.xi_inflate,
    (B.innerPower_beta m hm).1, (B.innerPower_beta m hm).2]
  have hq := B.boundary_q_eq
  have ha := B.c_lt_a
  have hb := B.a_lt_b
  have hc : (0 : ℤ) ≤ B.c := by positivity
  constructor
  · rintro ⟨k, hk0, hkm, (⟨hak, hlo, hhi⟩ | ⟨hak, hlo, hhi⟩)⟩
    · let i : Fin (m + 1) := ⟨((m : ℤ) - k - 1).toNat, by omega⟩
      have hi : (i.val : ℤ) = (m : ℤ) - k - 1 := by
        dsimp [i]
        omega
      have him : i.val ≠ m := by omega
      refine ⟨i, by omega, ?_, ?_⟩
      · rw [powerLower, ite_eq_right him]
        nlinarith
      · rw [powerUpper]
        split_ifs with hz
        · have hiz : (i.val : ℤ) = 0 := by exact_mod_cast hz
          nlinarith
        · nlinarith
    · let i : Fin (m + 1) := ⟨((m : ℤ) - k).toNat, by omega⟩
      have hi : (i.val : ℤ) = (m : ℤ) - k := by dsimp [i]; omega
      have hiz : i.val ≠ 0 := by omega
      refine ⟨i, by omega, ?_, ?_⟩
      · rw [powerLower]
        split_ifs with he
        · have hie : (i.val : ℤ) = m := by exact_mod_cast he
          nlinarith
        · nlinarith
      · rw [powerUpper, ite_eq_right hiz]
        nlinarith
  · rintro ⟨i, hi, hlo, hhi⟩
    have him := i.isLt
    by_cases hz : i.val = 0
    · have hiz : (i.val : ℤ) = 0 := by exact_mod_cast hz
      have hne : i.val ≠ m := by omega
      rw [powerLower, ite_eq_right hne] at hlo
      rw [powerUpper, ite_eq_left hz] at hhi
      refine ⟨(m : ℤ) - 1, by omega, by omega, Or.inl ⟨by omega, ?_, ?_⟩⟩ <;>
        nlinarith
    · by_cases he : i.val = m
      · have hie : (i.val : ℤ) = m := by exact_mod_cast he
        rw [powerLower, ite_eq_left he] at hlo
        rw [powerUpper, ite_eq_right hz] at hhi
        refine ⟨0, by omega, by omega, Or.inr ⟨by omega, ?_, ?_⟩⟩ <;>
          nlinarith
      · rw [powerLower, ite_eq_right he] at hlo
        rw [powerUpper, ite_eq_right hz] at hhi
        by_cases hcut : b < ((m : ℤ) - i.val) * (B.boundary.q - 1)
        · refine ⟨(m : ℤ) - i.val - 1, by omega, by omega,
            Or.inl ⟨by omega, ?_, ?_⟩⟩ <;> nlinarith
        · refine ⟨(m : ℤ) - i.val, by omega, by omega,
            Or.inr ⟨by omega, ?_, ?_⟩⟩ <;> nlinarith

end SkewClassInflation.ThinParameters
