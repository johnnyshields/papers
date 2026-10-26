/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
import SkewMarkedFactor.TwoRowFamily
import SkewMarkedFactor.FactorRecovery

/-!
# Explicit readouts for the general two-row family

`eq:two-row-last` and `eq:two-row-previous` in «Explicit formulas and examples»
(`sec:examples`) of `shields-2026-skew-marked-factor.tex`.
The outer is an arbitrary connected skew diagram.  The singleton reading is
computed directly; all proper charts use the actual factor-recovery displays.
-/

namespace SkewMarkedFactor
open Gluing Gluing.Plan Gluing.MarkedInner MvPolynomial

/-- A row has complete function `h_n`, including the empty row. -/
theorem cellSchur_rowCells (n : ℕ) : cellSchur (rowCells 0 n) = hh n := by
  by_cases hn : n = 0
  · subst n
    have he : rowCells 0 0 = ∅ := by
      ext ⟨a, b⟩
      simp [mem_rowCells]
    change cellSchur (rowCells 0 0) = hh 0
    rw [he, cellSchur_empty, hh_zero]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    let P : Profile 0 :=
      { r := ![n]
        g := Fin.elim0
        r_pos := by intro i; fin_cases i; exact hnpos
        g_lt_castSucc := fun i => Fin.elim0 i
        g_lt_succ := fun i => Fin.elim0 i }
    have he : rowCells 0 n = P.cells := by
      ext ⟨a, b⟩
      rw [mem_rowCells, Profile.mem_cells]
      constructor
      · rintro ⟨rfl, hlo, hhi⟩
        refine ⟨0, rfl, ?_, ?_⟩ <;> simp [Profile.zeta, Profile.xi, P] <;> omega
      · rintro ⟨i, hi, hlo, hhi⟩
        fin_cases i
        simpa [Profile.zeta, Profile.xi, P] using And.intro hi.symm (And.intro hlo hhi)
    rw [he, cellSchur_cells, Profile.schur, Matrix.det_succ_row_zero]
    simp [Profile.zeta, Profile.xi, P]

/-- The two-by-two Jacobi–Trudi determinant is computed from the actual cells. -/
theorem twoRowInner_schur (s : TwoRowParameters) :
    cellSchur (twoRowInner s) = hh s.x * hh s.y - hh s.d * hh ((s.x : ℤ) + s.y - s.d) := by
  unfold twoRowInner twoRows
  rw [cellSchur_translate, cellSchur_cells, Profile.schur, Matrix.det_fin_two]
  rw [twoRow_xi, twoRow_zeta]
  change hh ((s.y : ℤ) - s.d + s.x - ((s.y : ℤ) - s.d)) *
      hh ((s.y : ℤ) - 0) -
      hh ((s.y : ℤ) - s.d + s.x - 0) * hh ((s.y : ℤ) - ((s.y : ℤ) - s.d)) = _
  have e0 : (s.y : ℤ) - s.d + s.x - ((s.y : ℤ) - s.d) = s.x := by ring
  have e1 : (s.y : ℤ) - s.d + s.x - 0 = (s.x : ℤ) + s.y - s.d := by ring
  have e2 : (s.y : ℤ) - ((s.y : ℤ) - s.d) = s.d := by ring
  rw [e0, e1, e2]
  simp only [sub_zero]
  ring

section Family
variable (s : TwoRowParameters)

/-- All three normalizers are proved from their actual finite hatted cell sets. -/
theorem twoRow_normalizers :
    normalizerRow (twoRowMark s) = hh s.w ∧
      normalizerColumn (twoRowMark s) = 1 ∧
      normalizerDiagonal (twoRowMark s) = hh s.d := by
  refine ⟨?_, ?_, ?_⟩
  · rw [normalizerRow]
    change cellSchur (translate (1, 0) (rowCells 0 s.w)) = _
    rw [cellSchur_translate, cellSchur_rowCells]
  · rw [normalizerColumn, twoRowMark_hatMarkFin, cellSchur_empty]
  · rw [normalizerDiagonal, twoRowMark_hatMiddle, cellSchur_translate, cellSchur_rowCells]

theorem twoRow_edgeSign : edgeSign (twoRowMark s) 1 = -1 := by
  simp [edgeSign, twoRowMark]

/-- Last display for the genuine proper chart, with unrestricted connected outer. -/
theorem twoRow_last_proper {D : Diagram} (hD : IsConnectedSkew D) (ha : 2 ≤ D.card) :
    deltaAt s.period D.card (cellSchur ((twoRowMark s).compose D)) =
      (-1 : Lambda) ^ D.card * C (standardTableauCount D : ℚ) *
        hh s.d ^ span D * hh s.w ^ numRows D := by
  have hχ := twoRowChart_proper s hD ha
  have ht := ordinary_last_display hχ
  rw [terminalDerivative, factor_recovery_order hχ] at ht
  obtain ⟨hA, hB, hC⟩ := twoRow_normalizers s
  simp only [Chart.parent, Chart.period, twoRowMark_period, Int.toNat_natCast,
    twoRow_edgeSign, Int.cast_neg, Int.cast_one, hA, hB, hC, one_pow, mul_one] at ht
  exact ht.trans (by ring)

/-- Penultimate display, including all zero normalizer boundaries. -/
theorem twoRow_previous_proper {D : Diagram} (hD : IsConnectedSkew D) (ha : 2 ≤ D.card) :
    deltaAt s.period (D.card - 1) (cellSchur ((twoRowMark s).compose D)) =
      (-1 : Lambda) ^ (D.card - 1) * C (standardTableauCount D : ℚ) *
        hh s.d ^ (span D - 1) * hh s.w ^ (numRows D - 1) *
          (hh s.x * hh s.y - hh s.d * hh ((s.x : ℤ) + s.y - s.d)) := by
  have hχ := twoRowChart_proper s hD ha
  have ht := ordinary_penultimate_display hχ
  rw [penultimateDerivative, factor_recovery_order hχ] at ht
  obtain ⟨hA, hB, hC⟩ := twoRow_normalizers s
  have hE : (twoRowMark s).E = twoRowInner s := rfl
  simp only [Chart.parent, Chart.period, twoRowMark_period, Int.toNat_natCast,
    twoRow_edgeSign, Int.cast_neg, Int.cast_one, hA, hB, hC, one_pow, mul_one,
    hE, twoRowInner_schur] at ht
  exact ht.trans (by ring)

/-- The actual single-cell composition is a translate of the inner. -/
theorem twoRow_parent_singleton (z : ℤ × ℤ) :
    cellSchur ((twoRowMark s).compose {z}) = cellSchur (twoRowInner s) := by
  have he : (twoRowMark s).compose {z} =
      translate ((twoRowMark s).origin {z} z) (twoRowInner s) := by
    ext t
    rw [mem_compose (Finset.singleton_nonempty z)]
    simp [MarkedInner.SameRibbon, twoRowMark]
  rw [he, cellSchur_translate]

/-- Direct one-cell calculation, not a proper-chart assumption on a singleton. -/
theorem twoRow_singleton_derivative (z : ℤ × ℤ) :
    pDeriv s.period (cellSchur ((twoRowMark s).compose {z})) =
      -(hh s.d * hh s.w) := by
  have hx := s.x_bound
  have hy := s.y_bound
  have hp := s.period_cast
  have hpos : 0 < s.period := by have := s.width_lt_period; omega
  have hxp : (s.x : ℤ) - s.period < 0 := by omega
  have hyp : (s.y : ℤ) - s.period < 0 := by omega
  have hdp : (s.d : ℤ) - s.period < 0 := by omega
  have hrest : (s.x : ℤ) + s.y - s.d - s.period = s.w := by omega
  rw [twoRow_parent_singleton, twoRowInner_schur, map_sub,
    Derivation.leibniz, Derivation.leibniz]
  simp only [Gluing.Plan.KernelAux.pDeriv_hh hpos, hh_of_neg hxp, hh_of_neg hyp, hh_of_neg hdp,
    hrest, smul_eq_mul, mul_zero, add_zero, zero_sub]

/-- The displayed formulas also hold for area one and impose no ribbon restriction. -/
theorem twoRow_formulas {D : Diagram} (hD : IsConnectedSkew D) :
    deltaAt s.period D.card (cellSchur ((twoRowMark s).compose D)) =
        (-1 : Lambda) ^ D.card * C (standardTableauCount D : ℚ) *
          hh s.d ^ span D * hh s.w ^ numRows D ∧
      deltaAt s.period (D.card - 1) (cellSchur ((twoRowMark s).compose D)) =
        (-1 : Lambda) ^ (D.card - 1) * C (standardTableauCount D : ℚ) *
          hh s.d ^ (span D - 1) * hh s.w ^ (numRows D - 1) *
            (hh s.x * hh s.y - hh s.d * hh ((s.x : ℤ) + s.y - s.d)) := by
  by_cases ha : 2 ≤ D.card
  · exact ⟨twoRow_last_proper s hD ha, twoRow_previous_proper s hD ha⟩
  · have hc : D.card = 1 := by have := hD.2.1.card_pos; omega
    obtain ⟨z, rfl⟩ := Finset.card_eq_one.mp hc
    have hr : numRows ({z} : Diagram) = 1 := by simp [numRows, rowSet]
    have hM : span ({z} : Diagram) = 1 := by simp [span, contents]
    constructor
    · simp only [Finset.card_singleton, standardTableauCount_singleton, hr, hM,
        pow_one, Nat.cast_one, map_one, mul_one, deltaAt_succ, deltaAt_zero]
      rw [twoRow_singleton_derivative]
      ring
    · simp only [Finset.card_singleton, standardTableauCount_singleton, hr, hM,
        Nat.sub_self, pow_zero, Nat.cast_one, map_one, mul_one, one_mul, deltaAt_zero]
      rw [twoRow_parent_singleton, twoRowInner_schur]

end Family
end SkewMarkedFactor
