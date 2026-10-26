/- TODO-COPIED: adapted from
`skew-factor-gluing/lean/SkewGluing/Aligned/InnerFactor/AgreeOrd.lean`. -/
import GluingCore.Aligned.InnerFactor.Agree

/-!
# Repetition of the outer, ordinary marks

Formalizes `shields-2026-skew-factor-gluing.tex`, «Equal and divisible periods»
(`prop:gluing-divisible`), via `eq:gluing-offsets` and fixed-chart injectivity.

For an ordinary legal mark (empty or not) the diagonal of `D ∘_ω E` on the private residue `w`
of the class `J` has the rows `[oRowLo J + ℓ_w, oRowHi J + h_w]`; repetition of the composite
therefore gives repetition of the outer, with the row shift `τ₁ - Δ v₁` in case (a) and
`Δ v₁ - τ₁` in case (b).

Sorry-free.
-/

namespace GluingCore

open MarkedInner

variable {ω : MarkedInner} {D : Diagram}

/-- The first and last rows of the private diagonal `w` of the class `J`, for every legal
ordinary mark. -/
theorem MarkedInner.IsLegal.ord_private_rows (hω : ω.IsLegal) (hmix : ¬ ω.case.IsMixed)
    (hD : IsConnectedSkew D) {J : ℤ} (hJ : minContent D ≤ J ∧ J ≤ maxContent D) :
    diagLo (ω.compose D) (minContent ω.E + (J * ω.period + ω.widthZ)) =
      ω.oRowLo D J + ω.lo ω.widthZ ∧
    diagHi (ω.compose D) (minContent ω.E + (J * ω.period + ω.widthZ)) =
      ω.oRowHi D J + ω.hi ω.widthZ := by
  by_cases hW : ω.W = ∅
  · have he : ω.IsLegalEmpty := ⟨hω, hW⟩
    have hq := he.period_pos
    have hw := he.width_zero
    have hc := he.classRows hD
    have hv : ValidClass (minContent D) (maxContent D) ω.widthZ J 0 := Or.inl hJ
    rw [hw]
    exact ⟨by simpa using hc.diagLo_eq (le_refl _) hq hv,
      by simpa using hc.diagHi_eq (le_refl _) hq hv⟩
  · exact ord_rows_w ⟨hω, Finset.nonempty_iff_ne_empty.mpr hW⟩ hD hmix hJ

namespace PerData

variable {a b Δ : ℤ} {τ : ℤ × ℤ}

/-- Repetition of the origin rows on the private residue, ordinary marks. -/
theorem oRow_shift (h : PerData ω D a b Δ τ) (hmix : ¬ ω.case.IsMixed) {J : ℤ}
    (h0 : minContent D + b ≤ J) (h1 : J ≤ minContent D + a - 1) :
    ω.oRowLo D (J + Δ) = ω.oRowLo D J + τ.1 ∧ ω.oRowHi D (J + Δ) = ω.oRowHi D J + τ.1 := by
  have hq := h.legal.period_pos
  have hwq := h.legal.2.2.1.2
  have hw0 : 0 ≤ ω.widthZ := by unfold widthZ; positivity
  have hwq' : ω.widthZ < ω.period := hwq
  have hexp : (minContent D + a - 1) * ω.period = (minContent D + a) * ω.period - ω.period := by
    ring
  have hM := h.hM
  have hΔ := h.hΔ
  have hb := h.hb
  have ha := h.ha
  have hJ : minContent D ≤ J ∧ J ≤ maxContent D := by omega
  have hJ' : minContent D ≤ J + Δ ∧ J + Δ ≤ maxContent D := by omega
  have r1 := h.legal.ord_private_rows hmix h.conn hJ
  have r2 := h.legal.ord_private_rows hmix h.conn hJ'
  have hk : minContent ω.E + (J * ω.period + ω.widthZ) ∈ contents (ω.compose D) := by
    rw [h.mem_contents_compose]
    have := mul_le_mul_of_nonneg_right hJ.1 hq.le
    have := mul_le_mul_of_nonneg_right hJ.2 hq.le
    unfold widthZ at *
    constructor <;> nlinarith
  have ds := h.diag_shift hk
    (by
      have := mul_le_mul_of_nonneg_right h0 hq.le
      nlinarith)
    (by
      have := mul_le_mul_of_nonneg_right h1 hq.le
      nlinarith)
  have e : minContent ω.E + (J * ω.period + ω.widthZ) + Δ * ω.period =
      minContent ω.E + ((J + Δ) * ω.period + ω.widthZ) := by ring
  rw [e] at ds
  rw [r1.1, r2.1] at ds
  have ds2 := ds.2
  have ds1 := ds.1
  rw [r1.2, r2.2] at ds2
  constructor <;> omega

/-- **Repetition of the outer, ordinary marks.** -/
theorem factorData_ord (h : PerData ω D a b Δ τ) (hmix : ¬ ω.case.IsMixed) :
    ∃ z₁, FactorData D a b Δ z₁ := by
  have hcc : ω.case = .a ∨ ω.case = .b := by
    unfold AttachCase.IsMixed at hmix
    cases hh : ω.case <;> simp_all
  have hM := h.hM
  rcases hcc with hc | hc
  · refine ⟨τ.1 - Δ * ω.rowShift, h.conn, h.ha, h.hb, h.hba, h.hΔ, h.hM, ?_⟩
    intro k h0 h1
    have o := h.oRow_shift hmix h0 h1
    have hp : (k + Δ) * ω.rowShift = k * ω.rowShift + Δ * ω.rowShift := by ring
    simp only [oRowLo, oRowHi, hc, hp] at o
    constructor <;> omega
  · refine ⟨Δ * ω.rowShift - τ.1, h.conn, h.ha, h.hb, h.hba, h.hΔ, h.hM, ?_⟩
    intro k h0 h1
    have o := h.oRow_shift hmix h0 h1
    have hp : (k + Δ) * ω.rowShift = k * ω.rowShift + Δ * ω.rowShift := by ring
    simp only [oRowLo, oRowHi, hc, hp] at o
    constructor <;> omega

end PerData

end GluingCore
