/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.BetaReduction

/-!
# Necessary polynomial tests for a supplied period

Formalizes `shields-2026-skew-corner-descent.tex`, «Period comparison and polynomial
obstructions» (`sec:periods`, `prop:period-tests`, `eq:candidate-defect`).
The tests concern actual irreducible divisors, not a reconstruction from the cofactor.

Sorry-free.
-/

namespace SkewGluing.MarkedInner
open SkewCornerDescent.Matrix
variable {ω : MarkedInner}

/-- Associates have the same maximum generator index. -/
theorem polynomialSpan_eq_of_associated {f g : Lambda} (hg : g ≠ 0)
    (he : Associated f g) : polynomialSpan f = polynomialSpan g := by
  exact le_antisymm (polynomialSpan_le_of_dvd hg he.dvd)
    (polynomialSpan_le_of_dvd (he.ne_zero_iff.mpr hg) he.symm.dvd)

/-- Every high-span prime has the exact transported residue and minimum span. -/
theorem IsLegal.highSpan_period_test (h : ω.IsLegal) {D : Diagram}
    (hD : IsConnectedSkew D) (hcard : 2 ≤ D.card) {f : Lambda}
    (hf : Irreducible f) (hs : ω.period ≤ (polynomialSpan f : ℤ))
    (hd : f ∣ cellSchur (diagramInterior (ω.compose D)) (h.connected_compose hD).1.interior) :
    ω.period + ω.width ≤ (polynomialSpan f : ℤ) ∧
      ((polynomialSpan f : ℤ) - ω.width) % ω.period = 0 := by
  obtain ⟨C, he⟩ := h.highSpan_factor_is_child hD hcard hf hs hd
  have hc := isConnectedSkew_component hD.1.interior C.2
  have hsp := polynomialSpan_eq_of_associated (h.irreducible_child hD C.2).ne_zero he
  rw [polynomialSpan_cellSchur (h.connected_compose hc)] at hsp
  have hv := span_compose hc h
  have hp : 0 < ω.period := by have := h.2.2.1.2; omega
  have hn : (1 : ℤ) ≤ span C.1 := by
    exact_mod_cast Finset.card_pos.mpr (hc.2.1.image content)
  constructor
  · rw [hsp, hv]
    nlinarith
  · rw [hsp, hv]
    simp only [add_sub_cancel_right, Int.mul_emod, Int.emod_self, mul_zero, Int.zero_emod]

/-- The only possible minimum-span connected factor is the supplied inner function. -/
theorem IsLegal.minimumSpan_factor (h : ω.IsLegal) {D G : Diagram}
    (hD : IsConnectedSkew D) (hcard : 2 ≤ D.card) (hG : IsConnectedSkew G)
    (hs : (span G : ℤ) = ω.period + ω.width)
    (hd : cellSchur G hG.1 ∣
      cellSchur (diagramInterior (ω.compose D)) (h.connected_compose hD).1.interior) :
    cellSchur G hG.1 = cellSchur ω.E h.1.1.1 := by
  have hf : Irreducible (cellSchur G hG.1) := by
    simpa only [map_integralCellSchur] using irreducible_integralCellSchur (K := ℚ) hG
  have hsp : ω.period ≤ (polynomialSpan (cellSchur G hG.1) : ℤ) := by
    rw [polynomialSpan_cellSchur hG]
    omega
  obtain ⟨C, he⟩ := h.highSpan_factor_is_child hD hcard hf hsp hd
  have hc := isConnectedSkew_component hD.1.interior C.2
  have hEq := cellSchur_eq_of_associated hG.1 (h.connected_compose hc).1 he
  have hEqsp := congrArg polynomialSpan hEq
  rw [polynomialSpan_cellSchur hG, polynomialSpan_cellSchur (h.connected_compose hc)] at hEqsp
  exact hEq.trans (h.child_at_minimum_span hD C.2 (by omega))

/-- A low-span prime cannot divide any irreducible actual child. -/
theorem IsLegal.lowSpan_not_dvd_child (h : ω.IsLegal) {D C : Diagram}
    (hD : IsConnectedSkew D) (hC : C ∈ edgeComponents (diagramInterior D)) {f : Lambda}
    (hf : Irreducible f) (hs : (polynomialSpan f : ℤ) < ω.period) :
    ¬ f ∣ cellSchur (ω.compose C)
      (h.connected_compose (isConnectedSkew_component hD.1.interior hC)).1 := by
  intro hd
  have he := hf.associated_of_dvd (h.irreducible_child hD hC) hd
  have hsp := polynomialSpan_eq_of_associated (h.irreducible_child hD hC).ne_zero he
  have hh := h.child_span_ge_period hD hC
  omega

/-- Above the mark width, a low-span prime occurs only in the middle normalization power. -/
theorem IsLegal.middle_multiplicity (h : ω.IsLegal) {D : Diagram}
    (hD : IsConnectedSkew D) (hcard : 2 ≤ D.card) {f : Lambda}
    (hf : Irreducible f) (hw : (ω.width : ℤ) < polynomialSpan f)
    (hp : (polynomialSpan f : ℤ) < ω.period) :
    emultiplicity f (cellSchur (diagramInterior (ω.compose D))
      (h.connected_compose hD).1.interior) =
      ((span D - span (diagramInterior D) : ℕ) : ℕ∞) *
        emultiplicity f (ω.normalC h) := by
  have hn (g : Lambda) (hgn : g ≠ 0) (hgs : polynomialSpan g ≤ ω.width) : ¬ f ∣ g := by
    intro hd
    have hb := polynomialSpan_le_of_dvd hgn hd
    have hb' : (polynomialSpan f : ℤ) ≤ ω.width := by exact_mod_cast hb.trans hgs
    omega
  obtain ⟨ha, hb, _, ht⟩ := h.normal_factors_ne_zero
  have hA : polynomialSpan (ω.normalA h) ≤ ω.width := by
    have := h.normal_mark_spans.1
    omega
  have hB : polynomialSpan (ω.normalB h) ≤ ω.width := by
    have := h.normal_mark_spans.2
    omega
  have hT : polynomialSpan (ω.normalTheta h) ≤ ω.width := by
    have hh := h.normalTheta_span_le
    have hw0 : (0 : ℤ) ≤ ω.width := Int.natCast_nonneg _
    have hh' : (polynomialSpan (ω.normalTheta h) : ℤ) ≤ ω.width := by omega
    exact_mod_cast hh'
  have hc : emultiplicity f (ω.childProduct h D hD.1) = 0 := by
    unfold childProduct
    rw [Finset.emultiplicity_prod hf.prime]
    apply Finset.sum_eq_zero
    intro C _
    exact emultiplicity_eq_zero.mpr (h.lowSpan_not_dvd_child hD C.2 hf hp)
  rw [h.corner_transport hD hcard, emultiplicity_mul hf.prime, hc, add_zero]
  unfold transportScalar
  rw [emultiplicity_mul hf.prime, emultiplicity_mul hf.prime,
    emultiplicity_mul hf.prime, emultiplicity_pow hf.prime,
    emultiplicity_pow hf.prime, emultiplicity_pow hf.prime,
    emultiplicity_eq_zero.mpr (hn _ ht hT),
    emultiplicity_eq_zero.mpr (hn _ ha hA),
    emultiplicity_eq_zero.mpr (hn _ hb hB)]
  simp only [mul_zero, zero_add]

/-- Middle-band factors obey both the sharp span bound and defect divisibility. -/
theorem IsLegal.middle_period_test (h : ω.IsLegal) {D : Diagram}
    (hD : IsConnectedSkew D) (hcard : 2 ≤ D.card) {f : Lambda}
    (hf : Irreducible f) (hw : (ω.width : ℤ) < polynomialSpan f)
    (hp : (polynomialSpan f : ℤ) < ω.period)
    (hd : f ∣ cellSchur (diagramInterior (ω.compose D))
      (h.connected_compose hD).1.interior) :
    (polynomialSpan f : ℤ) ≤ ω.period - ω.width - 2 ∧
      (span D - span (diagramInterior D)) ∣
        (emultiplicity f (cellSchur (diagramInterior (ω.compose D))
          (h.connected_compose hD).1.interior)).toNat := by
  have he := h.middle_multiplicity hD hcard hf hw hp
  have hc : f ∣ ω.normalC h := by
    by_contra hn
    rw [emultiplicity_eq_zero.mpr hn, mul_zero] at he
    exact (emultiplicity_eq_zero.mp he) hd
  have hsp := polynomialSpan_le_of_dvd h.normal_factors_ne_zero.2.2.1 hc
  have hb := h.normalC_span_le
  have hsp' : (polynomialSpan f : ℤ) ≤ polynomialSpan (ω.normalC h) := by
    exact_mod_cast hsp
  refine ⟨by omega, ?_⟩
  rw [he, ENat.toNat_mul, ENat.toNat_natCast]
  exact dvd_mul_right _ _

/-- The actual candidate defect is at least two. -/
theorem IsLegal.defect_ge_two {D : Diagram} (hD : IsConnectedSkew D)
    (hcard : 2 ≤ D.card) : 2 ≤ span D - span (diagramInterior D) := by
  have hh := IsLegal.corner_transport_exponents hD hcard
  omega

/-- The actual child function indexed by a southeast-interior component. -/
noncomputable def childFunction (ω : MarkedInner) (h : ω.IsLegal) {D : Diagram}
    (hD : IsConnectedSkew D) (C : {C // C ∈ edgeComponents (diagramInterior D)}) : Lambda :=
  cellSchur (ω.compose C.1)
    (h.connected_compose (isConnectedSkew_component hD.1.interior C.2)).1

open scoped Classical in
/-- The distinct high-span factors of the cofactor, in canonical primitive normalization. -/
noncomputable def highSpanSpectrum (ω : MarkedInner) (h : ω.IsLegal) {D : Diagram}
    (hD : IsConnectedSkew D) : Finset Lambda :=
  (edgeComponents (diagramInterior D)).attach.image (ω.childFunction h hD)

/-- The candidate outer span contributed by a factor. -/
noncomputable def candidateSpan (ω : MarkedInner) (f : Lambda) : ℕ :=
  (((polynomialSpan f : ℤ) - ω.width) / ω.period).toNat

/-- The candidate span of an actual child is exactly its outer's content span. -/
theorem IsLegal.candidateSpan_child (h : ω.IsLegal) {D : Diagram}
    (hD : IsConnectedSkew D) (C : {C // C ∈ edgeComponents (diagramInterior D)}) :
    ω.candidateSpan (ω.childFunction h hD C) = span C.1 := by
  have hp : ω.period ≠ 0 := by have := h.2.2.1.2; omega
  unfold candidateSpan childFunction
  rw [polynomialSpan_cellSchur
    (h.connected_compose (isConnectedSkew_component hD.1.interior C.2)),
    span_compose (isConnectedSkew_component hD.1.interior C.2) h, add_sub_cancel_right]
  simp only [Int.mul_ediv_cancel _ hp, Int.toNat_natCast]

open scoped Classical in
/-- Exact cofactor multiplicity equals the number of equal actual children. -/
theorem IsLegal.child_multiplicity_count (h : ω.IsLegal) {D : Diagram}
    (hD : IsConnectedSkew D) (hcard : 2 ≤ D.card)
    (C : {C // C ∈ edgeComponents (diagramInterior D)}) :
    emultiplicity (ω.childFunction h hD C)
      (cellSchur (diagramInterior (ω.compose D)) (h.connected_compose hD).1.interior) =
      (((edgeComponents (diagramInterior D)).attach.filter
        fun S => ω.childFunction h hD S = ω.childFunction h hD C).card : ℕ∞) := by
  classical
  have he (S : {C // C ∈ edgeComponents (diagramInterior D)}) :
      Associated (ω.childFunction h hD C) (ω.childFunction h hD S) ↔
        ω.childFunction h hD S = ω.childFunction h hD C := by
    constructor
    · intro hh
      exact (cellSchur_eq_of_associated
        (h.connected_compose (isConnectedSkew_component hD.1.interior C.2)).1
        (h.connected_compose (isConnectedSkew_component hD.1.interior S.2)).1 hh).symm
    · intro hh
      rw [hh]
  calc
    _ = ∑ S ∈ (edgeComponents (diagramInterior D)).attach,
        if Associated (ω.childFunction h hD C) (ω.childFunction h hD S)
          then (1 : ℕ∞) else 0 :=
      h.highSpan_multiplicity_count hD hcard (h.irreducible_child hD C.2)
        (h.child_span_ge_period hD C.2)
    _ = _ := by simp only [he, Finset.sum_boole]

/-- The factor-multiplicity candidate sum is exactly the total interior span. -/
theorem IsLegal.candidate_sum_eq_interior_span (h : ω.IsLegal) {D : Diagram}
    (hD : IsConnectedSkew D) (hcard : 2 ≤ D.card) :
    (∑ f ∈ ω.highSpanSpectrum h hD,
      (emultiplicity f (cellSchur (diagramInterior (ω.compose D))
        (h.connected_compose hD).1.interior)).toNat * ω.candidateSpan f) =
      span (diagramInterior D) := by
  classical
  unfold highSpanSpectrum
  have he := Finset.sum_comp (s := (edgeComponents (diagramInterior D)).attach)
    ω.candidateSpan (ω.childFunction h hD)
  simp only [nsmul_eq_mul] at he
  calc
    _ = ∑ f ∈ (edgeComponents (diagramInterior D)).attach.image (ω.childFunction h hD),
        ((edgeComponents (diagramInterior D)).attach.filter
          fun S => ω.childFunction h hD S = f).card * ω.candidateSpan f := by
      apply Finset.sum_congr rfl
      intro f hf
      obtain ⟨C, _, rfl⟩ := Finset.mem_image.mp hf
      rw [h.child_multiplicity_count hD hcard C, ENat.toNat_natCast]
    _ = ∑ C ∈ (edgeComponents (diagramInterior D)).attach,
        ω.candidateSpan (ω.childFunction h hD C) := he.symm
    _ = ∑ C ∈ (edgeComponents (diagramInterior D)).attach, span C.1 := by
      apply Finset.sum_congr rfl
      intro C _
      exact h.candidateSpan_child hD C
    _ = span (diagramInterior D) := by
      rw [Finset.sum_attach]
      exact sum_component_spans hD.1.interior

/-- Euclidean quotient and remainder recover the actual outer span and mark width. -/
theorem IsLegal.parent_div_mod (h : ω.IsLegal) {D : Diagram}
    (hD : IsConnectedSkew D) :
    (span (ω.compose D) : ℤ) / ω.period = span D ∧
      (span (ω.compose D) : ℤ) % ω.period = ω.width := by
  have hp : 0 < ω.period := by have := h.2.2.1.2; omega
  have hw : (ω.width : ℤ) < ω.period := h.2.2.1.2
  have hw0 : (0 : ℤ) ≤ ω.width := Int.natCast_nonneg _
  rw [span_compose hD h]
  constructor
  · rw [Int.add_ediv_of_dvd_left (dvd_mul_left _ _),
      Int.mul_ediv_cancel _ (ne_of_gt hp), Int.ediv_eq_zero_of_lt hw0 hw, add_zero]
  · rw [Int.add_emod, Int.mul_emod, Int.emod_self, mul_zero, Int.zero_emod,
      zero_add, Int.emod_eq_of_lt hw0 hw, Int.emod_eq_of_lt hw0 hw]

/-- All three polynomial period tests for an actual proper legal chart. -/
theorem IsLegal.period_tests (h : ω.IsLegal) {D : Diagram}
    (hD : IsConnectedSkew D) (hcard : 2 ≤ D.card) :
    let κ := cellSchur (diagramInterior (ω.compose D)) (h.connected_compose hD).1.interior
    let L := ∑ f ∈ ω.highSpanSpectrum h hD,
      (emultiplicity f κ).toNat * ω.candidateSpan f
    2 ≤ span D ∧
    (∀ f : Lambda, Irreducible f → ω.period ≤ (polynomialSpan f : ℤ) → f ∣ κ →
      ω.period + ω.width ≤ (polynomialSpan f : ℤ) ∧
        ((polynomialSpan f : ℤ) - ω.width) % ω.period = 0) ∧
    (∀ G : Diagram, ∀ hG : IsConnectedSkew G,
      (span G : ℤ) = ω.period + ω.width → cellSchur G hG.1 ∣ κ →
        cellSchur G hG.1 = cellSchur ω.E h.1.1.1) ∧
    2 ≤ span D - L ∧
    (∀ f : Lambda, Irreducible f → (ω.width : ℤ) < polynomialSpan f →
      (polynomialSpan f : ℤ) < ω.period → f ∣ κ →
        (polynomialSpan f : ℤ) ≤ ω.period - ω.width - 2 ∧
          (span D - L) ∣ (emultiplicity f κ).toNat) := by
  dsimp only
  rw [h.candidate_sum_eq_interior_span hD hcard]
  refine ⟨two_le_span_of_two_le_card hD hcard, ?_, ?_,
    IsLegal.defect_ge_two hD hcard, ?_⟩
  · intro f hf hs hd
    exact h.highSpan_period_test hD hcard hf hs hd
  · intro G hG hs hd
    exact h.minimumSpan_factor hD hcard hG hs hd
  · intro f hf hw hp hd
    exact h.middle_period_test hD hcard hf hw hp hd

end SkewGluing.MarkedInner
