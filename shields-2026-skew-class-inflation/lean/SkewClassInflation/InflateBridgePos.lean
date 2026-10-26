/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.InflateBridge

/-!
# The private bits of the inner, positive width, all four attachment cases

Supports `lem:inflate-chart` in `shields-2026-skew-class-inflation.tex`, \(0<w<q-1\).  If the
composite of a connected outer, with a one in each word, with a legal mark satisfies
\(B_T(j)A_T(j+1)=0\), then the private diagonals of the inflated inner are singletons:
\(A_E(w+1)=0\) and \(B_E(q-1)=0\).  Case (a) is `PosWidthA.private_bits`; case (b) is
`private_bits_b`, case (d) is `private_bits_d`, and case (c) follows from (d) by rotation.
Sorry-free.
-/

namespace SkewClassInflation

open SkewGluing SkewGluing.MarkedInner

namespace PosWidthB

variable {ω : MarkedInner} {D : Diagram}

theorem hex_b (hcb : ω.case = .b) : ω.ordT = 1 := by
  unfold MarkedInner.ordT
  simp [hcb]

theorem blockA (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D) (hcb : ω.case = .b) {s t : ℤ}
    (hph : ω.IsPhases s t) {J a : ℤ} (hJ1 : minContent D ≤ J) (hJ2 : J ≤ maxContent D)
    (ha1 : 1 ≤ a) (haq : a < ω.period) (has : a ≠ s) :
    SkewGluing.wordA (ω.compose D) ((J - minContent D) * ω.period + a) =
      SkewGluing.wordA ω.E a := by
  have hmix : ¬ ω.case.IsMixed := by simp [AttachCase.IsMixed, hcb]
  have hz := hex_b hcb
  have hc := ord_classRows h hD hmix
  have hmin := h.minContent_compose' hD
  have hv : ValidClass (minContent D) (maxContent D) ω.widthZ J a := Or.inl ⟨hJ1, hJ2⟩
  rw [hc.wordA_class' hmin rfl (by omega) haq hv (fun h0 => by omega),
    ord_classBitLo h hD hmix hph (by omega) haq hv (fun h0 => by omega)
      ⟨fun h1 => by omega, fun _ => has⟩]
  have hne : a ≠ 0 := by omega
  simp only [hne, ite_false]
  unfold SkewGluing.wordA bitA MarkedInner.lo
  have e : minContent ω.E + (a - 1) = minContent ω.E + a - 1 := by ring
  rw [e]

theorem blockB (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D) (hcb : ω.case = .b) {s t : ℤ}
    (hph : ω.IsPhases s t) {J a : ℤ} (hJ1 : minContent D ≤ J) (hJ2 : J ≤ maxContent D)
    (ha1 : 1 ≤ a) (haq : a < ω.period) (hat : a ≠ t) :
    SkewGluing.wordB (ω.compose D) ((J - minContent D) * ω.period + a) =
      SkewGluing.wordB ω.E a := by
  have hmix : ¬ ω.case.IsMixed := by simp [AttachCase.IsMixed, hcb]
  have hz := hex_b hcb
  have hc := ord_classRows h hD hmix
  have hmin := h.minContent_compose' hD
  have hv : ValidClass (minContent D) (maxContent D) ω.widthZ J a := Or.inl ⟨hJ1, hJ2⟩
  rw [hc.wordB_class' hmin rfl (by omega) haq hv (fun h0 => by omega),
    ord_classBitHi h hD hmix hph (by omega) haq hv (fun h0 => by omega)
      ⟨fun h1 => by omega, fun _ => hat⟩]
  have hne : a ≠ 0 := by omega
  simp only [hne, ite_false]
  unfold SkewGluing.wordB bitB MarkedInner.hi
  have e : minContent ω.E + (a - 1) = minContent ω.E + a - 1 := by ring
  rw [e]

theorem resA_one (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D) (hcb : ω.case = .b) {s t : ℤ}
    (hph : ω.IsPhases s t) {J : ℤ} (hJ1 : minContent D + 1 ≤ J) (hJ2 : J ≤ maxContent D) :
    SkewGluing.wordA (ω.compose D) ((J - minContent D) * ω.period) = 1 := by
  have hmix : ¬ ω.case.IsMixed := by simp [AttachCase.IsMixed, hcb]
  have hz := hex_b hcb
  have hc := ord_classRows h hD hmix
  have hmin := h.minContent_compose' hD
  have hq := h.width_lt_period
  have hw := h.width_pos
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph
  have hv : ValidClass (minContent D) (maxContent D) ω.widthZ J 0 := Or.inl ⟨by omega, hJ2⟩
  have := hc.wordA_class' hmin (J := J) (a := 0) (k := (J - minContent D) * ω.period)
    (by ring) le_rfl (by omega) hv (fun _ => hJ1)
  rw [this, ord_classBitLo h hD hmix hph le_rfl (by omega) hv (fun _ => hJ1)
    ⟨fun h1 => by omega, fun _ => by omega⟩]
  simp

theorem wordB_w_one (h : ω.IsLegalNonempty) (hcb : ω.case = .b) :
    SkewGluing.wordB ω.E ω.widthZ = 1 := by
  have hmix : ¬ ω.case.IsMixed := by simp [AttachCase.IsMixed, hcb]
  have hz := hex_b hcb
  have hw := h.width_pos
  have hcaps := ((ord_E_facts h hmix).2.2) hz
  unfold SkewGluing.wordB bitB
  unfold MarkedInner.hi at hcaps
  have e : minContent ω.E + ω.widthZ - 1 = minContent ω.E + (ω.widthZ - 1) := by ring
  rw [e]
  omega

/-- **Case (b): the private bits of the inner.** -/
theorem private_bits (h : ω.IsLegalNonempty) (hcb : ω.case = .b) (hD : IsConnectedSkew D)
    (hwq : ω.widthZ + 1 < ω.period)
    (hAD : ∃ j : ℤ, 1 ≤ j ∧ j < (span D : ℤ) ∧ SkewGluing.wordA D j = 1)
    (hz : ∀ j : ℤ, 1 ≤ j → j + 1 < (span (ω.compose D) : ℤ) →
      SkewGluing.wordB (ω.compose D) j * SkewGluing.wordA (ω.compose D) (j + 1) = 0) :
    SkewGluing.wordA ω.E (ω.widthZ + 1) = 0 ∧ SkewGluing.wordB ω.E (ω.period - 1) = 0 := by
  obtain ⟨s, t, hph⟩ := h.exists_phases
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph
  have hw := h.width_pos
  have hsF := h.span_compose_eq hD
  have hsp := span_eq_of_isConnectedSkew hD
  obtain ⟨jA, hjA1, hjA2, -⟩ := hAD
  have hmM : minContent D + 1 ≤ maxContent D := by omega
  constructor
  · have hB1 := wordB_w_one h hcb
    have b1 := blockB h hD hcb hph (J := minContent D) le_rfl (by omega) (a := ω.widthZ)
      (by omega) (by omega) (by omega)
    have a1 := blockA h hD hcb hph (J := minContent D) le_rfl (by omega) (a := ω.widthZ + 1)
      (by omega) (by omega) (by omega)
    have := hz ((minContent D - minContent D) * ω.period + ω.widthZ) (by simp; omega) (by
      rw [hsF]; simp; nlinarith)
    rw [b1, hB1, one_mul, show (minContent D - minContent D) * ω.period + ω.widthZ + 1 =
      (minContent D - minContent D) * ω.period + (ω.widthZ + 1) by ring, a1] at this
    exact this
  · have r1 := resA_one h hD hcb hph (J := minContent D + 1) (by omega) (by omega)
    have b1 := blockB h hD hcb hph (J := minContent D) le_rfl (by omega)
      (a := ω.period - 1) (by omega) (by omega) (by omega)
    have := hz ((minContent D - minContent D) * ω.period + (ω.period - 1)) (by simp; omega) (by
      rw [hsF]; simp; nlinarith)
    rw [b1, show (minContent D - minContent D) * ω.period + (ω.period - 1) + 1 =
      (minContent D + 1 - minContent D) * ω.period by ring, r1, mul_one] at this
    exact this

end PosWidthB

namespace PosWidthD

variable {ω : MarkedInner} {D : Diagram}

theorem blockB_w (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D) (hcd : ω.case = .d) {s t : ℤ}
    (hph : ω.IsPhases s t) {J : ℤ} (hJ1 : minContent D ≤ J) (hJ2 : J ≤ maxContent D) :
    SkewGluing.wordB (ω.compose D) ((J - minContent D) * ω.period + ω.widthZ) = 1 := by
  have hlt := h.phases_lt (Or.inr hcd) hph
  have hc := mix_classRows h hD hcd hph hlt
  have hmin := h.minContent_compose' hD
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hv : ValidClass (minContent D) (maxContent D) ω.widthZ J ω.widthZ := Or.inl ⟨hJ1, hJ2⟩
  rw [hc.wordB_class' hmin rfl (by omega) hq hv (fun h0 => by omega)]
  exact mix_classBitHi_w h hcd J

theorem blockB (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D) (hcd : ω.case = .d) {s t : ℤ}
    (hph : ω.IsPhases s t) {J a : ℤ} (hJ1 : minContent D ≤ J) (hJ2 : J ≤ maxContent D)
    (ha1 : 1 ≤ a) (haq : a < ω.period) :
    SkewGluing.wordB (ω.compose D) ((J - minContent D) * ω.period + a) =
      SkewGluing.wordB ω.E a := by
  have hlt := h.phases_lt (Or.inr hcd) hph
  have hc := mix_classRows h hD hcd hph hlt
  have hmin := h.minContent_compose' hD
  have hv : ValidClass (minContent D) (maxContent D) ω.widthZ J a := Or.inl ⟨hJ1, hJ2⟩
  rw [hc.wordB_class' hmin rfl (by omega) haq hv (fun h0 => by omega),
    mix_classBitHi h hcd J a (by omega) haq]
  have hne : a ≠ 0 := by omega
  simp only [hne, ite_false]
  unfold SkewGluing.wordB bitB MarkedInner.hi
  have e : minContent ω.E + (a - 1) = minContent ω.E + a - 1 := by ring
  rw [e]

/-- On the first private residue after the mark, the word `A` repeats the word of the inner. -/
theorem blockA_w1 (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D) (hcd : ω.case = .d) {s t : ℤ}
    (hph : ω.IsPhases s t) {J : ℤ} (hJ1 : minContent D ≤ J) (hJ2 : J ≤ maxContent D)
    (hwq : ω.widthZ + 1 < ω.period) :
    SkewGluing.wordA (ω.compose D) ((J - minContent D) * ω.period + (ω.widthZ + 1)) =
      SkewGluing.wordA ω.E (ω.widthZ + 1) := by
  have hlt := h.phases_lt (Or.inr hcd) hph
  have hc := mix_classRows h hD hcd hph hlt
  have hmin := h.minContent_compose' hD
  have hw := h.width_pos
  have hv : ValidClass (minContent D) (maxContent D) ω.widthZ J (ω.widthZ + 1) :=
    Or.inl ⟨hJ1, hJ2⟩
  have hv' := validClass_pred hv
  rw [hc.wordA_class' hmin rfl (by omega) (by omega) hv (fun h0 => by omega)]
  unfold classBitLo
  simp only [show ω.widthZ + 1 ≠ 0 by omega, ite_false]
  rw [mixLo_formula h hD hcd hph (by omega) hv', mixLo_formula h hD hcd hph (by omega) hv]
  unfold mixGLo SkewGluing.wordA bitA MarkedInner.lo
  have e : minContent ω.E + (ω.widthZ + 1 - 1) = minContent ω.E + (ω.widthZ + 1) - 1 := by ring
  simp only [show ¬ (ω.widthZ + 1 - 1 < ω.widthZ) by omega,
    show ¬ (ω.widthZ + 1 < ω.widthZ) by omega, ite_false]
  rw [show ω.widthZ + 1 - 1 = ω.widthZ by ring] at *
  rw [show minContent ω.E + (ω.widthZ + 1) - 1 = minContent ω.E + ω.widthZ by ring]
  ring

/-- At the residue zero with `t ≥ 1` the word `A` of the composite is one. -/
theorem resA_one (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D) (hcd : ω.case = .d) {s t : ℤ}
    (hph : ω.IsPhases s t) (ht1 : 1 ≤ t) {J : ℤ} (hJ1 : minContent D + 1 ≤ J)
    (hJ2 : J ≤ maxContent D) :
    SkewGluing.wordA (ω.compose D) ((J - minContent D) * ω.period) = 1 := by
  have hlt := h.phases_lt (Or.inr hcd) hph
  have hc := mix_classRows h hD hcd hph hlt
  have hmin := h.minContent_compose' hD
  have hq := h.width_lt_period
  have hw := h.width_pos
  obtain ⟨hs1, hs2, -, ht2, -, -⟩ := id hph
  have hv : ValidClass (minContent D) (maxContent D) ω.widthZ J 0 := Or.inl ⟨by omega, hJ2⟩
  rw [hc.wordA_class' hmin (J := J) (a := 0) (k := (J - minContent D) * ω.period)
    (by ring) le_rfl (by omega) hv (fun _ => hJ1)]
  unfold classBitLo
  simp only [ite_true]
  have hv1 := validClass_prev (ω.period - 1) hv hJ1
  rw [mixLo_formula h hD hcd hph (by omega) hv1, mixLo_formula h hD hcd hph le_rfl hv]
  have hcp := (d_caps h hcd).2
  have f0 := d_E_facts h hcd hph (a := 0) le_rfl (by omega)
  have hW0 := h.diagLo_W (a := 0) le_rfl (by omega)
  simp only [dLo, dHi, zero_add] at hcp f0 hW0
  have hp : (J - 1) * ω.rowShift = J * ω.rowShift - ω.rowShift := by ring
  unfold mixGLo profM
  unfold ValidClass at hv
  have hq1 : ω.period - 1 ≥ ω.widthZ := by omega
  simp only [show ¬ (ω.period - 1 < ω.widthZ) by omega, ite_false, show (0 : ℤ) < ω.widthZ by omega,
    show (0 : ℤ) < t by omega, and_true, ite_true] at *
  split_ifs <;> omega

/-- **Case (d): the private bits of the inner.** -/
theorem private_bits (h : ω.IsLegalNonempty) (hcd : ω.case = .d) (hD : IsConnectedSkew D)
    (hwq : ω.widthZ + 1 < ω.period)
    (hAD : ∃ j : ℤ, 1 ≤ j ∧ j < (span D : ℤ) ∧ SkewGluing.wordA D j = 1)
    (hz : ∀ j : ℤ, 1 ≤ j → j + 1 < (span (ω.compose D) : ℤ) →
      SkewGluing.wordB (ω.compose D) j * SkewGluing.wordA (ω.compose D) (j + 1) = 0) :
    SkewGluing.wordA ω.E (ω.widthZ + 1) = 0 ∧ SkewGluing.wordB ω.E (ω.period - 1) = 0 := by
  obtain ⟨s, t, hph⟩ := h.exists_phases
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph
  have hw := h.width_pos
  have hsF := h.span_compose_eq hD
  have hsp := span_eq_of_isConnectedSkew hD
  obtain ⟨jA, hjA1, hjA2, hjA3⟩ := hAD
  constructor
  · have b1 := blockB_w h hD hcd hph (J := minContent D) le_rfl (by omega)
    have a1 := blockA_w1 h hD hcd hph (J := minContent D) le_rfl (by omega) hwq
    have := hz ((minContent D - minContent D) * ω.period + ω.widthZ) (by simp; omega) (by
      rw [hsF]; simp; nlinarith)
    rw [b1, one_mul, show (minContent D - minContent D) * ω.period + ω.widthZ + 1 =
      (minContent D - minContent D) * ω.period + (ω.widthZ + 1) by ring, a1] at this
    exact this
  · by_cases ht0 : t = 0
    · have iface := (IsLegalNonempty.interface_d h hD hcd hph (j := jA) hjA1 hjA2).1
      rw [ht0, add_zero, hjA3] at iface
      have b1 := blockB h hD hcd hph (J := minContent D + jA - 1) (by omega) (by omega)
        (a := ω.period - 1) (by omega) (by omega)
      have e : (minContent D + jA - 1 - minContent D) * ω.period + (ω.period - 1) =
          jA * ω.period - 1 := by ring
      rw [e] at b1
      have := hz (jA * ω.period - 1) (by nlinarith) (by rw [hsF]; nlinarith)
      rw [b1, show jA * ω.period - 1 + 1 = jA * ω.period by ring, iface, mul_one] at this
      exact this
    · have r1 := resA_one h hD hcd hph (by omega) (J := minContent D + 1) (by omega) (by omega)
      have b1 := blockB h hD hcd hph (J := minContent D) le_rfl (by omega)
        (a := ω.period - 1) (by omega) (by omega)
      have := hz ((minContent D - minContent D) * ω.period + (ω.period - 1)) (by simp; omega) (by
        rw [hsF]; simp; nlinarith)
      rw [b1, show (minContent D - minContent D) * ω.period + (ω.period - 1) + 1 =
        (minContent D + 1 - minContent D) * ω.period by ring, r1, mul_one] at this
      exact this

end PosWidthD

namespace PosWidthC

variable {ω : MarkedInner} {D : Diagram}

/-- **Case (c): the private bits of the inner**, from case (d) by rotation. -/
theorem private_bits (h : ω.IsLegalNonempty) (hcc : ω.case = .c) (hD : IsConnectedSkew D)
    (hwq : ω.widthZ + 1 < ω.period)
    (hBD : ∃ j : ℤ, 1 ≤ j ∧ j < (span D : ℤ) ∧ SkewGluing.wordB D j = 1)
    (hz : ∀ j : ℤ, 1 ≤ j → j + 1 < (span (ω.compose D) : ℤ) →
      SkewGluing.wordB (ω.compose D) j * SkewGluing.wordA (ω.compose D) (j + 1) = 0) :
    SkewGluing.wordA ω.E (ω.widthZ + 1) = 0 ∧ SkewGluing.wordB ω.E (ω.period - 1) = 0 := by
  obtain ⟨hG, hF, hsp⟩ := IsLegalNonempty.rotate_data h hD hcc
  have hD' : IsConnectedSkew (SkewGluing.rotate D) := isConnectedSkew_rotate hD
  have hcd : ω.rotate.case = .d := rotate_case_d hcc
  have hE := h.1.1.1
  have hspE := h.1.1.span_eq
  have hwz : ω.rotate.widthZ = ω.widthZ := widthZ_rotate ω
  have hper : ω.rotate.period = ω.period := rfl
  have hwz' : ω.widthZ = (ω.width : ℤ) := rfl
  set G := ω.rotate.compose (SkewGluing.rotate D) with hGdef
  have hsD : (span (SkewGluing.rotate D) : ℤ) = span D := by rw [span_rotate]
  have hAD' : ∃ j : ℤ, 1 ≤ j ∧ j < (span (SkewGluing.rotate D) : ℤ) ∧
      SkewGluing.wordA (SkewGluing.rotate D) j = 1 := by
    obtain ⟨j, h1, h2, h3⟩ := hBD
    refine ⟨(span D : ℤ) - j, by omega, by omega, ?_⟩
    rw [wordA_rotate hD]
    rw [show (span D : ℤ) - ((span D : ℤ) - j) = j by ring]
    exact h3
  have hzG : ∀ m : ℤ, 1 ≤ m → m + 1 < (span G : ℤ) →
      SkewGluing.wordB G m * SkewGluing.wordA G (m + 1) = 0 := by
    intro m h1 h2
    have hNG : (span G : ℤ) = span (ω.compose D) := by rw [hsp]
    have := hz ((span G : ℤ) - m - 1) (by omega) (by omega)
    rw [hF, wordB_rotate hG, wordA_rotate hG] at this
    rw [show (span G : ℤ) - ((span G : ℤ) - m - 1) = m + 1 by ring,
      show (span G : ℤ) - ((span G : ℤ) - m - 1 + 1) = m by ring, mul_comm] at this
    exact this
  have key := PosWidthD.private_bits h.rotate hcd hD' (by rw [hwz, hper]; exact hwq) hAD' hzG
  rw [hwz, hper] at key
  have eE : ω.rotate.E = SkewGluing.rotate ω.E := rfl
  rw [eE] at key
  rw [wordA_rotate hE, wordB_rotate hE] at key
  rw [show (span ω.E : ℤ) - (ω.widthZ + 1) = ω.period - 1 by omega,
    show (span ω.E : ℤ) - (ω.period - 1) = ω.widthZ + 1 by omega] at key
  exact ⟨key.2, key.1⟩

end PosWidthC

end SkewClassInflation
