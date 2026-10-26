/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.InflateBridgePos
import SkewClassInflation.InflateEdgeWidths
import SkewClassInflation.InflateLegal

/-!
# Inflation of legal charts

Formalizes `lem:inflate-chart` in `shields-2026-skew-class-inflation.tex`.
Sorry-free.
-/

namespace SkewClassInflation

open SkewGluing

namespace InflateChart

/-- Translating the inner of an ordinary composite of case (a) translates the composite. -/
theorem compose_translate_a {ω : MarkedInner} (hω : ω.case = .a) (u : ℤ × ℤ) {D : Diagram}
    (hD : D.Nonempty) : (MarkedInner.translate u ω).compose D = translate u (ω.compose D) := by
  have hm : ¬ ω.case.IsMixed := by rw [hω]; decide
  have hm' : ¬ (MarkedInner.translate u ω).case.IsMixed := hm
  ext x
  rw [MarkedInner.compose_of_ordinary hD hm', mem_translate, MarkedInner.compose_of_ordinary hD hm]
  have ho : ∀ d, (MarkedInner.translate u ω).origin D d = ω.origin D d := fun d => by
    simp only [MarkedInner.origin, MarkedInner.translate_case, MarkedInner.translate_v]
  simp only [ho, MarkedInner.translate_E, mem_translate]
  have e : ∀ d : ℤ × ℤ, x - u - ω.origin D d = x - ω.origin D d - u := fun d => by abel
  simp only [e]

theorem lowerCopy_singleton {E : Diagram} (hE : IsConnectedSkew E) (h0 : minContent E = 0) :
    SlotGeom.lowerCopy (inflateCells E) 1 1 (diagHi (inflateCells E)) =
      {sw (inflateCells E)} := by
  have hI := isConnectedSkew_inflateCells hE
  have hmin := minContent_inflateCells hE
  rw [h0] at hmin
  have hs := isConnectedSkew_iff_diagonal.mp hI
  have hne := hs.1
  have hc := hs.contents_eq
  have hsw : sw (inflateCells E) = (diagLo (inflateCells E) 0, diagLo (inflateCells E) 0) := by
    unfold sw; rw [hmin]; ext <;> simp
  have hle : minContent (inflateCells E) ≤ maxContent (inflateCells E) :=
    minContent_le (maxContent_mem hne)
  have hend := hs.2.2.2.2 0 (by rw [hc, Finset.mem_Icc]; omega) (Or.inl (by
    rw [hc, Finset.mem_Icc]; omega))
  ext ⟨i, j⟩
  unfold SlotGeom.lowerCopy
  rw [Finset.mem_filter, Finset.mem_singleton, hsw]
  constructor
  · rintro ⟨hx, h1, h2⟩
    have hk : j - i ∈ contents (inflateCells E) := content_mem_contents hx
    rw [hc, Finset.mem_Icc] at hk
    have l1 := diagLo_le (k := j - i) hx (by ring)
    have l2 := le_diagHi (k := j - i) hx (by ring)
    simp only [content] at h1 h2
    have hk0 : j - i = 0 := by omega
    rw [hk0] at l1 l2
    simp only [show ¬ (1 ≤ j - i) by omega, ite_false] at h2
    have : i = diagLo (inflateCells E) 0 := by omega
    have hj : j = i := by omega
    rw [hj]
    ext <;> simp [this]
  · intro hx
    have hx' := Prod.mk.inj hx
    have hm : (i, j) ∈ inflateCells E := by
      have := sw_mem hne
      rw [hsw] at this
      rw [hx'.1, hx'.2]; exact this
    refine ⟨hm, by simp only [content]; omega, ?_⟩
    have hj0 : j - i = 0 := by omega
    simp only [content, hj0, show ¬ (1 ≤ (0 : ℤ)) by omega, ite_false]
    omega

/-- The singleton end mark of `lem:inflate-chart` at width zero, in any position of `V`.
The inner is `I(V)`, the displacement is the original `v_H`, the mark is the singleton `(a)` at the
southwest cell, and the composite is the cell inflation of the empty-mark composite. -/
theorem width_zero {ω : MarkedInner} {D : Diagram} (h : ω.IsLegalEmpty)
    (hD : IsConnectedSkew D) (hrow : ¬ IsRowDiagram D) (hq2 : 2 ≤ ω.period)
    {n : ℕ} {P : Profile n} {v : ℤ × ℤ}
    (hT : ω.compose D = translate v (profileCells P)) (hz : (Profile.inflate 1 P).ZeroFree) :
    ∃ ω' : MarkedInner, ω'.IsLegal ∧ ω'.E = inflateCells ω.E ∧ ω'.v = ω.v ∧ ω'.case = .a ∧
      ω'.W = {sw (inflateCells ω.E)} ∧ ω'.width = 1 ∧ ω'.period = ω.period ∧
      ω'.compose D = inflateCells (ω.compose D) := by
  have hE := h.1.1.1
  have hEne : ω.E.Nonempty := hE.2.1
  have hca := h.case_a
  have hDne : D.Nonempty := hD.2.1
  set u : ℤ × ℤ := (0, -minContent ω.E) with hu
  have hcu : content u = -minContent ω.E := by simp [hu, content]
  set ω0 := MarkedInner.translate u ω with hω0
  have hleg0 : ω0.IsLegalEmpty := ⟨MarkedInner.isLegal_translate u h.1, by simp [hω0, h.2, SkewGluing.translate]⟩
  have h0 : minContent ω0.E = 0 := by
    change minContent (translate u ω.E) = 0
    rw [minContent_translate hEne, hcu]; ring
  have hper0 : ω0.period = ω.period := MarkedInner.period_translate u ω
  have hcomp0 : ω0.compose D = translate u (ω.compose D) := compose_translate_a hca u hDne
  have hT0 : ω0.compose D = translate (u + v) (profileCells P) := by
    rw [hcomp0, hT, SkewGluing.translate_translate]
  obtain ⟨hleg, hper, hcomp⟩ := width_zero_chart hleg0 hD hrow (by omega) h0 hT0 hz
  set mark0 := SlotGeom.mark (inflateCells ω0.E) (maxContent ω0.E + 1) 1 1
    (diagLo ω0.E (maxContent ω0.E) - diagLo ω0.E 0) (diagHi (inflateCells ω0.E)) with hmark0
  obtain ⟨hE0, hv0, hc0⟩ := singleton_mark_data hleg0.1.1.1 h0
  have hEI : ω.E = translate (-u) ω0.E := by
    change ω.E = translate (-u) (translate u ω.E)
    rw [SkewGluing.translate_translate, neg_add_cancel, SkewGluing.translate_zero]
  have hW0 : mark0.W = {sw (inflateCells ω0.E)} := lowerCopy_singleton hleg0.1.1.1 h0
  have hI0 : IsConnectedSkew (inflateCells ω0.E) := isConnectedSkew_inflateCells hleg0.1.1.1
  have hEI' : inflateCells ω.E = translate (-u) (inflateCells ω0.E) := by
    rw [hEI, inflateCells_translate]
  have hsw : sw (inflateCells ω.E) = sw (inflateCells ω0.E) + (-u) := by
    rw [hEI', sw_translate hI0.2.1]
  refine ⟨MarkedInner.translate (-u) mark0, MarkedInner.isLegal_translate (-u) hleg, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · change translate (-u) mark0.E = _
    rw [hE0, hEI']
  · change mark0.v = ω.v
    rw [hv0, (h.isEmptyMark).2.1]
    exact MarkedInner.vH_translate u ω.E
  · exact hc0
  · change translate (-u) mark0.W = _
    rw [hW0, hsw]
    ext x
    simp [SkewGluing.translate, Finset.mem_image]
  · rw [MarkedInner.width_translate]
    have : mark0.W = {sw (inflateCells ω0.E)} := hW0
    simp [MarkedInner.width, this, span, contents]
  · rw [MarkedInner.period_translate, hper, hper0]
  · rw [compose_translate_a hc0 (-u) hDne, hcomp, hcomp0, ← inflateCells_translate,
      SkewGluing.translate_translate, neg_add_cancel, SkewGluing.translate_zero]

/-! ### Width `q - 1`: zero-freeness forces the atom -/

section Wq1

variable {ω : MarkedInner} {D : Diagram}

/-- Rotation reduces case (c) to case (d), keeping the outer ones and the zero-free words. -/
theorem rotate_zeroFree (h : ω.IsLegalNonempty) (hcc : ω.case = .c) (hD : IsConnectedSkew D)
    (hBD : ∃ j : ℤ, 1 ≤ j ∧ j < (span D : ℤ) ∧ SkewGluing.wordB D j = 1)
    (hz : ∀ j : ℤ, 1 ≤ j → j + 1 < (span (ω.compose D) : ℤ) →
      SkewGluing.wordB (ω.compose D) j * SkewGluing.wordA (ω.compose D) (j + 1) = 0) :
    ω.rotate.case = .d ∧ IsConnectedSkew (SkewGluing.rotate D) ∧
      (∃ j : ℤ, 1 ≤ j ∧ j < (span (SkewGluing.rotate D) : ℤ) ∧
        SkewGluing.wordA (SkewGluing.rotate D) j = 1) ∧
      (∀ j : ℤ, 1 ≤ j → j + 1 < (span (ω.rotate.compose (SkewGluing.rotate D)) : ℤ) →
        SkewGluing.wordB (ω.rotate.compose (SkewGluing.rotate D)) j *
          SkewGluing.wordA (ω.rotate.compose (SkewGluing.rotate D)) (j + 1) = 0) := by
  obtain ⟨hG, hF, hsp⟩ := MarkedInner.IsLegalNonempty.rotate_data h hD hcc
  have hD' : IsConnectedSkew (SkewGluing.rotate D) := isConnectedSkew_rotate hD
  have hsD : (span (SkewGluing.rotate D) : ℤ) = span D := by rw [span_rotate]
  refine ⟨MarkedInner.rotate_case_d hcc, hD', ?_, ?_⟩
  · obtain ⟨j, h1, h2, h3⟩ := hBD
    refine ⟨(span D : ℤ) - j, by omega, by omega, ?_⟩
    rw [wordA_rotate hD, show (span D : ℤ) - ((span D : ℤ) - j) = j by ring]
    exact h3
  · intro m h1 h2
    have := hz ((span (ω.rotate.compose (SkewGluing.rotate D)) : ℤ) - m - 1) (by omega) (by
      rw [hsp]; omega)
    rw [hF, wordB_rotate hG, wordA_rotate hG] at this
    rw [show (span (ω.rotate.compose (SkewGluing.rotate D)) : ℤ) -
        ((span (ω.rotate.compose (SkewGluing.rotate D)) : ℤ) - m - 1) = m + 1 by ring,
      show (span (ω.rotate.compose (SkewGluing.rotate D)) : ℤ) -
        ((span (ω.rotate.compose (SkewGluing.rotate D)) : ℤ) - m - 1 + 1) = m by ring,
      mul_comm] at this
    exact this

/-- Case (a) residue zero with `t ≠ 0`, also on the last block `J = M + 1`. -/
theorem resA_one_last (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D) (hca : ω.case = .a)
    {s t : ℤ} (hph : ω.IsPhases s t) (ht0 : t ≠ 0) {J : ℤ} (hJ1 : minContent D + 1 ≤ J)
    (hJ2 : J ≤ maxContent D + 1) :
    SkewGluing.wordA (ω.compose D) ((J - minContent D) * ω.period) = 1 := by
  have hmix : ¬ ω.case.IsMixed := by simp [AttachCase.IsMixed, hca]
  have hz := PosWidthA.hex_a hca
  have hc := MarkedInner.ord_classRows h hD hmix
  have hmin := h.minContent_compose' hD
  have hq := h.width_lt_period
  have hw := h.width_pos
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph
  have hv : ValidClass (minContent D) (maxContent D) ω.widthZ J 0 := by
    by_cases hJ : J ≤ maxContent D
    · exact Or.inl ⟨by omega, hJ⟩
    · exact Or.inr ⟨by omega, by omega⟩
  have := hc.wordA_class' hmin (J := J) (a := 0) (k := (J - minContent D) * ω.period)
    (by ring) le_rfl (by omega) hv (fun _ => hJ1)
  rw [this, MarkedInner.ord_classBitLo h hD hmix hph le_rfl (by omega) hv (fun _ => hJ1)
    ⟨fun _ => fun hh => ht0 hh.symm, fun h1 => by omega⟩]
  simp

/-- At width `q - 1`, a legal nonempty mark whose composite with a connected outer having a one in
each word is zero-free is of case (a) with the phases `s = w` and `t = 0`. -/
theorem wq1_case (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D)
    (hwq : ω.widthZ + 1 = ω.period)
    (hAD : ∃ j : ℤ, 1 ≤ j ∧ j < (span D : ℤ) ∧ SkewGluing.wordA D j = 1)
    (hBD : ∃ j : ℤ, 1 ≤ j ∧ j < (span D : ℤ) ∧ SkewGluing.wordB D j = 1)
    (hz : ∀ j : ℤ, 1 ≤ j → j + 1 < (span (ω.compose D) : ℤ) →
      SkewGluing.wordB (ω.compose D) j * SkewGluing.wordA (ω.compose D) (j + 1) = 0) :
    ω.case = .a ∧ ∀ s t : ℤ, ω.IsPhases s t → s = ω.widthZ ∧ t = 0 := by
  have hw := h.width_pos
  have hsF := h.span_compose_eq hD
  have hsp := span_eq_of_isConnectedSkew hD
  obtain ⟨jA, hjA1, hjA2, hjA3⟩ := hAD
  obtain ⟨jB, hjB1, hjB2, hjB3⟩ := hBD
  have hmM : minContent D + 1 ≤ maxContent D := by omega
  obtain ⟨s0, t0, hph0⟩ := h.exists_phases
  -- case (d) cannot occur
  have dcase : ∀ ω' : MarkedInner, ∀ D' : Diagram, ω'.IsLegalNonempty → ω'.case = .d →
      IsConnectedSkew D' → ω'.widthZ + 1 = ω'.period →
      (∃ j : ℤ, 1 ≤ j ∧ j < (span D' : ℤ) ∧ SkewGluing.wordA D' j = 1) →
      (∀ j : ℤ, 1 ≤ j → j + 1 < (span (ω'.compose D') : ℤ) →
        SkewGluing.wordB (ω'.compose D') j * SkewGluing.wordA (ω'.compose D') (j + 1) = 0) →
      False := by
    intro ω' D' h' hcd hD' hwq' hAD' hz'
    obtain ⟨s, t, hph⟩ := h'.exists_phases
    obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph
    have hw' := h'.width_pos
    have hsF' := h'.span_compose_eq hD'
    have hsp' := span_eq_of_isConnectedSkew hD'
    obtain ⟨jA', hjA1', hjA2', hjA3'⟩ := hAD'
    have b1 := PosWidthD.blockB_w h' hD' hcd hph (J := minContent D') le_rfl (by omega)
    by_cases ht0 : t = 0
    · have iface := (MarkedInner.IsLegalNonempty.interface_d h' hD' hcd hph (j := jA') hjA1'
        hjA2').1
      rw [ht0, add_zero, hjA3'] at iface
      have b2 := PosWidthD.blockB_w h' hD' hcd hph (J := minContent D' + jA' - 1) (by omega)
        (by omega)
      have e : (minContent D' + jA' - 1 - minContent D') * ω'.period + ω'.widthZ =
          jA' * ω'.period - 1 := by rw [← hwq']; ring
      rw [e] at b2
      have := hz' (jA' * ω'.period - 1) (by nlinarith) (by rw [hsF']; nlinarith)
      rw [b2, show jA' * ω'.period - 1 + 1 = jA' * ω'.period by ring, iface] at this
      norm_num at this
    · have r1 := PosWidthD.resA_one h' hD' hcd hph (by omega) (J := minContent D' + 1)
        (by omega) (by omega)
      have := hz' ((minContent D' - minContent D') * ω'.period + ω'.widthZ) (by simp; omega) (by
        rw [hsF']; simp; nlinarith)
      rw [b1, show (minContent D' - minContent D') * ω'.period + ω'.widthZ + 1 =
        (minContent D' + 1 - minContent D') * ω'.period by rw [← hwq']; ring, r1] at this
      norm_num at this
  have hcase : ω.case = .a := by
    by_contra hna
    have hc4 : ω.case = .b ∨ ω.case = .c ∨ ω.case = .d := by
      cases hc : ω.case <;> simp_all
    rcases hc4 with hcb | hcc | hcd
    · obtain ⟨s, t, hph⟩ := h.exists_phases
      obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph
      have hB1 := PosWidthB.wordB_w_one h hcb
      have b1 := PosWidthB.blockB h hD hcb hph (J := minContent D) le_rfl (by omega)
        (a := ω.widthZ) (by omega) (by omega) (by omega)
      have r1 := PosWidthB.resA_one h hD hcb hph (J := minContent D + 1) (by omega) (by omega)
      have := hz ((minContent D - minContent D) * ω.period + ω.widthZ) (by simp; omega) (by
        rw [hsF]; simp; nlinarith)
      rw [b1, hB1, show (minContent D - minContent D) * ω.period + ω.widthZ + 1 =
        (minContent D + 1 - minContent D) * ω.period by rw [← hwq]; ring, r1] at this
      norm_num at this
    · obtain ⟨hcd, hD', hAD', hzG⟩ := rotate_zeroFree h hcc hD ⟨jB, hjB1, hjB2, hjB3⟩ hz
      exact dcase ω.rotate _ h.rotate hcd hD' (by
        rw [MarkedInner.widthZ_rotate]; exact hwq) hAD' hzG
    · exact dcase ω D h hcd hD hwq ⟨jA, hjA1, hjA2, hjA3⟩ hz
  refine ⟨hcase, fun s t hph => ?_⟩
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph
  have hmix : ¬ ω.case.IsMixed := by simp [AttachCase.IsMixed, hcase]
  have hordT := PosWidthA.hex_a hcase
  -- t = 0
  have hsw : s = ω.widthZ := by
    by_contra hne
    have hlt : s < ω.widthZ := by omega
    have hB1 := PosWidthA.wordB_w_one h hcase hph hlt
    have b1 := PosWidthA.blockB h hD hcase hph (J := minContent D) le_rfl (by omega)
      (a := ω.widthZ) (by omega) (by omega) (by omega)
    by_cases ht0 : t = 0
    · have r1 := PosWidthA.resA_zero h hD hcase hph ht0 (J := minContent D + jA) (by omega)
        (by omega)
      have b2 := PosWidthA.blockB h hD hcase hph (J := minContent D + jA - 1) (by omega)
        (by omega) (a := ω.widthZ) (by omega) (by omega) (by omega)
      have e : (minContent D + jA - 1 - minContent D) * ω.period + ω.widthZ =
          (minContent D + jA - minContent D) * ω.period - 1 := by
        have : ω.period = ω.widthZ + 1 := by omega
        rw [this]; ring
      rw [e] at b2
      have := hz ((minContent D + jA - minContent D) * ω.period - 1) (by nlinarith) (by
        rw [hsF]; nlinarith)
      have hA1 : bitA D (minContent D + jA) = 1 := hjA3
      rw [b2, hB1, show (minContent D + jA - minContent D) * ω.period - 1 + 1 =
        (minContent D + jA - minContent D) * ω.period by ring, r1, hA1] at this
      norm_num at this
    · have r1 := resA_one_last h hD hcase hph ht0 (J := minContent D + 1) (by omega) (by omega)
      have := hz ((minContent D - minContent D) * ω.period + ω.widthZ) (by simp; omega) (by
        rw [hsF]; simp; nlinarith)
      rw [b1, hB1, show (minContent D - minContent D) * ω.period + ω.widthZ + 1 =
        (minContent D + 1 - minContent D) * ω.period by rw [← hwq]; ring, r1] at this
      norm_num at this
  refine ⟨hsw, ?_⟩
  by_contra ht0
  have s1 := PosWidthA.slotB h hD hcase hph (J := minContent D + jB) (by omega) (by omega)
  have r1 := resA_one_last h hD hcase hph ht0 (J := minContent D + jB + 1) (by omega) (by omega)
  have hpos : 0 ≤ SkewGluing.wordB ω.E s := by
    have hbin := h.1.1.1
    have hs := isConnectedSkew_iff_diagonal.mp hbin
    have hc := hs.contents_eq
    have hspan := h.1.1.span_eq
    have hspan' := span_eq_of_isConnectedSkew hbin
    have hwz : ω.widthZ = (ω.width : ℤ) := rfl
    have := (hs.2.2.2.1 (minContent ω.E + s) (by rw [hc, Finset.mem_Icc]; omega)
      (by rw [hc, Finset.mem_Icc]; omega)).2
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    unfold SkewGluing.wordB
    omega
  have hbD : bitB D (minContent D + jB) = 1 := hjB3
  have := hz ((minContent D + jB - minContent D) * ω.period + s) (by nlinarith) (by
    rw [hsF]; nlinarith)
  rw [s1, show (minContent D + jB - minContent D) * ω.period + s + 1 =
    (minContent D + jB + 1 - minContent D) * ω.period by rw [← hwq, hsw]; ring, r1, hbD] at this
  omega

end Wq1

/-! ### Width `q - 1`: the mark is the atom -/

section Atom

variable {ω : MarkedInner}

theorem diag_unique (h : ω.IsLegalNonempty) {z z' : ℤ × ℤ} (hz : z ∈ ω.E) (hz' : z' ∈ ω.E)
    (c : ℤ) (hc : content z = c) (hc' : content z' = c) (hs : ω.lo (c - minContent ω.E) =
      ω.hi (c - minContent ω.E)) : z = z' := by
  obtain ⟨i, j⟩ := z
  obtain ⟨i', j'⟩ := z'
  have e1 := diagLo_le (k := c) hz (by simpa [content] using hc)
  have e2 := le_diagHi (k := c) hz (by simpa [content] using hc)
  have e3 := diagLo_le (k := c) hz' (by simpa [content] using hc')
  have e4 := le_diagHi (k := c) hz' (by simpa [content] using hc')
  unfold MarkedInner.lo MarkedInner.hi at hs
  rw [show minContent ω.E + (c - minContent ω.E) = c by ring] at hs
  simp only [content] at hc hc'
  have : i = i' := by omega
  subst this
  have : j = j' := by omega
  rw [this]

/-- A legal nonempty mark of width `q - 1`, case (a), phases `(w, 0)`, is the atom of its lower
copy. -/
theorem eq_atomMark (h : ω.IsLegalNonempty) (hca : ω.case = .a) (hwq : ω.widthZ + 1 = ω.period)
    {s t : ℤ} (hph : ω.IsPhases s t) (hs : s = ω.widthZ) (ht : t = 0) :
    ω = atomMark ω.W := by
  have hn := h.nonemptyMark
  obtain ⟨hWne, hWc, hWE, hUE, hsw, hneU, -⟩ := hn
  have hEc := h.isConnectedSkew_E
  have hEne : ω.E.Nonempty := hEc.2.1
  have hmW := h.minContent_W
  have hw := h.width_pos
  have hWd := isConnectedSkew_iff_diagonal.mp hWc
  have hWsp := span_eq_of_isConnectedSkew hWc
  have hwidth : (span ω.W : ℤ) = ω.widthZ := rfl
  have hWcont : contents ω.W = Finset.Icc (minContent ω.E) (minContent ω.E + ω.widthZ - 1) := by
    rw [hWd.contents_eq, hmW]
    have : maxContent ω.W = minContent ω.E + ω.widthZ - 1 := by omega
    rw [this]
  have hmaxW : maxContent ω.W = minContent ω.E + ω.widthZ - 1 := by omega
  obtain ⟨hl, hu⟩ := h.attach.1 hca
  obtain ⟨x, hxm, hxc, hxW⟩ := hl
  obtain ⟨y, hym, hyc, hyU⟩ := hu
  have hmid := h.contents_middle hph
  rw [hs, ht] at hmid
  have hxc' : content x = minContent ω.E + ω.widthZ := by
    have := content_mem_contents hxm
    rw [hmid, Finset.mem_Icc] at this; omega
  have hyc' : content y = minContent ω.E + ω.widthZ := by
    have := content_mem_contents hym
    rw [hmid, Finset.mem_Icc] at this; omega
  have hxE : x ∈ ω.E := (Finset.mem_sdiff.mp hxm).1
  have hyE : y ∈ ω.E := (Finset.mem_sdiff.mp hym).1
  have hsing : ω.lo (minContent ω.E + ω.widthZ - minContent ω.E) =
      ω.hi (minContent ω.E + ω.widthZ - minContent ω.E) := by
    rw [show minContent ω.E + ω.widthZ - minContent ω.E = ω.widthZ by ring]
    exact h.lo_w_eq_hi_w
  have hxy : x = y := diag_unique h hxE hyE _ hxc' hyc' hsing
  -- ne W and sw W
  have hneW : (x.1, x.2 - 1) = ne ω.W := by
    have hne' : ne ω.W ∈ ω.W := ne_mem hWne
    have hcne : content (ne ω.W) = maxContent ω.W := content_ne hWne
    have hend := hWd.2.2.2.2 (maxContent ω.W) (maxContent_mem hWne) (Or.inr (by
      rw [hWd.contents_eq, Finset.mem_Icc]; omega))
    have e1 := diagLo_le (k := maxContent ω.W) hxW (by simp only [content] at hxc'; omega)
    have e2 := le_diagHi (k := maxContent ω.W) hxW (by simp only [content] at hxc'; omega)
    generalize ne ω.W = nn at *
    obtain ⟨a, b⟩ := nn
    have e3 := diagLo_le (k := maxContent ω.W) hne' (by simpa [content] using hcne)
    have e4 := le_diagHi (k := maxContent ω.W) hne' (by simpa [content] using hcne)
    simp only [content] at hcne hxc'
    ext <;> simp only <;> omega
  have hswW : (y.1, y.2 + 1) - ω.v = sw ω.W := by
    have hmem : (y.1, y.2 + 1) - ω.v ∈ ω.W := by
      have := hyU
      unfold MarkedInner.upper at this
      exact mem_translate.mp this
    have hcv : content ω.v = ω.period := rfl
    have hc1 : content ((y.1, y.2 + 1) - ω.v) = minContent ω.W := by
      rw [MarkedInner.content_sub, hcv, hmW]
      simp only [content] at hyc' ⊢
      omega
    have hsw' : sw ω.W ∈ ω.W := sw_mem hWne
    have hend := hWd.2.2.2.2 (minContent ω.W) (minContent_mem hWne) (Or.inl (by
      rw [hWd.contents_eq, Finset.mem_Icc]; omega))
    have hcs : content (sw ω.W) = minContent ω.W := content_sw hWne
    generalize (y.1, y.2 + 1) - ω.v = pp at *
    generalize sw ω.W = ss at *
    obtain ⟨a, b⟩ := pp
    obtain ⟨a', b'⟩ := ss
    have e1 := diagLo_le (k := minContent ω.W) hmem (by simpa [content] using hc1)
    have e2 := le_diagHi (k := minContent ω.W) hmem (by simpa [content] using hc1)
    have e3 := diagLo_le (k := minContent ω.W) hsw' (by simpa [content] using hcs)
    have e4 := le_diagHi (k := minContent ω.W) hsw' (by simpa [content] using hcs)
    simp only [content] at hc1 hcs
    ext <;> simp only <;> omega
  have hv : ω.v = atomDisp ω.W := by
    have h1 : ω.v = (y.1, y.2 + 1) - sw ω.W := by rw [← hswW]; abel
    have h2 : y = x := hxy.symm
    rw [h1, h2]
    unfold atomDisp
    have : (x.1, x.2 + 1) = (x.1, x.2 - 1) + (0, 2) := by ext <;> simp <;> ring
    rw [this, hneW]
    ext <;> simp <;> ring
  have hxne : x = ne ω.W + (0, 1) := by
    rw [← hneW]; ext <;> simp
  have hE : ω.E = atomInner ω.W := by
    unfold atomInner
    ext z
    simp only [Finset.mem_union, Finset.mem_singleton]
    constructor
    · intro hz
      by_cases h1 : z ∈ ω.W
      · exact Or.inl (Or.inl h1)
      by_cases h2 : z ∈ ω.upper
      · refine Or.inr ?_
        rw [← hv]; exact h2
      · refine Or.inl (Or.inr ?_)
        have hzm : z ∈ ω.middle := Finset.mem_sdiff.mpr ⟨hz, by simp [h1, h2]⟩
        have hzc : content z = minContent ω.E + ω.widthZ := by
          have := content_mem_contents hzm
          rw [hmid, Finset.mem_Icc] at this; omega
        rw [← hxne]
        exact diag_unique h hz hxE _ hzc hxc' hsing
    · rintro ((hz | hz) | hz)
      · exact hWE hz
      · rw [hz, ← hxne]; exact hxE
      · apply hUE
        unfold MarkedInner.upper
        rw [hv]; exact hz
  cases ω
  simp only [atomMark, MarkedInner.mk.injEq] at *
  refine ⟨hE, trivial, hv, hca⟩

end Atom

theorem width_pos_of_ne_empty {ω : MarkedInner} (hω : ω.IsLegal) (hW : ω.W.Nonempty) :
    ω.IsLegalNonempty := ⟨hω, hW⟩

theorem W_empty_of_width_zero {ω : MarkedInner} (hω : ω.IsLegal) (h0 : ω.widthZ = 0) :
    ω.W = ∅ := by
  by_contra hne
  have := MarkedInner.IsLegalNonempty.width_pos (ω := ω)
    ⟨hω, Finset.nonempty_iff_ne_empty.mpr hne⟩
  omega

theorem period_ge_two {ω : MarkedInner} (h : ω.IsLegalEmpty) (hE2 : 2 ≤ ω.E.card) :
    2 ≤ ω.period := by
  have hq := h.period_pos
  by_contra hlt
  have hq1 : ω.period = 1 := by omega
  have hsp := h.span_eq
  have hE := h.1.1.1
  have hs := isConnectedSkew_iff_diagonal.mp hE
  have hsp' := span_eq_of_isConnectedSkew hE
  have hc := hs.contents_eq
  have hmM : maxContent ω.E = minContent ω.E := by omega
  have hend := hs.2.2.2.2 (minContent ω.E) (minContent_mem hs.1) (Or.inl (by
    rw [hc, Finset.mem_Icc]; omega))
  have : ω.E.card ≤ 1 := by
    rw [Finset.card_le_one]
    rintro ⟨i, j⟩ hz ⟨i', j'⟩ hz'
    have k1 : j - i = minContent ω.E := by
      have := content_mem_contents hz
      rw [hc, Finset.mem_Icc] at this; simp only [content] at this; omega
    have k2 : j' - i' = minContent ω.E := by
      have := content_mem_contents hz'
      rw [hc, Finset.mem_Icc] at this; simp only [content] at this; omega
    have e1 := diagLo_le (k := minContent ω.E) hz k1
    have e2 := le_diagHi (k := minContent ω.E) hz k1
    have e3 := diagLo_le (k := minContent ω.E) hz' k2
    have e4 := le_diagHi (k := minContent ω.E) hz' k2
    have : i = i' := by omega
    subst this
    have : j = j' := by omega
    rw [this]
  omega

theorem B_E_w_zero {ω : MarkedInner} (h : ω.IsLegalNonempty) (hca : ω.case = .a) {s t : ℤ}
    (hph : ω.IsPhases s t) (hs : s = ω.widthZ) :
    SkewGluing.wordB ω.E ω.widthZ = 0 := by
  have hmix : ¬ ω.case.IsMixed := by simp [AttachCase.IsMixed, hca]
  have hz := PosWidthA.hex_a hca
  have hw := h.width_pos
  have hcaps := (MarkedInner.ord_E_facts h hmix).2.1 hz
  have o := (MarkedInner.ord_offsets h hmix hph (b := ω.widthZ - 1) (by omega) le_rfl).1 hz
  unfold MarkedInner.dLo MarkedInner.dHi at o hcaps
  have o2 := o.2.2.2 (by omega)
  have hc1 := hcaps.1.2.2
  unfold SkewGluing.wordB bitB
  unfold MarkedInner.hi at hc1 o2
  have e : minContent ω.E + ω.widthZ - 1 = minContent ω.E + (ω.widthZ - 1) := by ring
  rw [e]
  omega

/-- At width `q - 1`, zero-freeness of `I(T)` makes the inflated outer zero-free. -/
theorem outer_zeroFree {ω : MarkedInner} {D : Diagram} (h : ω.IsLegalNonempty)
    (hD : IsConnectedSkew D) (hca : ω.case = .a) (hwq : ω.widthZ + 1 = ω.period) {s t : ℤ}
    (hph : ω.IsPhases s t) (hs : s = ω.widthZ) (ht : t = 0)
    (hz : ∀ j : ℤ, 1 ≤ j → j + 1 < (span (ω.compose D) : ℤ) →
      SkewGluing.wordB (ω.compose D) j * SkewGluing.wordA (ω.compose D) (j + 1) = 0)
    {m : ℕ} {Q : Profile m} {u : ℤ × ℤ} (hDQ : D = translate u (profileCells Q)) :
    (Profile.inflate 1 Q).ZeroFree := by
  rw [zeroFree_inflate_one_iff_words Q hDQ]
  intro j hj1 hj2
  have hsF := h.span_compose_eq hD
  have hsp := span_eq_of_isConnectedSkew hD
  have hw := h.width_pos
  have bE := B_E_w_zero h hca hph hs
  have s1 := PosWidthA.slotB h hD hca hph (J := minContent D + j) (by omega) (by omega)
  have r1 := PosWidthA.resA_zero h hD hca hph ht (J := minContent D + j + 1) (by omega)
    (by omega)
  rw [hs] at s1
  have := hz ((minContent D + j - minContent D) * ω.period + ω.widthZ) (by nlinarith) (by
    rw [hsF]; nlinarith)
  rw [s1, bE, show (minContent D + j - minContent D) * ω.period + ω.widthZ + 1 =
    (minContent D + j + 1 - minContent D) * ω.period by rw [← hwq]; ring, r1, zero_add] at this
  unfold SkewGluing.wordA SkewGluing.wordB
  rw [add_assoc] at this
  exact this

theorem pinches {ω : MarkedInner}
    (hA : SkewGluing.wordA ω.E (ω.widthZ + 1) = 0) (hB : SkewGluing.wordB ω.E (ω.period - 1) = 0) :
    ω.lo (ω.widthZ + 1) = ω.lo ω.widthZ ∧ ω.hi (ω.period - 2) = ω.hi (ω.period - 1) := by
  unfold SkewGluing.wordA SkewGluing.wordB bitA bitB at *
  unfold MarkedInner.lo MarkedInner.hi
  have e1 : minContent ω.E + (ω.widthZ + 1) - 1 = minContent ω.E + ω.widthZ := by ring
  have e2 : minContent ω.E + (ω.period - 1) - 1 = minContent ω.E + (ω.period - 2) := by ring
  rw [e1] at hA
  rw [e2] at hB
  constructor <;> omega

/-- **Inflation of legal charts** (`lem:inflate-chart`).  Let `T = C ∘_μ V` be a proper legal
chart, `C` not a row, and `T` a translate of the cell diagram of `P` with `I(T)` zero-free.  Then
`I(T)` has a legal chart of period `q`, in the three alternatives of the lemma:

1. for `0 < w < q - 1` the inner `I(V)` with the mark `I(W)`, the same displacement and attachment;
2. for `w = 0` the inner `I(V)` with its singleton end mark `(a)` at `sw(I(V))` and the same
   displacement, whatever the position of `V`;
3. for `w = q - 1` the original inner is the atom `𝒜(W)` of its lower copy, `I(T)` is
   `I(C) ∘_∅ I(W)` with `I(W)` a legal empty-mark inner of period `q`, and `I(C)` is zero-free. -/
theorem inflate_chart {ω : MarkedInner} {D : Diagram} (hω : ω.IsLegal)
    (hD : IsConnectedSkew D) (hrow : ¬ IsRowDiagram D) (hE2 : 2 ≤ ω.E.card)
    {n : ℕ} {P : Profile n} {v : ℤ × ℤ}
    (hT : ω.compose D = translate v (profileCells P)) (hz : (Profile.inflate 1 P).ZeroFree) :
    (0 < ω.widthZ → ω.widthZ + 1 < ω.period →
      (inflateMarked ω).IsLegal ∧ (inflateMarked ω).period = ω.period ∧
        (inflateMarked ω).widthZ = ω.widthZ + 1 ∧ (inflateMarked ω).case = ω.case ∧
        (inflateMarked ω).E = inflateCells ω.E ∧ (inflateMarked ω).W = inflateCells ω.W ∧
        (inflateMarked ω).v = ω.v ∧
        (inflateMarked ω).compose D = inflateCells (ω.compose D)) ∧
    (ω.widthZ = 0 →
      ∃ ω' : MarkedInner, ω'.IsLegal ∧ ω'.E = inflateCells ω.E ∧ ω'.v = ω.v ∧ ω'.case = .a ∧
        ω'.W = {sw (inflateCells ω.E)} ∧ ω'.width = 1 ∧ ω'.period = ω.period ∧
        ω'.compose D = inflateCells (ω.compose D)) ∧
    (0 < ω.widthZ → ω.widthZ + 1 = ω.period →
      ∃ W : Diagram, IsConnectedSkew W ∧ ω = atomMark W ∧ (emptyMarkH (inflateCells W)).IsLegal ∧
        (emptyMarkH (inflateCells W)).period = ω.period ∧
        inflateCells (ω.compose D) = (emptyMarkH (inflateCells W)).compose (inflateCells D) ∧
        ∀ (m : ℕ) (Q : Profile m) (u : ℤ × ℤ), D = translate u (profileCells Q) →
          (Profile.inflate 1 Q).ZeroFree) := by
  have hDne : D.Nonempty := hD.2.1
  have hAD := exists_wordA_one hD hrow
  have hBD := exists_wordB_one hD hrow
  refine ⟨fun hw hwq => ?_, fun hw0 => ?_, fun hw hwq => ?_⟩
  · have hWne : ω.W.Nonempty := by
      by_contra hne
      have : ω.W = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      have : ω.widthZ = 0 := by
        unfold MarkedInner.widthZ MarkedInner.width; simp [this, span, contents]
      omega
    have h : ω.IsLegalNonempty := ⟨hω, hWne⟩
    have hzw := (zeroFree_inflate_one_iff_words P hT).mp hz
    obtain ⟨s, t, hph⟩ := h.exists_phases
    have hpb : SkewGluing.wordA ω.E (ω.widthZ + 1) = 0 ∧
        SkewGluing.wordB ω.E (ω.period - 1) = 0 := by
      cases hc : ω.case
      · exact PosWidthA.private_bits h hc hD hwq hAD hBD hzw
      · exact PosWidthB.private_bits h hc hD hwq hAD hzw
      · exact PosWidthC.private_bits h hc hD hwq hBD hzw
      · exact PosWidthD.private_bits h hc hD hwq hAD hzw
    obtain ⟨p1, p2⟩ := pinches hpb.1 hpb.2
    obtain ⟨k1, -, k3, k4, k5⟩ := inflate_mark_isLegal h hph hwq p1 p2
    exact ⟨k1.1, k4, k3, k5, rfl, rfl, rfl, compose_inflateMarked ω D hDne⟩
  · have hW := W_empty_of_width_zero hω hw0
    have hle : ω.IsLegalEmpty := ⟨hω, hW⟩
    have hq2 := period_ge_two hle hE2
    exact width_zero hle hD hrow hq2 hT hz
  · have hWne : ω.W.Nonempty := by
      by_contra hne
      have : ω.W = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      have : ω.widthZ = 0 := by
        unfold MarkedInner.widthZ MarkedInner.width; simp [this, span, contents]
      omega
    have h : ω.IsLegalNonempty := ⟨hω, hWne⟩
    have hzw := (zeroFree_inflate_one_iff_words P hT).mp hz
    obtain ⟨hca, hst⟩ := wq1_case h hD hwq hAD hBD hzw
    obtain ⟨s, t, hph⟩ := h.exists_phases
    obtain ⟨hs, ht⟩ := hst s t hph
    have heq := eq_atomMark h hca hwq hph hs ht
    have hWc := h.nonemptyMark.2.1
    refine ⟨ω.W, hWc, heq, ?_⟩
    have hI := isConnectedSkew_inflateCells hWc
    obtain ⟨l1, l2, l3⟩ := atom_empty_mark_isLegal hWc
    refine ⟨l1, ?_, ?_, fun m Q u hDQ => outer_zeroFree h hD hca hwq hph hs ht hzw hDQ⟩
    · rw [l3, ← hwq]; rfl
    · have := atom_compose_inflate hWc hDne
      rw [← heq] at this
      exact this

end InflateChart

end SkewClassInflation
