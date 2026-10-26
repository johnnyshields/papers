/- TODO-COPIED: adapted from
`skew-factor-gluing/lean/SkewGluing/MarkTransfer.lean`. -/
import GluingCore.Coding
import GluingCore.MarkLocality
import GluingCore.CellSchur

/-!
# Transfer of legal marks between composites with a fixed mixed inner

Formalizes `shields-2026-skew-factor-gluing.tex`, «Diagonal geometry» (`cor:gluing-mark-transfer`,
with `lem:gluing-mark-locality`, `lem:gluing-local` (3) and `lem:gluing-coding`).

For a legal mixed mark `ω` of period `q` and connected outers `V`, `V'` of equal span, the
southwest-normalized composites `V ∘_ω E` and `V' ∘_ω E` agree on their first and last `q`
diagonals (`normalize_compose_first`, `normalize_compose_last`), up to the translation `(r - 1) v`
that does not depend on the outer.

* `MarkedInner.IsLegalNonempty.mark_transfer`: for every `0 ≤ u ≤ q`, the two composites carry the
  same legal marks of width `u` (same `W₋`, displacement, attachment case), and neither carries one
  at `u = q`; for `u = 0` this is the equality of the two displacements `v_H`
  (`ne_normalize_compose`, `legal_width_zero_iff`), for `1 ≤ u < q` it is
  `lem:gluing-mark-locality` (`legal_transfer_mid`, `hatMark_transfer`), and the case `u = q` is
  `no_mark_of_width_period` (`no_mark_of_width_period_d`, and case (c) by rotation);
* `MarkedInner.IsLegalNonempty.mark_transfer_of_cellSchur_eq`: the same for Schur-equal connected
  outers, which have equal span;
* the sharpness examples at `u = q + 1` (`(3) ∘ (2, 1)` carries a legal mark of width three,
  `(2, 2) ∘ (2, 1)` none), checked by `decide`.

Sorry-free.
-/

namespace GluingCore

namespace MarkedInner

variable {ω : MarkedInner} {D : Diagram}

theorem IsLegalNonempty.sw_compose_mixed (h : ω.IsLegalNonempty) (hmix : ω.case.IsMixed)
    (hD : IsConnectedSkew D) : sw (ω.compose D) = sw ω.E + minContent D • ω.v := by
  have hq := h.1.period_pos
  have hDne := hD.2.1
  have hEne : ω.E.Nonempty := h.isConnectedSkew_E.2.1
  have hF := h.1.isConnectedSkew_compose hD
  have hFne := hF.2.1
  have hmin := h.1.minContent_compose hD
  have hmem := sw_mem hFne
  have hc : content (sw (ω.compose D)) = minContent ω.E + minContent D * ω.period := by
    rw [content_sw hFne, hmin]
  have hwin := h.1.compose_first_window hD
  have hmem' : sw (ω.compose D) ∈ (ω.compose D).filter
      (fun x => content x ≤ minContent ω.E + minContent D * ω.period + ω.period - 1) := by
    rw [Finset.mem_filter]
    exact ⟨hmem, by omega⟩
  rw [hwin, mem_translate, (origin_ends_mixed hmix hD).1, Finset.mem_filter] at hmem'
  have hc2 : content (sw (ω.compose D) - minContent D • ω.v) = minContent ω.E := by
    rw [content_sub, content_smul, hc]
    have : content ω.v = ω.period := rfl
    rw [this]
    ring
  have := eq_sw_of_content h.isConnectedSkew_E hmem'.1 (by rw [hc2])
  rw [← this]
  abel

/-- The first `q` diagonals of the southwest-normalized composite are those of the normalized
inner. -/
theorem IsLegalNonempty.normalize_compose_first (h : ω.IsLegalNonempty) (hmix : ω.case.IsMixed)
    (hD : IsConnectedSkew D) {x : ℤ × ℤ} (hx : content x ≤ ω.period - 1) :
    x ∈ normalize (ω.compose D) ↔ x ∈ normalize ω.E := by
  have hq := h.1.period_pos
  have hDne := hD.2.1
  have hEne : ω.E.Nonempty := h.isConnectedSkew_E.2.1
  have hF := h.1.isConnectedSkew_compose hD
  have hmin := h.1.minContent_compose hD
  have hsw := h.sw_compose_mixed hmix hD
  have hwin := h.1.compose_first_window hD
  rw [mem_normalize, mem_normalize]
  have hcx : content (x + sw (ω.compose D)) ≤
      minContent ω.E + minContent D * ω.period + ω.period - 1 := by
    rw [content_add, content_sw hF.2.1, hmin]
    omega
  have e : x + sw (ω.compose D) - minContent D • ω.v = x + sw ω.E := by
    rw [hsw]; abel
  constructor
  · intro hmem
    have hmem' : x + sw (ω.compose D) ∈ (ω.compose D).filter
        (fun x => content x ≤ minContent ω.E + minContent D * ω.period + ω.period - 1) :=
      Finset.mem_filter.mpr ⟨hmem, hcx⟩
    rw [hwin, mem_translate, (origin_ends_mixed hmix hD).1, e, Finset.mem_filter] at hmem'
    exact hmem'.1
  · intro hmem
    have hc3 : content (x + sw ω.E) ≤ minContent ω.E + ω.period - 1 := by
      rw [content_add, content_sw hEne]
      omega
    have hmem' : x + sw (ω.compose D) ∈ translate (ω.origin D (sw D))
        (ω.E.filter fun y => content y ≤ minContent ω.E + ω.period - 1) := by
      rw [mem_translate, (origin_ends_mixed hmix hD).1, e, Finset.mem_filter]
      exact ⟨hmem, hc3⟩
    rw [← hwin, Finset.mem_filter] at hmem'
    exact hmem'.1

/-- The last `q` diagonals of the southwest-normalized composite are those of the normalized inner,
translated by `(r - 1) v`, where `r - 1 = M - m` is the span of the outer minus one: this does not
depend on the outer but for its span. -/
theorem IsLegalNonempty.normalize_compose_last (h : ω.IsLegalNonempty) (hmix : ω.case.IsMixed)
    (hD : IsConnectedSkew D) {x : ℤ × ℤ}
    (hx : (maxContent D - minContent D) * ω.period + ω.widthZ ≤ content x) :
    x ∈ normalize (ω.compose D) ↔
      x ∈ translate ((maxContent D - minContent D) • ω.v) (normalize ω.E) := by
  have hq := h.1.period_pos
  have hDne := hD.2.1
  have hEne : ω.E.Nonempty := h.isConnectedSkew_E.2.1
  have hF := h.1.isConnectedSkew_compose hD
  have hmin := h.1.minContent_compose hD
  have hsw := h.sw_compose_mixed hmix hD
  have hwin := h.1.compose_last_window hD
  have hw := h.width_pos
  rw [mem_normalize, mem_translate, mem_normalize]
  have hcx : minContent ω.E + maxContent D * ω.period + ω.width ≤
      content (x + sw (ω.compose D)) := by
    rw [content_add, content_sw hF.2.1, hmin]
    have : (maxContent D - minContent D) * ω.period = maxContent D * ω.period -
        minContent D * ω.period := by ring
    have hw' : (ω.width : ℤ) = ω.widthZ := rfl
    omega
  have hmM : minContent D ≤ maxContent D := minContent_le (maxContent_mem hDne)
  have e : x + sw (ω.compose D) - maxContent D • ω.v =
      x - (maxContent D - minContent D) • ω.v + sw ω.E := by
    rw [hsw, sub_smul]
    abel
  have hc3 : minContent ω.E + ω.width ≤ content (x - (maxContent D - minContent D) • ω.v +
      sw ω.E) := by
    rw [content_add, content_sub, content_smul, content_sw hEne]
    have : content ω.v = ω.period := rfl
    rw [this]
    have hw' : (ω.width : ℤ) = ω.widthZ := rfl
    omega
  constructor
  · intro hmem
    have hmem' : x + sw (ω.compose D) ∈ (ω.compose D).filter
        (fun x => minContent ω.E + maxContent D * ω.period + ω.width ≤ content x) :=
      Finset.mem_filter.mpr ⟨hmem, hcx⟩
    rw [hwin, mem_translate, (origin_ends_mixed hmix hD).2, e, Finset.mem_filter] at hmem'
    exact hmem'.1
  · intro hmem
    have hmem' : x + sw (ω.compose D) ∈ translate (ω.origin D (ne D))
        (ω.E.filter fun y => minContent ω.E + ω.width ≤ content y) := by
      rw [mem_translate, (origin_ends_mixed hmix hD).2, e, Finset.mem_filter]
      exact ⟨hmem, hc3⟩
    rw [← hwin, Finset.mem_filter] at hmem'
    exact hmem'.1

theorem span_eq_of_outer (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D) :
    (span (ω.compose D) : ℤ) = (span D : ℤ) * ω.period + ω.widthZ := by
  have := span_compose hD h.1
  exact this

theorem sw_normalize_eq {F : Diagram} (hF : IsConnectedSkew F) : sw (normalize F) = (0, 0) := by
  unfold normalize
  rw [sw_translate hF.2.1]
  ext <;> simp

theorem span_normalize (F : Diagram) : span (normalize F) = span F := span_translate _

/-- The hypotheses of `lem:gluing-mark-locality` for two southwest-normalized composites with the
same mixed inner and outers of equal span `r ≥ 2`, at a width `1 ≤ u < q`, with `τ = 0`. -/
theorem IsLegalNonempty.markWindows_compose {D' : Diagram} (h : ω.IsLegalNonempty)
    (hmix : ω.case.IsMixed) (hD : IsConnectedSkew D) (hD' : IsConnectedSkew D')
    (hspan : span D = span D') (hr : 2 ≤ span D) {u : ℕ} (hu1 : 1 ≤ u)
    (huq : (u : ℤ) < ω.period) :
    MarkWindows (normalize (ω.compose D)) (normalize (ω.compose D')) 0 (span (ω.compose D)) u := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hF := h.1.isConnectedSkew_compose hD
  have hF' := h.1.isConnectedSkew_compose hD'
  have hN := span_eq_of_outer h hD
  have hN' := span_eq_of_outer h hD'
  have hNN : span (ω.compose D') = span (ω.compose D) := by
    have : (span (ω.compose D') : ℤ) = span (ω.compose D) := by rw [hN, hN', hspan]
    exact_mod_cast this
  have hmM : span D = span D' := hspan
  have hsD := span_eq_of_isConnectedSkew hD
  have hsD' := span_eq_of_isConnectedSkew hD'
  have hdiff : maxContent D' - minContent D' = maxContent D - minContent D := by
    have : (span D : ℤ) = span D' := by rw [hspan]
    omega
  refine ⟨isConnectedSkew_normalize hF, isConnectedSkew_normalize hF', sw_normalize_eq hF,
    sw_normalize_eq hF', by rw [span_normalize], by rw [span_normalize, hNN], hu1, ?_, ?_, ?_,
    by simp [content]⟩
  · have : (2 : ℤ) ≤ span D := by exact_mod_cast hr
    have := mul_le_mul_of_nonneg_right this (show (0 : ℤ) ≤ ω.period by omega)
    omega
  · intro x hx0 hx1
    rw [h.normalize_compose_first hmix hD (by omega), h.normalize_compose_first hmix hD' (by omega)]
  · intro x hx0 hx1
    have hl : (maxContent D - minContent D) * ω.period + ω.widthZ ≤ content x := by
      have : (span D : ℤ) * ω.period = (maxContent D - minContent D) * ω.period + ω.period := by
        rw [hsD]; ring
      omega
    have hl' : (maxContent D' - minContent D') * ω.period + ω.widthZ ≤ content x := by
      rw [hdiff]; exact hl
    rw [h.normalize_compose_last hmix hD' hl', hdiff, translate_zero,
      ← h.normalize_compose_last hmix hD hl]

/-- A legal mark of width `u ≥ 1` on a southwest-normalized connected diagram of span `N` is a
candidate mark in the sense of `lem:gluing-mark-locality`. -/
theorem localMark_of_legal {F W : Diagram} {v : ℤ × ℤ} {cs : AttachCase} {N u : ℕ}
    (hF : IsConnectedSkew F) (hsw : sw F = (0, 0)) (hN : span F = N) (hu : span W = u)
    (h1 : 1 ≤ u) (hl : (MarkedInner.mk F W v cs).IsLegal) : LocalMark F N u W v := by
  have hwf := hl.1
  have hnon : (MarkedInner.mk F W v cs).IsNonemptyMark := by
    rcases hwf.2 with he | hn
    · have : W = ∅ := he.1
      subst this
      simp [span, contents] at hu
      omega
    · exact hn
  have hb := hnon.content_bounds hF
  have hmin : minContent F = 0 := by
    have := content_sw hF.2.1
    rw [hsw] at this
    simpa [content] using this.symm
  have hspan := hwf.span_eq
  refine ⟨hnon.2.2.1, fun x hx => ?_, ?_⟩
  · have := hb.1 x hx
    have hw : (MarkedInner.mk F W v cs).width = u := hu
    rw [hmin, hw] at this
    omega
  · have hw : (MarkedInner.mk F W v cs).width = u := hu
    have hp : (MarkedInner.mk F W v cs).period = content v := rfl
    have : (span F : ℤ) = (MarkedInner.mk F W v cs).period + (MarkedInner.mk F W v cs).width :=
      hspan
    rw [hN, hw, hp] at this
    omega

/-- **`cor:gluing-mark-transfer`, widths `1 ≤ u < q`, outers of span `r ≥ 2`.**  The
southwest-normalized composites carry the same legal marks of width `u`, with the same cells
`W₋`, displacement and attachment case. -/
theorem IsLegalNonempty.legal_transfer_mid {D' : Diagram} (h : ω.IsLegalNonempty)
    (hmix : ω.case.IsMixed) (hD : IsConnectedSkew D) (hD' : IsConnectedSkew D')
    (hspan : span D = span D') (hr : 2 ≤ span D) {u : ℕ} (hu1 : 1 ≤ u)
    (huq : (u : ℤ) < ω.period) (W : Diagram) (v : ℤ × ℤ) (cs : AttachCase)
    (hW : span W = u) :
    (MarkedInner.mk (normalize (ω.compose D)) W v cs).IsLegal ↔
      (MarkedInner.mk (normalize (ω.compose D')) W v cs).IsLegal := by
  have M := h.markWindows_compose hmix hD hD' hspan hr hu1 huq
  have hF := h.1.isConnectedSkew_compose hD
  have hF' := h.1.isConnectedSkew_compose hD'
  have hN := span_eq_of_outer h hD
  have hN' := span_eq_of_outer h hD'
  have hNN : span (ω.compose D') = span (ω.compose D) := by
    have : (span (ω.compose D') : ℤ) = span (ω.compose D) := by rw [hN, hN', hspan]
    exact_mod_cast this
  constructor
  · intro hl
    have L := localMark_of_legal (isConnectedSkew_normalize hF) (sw_normalize_eq hF)
      (span_normalize _) hW hu1 hl
    have := (mark_locality M L cs).mp hl
    simpa using this
  · intro hl
    have L := localMark_of_legal (isConnectedSkew_normalize hF') (sw_normalize_eq hF')
      (by rw [span_normalize, hNN]) hW hu1 hl
    have := (mark_locality M.symm L cs).mp hl
    simpa using this

/-! ### Width zero -/

theorem width_zero_iff {W : Diagram} : span W = 0 ↔ W = ∅ := by
  unfold span contents
  rw [Finset.card_eq_zero, Finset.image_eq_empty]

/-- The empty mark `(∅, v_H, (a))` of a connected skew diagram is legal. -/
theorem isLegal_emptyMark {F : Diagram} (hF : IsConnectedSkew F) :
    (MarkedInner.mk F ∅ (vH F) .a).IsLegal := by
  have hne := hF.2.1
  have hper : (MarkedInner.mk F ∅ (vH F) .a).period = span F := by
    have := span_eq_of_isConnectedSkew hF
    unfold MarkedInner.period vH
    simp only [content_add, content_sub, content_ne hne, content_sw hne]
    simp only [content]
    omega
  have hpos : 0 < (span F : ℤ) := by
    have := span_eq_of_isConnectedSkew hF
    have := minContent_le (maxContent_mem hne)
    omega
  refine ⟨⟨hF, Or.inl ⟨rfl, rfl, rfl⟩⟩, ?_, ?_, ?_, ?_⟩
  · intro W' hW' hlt hsk hcont x hx
    have : W' = ∅ := by
      have : contents W' = ∅ := by simpa [contents] using hcont
      simpa [contents] using this
    exact absurd hlt (by simp [this])
  · refine ⟨by simp [MarkedInner.width, span, contents], ?_⟩
    have : (MarkedInner.mk F ∅ (vH F) .a).width = 0 := by simp [MarkedInner.width, span, contents]
    rw [this, hper]
    simpa using hpos
  · have hu : (MarkedInner.mk F ∅ (vH F) .a).upper = ∅ := by
      simp [MarkedInner.upper, translate]
    refine ⟨?_, ?_⟩
    · change IsConnectedSkew (F \ ∅)
      simpa using hF
    · change IsConnectedSkew (F \ (MarkedInner.mk F ∅ (vH F) .a).upper)
      rw [hu]
      simpa using hF
  · exact noHatAdjacency_of_empty rfl

/-- The legal marks of width zero on a connected skew diagram: only the empty mark. -/
theorem legal_width_zero_iff {F W : Diagram} {v : ℤ × ℤ} {cs : AttachCase}
    (hF : IsConnectedSkew F) (hW : span W = 0) :
    (MarkedInner.mk F W v cs).IsLegal ↔ W = ∅ ∧ v = vH F ∧ cs = .a := by
  have hW0 := width_zero_iff.mp hW
  constructor
  · intro hl
    rcases hl.1.2 with he | hn
    · exact ⟨hW0, he.2.1, he.2.2⟩
    · exact absurd hW0 hn.1.ne_empty
  · rintro ⟨-, rfl, rfl⟩
    subst hW0
    exact isLegal_emptyMark hF

/-! ### No legal mark of width `q` -/

/-- In case (d) the classes `(m, a)` and `(M, a)` with `w ≤ a < q` are singletons exactly when the
private diagonal `a` of `E` is: `mixLo = mixHi`. -/
theorem IsLegalNonempty.mix_singleton_private (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D)
    (hcd : ω.case = .d) {s t : ℤ} (hph : ω.IsPhases s t) {J : ℤ}
    (hJ : J = minContent D ∨ J = maxContent D) {a : ℤ} (ha1 : ω.widthZ ≤ a)
    (hlo : ω.lo a = ω.hi a) :
    ω.mixLo D J a = ω.mixHi J a := by
  have hmM : minContent D ≤ maxContent D := minContent_le (maxContent_mem hD.2.1)
  have hw := h.width_pos
  have hv : ValidClass (minContent D) (maxContent D) ω.widthZ J a := by
    unfold ValidClass
    omega
  have hF := mixLo_formula h hD hcd hph (by omega) hv
  have he := D_end_singleton hD hJ
  unfold mixGLo profM at hF
  have hnl : ¬ a < ω.widthZ := by omega
  simp only [hnl, ite_false] at hF
  have hJ' : minContent D ≤ J ∧ J ≤ maxContent D := by omega
  simp only [hJ', and_self, ite_true] at hF
  unfold mixHi
  omega

/-- **Case (d), no mark of width `q`.**  A composite `D ∘_ω E` of a legal case-(d) mark carries no
legal mark of width `q`, even after a translation `t`.  The displacement of such a mark is both
`y - sw(F)` and `ne(F) - x`, for the cells `x`, `y` on the private singleton diagonals `q - 1` and
`N - q`.  **Differs from the paper's route.**  The paper compares two sums of southeast bits using
the periodicity of `lem:gluing-coding`; here the four southeast rows are read directly from
`J v₁ + h_a`, and the two readings of the displacement differ by `B_w - B_q = 1`.  The outer may
have any span (for span one this is also excluded by II). -/
theorem IsLegalNonempty.no_mark_of_width_period_d (h : ω.IsLegalNonempty) (hcd : ω.case = .d)
    (hD : IsConnectedSkew D) (t : ℤ × ℤ) {W : Diagram} {vη : ℤ × ℤ}
    {cs : AttachCase} (hW : (span W : ℤ) = ω.period) :
    ¬ (MarkedInner.mk (translate t (ω.compose D)) W vη cs).IsLegal := by
  intro hl
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hDne := hD.2.1
  have hmM : minContent D ≤ maxContent D := minContent_le (maxContent_mem hDne)
  obtain ⟨s, t', hph⟩ := h.exists_phases
  have hlt := h.phases_lt (Or.inr hcd) hph
  have hc := mix_classRows h hD hcd hph hlt
  have hmin := h.minContent_compose' hD
  have hN := h.span_compose_eq hD
  have hF0 := h.1.isConnectedSkew_compose hD
  have hG := isConnectedSkew_translate t hF0
  have hGne := hG.2.1
  have hF0ne := hF0.2.1
  have hnon : (MarkedInner.mk (translate t (ω.compose D)) W vη cs).IsNonemptyMark := by
    rcases hl.1.2 with he | hn
    · have : W = ∅ := he.1
      subst this
      simp [span, contents] at hW
      omega
    · exact hn
  have hWne : W.Nonempty := hnon.1
  have hWsk : IsConnectedSkew W := hnon.2.1
  have hWG : W ⊆ translate t (ω.compose D) := hnon.2.2.1
  have hUG : translate vη W ⊆ translate t (ω.compose D) := hnon.2.2.2.1
  have hswW : sw (translate t (ω.compose D)) ∈ W := hnon.2.2.2.2.1
  have hspan : (span (translate t (ω.compose D)) : ℤ) = content vη + (span W : ℤ) :=
    hl.1.span_eq
  rw [span_translate] at hspan
  have hminG : minContent (translate t (ω.compose D)) =
      minContent (ω.compose D) + content t := minContent_translate hF0ne t
  have hminW : minContent W = minContent (translate t (ω.compose D)) := by
    apply le_antisymm
    · have := content_mem_contents hswW
      rw [content_sw hGne] at this
      exact minContent_le this
    · exact minContent_le (Finset.image_subset_image hWG (minContent_mem hWne))
  have hspW := span_eq_of_isConnectedSkew hWsk
  obtain ⟨zi, hz⟩ := mem_contents_iff.mp (maxContent_mem hWne)
  have hzW : (zi, zi + maxContent W) ∈ W := hz
  have hzc : content (zi, zi + maxContent W) = maxContent W := by simp [content]
  -- the four cells of the composite
  have hsw : sw (translate t (ω.compose D)) = sw (ω.compose D) + t := sw_translate hF0ne t
  have hswUG : sw (translate t (ω.compose D)) + vη ∈ translate t (ω.compose D) :=
    hUG (Finset.mem_image.mpr ⟨_, hswW, rfl⟩)
  have hzUG : (zi, zi + maxContent W) + vη ∈ translate t (ω.compose D) :=
    hUG (Finset.mem_image.mpr ⟨_, hzW, rfl⟩)
  have hzG : (zi, zi + maxContent W) ∈ translate t (ω.compose D) := hWG hzW
  rw [mem_translate] at hswUG hzUG hzG
  have hswF : sw (ω.compose D) ∈ ω.compose D := sw_mem hF0ne
  have hcsw : content (sw (ω.compose D)) = minContent (ω.compose D) := content_sw hF0ne
  have hcv : content vη = (span (ω.compose D) : ℤ) - ω.period := by omega
  have e1 : (maxContent D + 1) * ω.period = maxContent D * ω.period + ω.period := by ring
  have e2 : (maxContent D - minContent D + 1) * ω.period =
      maxContent D * ω.period - minContent D * ω.period + ω.period := by ring
  have b1 := hc.row_bounds (J := minContent D) (a := 0) (le_refl _) (by omega) hswF
    (by rw [hcsw, hmin]; ring)
  have b2 := hc.row_bounds (J := minContent D) (a := ω.period - 1) (by omega) (by omega) hzG
    (by rw [content_sub, hzc, hminG, hmin] at *; omega)
  have b3 := hc.row_bounds (J := maxContent D) (a := ω.widthZ) (by omega) hq hswUG
    (by
      rw [content_sub, content_add, hsw, content_add, hcsw, hmin, hcv, hN]
      omega)
  have b4 := hc.row_bounds (J := maxContent D + 1) (a := ω.widthZ - 1) (by omega) (by omega) hzUG
    (by
      rw [content_sub, content_add, hzc, hcv, hN, hminG, hmin] at *
      omega)
  have f0 := mix_first h hD hcd
  have f1 := mix_last h hD hcd hph
  have caps := d_caps h hcd
  have g1 := h.lo_pred_period_eq_hi
  have g2 := h.lo_w_eq_hi_w
  have hp1 : (maxContent D + 1) * ω.rowShift = maxContent D * ω.rowShift + ω.rowShift := by ring
  have r1 : (sw (ω.compose D)).1 = minContent D * ω.rowShift + ω.hi 0 := by
    have := b1.2.1
    have := b1.2.2
    unfold mixHi at *
    omega
  have r2 := h.mix_singleton_private hD hcd hph (J := minContent D) (Or.inl rfl)
    (a := ω.period - 1) (by omega) g1
  have r3 := h.mix_singleton_private hD hcd hph (J := maxContent D) (Or.inr rfl)
    (a := ω.widthZ) (le_refl _) g2
  unfold mixHi at f0 f1 r2 r3
  simp only [dLo, dHi, zero_add] at caps
  have u1 : (sw (translate t (ω.compose D)) + vη - t).1 = (sw (ω.compose D)).1 + vη.1 := by
    rw [hsw]
    simp only [Prod.fst_sub, Prod.fst_add]
    omega
  have u2 : ((zi, zi + maxContent W) + vη - t).1 = (zi - t.1) + vη.1 := by
    simp only [Prod.fst_sub, Prod.fst_add]
    omega
  have u3 : ((zi, zi + maxContent W) - t).1 = zi - t.1 := by
    simp only [Prod.fst_sub]
  unfold mixHi at b1 b2 b3 b4
  omega

/-- **Case (c), no mark of width `q`.**  **Differs from the paper's route.**  The paper treats case
(c) by antitransposition; here the rotation `compose_rotate_c` reduces it to case (d). -/
theorem IsLegalNonempty.no_mark_of_width_period_c (h : ω.IsLegalNonempty) (hcc : ω.case = .c)
    (hD : IsConnectedSkew D) (t : ℤ × ℤ) {W : Diagram} {vη : ℤ × ℤ} {cs : AttachCase}
    (hW : (span W : ℤ) = ω.period) :
    ¬ (MarkedInner.mk (translate t (ω.compose D)) W vη cs).IsLegal := by
  intro hl
  have hF := compose_rotate_c hcc hD.2.1
  have hl' := isLegal_rotate hl
  have e : (MarkedInner.mk (translate t (ω.compose D)) W vη cs).rotate =
      MarkedInner.mk (translate (-t) (ω.rotate.compose (GluingCore.rotate D)))
        (GluingCore.rotate (translate vη W)) vη cs.rotate := by
    change MarkedInner.mk (GluingCore.rotate (translate t (ω.compose D)))
      (GluingCore.rotate (translate vη W)) vη cs.rotate = _
    rw [hF, rotate_translate_diagram, GluingCore.rotate_rotate]
  rw [e] at hl'
  refine h.rotate.no_mark_of_width_period_d (rotate_case_d hcc) (isConnectedSkew_rotate hD) (-t)
    (W := GluingCore.rotate (translate vη W)) (vη := vη) (cs := cs.rotate) ?_ hl'
  have : span (GluingCore.rotate (translate vη W)) = span W := by
    rw [span_rotate, span_translate]
  rw [this, hW]
  rfl

/-- **`cor:gluing-mark-transfer`, `u = q`.**  A composite of a legal mixed mark `ω` of period `q`
carries no legal mark of width `q`, whatever the connected outer, even after a translation. -/
theorem IsLegalNonempty.no_mark_of_width_period (h : ω.IsLegalNonempty) (hmix : ω.case.IsMixed)
    (hD : IsConnectedSkew D) (t : ℤ × ℤ) {W : Diagram} {vη : ℤ × ℤ} {cs : AttachCase}
    (hW : (span W : ℤ) = ω.period) :
    ¬ (MarkedInner.mk (translate t (ω.compose D)) W vη cs).IsLegal := by
  rcases hmix with hc | hc
  · exact h.no_mark_of_width_period_c hc hD t hW
  · exact h.no_mark_of_width_period_d hc hD t hW

/-- A legal mark of width `u ≥ 1` on a southwest-normalized connected diagram `F` of span `N` has
`W₋` on the contents `[0, u - 1]` and a displacement `v` that is a cell of `F` of content `N - u`.
This reduces the search for the legal marks of a given width to a finite set of candidates. -/
theorem legal_mark_bounds {F W : Diagram} {v : ℤ × ℤ} {cs : AttachCase} {N u : ℕ}
    (hF : IsConnectedSkew F) (hsw : sw F = (0, 0)) (hN : span F = N) (hu : span W = u)
    (h1 : 1 ≤ u) (hl : (MarkedInner.mk F W v cs).IsLegal) :
    W ⊆ F.filter (fun x => content x ≤ (u : ℤ) - 1) ∧
      v ∈ F.filter (fun x => content x = (N : ℤ) - u) := by
  have L := localMark_of_legal hF hsw hN hu h1 hl
  have hnon : (MarkedInner.mk F W v cs).IsNonemptyMark := by
    rcases hl.1.2 with he | hn
    · have : W = ∅ := he.1
      subst this
      simp [span, contents] at hu
      omega
    · exact hn
  refine ⟨fun x hx => Finset.mem_filter.mpr ⟨L.subset hx, (L.content_mem x hx).2⟩, ?_⟩
  have hswW : sw F ∈ W := hnon.2.2.2.2.1
  have hUF : translate v W ⊆ F := hnon.2.2.2.1
  have := hUF (Finset.mem_image.mpr ⟨_, hswW, rfl⟩)
  rw [hsw] at this
  have e : ((0 : ℤ), (0 : ℤ)) + v = v := by ext <;> simp
  rw [e] at this
  exact Finset.mem_filter.mpr ⟨this, L.content_v⟩

/-! ### Assembly -/

theorem maxContent_normalize {F : Diagram} (hF : IsConnectedSkew F) :
    maxContent (normalize F) = (span F : ℤ) - 1 := by
  have hne := hF.2.1
  unfold normalize
  rw [maxContent_translate hne, span_eq_of_isConnectedSkew hF]
  have : content (-sw F) = -minContent F := by
    rw [← content_sw hne]
    simp only [content, Prod.fst_neg, Prod.snd_neg]
    ring
  rw [this]
  ring

/-- For outers of span one, the normalized composites are both the normalized inner. -/
theorem IsLegalNonempty.normalize_compose_of_span_one (h : ω.IsLegalNonempty)
    (hmix : ω.case.IsMixed) (hD : IsConnectedSkew D) (h1 : span D = 1) :
    normalize (ω.compose D) = normalize ω.E := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hsD := span_eq_of_isConnectedSkew hD
  have h0 : maxContent D - minContent D = 0 := by
    have : (span D : ℤ) = 1 := by rw [h1]; rfl
    omega
  ext x
  by_cases hx : content x ≤ ω.period - 1
  · exact h.normalize_compose_first hmix hD hx
  · rw [h.normalize_compose_last hmix hD (by rw [h0]; omega), h0, zero_smul, translate_zero]

/-- **`cor:gluing-mark-transfer`, the hatted mark and the middles.**  For a legal mark of width
`1 ≤ u < q` on one of the two composites, both middles are connected skew and the hatted marks
agree. -/
theorem IsLegalNonempty.hatMark_transfer {D' : Diagram} (h : ω.IsLegalNonempty)
    (hmix : ω.case.IsMixed) (hD : IsConnectedSkew D) (hD' : IsConnectedSkew D')
    (hspan : span D = span D') {u : ℕ} (hu1 : 1 ≤ u)
    (huq : (u : ℤ) < ω.period) {W : Diagram} {v : ℤ × ℤ} {cs : AttachCase} (hW : span W = u)
    (hl : (MarkedInner.mk (normalize (ω.compose D)) W v cs).IsLegal) :
    IsConnectedSkew (MarkedInner.mk (normalize (ω.compose D)) W v cs).middle ∧
    IsConnectedSkew (MarkedInner.mk (normalize (ω.compose D')) W v cs).middle ∧
    (MarkedInner.mk (normalize (ω.compose D')) W v cs).hatMark W =
      (MarkedInner.mk (normalize (ω.compose D)) W v cs).hatMark W := by
  have hF := h.1.isConnectedSkew_compose hD
  by_cases hr : span D = 1
  · have hr' : span D' = 1 := by rw [← hspan]; exact hr
    have hWne : W.Nonempty := by
      apply Finset.nonempty_iff_ne_empty.mpr
      intro hW0
      subst hW0
      simp [span, contents] at hW
      omega
    have hm : IsConnectedSkew (MarkedInner.mk (normalize (ω.compose D)) W v cs).middle :=
      MarkedInner.IsLegal.middle_connected hl hWne
    rw [h.normalize_compose_of_span_one hmix hD' hr', ← h.normalize_compose_of_span_one hmix hD hr]
    exact ⟨hm, hm, rfl⟩
  · have hr2 : 2 ≤ span D := by
      have h1 : 0 < span D := by
        unfold span
        exact Finset.card_pos.mpr (Finset.image_nonempty.mpr hD.2.1)
      omega
    have M := h.markWindows_compose hmix hD hD' hspan hr2 hu1 huq
    have L := localMark_of_legal (isConnectedSkew_normalize hF) (sw_normalize_eq hF)
      (span_normalize _) hW hu1 hl
    have := mark_locality_middle_hatMark M L hl
    simpa using this

/-- The southwest-normalized composites of outers of equal span have the same northeast cell. -/
theorem IsLegalNonempty.ne_normalize_compose {D' : Diagram} (h : ω.IsLegalNonempty)
    (hmix : ω.case.IsMixed) (hD : IsConnectedSkew D) (hD' : IsConnectedSkew D')
    (hspan : span D = span D') :
    ne (normalize (ω.compose D)) = ne (normalize (ω.compose D')) := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hF := h.1.isConnectedSkew_compose hD
  have hF' := h.1.isConnectedSkew_compose hD'
  have hNF := isConnectedSkew_normalize hF
  have hNF' := isConnectedSkew_normalize hF'
  have hN := span_eq_of_outer h hD
  have hN' := span_eq_of_outer h hD'
  have hsD := span_eq_of_isConnectedSkew hD
  have hsD' := span_eq_of_isConnectedSkew hD'
  have hdiff : maxContent D' - minContent D' = maxContent D - minContent D := by
    have : (span D : ℤ) = span D' := by rw [hspan]
    omega
  have hz := ne_mem hNF.2.1
  have hzc := content_ne hNF.2.1
  rw [maxContent_normalize hF] at hzc
  have hl : (maxContent D - minContent D) * ω.period + ω.widthZ ≤ content (ne (normalize
      (ω.compose D))) := by
    rw [hzc, hN, hsD]
    have : (maxContent D - minContent D + 1) * ω.period =
        (maxContent D - minContent D) * ω.period + ω.period := by ring
    omega
  have hl' : (maxContent D' - minContent D') * ω.period + ω.widthZ ≤ content (ne (normalize
      (ω.compose D))) := by rw [hdiff]; exact hl
  have hz' : ne (normalize (ω.compose D)) ∈ normalize (ω.compose D') := by
    rw [h.normalize_compose_last hmix hD' hl', hdiff, ← h.normalize_compose_last hmix hD hl]
    exact hz
  have hzc' : content (ne (normalize (ω.compose D))) = maxContent (normalize (ω.compose D')) := by
    rw [maxContent_normalize hF', hzc, hN, hN', hspan]
  exact eq_ne_of_content hNF' hz' hzc'

/-- **`cor:gluing-mark-transfer`.**  Let `ω` be a legal mixed mark of period `q`, and let `D`, `D'`
be connected diagrams of equal span.  For every width `0 ≤ u ≤ q` the southwest-normalized diagrams
`D ∘_ω E` and `D' ∘_ω E` carry the same legal marks of width `u`: a mark with cells `W₋`,
displacement `v`, attachment case `cs` and span `W₋ = u` is legal on one exactly when it is on
the other (and then its middle is connected skew with the same hatted mark, by
`hatMark_transfer`).  At `u = q` neither carries one. -/
theorem IsLegalNonempty.mark_transfer {D' : Diagram} (h : ω.IsLegalNonempty)
    (hmix : ω.case.IsMixed) (hD : IsConnectedSkew D) (hD' : IsConnectedSkew D')
    (hspan : span D = span D') {u : ℕ} (hu : (u : ℤ) ≤ ω.period) (W : Diagram) (v : ℤ × ℤ)
    (cs : AttachCase) (hW : span W = u) :
    ((MarkedInner.mk (normalize (ω.compose D)) W v cs).IsLegal ↔
      (MarkedInner.mk (normalize (ω.compose D')) W v cs).IsLegal) ∧
    ((u : ℤ) = ω.period →
      ¬ (MarkedInner.mk (normalize (ω.compose D)) W v cs).IsLegal ∧
      ¬ (MarkedInner.mk (normalize (ω.compose D')) W v cs).IsLegal) := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hF := h.1.isConnectedSkew_compose hD
  have hF' := h.1.isConnectedSkew_compose hD'
  have hNF := isConnectedSkew_normalize hF
  have hNF' := isConnectedSkew_normalize hF'
  refine ⟨?_, fun hq' => ?_⟩
  · by_cases hu0 : u = 0
    · subst hu0
      rw [legal_width_zero_iff hNF hW, legal_width_zero_iff hNF' hW]
      have hv : vH (normalize (ω.compose D)) = vH (normalize (ω.compose D')) := by
        unfold vH
        rw [h.ne_normalize_compose hmix hD hD' hspan, sw_normalize_eq hF, sw_normalize_eq hF']
      rw [hv]
    · by_cases huq : (u : ℤ) = ω.period
      · have e1 := (h.no_mark_of_width_period hmix hD (-(sw (ω.compose D))) (W := W) (vη := v)
          (cs := cs) (by rw [hW]; exact huq))
        have e2 := (h.no_mark_of_width_period hmix hD' (-(sw (ω.compose D'))) (W := W) (vη := v)
          (cs := cs) (by rw [hW]; exact huq))
        exact ⟨fun hl => absurd hl e1, fun hl => absurd hl e2⟩
      · have hlt : (u : ℤ) < ω.period := lt_of_le_of_ne hu huq
        by_cases hr : span D = 1
        · have hr' : span D' = 1 := by rw [← hspan]; exact hr
          rw [h.normalize_compose_of_span_one hmix hD hr,
            h.normalize_compose_of_span_one hmix hD' hr']
        · have hr2 : 2 ≤ span D := by
            have := hD.2.1
            have h1 : 0 < span D := by
              unfold span
              exact Finset.card_pos.mpr (Finset.image_nonempty.mpr this)
            omega
          exact h.legal_transfer_mid hmix hD hD' hspan hr2 (by omega) hlt W v cs hW
  · have e1 := (h.no_mark_of_width_period hmix hD (-(sw (ω.compose D))) (W := W) (vη := v)
      (cs := cs) (by rw [hW]; exact hq'))
    have e2 := (h.no_mark_of_width_period hmix hD' (-(sw (ω.compose D'))) (W := W) (vη := v)
      (cs := cs) (by rw [hW]; exact hq'))
    exact ⟨e1, e2⟩

/-- **`cor:gluing-mark-transfer`, over a fiber.**  Schur-equal connected outers have equal span, so
the diagrams `A ∘_ω E` of the fiber `fiber cellSchur ω Q` with the first orientation all carry the
same legal marks of each width at most `q`, and none of width `q`. -/
theorem IsLegalNonempty.mark_transfer_of_cellSchur_eq {A A' : Diagram} (h : ω.IsLegalNonempty)
    (hmix : ω.case.IsMixed) (hA : IsConnectedSkew A) (hA' : IsConnectedSkew A')
    (hs : cellSchur A = cellSchur A') {u : ℕ} (hu : (u : ℤ) ≤ ω.period) (W : Diagram)
    (v : ℤ × ℤ) (cs : AttachCase) (hW : span W = u) :
    ((MarkedInner.mk (normalize (ω.compose A)) W v cs).IsLegal ↔
      (MarkedInner.mk (normalize (ω.compose A')) W v cs).IsLegal) ∧
    ((u : ℤ) = ω.period →
      ¬ (MarkedInner.mk (normalize (ω.compose A)) W v cs).IsLegal ∧
      ¬ (MarkedInner.mk (normalize (ω.compose A')) W v cs).IsLegal) :=
  h.mark_transfer hmix hA hA' (span_eq_of_cellSchur_eq hA hA' hs) hu W v cs hW

end MarkedInner

/-! ### Checked examples: the transfer and its sharpness

The hook `(2, 1)` with its singleton case-(d) mark has period `q = 2`.  The outers `(3)` and
`(2, 2)` have equal span three. -/

section Examples

open MarkedInner

/-- `hookInner` is a legal mixed mark with a nonempty copy. -/
theorem hookInner_isLegalNonempty : hookInner.IsLegalNonempty := ⟨by decide, ⟨(1, 0), by decide⟩⟩

/-- Instance of `cor:gluing-mark-transfer` at `u = 1 < q`: the composites `(3) ∘ (2, 1)` and
`(2, 2) ∘ (2, 1)` carry the same legal marks of width one. -/
example : ∀ (W : Diagram) (v : ℤ × ℤ) (cs : AttachCase), span W = 1 →
    ((MarkedInner.mk (normalize (compose (skewOf [3] []) hookInner)) W v cs).IsLegal ↔
      (MarkedInner.mk (normalize (compose (skewOf [2, 2] []) hookInner)) W v cs).IsLegal) :=
  fun W v cs hW => (hookInner_isLegalNonempty.mark_transfer (Or.inr rfl) (by decide)
    (by decide) (by decide) (u := 1) (by decide) W v cs hW).1

/-- Sharpness at `u = q + 1 = 3`: `(3) ∘ (2, 1)` carries a legal mark of width three, the case-(d)
mark with `W₋ = {(-1, 0), (-1, 1), (0, 0)}` and displacement `(-2, 2)`. -/
example : ∃ (W : Diagram) (v : ℤ × ℤ) (cs : AttachCase), span W = 3 ∧
    (MarkedInner.mk (normalize (compose (skewOf [3] []) hookInner)) W v cs).IsLegal :=
  ⟨{(-1, 0), (-1, 1), (0, 0)}, (-2, 2), .d, by decide, by decide +kernel⟩

/-- The southwest-normalized composite `(2, 2) ∘ (2, 1)`, as a list of cells. -/
def sharpComposite : Diagram :=
  {(-3, 0), (-2, 0), (-3, 2), (-3, 3), (-1, 0), (0, 0), (-2, 1), (-2, 2), (-1, 1), (-3, 1)}

theorem normalize_compose_sharp :
    normalize (compose (skewOf [2, 2] []) hookInner) = sharpComposite := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The candidate marks of width three on `(2, 2) ∘ (2, 1)` are all illegal. -/
theorem sharpComposite_no_candidate :
    ∀ W ∈ (sharpComposite.filter (fun x => content x ≤ 2)).powerset,
      ∀ x ∈ sharpComposite.filter (fun x => content x = 4),
      ∀ cs ∈ ({AttachCase.a, .b, .c, .d} : Finset AttachCase), span W = 3 →
        ¬ (MarkedInner.mk sharpComposite W x cs).IsLegal := by
  decide +kernel

/-- Sharpness at `u = q + 1 = 3`: `(2, 2) ∘ (2, 1)` carries no legal mark of width three. -/
example : ¬ ∃ (W : Diagram) (v : ℤ × ℤ) (cs : AttachCase), span W = 3 ∧
    (MarkedInner.mk (normalize (compose (skewOf [2, 2] []) hookInner)) W v cs).IsLegal := by
  rintro ⟨W, v, cs, hW, hl⟩
  rw [normalize_compose_sharp] at hl
  have hF : IsConnectedSkew sharpComposite := by decide +kernel
  have hsw : sw sharpComposite = (0, 0) := by decide +kernel
  have hN : span sharpComposite = 7 := by decide +kernel
  obtain ⟨hWs, hv⟩ := legal_mark_bounds (u := 3) hF hsw hN hW (by omega) hl
  have hcs : cs ∈ ({AttachCase.a, .b, .c, .d} : Finset AttachCase) := by cases cs <;> decide
  exact sharpComposite_no_candidate W (Finset.mem_powerset.mpr hWs) v hv cs hcs hW hl

end Examples

end GluingCore
