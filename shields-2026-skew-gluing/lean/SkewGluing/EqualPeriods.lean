import SkewGluing.Antitranspose
import SkewGluing.Local
import SkewGluing.Invariance
import SkewGluing.MarkLocality
import SkewGluing.CellSchur

/-!
# Equal periods give the same fiber

Formalizes `shields-2026-skew-gluing.tex`, «Equal and divisible periods»
(`lem:gluing-equal`), with `eq:gluing-gauge`, and the fiber clique statement of
`def:gluing-graph`.

* `MarkedInner.IsLegal.width_eq_span_emod`, `MarkedInner.IsLegal.span_outer_eq_div`: the span law
  fixes the width `w = N mod q` and the outer span `r = N / q`;
  `MarkedInner.IsLegal.width_eq_of_translate` gives equal widths and outer spans for two charts
  of one parent with equal periods.
* `MarkedInner.IsLegal.exists_translate_of_windows`: the two extreme windows determine `E` for
  every legal mark, empty or not (`IsLegalNonempty.windows_determine` extended to width zero);
  `MarkedInner.IsLegal.windows_of_translate` supplies the windows of translates.
* `MarkedInner.IsLegal.equal_periods_cases`, `MarkedInner.IsLegal.equal_periods_outer`: two legal
  marks of equal period on one parent have inner diagrams that are translates, and either the
  marks agree up to that translation (with `s_{D'} = s_D`), or they are the ordinary (a)/(b)
  double (displacements differing by `e`, `s_{D'} = ι s_D`); a mixed mark is never in a double.
* `fiber_gauge`, `fiberClass_gauge`: for ordinary marks `ω_a`, `ω_b` on one diagram with
  `v_a = v_b + e`, `𝓕(ω_a, Q) = 𝓕(ω_b, ι Q)` as sets of cells, in both orientations
  (`MarkedInner.rotate_compose_antitranspose_gauge`); `fiber_emptyMarks` is the width-zero form.
* `MarkedInner.IsLegal.equal_periods_same_fiber`, `Chart.IsProperLegal.equal_periods_same_fiber`:
  **`lem:gluing-equal`**, `𝓕(ω, s_D) = 𝓕(ω', s_{D'})` up to translation, for charts and for
  marked inners.  `Chart.IsProperLegal.equal_periods_cases` is the chart form of the case split.
* `exists_chart_of_mem_fiberClass`, `fiberClass_hasCommonFinalFactor`: two members of one fiber
  that are not translates of one another have a common final factor (`HasCommonFinalFactor`);
  no Olson-Harris input is used.

Sorry-free.
-/

namespace SkewGluing

namespace MarkedInner

variable {ω ω' : MarkedInner} {D D' : Diagram}

/-- The first diagonal of a connected skew diagram is a singleton. -/
theorem diagLo_eq_diagHi_minContent {E : Diagram} (hE : IsConnectedSkew E) :
    diagLo E (minContent E) = diagHi E (minContent E) :=
  (isConnectedSkew_iff_diagonal.mp hE).2.2.2.2 _
    (minContent_mem (isConnectedSkew_iff_diagonal.mp hE).1)
    (Or.inl (fun hm => by have := minContent_le hm; omega))

/-- The diagonal `w` of a legal mark is a singleton: for a nonempty mark this is
`lem:gluing-local` (1), for the empty mark it is the first diagonal. -/
theorem IsLegal.diagLo_width_eq_diagHi (h : ω.IsLegal) :
    diagLo ω.E (minContent ω.E + ω.width) = diagHi ω.E (minContent ω.E + ω.width) := by
  by_cases hW : ω.W = ∅
  · have hw : ω.width = 0 := by simp [width, span, contents, hW]
    rw [hw]
    simpa using diagLo_eq_diagHi_minContent h.1.1
  · have := (IsLegalNonempty.lo_w_eq_hi_w ⟨h, Finset.nonempty_iff_ne_empty.mpr hW⟩)
    exact this

/-- A legal mark with a nonempty copy has positive width. -/
theorem IsLegal.width_pos_of_nonempty (h : ω.IsLegal) (hW : ω.W.Nonempty) : 0 < ω.width := by
  have := (IsLegalNonempty.width_pos ⟨h, hW⟩)
  unfold widthZ at this
  omega

/-- A mark with empty copy has width zero. -/
theorem width_eq_zero_of_eq_empty (hW : ω.W = ∅) : ω.width = 0 := by
  simp [width, span, contents, hW]

/-- **`lem:gluing-local` (3), the two windows determine `E`, for every legal mark.**  Let
`ω`, `ω'` be legal marks of the same period and the same width (empty or not), and `D`, `D'`
connected outers.  If the first `q` diagonals and the last `q` diagonals of `D ∘_ω E` and
`D' ∘_{ω'} E'` are translates of each other, then `E'` is a translate of `E`.

This extends `IsLegalNonempty.windows_determine` to the empty mark, with the same proof. -/
theorem IsLegal.exists_translate_of_windows (h : ω.IsLegal) (h' : ω'.IsLegal)
    (hD : IsConnectedSkew D) (hD' : IsConnectedSkew D') (hq : ω'.period = ω.period)
    (hw : ω'.width = ω.width) {σ₁ σ₂ : ℤ × ℤ}
    (h1 : SkewGluing.translate σ₁ ((ω.compose D).filter fun x =>
        content x ≤ minContent (ω.compose D) + ω.period - 1) =
      (ω'.compose D').filter fun x => content x ≤ minContent (ω'.compose D') + ω.period - 1)
    (h2 : SkewGluing.translate σ₂ ((ω.compose D).filter fun x =>
        maxContent (ω.compose D) - ω.period + 1 ≤ content x) =
      (ω'.compose D').filter fun x => maxContent (ω'.compose D') - ω.period + 1 ≤ content x) :
    ∃ δ, ω'.E = SkewGluing.translate δ ω.E := by
  have hwn : (ω'.width : ℤ) = ω.width := by exact_mod_cast hw
  have ec1 : ∀ {μ : MarkedInner} {B : Diagram}, μ.IsLegal → IsConnectedSkew B →
      ∀ x, (content x ≤ minContent (μ.compose B) + μ.period - 1) ↔
        content x ≤ minContent μ.E + minContent B * μ.period + μ.period - 1 := by
    intro μ B hμ hB x
    rw [hμ.minContent_compose hB]
  have ec2 : ∀ {μ : MarkedInner} {B : Diagram}, μ.IsLegal → IsConnectedSkew B →
      ∀ x, (maxContent (μ.compose B) - μ.period + 1 ≤ content x) ↔
        minContent μ.E + maxContent B * μ.period + μ.width ≤ content x := by
    intro μ B hμ hB x
    rw [hμ.maxContent_compose hB]; omega
  have f1 : (ω.compose D).filter (fun x => content x ≤ minContent (ω.compose D) + ω.period - 1) =
      (ω.compose D).filter (fun x =>
        content x ≤ minContent ω.E + minContent D * ω.period + ω.period - 1) :=
    Finset.filter_congr (fun x _ => ec1 h hD x)
  have f1' : (ω'.compose D').filter (fun x =>
      content x ≤ minContent (ω'.compose D') + ω.period - 1) =
      (ω'.compose D').filter (fun x =>
        content x ≤ minContent ω'.E + minContent D' * ω'.period + ω'.period - 1) :=
    Finset.filter_congr (fun x _ => by rw [← hq]; exact ec1 h' hD' x)
  have f2 : (ω.compose D).filter (fun x => maxContent (ω.compose D) - ω.period + 1 ≤ content x) =
      (ω.compose D).filter (fun x =>
        minContent ω.E + maxContent D * ω.period + ω.width ≤ content x) :=
    Finset.filter_congr (fun x _ => ec2 h hD x)
  have f2' : (ω'.compose D').filter (fun x =>
      maxContent (ω'.compose D') - ω.period + 1 ≤ content x) =
      (ω'.compose D').filter (fun x =>
        minContent ω'.E + maxContent D' * ω'.period + ω'.width ≤ content x) :=
    Finset.filter_congr (fun x _ => by rw [← hq]; exact ec2 h' hD' x)
  rw [f1, f1', h.compose_first_window hD, h'.compose_first_window hD',
    SkewGluing.translate_translate]
    at h1
  rw [f2, f2', h.compose_last_window hD, h'.compose_last_window hD',
    SkewGluing.translate_translate]
    at h2
  have tc : ∀ {a b : ℤ × ℤ} {A B : Diagram}, SkewGluing.translate a A = SkewGluing.translate b B →
      B = SkewGluing.translate (-b + a) A := by
    intro a b A B hh
    have : SkewGluing.translate (-b) (SkewGluing.translate b B) = B := by
      rw [SkewGluing.translate_translate]; simp [SkewGluing.translate_zero]
    rw [← this, ← hh, SkewGluing.translate_translate]
  rw [hwn] at h2
  have hs := h.1.span_eq
  have hs' := h'.1.span_eq
  have hws := h.2.2.1.2
  have hs1 := h.diagLo_width_eq_diagHi
  have hs1' := h'.diagLo_width_eq_diagHi
  rw [hw] at hs1'
  have hw0 : 0 ≤ (ω.width : ℤ) := by positivity
  exact eq_translate_of_windows (E := ω.E) (E' := ω'.E) (q := ω.period) (w := (ω.width : ℤ))
    h.1.1 h'.1.1 hs (by rw [hq, hwn] at hs'; exact hs') hw0 hws hs1 hs1'
    (by have := (tc h1).symm; rw [hq] at this; exact this) (tc h2).symm

/-- **`lem:gluing-local` (3) and `lem:gluing-equal`: the span law fixes the width.**  For a legal
mark and a connected outer, the span of `D ∘_ω E` is `r q + w` with `0 ≤ w < q`, so
`w = N_F mod q`. -/
theorem IsLegal.width_eq_span_emod (h : ω.IsLegal) (hD : IsConnectedSkew D) :
    (ω.width : ℤ) = (span (ω.compose D) : ℤ) % ω.period := by
  have hsp := span_compose hD h
  have hq := h.period_pos
  have hwq := h.2.2.1.2
  have hw0 : 0 ≤ (ω.width : ℤ) := by positivity
  rw [hsp, Int.add_comm, Int.add_mul_emod_self_right]
  exact (Int.emod_eq_of_lt hw0 hwq).symm

/-- **`lem:gluing-equal`: the span law fixes the outer span.**  `N_D = N_F / q`. -/
theorem IsLegal.span_outer_eq_div (h : ω.IsLegal) (hD : IsConnectedSkew D) :
    (span D : ℤ) = (span (ω.compose D) : ℤ) / ω.period := by
  have hsp := span_compose hD h
  have hq := h.period_pos
  have hwq := h.2.2.1.2
  have hw0 : 0 ≤ (ω.width : ℤ) := by positivity
  rw [hsp, Int.add_comm, Int.add_mul_ediv_right _ _ hq.ne', Int.ediv_eq_zero_of_lt hw0 hwq]
  simp

/-- Two legal marks of equal period, composed with connected outers into translates of one
diagram, have the same width and the same outer span. -/
theorem IsLegal.width_eq_of_translate (h : ω.IsLegal) (h' : ω'.IsLegal)
    (hD : IsConnectedSkew D) (hD' : IsConnectedSkew D') (hq : ω'.period = ω.period)
    {t : ℤ × ℤ} (hF : ω'.compose D' = SkewGluing.translate t (ω.compose D)) :
    ω'.width = ω.width ∧ span D' = span D := by
  have e := span_translate (D := ω.compose D) t
  rw [← hF] at e
  have w1 := h.width_eq_span_emod hD
  have w2 := h'.width_eq_span_emod hD'
  have d1 := h.span_outer_eq_div hD
  have d2 := h'.span_outer_eq_div hD'
  rw [e, hq] at w2 d2
  constructor
  · have : (ω'.width : ℤ) = ω.width := w2.trans w1.symm
    exact_mod_cast this
  · have : (span D' : ℤ) = span D := by rw [d2, d1]
    exact_mod_cast this

theorem translate_filter_content_le (t : ℤ × ℤ) (A : Diagram) (k : ℤ) :
    SkewGluing.translate t (A.filter fun x => content x ≤ k) =
      (SkewGluing.translate t A).filter fun x => content x ≤ k + content t := by
  ext x
  simp only [mem_translate, Finset.mem_filter, content_sub]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩

theorem translate_filter_content_ge (t : ℤ × ℤ) (A : Diagram) (k : ℤ) :
    SkewGluing.translate t (A.filter fun x => k ≤ content x) =
      (SkewGluing.translate t A).filter fun x => k + content t ≤ content x := by
  ext x
  simp only [mem_translate, Finset.mem_filter, content_sub]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩

/-- Two diagrams that are translates of one diagram are translates of each other. -/
theorem eq_translate_of_translate_eq {a b : ℤ × ℤ} {X Y F : Diagram}
    (hX : F = SkewGluing.translate a X) (hY : F = SkewGluing.translate b Y) :
    Y = SkewGluing.translate (a - b) X := by
  have : SkewGluing.translate (-b) (SkewGluing.translate b Y) = Y := by
    rw [SkewGluing.translate_translate]; simp [SkewGluing.translate_zero]
  rw [← this, ← hY, hX, SkewGluing.translate_translate]
  congr 1
  abel

/-- **`lem:gluing-equal`, the extreme windows of translates.**  If `D' ∘_{ω'} E'` is a translate
of `D ∘_ω E`, the first `q` diagonals and the last `q` diagonals of the two composites are
translates of each other. -/
theorem IsLegal.windows_of_translate (h : ω.IsLegal) (hD : IsConnectedSkew D) {t : ℤ × ℤ}
    (hF : ω'.compose D' = SkewGluing.translate t (ω.compose D)) :
    (SkewGluing.translate t ((ω.compose D).filter fun x =>
        content x ≤ minContent (ω.compose D) + ω.period - 1) =
      (ω'.compose D').filter fun x => content x ≤ minContent (ω'.compose D') + ω.period - 1) ∧
    (SkewGluing.translate t ((ω.compose D).filter fun x =>
        maxContent (ω.compose D) - ω.period + 1 ≤ content x) =
      (ω'.compose D').filter fun x => maxContent (ω'.compose D') - ω.period + 1 ≤ content x) := by
  have hne : (ω.compose D).Nonempty := (h.isConnectedSkew_compose hD).2.1
  rw [hF, minContent_translate hne, maxContent_translate hne]
  rw [translate_filter_content_le, translate_filter_content_ge]
  constructor <;> congr! 2 <;> omega

/-- **`lem:gluing-equal`, structure of two marks of equal period on one parent.**  Let `ω`, `ω'`
be legal marks of the same period and `D`, `D'` connected outers with `D' ∘_{ω'} E'` a translate
of `D ∘_ω E`.  Then `E'` is a translate of `E` (the span law and `lem:gluing-local` (3)), and
either `ω'` is the translate of `ω` by that translation, or the width is positive and the two
marks are the ordinary double: cases (a) and (b), with the displacement of the case-(a) mark the
larger by `e` (`IsLegal.double_cases`).  A mixed mark is never in a double.

**Differs from the paper's route.**  At width zero the paper compares the two edge readings
`v_H`, `v_V` of the empty overlap as two charts; here the empty mark is the single horizontal
datum, so two empty marks are always translates, and the vertical reading enters only through
`fiber_emptyMarks`. -/
theorem IsLegal.equal_periods_cases (h : ω.IsLegal) (h' : ω'.IsLegal)
    (hD : IsConnectedSkew D) (hD' : IsConnectedSkew D') (hq : ω'.period = ω.period)
    {t : ℤ × ℤ} (hF : ω'.compose D' = SkewGluing.translate t (ω.compose D)) :
    ∃ δ : ℤ × ℤ, ω'.E = SkewGluing.translate δ ω.E ∧
      (ω' = ω.translate δ ∨
        (0 < ω.width ∧
          ((ω.case = .a ∧ ω'.case = .b ∧ ω.v = ω'.v + eCell) ∨
            (ω.case = .b ∧ ω'.case = .a ∧ ω'.v = ω.v + eCell)))) := by
  obtain ⟨hw, -⟩ := h.width_eq_of_translate h' hD hD' hq hF
  obtain ⟨w1, w2⟩ := h.windows_of_translate hD hF
  obtain ⟨δ, hδ⟩ := h.exists_translate_of_windows h' hD hD' hq hw w1 w2
  refine ⟨δ, hδ, ?_⟩
  by_cases hW : ω.W = ∅
  · left
    have hw0 : ω.width = 0 := width_eq_zero_of_eq_empty hW
    have hW' : ω'.W = ∅ := by
      by_contra hne
      have := h'.width_pos_of_nonempty (Finset.nonempty_iff_ne_empty.mpr hne)
      omega
    have e1 := (IsLegalEmpty.isEmptyMark ⟨h, hW⟩)
    have e2 := (IsLegalEmpty.isEmptyMark ⟨h', hW'⟩)
    obtain ⟨-, hv1, hc1⟩ := e1
    obtain ⟨-, hv2, hc2⟩ := e2
    obtain ⟨E, W, v, cs⟩ := ω
    obtain ⟨E', W', v', cs'⟩ := ω'
    simp only at hδ hW hW' hv1 hv2 hc1 hc2
    subst hδ hW hW' hc1 hc2 hv1 hv2
    change (⟨SkewGluing.translate δ E, ∅, vH (SkewGluing.translate δ E), .a⟩ : MarkedInner) =
      ⟨SkewGluing.translate δ E, SkewGluing.translate δ ∅, vH E, .a⟩
    rw [vH_translate]
    simp [SkewGluing.translate]
  · have hWn : ω.W.Nonempty := Finset.nonempty_iff_ne_empty.mpr hW
    have hlt : (ω.translate δ).IsLegal := isLegal_translate δ h
    have hWt : (ω.translate δ).W.Nonempty := hWn.image _
    have hW' : ω'.W.Nonempty := by
      by_contra hne
      have hemp : ω'.W = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      have := width_eq_zero_of_eq_empty hemp
      have := h.width_pos_of_nonempty hWn
      omega
    have hwt : ω'.width = (ω.translate δ).width := by
      rw [hw, width_translate]
    rcases hlt.displacement_adjacent h' hWt hW' hδ hwt with a | a | a
    · left
      exact hlt.eq_of_displacement h' hWt hW' hδ a
    · right
      obtain ⟨c1, c2⟩ := hlt.double_cases h' hWt hW' hδ hwt a
      exact ⟨h.width_pos_of_nonempty hWn, Or.inr ⟨c1, c2, a⟩⟩
    · right
      obtain ⟨c1, c2⟩ := h'.double_cases hlt hW' hWt hδ.symm hwt.symm a
      exact ⟨h.width_pos_of_nonempty hWn, Or.inl ⟨c2, c1, a⟩⟩

end MarkedInner

/-! ### The ordinary gauge on fibers -/

/-- **`eq:gluing-gauge`, rotated form.**  The identity also holds after rotating the entire
marked inner. -/
theorem MarkedInner.rotate_compose_antitranspose_gauge {D : Diagram} (hD : D.Nonempty)
    {ωa ωb : MarkedInner} (hE : ωa.E = ωb.E) (ha : ωa.case = .a) (hb : ωb.case = .b)
    (hv : ωa.v = ωb.v + eCell) :
    ωa.rotate.compose D = ωb.rotate.compose (antitranspose D) :=
  MarkedInner.compose_antitranspose_gauge hD (by simp [MarkedInner.rotate, hE])
    (by simp [MarkedInner.rotate, ha, AttachCase.rotate])
    (by simp [MarkedInner.rotate, hb, AttachCase.rotate]) (by simp [MarkedInner.rotate, hv])

/-- **`lem:gluing-equal`, the gauge case on fibers.**  Let `ω_a`, `ω_b` be marked inners on one
diagram of the ordinary cases (a), (b) with `v_a = v_b + e`.  Then `𝓕(ω_a, Q) = 𝓕(ω_b, ι Q)`,
as sets of cells, with no translation needed: `A ∘_{ω_a} E = AT(A) ∘_{ω_b} E` and likewise for
the rotated marked inners, and `s_{AT(A)} = ι(s_A)`.  Equality of outer functions is preserved in
both directions because `ι` is an involution. -/
theorem fiber_gauge {ωa ωb : MarkedInner} (hE : ωa.E = ωb.E) (ha : ωa.case = .a)
    (hb : ωb.case = .b) (hv : ωa.v = ωb.v + eCell) (Q : Lambda) :
    fiber cellSchur ωa Q = fiber cellSchur ωb (schurInvolution Q) := by
  ext F
  constructor
  · rintro ⟨A, hA, hc, hQ, hF⟩
    have hAne := hA.2.1
    refine ⟨antitranspose A, isConnectedSkew_antitranspose hA, by rw [card_antitranspose]; exact hc,
      by rw [cellSchur_antitranspose, hQ], ?_⟩
    rcases hF with rfl | rfl
    · exact Or.inl (MarkedInner.compose_antitranspose_gauge hAne hE ha hb hv)
    · exact Or.inr (MarkedInner.rotate_compose_antitranspose_gauge hAne hE ha hb hv)
  · rintro ⟨A, hA, hc, hQ, hF⟩
    have hA' := isConnectedSkew_antitranspose hA
    have hAne := hA'.2.1
    refine ⟨antitranspose A, hA', by rw [card_antitranspose]; exact hc, ?_, ?_⟩
    · rw [cellSchur_antitranspose, hQ, schurInvolution_involutive Q]
    · rcases hF with rfl | rfl
      · left
        rw [MarkedInner.compose_antitranspose_gauge hAne hE ha hb hv, antitranspose_antitranspose]
      · right
        rw [MarkedInner.rotate_compose_antitranspose_gauge hAne hE ha hb hv,
          antitranspose_antitranspose]

/-- The gauge case of `lem:gluing-equal`, read up to translation. -/
theorem fiberClass_gauge {ωa ωb : MarkedInner} (hE : ωa.E = ωb.E) (ha : ωa.case = .a)
    (hb : ωb.case = .b) (hv : ωa.v = ωb.v + eCell) (Q : Lambda) :
    fiberClass cellSchur ωa Q = fiberClass cellSchur ωb (schurInvolution Q) := by
  unfold fiberClass
  rw [fiber_gauge hE ha hb hv Q]

/-! ### `lem:gluing-equal` -/

/-- **`lem:gluing-equal`, the outer functions of two charts of one parent with equal periods.**
Under the hypotheses of `MarkedInner.IsLegal.equal_periods_cases`: when `ω'` is the translate of
`ω`, fixed-chart injectivity (`MarkedInner.IsLegal.injective_compose`) makes the outers
translates of each other, so `s_{D'} = s_D`; in the ordinary double, `ω_a ∘` and `ω_b ∘` agree
by `eq:gluing-gauge`, fixed-chart injectivity identifies the outer on the `ω_b` side with
`AT` of the one on the `ω_a` side, and `s_{D'} = ι(s_D)` (`s_{AT(D)} = ι(s_D)`, `ι` an
involution). -/
theorem MarkedInner.IsLegal.equal_periods_outer {ω ω' : MarkedInner} {D D' : Diagram}
    (h : ω.IsLegal) (h' : ω'.IsLegal) (hD : IsConnectedSkew D) (hD' : IsConnectedSkew D')
    (hq : ω'.period = ω.period) {t : ℤ × ℤ}
    (hF : ω'.compose D' = SkewGluing.translate t (ω.compose D)) :
    ∃ δ : ℤ × ℤ, ω'.E = SkewGluing.translate δ ω.E ∧
      ((ω' = ω.translate δ ∧ cellSchur D' = cellSchur D) ∨
        (0 < ω.width ∧
          ((ω.case = .a ∧ ω'.case = .b ∧ ω.v = ω'.v + eCell) ∨
            (ω.case = .b ∧ ω'.case = .a ∧ ω'.v = ω.v + eCell)) ∧
          cellSchur D' = schurInvolution (cellSchur D))) := by
  obtain ⟨δ, hδ, hcases⟩ := h.equal_periods_cases h' hD hD' hq hF
  refine ⟨δ, hδ, ?_⟩
  have hlt : (ω.translate δ).IsLegal := MarkedInner.isLegal_translate δ h
  have hFt : ω'.compose D' = SkewGluing.translate (t - δ) ((ω.translate δ).compose D) := by
    rw [hF, MarkedInner.compose_translate, SkewGluing.translate_translate]
    congr 1
    abel
  rcases hcases with rfl | ⟨hw, ⟨ha, hb, hv⟩ | ⟨ha, hb, hv⟩⟩
  · left
    refine ⟨rfl, ?_⟩
    obtain ⟨u, hu⟩ := hlt.injective_compose hD hD' hFt
    rw [hu, cellSchur_translate]
  · right
    refine ⟨hw, Or.inl ⟨ha, hb, hv⟩, ?_⟩
    have hg := MarkedInner.compose_antitranspose_gauge (ωa := ω.translate δ) (ωb := ω')
      hD.2.1 hδ.symm ha hb hv
    have hAT := isConnectedSkew_antitranspose hD
    rw [hg] at hFt
    obtain ⟨u, hu⟩ := h'.injective_compose hAT hD' hFt
    rw [hu, cellSchur_translate, cellSchur_antitranspose]
  · right
    refine ⟨hw, Or.inr ⟨ha, hb, hv⟩, ?_⟩
    have hAT := isConnectedSkew_antitranspose hD'
    have hg := MarkedInner.compose_antitranspose_gauge (ωa := ω') (ωb := ω.translate δ)
      hD'.2.1 hδ hb ha hv
    rw [hg] at hFt
    obtain ⟨u, hu⟩ := hlt.injective_compose hD hAT hFt
    have : cellSchur (antitranspose D') = cellSchur D := by rw [hu, cellSchur_translate]
    rw [cellSchur_antitranspose] at this
    rw [← this, schurInvolution_involutive]

/-- **`lem:gluing-equal`.**  Two proper legal charts of the same parent with equal periods define
the same fiber: `𝓕(ω, s_D)` and `𝓕(ω', s_{D'})`, read up to translation (as the paper reads
diagrams), coincide.  Each fiber contains the compositions through both orientations `ω` and
`ω*`.  In the ordinary double the outer functions differ by `ι` and the fibers are matched by the
gauge `fiber_gauge`; otherwise the marked inners agree up to translation, and the outers are
translates of each other. -/
theorem MarkedInner.IsLegal.equal_periods_same_fiber {ω ω' : MarkedInner} {D D' : Diagram}
    (h : ω.IsLegal) (h' : ω'.IsLegal) (hD : IsConnectedSkew D) (hD' : IsConnectedSkew D')
    (hq : ω'.period = ω.period) {t : ℤ × ℤ}
    (hF : ω'.compose D' = SkewGluing.translate t (ω.compose D)) :
    fiberClass cellSchur ω (cellSchur D) = fiberClass cellSchur ω' (cellSchur D') := by
  obtain ⟨δ, hδ, hcases⟩ := h.equal_periods_outer h' hD hD' hq hF
  have hstep := fiberClass_cellSchur_translate_inner δ ω (cellSchur D)
  rcases hcases with ⟨rfl, hs⟩ | ⟨-, ⟨ha, hb, hv⟩ | ⟨ha, hb, hv⟩, hs⟩
  · rw [hs, ← hstep]
  · rw [← hstep, hs]
    exact fiberClass_gauge (ωa := ω.translate δ) (ωb := ω') hδ.symm ha hb hv _
  · rw [← hstep]
    have := fiberClass_gauge (ωa := ω') (ωb := ω.translate δ) hδ hb ha hv (cellSchur D')
    rw [this, hs, schurInvolution_involutive]

/-- **`lem:gluing-equal`, for charts.**  Two proper legal charts of one parent with equal periods
define the same fiber (up to translation). -/
theorem Chart.IsProperLegal.equal_periods_same_fiber {χ₁ χ₂ : Chart} {F : Diagram}
    (h₁ : χ₁.IsProperLegal) (h₂ : χ₂.IsProperLegal) (hF₁ : χ₁.IsChartOf F)
    (hF₂ : χ₂.IsChartOf F) (hq : χ₁.period = χ₂.period) :
    fiberClass cellSchur χ₁.ω (cellSchur χ₁.D) = fiberClass cellSchur χ₂.ω (cellSchur χ₂.D) := by
  obtain ⟨t₁, ht₁⟩ := hF₁
  obtain ⟨t₂, ht₂⟩ := hF₂
  exact MarkedInner.IsLegal.equal_periods_same_fiber h₁.2.2.2 h₂.2.2.2 h₁.1 h₂.1 hq.symm
    (MarkedInner.eq_translate_of_translate_eq ht₁ ht₂)

/-- **`lem:gluing-equal`, structure for charts.**  Two proper legal charts of one parent with
equal periods have inner diagrams that are translates of each other, and either the marked inners
agree up to that translation (and the outer functions agree), or the width is positive and the
marked inners are the ordinary double of cases (a), (b), with displacements differing by `e`
and outer functions exchanged by `ι`. -/
theorem Chart.IsProperLegal.equal_periods_cases {χ₁ χ₂ : Chart} {F : Diagram}
    (h₁ : χ₁.IsProperLegal) (h₂ : χ₂.IsProperLegal) (hF₁ : χ₁.IsChartOf F)
    (hF₂ : χ₂.IsChartOf F) (hq : χ₁.period = χ₂.period) :
    ∃ δ : ℤ × ℤ, χ₂.ω.E = SkewGluing.translate δ χ₁.ω.E ∧
      ((χ₂.ω = χ₁.ω.translate δ ∧ cellSchur χ₂.D = cellSchur χ₁.D) ∨
        (0 < χ₁.ω.width ∧
          ((χ₁.ω.case = .a ∧ χ₂.ω.case = .b ∧ χ₁.ω.v = χ₂.ω.v + eCell) ∨
            (χ₁.ω.case = .b ∧ χ₂.ω.case = .a ∧ χ₂.ω.v = χ₁.ω.v + eCell)) ∧
          cellSchur χ₂.D = schurInvolution (cellSchur χ₁.D))) := by
  obtain ⟨t₁, ht₁⟩ := hF₁
  obtain ⟨t₂, ht₂⟩ := hF₂
  exact MarkedInner.IsLegal.equal_periods_outer h₁.2.2.2 h₂.2.2.2 h₁.1 h₂.1 hq.symm
    (MarkedInner.eq_translate_of_translate_eq ht₁ ht₂)

/-! ### Width zero -/

/-- **`lem:gluing-equal`, width zero.**  The two edge readings of the empty overlap give the same
fibers up to `ι`: `𝓕(ω_H, Q) = 𝓕(ω_V, ι Q)` as sets of cells, where `ω_H` is the empty mark with
displacement `v_H` (case (a)) and `ω_V` the case-(b) datum with displacement `v_V`; `v_H - v_V = e`
(`vH_eq_vV_add_eCell`).  The vertical reading is not a legal marked inner of this development
(the empty mark is the horizontal one), so it enters only through this identity. -/
theorem fiber_emptyMarks (E : Diagram) (Q : Lambda) :
    fiber cellSchur (emptyMarkH E) Q = fiber cellSchur (emptyMarkV E) (schurInvolution Q) :=
  fiber_gauge (ωa := emptyMarkH E) (ωb := emptyMarkV E) rfl rfl rfl (vH_eq_vV_add_eCell E) Q

/-! ### Fibers are cliques -/

/-- Every member of `𝓕(ω, Q)`, read up to translation, is the parent of a proper legal chart
whose marked inner is `ω` or `ω*` and whose outer has `s_D = Q`. -/
theorem exists_chart_of_mem_fiberClass {ω : MarkedInner} (hω : ω.IsLegal) (hE : 2 ≤ ω.E.card)
    {Q : Lambda} {F : Diagram} (hF : F ∈ fiberClass cellSchur ω Q) :
    ∃ χ : Chart, χ.IsProperLegal ∧ χ.IsChartOf F ∧ (χ.ω = ω ∨ χ.ω = ω.rotate) ∧
      cellSchur χ.D = Q := by
  obtain ⟨F', ⟨A, hA, hc, hQ, hF'⟩, t, rfl⟩ := hF
  rcases hF' with rfl | rfl
  · exact ⟨⟨A, ω⟩, ⟨hA, hc, hE, hω⟩, ⟨t, rfl⟩, Or.inl rfl, hQ⟩
  · refine ⟨⟨A, ω.rotate⟩, ⟨hA, hc, ?_, MarkedInner.isLegal_rotate hω⟩, ⟨t, rfl⟩,
      Or.inr rfl, hQ⟩
    change 2 ≤ (SkewGluing.rotate ω.E).card
    rw [SkewGluing.rotate, Finset.card_image_of_injective _ neg_injective]
    exact hE

/-- **Fibers are cliques (the part of `def:gluing-graph` that needs no Olson-Harris input).**
Two members of one fiber `𝓕(ω, Q)` of a legal marked inner with `|E| ≥ 2`, which are not
translates of one another, have a common final factor in the sense of `HasCommonFinalFactor`:
their proper charts `(A_i, ω)` or `(A_i, ω*)` have the same marked inner up to transported
rotation, and `s_{A_1} = Q = s_{A_2}`.  That the whole fiber lies in one Schur class is the
separate Olson-Harris input and is not used here. -/
theorem fiberClass_hasCommonFinalFactor {ω : MarkedInner} (hω : ω.IsLegal)
    (hE : 2 ≤ ω.E.card) {Q : Lambda} {F₁ F₂ : Diagram} (h₁ : F₁ ∈ fiberClass cellSchur ω Q)
    (h₂ : F₂ ∈ fiberClass cellSchur ω Q) (hne : ¬ ∃ t, F₂ = SkewGluing.translate t F₁) :
    HasCommonFinalFactor cellSchur F₁ F₂ := by
  obtain ⟨χ₁, p₁, c₁, o₁, s₁⟩ := exists_chart_of_mem_fiberClass hω hE h₁
  obtain ⟨χ₂, p₂, c₂, o₂, s₂⟩ := exists_chart_of_mem_fiberClass hω hE h₂
  refine ⟨hne, χ₁, χ₂, p₁, p₂, c₁, c₂, ?_, s₁.trans s₂.symm⟩
  have rfl_equiv : ∀ ν : MarkedInner, ν.EquivTranslate ν := fun ν =>
    ⟨0, by rw [← MarkedInner.translate_eq_translateBy, MarkedInner.translate_zero]⟩
  have rot_equiv : ∀ ν : MarkedInner, ν.rotate.rotate.EquivTranslate ν := fun ν => by
    rw [MarkedInner.rotate_rotate]; exact rfl_equiv ν
  have key : ∀ a b : MarkedInner, (a = ω ∨ a = ω.rotate) → (b = ω ∨ b = ω.rotate) →
      a.EquivTranslate b ∨ a.rotate.EquivTranslate b := by
    rintro a b (rfl | rfl) (rfl | rfl)
    · exact Or.inl (rfl_equiv _)
    · exact Or.inr (rfl_equiv _)
    · exact Or.inr (rot_equiv _)
    · exact Or.inl (rfl_equiv _)
  exact key _ _ o₁ o₂

/-! ### Checked examples -/

section Examples

open MarkedInner

/-- The gauge double of the worked example: both marks are legal, of period `q`, with
`v_a = v_b + e`. -/
example : gaugeInnerA.IsLegal ∧ gaugeInnerB.IsLegal := by
  exact ⟨by decide +kernel, by decide +kernel⟩

example : gaugeInnerA.period = gaugeInnerB.period := by decide

/-- `lem:gluing-equal` on the worked gauge example: the charts `((2), ω_a)` and
`(AT (2), ω_b)` of the same parent have the same fiber. -/
example : fiberClass cellSchur gaugeInnerA (cellSchur (skewOf [2] [])) =
    fiberClass cellSchur gaugeInnerB (cellSchur (antitranspose (skewOf [2] []))) :=
  MarkedInner.IsLegal.equal_periods_same_fiber (t := 0) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (isConnectedSkew_antitranspose (by decide +kernel)) (by decide)
    (by rw [translate_zero]; decide +kernel)

/-- The span law on the chart figure: `N_F = 8`, `q = 3`, `w = 8 mod 3 = 2`. -/
example : (chartFigureInner.width : ℤ) =
    (span (compose domino chartFigureInner) : ℤ) % chartFigureInner.period := by
  decide +kernel

/-- The two displacements of the gauge example differ by `e`, the larger one carrying case (a). -/
example : gaugeInnerA.v = gaugeInnerB.v + eCell := by decide

end Examples

end SkewGluing
