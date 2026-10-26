import SkewBase.SearchesComplete
import SkewBase.Copied.TranslateInner
import SkewBase.Copied.OuterTranslate

/-!
# Normalized position of a chart

Formalizes `shields-2026-skew-base-computational.tex`, «The geometry of a chart and two complete
searches» (`sec:roots`): the convention "translate so that the least contents of `D`, `E` and
`F` are `0`", used in `lem:copies`, `lem:bands`, `cor:outer` and `thm:searches`.

A chart `(D, ω)` is in *normalized position* when `sw D = (0, 0)` and `sw E = (0, 0)`.  Then its
composite has `sw F = (0, 0)` (`sw_compose_of_sw_zero`).  Every proper chart of a diagram `F` has
a normalized representative whose composite is `normalize F` (`exists_normalized_chart`), obtained
by translating the outer (`compose_translate_outer`) and the inner (`compose_translate_inner`).

Sorry-free.
-/

namespace SkewBase

open SkewGluing

/-- **Composition with a translated marked inner.**  Translating the inner translates the
composite by the same vector. -/
theorem compose_translate_inner (u : ℤ × ℤ) {D : Diagram} (hD : D.Nonempty) (ω : MarkedInner) :
    (ω.translate u).compose D = translate u (ω.compose D) := by
  ext x
  rw [MarkedInner.mem_compose hD, mem_translate, MarkedInner.mem_compose hD]
  apply or_congr
  · refine exists_congr fun d => and_congr_right fun _ => ?_
    have ho : (ω.translate u).origin D d = ω.origin D d := rfl
    rw [ho, mem_translate, mem_translate, MarkedInner.translate_E, mem_translate, sub_right_comm]
  · refine exists_congr fun d => and_congr_right fun _ => and_congr Iff.rfl ?_
    have ho : (ω.translate u).origin D d = ω.origin D d := rfl
    have hs : (ω.translate u).supplementalShift = ω.supplementalShift := rfl
    rw [ho, hs, mem_translate, mem_translate, MarkedInner.upper_translate, mem_translate,
      sub_right_comm]

/-- The composite of a chart in normalized position has `sw F = (0, 0)`. -/
theorem sw_compose_of_sw_zero {ω : MarkedInner} (hω : ω.IsLegal) {D : Diagram}
    (hD : IsConnectedSkew D) (hswD : sw D = 0) (hswE : sw ω.E = 0) :
    sw (ω.compose D) = 0 := by
  have hE0 := (sw_zero_facts hω.1.1 hswE).1
  obtain ⟨hD0, hlo, hhi⟩ := sw_zero_facts hD hswD
  have hq := period_pos hω
  have hsub := E_subset_compose (ω := ω) hD hswD
  have h00 : ((0 : ℤ), (0 : ℤ)) ∈ ω.compose D := by
    apply hsub
    have := sw_mem hω.1.1.2.1
    rw [hswE] at this
    exact this
  have hnonneg : ∀ x ∈ ω.compose D, 0 ≤ content x := by
    intro x hx
    rcases (MarkedInner.mem_compose hD.2.1).mp hx with ⟨d, hd, hxd⟩ | ⟨d, hd, -, hxd⟩
    · have h := content_mem_copy hω hE0 D d hxd
      have : 0 ≤ content d := hD0 ▸ minContent_le (content_mem_contents hd)
      nlinarith [h.1]
    · have h := content_mem_supplemental hω hE0 D d hxd
      have : 0 ≤ content d := hD0 ▸ minContent_le (content_mem_contents hd)
      nlinarith [h.1]
  have hc0 : (0 : ℤ) ∈ contents (ω.compose D) := mem_contents_iff.mpr ⟨0, by simpa using h00⟩
  have hmin : minContent (ω.compose D) = 0 := by
    apply minContent_eq_of hc0
    intro k hk
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hk
    exact hnonneg x hx
  have hlow : diagLo (ω.compose D) 0 = 0 := by
    apply diagLo_eq_of (by simpa using h00)
    intro i hi
    have hxc : content (i, i + 0) < ω.period := by simp [content]; omega
    have := (mem_compose_lower_iff hω hE0 hD hswD hxc).mp hi
    have h2 := MarkedInner.eq_sw_of_content hω.1.1 this (by simp [content, hE0])
    rw [hswE] at h2
    have := congrArg Prod.fst h2
    simp only [Prod.fst_zero] at this
    omega
  simp only [sw, hmin, hlow]
  rfl

theorem sw_translate_cancel {X : Diagram} (hX : X.Nonempty) (v : ℤ × ℤ) (h : v = -sw X) :
    sw (translate v X) = 0 := by
  rw [sw_translate hX, h]; abel

/-- **Normalized representative.**  Every proper chart of `F` is, after translating the outer by
`-sw D` and the inner by `-sw E`, a proper chart of `normalize F` in normalized position. -/
theorem exists_normalized_chart {χ : Chart} (h : χ.IsProperLegal) {F : Diagram}
    (hF : χ.IsChartOf F) :
    ∃ χ' : Chart, χ'.IsProperLegal ∧ χ'.parent = normalize F ∧ sw χ'.D = 0 ∧ sw χ'.ω.E = 0 ∧
      χ'.D = normalize χ.D ∧ χ'.ω = χ.ω.translate (-sw χ.ω.E) := by
  obtain ⟨D, ω⟩ := χ
  obtain ⟨hD, hD2, hE2, hω⟩ := h
  obtain ⟨t, rfl⟩ := hF
  change IsConnectedSkew D at hD
  change 2 ≤ D.card at hD2
  change 2 ≤ ω.E.card at hE2
  change ω.IsLegal at hω
  have hDne : D.Nonempty := hD.2.1
  have hEne : ω.E.Nonempty := hω.1.1.2.1
  have hD' : IsConnectedSkew (normalize D) := isConnectedSkew_normalize hD
  have hω' : (ω.translate (-sw ω.E)).IsLegal := MarkedInner.isLegal_translate _ hω
  have hswD : sw (normalize D) = 0 := sw_translate_cancel hDne _ rfl
  have hswE : sw (ω.translate (-sw ω.E)).E = 0 := sw_translate_cancel hEne _ rfl
  have hcardD : (normalize D).card = D.card :=
    Finset.card_image_of_injective _ (add_left_injective _)
  have hcardE : (translate (-sw ω.E) ω.E).card = ω.E.card :=
    Finset.card_image_of_injective _ (add_left_injective _)
  refine ⟨⟨normalize D, ω.translate (-sw ω.E)⟩, ⟨hD', by simpa [hcardD] using hD2,
    by change 2 ≤ (translate (-sw ω.E) ω.E).card; rw [hcardE]; exact hE2, hω'⟩, ?_, hswD, hswE,
    rfl, rfl⟩
  have hsw := sw_compose_of_sw_zero hω' hD' hswD hswE
  have hcne : (ω.compose D).Nonempty := by
    obtain ⟨x, hx⟩ := hEne
    exact ⟨x + ω.origin D (sw D), (MarkedInner.mem_compose hDne).mpr
      (Or.inl ⟨sw D, sw_mem hDne, mem_translate.mpr (by simpa using hx)⟩)⟩
  have hs : (ω.translate (-sw ω.E)).compose (normalize D) =
      translate (-sw ω.E + ω.outerShift (-sw D)) (ω.compose D) := by
    unfold normalize
    rw [compose_translate_inner (-sw ω.E) (D := translate (-sw D) D) (hDne.image _) ω,
      MarkedInner.compose_translate_outer _ hDne, translate_translate]
  change (ω.translate (-sw ω.E)).compose (normalize D) = normalize (translate t (ω.compose D))
  calc (ω.translate (-sw ω.E)).compose (normalize D)
      = normalize ((ω.translate (-sw ω.E)).compose (normalize D)) :=
        (normalize_of_sw_zero hsw).symm
    _ = normalize (ω.compose D) := by rw [hs, normalize_translate hcne]
    _ = normalize (translate t (ω.compose D)) := (normalize_translate hcne t).symm

/-! ### Search S and search B return exactly the normalized proper charts -/

/-- The proper charts of `F` in normalized position: `sw D = (0, 0)` and `sw E = (0, 0)`. -/
def NormalizedProperCharts (F : Diagram) : Set Chart :=
  {χ | χ.IsProperLegal ∧ χ.parent = F ∧ sw χ.D = 0 ∧ sw χ.ω.E = 0}

theorem sw_normalize {X : Diagram} (hX : X.Nonempty) : sw (normalize X) = 0 :=
  sw_translate_cancel hX _ rfl

/-- A diagram containing `(0, 0)`, with no cell of negative content and no other cell of
content `0`, has `sw = (0, 0)`. -/
theorem sw_eq_zero_of_least {X : Diagram} (h0 : ((0 : ℤ), (0 : ℤ)) ∈ X)
    (hnn : ∀ x ∈ X, 0 ≤ content x) (hu : ∀ x ∈ X, content x = 0 → x = (0, 0)) : sw X = 0 := by
  have hc0 : (0 : ℤ) ∈ contents X := mem_contents_iff.mpr ⟨0, by simpa using h0⟩
  have hmin : minContent X = 0 := by
    apply minContent_eq_of hc0
    intro k hk
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hk
    exact hnn x hx
  have hlow : diagLo X 0 = 0 := by
    apply diagLo_eq_of (by simpa using h0)
    intro i hi
    have := congrArg Prod.fst (hu _ hi (by simp [content]))
    simp only at this
    omega
  simp only [sw, hmin, hlow]
  rfl

/-- The outer generated by `lem:heights` has `sw D = (0, 0)`. -/
theorem sw_of_mem_heightCandidates {F : Diagram} {q w N : ℤ} {D : Diagram}
    (h : D ∈ heightCandidates F q w N) (hN : 0 < N) : sw D = 0 := by
  obtain ⟨-, α, hα0, hh0, -, rfl⟩ := h
  exact sw_diagramOfRows (by omega) hα0 (by simp [hα0, hh0])

theorem sw_corOuterA {F : Diagram} {q w N v₁ : ℤ} (hN : 0 < N) :
    sw (corOuterA F q w N v₁) = 0 := by
  unfold corOuterA
  exact sw_diagramOfRows (by omega) (by simp [privateRow]) (by simp [privateRow, privateHeight])

theorem sw_corOuterB {F : Diagram} {q w N v₁ : ℤ} (hN : 0 < N) :
    sw (corOuterB F q w N v₁) = 0 := by
  unfold corOuterB
  exact sw_diagramOfRows (by omega) (by simp [privateRow, privateHeight])
    (by simp [privateRow])

/-- **Search S returns exactly the proper charts of `F`** (`thm:searches`), in normalized
position. -/
theorem searchS_eq (F : Diagram) : SearchS F = NormalizedProperCharts F := by
  ext χ
  constructor
  · intro h
    obtain ⟨hpl, hP⟩ := searchS_sound h
    obtain ⟨⟨S, -, -, hS2, hE⟩, -, -, h2, -, hD, -⟩ := h
    refine ⟨hpl, hP, sw_of_mem_heightCandidates hD (by omega), ?_⟩
    rw [hE]
    exact sw_normalize (Finset.card_pos.mp (by omega))
  · rintro ⟨hpl, hP, hswD, hswE⟩
    exact searchS_complete hpl hP hswD hswE

/-- The inner formed from the bands of a connected `F` with `sw F = (0, 0)` has
`sw E = (0, 0)`. -/
theorem sw_bandInner {F : Diagram} (hF : IsConnectedSkew F) (hsw : sw F = 0) {q : ℤ}
    (hq : 2 ≤ q) (hag : BandsAgree F q) : sw (bandInner F q) = 0 := by
  obtain ⟨hmin, hlo, hhi⟩ := sw_zero_facts hF hsw
  have hw0 : 0 ≤ (span F : ℤ) % q := Int.emod_nonneg _ (by omega)
  have h00 : ((0 : ℤ), (0 : ℤ)) ∈ F := by
    have := sw_mem hF.2.1
    rwa [hsw] at this
  have hbot : ∀ x ∈ bottomBand F q, 0 ≤ content x ∧ x ∈ F := fun x hx => by
    simp only [bottomBand, Finset.mem_filter] at hx
    exact ⟨hx.2.1, hx.1⟩
  have hF0 : ∀ x ∈ F, content x = 0 → x = (0, 0) := fun x hx hc => by
    have := MarkedInner.eq_sw_of_content hF hx (by rw [hmin]; exact hc)
    rwa [hsw] at this
  apply sw_eq_zero_of_least
  · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨h00, by simp [content]; omega⟩)
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (hbot x hx).1
    · unfold topBand at hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      simp only [Finset.mem_filter] at hy
      rw [content_add]
      have hc1 : content (leastCell F ((span F : ℤ) % q)) = (span F : ℤ) % q := by
        simp [leastCell, content]
      have hc2 : content (leastCell F ((span F : ℤ) - q)) = (span F : ℤ) - q := by
        simp [leastCell, content]
      have : content (leastCell F ((span F : ℤ) % q) - leastCell F ((span F : ℤ) - q)) =
          (span F : ℤ) % q - ((span F : ℤ) - q) := by
        rw [MarkedInner.content_sub, hc1, hc2]
      omega
  · intro x hx hc
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hF0 x (hbot x hx).2 hc
    · have hx' := hx
      unfold topBand at hx'
      obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hx'
      simp only [Finset.mem_filter] at hy
      have hc1 : content (leastCell F ((span F : ℤ) % q)) = (span F : ℤ) % q := by
        simp [leastCell, content]
      have hc2 : content (leastCell F ((span F : ℤ) - q)) = (span F : ℤ) - q := by
        simp [leastCell, content]
      have hcu : content (leastCell F ((span F : ℤ) % q) - leastCell F ((span F : ℤ) - q)) =
          (span F : ℤ) % q - ((span F : ℤ) - q) := by
        rw [MarkedInner.content_sub, hc1, hc2]
      have hcx : content x = content y +
          content (leastCell F ((span F : ℤ) % q) - leastCell F ((span F : ℤ) - q)) := by
        rw [← hyx, content_add]
      have hw : (span F : ℤ) % q = 0 := by omega
      have hmem := (hag x (by omega) (by omega)).mpr hx
      exact hF0 _ (hbot _ hmem).2 hc

/-- **Search B returns exactly the proper charts of `F`** (`thm:searches`), in normalized
position. -/
theorem searchB_eq {F : Diagram} (hF : IsConnectedSkew F) (hsw : sw F = 0) :
    SearchB F = NormalizedProperCharts F := by
  ext χ
  constructor
  · intro h
    obtain ⟨hpl, hP⟩ := searchB_sound h
    obtain ⟨q, hq2, hq, hq', hag1, hag2, hag, hE, hEc, hω, hout, hD, hP'⟩ := h
    have hN : 0 < (span F : ℤ) / q := by
      have := (Int.le_ediv_iff_mul_le (by omega : 0 < q)).mpr (by omega : 2 * q ≤ span F)
      omega
    refine ⟨hpl, hP, ?_, ?_⟩
    · unfold SearchBOuter at hout
      cases hc : χ.ω.case <;> rw [hc] at hout
      · rw [hout]; exact sw_corOuterA hN
      · rw [hout]; exact sw_corOuterB hN
      · exact sw_of_mem_heightCandidates hout.2 hN
      · exact sw_of_mem_heightCandidates hout.2 hN
    · rw [hE]; exact sw_bandInner hF hsw hq2 hag
  · rintro ⟨hpl, hP, hswD, hswE⟩
    exact searchB_complete hpl hP hswD hswE

/-- **`thm:searches`, completeness up to translation, search S.**  Every proper chart of a
diagram `F` has a translate (of the outer by `-sw D`, of the inner by `-sw E`) returned by
search S on `normalize F`. -/
theorem exists_searchS_of_isChartOf {χ : Chart} (h : χ.IsProperLegal) {F : Diagram}
    (hF : χ.IsChartOf F) :
    ∃ χ' ∈ SearchS (normalize F), χ'.D = normalize χ.D ∧
      χ'.ω = χ.ω.translate (-sw χ.ω.E) := by
  obtain ⟨χ', hpl, hP, hswD, hswE, hD, hω⟩ := exists_normalized_chart h hF
  exact ⟨χ', searchS_complete hpl hP hswD hswE, hD, hω⟩

/-- **`thm:searches`, completeness up to translation, search B.** -/
theorem exists_searchB_of_isChartOf {χ : Chart} (h : χ.IsProperLegal) {F : Diagram}
    (hF : χ.IsChartOf F) :
    ∃ χ' ∈ SearchB (normalize F), χ'.D = normalize χ.D ∧
      χ'.ω = χ.ω.translate (-sw χ.ω.E) := by
  obtain ⟨χ', hpl, hP, hswD, hswE, hD, hω⟩ := exists_normalized_chart h hF
  exact ⟨χ', searchB_complete hpl hP hswD hswE, hD, hω⟩

end SkewBase
