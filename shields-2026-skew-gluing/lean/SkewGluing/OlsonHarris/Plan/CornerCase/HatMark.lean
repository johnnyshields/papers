import SkewGluing.OlsonHarris.Plan.CornerCase.Combinatorics

/-!
# The hatted mark of a corner mark is skew

Formalizes `shields-2026-skew-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `eq:gluing-offsets`) and «Diagonal geometry» (`lem:gluing-local`): thesis
Remark 5.3.7 (`OlsonHarris2024HopfApplications`) for a legal mark of case (c).

Both copies of the mark are northwest-justified (`lem:gluing-local` (2)), so the hatted mark
`\overline W = {x ∈ 𝐄 : x + e ∈ W₋} ∪ {x ∈ W₋ : x + e ∈ 𝐄}` is the set of the cells of `W₋` whose
southeast neighbor lies in `𝐄` (`hatMarkFin_eq`), and this set is skew because only the copies
`E` and `E - v` of `E` meet the diagonals of `W₋`.

Sorry-free.
-/

namespace SkewGluing

namespace Plan

namespace Corner

open MarkedInner

/-- A cell of the periodic window on a diagonal of the mark lies in `E` or in `E - v`. -/
theorem mem_periodicWindow_cases {ω : MarkedInner} (hω : ω.IsLegal) (hc : ω.case = .c)
    {y z : ℤ × ℤ} (hy : y ∈ ω.W) (hzc : content z = content y) (hz : z ∈ periodicWindow ω) :
    z ∈ ω.E ∨ z + ω.v ∈ ω.E := by
  have hnon := isNonemptyMark_of_case_c hω hc
  have hb := hnon.content_bounds hω.1.1
  have hyb := (hb.1 y hy)
  have hwq : (ω.width : ℤ) < ω.period := hω.2.2.1.2
  unfold periodicWindow at hz
  obtain ⟨k, hk, hzk⟩ := Finset.mem_biUnion.mp hz
  rw [Finset.mem_Icc] at hk
  have hzE : z - k • ω.v ∈ ω.E := mem_translate.mp hzk
  have hcz := (hb.2 _ hzE)
  rw [content_sub, content_smul, hzc] at hcz
  have hq : ω.period = content ω.v := rfl
  have h1 : k * content ω.v < content ω.v := by nlinarith
  have h2 : -(k * content ω.v) < 2 * content ω.v := by nlinarith
  have hk1 : k ≤ 0 := by
    by_contra hh
    have : 1 ≤ k := by omega
    nlinarith
  have hk2 : -1 ≤ k := by
    by_contra hh
    have : k ≤ -2 := by omega
    nlinarith
  have : k = 0 ∨ k = -1 := by omega
  rcases this with rfl | rfl
  · left; simpa using hzE
  · right; simpa using hzE

/-- Both copies are northwest-justified, so if `y ∈ W₋` and `y - e` lies in the periodic window
then `y - e ∈ W₋`. -/
theorem sub_eCell_mem_W {ω : MarkedInner} (hω : ω.IsLegal) (hc : ω.case = .c) {y : ℤ × ℤ}
    (hy : y ∈ ω.W) (hxP : y - eCell ∈ periodicWindow ω) : y - eCell ∈ ω.W := by
  have hW : ω.W.Nonempty := (isNonemptyMark_of_case_c hω hc).1
  have hl : ω.IsLegalNonempty := ⟨hω, hW⟩
  have hnon := isNonemptyMark_of_case_c hω hc
  have hb := hnon.content_bounds hω.1.1
  have hnw := hl.nwJustified hc
  have hWc := isConnectedSkew_iff_diagonal.mp hnon.2.1
  have hUc : HasDiagonalShape ω.upper :=
    isConnectedSkew_iff_diagonal.mp (isConnectedSkew_translate ω.v hnon.2.1)
  have hyb := hb.1 y hy
  obtain ⟨hn1, hn2⟩ := hnw (content y - minContent ω.E) (by omega)
    (by unfold MarkedInner.widthZ; omega)
  have e1 : minContent ω.E + (content y - minContent ω.E) = content y := by ring
  have e2 : minContent ω.E + (content y - minContent ω.E + ω.period) = content y + ω.period := by
    ring
  rw [e1] at hn1
  rw [e2] at hn2
  have hzc : content (y - eCell) = content y := by simp [content, eCell]
  have hzcell : y - eCell = ((y - eCell).1, (y - eCell).1 + content y) :=
    Prod.ext rfl (by simp only [Prod.snd_sub, Prod.fst_sub, content, eCell]; ring)
  have hyr : y.1 ≤ diagHi ω.W (content y) := le_diagHi hy rfl
  rcases mem_periodicWindow_cases hω hc hy hzc hxP with hzE | hzE
  · have hlo : diagLo ω.E (content y) ≤ (y - eCell).1 := diagLo_le hzE (by rw [← hzc]; rfl)
    rw [hzcell]
    exact hWc.mem_iff.mpr ⟨content_mem_contents hy, by omega, by simp [eCell] at hyr ⊢; omega⟩
  · have hyU : y + ω.v ∈ ω.upper := by
      unfold MarkedInner.upper; exact mem_translate.mpr (by simpa using hy)
    have hcv : content ω.v = ω.period := rfl
    have hzc2 : content (y - eCell + ω.v) = content y + ω.period := by
      rw [content_add, hzc, hcv]
    have hyc2 : content (y + ω.v) = content y + ω.period := by rw [content_add, hcv]
    have hlo : diagLo ω.E (content y + ω.period) ≤ (y - eCell + ω.v).1 :=
      diagLo_le hzE (by rw [← hzc2]; rfl)
    have hup : (y + ω.v).1 ≤ diagHi ω.upper (content y + ω.period) :=
      le_diagHi hyU (by rw [← hyc2]; rfl)
    have hcU : content y + ω.period ∈ contents ω.upper := by
      rw [← hyc2]; exact content_mem_contents hyU
    have hzcell2 : y - eCell + ω.v =
        ((y - eCell + ω.v).1, (y - eCell + ω.v).1 + (content y + ω.period)) := by
      rw [← hzc2]
      exact Prod.ext rfl (by simp only [content]; ring)
    simp only [Prod.fst_add, Prod.fst_sub, eCell] at hlo hup
    have hmem : y - eCell + ω.v ∈ ω.upper := by
      rw [hzcell2]
      refine hUc.mem_iff.mpr ⟨hcU, ?_, ?_⟩
      · simp only [Prod.fst_add, Prod.fst_sub, eCell]; omega
      · simp only [Prod.fst_add, Prod.fst_sub, eCell]; omega
    have := mem_translate.mp hmem
    simpa using this

/-- For a legal mark of case (c), the hatted mark is the set of the cells of `W₋` whose
southeast neighbor lies in the periodic window. -/
theorem hatMarkFin_eq {ω : MarkedInner} (hω : ω.IsLegal) (hc : ω.case = .c) :
    hatMarkFin ω = ω.W.filter fun x => x + eCell ∈ periodicWindow ω := by
  have hnon := isNonemptyMark_of_case_c hω hc
  have hEP : ∀ x ∈ ω.E, x ∈ periodicWindow ω := by
    intro x hx
    unfold periodicWindow
    refine Finset.mem_biUnion.mpr ⟨0, by simp, ?_⟩
    simpa [translate_zero] using hx
  ext x
  constructor
  · intro hx
    unfold hatMarkFin at hx
    rcases Finset.mem_union.mp hx with h | h
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp h).1
      have hxP : y - eCell ∈ periodicWindow ω := (Finset.mem_filter.mp h).2.2
      refine Finset.mem_filter.mpr ⟨sub_eCell_mem_W hω hc hy hxP, ?_⟩
      have : y ∈ ω.E := hnon.2.2.1 hy
      simpa using hEP y this
    · exact h
  · intro hx
    unfold hatMarkFin
    exact Finset.mem_union_right _ hx

/-- **Thesis Remark 5.3.7, the hatted mark.**  For a legal mark of case (c), the hatted mark
`\overline W` is a skew diagram: it is the set of the cells `x` of `W₋` with `x + e` in the
periodic window (`hatMarkFin_eq`), and a cell of the window on a diagonal of the mark lies in `E`
or in `E - v` (`mem_periodicWindow_cases`), so the convexity of `E` carries `x + e` to every cell
of a rectangle of `W₋`. -/
theorem isSkew_hatMarkFin {ω : MarkedInner} (hω : ω.IsLegal) (hc : ω.case = .c) :
    IsSkew (hatMarkFin ω) := by
  have hnon := isNonemptyMark_of_case_c hω hc
  have hE : IsSkew ω.E := hω.1.1.1
  have hWs : IsSkew ω.W := hnon.2.1.1
  rw [hatMarkFin_eq hω hc]
  intro x hx y hy h1 h2 i hi j hj
  rw [Finset.mem_filter] at hx hy ⊢
  simp only [Finset.mem_Icc] at hi hj
  have hij : (i, j) ∈ ω.W := hWs.mem (a := x.1) (b := x.2) (c := y.1) (d := y.2) hx.1 hy.1
    h1 h2 hi.1 hi.2 hj.1 hj.2
  refine ⟨hij, ?_⟩
  have hzc : content (y + eCell) = content y := content_eCell_add y
  have hP : ∀ k : ℤ, k ∈ Finset.Icc (-2 : ℤ) 2 → (i, j) + eCell - k • ω.v ∈ ω.E →
      (i, j) + eCell ∈ periodicWindow ω := by
    intro k hk hmem
    exact Finset.mem_biUnion.mpr ⟨k, hk, mem_translate.mpr hmem⟩
  rcases mem_periodicWindow_cases hω hc hy.1 hzc hy.2 with hyE | hyE
  · refine hP 0 (by simp) ?_
    have hijE : (i, j) ∈ ω.E := hnon.2.2.1 hij
    have hyE2 : (y.1 + 1, y.2 + 1) ∈ ω.E := hyE
    have : ((i + 1, j + 1) : ℤ × ℤ) ∈ ω.E :=
      hE.mem (a := i) (b := j) (c := y.1 + 1) (d := y.2 + 1) hijE hyE2
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    simpa [eCell] using this
  · refine hP (-1) (by simp) ?_
    have hijU : (i, j) + ω.v ∈ ω.E := by
      have : (i, j) + ω.v ∈ ω.upper := by
        unfold MarkedInner.upper; exact mem_translate.mpr (by simpa using hij)
      exact hnon.2.2.2.1 this
    have hijU' : (i + ω.v.1, j + ω.v.2) ∈ ω.E := hijU
    have hyE' : (y.1 + 1 + ω.v.1, y.2 + 1 + ω.v.2) ∈ ω.E := hyE
    have h3 : (i + 1 + ω.v.1, j + 1 + ω.v.2) ∈ ω.E :=
      hE.mem (a := i + ω.v.1) (b := j + ω.v.2) (c := y.1 + 1 + ω.v.1) (d := y.2 + 1 + ω.v.2)
        hijU' hyE' (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega)
    have e : (i, j) + eCell - (-1 : ℤ) • ω.v = (i + 1 + ω.v.1, j + 1 + ω.v.2) := by
      ext <;> simp [eCell]
    rw [e]
    exact h3

end Corner

end Plan

end SkewGluing
