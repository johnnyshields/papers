import SkewGluing.OlsonHarris.Plan.CornerCase.Crem.Compose

/-!
# The hatted shapes of a case-(c) mark on the diagonals of `E`

Formalizes `shields-2026-skew-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `eq:gluing-offsets`, `def:gluing-graph`): thesis §5.3.1 and §5.5
(`OlsonHarris2024HopfApplications`).

For a legal mark of case (c) with phases `s`, `t`, the shapes `W`, `\overline W` and
`\overline O` have the rows `[ℓ_a, h_a - [s ≤ a]]`, `[ℓ_a, h_a - [t ≤ a]]` on the diagonals
`0 ≤ a < w`, and `[ℓ_a, h_a - 1]` on the diagonals `w ≤ a < q` (`mem_hatMarkFin_cell`,
`mem_hatMiddleFin_cell`).

Sorry-free.
-/

namespace SkewGluing

namespace Plan

namespace Corner

namespace Rem

open MarkedInner

variable {ω : MarkedInner}

theorem mem_hatMiddleFin_cell (h : ω.IsLegalNonempty) {a r : ℤ} :
    ω.cell a r ∈ hatMiddleFin ω ↔
      ω.widthZ ≤ a ∧ a < ω.period ∧ ω.lo a ≤ r ∧ r + 1 ≤ ω.hi a := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  unfold hatMiddleFin
  rw [Finset.mem_filter, cell_add_e]
  constructor
  · rintro ⟨hx, hx'⟩
    have hEx := (h.mem_middle.mp hx).1
    have hEy := (h.mem_middle.mp hx').1
    rw [h.mem_E] at hEx hEy
    have haw : ω.widthZ ≤ a := by
      by_contra hlt
      have := h.middle_thin hx hx' (by simp [cell, content])
        (Or.inl (by rw [content_cell]; omega))
      have := (cell_inj ω this).2
      omega
    have haq : a < ω.period := by
      by_contra hlt
      have := h.middle_thin hx hx' (by simp [cell, content])
        (Or.inr (by rw [content_cell]; omega))
      have := (cell_inj ω this).2
      omega
    exact ⟨haw, haq, hEx.2.2.1, hEy.2.2.2⟩
  · rintro ⟨h1, h2, h3, h4⟩
    have hlh := h.lo_le_hi (a := a) (by omega) (by omega)
    have hnW : ∀ r', ω.cell a r' ∉ ω.W := by
      intro r' hr
      rw [h.mem_W] at hr
      omega
    refine ⟨?_, ?_⟩
    · rw [h.mem_middle_lt h2]
      exact ⟨h.mem_E.mpr ⟨by omega, by omega, h3, by omega⟩, hnW r⟩
    · rw [h.mem_middle_lt h2]
      exact ⟨h.mem_E.mpr ⟨by omega, by omega, by omega, h4⟩, hnW (r + 1)⟩

/-- A cell of the periodic window on a diagonal of the mark lies in `E` or in `E - v`. -/
theorem mem_periodicWindow_iff (h : ω.IsLegalNonempty) {y z : ℤ × ℤ} (hy : y ∈ ω.W)
    (hzc : content z = content y) :
    z ∈ periodicWindow ω ↔ z ∈ ω.E ∨ z + ω.v ∈ ω.E := by
  have hnon := h.nonemptyMark
  have hb := hnon.content_bounds h.isConnectedSkew_E
  have hyb := (hb.1 y hy)
  have hwq : (ω.width : ℤ) < ω.period := h.1.2.2.1.2
  constructor
  · intro hz
    unfold periodicWindow at hz
    obtain ⟨k, hk, hzk⟩ := Finset.mem_biUnion.mp hz
    rw [Finset.mem_Icc] at hk
    have hzE : z - k • ω.v ∈ ω.E := mem_translate.mp hzk
    have hcz := (hb.2 _ hzE)
    rw [content_sub, content_smul, hzc] at hcz
    have hq : ω.period = content ω.v := rfl
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
  · rintro (hz | hz)
    · exact Finset.mem_biUnion.mpr ⟨0, by simp, by simpa [translate_zero] using hz⟩
    · refine Finset.mem_biUnion.mpr ⟨-1, by simp, mem_translate.mpr ?_⟩
      simpa using hz

theorem mem_hatMarkFin_cell (h : ω.IsLegalNonempty) (hc : ω.case = .c) {s t : ℤ}
    (hph : ω.IsPhases s t) {a r : ℤ} :
    ω.cell a r ∈ hatMarkFin ω ↔
      0 ≤ a ∧ a ≤ ω.widthZ - 1 ∧ ω.lo a ≤ r ∧ r ≤ ω.hi a - (if t ≤ a then 1 else 0) := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hlt := h.phases_lt (Or.inl hc) hph
  have hwin : ∀ ρ, ∀ b, 0 ≤ b → b ≤ ω.widthZ - 1 →
      (ω.cell b ρ ∈ periodicWindow ω ↔ (ω.lo b ≤ ρ ∧ ρ ≤ ω.hi b) ∨
        (ω.lo b ≤ ρ ∧ ρ ≤ ω.hi b + (if b < t then 1 else if b < s then 0 else -1))) := by
    intro ρ b hb0 hb1
    obtain ⟨r0, hr0⟩ := h.exists_W hb0 hb1
    rw [mem_periodicWindow_iff h hr0 (by rw [content_cell]; simp [cell, content])]
    rw [cell_add_v, h.mem_E, h.mem_E]
    have hs := hi_shift h hc hph hb0 hb1
    have hl2 := lo_shift h hc hb0 hb1
    constructor
    · rintro (⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩)
      · left; exact ⟨h3, h4⟩
      · right; refine ⟨by omega, by omega⟩
    · rintro (⟨h3, h4⟩ | ⟨h3, h4⟩)
      · left; exact ⟨by omega, by omega, h3, h4⟩
      · right; exact ⟨by omega, by omega, by omega, by omega⟩
  have himg : ∀ x : ℤ × ℤ, (∃ y ∈ ω.W, y - eCell = x) ↔ x + eCell ∈ ω.W := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨x + eCell, hx, by simp⟩
  unfold hatMarkFin
  rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter, Finset.mem_image, himg,
    cell_add_e]
  constructor
  · rintro (⟨-, h1, h2⟩ | ⟨h1, h2⟩)
    · rw [mem_W_cell h hc hph] at h1
      rcases hwin r a h1.1 h1.2.1 |>.mp h2 with h2' | h2'
      · refine ⟨h1.1, h1.2.1, by omega, ?_⟩
        split_ifs at h2' h1 ⊢ <;> omega
      · refine ⟨h1.1, h1.2.1, by omega, ?_⟩
        split_ifs at h2' h1 ⊢ <;> omega
    · rw [mem_W_cell h hc hph] at h1
      rcases (hwin (r + 1) a h1.1 h1.2.1).mp h2 with h2' | h2'
      · refine ⟨h1.1, h1.2.1, h1.2.2.1, ?_⟩
        split_ifs at h2' h1 ⊢ <;> omega
      · refine ⟨h1.1, h1.2.1, h1.2.2.1, ?_⟩
        split_ifs at h2' h1 ⊢ <;> omega
  · rintro ⟨h1, h2, h3, h4⟩
    right
    have hs := hi_shift h hc hph h1 h2
    refine ⟨(mem_W_cell h hc hph).mpr ⟨h1, h2, h3, ?_⟩, (hwin (r + 1) a h1 h2).mpr ?_⟩
    · split_ifs at h4 ⊢ <;> omega
    · by_cases hat : a < t
      · right
        split_ifs at h4 ⊢ <;> omega
      · left
        split_ifs at h4 <;> omega

end Rem

end Corner

end Plan

end SkewGluing
