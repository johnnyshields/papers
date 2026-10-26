import SkewGluing.Aligned.CaseD.Legal1

/-!
# Aligned marks, case (d): legality of the lower mark

Formalizes `shields-2026-skew-gluing.tex`, «Equal and divisible periods»
(`lem:gluing-aligned`).

`alD_case V a θ` is the attachment case read off the tails, `alD_lowerMark V a θ` the lower mark
`μ = (V, Z, z, alD_case)`, and `alD_lowerMark_isLegal` proves it is legal under `alD_Data V a θ`:
I because a larger copy would be a larger intersection, II from `b < a`, III from
`alD_compl_lower`, `alD_compl_upper`, IV by the content-distance argument.

Sorry-free.
-/

namespace SkewGluing

open Classical in
/-- The attachment case of the lower mark: the lower attachment (horizontal or vertical) and
the upper attachment, read off the middle. -/
noncomputable def alD_case (V : Diagram) (a θ : ℤ) : AttachCase :=
  if (alD_mark V a θ .a).LowerH then
    (if (alD_mark V a θ .a).UpperH then .a else .c)
  else (if (alD_mark V a θ .a).UpperH then .d else .b)

/-- The lower mark `μ` of `lem:gluing-aligned` on `V`. -/
noncomputable def alD_lowerMark (V : Diagram) (a θ : ℤ) : MarkedInner :=
  alD_mark V a θ (alD_case V a θ)

section Legal

variable {V : Diagram} {a θ : ℤ}

theorem alD_mark_case (cs : AttachCase) : (alD_mark V a θ cs).case = cs := rfl

theorem alD_lowerMark_E : (alD_lowerMark V a θ).E = V := rfl
theorem alD_lowerMark_W : (alD_lowerMark V a θ).W = alD_Z V a θ := rfl
theorem alD_lowerMark_v : (alD_lowerMark V a θ).v = alD_z a θ := rfl
theorem alD_lowerMark_period : (alD_lowerMark V a θ).period = a := alD_period _

theorem alD_attachmentMatches (hV : IsConnectedSkew V) (hD : alD_Data V a θ) :
    (alD_lowerMark V a θ).AttachmentMatches := by
  have hl := alD_lower_attach (cs := .a) hV hD
  have hu := alD_upper_attach (cs := .a) hV hD
  have eLH : ∀ cs, (alD_mark V a θ cs).LowerH ↔ (alD_mark V a θ .a).LowerH := fun _ => Iff.rfl
  have eLV : ∀ cs, (alD_mark V a θ cs).LowerV ↔ (alD_mark V a θ .a).LowerV := fun _ => Iff.rfl
  have eUH : ∀ cs, (alD_mark V a θ cs).UpperH ↔ (alD_mark V a θ .a).UpperH := fun _ => Iff.rfl
  have eUV : ∀ cs, (alD_mark V a θ cs).UpperV ↔ (alD_mark V a θ .a).UpperV := fun _ => Iff.rfl
  unfold MarkedInner.AttachmentMatches alD_lowerMark
  rw [eLH, eLV, eUH, eUV]
  unfold alD_case
  by_cases h1 : (alD_mark V a θ .a).LowerH <;> by_cases h2 : (alD_mark V a θ .a).UpperH <;>
    simp only [h1, h2, ↓reduceIte]
  · simp [alD_mark_case]
  · simp [alD_mark_case, hu.resolve_left h2]
  · simp [alD_mark_case, hl.resolve_left h1]
  · simp [alD_mark_case, hl.resolve_left h1, hu.resolve_left h2]

theorem alD_isNonemptyMark (hV : IsConnectedSkew V) (hD : alD_Data V a θ) :
    (alD_lowerMark V a θ).IsNonemptyMark :=
  ⟨alD_Z_nonempty hV hD, alD_Z_connected hV hD, fun _x hx => alD_Z_sub hx,
    fun _x hx => alD_upper_sub hV hD hx, alD_sw_mem hV hD, alD_ne_mem hV hD,
    alD_attachmentMatches hV hD⟩

theorem alD_isWellFormed (hV : IsConnectedSkew V) (hD : alD_Data V a θ) :
    (alD_lowerMark V a θ).IsWellFormed := ⟨hV, Or.inr (alD_isNonemptyMark hV hD)⟩

theorem alD_isNarrow (hV : IsConnectedSkew V) (hD : alD_Data V a θ) :
    (alD_lowerMark V a θ).IsNarrow := by
  have hw := alD_width (cs := alD_case V a θ) hV hD
  have hp := alD_lowerMark_period (V := V) (a := a) (θ := θ)
  have hb := hD.hb
  have hba := hD.hba
  unfold MarkedInner.IsNarrow
  have : ((alD_lowerMark V a θ).width : ℤ) = (span V : ℤ) - a := hw
  rw [hp]
  omega

theorem alD_removalsConnected (hV : IsConnectedSkew V) (hD : alD_Data V a θ) :
    (alD_lowerMark V a θ).RemovalsConnected := by
  obtain ⟨s, hs1, hs2, hs3, hs4⟩ := alD_s hV hD
  obtain ⟨t, ht0, ht1, ht2, ht3⟩ := alD_t hV hD
  exact ⟨alD_compl_lower hV hD hs1 hs2 hs3 hs4, alD_compl_upper hV hD ht0 ht1 ht2 ht3⟩

theorem alD_isMaximal (hV : IsConnectedSkew V) (hD : alD_Data V a θ) :
    (alD_lowerMark V a θ).IsMaximal := by
  apply MarkedInner.IsMaximalAtDisplacement.isMaximal hV (alD_isNonemptyMark hV hD)
  intro W' hW' hlt _ _ hsub
  have hW'V : W' ⊆ V := Finset.mem_powerset.mp hW'
  apply hlt.2
  intro y hy
  change y ∈ alD_Z V a θ
  unfold alD_Z
  rw [Finset.mem_filter]
  refine ⟨hW'V hy, ?_⟩
  have h1 : y + (alD_lowerMark V a θ).v ∈ translate (alD_lowerMark V a θ).v W' :=
    mem_translate.mpr (by simpa using hy)
  exact hsub h1

theorem alD_noHat (hV : IsConnectedSkew V) (hD : alD_Data V a θ) :
    (alD_lowerMark V a θ).NoHatAdjacency := by
  have hb := hD.hb
  have hba := hD.hba
  have ha := hD.ha
  intro k m x hx y hy hadj
  obtain ⟨hx1, hx2⟩ := hx
  have hcv : content (alD_lowerMark V a θ).v = a := alD_period _
  -- the middle cell and its diagonal neighbor `x + e`
  have hx1' : x - k • (alD_lowerMark V a θ).v ∈ (alD_lowerMark V a θ).middle :=
    MarkedInner.mem_translate_smul.mp hx1
  have hx2' : (x - k • (alD_lowerMark V a θ).v) + eCell ∈ (alD_lowerMark V a θ).middle := by
    have := MarkedInner.mem_translate_smul.mp hx2
    have e : x + eCell - k • (alD_lowerMark V a θ).v =
        (x - k • (alD_lowerMark V a θ).v) + eCell := by abel
    rw [e] at this; exact this
  set x0 := x - k • (alD_lowerMark V a θ).v with hx0
  have hform := alD_cell_form V x0
  have hj := alD_middle_thin (cs := alD_case V a θ) hV hD (r₁ := x0.1) (r₂ := x0.1 + 1)
    (j := content x0 - minContent V) (by rw [← hform]; exact hx1')
    (by
      have e : (x0.1 + 1, x0.1 + 1 + (minContent V + (content x0 - minContent V))) =
          x0 + eCell := by
        ext <;> simp [content, eCell]; ring
      rw [e]; exact hx2') (by omega)
  have hcx : content x = content x0 + k * a := by
    have : x = x0 + k • (alD_lowerMark V a θ).v := by rw [hx0]; abel
    rw [this, content_add, MarkedInner.content_smul, hcv]
  -- the content of `y` modulo the period
  have hcy : ∃ i, 0 ≤ i ∧ i ≤ (span V : ℤ) - a - 1 ∧ content y = minContent V + i + m * a := by
    have key : ∀ z, z - m • (alD_lowerMark V a θ).v ∈ alD_Z V a θ →
        ∃ i, 0 ≤ i ∧ i ≤ (span V : ℤ) - a - 1 ∧ content z = minContent V + i + m * a := by
      intro z hz
      have := alD_Z_content hV hD hz
      rw [MarkedInner.content_sub, MarkedInner.content_smul, hcv] at this
      exact ⟨content z - m * a - minContent V, by omega, by omega, by omega⟩
    rcases hy with ⟨-, hy2⟩ | ⟨hy1, -⟩
    · have h := MarkedInner.mem_translate_smul.mp hy2
      obtain ⟨i, h1, h2, h3⟩ := key (y + eCell) (by
        have e : y + eCell - m • (alD_lowerMark V a θ).v ∈ alD_Z V a θ := h
        exact e)
      rw [MarkedInner.content_eCell_add] at h3
      exact ⟨i, h1, h2, h3⟩
    · exact key y (MarkedInner.mem_translate_smul.mp hy1)
  obtain ⟨i, hi0, hi1, hcy⟩ := hcy
  have hca := content_adj hadj
  rw [hcx, hcy] at hca
  have e : (k - m) * a = k * a - m * a := by ring
  by_cases hkm : k - m ≤ -1
  · have : (k - m) * a ≤ -a := by nlinarith
    omega
  · have : 0 ≤ (k - m) * a := by nlinarith
    omega

theorem alD_lowerMark_isLegal (hV : IsConnectedSkew V) (hD : alD_Data V a θ) :
    (alD_lowerMark V a θ).IsLegal :=
  ⟨alD_isWellFormed hV hD, alD_isMaximal hV hD, alD_isNarrow hV hD,
    alD_removalsConnected hV hD, alD_noHat hV hD⟩

end Legal

end SkewGluing
