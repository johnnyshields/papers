import SkewGluing.Aligned.InnerFactor.Assemble

/-!
# The inner factor of a divisible chart: `B = V ∘_ω E`

Formalizes `shields-2026-skew-gluing.tex`, «Equal and divisible periods»
(`prop:gluing-divisible`).

`exists_inner_factor_core`: if `D ∘_ω E` is a translate of `C ∘_η B` for legal marks `ω`, `η`
with periods `q < Q`, `q ∣ Q`, and `ω` is not of case (c), then `B = V ∘_ω E` up to
translation for a connected `V` of span `Q / q + b`, `b ≥ 0`.

Sorry-free.
-/

namespace SkewGluing

open MarkedInner

namespace MarkedInner

variable {ω η : MarkedInner} {D C : Diagram}

/-- A singleton diagonal read through the first window. -/
theorem diag_singleton_of_first_window {E E' : Diagram} {q w : ℤ} {δ : ℤ × ℤ}
    (hw0 : 0 ≤ w) (hwq : w ≤ q - 1) (hmax : minContent E' + w ≤ maxContent E')
    (hE' : IsConnectedSkew E')
    (hδ : content δ = minContent E' - minContent E)
    (hsing : diagLo E (minContent E + w) = diagHi E (minContent E + w))
    (h1 : translate δ (E.filter fun y => content y ≤ minContent E + q - 1) =
      E'.filter fun y => content y ≤ minContent E' + q - 1) :
    diagLo E' (minContent E' + w) = diagHi E' (minContent E' + w) := by
  have hs' := isConnectedSkew_iff_diagonal.mp hE'
  have hk : minContent E' + w ∈ contents E' := by
    rw [hs'.mem_contents_iff]; omega
  have back : ∀ x : ℤ × ℤ, x ∈ E' → content x = minContent E' + w → x - δ ∈ E ∧
      content (x - δ) = minContent E + w := by
    intro x hx hcx
    have hx' : x ∈ E'.filter fun y => content y ≤ minContent E' + q - 1 :=
      Finset.mem_filter.mpr ⟨hx, by omega⟩
    rw [← h1, mem_translate] at hx'
    refine ⟨(Finset.mem_filter.mp hx').1, ?_⟩
    rw [content_sub]; omega
  have m1 := diagLo_mem hk
  have m2 := diagHi_mem hk
  have c1 : content (diagLo E' (minContent E' + w), diagLo E' (minContent E' + w) +
      (minContent E' + w)) = minContent E' + w := by simp [content]
  have c2 : content (diagHi E' (minContent E' + w), diagHi E' (minContent E' + w) +
      (minContent E' + w)) = minContent E' + w := by simp [content]
  obtain ⟨b1, d1⟩ := back _ m1 c1
  obtain ⟨b2, d2⟩ := back _ m2 c2
  have := eq_of_singleton_diag hsing b1 b2 d1 d2
  have h3 := congrArg Prod.fst this
  simp only [Prod.fst_sub] at h3
  omega


/-- **The inner factor, `ω` not of case (c).** -/
theorem exists_inner_factor_core (hω : ω.IsLegal) (hc : ω.case ≠ .c) (hD : IsConnectedSkew D)
    (hη : η.IsLegal) (hC : IsConnectedSkew C) {u : ℤ × ℤ}
    (hFG : ω.compose D = translate u (η.compose C)) (hlt : ω.period < η.period)
    (hdiv : ω.period ∣ η.period) :
    ∃ (V : Diagram) (t : ℤ × ℤ), IsConnectedSkew V ∧ 2 ≤ V.card ∧
      η.E = translate t (ω.compose V) := by
  obtain ⟨a, b, Δ, ha, hb, hba, hΔ, hQ, hw', hr, hΔq⟩ :=
    exists_divisible_numbers hω hη hD hC hFG hlt hdiv
  have hP := perData_of_charts hω hη hD hC hFG ha hb hba hΔ hQ hw' hr hΔq
  obtain ⟨z₁, hf⟩ : ∃ z₁, FactorData D a b Δ z₁ := by
    by_cases hmix : ω.case.IsMixed
    · rcases hmix with hcc | hcc
      · exact absurd hcc hc
      · exact hP.factorData_d hcc
    · exact hP.factorData_ord hmix
  have hV : IsConnectedSkew (innerFactor D a b Δ z₁) := hf.isConnectedSkew_innerFactor
  have hCne := hC.2.1
  have hG : (η.compose C).Nonempty := by
    obtain ⟨d, hd⟩ := id hCne
    obtain ⟨y, hy⟩ := hη.1.1.2.1
    exact ⟨y + η.origin C d, (mem_compose hCne).mpr
      (Or.inl ⟨d, hd, mem_translate.mpr (by simpa using hy)⟩)⟩
  have hq := hω.period_pos
  have hQpos := hη.period_pos
  have hwz : η.widthZ = (η.width : ℤ) := rfl
  have hwz2 : ω.widthZ = (ω.width : ℤ) := rfl
  have hw0' : 0 ≤ η.widthZ := by rw [hwz]; positivity
  have hwq' : η.widthZ < η.period := hη.2.2.1.2
  have hM1 := hω.minContent_compose hD
  have hM2 := hη.minContent_compose hC
  have hM3 : minContent (ω.compose D) = minContent (η.compose C) + content u := by
    rw [hFG, minContent_translate hG]
  have hM4 := hω.minContent_compose hV
  rw [hf.minContent_innerFactor] at hM4
  have hspC := span_eq_of_isConnectedSkew hC
  have hspD := span_eq_of_isConnectedSkew hD
  have e1 : (minContent D + a) * ω.period = minContent D * ω.period + a * ω.period := by ring
  have e1' : (minContent D + b) * ω.period = minContent D * ω.period + b * ω.period := by ring
  have hT := content_factorShift ω Δ z₁
  have hτ := content_ne_sub_sw_origin η hC
  have hmulC : (maxContent C - minContent C) * η.period =
      maxContent C * η.period - minContent C * η.period := by ring
  have hΔq' : Δ * ω.period = (maxContent C - minContent C) * η.period := by
    have : (span C : ℤ) - 1 = maxContent C - minContent C := by omega
    rw [hΔq, this]
  have hc1 : content (η.origin C (sw C)) = minContent C * η.period := by
    rw [content_origin, content_sw hCne]
  have hc2 : content (η.origin C (ne C)) = maxContent C * η.period := by
    rw [content_origin, content_ne hCne]
  -- the first window
  have h1 : translate (u + η.origin C (sw C))
      (η.E.filter fun y => content y ≤ minContent η.E + η.period - 1) =
      (ω.compose (innerFactor D a b Δ z₁)).filter fun y =>
        content y ≤ minContent (ω.compose (innerFactor D a b Δ z₁)) + η.period - 1 := by
    ext y
    simp only [Finset.mem_filter, mem_translate]
    have hcy : content (y - (u + η.origin C (sw C))) =
        content y - content u - minContent C * η.period := by
      rw [content_sub, content_add, hc1]; ring
    rw [hcy]
    constructor
    · rintro ⟨hy, hyc⟩
      have hyc' : content y ≤ minContent (ω.compose (innerFactor D a b Δ z₁)) +
          η.period - 1 := by linarith
      refine ⟨?_, hyc'⟩
      rw [hf.mem_compose_iff_prefix hω (by rw [hQ] at hyc'; linarith), hFG, mem_translate,
        hη.mem_compose_first hC (by rw [content_sub]; linarith [hη.minContent_compose hC])]
      rw [sub_sub]
      exact hy
    · rintro ⟨hy, hyc⟩
      refine ⟨?_, by linarith⟩
      rw [hf.mem_compose_iff_prefix hω (by rw [hQ] at hyc; linarith), hFG, mem_translate,
        hη.mem_compose_first hC (by rw [content_sub]; linarith [hη.minContent_compose hC])] at hy
      rw [sub_sub] at hy
      exact hy
  -- the last window
  have h2 : translate (u + η.origin C (ne C) - factorShift ω Δ z₁)
      (η.E.filter fun y => minContent η.E + η.widthZ ≤ content y) =
      (ω.compose (innerFactor D a b Δ z₁)).filter fun y =>
        minContent (ω.compose (innerFactor D a b Δ z₁)) + η.widthZ ≤ content y := by
    ext y
    simp only [Finset.mem_filter, mem_translate]
    have hcy : content (y - (u + η.origin C (ne C) - factorShift ω Δ z₁)) =
        content y - content u - maxContent C * η.period + Δ * ω.period := by
      rw [content_sub, content_sub, content_add, hc2, hT]; ring
    rw [hcy]
    have hsuf : ∀ y : ℤ × ℤ, minContent (ω.compose (innerFactor D a b Δ z₁)) + η.widthZ ≤
        content y → (y ∈ ω.compose (innerFactor D a b Δ z₁) ↔
          y - (u + η.origin C (ne C) - factorShift ω Δ z₁) ∈ η.E) := by
      intro y hy
      rw [hf.mem_compose_iff_suffix hω (by rw [hwz] at hy; linarith), hFG, mem_translate,
        hη.mem_compose_last hC (by
          rw [content_sub, content_add, hT]; linarith [hη.minContent_compose hC])]
      have e : y + factorShift ω Δ z₁ - u - η.origin C (ne C) =
          y - (u + η.origin C (ne C) - factorShift ω Δ z₁) := by abel
      rw [e]
    constructor
    · rintro ⟨hy, hyc⟩
      have hyc' : minContent (ω.compose (innerFactor D a b Δ z₁)) + η.widthZ ≤ content y := by
        rw [hwz] at hyc ⊢; linarith
      exact ⟨(hsuf y hyc').mpr hy, hyc'⟩
    · rintro ⟨hy, hyc⟩
      refine ⟨(hsuf y hyc).mp hy, ?_⟩
      rw [hwz] at hyc ⊢; linarith
  -- the singleton diagonal
  have hspB : (span η.E : ℤ) = η.period + η.widthZ := hη.1.span_eq
  have hmaxB' := hω.maxContent_compose hV
  have hspV : (span (innerFactor D a b Δ z₁) : ℤ) = a + b := hf.span_innerFactor
  have hspV' := span_eq_of_isConnectedSkew hV
  rw [hf.minContent_innerFactor] at hspV'
  have hB' := hω.isConnectedSkew_compose hV
  have hspB' : (span (ω.compose (innerFactor D a b Δ z₁)) : ℤ) = η.period + η.widthZ := by
    rw [span_compose hV hω, hspV, hQ, hw']
    unfold widthZ
    ring
  have hsing' := diag_singleton_of_first_window (E := η.E)
    (E' := ω.compose (innerFactor D a b Δ z₁)) (q := η.period) (w := η.widthZ)
    (δ := u + η.origin C (sw C)) hw0' (by omega) (by
      have := span_eq_of_isConnectedSkew hB'
      omega) hB' (by
      rw [content_add, hc1, hM4]; rw [hM3, hM2] at hM1; linarith) hη.diag_w_singleton h1
  obtain ⟨δ, hδ⟩ := eq_translate_of_windows (E := η.E)
    (E' := ω.compose (innerFactor D a b Δ z₁)) (q := η.period) (w := η.widthZ) hη.1.1 hB' hspB
    hspB' hw0' hwq' hη.diag_w_singleton hsing' h1 h2
  refine ⟨innerFactor D a b Δ z₁, -δ, hV, ?_, ?_⟩
  · have hle : (contents (innerFactor D a b Δ z₁)).card ≤ (innerFactor D a b Δ z₁).card :=
      Finset.card_image_le
    have : (span (innerFactor D a b Δ z₁) : ℤ) ≤ (innerFactor D a b Δ z₁).card := by
      exact_mod_cast hle
    omega
  · rw [hδ, translate_translate]
    simp [translate_zero]

end MarkedInner

end SkewGluing
