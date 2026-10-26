import SkewGluing.Aligned
import SkewGluing.Aligned.InnerFactor
import SkewGluing.CellSchur
import SkewGluing.Invariance

/-!
# Divisible periods

Formalizes `shields-2026-skew-gluing.tex`, «Equal and divisible periods»
(`prop:gluing-divisible`, with `lem:gluing-aligned`, `eq:gluing-reassociation`).

`prop:gluing-divisible`: if `F = D ∘_ω E = C ∘_η B` are proper legal charts of periods `q < Q`
with `q ∣ Q`, then `B = V ∘_ω E` for a connected `V` with at least two cells; a legal lower mark
on `V` gives `eq:gluing-reassociation` for the coarse chart; and the fiber of the coarse chart is
contained in the fiber of the fine chart.

The fiber containment is proved from `lem:gluing-aligned` (`MarkedInner.IsLegal.aligned`),
fixed-chart injectivity, and the Olson-Harris composition and reversal theorems, taken as the
explicit hypothesis `hOH` (Olson-Harris Thms. 5.3.9–5.3.10), discharged by
`olsonHarrisComposition` in `SkewGluing.MainTheorems`.  The fibers are read up to translation
(`fiberClass`), as the paper reads diagrams.

The construction of `V` from the aligned outer pieces is in `SkewGluing.Aligned.InnerFactor`.

Sorry-free.
-/

namespace SkewGluing

namespace MarkedInner

variable {ω η μ : MarkedInner} {V : Diagram} {γ : Diagram → Diagram}

/-- The rotated form of a reassociation: `η* ∘ C = ω* ∘ (μ* ∘ γ(C))` on `V*`. -/
theorem IsReassociation.rotate_forward (hV : V.Nonempty) (h : IsReassociation ω η V μ γ) :
    IsReassociation ω.rotate η.rotate (SkewGluing.rotate V) μ.rotate γ :=
  IsReassociation.rotate (ω := ω.rotate) (η := η.rotate) (V := SkewGluing.rotate V) (μ := μ)
    (hV.image _) (by rw [rotate_rotate, rotate_rotate, SkewGluing.rotate_rotate]; exact h)

theorem IsReassociation.connected_gamma (h : IsReassociation ω η V μ γ) {C : Diagram}
    (hC : IsConnectedSkew C) : IsConnectedSkew (γ C) := by
  rcases h.gamma with h1 | ⟨h1, -⟩
  · rw [h1]; exact hC
  · rw [h1]; exact isConnectedSkew_antitranspose hC

theorem card_le_compose {μ : MarkedInner} {D : Diagram} (hD : D.Nonempty) :
    μ.E.card ≤ (μ.compose D).card := by
  obtain ⟨d, hd⟩ := hD
  have hsub : SkewGluing.translate (μ.origin D d) μ.E ⊆ μ.compose D := by
    intro x hx
    rw [mem_compose ⟨d, hd⟩]
    exact Or.inl ⟨d, hd, hx⟩
  calc μ.E.card = (SkewGluing.translate (μ.origin D d) μ.E).card := by
        rw [SkewGluing.translate, Finset.card_image_of_injective _ (add_left_injective _)]
    _ ≤ _ := Finset.card_le_card hsub

/-- **Fiber containment from a reassociation.**  Let `η` on `U = V ∘_ω E` be reassociated
through the legal lower mark `μ` on `V` (`lem:gluing-aligned`).  Under the Olson-Harris
composition and reversal theorems `hOH` (Olson-Harris Thms. 5.3.9–5.3.10), the fiber of `η` over
`s_C` lies, up to translation, in the fiber of `ω` over `s_{γ(C) ∘_μ V}`, both orientations
included. -/
theorem IsReassociation.fiberClass_subset
    (hOH : ∀ (ω : MarkedInner), ω.IsLegal → ∀ D D' : Diagram, IsConnectedSkew D →
      IsConnectedSkew D' → cellSchur D = cellSchur D' →
      cellSchur (ω.compose D) = cellSchur (ω.compose D') ∧
      cellSchur (ω.rotate.compose D) = cellSchur (ω.compose D'))
    (hr : IsReassociation ω η V μ γ) (hV : IsConnectedSkew V) (hV2 : 2 ≤ V.card)
    {C : Diagram} (hC : IsConnectedSkew C) :
    fiber cellSchur η (cellSchur C) ⊆
      fiberClass cellSchur ω (cellSchur (μ.compose (γ C))) := by
  intro X hX
  obtain ⟨C', hC', -, hs, hX⟩ := hX
  have hγC := hr.connected_gamma hC
  have hγC' := hr.connected_gamma hC'
  have hsγ : cellSchur (γ C') = cellSchur (γ C) := by
    rcases hr.gamma with h1 | ⟨h1, -⟩
    · rw [h1]; simp only [id_eq]; exact hs
    · rw [h1, cellSchur_antitranspose, cellSchur_antitranspose, hs]
  have hμ := hr.legal
  have hoh := hOH μ hμ _ _ hγC' hγC hsγ
  have hconn : IsConnectedSkew (μ.compose (γ C')) := hμ.isConnectedSkew_compose hγC'
  have hconn' : IsConnectedSkew (μ.rotate.compose (γ C')) :=
    (isLegal_rotate hμ).isConnectedSkew_compose hγC'
  have hcard : 2 ≤ (μ.compose (γ C')).card := by
    refine le_trans ?_ (card_le_compose hγC'.2.1); rw [hr.inner]; exact hV2
  have hcard' : 2 ≤ (μ.rotate.compose (γ C')).card := by
    refine le_trans ?_ (card_le_compose hγC'.2.1)
    change 2 ≤ (SkewGluing.rotate μ.E).card
    rw [hr.inner, SkewGluing.rotate, Finset.card_image_of_injective _ neg_injective]; exact hV2
  rcases hX with rfl | rfl
  · rw [hr.compose_eq C' hC']
    exact subset_fiberClass cellSchur ⟨_, hconn, hcard, hoh.1, Or.inl rfl⟩
  · rw [(hr.rotate_forward hV.2.1).compose_eq C' hC']
    exact subset_fiberClass cellSchur ⟨_, hconn', hcard', hoh.2, Or.inr rfl⟩

/-- **`prop:gluing-divisible`, the inner factor.**  If `F = D ∘_ω E = C ∘_η B` are proper legal
charts of periods `q < Q` with `q ∣ Q`, then `B = V ∘_ω E` (up to translation) for a connected
`V` with at least two cells.  The construction of `V` from the aligned outer pieces and the
window comparison are in `SkewGluing.Aligned.InnerFactor`. -/
theorem exists_inner_factor {F : Diagram} {χ₁ χ₂ : Chart} (h₁ : χ₁.IsProperLegal)
    (h₂ : χ₂.IsProperLegal) (hF₁ : χ₁.IsChartOf F) (hF₂ : χ₂.IsChartOf F)
    (hlt : χ₁.period < χ₂.period) (hdiv : χ₁.period ∣ χ₂.period) :
    ∃ (V : Diagram) (t : ℤ × ℤ), IsConnectedSkew V ∧ 2 ≤ V.card ∧
      χ₂.ω.E = SkewGluing.translate t (χ₁.ω.compose V) :=
  exists_inner_factor_proof h₁ h₂ hF₁ hF₂ hlt hdiv

/-- **`prop:gluing-divisible`.**  Let `F = D ∘_ω E = C ∘_η B` be proper legal charts of periods
`q < Q` with `q ∣ Q`.  Then `B = V ∘_ω E` (up to translation) for a connected `V` with at least
two cells; a legal lower mark `μ` on `V` and `γ ∈ {id, AT}` give `eq:gluing-reassociation` for
the coarse chart (`IsReassociation`, with the marked inner `ω` translated into position); and the
fiber of the coarse chart is contained, up to translation, in the fiber of the fine chart.  The
containment uses the Olson-Harris composition and reversal theorems as the explicit hypothesis
`hOH` (Olson-Harris Thms. 5.3.9–5.3.10), and fixed-chart injectivity. -/
theorem divisible
    (hOH : ∀ (ω : MarkedInner), ω.IsLegal → ∀ D D' : Diagram, IsConnectedSkew D →
      IsConnectedSkew D' → cellSchur D = cellSchur D' →
      cellSchur (ω.compose D) = cellSchur (ω.compose D') ∧
      cellSchur (ω.rotate.compose D) = cellSchur (ω.compose D'))
    {F : Diagram} {χ₁ χ₂ : Chart} (h₁ : χ₁.IsProperLegal) (h₂ : χ₂.IsProperLegal)
    (hF₁ : χ₁.IsChartOf F) (hF₂ : χ₂.IsChartOf F)
    (hlt : χ₁.period < χ₂.period) (hdiv : χ₁.period ∣ χ₂.period) :
    ∃ (V : Diagram) (t : ℤ × ℤ), IsConnectedSkew V ∧ 2 ≤ V.card ∧
      χ₂.ω.E = SkewGluing.translate t (χ₁.ω.compose V) ∧
      (∃ (μ : MarkedInner) (γ : Diagram → Diagram),
        IsReassociation (χ₁.ω.translate t) χ₂.ω V μ γ) ∧
      fiberClass cellSchur χ₂.ω (cellSchur χ₂.D) ⊆
        fiberClass cellSchur χ₁.ω (cellSchur χ₁.D) := by
  obtain ⟨V, t, hV, hV2, hE⟩ := exists_inner_factor h₁ h₂ hF₁ hF₂ hlt hdiv
  obtain ⟨hD, -, -, hω⟩ := h₁
  obtain ⟨hC, -, -, hη⟩ := h₂
  obtain ⟨s₁, hs₁⟩ := hF₁
  obtain ⟨s₂, hs₂⟩ := hF₂
  set ω₁ := χ₁.ω.translate t with hω₁
  have hU : χ₂.ω.E = ω₁.compose V := by rw [hω₁, compose_translate]; exact hE
  obtain ⟨a, ha⟩ := hdiv
  have ha' : content χ₂.ω.v = a * ω₁.period := by
    have : content χ₂.ω.v = χ₂.ω.period := rfl
    rw [this]
    have h3 : ω₁.period = χ₁.ω.period := period_translate t _
    rw [h3, mul_comm]; exact ha
  have hω₁l : ω₁.IsLegal := isLegal_translate t hω
  obtain ⟨μ, γ, hr⟩ := hω₁l.aligned hV hη hU ha'
  refine ⟨V, t, hV, hV2, hE, ⟨μ, γ, hr⟩, ?_⟩
  -- the outer `γ(C) ∘_μ V` has the function of `D`
  have hγC := hr.connected_gamma hC
  have hA : IsConnectedSkew (μ.compose (γ χ₂.D)) := hr.legal.isConnectedSkew_compose hγC
  have hs₁' : F = SkewGluing.translate s₁ (χ₁.ω.compose χ₁.D) := hs₁
  have hs₂' : F = SkewGluing.translate s₂ (χ₂.ω.compose χ₂.D) := hs₂
  have hP : χ₂.ω.compose χ₂.D =
      SkewGluing.translate (-s₂ + s₁) (χ₁.ω.compose χ₁.D) := by
    have e1 : SkewGluing.translate (-s₂) F = χ₂.ω.compose χ₂.D := by
      rw [hs₂', SkewGluing.translate_translate]; simp [SkewGluing.translate_zero]
    rw [← e1, hs₁', SkewGluing.translate_translate]
  have hcomp := hr.compose_eq χ₂.D hC
  rw [hω₁, compose_translate, hP] at hcomp
  have hcomp' : χ₁.ω.compose (μ.compose (γ χ₂.D)) =
      SkewGluing.translate (-t + (-s₂ + s₁)) (χ₁.ω.compose χ₁.D) := by
    have := congrArg (SkewGluing.translate (-t)) hcomp.symm
    rw [SkewGluing.translate_translate, SkewGluing.translate_translate] at this
    simpa [SkewGluing.translate_zero] using this
  obtain ⟨w, hw⟩ := hω.injective_compose hD hA hcomp'
  have hsA : cellSchur (μ.compose (γ χ₂.D)) = cellSchur χ₁.D := by
    rw [hw, cellSchur_translate]
  have hsub := IsReassociation.fiberClass_subset hOH hr hV hV2 hC
  rw [hsA] at hsub
  have hfib : ∀ {X : Diagram}, X ∈ fiber cellSchur χ₂.ω (cellSchur χ₂.D) →
      X ∈ fiberClass cellSchur χ₁.ω (cellSchur χ₁.D) := by
    intro X hX
    have := hsub hX
    rwa [hω₁, fiberClass_cellSchur_translate_inner] at this
  rintro X ⟨F', hF', t₀, rfl⟩
  obtain ⟨F'', hF'', t₁, rfl⟩ := hfib hF'
  exact ⟨F'', hF'', t₀ + t₁, by rw [SkewGluing.translate_translate]⟩

end MarkedInner

end SkewGluing
