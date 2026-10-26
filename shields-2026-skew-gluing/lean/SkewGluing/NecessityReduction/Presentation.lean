import SkewGluing.NecessityReduction.Statements
import SkewGluing.Lines.Rows
import SkewGluing.Invariance

/-!
# Left-associated composition presentations

Formalizes `shields-2026-skew-gluing.tex`, «Reduction of composition necessity»
(`thm:necessity-reduction`), the notions it speaks about.

A *presentation* `(((F₀ ∘_{ω₁} E₁) ∘_{ω₂} E₂) ⋯ ∘_{ω_k} E_k)` of a diagram is a first factor
`F₀` and a list of marked inners `ω_i` (each carrying its inner `E_i = ω_i.E`), composed from
the left.  It is *legal* if `F₀` is connected skew and every `ω_i` is legal (so every factor is
a connected skew diagram, and so is every partial composite).  Two presentations *correspond*
when they have the same number of factors and each factor of the second is, up to translation,
the corresponding factor of the first or its rotation, with the entire mark transported
(`MarkedInner.rotate`): "agree up to transported rotation".

* `Presentation.value`, `Presentation.IsLegal`, `Presentation.Corresponds`.
* `Presentation.IsCompleteTower`: a *complete source-minimal tower*: a source-minimal chart is
  chosen, then repeated on its actual outer, until a chartless diagram is reached.
  `exists_isCompleteTower`: every connected diagram is the value of one (the span law makes the
  procedure finite).
* `Presentation.reversalFamily`: the diagrams obtained by independently retaining or rotating
  each factor, read up to translation.
* `Presentation.Corresponds.cellSchur_value`,
  `Presentation.Corresponds.rotationMates_or_hasCommonFinalFactor`:
  forward composition and reversal along corresponding presentations, and the common-factor
  edge of a nonrotation pair (the first implication of `thm:necessity-reduction`).

Forward composition and reversal is the hypothesis `hOH : OlsonHarrisComposition`, discharged by
`olsonHarrisComposition` in `SkewGluing.MainTheorems`.

Sorry-free.
-/

namespace SkewGluing

/-! ### Singleton factors -/

namespace MarkedInner

/-- Composing with a single-cell outer `{d}` gives a translate of the inner. -/
theorem compose_singleton_outer (ω : MarkedInner) (d : ℤ × ℤ) :
    ω.compose {d} = SkewGluing.translate (ω.origin {d} d) ω.E := by
  have hne : ({d} : Diagram).Nonempty := Finset.singleton_nonempty d
  ext x
  rw [mem_compose hne]
  simp only [Finset.mem_singleton, exists_eq_left]
  constructor
  · rintro (h | ⟨⟨h, -⟩, -⟩)
    · exact h
    · exfalso
      have := congrArg Prod.fst (Finset.mem_singleton.mp h)
      simp at this
  · exact Or.inl

/-- Composing with a legal marked inner whose inner is a single cell is the identity, up to
translation: such a mark is empty (a nonempty mark would have period zero), and the empty mark
on one cell places the copies at the cells of the outer. -/
theorem IsLegal.compose_of_card_le_one {ω : MarkedInner} (hω : ω.IsLegal)
    (hE : ¬ 2 ≤ ω.E.card) {D : Diagram} (hD : D.Nonempty) :
    ∃ t : ℤ × ℤ, ω.compose D = SkewGluing.translate t D := by
  have hEne : ω.E.Nonempty := hω.1.1.2.1
  obtain ⟨c, hc⟩ : ∃ c, ω.E = {c} := by
    apply Finset.card_eq_one.mp
    have := hEne.card_pos
    omega
  have hall : ∀ x ∈ ω.E, x = c := by
    intro x hx; rw [hc] at hx; simpa using hx
  rcases hω.1.2 with ⟨h1, h2, h3⟩ | hnon
  · have hsw : sw ω.E = c := hall _ (sw_mem hEne)
    have hnee : ne ω.E = c := hall _ (ne_mem hEne)
    have hv : ω.v = (0, 1) := by
      rw [h2]; unfold vH; rw [hsw, hnee]; simp
    refine ⟨c, ?_⟩
    ext x
    rw [mem_compose hD, mem_translate]
    have hor : ∀ d : ℤ × ℤ, ω.origin D d = d := by
      intro d
      unfold origin
      rw [h3, hv]
      ext <;> simp [content, eCell]
    constructor
    · rintro (⟨d, hd, hx⟩ | ⟨d, -, hr, -⟩)
      · rw [hor, hc, mem_translate] at hx
        simp only [Finset.mem_singleton] at hx
        have : x - c = d := by rw [← hx]; abel
        rw [this]; exact hd
      · exact absurd hr (sameRibbon_of_ordinary (by simp [AttachCase.IsMixed, h3]) D d)
    · intro hx
      refine Or.inl ⟨x - c, hx, ?_⟩
      rw [hor, hc, mem_translate]
      simp
  · exfalso
    obtain ⟨hWne, -, hWE, hUE, -⟩ := hnon
    obtain ⟨y, hy⟩ := hWne
    have hyc : y = c := hall _ (hWE hy)
    have hup : y + ω.v ∈ ω.upper := mem_translate.mpr (by simpa using hy)
    have hyv : y + ω.v = c := hall _ (hUE hup)
    have hv0 : ω.v = 0 := by rw [hyc] at hyv; simpa using hyv
    have := hω.period_pos
    unfold period at this
    rw [hv0] at this
    simp [content] at this

end MarkedInner

/-! ### Rotation mates -/

theorem RotationMates.of_translates {D D' F G : Diagram} (h : RotationMates D D') {a b : ℤ × ℤ}
    (hF : F = translate a D) (hG : G = translate b D') : RotationMates F G := by
  rcases h with ⟨s, hs⟩ | ⟨s, hs⟩
  · refine Or.inl ⟨b + s - a, ?_⟩
    rw [hG, hs, hF, translate_translate, translate_translate]
    congr 1; abel
  · refine Or.inr ⟨b + s + a, ?_⟩
    rw [hG, hs, hF, rotate_translate_eq, translate_translate, translate_translate]
    congr 1; abel

theorem RotationMates.cellSchur_eq {F G : Diagram} (h : RotationMates F G) :
    cellSchur G = cellSchur F := by
  rcases h with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · exact cellSchur_translate _ _
  · rw [cellSchur_translate, cellSchur_rotate]

/-- A proper chart has an outer of strictly smaller span (the span law
`N_F = N_D q + w > N_D`). -/
theorem Chart.IsProperLegal.span_outer_lt {χ : Chart} (h : χ.IsProperLegal) :
    span χ.D < span χ.parent := by
  obtain ⟨hD, hc, hE, hω⟩ := h
  have hspan := MarkedInner.span_compose hD hω
  have hE2 := two_le_span_of_two_le_card hω.1.1 hE
  have hD2 := two_le_span_of_two_le_card hD hc
  have hEq := hω.1.span_eq
  have hwq := hω.2.2.1.2
  have hq := hω.period_pos
  have hq2 : 2 ≤ χ.ω.period := by omega
  change span χ.D < span (χ.ω.compose χ.D)
  have : (span χ.D : ℤ) < span (χ.ω.compose χ.D) := by
    rw [hspan]
    have h1 : (2 : ℤ) ≤ span χ.D := by exact_mod_cast hD2
    nlinarith [(by positivity : (0 : ℤ) ≤ χ.ω.width)]
  exact_mod_cast this

theorem MarkedInner.EquivTranslate.refl (ω : MarkedInner) : ω.EquivTranslate ω :=
  ⟨0, (MarkedInner.translate_zero ω).symm⟩

/-! ### Presentations -/

/-- A left-associated composition presentation: a first factor and the marked inners composed
onto it one after another. -/
inductive Presentation : Type
  /-- The one-factor presentation `F₀`. -/
  | first (F₀ : Diagram) : Presentation
  /-- Compose the presentation so far with one more marked inner: `(⋯) ∘_ω E`. -/
  | step (π : Presentation) (ω : MarkedInner) : Presentation

namespace Presentation

/-- The diagram presented: `F₀`, respectively `ω.compose` of the diagram so far. -/
def value : Presentation → Diagram
  | first F₀ => F₀
  | step π ω => ω.compose π.value

/-- The presentation is legal with connected factors: `F₀` is connected skew and every marked
inner is legal (its inner `E` is then connected skew). -/
def IsLegal : Presentation → Prop
  | first F₀ => IsConnectedSkew F₀
  | step π ω => π.IsLegal ∧ ω.IsLegal

/-- Two presentations *correspond* when they have the same number of factors and every factor
of the second is, up to translation, the factor of the first or its rotation, the whole mark
being transported (`ω ↦ ω*`). -/
def Corresponds : Presentation → Presentation → Prop
  | first F₀, first F₀' => RotationMates F₀ F₀'
  | step π ω, step π' ω' => π.Corresponds π' ∧ (ω.EquivTranslate ω' ∨ ω.rotate.EquivTranslate ω')
  | _, _ => False

/-- The reversal family of a presentation: the diagrams, up to translation, of the
presentations obtained by independently retaining or rotating each factor with its mark. -/
def reversalFamily (π : Presentation) : Set Diagram :=
  {G | ∃ π' : Presentation, π.Corresponds π' ∧ ∃ t : ℤ × ℤ, G = translate t π'.value}

theorem isConnectedSkew_value : ∀ {π : Presentation}, π.IsLegal → IsConnectedSkew π.value
  | first _, h => h
  | step _ _, h => h.2.isConnectedSkew_compose (isConnectedSkew_value h.1)

theorem Corresponds.isLegal : ∀ {π π' : Presentation}, π.Corresponds π' → π.IsLegal →
    π'.IsLegal
  | first F₀, first F₀', h, hl => by
    rcases h with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · exact isConnectedSkew_translate t hl
    · exact isConnectedSkew_translate t (isConnectedSkew_rotate hl)
  | step π ω, step π' ω', ⟨h, hω⟩, hl => by
    refine ⟨Corresponds.isLegal h hl.1, ?_⟩
    rcases hω with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · exact MarkedInner.isLegal_translate t hl.2
    · exact MarkedInner.isLegal_translate t (MarkedInner.isLegal_rotate hl.2)
  | first _, step _ _, h, _ => h.elim
  | step _ _, first _, h, _ => h.elim

/-- A corresponding marked inner has the same number of inner cells. -/
theorem card_inner_of_correspond {ω ω' : MarkedInner}
    (h : ω.EquivTranslate ω' ∨ ω.rotate.EquivTranslate ω') : ω'.E.card = ω.E.card := by
  rcases h with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · exact Finset.card_image_of_injective _ (add_left_injective t)
  · change (translate t (rotate ω.E)).card = _
    rw [translate, Finset.card_image_of_injective _ (add_left_injective t)]
    exact Chart.card_rotate _

/-- **Forward composition and reversal along corresponding presentations.**  Corresponding legal
presentations present Schur-equal diagrams (Olson-Harris, Thms. 5.3.9–5.3.10, as the hypothesis
`hOH`). -/
theorem Corresponds.cellSchur_value (hOH : OlsonHarrisComposition) :
    ∀ {π π' : Presentation}, π.Corresponds π' → π.IsLegal →
      cellSchur π'.value = cellSchur π.value
  | first F₀, first F₀', h, _ => RotationMates.cellSchur_eq h
  | step π ω, step π' ω', ⟨h, hω⟩, hl => by
    have ih := Corresponds.cellSchur_value hOH h hl.1
    have hD := isConnectedSkew_value hl.1
    have hD' := isConnectedSkew_value (h.isLegal hl.1)
    change cellSchur (ω'.compose π'.value) = cellSchur (ω.compose π.value)
    rcases hω with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · change cellSchur ((ω.translate t).compose π'.value) = _
      rw [MarkedInner.compose_translate, cellSchur_translate]
      exact hOH ω hl.2 _ _ hD' hD ih
    · change cellSchur ((ω.rotate.translate t).compose π'.value) = _
      rw [MarkedInner.compose_translate, cellSchur_translate]
      exact (hOH.compose_eq_rotate_compose hl.2 hD hD' ih.symm).symm
  | first _, step _ _, h, _ => h.elim
  | step _ _, first _, h, _ => h.elim

/-- **Nonrotation pairs of a corresponding pair of presentations have a common final factor**
(`thm:necessity-reduction`, first implication, before the passage to classes).  Let `π`, `π'` be
corresponding legal presentations.  Then their values are rotation mates, or have a common final
factor.  Stages whose inner is a single cell and a single-cell first factor are the trivial
stages of the paper: they change the diagram only by translation, and are absorbed along the
induction; the last nontrivial stage is a pair of proper charts with equal outer functions.

**Differs from the paper's route.**  Trivial stages are absorbed along the induction instead of
being removed from the presentations in advance. -/
theorem Corresponds.rotationMates_or_hasCommonFinalFactor (hOH : OlsonHarrisComposition) :
    ∀ {π π' : Presentation}, π.Corresponds π' → π.IsLegal →
      RotationMates π.value π'.value ∨ HasCommonFinalFactor cellSchur π.value π'.value
  | first F₀, first F₀', h, _ => Or.inl h
  | step π ω, step π' ω', ⟨h, hω⟩, hl => by
    have ih := Corresponds.rotationMates_or_hasCommonFinalFactor hOH h hl.1
    have hs := Corresponds.cellSchur_value hOH h hl.1
    have hlD' := h.isLegal hl.1
    have hD := isConnectedSkew_value hl.1
    have hD' := isConnectedSkew_value hlD'
    have hω' : ω'.IsLegal := by
      rcases hω with ⟨t, rfl⟩ | ⟨t, rfl⟩
      · exact MarkedInner.isLegal_translate t hl.2
      · exact MarkedInner.isLegal_translate t (MarkedInner.isLegal_rotate hl.2)
    have hEc := card_inner_of_correspond hω
    change RotationMates (ω.compose π.value) (ω'.compose π'.value) ∨
      HasCommonFinalFactor cellSchur (ω.compose π.value) (ω'.compose π'.value)
    by_cases hE : 2 ≤ ω.E.card
    · have hE' : 2 ≤ ω'.E.card := by omega
      by_cases hDc : 2 ≤ π.value.card
      · -- both stages proper
        have hcard : π'.value.card = π.value.card :=
          card_eq_of_cellSchur_eq hD hD'.1 hs
        have hDc' : 2 ≤ π'.value.card := by omega
        by_cases hFG : ∃ t, ω'.compose π'.value = translate t (ω.compose π.value)
        · exact Or.inl (Or.inl hFG)
        · refine Or.inr ⟨hFG, ⟨π.value, ω⟩, ⟨π'.value, ω'⟩, ⟨hD, hDc, hE, hl.2⟩,
            ⟨hD', hDc', hE', hω'⟩, ⟨0, ?_⟩, ⟨0, ?_⟩, hω, hs.symm⟩
          · exact (translate_zero).symm
          · exact (translate_zero).symm
      · -- the outer is a single cell, so the composite is a translate of the inner
        have hDne := hD.2.1
        obtain ⟨d, hd⟩ : ∃ d, π.value = {d} := by
          apply Finset.card_eq_one.mp
          have := hDne.card_pos
          omega
        have hcard : π'.value.card = π.value.card :=
          card_eq_of_cellSchur_eq hD hD'.1 hs
        obtain ⟨d', hd'⟩ : ∃ d', π'.value = {d'} := by
          apply Finset.card_eq_one.mp
          have := hDne.card_pos
          omega
        refine Or.inl ?_
        have hmates : RotationMates ω.E ω'.E := by
          rcases hω with ⟨t, rfl⟩ | ⟨t, rfl⟩
          · exact Or.inl ⟨t, rfl⟩
          · exact Or.inr ⟨t, rfl⟩
        rw [hd, hd', MarkedInner.compose_singleton_outer, MarkedInner.compose_singleton_outer]
        exact RotationMates.of_translates hmates rfl rfl
    · -- the stage is trivial: a single-cell inner leaves the diagram unchanged up to translation
      have hE' : ¬ 2 ≤ ω'.E.card := by omega
      obtain ⟨a, ha⟩ := hl.2.compose_of_card_le_one hE hD.2.1
      obtain ⟨b, hb⟩ := hω'.compose_of_card_le_one hE' hD'.2.1
      rw [ha, hb]
      rcases ih with ih | ih
      · exact Or.inl (RotationMates.of_translates ih rfl rfl)
      · exact Or.inr ((ih.translate_left a).translate_right b)
  | first _, step _ _, h, _ => h.elim
  | step _ _, first _, h, _ => h.elim

/-! ### Complete source-minimal towers -/

/-- A *complete source-minimal tower*: the first factor is a chartless connected diagram, and
every stage is a source-minimal chart, at the diagram built so far, whose outer is the actual
presentation built so far.  The inner of a stage need not be chartless. -/
inductive IsCompleteTower : Presentation → Prop
  | first {F₀ : Diagram} : IsConnectedSkew F₀ → ¬ HasProperChart F₀ → IsCompleteTower (first F₀)
  | step {π : Presentation} {ω : MarkedInner} : IsCompleteTower π →
      (⟨π.value, ω⟩ : Chart).IsSourceMinimal (ω.compose π.value) → IsCompleteTower (step π ω)

theorem IsCompleteTower.isLegal : ∀ {π : Presentation}, IsCompleteTower π → π.IsLegal
  | _, .first h _ => h
  | _, .step hπ hsm => ⟨hπ.isLegal, hsm.1.2.2.2⟩

/-- **Complete source-minimal towers exist.**  Every connected diagram is the value of a
complete source-minimal tower: choose a source-minimal chart, and repeat on its actual outer
(which has strictly smaller span) until a chartless diagram is reached. -/
theorem exists_isCompleteTower :
    ∀ (n : ℕ) (F : Diagram), span F = n → IsConnectedSkew F →
      ∃ π : Presentation, IsCompleteTower π ∧ π.value = F := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro F hn hF
    by_cases hroot : HasProperChart F
    · obtain ⟨χ, hχ⟩ := Chart.exists_isSourceMinimal hroot
      obtain ⟨hp, ⟨t, ht⟩, hmin⟩ := hχ
      have hlt : span χ.D < n := by
        have := hp.span_outer_lt
        rw [ht, span_translate] at hn
        omega
      obtain ⟨π₀, hπ₀, hval⟩ := ih _ hlt χ.D rfl hp.1
      refine ⟨step π₀ (χ.ω.translate t), .step hπ₀ ?_, ?_⟩
      · rw [hval]
        have hF' : (χ.ω.translate t).compose χ.D = F := by
          rw [MarkedInner.compose_translate, ht]; rfl
        rw [hF']
        refine ⟨⟨hp.1, hp.2.1, ?_, MarkedInner.isLegal_translate t hp.2.2.2⟩,
          ⟨0, by rw [translate_zero]; exact hF'.symm⟩, ?_⟩
        · change 2 ≤ (translate t χ.ω.E).card
          rw [translate, Finset.card_image_of_injective _ (add_left_injective t)]
          exact hp.2.2.1
        · intro χ'' h1 h2
          have := hmin χ'' h1 h2
          unfold Chart.score at this ⊢
          simpa [MarkedInner.width_translate, span_translate] using this
      · change (χ.ω.translate t).compose π₀.value = F
        rw [hval, MarkedInner.compose_translate, ht]; rfl
    · exact ⟨first F, .first hF hroot, rfl⟩

end Presentation

end SkewGluing
