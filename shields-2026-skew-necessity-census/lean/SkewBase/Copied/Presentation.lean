-- [TODO-COPIED] from skew-factor-gluing/lean/SkewGluing/NecessityReduction/Presentation.lean
-- [TODO-COPIED] and skew-factor-gluing/lean/SkewGluing/NecessityReduction/Statements.lean
import SkewBase.Copied.Composition

/-!
# Left-associated composition presentations

The presentation `(((F₀ ∘_{ω₁} E₁) ∘_{ω₂} E₂) ⋯ ∘_{ω_k} E_k)` of `eq:tower` and the relation
`Presentation.Corresponds` of two presentations whose factors agree up to transported
rotation, with `RotationMates`.

Sorry-free.
-/

namespace SkewGluing

-- [TODO-COPIED] from skew-factor-gluing/lean/SkewGluing/NecessityReduction/Statements.lean
/-- Two diagrams are rotation mates: they are equal up to translation, or one is a translate of
the rotation of the other. -/
def RotationMates (F G : Diagram) : Prop :=
  (∃ t, G = translate t F) ∨ ∃ t, G = translate t (rotate F)

-- [TODO-COPIED] from skew-factor-gluing/lean/SkewGluing/NecessityReduction/Presentation.lean
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

end Presentation

end SkewGluing
