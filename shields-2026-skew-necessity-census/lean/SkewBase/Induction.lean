import SkewBase.ChartSize
import SkewBase.Keys
import SkewBase.Copied.OuterTranslate
import SkewBase.Copied.Presentation

/-!
# Necessity from common keys, by induction on area

Formalizes `shields-2026-skew-base-computational.tex`, «Keys and necessity» (`sec:keys`):
`prop:induction`.

The outer function `s : Diagram → R` is arbitrary (in the paper, the skew Schur function).
`CommonKeysUpTo s n` says that every pair of `s`-equal connected diagrams of at most `n` cells
that are not rotation mates has a common key: `keySet s F ∩ keySet s G` is nonempty
(`SkewBase/Keys.lean`).  A common key gives a common final factor (`HasCommonFinalFactor`): proper
legal charts whose marked inners agree up to translation and rotation and whose outers have the
same value of `s`.  `CommonFinalFactorsUpTo s n` is the weaker hypothesis that the
induction consumes; the key form is the paper's, and it needs no ordinary-gauge identification,
which the paper uses only to show that a single key is well defined on a class.
`NecessityUpTo s n` is the necessity direction of the conjecture of McNamara and
van Willigenburg for these diagrams: every `s`-equal pair is presented by corresponding
left-associated compositions with legal marks (`Presentation`).  The induction passes from the
common keys of a pair to presentations of their outers, which are smaller by `lem:size`
(`SkewBase.two_mul_card_outer_le`).

Sorry-free.
-/

namespace SkewBase

open SkewGluing

variable {R : Type*}

/-- Every `s`-equal pair of connected diagrams of at most `n` cells, not rotation mates, has a
common final factor: proper legal charts with the same marked inner up to translation and
transported rotation and the same outer value. -/
def CommonFinalFactorsUpTo (s : Diagram → R) (n : ℕ) : Prop :=
  ∀ F G : Diagram, IsConnectedSkew F → IsConnectedSkew G → F.card ≤ n → s F = s G →
    ¬ RotationMates F G → HasCommonFinalFactor s F G

/-- The hypothesis of `prop:induction`: `K(X) ∩ K(Y) ≠ ∅` for every connected `X` of at most
`n` cells and every connected `s`-equal `Y` that is not a rotation mate of `X`. -/
def CommonKeysUpTo (s : Diagram → R) (n : ℕ) : Prop :=
  ∀ F G : Diagram, IsConnectedSkew F → IsConnectedSkew G → F.card ≤ n → s F = s G →
    ¬ RotationMates F G → (keySet s F ∩ keySet s G).Nonempty

/-- A common key of two diagrams that are not translates of one another is a common final
factor. -/
theorem hasCommonFinalFactor_of_common_key {s : Diagram → R} {F G : Diagram}
    (hnt : ¬ ∃ t, G = translate t F) (hk : (keySet s F ∩ keySet s G).Nonempty) :
    HasCommonFinalFactor s F G := by
  obtain ⟨k, hF, hG⟩ := hk
  exact ⟨hnt, exists_charts_of_mem_keySet_inter hF hG⟩

theorem commonFinalFactorsUpTo_of_commonKeysUpTo {s : Diagram → R} {n : ℕ}
    (h : CommonKeysUpTo s n) : CommonFinalFactorsUpTo s n :=
  fun F G hF hG hn hs hm =>
    hasCommonFinalFactor_of_common_key (fun ht => hm (Or.inl ht)) (h F G hF hG hn hs hm)

/-- The necessity direction of the conjecture, for connected diagrams of at most `n` cells: every
`s`-equal pair has corresponding legal presentations, read up to translation. -/
def NecessityUpTo (s : Diagram → R) (n : ℕ) : Prop :=
  ∀ F G : Diagram, IsConnectedSkew F → IsConnectedSkew G → F.card ≤ n → s F = s G →
    ∃ π π' : Presentation, π.IsLegal ∧ π'.IsLegal ∧ π.Corresponds π' ∧
      (∃ t : ℤ × ℤ, F = translate t π.value) ∧ ∃ t : ℤ × ℤ, G = translate t π'.value

/-- The induction of `prop:induction`, from common final factors.  The induction is on the area
of `F`. -/
theorem necessityUpTo_of_commonFinalFactorsUpTo (s : Diagram → R) (n : ℕ)
    (hkeys : CommonFinalFactorsUpTo s n) : NecessityUpTo s n := by
  suffices h : ∀ k : ℕ, ∀ F G : Diagram, F.card = k → IsConnectedSkew F → IsConnectedSkew G →
      k ≤ n → s F = s G →
      ∃ π π' : Presentation, π.IsLegal ∧ π'.IsLegal ∧ π.Corresponds π' ∧
        (∃ t : ℤ × ℤ, F = translate t π.value) ∧ ∃ t : ℤ × ℤ, G = translate t π'.value by
    intro F G hF hG hn hs
    exact h F.card F G rfl hF hG hn hs
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro F G hk hF hG hn hs
    by_cases hmates : RotationMates F G
    · exact ⟨.first F, .first G, hF, hG, hmates, ⟨0, (translate_zero).symm⟩,
        ⟨0, (translate_zero).symm⟩⟩
    · obtain ⟨-, χ₁, χ₂, h₁, h₂, ⟨t₁, hF₁⟩, ⟨t₂, hG₂⟩, hω, hsD⟩ :=
        hkeys F G hF hG (hk ▸ hn) hs hmates
      have hcard : χ₁.D.card < k := by
        have h2 := two_mul_card_outer_le h₁
        have h3 : F.card = χ₁.parent.card := card_of_isChartOf ⟨t₁, hF₁⟩
        have h4 := h₁.2.1
        omega
      obtain ⟨π, π', hπ, hπ', hcor, ⟨a, ha⟩, ⟨b, hb⟩⟩ :=
        ih _ hcard χ₁.D χ₂.D rfl h₁.1 h₂.1 (by omega) hsD
      have hne : π.value.Nonempty := by
        have := h₁.1.2.1
        rw [ha] at this
        obtain ⟨x, hx⟩ := this
        obtain ⟨y, hy, -⟩ := Finset.mem_image.mp hx
        exact ⟨y, hy⟩
      have hne' : π'.value.Nonempty := by
        have := h₂.1.2.1
        rw [hb] at this
        obtain ⟨x, hx⟩ := this
        obtain ⟨y, hy, -⟩ := Finset.mem_image.mp hx
        exact ⟨y, hy⟩
      refine ⟨.step π χ₁.ω, .step π' χ₂.ω, ⟨hπ, h₁.2.2.2⟩, ⟨hπ', h₂.2.2.2⟩, ⟨hcor, hω⟩,
        ⟨t₁ + χ₁.ω.outerShift a, ?_⟩, ⟨t₂ + χ₂.ω.outerShift b, ?_⟩⟩
      · rw [hF₁]
        change translate t₁ (χ₁.ω.compose χ₁.D) = translate _ (χ₁.ω.compose π.value)
        rw [ha, MarkedInner.compose_translate_outer a hne, translate_translate]
      · rw [hG₂]
        change translate t₂ (χ₂.ω.compose χ₂.D) = translate _ (χ₂.ω.compose π'.value)
        rw [hb, MarkedInner.compose_translate_outer b hne', translate_translate]

/-- **`prop:induction`.**  If every `s`-equal pair of connected diagrams of at most `n` cells that
are not rotation mates has a common key, `K(X) ∩ K(Y) ≠ ∅`, then the necessity direction holds for
every connected diagram of at most `n` cells. -/
theorem necessityUpTo_of_commonKeysUpTo (s : Diagram → R) (n : ℕ)
    (hkeys : CommonKeysUpTo s n) : NecessityUpTo s n :=
  necessityUpTo_of_commonFinalFactorsUpTo s n (commonFinalFactorsUpTo_of_commonKeysUpTo hkeys)

end SkewBase
