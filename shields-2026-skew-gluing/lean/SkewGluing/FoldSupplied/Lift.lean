import SkewGluing.Aligned
import SkewGluing.Divisible

/-!
# Lifting a fold of the inner to the original parent

Formalizes `shields-2026-skew-gluing.tex`, «Two ordinary roots» and «Pairs involving mixed
charts» (`prop:gluing-ordinary-fold`, `prop:gluing-mixed-fold`), `lem:gluing-small`, and
`lem:gluing-aligned`: once the supplied inner `E` of a proper chart `F = D ∘_ω E` has a proper
legal chart `E = A_E ∘_κ K` of a period dividing that of `ω`, the original mark `ω` has
displacement content a multiple of the period of `κ`, and aligned composition gives
`F = D_g ∘_κ K` with `D_g = γ(D) ∘_λ A_E`.

* `FoldSupplied.lift`: the new outer `D_g`, the descended mark `λ` and the gauge `γ`.
* `FoldSupplied.exists_lifted_chart`: the lifted chart is a proper legal chart of `F` whose marked
  inner is the supplied fold `κ` (translated), whose period is the period of `κ`, and whose outer
  is `λ ∘ γ(D)` over `A_E`.

Sorry-free.
-/

namespace SkewGluing
namespace FoldSupplied

open MarkedInner

/-- **The lift through aligned composition.**  Let `ω` be a legal mark whose inner `ω.E` is the
translate of `κ ∘ A` with `κ` legal, `A` connected, and the period of `κ` dividing that of `ω`.
Then there are a legal mark `λ` on `A` and `γ ∈ {id, AT}` (`AT` only for an empty `λ`) such that
for every connected outer `D`, `ω ∘ D = κ' ∘ (λ ∘ γ(D))`, with `κ'` the translate of `κ`
matching `ω.E`. -/
theorem lift {ω κ : MarkedInner} {A : Diagram} (hω : ω.IsLegal) (hκ : κ.IsLegal)
    (hA : IsConnectedSkew A) {t : ℤ × ℤ} (hE : ω.E = translate t (κ.compose A))
    (hdvd : κ.period ∣ ω.period) :
    ∃ (μ : MarkedInner) (γ : Diagram → Diagram), μ.IsLegal ∧ μ.E = A ∧
      (γ = id ∨ (γ = antitranspose ∧ μ.W = ∅)) ∧
      ∀ D : Diagram, IsConnectedSkew D →
        ω.compose D = (κ.translate t).compose (μ.compose (γ D)) := by
  have hκt : (κ.translate t).IsLegal := isLegal_translate t hκ
  have hU : ω.E = (κ.translate t).compose A := by
    rw [compose_translate]; exact hE
  obtain ⟨a, ha⟩ := hdvd
  have ha' : content ω.v = a * (κ.translate t).period := by
    rw [period_translate]
    have h1 : ω.period = content ω.v := rfl
    rw [← h1, ha]; ring
  obtain ⟨μ, γ, h⟩ := IsLegal.aligned hκt hA hω hU ha'
  exact ⟨μ, γ, h.legal, h.inner, h.gamma, h.compose_eq⟩

/-- **The lifted chart.**  Let `χ` be a proper legal chart of `F`, and `ψ` a proper legal chart of
its inner `χ.ω.E` of a period dividing `χ.period`.  Then `F` has a proper legal chart whose marked
inner is `ψ.ω` up to translation, whose period is the period of `ψ`, and whose outer is the
composite `λ ∘ γ(χ.D)` over `ψ.D`, with `λ` a legal mark on `ψ.D`. -/
theorem exists_lifted_chart {F : Diagram} {χ ψ : Chart} (hχ : χ.IsProperLegal)
    (hψ : ψ.IsProperLegal) (hF : χ.IsChartOf F) (hE : ψ.IsChartOf χ.ω.E)
    (hdvd : ψ.period ∣ χ.period) :
    ∃ (χ' : Chart) (μ : MarkedInner) (γ : Diagram → Diagram) (t : ℤ × ℤ),
      χ'.IsProperLegal ∧ χ'.IsChartOf F ∧ χ'.ω = ψ.ω.translate t ∧ χ'.period = ψ.period ∧
      μ.IsLegal ∧ μ.E = ψ.D ∧ (γ = id ∨ (γ = antitranspose ∧ μ.W = ∅)) ∧
      χ'.D = μ.compose (γ χ.D) := by
  obtain ⟨hD, hDc, hEc, hω⟩ := hχ
  obtain ⟨hD', hDc', hEc', hω'⟩ := hψ
  obtain ⟨t, ht⟩ := hE
  obtain ⟨μ, γ, hμ, hμE, hγ, hcomp⟩ :=
    lift (ω := χ.ω) (κ := ψ.ω) (A := ψ.D) hω hω' hD' ht
      (by unfold Chart.period at hdvd; exact hdvd)
  have hγD : IsConnectedSkew (γ χ.D) := by
    rcases hγ with h | ⟨h, -⟩
    · rw [h]; exact hD
    · rw [h]; exact isConnectedSkew_antitranspose hD
  have hconn : IsConnectedSkew (μ.compose (γ χ.D)) := hμ.isConnectedSkew_compose hγD
  obtain ⟨t0, ht0⟩ := hF
  refine ⟨⟨μ.compose (γ χ.D), ψ.ω.translate t⟩, μ, γ, t, ⟨hconn, ?_, ?_,
    isLegal_translate t hω'⟩, ⟨t0, ?_⟩, rfl, rfl, hμ, hμE, hγ, rfl⟩
  · change 2 ≤ (μ.compose (γ χ.D)).card
    have h1 := card_le_compose (μ := μ) (D := γ χ.D) hγD.2.1
    rw [hμE] at h1
    omega
  · change 2 ≤ (translate t ψ.ω.E).card
    rw [SkewGluing.translate, Finset.card_image_of_injective _ (add_left_injective _)]
    exact hEc'
  · rw [ht0, Chart.parent, Chart.parent]
    change translate t0 (χ.ω.compose χ.D) = translate t0 ((ψ.ω.translate t).compose _)
    rw [hcomp χ.D hD]

end FoldSupplied
end SkewGluing
