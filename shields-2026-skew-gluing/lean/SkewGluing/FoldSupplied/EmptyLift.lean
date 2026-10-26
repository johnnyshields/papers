import SkewGluing.FoldSupplied.Empty
import SkewGluing.FoldSupplied.Lift
import SkewGluing.OrdinaryFold

/-!
# The empty residue fold of a supplied empty inner, lifted to the parent

Formalizes `shields-2026-skew-gluing.tex`, «Small-overlap roots» (`lem:gluing-small`) and
`ge:empty-fold`: for a proper legal chart `F = D ∘_ω E` whose mark is the horizontal empty mark
(width zero), the inner `E` of span `p` is an actual connected inner with its empty mark; when its
completed native words are `d`-periodic (`d ∣ p`, `2 ≤ d < p`), `ge:empty-fold` gives
`E = Row/Col ∘_EMPTY K₀`, and aligned composition lifts the fold to
`F = D_d ∘_EMPTY K₀` with `D_d = γ(D) ∘_λ (Row/Col)`.

Sorry-free.
-/

namespace SkewGluing
namespace FoldSupplied

open MarkedInner SmallOverlap OrdinaryFold

theorem empty_fold_lift {F : Diagram} {χ : Chart} (hχ : χ.IsProperLegal) (hF : χ.IsChartOf F)
    (hW : χ.ω.W = ∅) {d : ℕ} (hd : 2 ≤ d) (hdp : d < span χ.ω.E) (hdvd : d ∣ span χ.ω.E)
    {lam : ℤ} (hlam : lam = 0 ∨ lam = 1)
    (hA : ∀ k, d ≤ k → k < span χ.ω.E → completedA χ.ω.E lam k = completedA χ.ω.E lam (k - d))
    (hB : ∀ k, d ≤ k → k < span χ.ω.E → completedB χ.ω.E lam k = completedB χ.ω.E lam (k - d)) :
    ∃ (χ' ψ : Chart) (μ : MarkedInner) (γ : Diagram → Diagram) (u : ℤ × ℤ),
      ψ.IsProperLegal ∧ ψ.IsChartOf χ.ω.E ∧ ψ.period = d ∧ ψ.ω.W = ∅ ∧
      ψ.D = lineOuter (span χ.ω.E / d) lam ∧
      χ'.IsProperLegal ∧ χ'.IsChartOf F ∧ χ'.ω = ψ.ω.translate u ∧ χ'.period = d ∧ χ'.ω.W = ∅ ∧
      μ.IsLegal ∧ μ.E = ψ.D ∧ (γ = id ∨ (γ = antitranspose ∧ μ.W = ∅)) ∧
      χ'.D = μ.compose (γ χ.D) := by
  have hE : IsConnectedSkew χ.ω.E := hχ.2.2.2.1.1
  obtain ⟨ψ, hψ, hψE, hψper, -, hψW, hψD, -, -, -⟩ := empty_fold hE hd hdp hdvd rfl hlam hA hB
  have hmark : χ.ω = emptyMarkH χ.ω.E := hχ.eq_emptyMarkH hW
  have hper : χ.period = (span χ.ω.E : ℤ) := by
    change χ.ω.period = _
    rw [hmark]; exact emptyMarkH_period hE
  have hdvd' : ψ.period ∣ χ.period := by
    rw [hψper, hper]; exact Int.natCast_dvd_natCast.mpr hdvd
  obtain ⟨χ', μ, γ, u, h1, h2, h3, h4, h5, h6, h7, h8⟩ := exists_lifted_chart hχ hψ hF hψE hdvd'
  refine ⟨χ', ψ, μ, γ, u, hψ, hψE, hψper, hψW, hψD, h1, h2, h3, by rw [h4]; exact hψper, ?_, h5,
    h6, h7, h8⟩
  rw [h3, MarkedInner.translate_W, hψW]
  simp [SkewGluing.translate]

end FoldSupplied
end SkewGluing
