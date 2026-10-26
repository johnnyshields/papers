import SkewGluing.Aligned.Statement
import SkewGluing.Aligned.Lattice
import SkewGluing.Invariance
import SkewGluing.Aligned.InnerFactor.Final

/-!
# The inner factor of a divisible chart

Formalizes `shields-2026-skew-gluing.tex`, «Equal and divisible periods»
(`prop:gluing-divisible`), the first assertion: if `F = D ∘_ω E = C ∘_η B` are proper legal
charts of periods `q < Q` with `q ∣ Q`, then `B = V ∘_ω E` for a connected `V` with at least two
cells.

The construction follows the paper: the first and the last `Q` diagonals of `F` are the two
windows of `B`, they repeat the diagonals `[b, a - 1]` of `D` (`Q = a q`, `b q + w` the width of
`η`), and `V` is the union of the aligned outer pieces (`SkewGluing.innerFactor`).  The alignment
reads the private residue `w` of the diagonals of `F` for an ordinary mark, and the heights
`M_j` and overlaps `S_j` on the private residue `w` and a marked residue meeting neither middle
tail for case (d) (`SkewGluing.PerData.factorData_ord`, `SkewGluing.PerData.factorData_d`);
case (c) follows by rotation.  `V ∘_ω E` and `B` are shown to be translates by the uniqueness of
`lem:gluing-local` (3) from their two windows (`eq_translate_of_windows`), where the windows of
`V ∘_ω E` are read by locality of composition (`SkewGluing.FactorData.mem_compose_iff_prefix`,
`SkewGluing.FactorData.mem_compose_iff_suffix`).

Sorry-free.
-/

namespace SkewGluing

namespace MarkedInner

/-- `prop:gluing-divisible`, the inner factor: if `F = D ∘_ω E = C ∘_η B` are proper legal
charts of periods `q < Q` with `q ∣ Q`, then `B = V ∘_ω E` (up to translation) for a connected
`V` with at least two cells. -/
theorem exists_inner_factor_proof {F : Diagram} {χ₁ χ₂ : Chart} (h₁ : χ₁.IsProperLegal)
    (h₂ : χ₂.IsProperLegal) (hF₁ : χ₁.IsChartOf F) (hF₂ : χ₂.IsChartOf F)
    (hlt : χ₁.period < χ₂.period) (hdiv : χ₁.period ∣ χ₂.period) :
    ∃ (V : Diagram) (t : ℤ × ℤ), IsConnectedSkew V ∧ 2 ≤ V.card ∧
      χ₂.ω.E = SkewGluing.translate t (χ₁.ω.compose V) := by
  obtain ⟨hD, -, -, hω⟩ := h₁
  obtain ⟨hC, -, -, hη⟩ := h₂
  obtain ⟨s₁, hs₁⟩ := hF₁
  obtain ⟨s₂, hs₂⟩ := hF₂
  have hs₁' : F = SkewGluing.translate s₁ (χ₁.ω.compose χ₁.D) := hs₁
  have hs₂' : F = SkewGluing.translate s₂ (χ₂.ω.compose χ₂.D) := hs₂
  have hFG : χ₁.ω.compose χ₁.D =
      SkewGluing.translate (-s₁ + s₂) (χ₂.ω.compose χ₂.D) := by
    have e1 : SkewGluing.translate (-s₁) F = χ₁.ω.compose χ₁.D := by
      rw [hs₁', SkewGluing.translate_translate]; simp [SkewGluing.translate_zero]
    rw [← e1, hs₂', SkewGluing.translate_translate]
  have hlt' : χ₁.ω.period < χ₂.ω.period := hlt
  have hdiv' : χ₁.ω.period ∣ χ₂.ω.period := hdiv
  by_cases hc : χ₁.ω.case = .c
  · -- case (c) by rotation
    have hFG' : χ₁.ω.rotate.compose (SkewGluing.rotate χ₁.D) =
        SkewGluing.translate (-(-s₁ + s₂))
          (χ₂.ω.rotate.compose (SkewGluing.rotate χ₂.D)) := by
      rw [rotate_compose hD.2.1, rotate_compose hC.2.1, hFG, rotate_translate_diagram]
    obtain ⟨V', t', hV', hcard', hE'⟩ := exists_inner_factor_core (isLegal_rotate hω)
      (by rw [rotate_case_d hc]; decide) (isConnectedSkew_rotate hD) (isLegal_rotate hη)
      (isConnectedSkew_rotate hC) hFG' (by rw [period_rotate, period_rotate]; exact hlt')
      (by rw [period_rotate, period_rotate]; exact hdiv')
    refine ⟨SkewGluing.rotate V', ?_, isConnectedSkew_rotate hV', ?_, ?_⟩
    · exact -t'
    · rw [SkewGluing.rotate, Finset.card_image_of_injective _ neg_injective]; exact hcard'
    · have hV'ne : (SkewGluing.rotate V').Nonempty := hV'.2.1.image _
      have e : χ₁.ω.rotate.compose V' =
          SkewGluing.rotate (χ₁.ω.compose (SkewGluing.rotate V')) := by
        rw [← rotate_compose hV'ne, SkewGluing.rotate_rotate]
      rw [e, rotate_E] at hE'
      have := congrArg SkewGluing.rotate hE'
      rw [SkewGluing.rotate_rotate, rotate_translate_diagram, SkewGluing.rotate_rotate] at this
      exact this
  · exact exists_inner_factor_core hω hc hD hη hC hFG hlt' hdiv'

end MarkedInner

end SkewGluing
