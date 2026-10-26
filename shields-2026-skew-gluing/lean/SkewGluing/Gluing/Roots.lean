import SkewGluing.OrdinaryFold
import SkewGluing.MixedFold
import SkewGluing.SmallOverlap
import SkewGluing.Lines

/-!
# The gcd root of two roots of nondividing periods

Formalizes `shields-2026-skew-gluing.tex`, «Completion of the gluing proof» (`thm:gluing`):
the case split on two proper roots of nondividing periods with `g = gcd(p, Q) > 1`.

`Chart.IsProperLegal.exists_gcd_root` combines the constructive leaves:

* a root of width zero or one (`lem:gluing-small`, `Chart.IsProperRoot.exists_small_root_gcd`);
* two ordinary roots with widths at least two (`prop:gluing-ordinary-fold`,
  `OrdinaryPair.exists_gcd_root`);
* at least one mixed root with both widths at least two: remainder zero is impossible, an
  opposite-mixed or mixed/ordinary pair is excluded (`lem:gluing-incompatible`), and the equal
  mixed cases fold (`prop:gluing-mixed-fold`, `gluing_mixed_fold`).

The root produced is a proper legal chart of the same parent of period `g`.

Sorry-free.
-/

namespace SkewGluing

namespace Chart

/-- The period of a proper legal chart is positive, so `toNat` loses nothing. -/
theorem IsProperLegal.period_toNat {χ : Chart} (h : χ.IsProperLegal) :
    (χ.period.toNat : ℤ) = χ.period :=
  Int.toNat_of_nonneg (by have := h.2.2.2.period_pos; unfold Chart.period; omega)

theorem IsProperLegal.isProperRoot {χ : Chart} {F : Diagram} (h : χ.IsProperLegal)
    (hF : χ.IsChartOf F) : χ.IsProperRoot F χ.period.toNat :=
  ⟨h, hF, h.period_toNat.symm⟩

/-- **The gcd root.**  Two proper legal charts of one diagram `F` whose periods `p`, `Q` divide
neither one another and have `g = gcd(p, Q) > 1` give a proper legal chart of `F` of period `g`.
The case split is that of the proof of `thm:gluing`: a root of width at most one
(`lem:gluing-small`); two ordinary roots (`prop:gluing-ordinary-fold`); and otherwise a mixed
root, excluding mixed/ordinary and opposite pairs and folding the equal mixed cases
(`lem:gluing-incompatible`, `prop:gluing-mixed-fold`). -/
theorem IsProperLegal.exists_gcd_root {F : Diagram} {χ₁ χ₂ : Chart} (h₁ : χ₁.IsProperLegal)
    (h₂ : χ₂.IsProperLegal) (c₁ : χ₁.IsChartOf F) (c₂ : χ₂.IsChartOf F)
    (hnd₁ : ¬ χ₁.period.toNat ∣ χ₂.period.toNat) (hnd₂ : ¬ χ₂.period.toNat ∣ χ₁.period.toNat)
    (hg : 1 < Nat.gcd χ₁.period.toNat χ₂.period.toNat) :
    ∃ χ : Chart, χ.IsProperLegal ∧ χ.IsChartOf F ∧
      χ.period = (Nat.gcd χ₁.period.toNat χ₂.period.toNat : ℤ) := by
  have r₁ := h₁.isProperRoot c₁
  have r₂ := h₂.isProperRoot c₂
  by_cases hw₁ : χ₁.ω.width ≤ 1
  · obtain ⟨χ, hχ, -⟩ := r₁.exists_small_root_gcd r₂ hw₁ rfl hg
    exact ⟨χ, hχ.1, hχ.2.1, hχ.2.2⟩
  by_cases hw₂ : χ₂.ω.width ≤ 1
  · obtain ⟨χ, hχ, -⟩ := r₂.exists_small_root_gcd r₁ hw₂ rfl (by rwa [Nat.gcd_comm])
    refine ⟨χ, hχ.1, hχ.2.1, ?_⟩
    rw [hχ.2.2, Nat.gcd_comm]
  have hW₁ : χ₁.ω.W.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    have := MarkedInner.width_eq_zero_of_eq_empty he
    omega
  have hW₂ : χ₂.ω.W.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    have := MarkedInner.width_eq_zero_of_eq_empty he
    omega
  have T : TwoRoots F χ₁ χ₂ := ⟨h₁, h₂, c₁, c₂, hnd₁, hnd₂⟩
  by_cases hmix : χ₁.ω.case.IsMixed ∨ χ₂.ω.case.IsMixed
  · have hsame := TwoRoots.gluing_incompatible T hmix
    have hm₁ : χ₁.ω.case.IsMixed := by
      rcases hmix with h | h
      · exact h
      · rwa [← hsame] at h
    obtain ⟨χ, hχ, hF, hper, -⟩ := gluing_mixed_fold T hg hsame hm₁
    refine ⟨χ, hχ, hF, ?_⟩
    rw [← hχ.period_toNat]
    exact congrArg _ hper
  · push Not at hmix
    have hP : OrdinaryPair F χ₁ χ₂ :=
      ⟨h₁, h₂, c₁, c₂, hmix.1, hmix.2, hW₁, hW₂, hnd₁, hnd₂⟩
    obtain ⟨g, a, b, c, d, M, wg, hd⟩ := hP.exists_gcdData
    have hgeq : g = Nat.gcd χ₁.period.toNat χ₂.period.toNat := hd.g_eq
    obtain ⟨χ, hχ, hF, hper, -⟩ := hP.exists_gcd_root hd (by rw [hgeq]; exact hg)
    exact ⟨χ, hχ, hF, by rw [hper, hgeq]⟩

end Chart

end SkewGluing
