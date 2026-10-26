/- TODO-COPIED: adapted from
`skew-factor-gluing/lean/SkewGluing/Aligned/CaseD/Gen.lean`. -/
import GluingCore.Aligned.CaseD.ProfD

/-!
# Aligned marks, case (d): the marked heights of a composite with a case-(d) mark

Formalizes `shields-2026-skew-factor-gluing.tex`, «Equal and divisible periods»
(`eq:gluing-mixed-profile`, `eq:gluing-nested-count`).

For any legal case-(d) mark `ω` with a nonempty copy and a connected outer `C`, the height of
`C ∘_ω E` on a marked diagonal `i < w` is `height W₋ + CT_{ℓ_i}(J)` with
`ℓ_i = dLo ω i ∈ {-1, 0, 1}` the northwest offset (`alD_mixed_marked`); on a private diagonal it is
`height E + M^C_J - 1`.

Sorry-free.
-/

namespace GluingCore

namespace MarkedInner

variable {ω : MarkedInner} {C : Diagram}

theorem alD_mixed_marked (hl : ω.IsLegalNonempty) (hC : IsConnectedSkew C) (hc : ω.case = .d)
    {J i : ℤ} (hi0 : 0 ≤ i) (hi1 : i < ω.widthZ)
    (hv : ValidClass (minContent C) (maxContent C) ω.widthZ J i) :
    height (ω.compose C) (minContent ω.E + (J * ω.period + i)) =
      height ω.W (minContent ω.E + i) + alD_CT C (ω.dLo i) J := by
  have hmM : minContent C ≤ maxContent C := minContent_le (maxContent_mem hC.2.1)
  obtain ⟨s, t, hph⟩ := hl.exists_phases
  have hlt := hl.phases_lt (Or.inr hc) hph
  have hf := d_E_facts hl hc hph hi0 (by omega : i ≤ ω.widthZ - 1)
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hf
  have := mix_height_marked hl hC hc hph hlt (J := J) (a := i) hi0 hi1 (by
    unfold ValidClass at hv; omega)
  rw [this]
  unfold alD_CT
  congr 1
  by_cases h1 : i < t
  · have := f4 h1
    have : ω.dLo i = -1 := by omega
    simp [h1, this]
  · by_cases h2 : i < s
    · have := f5 (by omega)
      have := f7 h2
      have : ω.dLo i = 0 := by omega
      simp [h1, h2, this]
    · have := f6 (by omega)
      have : ω.dLo i = 1 := by omega
      simp [h1, h2, this]

theorem alD_mixed_private (hl : ω.IsLegalNonempty) (hC : IsConnectedSkew C) (hc : ω.case = .d)
    {J i : ℤ} (hi0 : ω.widthZ ≤ i) (hi1 : i < ω.period) (hJ : minContent C ≤ J ∧ J ≤ maxContent C) :
    height (ω.compose C) (minContent ω.E + (J * ω.period + i)) =
      height ω.E (minContent ω.E + i) + profM C J - 1 := by
  obtain ⟨s, t, hph⟩ := hl.exists_phases
  have hlt := hl.phases_lt (Or.inr hc) hph
  have hw := hl.width_pos
  have := (hl.mixed_profile hC hc hph hlt (J := J) (a := i) (by omega) hi1
    (Or.inl hJ)).2.1 hi0
  exact this

end MarkedInner

end GluingCore
