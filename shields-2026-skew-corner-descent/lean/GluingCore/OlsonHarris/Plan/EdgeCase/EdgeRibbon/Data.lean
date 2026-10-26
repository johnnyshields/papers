-- TODO-COPIED from skew-factor-gluing/lean/
-- SkewGluing/OlsonHarris/Plan/EdgeCase/EdgeRibbon/Data.lean
import GluingCore.OlsonHarris.Plan.EdgeCase.EdgeRibbon.Model
import GluingCore.Local.Final

/-!
# The border model of the composite of a legal mark of case (a)

Formalizes `shields-2026-skew-factor-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `eq:gluing-offsets`, `eq:gluing-bits`, `lem:gluing-local`): the hypotheses of
`BorderModel` for the composite `D ∘_ω E` of a connected outer diagram `D` and a legal mark `ω` of
case (a), nonempty or empty.  The phase `t` is the phase of the upper middle tail
(`MarkedInner.IsPhases`) for a nonempty mark and `0` for the empty mark; in both cases the greatest
content of the middle is `c₀ + q + t - 1`.

Sorry-free.
-/

set_option linter.style.openClassical false

namespace GluingCore

namespace Plan

namespace EdgeRibbon

open scoped Classical

open GluingCore.MarkedInner

theorem oRowLo_a {ω : MarkedInner} (hc : ω.case = .a) (D : Diagram) (j : ℤ) :
    ω.oRowLo D j = j * ω.rowShift + diagLo D j := by
  simp [oRowLo, hc]

/-- The border model of the composite of a nonempty legal mark of case (a). -/
theorem borderModel_nonempty {ω : MarkedInner} (h : ω.IsLegalNonempty) (hc : ω.case = .a)
    {D : Diagram} (hD : IsConnectedSkew D) :
    ∃ t : ℤ, ∃ fLo fHi : ℤ → ℤ → ℤ,
      BorderModel (ω.compose D) (minContent ω.E) ω.period ω.widthZ t (minContent D)
        (maxContent D) ω.rowShift (diagLo D) ω.lo fLo fHi ∧
      maxContent ω.middle = minContent ω.E + ω.period + t - 1 := by
  have hmix : ¬ ω.case.IsMixed := by simp [AttachCase.IsMixed, hc]
  obtain ⟨s, t, hph⟩ := h.exists_phases
  obtain ⟨hs1, hs2, ht1, ht2, hS, hT⟩ := hph
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hE := ord_E_facts h hmix
  have hT0 : ω.ordT = 0 := by simp [ordT, hc]
  have hcaps := hE.2.1 hT0
  refine ⟨t, ω.ordLo D, ω.ordHi D, ⟨ord_classRows h hD hmix, ?_, ht1, Or.inl ht2, ?_, ?_, ?_, ?_,
    ?_, ?_⟩, ?_⟩
  · intro J a ha0 haq hv
    have hp1 : (J - 1) * ω.rowShift = J * ω.rowShift - ω.rowShift := by ring
    have hlt : a < t → ω.lo (a + ω.period) = ω.rowShift + ω.lo a - 1 := by
      intro hat
      have h1 := hE.1 a ha0 (by omega)
      have h2 := (hT a ha0 (by omega)).mpr hat
      unfold TailUpper dLo dHi at h2
      unfold dLo dHi at h1
      have := h1.1 hT0
      have := h1.2.2
      omega
    have hge : t ≤ a → a < ω.widthZ → ω.lo (a + ω.period) = ω.rowShift + ω.lo a := by
      intro hta haw
      have h1 := hE.1 a ha0 (by omega)
      have h2 : ¬ ω.TailUpper a := fun hh => by have := (hT a ha0 (by omega)).mp hh; omega
      unfold TailUpper dLo dHi at h2
      unfold dLo dHi at h1
      have := h1.1 hT0
      have := h1.2.2
      omega
    have hbit : minContent D + 1 ≤ J → J ≤ maxContent D →
        diagLo D (J - 1) - diagLo D J = 0 ∨ diagLo D (J - 1) - diagLo D J = 1 :=
      fun h1 h2 => (D_bits hD h1 h2).1
    unfold ordLo rowF
    simp only [oRowLo_a hc]
    unfold ValidClass at hv
    rcases hv with hv | ⟨hv1, hv2⟩
    · split_ifs <;> omega
    · subst hv1
      simp only [add_sub_cancel_right]
      split_ifs <;> omega
  · intro a ha0 hat
    have h1 := hE.1 a ha0 (by omega)
    have h2 := (hT a ha0 (by omega)).mpr hat
    unfold TailUpper dLo dHi at h2
    unfold dLo dHi at h1
    have := h1.1 hT0
    have := h1.2.2
    omega
  · intro a hta haw
    have h1 := hE.1 a (by omega) (by omega)
    have h2 : ¬ ω.TailUpper a := fun hh => by have := (hT a (by omega) (by omega)).mp hh; omega
    unfold TailUpper dLo dHi at h2
    unfold dLo dHi at h1
    have := h1.1 hT0
    have := h1.2.2
    omega
  · intro a ha0 ha1
    exact h.bit_lo' (a := a) (b := a + 1) rfl ha0 ha1
  · have := hcaps.2.2.2
    unfold dLo at this
    simp only [zero_add] at this
    omega
  · intro _
    exact hcaps.1.2.1
  · intro J h1 h2
    exact (D_bits hD h1 h2).1
  · have hcm := h.contents_middle ⟨hs1, hs2, ht1, ht2, hS, hT⟩
    refine maxContent_eq_of (by rw [hcm, Finset.mem_Icc]; omega) fun k hk => ?_
    rw [hcm, Finset.mem_Icc] at hk
    exact hk.2

/-- The border model of the composite of the empty mark. -/
theorem borderModel_empty {ω : MarkedInner} (h : ω.IsLegalEmpty) {D : Diagram}
    (hD : IsConnectedSkew D) :
    ∃ t : ℤ, ∃ fLo fHi : ℤ → ℤ → ℤ,
      BorderModel (ω.compose D) (minContent ω.E) ω.period ω.widthZ t (minContent D)
        (maxContent D) ω.rowShift (diagLo D) ω.lo fLo fHi ∧
      maxContent ω.middle = minContent ω.E + ω.period + t - 1 := by
  have hc := h.case_a
  have hq := h.period_pos
  have hw := h.width_zero
  refine ⟨0, _, _, ⟨h.classRows hD, ?_, le_rfl, Or.inr ⟨hw, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro J a ha0 haq hv
    unfold ValidClass at hv
    unfold rowF
    simp only [oRowLo_a hc]
    split_ifs <;> omega
  · intro a ha0 hat; omega
  · intro a hta haw; omega
  · intro a ha0 ha1
    exact h.bit_lo' (a := a) (b := a + 1) rfl ha0 (by omega)
  · have := h.rowShift_eq
    omega
  · intro hpos; omega
  · intro J h1 h2
    exact (D_bits hD h1 h2).1
  · have hmid : ω.middle = ω.E := by
      have : ω.W = ∅ := h.2
      simp [middle, upper, this, translate]
    rw [hmid]
    have hsp := span_eq_of_isConnectedSkew h.1.1.1
    have h2 := h.span_eq
    omega

end EdgeRibbon

end Plan

end GluingCore
