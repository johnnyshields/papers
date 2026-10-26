-- TODO-COPIED: skew-factor-gluing/lean/SkewGluing/Coding/Periodic.lean
import SkewGluing.Coding.Mixed

/-!
# The parent boundary words are periodic off the holes

Formalizes `shields-2026-skew-factor-gluing.tex`, «Diagonal geometry» (`lem:gluing-coding`,
`eq:gluing-holes`).

For a legal mark with a nonempty copy and a connected outer `D`, the boundary words of
`F = D ∘_ω E` on the positions `1, …, N - 1` have period `q` except at the residues of the table
`eq:gluing-holes`, in the form `PeriodWords.PeriodExcept` of `lem:gluing-periods`.  This file does
cases (a), (b), (d); case (c) is in `SkewGluing.Coding.CaseC` and the empty mark in
`SkewGluing.Coding.Empty`.

Sorry-free.
-/

namespace SkewGluing

/-- The exceptional residues of the first-row word `A` in the table `eq:gluing-holes`, for the
middle phases `s, t`. -/
def holesA (x : AttachCase) (s t : ℤ) : Finset ℤ :=
  match x with
  | .a => {t}
  | .b => {s}
  | .c => ∅
  | .d => {t, s}

/-- The exceptional residues of the last-row word `B` in the table `eq:gluing-holes`, for the
middle phases `s, t`. -/
def holesB (x : AttachCase) (s t : ℤ) : Finset ℤ :=
  match x with
  | .a => {s}
  | .b => {t}
  | .c => {t, s}
  | .d => ∅

namespace MarkedInner

variable {ω : MarkedInner} {D : Diagram}

theorem IsLegalNonempty.span_compose_eq (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D) :
    (span (ω.compose D) : ℤ) = (maxContent D - minContent D + 1) * ω.period + ω.widthZ := by
  rw [span_compose hD h.1, span_eq_of_isConnectedSkew hD]
  rfl

theorem IsLegalNonempty.minContent_compose' (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D) :
    minContent (ω.compose D) = minContent ω.E + minContent D * ω.period :=
  h.1.minContent_compose hD

/-- **`lem:gluing-coding`, holes, cases (a) and (b).**  **Differs from the paper's route.**  The
paper derives case (b) from case (a) by antitransposition; here both ordinary cases are read from
the same closed forms of the rows of the composite. -/
theorem IsLegalNonempty.periodExcept_ordinary (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D)
    (hmix : ¬ ω.case.IsMixed) {s t : ℤ} (hph : ω.IsPhases s t) :
    PeriodWords.PeriodExcept (span (ω.compose D) - 1) ω.period.toNat
      (holesA ω.case s t) (wordA (ω.compose D)) ∧
    PeriodWords.PeriodExcept (span (ω.compose D) - 1) ω.period.toNat
      (holesB ω.case s t) (wordB (ω.compose D)) := by
  have hmM : minContent D ≤ maxContent D := minContent_le (maxContent_mem hD.2.1)
  have hc := ord_classRows h hD hmix
  have hmin := h.minContent_compose' hD
  have hN := h.span_compose_eq hD
  have hz := ordT_eq_zero_iff hmix
  have hcc : ω.case = .a ∨ ω.case = .b := by
    unfold AttachCase.IsMixed at hmix
    cases hh : ω.case <;> simp_all
  have hq := h.width_lt_period
  have hw := h.width_pos
  refine ⟨periodExcept_of_classBit hc hN (fun J a h0 h1 hv hJ => hc.wordA_class hmin h0 h1 hv hJ)
    ?_, periodExcept_of_classBit hc hN
      (fun J a h0 h1 hv hJ => hc.wordB_class hmin h0 h1 hv hJ) ?_⟩
  · intro J a h0 h1 hS hv hv' hJ
    have hJ' : a = 0 → minContent D + 1 ≤ J + 1 := fun _ => by
      have := validClass_ge hmM hv; omega
    rcases hcc with hca | hcb
    · have hex : (ω.ordT = 0 → a ≠ t) ∧ (ω.ordT = 1 → a ≠ s) := by
        have := (hz.mpr hca)
        refine ⟨fun _ => ?_, fun h1 => by omega⟩
        simpa [holesA, hca] using hS
      rw [ord_classBitLo h hD hmix hph h0 h1 hv hJ hex,
        ord_classBitLo h hD hmix hph h0 h1 hv' hJ' hex]
    · have hex : (ω.ordT = 0 → a ≠ t) ∧ (ω.ordT = 1 → a ≠ s) := by
        have hne : ¬ ω.ordT = 0 := fun h0' => by
          have := hz.mp h0'
          rw [hcb] at this
          cases this
        refine ⟨fun h0' => absurd h0' hne, fun _ => ?_⟩
        simpa [holesA, hcb] using hS
      rw [ord_classBitLo h hD hmix hph h0 h1 hv hJ hex,
        ord_classBitLo h hD hmix hph h0 h1 hv' hJ' hex]
  · intro J a h0 h1 hS hv hv' hJ
    have hJ' : a = 0 → minContent D + 1 ≤ J + 1 := fun _ => by
      have := validClass_ge hmM hv; omega
    rcases hcc with hca | hcb
    · have hex : (ω.ordT = 0 → a ≠ s) ∧ (ω.ordT = 1 → a ≠ t) := by
        have := (hz.mpr hca)
        refine ⟨fun _ => ?_, fun h1 => by omega⟩
        simpa [holesB, hca] using hS
      rw [ord_classBitHi h hD hmix hph h0 h1 hv hJ hex,
        ord_classBitHi h hD hmix hph h0 h1 hv' hJ' hex]
    · have hex : (ω.ordT = 0 → a ≠ s) ∧ (ω.ordT = 1 → a ≠ t) := by
        have hne : ¬ ω.ordT = 0 := fun h0' => by
          have := hz.mp h0'
          rw [hcb] at this
          cases this
        refine ⟨fun h0' => absurd h0' hne, fun _ => ?_⟩
        simpa [holesB, hcb] using hS
      rw [ord_classBitHi h hD hmix hph h0 h1 hv hJ hex,
        ord_classBitHi h hD hmix hph h0 h1 hv' hJ' hex]

/-- **`lem:gluing-coding`, holes, case (d).** -/
theorem IsLegalNonempty.periodExcept_d (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D)
    (hcd : ω.case = .d) {s t : ℤ} (hph : ω.IsPhases s t) :
    PeriodWords.PeriodExcept (span (ω.compose D) - 1) ω.period.toNat
      (holesA ω.case s t) (wordA (ω.compose D)) ∧
    PeriodWords.PeriodExcept (span (ω.compose D) - 1) ω.period.toNat
      (holesB ω.case s t) (wordB (ω.compose D)) := by
  have hmM : minContent D ≤ maxContent D := minContent_le (maxContent_mem hD.2.1)
  have hlt := h.phases_lt (Or.inr hcd) hph
  have hc := mix_classRows h hD hcd hph hlt
  have hmin := h.minContent_compose' hD
  have hN := h.span_compose_eq hD
  have hq := h.width_lt_period
  have hw := h.width_pos
  refine ⟨periodExcept_of_classBit hc hN (fun J a h0 h1 hv hJ => hc.wordA_class hmin h0 h1 hv hJ)
    ?_, periodExcept_of_classBit hc hN
      (fun J a h0 h1 hv hJ => hc.wordB_class hmin h0 h1 hv hJ) ?_⟩
  · intro J a h0 h1 hS hv hv' hJ
    have hJ' : a = 0 → minContent D + 1 ≤ J + 1 := fun _ => by
      have := validClass_ge hmM hv; omega
    have hS' : a ≠ t ∧ a ≠ s := by
      simpa [holesA, hcd, not_or] using hS
    exact mix_classBitLo_periodic h hD hcd hph h0 h1 hv hv' hJ hS'.1 hS'.2
  · intro J a h0 h1 hS hv hv' hJ
    rw [mix_classBitHi h hcd J a h0 h1, mix_classBitHi h hcd (J + 1) a h0 h1]

end MarkedInner

end SkewGluing
