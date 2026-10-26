import SkewGluing.SmallOverlap.EmptyFold

/-!
# Singleton marks: the end bits of the inner

Formalizes `shields-2026-skew-gluing.tex`, «Period words, line inners, and small
overlaps» (`lem:gluing-small`), the case of a root of width one.

For a legal mark of width one the lower copy is the southwest cell of `E` and the upper copy the
northeast cell.  The diagonals `0, 1, q - 1, q` of `E` are singletons, and the attachment fixes the
end bits of `E`: with `λ = 0` for a horizontal and `1` for a vertical lower attachment, and
`υ = 0` for a horizontal and `1` for a vertical upper attachment,
`A^E_1 = B^E_1 = λ` and `A^E_q = B^E_q = υ` (`lowerH_bits_one`, `lowerV_bits_one`,
`upperH_bits_one`, `upperV_bits_one`).

Sorry-free.
-/

namespace SkewGluing

open MarkedInner

namespace MarkedInner

variable {ω : MarkedInner}

/-- The singleton marks: the end bits of `E` at the lower end, horizontal attachment. -/
theorem IsLegalNonempty.lowerH_bits_one (h : ω.IsLegalNonempty) (hw : ω.widthZ = 1)
    (hH : ω.LowerH) : ω.lo 0 - ω.lo 1 = 0 ∧ ω.hi 0 - ω.hi 1 = 0 := by
  obtain ⟨-, c2, c3⟩ := h.lower_caps_H hH
  have s1 := h.lo_w_eq_hi_w
  have s0 := h.lo_zero
  rw [hw] at c2 c3 s1
  norm_num at c2 c3
  omega

theorem IsLegalNonempty.lowerV_bits_one (h : ω.IsLegalNonempty) (hw : ω.widthZ = 1)
    (hV : ω.LowerV) : ω.lo 0 - ω.lo 1 = 1 ∧ ω.hi 0 - ω.hi 1 = 1 := by
  obtain ⟨-, c2, c3⟩ := h.lower_caps_V hV
  have s1 := h.lo_w_eq_hi_w
  have s0 := h.lo_zero
  rw [hw] at c2 c3 s1
  norm_num at c2 c3
  omega

theorem IsLegalNonempty.upperH_bits_one (h : ω.IsLegalNonempty) (hw : ω.widthZ = 1)
    (hH : ω.UpperH) : ω.lo (ω.period - 1) - ω.lo ω.period = 0 ∧
      ω.hi (ω.period - 1) - ω.hi ω.period = 0 := by
  obtain ⟨-, c2, c3⟩ := h.upper_caps_H hH
  have s1 := h.lo_pred_period_eq_hi
  have s0 := h.lo_last
  rw [hw] at s0
  have e : ω.period + 1 - 1 = ω.period := by ring
  rw [e] at s0
  omega

theorem IsLegalNonempty.upperV_bits_one (h : ω.IsLegalNonempty) (hw : ω.widthZ = 1)
    (hV : ω.UpperV) : ω.lo (ω.period - 1) - ω.lo ω.period = 1 ∧
      ω.hi (ω.period - 1) - ω.hi ω.period = 1 := by
  obtain ⟨-, c2, c3⟩ := h.upper_caps_V hV
  have s1 := h.lo_pred_period_eq_hi
  have s0 := h.lo_last
  rw [hw] at s0
  have e : ω.period + 1 - 1 = ω.period := by ring
  rw [e] at s0
  omega

end MarkedInner

namespace SmallOverlap

/-! ### The boundary coding at period `p` (`eq:gluing-singleton`) -/

/-- **`eq:gluing-singleton`.**  The boundary coding of a width-one root at period `p`, on words `A`,
`B` of length `L`: the free (exceptional) residues of `A` and `B`, and the fixed values.  Here
`A 1`, `B 1` are the values at residue one and `A p`, `B p` those at the positive multiples of the
period (the paper's subscripts one and zero).

| case | free `A` | free `B` | fixed values |
|---|---|---|---|
| (a) | `0` | `1` | `A_1 = B_0 = 0` |
| (b) | `1` | `0` | `A_0 = B_1 = 1` |
| (c) | none | `0, 1` | `A_1 = 0`, `A_0 = 1` |
| (d) | `0, 1` | none | `B_1 = 1`, `B_0 = 0` |
-/
def SingletonTable (L p : ℕ) (cs : AttachCase) (A B : ℤ → ℤ) : Prop :=
  match cs with
  | .a => PeriodWords.PeriodExcept L p {0} A ∧ PeriodWords.PeriodExcept L p {1} B ∧
      A 1 = 0 ∧ B p = 0
  | .b => PeriodWords.PeriodExcept L p {1} A ∧ PeriodWords.PeriodExcept L p {0} B ∧
      A p = 1 ∧ B 1 = 1
  | .c => PeriodWords.PeriodExcept L p ∅ A ∧ PeriodWords.PeriodExcept L p {0, 1} B ∧
      A 1 = 0 ∧ A p = 1
  | .d => PeriodWords.PeriodExcept L p {0, 1} A ∧ PeriodWords.PeriodExcept L p ∅ B ∧
      B 1 = 1 ∧ B p = 0

/-- A legal mark of width one is a nonempty mark. -/
theorem _root_.SkewGluing.Chart.IsProperRoot.W_nonempty_of_width_one {χ : Chart} {F : Diagram}
    {p : ℕ} (_h : χ.IsProperRoot F p) (hw : χ.ω.width = 1) : χ.ω.W.Nonempty := by
  by_contra hne
  have : χ.ω.W = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
  have := width_eq_zero_of_eq_empty this
  omega

/-- The phases of a mark of width one are `s = 1`, `t = 0`. -/
theorem phases_one {ω : MarkedInner} {s t : ℤ} (hph : ω.IsPhases s t) (hw : ω.widthZ = 1) :
    s = 1 ∧ t = 0 := by
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := hph
  omega

/-- The first- and second-block bits at positions `1` and `p` of an ordinary width-one composite,
at the positions that are not exceptional. -/
theorem _root_.SkewGluing.Chart.IsProperRoot.ordinary_fixed_bits {χ : Chart} {F : Diagram}
    {p : ℕ} (h : χ.IsProperRoot F p) (hw : χ.ω.width = 1) (hmix : ¬ χ.ω.case.IsMixed) :
    (χ.ω.case = .a → wordA F 1 = 0 ∧ wordB F p = 0) ∧
    (χ.ω.case = .b → wordA F p = 1 ∧ wordB F 1 = 1) := by
  have hW := h.W_nonempty_of_width_one hw
  have hlegal : χ.ω.IsLegalNonempty := ⟨h.1.2.2.2, hW⟩
  have hwZ : χ.ω.widthZ = 1 := by unfold MarkedInner.widthZ; omega
  obtain ⟨s, t, hph⟩ := hlegal.exists_phases
  obtain ⟨rfl, rfl⟩ := phases_one hph hwZ
  have hD := h.1.1
  obtain ⟨hr, hN, hwq, hp2⟩ := h.arith
  have hper : χ.ω.period = (p : ℤ) := h.2.2
  have hq := hlegal.width_lt_period
  have hc := ord_classRows hlegal hD hmix
  have hmin := hlegal.minContent_compose' hD
  have hspD := span_eq_of_isConnectedSkew hD
  have hmM : minContent χ.D ≤ maxContent χ.D := minContent_le (maxContent_mem hD.2.1)
  have hsF := h.span_eq
  have hsp : 2 ≤ span F := by
    have : (0 : ℤ) ≤ χ.ω.width := by positivity
    have : (span χ.D : ℤ) ≤ span F := by nlinarith
    omega
  have hv0 : ∀ a, ValidClass (minContent χ.D) (maxContent χ.D) χ.ω.widthZ (minContent χ.D) a :=
    fun a => Or.inl ⟨le_rfl, hmM⟩
  have hv1 : ∀ a, ValidClass (minContent χ.D) (maxContent χ.D) χ.ω.widthZ
      (minContent χ.D + 1) a := fun a => Or.inl ⟨by omega, by omega⟩
  have hFw : ∀ k : ℤ, 1 ≤ k → k < (span F : ℤ) → wordA F k = wordA (χ.ω.compose χ.D) k := by
    intro k h1 h2; exact h.wordA_eq h1 h2
  have hFwB : ∀ k : ℤ, 1 ≤ k → k < (span F : ℤ) → wordB F k = wordB (χ.ω.compose χ.D) k := by
    intro k h1 h2; exact h.wordB_eq h1 h2
  have hNZ : (span F : ℤ) = (span χ.D : ℤ) * p + 1 := by rw [hN, hw]; push_cast; ring
  have hpF : (p : ℤ) < span F := by
    have : (2 : ℤ) ≤ span χ.D := by exact_mod_cast hr
    have : (2 : ℤ) ≤ p := by exact_mod_cast hp2
    nlinarith
  refine ⟨fun hca => ?_, fun hcb => ?_⟩
  · have hz : χ.ω.ordT = 0 := (ordT_eq_zero_iff hmix).mpr hca
    obtain ⟨hl, -⟩ := hlegal.attach.1 hca
    obtain ⟨b1, -⟩ := hlegal.lowerH_bits_one hwZ hl
    have e1 := hc.wordA_class' hmin (J := minContent χ.D) (a := 1) (k := 1) (by ring)
      (by omega) (by omega) (hv0 1) (fun h => by omega)
    have f1 := ord_classBitLo hlegal hD hmix hph (J := minContent χ.D) (a := 1) (by omega)
      (by omega) (hv0 1) (fun _ => by omega) ⟨fun _ => by omega, fun h => by omega⟩
    have e2 := hc.wordB_class' hmin (J := minContent χ.D + 1) (a := 0) (k := p) (by rw [hper]; ring)
      (le_refl _) (by omega) (hv1 0) (fun _ => le_refl _)
    have f2 := ord_classBitHi hlegal hD hmix hph (J := minContent χ.D + 1) (a := 0) (le_refl _)
      (by omega) (hv1 0) (fun _ => le_refl _) ⟨fun _ => by omega, fun h => by omega⟩
    refine ⟨?_, ?_⟩
    · rw [hFw 1 (by omega) (by omega), e1, f1]
      simp only [show (1 : ℤ) ≠ 0 by omega, ite_false]
      simpa using b1
    · rw [hFwB p (by omega) hpF, e2, f2]
      simp
  · have hz : χ.ω.ordT = 1 := by
      have := ordT_cases hmix
      have h0 := (ordT_eq_zero_iff hmix).not.mpr (by rw [hcb]; simp)
      omega
    obtain ⟨hl, -⟩ := hlegal.attach.2.1 hcb
    obtain ⟨-, b1⟩ := hlegal.lowerV_bits_one hwZ hl
    have e1 := hc.wordB_class' hmin (J := minContent χ.D) (a := 1) (k := 1) (by ring)
      (by omega) (by omega) (hv0 1) (fun h => by omega)
    have f1 := ord_classBitHi hlegal hD hmix hph (J := minContent χ.D) (a := 1) (by omega)
      (by omega) (hv0 1) (fun h => by omega) ⟨fun h => by omega, fun _ => by omega⟩
    have e2 := hc.wordA_class' hmin (J := minContent χ.D + 1) (a := 0) (k := p) (by rw [hper]; ring)
      (le_refl _) (by omega) (hv1 0) (fun _ => le_refl _)
    have f2 := ord_classBitLo hlegal hD hmix hph (J := minContent χ.D + 1) (a := 0) (le_refl _)
      (by omega) (hv1 0) (fun _ => le_refl _) ⟨fun h => by omega, fun _ => by omega⟩
    refine ⟨?_, ?_⟩
    · rw [hFw p (by omega) hpF, e2, f2]
      simp
    · rw [hFwB 1 (by omega) (by omega), e1, f1]
      simp only [show (1 : ℤ) ≠ 0 by omega, ite_false]
      simpa using b1

/-- **`eq:gluing-singleton`.**  The boundary words of a diagram with a proper root of width one
and period `p` satisfy the singleton table at period `p`, in the case of the root. -/
theorem _root_.SkewGluing.Chart.IsProperRoot.singleton_table {χ : Chart} {F : Diagram} {p : ℕ}
    (h : χ.IsProperRoot F p) (hw : χ.ω.width = 1) :
    SingletonTable (span F - 1) p χ.ω.case (wordA F) (wordB F) := by
  have hW := h.W_nonempty_of_width_one hw
  have hlegal : χ.ω.IsLegalNonempty := ⟨h.1.2.2.2, hW⟩
  have hwZ : χ.ω.widthZ = 1 := by unfold MarkedInner.widthZ; omega
  obtain ⟨s, t, hph⟩ := hlegal.exists_phases
  obtain ⟨rfl, rfl⟩ := phases_one hph hwZ
  have hper := h.periodic_nonempty hW hph
  have hD := h.1.1
  obtain ⟨hr, hN, hwq, hp2⟩ := h.arith
  have hperZ : χ.ω.period = (p : ℤ) := h.2.2
  have hNZ : (span F : ℤ) = (span χ.D : ℤ) * p + 1 := by rw [hN, hw]; push_cast; ring
  have hsd : (2 : ℤ) ≤ span χ.D := by exact_mod_cast hr
  have hp2' : (2 : ℤ) ≤ p := by exact_mod_cast hp2
  have hpF : (p : ℤ) < span F := by nlinarith
  have hLZ : (((span F - 1 : ℕ)) : ℤ) = (span F : ℤ) - 1 := by
    have : 1 ≤ span F := by omega
    push_cast [Nat.cast_sub this]; rfl
  cases hc : χ.ω.case
  · have hfix := (h.ordinary_fixed_bits hw (by simp [AttachCase.IsMixed, hc])).1 hc
    rw [hc] at hper
    simp only [holesA, holesB] at hper
    exact ⟨hper.1, hper.2, hfix.1, hfix.2⟩
  · have hfix := (h.ordinary_fixed_bits hw (by simp [AttachCase.IsMixed, hc])).2 hc
    rw [hc] at hper
    simp only [holesA, holesB] at hper
    exact ⟨hper.1, hper.2, hfix.1, hfix.2⟩
  · -- case (c): the word `A` has the full period `p`
    rw [hc] at hper
    simp only [holesA, holesB] at hper
    obtain ⟨-, -, -, -, c5, c6⟩ := hlegal.caps_c hD hc hph
    refine ⟨hper.1, hper.2, ?_, ?_⟩
    · have hx := periodExcept_eq_of_dvd hper.1 (by omega : 0 < p) (x := 1) (y := (span F : ℤ) - p)
        (by omega) (by linarith [hLZ]) (by omega) ⟨(span χ.D - 1 : ℤ), by linarith [hNZ]⟩
        (by simp)
      rw [hx]
      have e := h.wordA_eq (k := (span F : ℤ) - p) (by omega) (by omega)
      rw [e]
      have := c6
      rw [hperZ] at this
      have hs : span (χ.ω.compose χ.D) = span F := h.span_eq.symm
      rw [hs] at this
      exact this
    · have hx := periodExcept_eq_of_dvd hper.1 (by omega : 0 < p) (x := p) (y := (span F : ℤ) - 1)
        (by omega) (by linarith [hLZ]) (by omega) ⟨(span χ.D - 1 : ℤ), by linarith [hNZ]⟩
        (by simp)
      rw [hx]
      have e := h.wordA_eq (k := (span F : ℤ) - 1) (by omega) (by omega)
      rw [e]
      have := c5
      rw [hwZ] at this
      have hs : span (χ.ω.compose χ.D) = span F := h.span_eq.symm
      rw [hs] at this
      exact this
  · -- case (d)
    rw [hc] at hper
    simp only [holesA, holesB] at hper
    obtain ⟨-, -, -, -, c5, c6⟩ := hlegal.caps_d hD hc hph
    refine ⟨hper.1, hper.2, ?_, ?_⟩
    · rw [h.wordB_eq (by omega) (by omega)]
      have := c5
      rw [hwZ] at this
      exact this
    · rw [h.wordB_eq (by omega) hpF]
      have := c6
      rw [hperZ] at this
      exact this

end SmallOverlap
end SkewGluing
