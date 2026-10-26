/- TODO-COPIED: adapted from
`skew-factor-gluing/lean/SkewGluing/Lines/ChartRoot.lean`. -/
import GluingCore.Lines.RootData
import GluingCore.Lines.InnerLine

/-!
# The word data of a proper root

Formalizes `shields-2026-skew-factor-gluing.tex`, «Period words, line inners, and small
overlaps» (`lem:gluing-lines`), first assertion: the input of the word-level argument
(`GluingCore.Lines.RootData`) is supplied by `lem:gluing-coding`, `lem:gluing-local` and the first
window of the composite.

`rootData_of_chart`: a proper legal chart `χ` of period `q` has `RootData` on the boundary words of
its parent, with `rowE`, `colE` the statements that its inner is a row, a column, and `mix` the
statement that its case is mixed.

Sorry-free.
-/

namespace GluingCore

namespace Lines

open MarkedInner PeriodWords

variable {ω : MarkedInner} {D : Diagram}

/-- The sums of the two words of `E` over `[1, q - 1]` agree: the diagonal `q - 1` is a
singleton. -/
theorem sum_first_eq (hω : ω.IsLegal) (hD : IsConnectedSkew D) {q : ℕ}
    (hq : (q : ℤ) = ω.period) (hsing : diagLo ω.E (minContent ω.E + ((q - 1 : ℕ) : ℤ)) =
      diagHi ω.E (minContent ω.E + ((q - 1 : ℕ) : ℤ))) :
    ∑ x ∈ Finset.Icc (1 : ℤ) ((q : ℤ) - 1), wordA (ω.compose D) x =
      ∑ x ∈ Finset.Icc (1 : ℤ) ((q : ℤ) - 1), wordB (ω.compose D) x := by
  have hq1 : 1 ≤ q := by have := hω.period_pos; omega
  have hcast : (((q - 1 : ℕ)) : ℤ) = (q : ℤ) - 1 := by omega
  rw [Finset.sum_congr rfl (fun x hx => hω.wordA_compose_first hD
      (Finset.mem_Icc.mp hx).1 (by have := (Finset.mem_Icc.mp hx).2; omega)),
    Finset.sum_congr rfl (fun x hx => hω.wordB_compose_first hD
      (Finset.mem_Icc.mp hx).1 (by have := (Finset.mem_Icc.mp hx).2; omega))]
  rw [← hcast]
  exact (sum_wordA_eq_sum_wordB_iff hω.1.1 _).mpr hsing

/-- The numerical data of a proper legal chart: `q ≥ 2`, `w < q`, `r = N_D ≥ 2` and
`N = r q + w`. -/
theorem chart_numerics {χ : Chart} (hχ : χ.IsProperLegal) :
    2 ≤ χ.period.toNat ∧ χ.ω.width < χ.period.toNat ∧ 2 ≤ span χ.D ∧
      span χ.parent = span χ.D * χ.period.toNat + χ.ω.width := by
  obtain ⟨hD, hDc, hEc, hω⟩ := hχ
  have hq := hω.period_pos
  have hwq := hω.2.2.1.2
  have hspE := hω.1.span_eq
  have hE2 := two_le_span_of_two_le_card hω.1.1 hEc
  have hD2 := two_le_span_of_two_le_card hD hDc
  have hN := span_compose hD hω
  have hqt : (χ.period.toNat : ℤ) = χ.period := Int.toNat_of_nonneg hq.le
  have hper : χ.period = χ.ω.period := rfl
  refine ⟨by omega, by omega, hD2, ?_⟩
  unfold Chart.parent
  have : ((span (χ.ω.compose χ.D) : ℕ) : ℤ) =
      ((span χ.D * χ.period.toNat + χ.ω.width : ℕ) : ℤ) := by
    push_cast
    rw [hN, hqt]
    rfl
  exact_mod_cast this

/-- The bits of the composite on `[1, q - 1]` are those of the inner. -/
theorem bits_inner_of_parent (hω : ω.IsLegal) (hD : IsConnectedSkew D) {q : ℕ}
    (hq : (q : ℤ) = ω.period) {ε : ℤ}
    (hz : ∀ x ∈ Finset.Icc (1 : ℤ) ((q : ℤ) - 1),
      wordA (ω.compose D) x = ε ∧ wordB (ω.compose D) x = ε) :
    ∀ x ∈ Finset.Icc (1 : ℤ) ((q : ℤ) - 1), wordA ω.E x = ε ∧ wordB ω.E x = ε := by
  intro x hx
  have hx' := Finset.mem_Icc.mp hx
  rw [← hω.wordA_compose_first hD hx'.1 (by omega), ← hω.wordB_compose_first hD hx'.1 (by omega)]
  exact hz x hx

/-- **The data of an ordinary root with a nonempty mark** (cases (a), (b)). -/
theorem ordRoot_nonempty (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D)
    (hmix : ¬ ω.case.IsMixed) :
    OrdRoot (wordA (ω.compose D)) (wordB (ω.compose D)) (span (ω.compose D))
      ω.period.toNat ω.width (IsRowDiagram ω.E) (IsColumnDiagram ω.E) := by
  obtain ⟨s, t, hph⟩ := h.exists_phases
  have hcod := h.gluing_coding_periodic hD hph
  have hq := h.1.period_toNat_cast
  have hqw := h.width_lt_period
  have hwpos := h.width_pos
  have hwZ : (ω.width : ℤ) = ω.widthZ := rfl
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph
  have hcast : (((ω.period.toNat - 1 : ℕ)) : ℤ) = (ω.period.toNat : ℤ) - 1 := by omega
  have hsE : diagLo ω.E (minContent ω.E + (ω.period - 1)) =
      diagHi ω.E (minContent ω.E + (ω.period - 1)) := h.lo_pred_period_eq_hi
  have hsum := sum_first_eq h.1 hD hq (by rw [hcast, hq]; exact hsE)
  have hmid : ∀ k, 1 ≤ k → k ≤ ω.widthZ → k ∈ Finset.Icc (1 : ℤ) ((ω.period.toNat : ℤ) - 1) :=
    fun k h1 h2 => by rw [Finset.mem_Icc]; omega
  have hcases : ω.case = .a ∨ ω.case = .b := by
    cases hc : ω.case <;> simp_all [AttachCase.IsMixed]
  rcases hcases with hca | hcb
  · have hc := h.caps_a hD hca hph
    rw [hca] at hcod
    refine ⟨t, s, ht1, by omega, by omega, hs2, hcod.1, hcod.2, hc.1, fun _ => hc.2.1, hsum,
      ?_, ?_⟩
    · intro hz
      have hzE := bits_inner_of_parent h.1 hD hq hz
      have ht0 : t = 0 := by
        by_contra hne
        have := hc.1 (by omega)
        have := (hz t (hmid t (by omega) (by omega))).1
        omega
      exact h.isRowDiagram_of_prefix hca hph ht0 hq hzE
    · intro hz
      exfalso
      have := (hz s (hmid s hs1 hs2)).2
      have := hc.2.1
      omega
  · have hc := h.caps_b hD hcb hph
    rw [hcb] at hcod
    refine ⟨s, t, by omega, hs2, ht1, by omega, hcod.1, hcod.2, fun _ => hc.2.1, hc.1, hsum,
      ?_, ?_⟩
    · intro hz
      exfalso
      have := (hz s (hmid s hs1 hs2)).1
      have := hc.2.1
      omega
    · intro hz
      have hzE := bits_inner_of_parent h.1 hD hq hz
      have ht0 : t = 0 := by
        by_contra hne
        have := hc.1 (by omega)
        have := (hz t (hmid t (by omega) (by omega))).2
        omega
      exact h.isColumnDiagram_of_prefix hcb hph ht0 hq hzE

/-- **The data of an ordinary root with the empty mark** (width zero). -/
theorem ordRoot_empty (h : ω.IsLegalEmpty) (hD : IsConnectedSkew D) :
    OrdRoot (wordA (ω.compose D)) (wordB (ω.compose D)) (span (ω.compose D))
      ω.period.toNat ω.width (IsRowDiagram ω.E) (IsColumnDiagram ω.E) := by
  have hq := h.1.period_toNat_cast
  have hw : ω.width = 0 := by
    have := h.width_zero
    unfold widthZ at this
    omega
  have hqpos := h.period_pos
  have hcast : (((ω.period.toNat - 1 : ℕ)) : ℤ) = (ω.period.toNat : ℤ) - 1 := by omega
  have hE := h.1.1.1
  have h' := isConnectedSkew_iff_diagonal.mp hE
  have hsp := span_eq_of_isConnectedSkew hE
  have hspE := h.span_eq
  have hsE : diagLo ω.E (minContent ω.E + (ω.period - 1)) =
      diagHi ω.E (minContent ω.E + (ω.period - 1)) := by
    have e : minContent ω.E + (ω.period - 1) = maxContent ω.E := by omega
    rw [e]
    exact h'.2.2.2.2 _ (maxContent_mem h'.1) (Or.inr (fun hm => by have := le_maxContent hm; omega))
  have hsum := sum_first_eq h.1 hD hq (by rw [hcast, hq]; exact hsE)
  obtain ⟨hpA, hpB⟩ := h.periodExcept hD
  refine ⟨0, 0, le_refl _, by omega, le_refl _, by omega, hpA, hpB, fun h => absurd h (by omega),
    fun h => absurd h (by omega), hsum, fun hz => ?_, fun hz => ?_⟩
  · exact h.isRowDiagram_of_prefix hq (bits_inner_of_parent h.1 hD hq hz)
  · exact h.isColumnDiagram_of_prefix hq (bits_inner_of_parent h.1 hD hq hz)

/-- The two private positions of a mixed root lie in `[1, N - 1]`. -/
theorem private_positions (h : ω.IsLegalNonempty) {N : ℕ}
    (hr : 2 ≤ span D) (hN : span (ω.compose D) = span D * ω.period.toNat + ω.width)
    (hNN : N = span (ω.compose D)) :
    (ω.widthZ ∈ Finset.Icc (1 : ℤ) ((N : ℤ) - 1) ∧ ω.period ∈ Finset.Icc (1 : ℤ) ((N : ℤ) - 1)) ∧
      ((N : ℤ) - ω.widthZ ∈ Finset.Icc (1 : ℤ) ((N : ℤ) - 1) ∧
        (N : ℤ) - ω.period ∈ Finset.Icc (1 : ℤ) ((N : ℤ) - 1)) := by
  have hq := h.1.period_toNat_cast
  have hqw := h.width_lt_period
  have hwpos := h.width_pos
  have hwZ : (ω.width : ℤ) = ω.widthZ := rfl
  have h2 : 2 * ω.period.toNat ≤ span D * ω.period.toNat := Nat.mul_le_mul_right _ hr
  subst hNN
  simp only [Finset.mem_Icc]
  omega

/-- **The data of a mixed root of case (d).** -/
theorem mixedRoot_d (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D) (hcd : ω.case = .d)
    (hr : 2 ≤ span D) (hN : span (ω.compose D) = span D * ω.period.toNat + ω.width) :
    MixedRoot (wordB (ω.compose D)) (wordA (ω.compose D)) (span (ω.compose D))
      ω.period.toNat ω.width ω.widthZ ω.period := by
  obtain ⟨s, t, hph⟩ := h.exists_phases
  have hcod := h.gluing_coding_periodic hD hph
  have hc := h.caps_d hD hcd hph
  have hq := h.1.period_toNat_cast
  have hpos := private_positions h hr hN rfl
  have hwpos := h.width_pos
  have hwZ : (ω.width : ℤ) = ω.widthZ := rfl
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph
  rw [hcd] at hcod
  have hwq : ω.widthZ = ((ω.width : ℕ) : ℤ) := rfl
  refine ⟨by omega, ⟨{t, s}, Finset.card_le_two, ?_, hcod.1⟩, hcod.2, hpos.1.1, hpos.1.2,
    hc.2.2.2.2.1, ?_⟩
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> omega
  · have := hc.2.2.2.2.2
    exact this

/-- **The data of a mixed root of case (c).** -/
theorem mixedRoot_c (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D) (hcc : ω.case = .c)
    (hr : 2 ≤ span D) (hN : span (ω.compose D) = span D * ω.period.toNat + ω.width) :
    MixedRoot (wordA (ω.compose D)) (wordB (ω.compose D)) (span (ω.compose D))
      ω.period.toNat ω.width ((span (ω.compose D) : ℤ) - ω.widthZ)
        ((span (ω.compose D) : ℤ) - ω.period) := by
  obtain ⟨s, t, hph⟩ := h.exists_phases
  have hcod := h.gluing_coding_periodic hD hph
  have hc := h.caps_c hD hcc hph
  have hq := h.1.period_toNat_cast
  have hpos := private_positions h hr hN rfl
  have hwpos := h.width_pos
  have hwZ : (ω.width : ℤ) = ω.widthZ := rfl
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph
  rw [hcc] at hcod
  refine ⟨by omega, ⟨{t, s}, Finset.card_le_two, ?_, hcod.2⟩, hcod.1, hpos.2.1, hpos.2.2,
    hc.2.2.2.2.1, hc.2.2.2.2.2⟩
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl <;> omega

/-- **The word data of a proper legal chart.**  A proper legal chart `χ` of period `q` has
`RootData` on the boundary words of its parent: its inner is a row (`rowE`), respectively a column
(`colE`), as far as the first period of the parent is constant, and the chart is mixed exactly when
`mix`. -/
theorem rootData_of_chart {χ : Chart} (hχ : χ.IsProperLegal) :
    RootData (wordA χ.parent) (wordB χ.parent) (span χ.parent) χ.period.toNat
      (IsRowDiagram χ.ω.E) (IsColumnDiagram χ.ω.E) χ.ω.case.IsMixed := by
  obtain ⟨hq2, hwq, hr2, hN⟩ := chart_numerics hχ
  obtain ⟨hD, hDc, hEc, hω⟩ := hχ
  have hper : χ.period = χ.ω.period := rfl
  have hpar : χ.parent = χ.ω.compose χ.D := rfl
  rw [hpar]
  rw [hpar] at hN
  rw [hper] at hq2 hwq hN ⊢
  have hqcast := hω.period_toNat_cast
  refine ⟨hq2, χ.ω.width, span χ.D, hwq, hr2, hN, ?_⟩
  by_cases hW : χ.ω.W.Nonempty
  · have h : χ.ω.IsLegalNonempty := ⟨hω, hW⟩
    have hcases : χ.ω.case = .a ∨ χ.ω.case = .b ∨ χ.ω.case = .c ∨ χ.ω.case = .d := by
      cases χ.ω.case <;> simp
    rcases hcases with hc | hc | hc | hc
    · have hmix : ¬ χ.ω.case.IsMixed := by simp [AttachCase.IsMixed, hc]
      exact Or.inl ⟨hmix, ordRoot_nonempty h hD hmix⟩
    · have hmix : ¬ χ.ω.case.IsMixed := by simp [AttachCase.IsMixed, hc]
      exact Or.inl ⟨hmix, ordRoot_nonempty h hD hmix⟩
    · have hmix : χ.ω.case.IsMixed := by simp [AttachCase.IsMixed, hc]
      refine Or.inr ⟨hmix, Or.inr ?_⟩
      have := mixedRoot_c h hD hc hr2 hN
      rw [hqcast]
      exact this
    · have hmix : χ.ω.case.IsMixed := by simp [AttachCase.IsMixed, hc]
      refine Or.inr ⟨hmix, Or.inl ?_⟩
      have := mixedRoot_d h hD hc hr2 hN
      rw [hqcast]
      exact this
  · have hWe : χ.ω.W = ∅ := Finset.not_nonempty_iff_eq_empty.mp hW
    have h : χ.ω.IsLegalEmpty := ⟨hω, hWe⟩
    have hmix : ¬ χ.ω.case.IsMixed := by simp [AttachCase.IsMixed, h.case_a]
    exact Or.inl ⟨hmix, ordRoot_empty h hD⟩

end Lines

end GluingCore
