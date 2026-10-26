import SkewGluing.MixedPairs.Periodic

/-!
# Pairs involving mixed charts

Formalizes `shields-2026-skew-gluing.tex`, «Pairs involving mixed charts»
(`lem:gluing-collision`, `lem:gluing-incompatible`, and the paragraph opening the subsection:
the fixed boundary of a mixed chart becomes periodic, and mixed pairs at remainder zero are
impossible).

`TwoRoots F χ₁ χ₂` is the standing setting of the subsection: two proper legal charts of the
parent `F` (up to translation) whose periods do not divide one another.  With `g = gcd p Q`, where
`p` and `Q` are the periods:

* `TwoRoots.fixed_boundary_d`, `TwoRoots.fixed_boundary_c`: the fixed boundary word of a mixed chart
  (`B` for case (d), `A` for case (c)) has period `g`;
* `TwoRoots.mixed_pairs_remainder_zero`: if `g ∣ N_F` then neither chart is mixed;
* `gluing_collision` (`lem:gluing-collision`): for a case-(d) chart `χ` of `F` with middle phases
  `s, t` and period a multiple of `g`, if `N_F = M g + w_g` with `0 < w_g < g`, the word `B` is
  `g`-periodic and `A` is `g`-periodic outside one residue `R`, then `s` and `t` are not both
  congruent to `R`;
* `TwoRoots.gluing_incompatible_mixed_ordinary`, `TwoRoots.gluing_incompatible_opposite` and
  `TwoRoots.gluing_incompatible` (`lem:gluing-incompatible`): a mixed/ordinary pair and an
  opposite-mixed pair are impossible; so a pair with a mixed chart has equal cases.

The paragraph and the lemmas sit under the standing assumption `g > 1`; the arguments below do not
use it (at `g = 1` every remainder is zero), so the statements hold for every nondividing pair.  The
proofs are on bit words (`SkewGluing.MixedPairs.Periodic`); case (c) is reduced to case (d) by
rotating both charts.

Sorry-free.
-/

namespace SkewGluing

/-- **The standing setting of «Pairs involving mixed charts».**  Two proper legal charts `χ₁`, `χ₂`
of the parent `F` (up to translation), neither period dividing the other. -/
structure TwoRoots (F : Diagram) (χ₁ χ₂ : Chart) : Prop where
  proper₁ : χ₁.IsProperLegal
  proper₂ : χ₂.IsProperLegal
  chart₁ : χ₁.IsChartOf F
  chart₂ : χ₂.IsChartOf F
  not_dvd₁ : ¬ χ₁.ω.period.toNat ∣ χ₂.ω.period.toNat
  not_dvd₂ : ¬ χ₂.ω.period.toNat ∣ χ₁.ω.period.toNat

/-- The boundary coding of a proper legal chart `χ` of `F`, with given middle phases, on the words
of `F` itself (the words of a translate of the parent agree with those of the parent). -/
theorem Chart.IsProperLegal.mixFoldCoding_of_chartOf {F : Diagram} {χ : Chart}
    (h : χ.IsProperLegal) (hF : χ.IsChartOf F) :
    (∃ s t : ℤ, MixFoldCoding (wordA F) (wordB F) (span F) χ.ω.period.toNat χ.ω.width
      χ.ω.case s t) ∧ ∀ s t : ℤ, χ.ω.W.Nonempty → χ.ω.IsPhases s t →
      MixFoldCoding (wordA F) (wordB F) (span F) χ.ω.period.toNat χ.ω.width χ.ω.case s t := by
  obtain ⟨v, hv⟩ := hF
  have hP : IsConnectedSkew χ.parent := h.2.2.2.isConnectedSkew_compose h.1
  have hs : span F = span χ.parent := by rw [hv, span_translate]
  have transfer : ∀ {s t : ℤ}, MixFoldCoding (wordA χ.parent) (wordB χ.parent) (span χ.parent)
      χ.ω.period.toNat χ.ω.width χ.ω.case s t →
      MixFoldCoding (wordA F) (wordB F) (span F) χ.ω.period.toNat χ.ω.width χ.ω.case s t := by
    intro s t c
    rw [hs]
    refine c.of_agree (fun k h1 h2 => ?_) (fun k h1 h2 => ?_)
    · rw [hv]; exact (wordA_translate hP v h1 (by omega)).symm
    · rw [hv]; exact (wordB_translate hP v h1 (by omega)).symm
  refine ⟨?_, fun s t hW hph => transfer (h.mixFoldCoding_nonempty hW hph)⟩
  obtain ⟨s, t, c⟩ := h.mixFoldCoding
  exact ⟨s, t, transfer c⟩

namespace TwoRoots

variable {F : Diagram} {χ₁ χ₂ : Chart}

theorem symm (T : TwoRoots F χ₁ χ₂) : TwoRoots F χ₂ χ₁ :=
  ⟨T.proper₂, T.proper₁, T.chart₂, T.chart₁, T.not_dvd₂, T.not_dvd₁⟩

theorem chart_rotate {χ : Chart} (h : χ.IsProperLegal) (hF : χ.IsChartOf F) :
    χ.rotate.IsChartOf (rotate F) := by
  obtain ⟨t, ht⟩ := hF
  refine ⟨-t, ?_⟩
  rw [ht, rotate_translate_eq, Chart.parent_rotate h]

/-- Rotating both charts gives two roots of the rotated parent. -/
theorem rotate (T : TwoRoots F χ₁ χ₂) : TwoRoots (SkewGluing.rotate F) χ₁.rotate χ₂.rotate :=
  ⟨T.proper₁.rotate, T.proper₂.rotate, chart_rotate T.proper₁ T.chart₁,
    chart_rotate T.proper₂ T.chart₂, T.not_dvd₁, T.not_dvd₂⟩

/-- The boundary codings of the two charts on the words of the common parent. -/
theorem codings (T : TwoRoots F χ₁ χ₂) :
    (∃ s t : ℤ, MixFoldCoding (wordA F) (wordB F) (span F) χ₁.ω.period.toNat χ₁.ω.width
      χ₁.ω.case s t) ∧
    (∃ s t : ℤ, MixFoldCoding (wordA F) (wordB F) (span F) χ₂.ω.period.toNat χ₂.ω.width
      χ₂.ω.case s t) ∧ MixFoldWordsOK (wordA F) (wordB F) (span F) := by
  have hF : IsConnectedSkew F := by
    obtain ⟨v, hv⟩ := T.chart₁
    rw [hv]
    exact isConnectedSkew_translate v (T.proper₁.2.2.2.isConnectedSkew_compose T.proper₁.1)
  exact ⟨(T.proper₁.mixFoldCoding_of_chartOf T.chart₁).1,
    (T.proper₂.mixFoldCoding_of_chartOf T.chart₂).1, MixFoldWordsOK.of_isConnectedSkew hF⟩

end TwoRoots

namespace TwoRoots

variable {F : Diagram} {χ₁ χ₂ : Chart}

theorem width_pos_of_mixed {χ : Chart} (h : χ.IsProperLegal) (hm : χ.ω.case.IsMixed) :
    0 < χ.ω.width := by
  obtain ⟨s, t, c⟩ := h.mixFoldCoding
  by_contra hw
  have := c.empty (by omega)
  rcases hm with hm | hm <;> rw [this] at hm <;> cases hm

theorem rotate_case_d {χ : Chart} (h : χ.ω.case = .c) : χ.rotate.ω.case = .d := by
  change χ.ω.case.rotate = .d
  rw [h]; rfl

theorem rotate_case_c {χ : Chart} (h : χ.ω.case = .d) : χ.rotate.ω.case = .c := by
  change χ.ω.case.rotate = .c
  rw [h]; rfl

theorem rotate_period (χ : Chart) : χ.rotate.ω.period.toNat = χ.ω.period.toNat := rfl

theorem span_rotate_eq (F : Diagram) : span (SkewGluing.rotate F) = span F := span_rotate

/-! ### The fixed boundary -/

/-- **The fixed boundary of a case-(d) chart becomes `g`-periodic.**  For two roots of nondividing
periods, the first of case (d), with the second of case (c) only when its period is the larger:
the word `B` of the parent has period `gcd p Q` (`lem:gluing-periods` (i) against an ordinary or
empty chart, the two full periods against a case-(d) chart, (iii) against a case-(c) chart of larger
period). -/
theorem fixed_boundary_d (T : TwoRoots F χ₁ χ₂) (hd : χ₁.ω.case = .d)
    (hcase : χ₂.ω.case = .c → χ₁.ω.period.toNat < χ₂.ω.period.toNat) :
    PeriodWords.PeriodExcept (span F - 1) (Nat.gcd χ₁.ω.period.toNat χ₂.ω.period.toNat) ∅
      (wordB F) := by
  obtain ⟨⟨s₁, t₁, c₁⟩, ⟨s₂, t₂, c₂⟩, -⟩ := T.codings
  rw [hd] at c₁
  exact mixFold_B_periodic c₁ (width_pos_of_mixed T.proper₁ (Or.inr hd)) c₂ hcase T.not_dvd₁
    T.not_dvd₂

/-- **The fixed boundary of a case-(c) chart becomes `g`-periodic.**  The word `A` of the parent has
period `gcd p Q` for a case-(c) first root, with the second root of case (d) only when its period is
the larger.  Case (c) is case (d) of the rotated charts, and rotation reverses the words. -/
theorem fixed_boundary_c (T : TwoRoots F χ₁ χ₂) (hc : χ₁.ω.case = .c)
    (hcase : χ₂.ω.case = .d → χ₁.ω.period.toNat < χ₂.ω.period.toNat) :
    PeriodWords.PeriodExcept (span F - 1) (Nat.gcd χ₁.ω.period.toNat χ₂.ω.period.toNat) ∅
      (wordA F) := by
  have T' := T.rotate
  have hrot : PeriodWords.PeriodExcept (span (SkewGluing.rotate F) - 1)
      (Nat.gcd χ₁.rotate.ω.period.toNat χ₂.rotate.ω.period.toNat) ∅ (wordB (SkewGluing.rotate F)) :=
    fixed_boundary_d T' (rotate_case_d hc) (fun h2 => by
      rw [rotate_period, rotate_period]
      apply hcase
      change χ₂.ω.case.rotate = .c at h2
      cases h : χ₂.ω.case <;> rw [h] at h2 <;> first | rfl | exact absurd h2 (by decide))
  rw [rotate_period, rotate_period, span_rotate_eq] at hrot
  have hF : IsConnectedSkew F := by
    obtain ⟨v, hv⟩ := T.chart₁
    rw [hv]
    exact isConnectedSkew_translate v (T.proper₁.2.2.2.isConnectedSkew_compose T.proper₁.1)
  have hsp := span_eq_of_isConnectedSkew hF
  have hmM : minContent F ≤ maxContent F := minContent_le (maxContent_mem hF.2.1)
  have hL : ((span F - 1 : ℕ) : ℤ) + 1 = (span F : ℤ) := by omega
  refine periodExcept_reverse (S := ∅) (f := wordB (SkewGluing.rotate F))
    (N := (span F : ℤ)) hL.symm (fun k => ?_) hrot (fun x _ => by simp)
  have := wordB_rotate hF ((span F : ℤ) - k)
  rw [sub_sub_cancel] at this
  exact this.symm

/-! ### Remainder zero -/

theorem remainder_zero_of_case_d (T : TwoRoots F χ₁ χ₂) (hd : χ₁.ω.case = .d)
    (hcase : χ₂.ω.case = .c → χ₁.ω.period.toNat < χ₂.ω.period.toNat)
    (hrem : span F % Nat.gcd χ₁.ω.period.toNat χ₂.ω.period.toNat = 0) : False := by
  obtain ⟨⟨s₁, t₁, c₁⟩, ⟨s₂, t₂, c₂⟩, -⟩ := T.codings
  rw [hd] at c₁
  exact mixFold_remainder_zero_words c₁ (width_pos_of_mixed T.proper₁ (Or.inr hd)) c₂ hcase
    T.not_dvd₁ T.not_dvd₂ hrem

theorem remainder_zero_of_mixed_first (T : TwoRoots F χ₁ χ₂) (hm : χ₁.ω.case.IsMixed)
    (hrem : span F % Nat.gcd χ₁.ω.period.toNat χ₂.ω.period.toNat = 0) : False := by
  -- the case-(d) statement, for a pair whose first chart is of case (d)
  have hD : ∀ {F : Diagram} {χ₁ χ₂ : Chart}, TwoRoots F χ₁ χ₂ → χ₁.ω.case = .d →
      span F % Nat.gcd χ₁.ω.period.toNat χ₂.ω.period.toNat = 0 → False := by
    intro F χ₁ χ₂ T hd hrem
    by_cases hcc : χ₂.ω.case = .c ∧ ¬ χ₁.ω.period.toNat < χ₂.ω.period.toNat
    · -- rotate and swap: the case-(c) chart becomes a case-(d) chart of smaller period
      have T' := T.symm.rotate
      refine remainder_zero_of_case_d T' (rotate_case_d hcc.1) (fun _ => ?_) ?_
      · rw [rotate_period, rotate_period]
        have hne : χ₁.ω.period.toNat ≠ χ₂.ω.period.toNat := fun h => T.not_dvd₁ (h ▸ dvd_refl _)
        omega
      · rw [span_rotate_eq, rotate_period, rotate_period, Nat.gcd_comm]; exact hrem
    · exact remainder_zero_of_case_d T hd (fun hc => by
        by_contra hlt; exact hcc ⟨hc, hlt⟩) hrem
  rcases hm with hc | hd
  · have T' := T.rotate
    exact hD T' (rotate_case_d hc) (by
      rw [span_rotate_eq, rotate_period, rotate_period]; exact hrem)
  · exact hD T hd hrem

/-- **Mixed pairs at remainder zero are impossible** (the paragraph opening «Pairs involving mixed
charts»).  If the two roots have nondividing periods `p, Q` and `gcd p Q` divides the span `N_F`,
then neither chart is mixed. -/
theorem mixed_pairs_remainder_zero (T : TwoRoots F χ₁ χ₂)
    (hrem : span F % Nat.gcd χ₁.ω.period.toNat χ₂.ω.period.toNat = 0) :
    ¬ χ₁.ω.case.IsMixed ∧ ¬ χ₂.ω.case.IsMixed := by
  refine ⟨fun hm => remainder_zero_of_mixed_first T hm hrem, fun hm => ?_⟩
  refine remainder_zero_of_mixed_first T.symm hm ?_
  rw [Nat.gcd_comm]; exact hrem

/-! ### `lem:gluing-incompatible` -/

theorem mixed_ordinary_of_case_d (T : TwoRoots F χ₁ χ₂) (hd : χ₁.ω.case = .d)
    (hord : ¬ χ₂.ω.case.IsMixed) : False := by
  obtain ⟨⟨s₁, t₁, c₁⟩, ⟨s₂, t₂, c₂⟩, -⟩ := T.codings
  rw [hd] at c₁
  have hw₁ := width_pos_of_mixed T.proper₁ (Or.inr hd)
  by_cases hw₂ : 0 < χ₂.ω.width
  · exact mixFold_mixed_ordinary_words c₁ hw₁ c₂ hw₂ hord T.not_dvd₁ T.not_dvd₂
  · -- an empty ordinary mark: the remainder is zero
    have w0 : χ₂.ω.width = 0 := by omega
    obtain ⟨r, -, hr⟩ := c₂.span_eq
    rw [w0, add_zero] at hr
    have hrem : span F % Nat.gcd χ₁.ω.period.toNat χ₂.ω.period.toNat = 0 := by
      rw [hr]
      exact Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_right (Nat.gcd_dvd_right _ _) _)
    exact (mixed_pairs_remainder_zero T hrem).1 (Or.inr hd)

/-- **`lem:gluing-incompatible`, mixed/ordinary.**  At nondividing periods, a mixed chart and an
ordinary chart (of any width, the empty mark included) of one parent cannot both occur. -/
theorem gluing_incompatible_mixed_ordinary (T : TwoRoots F χ₁ χ₂) (hm : χ₁.ω.case.IsMixed)
    (hord : ¬ χ₂.ω.case.IsMixed) : False := by
  rcases hm with hc | hd
  · refine mixed_ordinary_of_case_d T.rotate (rotate_case_d hc) ?_
    intro hm
    apply hord
    change χ₂.ω.case.rotate.IsMixed at hm
    unfold AttachCase.IsMixed at hm ⊢
    cases h : χ₂.ω.case <;> rw [h] at hm <;> simp [AttachCase.rotate] at hm ⊢
  · exact mixed_ordinary_of_case_d T hd hord

theorem opposite_of_period_lt (T : TwoRoots F χ₁ χ₂) (hd : χ₁.ω.case = .d)
    (hc : χ₂.ω.case = .c) (hlt : χ₁.ω.period.toNat < χ₂.ω.period.toNat) : False := by
  obtain ⟨⟨s₁, t₁, c₁⟩, ⟨s₂, t₂, c₂⟩, hF⟩ := T.codings
  rw [hd] at c₁
  rw [hc] at c₂
  exact mixFold_opposite_words c₁ (width_pos_of_mixed T.proper₁ (Or.inr hd)) c₂
    (width_pos_of_mixed T.proper₂ (Or.inl hc)) hF hlt T.not_dvd₁ T.not_dvd₂

/-- **`lem:gluing-incompatible`, opposite mixed.**  At nondividing periods, a case-(d) chart and a
case-(c) chart of one parent cannot both occur. -/
theorem gluing_incompatible_opposite (T : TwoRoots F χ₁ χ₂) (hd : χ₁.ω.case = .d)
    (hc : χ₂.ω.case = .c) : False := by
  have hne : χ₁.ω.period.toNat ≠ χ₂.ω.period.toNat := fun h => T.not_dvd₁ (h ▸ dvd_refl _)
  by_cases hlt : χ₁.ω.period.toNat < χ₂.ω.period.toNat
  · exact opposite_of_period_lt T hd hc hlt
  · -- rotate and swap, so that the case-(d) chart has the smaller period
    refine opposite_of_period_lt T.symm.rotate (rotate_case_d hc) (rotate_case_c hd) ?_
    rw [rotate_period, rotate_period]
    omega

/-- **`lem:gluing-incompatible`.**  At nondividing periods a mixed/ordinary pair and an
opposite-mixed pair are impossible: if one of the two roots is mixed, both have the same case. -/
theorem gluing_incompatible (T : TwoRoots F χ₁ χ₂)
    (hm : χ₁.ω.case.IsMixed ∨ χ₂.ω.case.IsMixed) : χ₁.ω.case = χ₂.ω.case := by
  by_contra hne
  rcases hm with hm | hm
  · by_cases h2 : χ₂.ω.case.IsMixed
    · rcases hm with h1 | h1 <;> rcases h2 with h2 | h2
      · exact hne (h1.trans h2.symm)
      · exact gluing_incompatible_opposite T.symm h2 h1
      · exact gluing_incompatible_opposite T h1 h2
      · exact hne (h1.trans h2.symm)
    · exact gluing_incompatible_mixed_ordinary T hm h2
  · by_cases h1 : χ₁.ω.case.IsMixed
    · rcases h1 with h1 | h1 <;> rcases hm with h2 | h2
      · exact hne (h1.trans h2.symm)
      · exact gluing_incompatible_opposite T.symm h2 h1
      · exact gluing_incompatible_opposite T h1 h2
      · exact hne (h1.trans h2.symm)
    · exact gluing_incompatible_mixed_ordinary T.symm hm h1

end TwoRoots

/-! ### `lem:gluing-collision` -/

/-- **`lem:gluing-collision`.**  Let a proper legal chart `χ` of `F` be of case (d), with middle
phases `s, t`, and let `g` divide its period.  Suppose `N_F = M g + w_g` with `0 < w_g < g`, that
the word `B` of `F` is `g`-periodic and that the word `A` of `F` is `g`-periodic outside one residue
`R`.  Then the two middle phases are not both congruent to `R` modulo `g`. -/
theorem gluing_collision {F : Diagram} {χ : Chart} (h : χ.IsProperLegal) (hF : χ.IsChartOf F)
    (hd : χ.ω.case = .d) {g : ℕ} (hg : 0 < g) (hgq : g ∣ χ.ω.period.toNat)
    (hrem : 0 < span F % g) {R : ℤ}
    (hB : PeriodWords.PeriodExcept (span F - 1) g ∅ (wordB F))
    (hA : PeriodWords.PeriodExcept (span F - 1) g {R} (wordA F)) {s t : ℤ}
    (hph : χ.ω.IsPhases s t) : ¬ (s % (g : ℤ) = R ∧ t % (g : ℤ) = R) := by
  have hw := TwoRoots.width_pos_of_mixed h (Or.inr hd)
  have hW : χ.ω.W.Nonempty := by
    by_contra hcon
    have := MarkedInner.width_eq_zero_of_eq_empty (Finset.not_nonempty_iff_eq_empty.mp hcon)
    omega
  have hc := (h.mixFoldCoding_of_chartOf hF).2 s t hW hph
  rw [hd] at hc
  have hFc : IsConnectedSkew F := by
    obtain ⟨v, hv⟩ := hF
    rw [hv]
    exact isConnectedSkew_translate v (h.2.2.2.isConnectedSkew_compose h.1)
  rintro ⟨hs, ht⟩
  exact mixFold_collision_words hc hw (MixFoldWordsOK.of_isConnectedSkew hFc) hg hgq hrem hB hA
    hs ht

end SkewGluing
