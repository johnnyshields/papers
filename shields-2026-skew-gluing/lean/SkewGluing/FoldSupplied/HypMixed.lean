import SkewGluing.FoldSupplied.MixedChart
import SkewGluing.FoldSupplied.HypOrdinary
import SkewGluing.MixedFold

/-!
# `prop:gluing-mixed-fold`: the class hypotheses of the fold from the two roots

Formalizes `shields-2026-skew-gluing.tex`, «Pairs involving mixed charts»
(`prop:gluing-mixed-fold`, `lem:gluing-periods` (ii), `lem:gluing-collision`): two case-(d) proper
roots of nondividing periods `p`, `Q` with `g = gcd (p, Q) > 1` have a parent whose southeast word
is `g`-periodic and whose northwest word follows generic bits modulo `g` off the simultaneous holes.
Restricted to the first `p`-window, which is the window of the supplied inner `E` of the first chart,
this makes every residue class modulo `g` of the native row list full or empty, and every class of
the square native column list outside the classes of the two contacts full or empty.

* `MarkedInner.IsLegalNonempty.wordA_period_d`: at the actual step `p` the northwest word of a
  case-(d) parent is one when `t ≥ 1`;
* `FoldSupplied.mixed_class_hyps`: the class hypotheses of `mixed_fold`, from the two roots;
* `FoldSupplied.mixed_fold_of_roots_d`: the mixed fold of the supplied inner of a first chart of
  case (d), lifted to the parent;
* `FoldSupplied.mixed_fold_of_roots`: the same for either mixed case, case (c) being the rotated
  comparison transported back.

Sorry-free.
-/

namespace SkewGluing

namespace MarkedInner

variable {ω : MarkedInner} {D : Diagram}

/-- At the actual step `p`, the northwest word of the parent of a case-(d) mark takes the value one
when the contact `t` is positive. -/
theorem IsLegalNonempty.wordA_period_d (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D)
    (hD2 : 2 ≤ span D) (hc : ω.case = .d) {s t : ℤ} (hph : ω.IsPhases s t) (ht : 1 ≤ t) :
    wordA (ω.compose D) ω.period = 1 := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph
  have hlt := h.phases_lt (Or.inr hc) hph
  have hmM : minContent D ≤ maxContent D := minContent_le (maxContent_mem hD.2.1)
  have hsp := span_eq_of_isConnectedSkew hD
  have hcl := mix_classRows h hD hc hph hlt
  have hmin := h.minContent_compose' hD
  have vq : ValidClass (minContent D) (maxContent D) ω.widthZ (minContent D + 1) 0 := by
    unfold ValidClass; omega
  have hv0 : ValidClass (minContent D) (maxContent D) ω.widthZ (minContent D) (ω.period - 1) :=
    Or.inl ⟨le_refl _, hmM⟩
  rw [hcl.wordA_class' hmin (J := minContent D + 1) (a := 0) (by ring) (le_refl _) (by omega) vq
    (fun _ => by omega)]
  unfold classBitLo
  simp only [ite_true, add_sub_cancel_right]
  rw [mixLo_formula h hD hc hph (by omega) hv0, mixLo_formula h hD hc hph (le_refl _) vq]
  have hcp := (d_caps h hc).2
  have f0 := d_E_facts h hc hph (a := 0) (le_refl _) (by omega)
  have hW0 := h.diagLo_W (a := 0) (le_refl _) (by omega)
  have he := D_end_singleton hD (x := minContent D) (Or.inl rfl)
  simp only [dLo, dHi, zero_add, add_zero] at hcp f0 hW0
  unfold mixGLo profM profS
  have hp : (minContent D + 1 - 1) * ω.rowShift = minContent D * ω.rowShift := by ring
  have hp2 : (minContent D + 1) * ω.rowShift = minContent D * ω.rowShift + ω.rowShift := by ring
  simp only [add_sub_cancel_right, add_zero]
  split_ifs <;> omega

end MarkedInner

namespace FoldSupplied

open MarkedInner

/-- The boundary coding, the private heights and the phases of a proper legal case-(d) chart `χ`
of `F`, on the words of `F`. -/
theorem mixFold_chart_data' {F : Diagram} {χ : Chart} (h : χ.IsProperLegal) (hF : χ.IsChartOf F)
    (hd : χ.ω.case = .d) :
    ∃ s t : ℤ, χ.ω.IsPhases s t ∧
      MixFoldCoding (wordA F) (wordB F) (span F) χ.ω.period.toNat χ.ω.width .d s t ∧
      MixFoldExtra (wordA F) (wordB F) (span F) χ.ω.period.toNat χ.ω.width s t ∧
      0 < χ.ω.width := by
  have hw := TwoRoots.width_pos_of_mixed h (Or.inr hd)
  have hW : χ.ω.W.Nonempty := by
    by_contra hcon
    have := MarkedInner.width_eq_zero_of_eq_empty (Finset.not_nonempty_iff_eq_empty.mp hcon)
    omega
  have hl : χ.ω.IsLegalNonempty := ⟨h.2.2.2, hW⟩
  obtain ⟨s, t, hph⟩ := hl.exists_phases
  obtain ⟨hs1, hs2, ht1, ht2, -⟩ := id hph
  have hcod := (h.mixFoldCoding_of_chartOf hF).2 s t hW hph
  rw [hd] at hcod
  have hP : IsConnectedSkew χ.parent := h.2.2.2.isConnectedSkew_compose h.1
  obtain ⟨v, hv⟩ := hF
  have hspan : span F = span χ.parent := by rw [hv, span_translate]
  have hD2 : 2 ≤ span χ.D := two_le_span_of_two_le_card h.1 h.2.1
  have hx := hl.mixFold_extra h.1 hD2 hd hph
  have hwq := hcod.w_lt
  have hN := hcod.two_q_add_w_le
  have hx' : MixFoldExtra (wordA χ.parent) (wordB χ.parent) (span F) χ.ω.period.toNat χ.ω.width
      s t := by
    rw [hspan]; exact hx
  refine ⟨s, t, hph, hcod, ?_, hw⟩
  refine hx'.of_agree hcod.q_pos hs1 hs2 ht1 ht2 (fun k h1 h2 => ?_) (fun k h1 h2 => ?_)
    (by omega)
  · rw [hv]
    exact (wordA_translate hP v h1 (by omega)).symm
  · rw [hv]
    exact (wordB_translate hP v h1 (by omega)).symm

/-- **The class hypotheses of `mixed_fold` from two case-(d) roots.**  Two case-(d) proper legal
roots `χ₁`, `χ₂` of one diagram, of nondividing periods with `g = gcd > 1`, make every residue
class modulo `g` of the native row list of the supplied inner `χ₁.ω.E` full or empty, and every
class of the square native column list outside the classes of the two contacts full or empty. -/
theorem mixed_class_hyps {F : Diagram} {χ₁ χ₂ : Chart} (T : TwoRoots F χ₁ χ₂)
    (hg : 1 < Nat.gcd χ₁.ω.period.toNat χ₂.ω.period.toNat) (h₁ : χ₁.ω.case = .d)
    (h₂ : χ₂.ω.case = .d) :
    ∃ s t : ℤ, χ₁.ω.IsPhases s t ∧
      FullOrEmptyAll (mixRowSet χ₁.ω.E χ₁.ω.period.toNat)
        (Nat.gcd χ₁.ω.period.toNat χ₂.ω.period.toNat) χ₁.ω.period.toNat ∧
      FullOrEmptyOff2 (mixColSet χ₁.ω.E χ₁.ω.period.toNat t.toNat)
        (Nat.gcd χ₁.ω.period.toNat χ₂.ω.period.toNat) χ₁.ω.period.toNat t.toNat s.toNat := by
  have hrem : 0 < span F % Nat.gcd χ₁.ω.period.toNat χ₂.ω.period.toNat := by
    by_contra hcon
    exact (TwoRoots.mixed_pairs_remainder_zero T (by omega)).1 (Or.inr h₁)
  have hFc : IsConnectedSkew F := by
    obtain ⟨v, hv⟩ := T.chart₁
    rw [hv]
    exact isConnectedSkew_translate v (T.proper₁.2.2.2.isConnectedSkew_compose T.proper₁.1)
  obtain ⟨s₁, t₁, hph₁, c₁, x₁, hw₁⟩ := mixFold_chart_data' T.proper₁ T.chart₁ h₁
  obtain ⟨s₂, t₂, hph₂, c₂, x₂, hw₂⟩ := mixFold_chart_data' T.proper₂ T.chart₂ h₂
  have P : MixFoldPair (wordA F) (wordB F) (span F) χ₁.ω.period.toNat χ₂.ω.period.toNat
      χ₁.ω.width χ₂.ω.width s₁ t₁ s₂ t₂ :=
    ⟨c₁, c₂, x₁, x₂, MixFoldWordsOK.of_isConnectedSkew hFc, hw₁, hw₂, T.not_dvd₁, T.not_dvd₂,
      hrem⟩
  refine ⟨s₁, t₁, hph₁, ?_⟩
  -- notation
  obtain ⟨hs1, hs2, ht1, ht2, hts⟩ := c₁.phases hw₁
  have hts' : t₁ < s₁ := hts (Or.inr rfl)
  set p := χ₁.ω.period.toNat with hp
  set Q := χ₂.ω.period.toNat with hQ
  set g := Nat.gcd p Q with hgdef
  have hg0 : 0 < g := P.g_pos
  have hgp : g ∣ p := Nat.gcd_dvd_left p Q
  have hgle : g ≤ p := Nat.le_of_dvd P.p_pos hgp
  have hgne : g ≠ p := by
    intro e
    apply T.not_dvd₁
    have := Nat.gcd_dvd_right p Q
    rw [← hgdef, e] at this
    exact this
  obtain ⟨m, hm⟩ := hgp
  have hmg : p = g * m := hm
  have hm2 : 2 ≤ m := by
    by_contra hcon
    have : m ≤ 1 := by omega
    have : g * m ≤ g * 1 := Nat.mul_le_mul_left g this
    omega
  obtain ⟨r, hr, hNr⟩ := c₁.span_eq
  have hN2 := c₁.two_q_add_w_le
  have hwp := c₁.w_lt
  have hl : χ₁.ω.IsLegalNonempty := by
    refine ⟨T.proper₁.2.2.2, ?_⟩
    by_contra hcon
    have := MarkedInner.width_eq_zero_of_eq_empty (Finset.not_nonempty_iff_eq_empty.mp hcon)
    omega
  have hD := T.proper₁.1
  have hD2 := two_le_span_of_two_le_card hD T.proper₁.2.1
  have hP : IsConnectedSkew χ₁.parent := T.proper₁.2.2.2.isConnectedSkew_compose hD
  obtain ⟨t0, ht0⟩ := T.chart₁
  have hspF : span F = span χ₁.parent := by rw [ht0]; exact span_translate _
  have hpcast := hl.1.period_toNat_cast
  have hpspan : p < span χ₁.parent := period_le_span_compose hl hD hD2
  -- the words of the supplied inner against the words of the parent
  have hWA : ∀ k : ℕ, 1 ≤ k → k < p → wordA χ₁.ω.E (k : ℤ) = wordA F (k : ℤ) := by
    intro k h1 h2
    rw [wordA_E_eq_compose hl hD h1 h2, ht0]
    exact (wordA_translate hP t0 (by exact_mod_cast h1) (by exact_mod_cast (by omega : k < span χ₁.parent))).symm
  have hWB : ∀ k : ℕ, 1 ≤ k → k < p → wordB χ₁.ω.E (k : ℤ) = wordB F (k : ℤ) := by
    intro k h1 h2
    rw [wordB_E_eq_compose hl hD h1 h2, ht0]
    exact (wordB_translate hP t0 (by exact_mod_cast h1) (by exact_mod_cast (by omega : k < span χ₁.parent))).symm
  -- the position bookkeeping
  have hpos : ∀ j ρ : ℕ, j < m → ρ < g → j * g + ρ < p := by
    intro j ρ hj hρ
    have : (j + 1) * g ≤ m * g := Nat.mul_le_mul_right g hj
    nlinarith
  have hmodk : ∀ j ρ : ℕ, ρ < g → (j * g + ρ) % g = ρ := by
    intro j ρ hρ
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hρ]
  have hdiv : ∀ j ρ : ℕ, (g : ℤ) ∣ ((j * g + ρ : ℕ) : ℤ) - (ρ : ℤ) := by
    intro j ρ
    refine ⟨j, ?_⟩
    push_cast; ring
  have hp1 : 1 ≤ p := P.p_pos
  have hNpZ : (p : ℤ) ≤ (span F : ℤ) - 1 := by
    have : p + 1 ≤ span F := by omega
    omega
  have hpm : p / g = m := by rw [hmg]; exact Nat.mul_div_cancel_left m hg0
  -- the row list
  have hRow : FullOrEmptyAll (mixRowSet χ₁.ω.E p) g p := by
    intro ρ hρ
    have hmemB : ∀ k : ℕ, k < p → (k ∈ mixRowSet χ₁.ω.E p ↔ 1 ≤ k ∧ wordB F (k : ℤ) = 1) := by
      intro k hk
      unfold mixRowSet
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨-, h1, h2⟩
        exact ⟨h1, by rw [← hWB k h1 hk]; exact h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨hk, h1, by rw [hWB k h1 hk]; exact h2⟩
    by_cases hρ0 : ρ = 0
    · subst hρ0
      right
      intro j hj hmem
      rw [hpm] at hj
      have hjp := hpos j 0 hj hg0
      obtain ⟨h1, h2⟩ := (hmemB _ hjp).mp hmem
      have hj1 : 1 ≤ j := by
        rcases Nat.eq_zero_or_pos j with h | h
        · subst h; simp at h1
        · exact h
      have e := mixFold_eq_of_gcd_dvd (N := span F) hg0 P.perB (x := ((j * g + 0 : ℕ) : ℤ))
        (y := (p : ℤ)) (by exact_mod_cast h1) (by have := hpos j 0 hj hg0; omega)
        (by exact_mod_cast hp1) hNpZ (by
          refine ⟨(m - j : ℕ), ?_⟩
          have : ((m - j : ℕ) : ℤ) = (m : ℤ) - j := by omega
          rw [this, hmg]; push_cast; ring)
      have hBp : wordB F (p : ℤ) = 0 := by
        have := c₁.caps_d hw₁ rfl
        exact this.2.2.2.2.2
      rw [hBp] at e
      rw [e] at h2
      omega
    · have hρ1 : 1 ≤ ρ := Nat.one_le_iff_ne_zero.mpr hρ0
      have hρp : ρ < p := by omega
      by_cases hv : wordB F (ρ : ℤ) = 1
      · left
        intro j hj
        rw [hpm] at hj
        have hjp := hpos j ρ hj hρ
        refine (hmemB _ hjp).mpr ⟨by omega, ?_⟩
        rw [← hv]
        exact mixFold_eq_of_gcd_dvd (N := span F) hg0 P.perB (by exact_mod_cast (by omega : 1 ≤ j * g + ρ))
          (by have : ((j * g + ρ : ℕ) : ℤ) < p := by exact_mod_cast hjp
              omega) (by exact_mod_cast hρ1) (by omega) (by
            obtain ⟨c, hc⟩ := hdiv j ρ
            exact ⟨-c, by linarith⟩)
      · right
        intro j hj hmem
        rw [hpm] at hj
        have hjp := hpos j ρ hj hρ
        obtain ⟨-, h2⟩ := (hmemB _ hjp).mp hmem
        apply hv
        rw [← h2]
        exact mixFold_eq_of_gcd_dvd (N := span F) hg0 P.perB (by exact_mod_cast hρ1) (by omega)
          (by exact_mod_cast (by omega : 1 ≤ j * g + ρ))
          (by have : ((j * g + ρ : ℕ) : ℤ) < p := by exact_mod_cast hjp
              omega) (hdiv j ρ)
  refine ⟨hRow, ?_⟩
  -- the column list
  have hnonsim : ∀ k : ℕ, k < p → k % g ≠ t₁.toNat % g → k % g ≠ s₁.toNat % g →
      ¬ mixFoldSim p Q s₁ t₁ s₂ t₂ (k : ℤ) := by
    intro k hk h1 h2 hsim
    have e : (k : ℤ) % (p : ℤ) = k := Int.emod_eq_of_lt (by omega) (by exact_mod_cast hk)
    have hs := hsim.1
    rw [e] at hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with hs | hs
    · apply h1
      have : k = t₁.toNat := by omega
      rw [this]
    · apply h2
      have : k = s₁.toNat := by omega
      rw [this]
  have hmemA : ∀ k : ℕ, k < p → k % g ≠ t₁.toNat % g →
      (k ∈ mixColSet χ₁.ω.E p t₁.toNat ↔ k = 0 ∨ (1 ≤ k ∧ wordA F (k : ℤ) = 1)) := by
    intro k hk hkt
    have hne : k ≠ t₁.toNat := fun e => hkt (by rw [e])
    unfold mixColSet nativeColSet
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_filter, Finset.mem_range, hne,
      ne_eq, not_false_eq_true, true_and]
    constructor
    · rintro (h0 | ⟨-, h1, h2⟩)
      · exact Or.inl h0
      · exact Or.inr ⟨h1, by rw [← hWA k h1 hk]; exact h2⟩
    · rintro (h0 | ⟨h1, h2⟩)
      · exact Or.inl h0
      · exact Or.inr ⟨hk, h1, by rw [hWA k h1 hk]; exact h2⟩
  have hgen : ∀ k : ℕ, 1 ≤ k → k < p → k % g ≠ t₁.toNat % g → k % g ≠ s₁.toNat % g →
      ∀ y : ℕ, 1 ≤ y → y < p → y % g = k % g → y % g ≠ t₁.toNat % g → y % g ≠ s₁.toNat % g →
        wordA F (k : ℤ) = wordA F (y : ℤ) := by
    intro k h1 hk h2 h3 y hy1 hy2 hyk h4 h5
    refine P.generic_eq (x := k) (y := y) ⟨by exact_mod_cast h1, by omega⟩
      ⟨by exact_mod_cast hy1, by omega⟩ ?_ (hnonsim k hk h2 h3) (hnonsim y hy2 h4 h5)
    have : (g : ℤ) ∣ (y : ℤ) - k := by
      have h6 : ((y % g : ℕ) : ℤ) = ((k % g : ℕ) : ℤ) := by rw [hyk]
      rw [Int.natCast_mod, Int.natCast_mod] at h6
      exact Int.ModEq.dvd h6.symm
    exact this
  have hAp : 1 ≤ t₁ → wordA F (p : ℤ) = 1 := by
    intro ht
    have h1 := hl.wordA_period_d hD hD2 h₁ hph₁ ht
    rw [← hpcast] at h1
    rw [ht0]
    rw [wordA_translate hP t0 (by exact_mod_cast hp1) (by exact_mod_cast hpspan)]
    exact h1
  intro ρ hρ hneT hneS
  rw [hpm]
  by_cases hρ0 : ρ = 0
  · subst hρ0
    left
    intro j hj
    have hjp := hpos j 0 hj hg0
    have hmod0 := hmodk j 0 hg0
    have ht1' : 1 ≤ t₁ := by
      have : t₁.toNat ≠ 0 := fun e => hneT (by rw [e]; simp)
      omega
    rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · subst hj0
      refine (hmemA _ hjp (by rw [hmod0]; exact hneT)).mpr (Or.inl (by simp))
    · refine (hmemA _ hjp (by rw [hmod0]; exact hneT)).mpr (Or.inr ⟨by nlinarith, ?_⟩)
      rw [← hAp ht1']
      refine P.generic_eq (x := ((j * g + 0 : ℕ) : ℤ)) (y := (p : ℤ))
        ⟨by exact_mod_cast (by nlinarith : 1 ≤ j * g + 0), by omega⟩
        ⟨by exact_mod_cast hp1, hNpZ⟩ ?_ (hnonsim _ hjp (by rw [hmod0]; exact hneT)
          (by rw [hmod0]; exact hneS)) ?_
      · refine ⟨(m : ℤ) - j, ?_⟩
        have h' : (p : ℤ) = g * m := by exact_mod_cast hmg
        push_cast; rw [h']; ring
      · intro hsim
        have e : (p : ℤ) % (p : ℤ) = 0 := Int.emod_self
        have hs := hsim.1
        rw [e] at hs
        simp only [Finset.mem_insert, Finset.mem_singleton] at hs
        omega
  · have hρ1 : 1 ≤ ρ := Nat.one_le_iff_ne_zero.mpr hρ0
    have hρp : ρ < p := by omega
    by_cases hv : wordA F (ρ : ℤ) = 1
    · left
      intro j hj
      have hjp := hpos j ρ hj hρ
      have hmk := hmodk j ρ hρ
      refine (hmemA _ hjp (by rw [hmk]; exact hneT)).mpr (Or.inr ⟨by omega, ?_⟩)
      rw [← hv]
      exact hgen _ (by omega) hjp (by rw [hmk]; exact hneT) (by rw [hmk]; exact hneS) ρ hρ1 hρp
        (by rw [hmk, Nat.mod_eq_of_lt hρ]) (by rw [Nat.mod_eq_of_lt hρ]; exact hneT) (by rw [Nat.mod_eq_of_lt hρ]; exact hneS)
    · right
      intro j hj hmem
      have hjp := hpos j ρ hj hρ
      have hmk := hmodk j ρ hρ
      obtain h0 | ⟨-, h2⟩ := (hmemA _ hjp (by rw [hmk]; exact hneT)).mp hmem
      · omega
      · apply hv
        rw [← hgen _ (by omega) hjp (by rw [hmk]; exact hneT) (by rw [hmk]; exact hneS) ρ hρ1 hρp
          (by rw [hmk, Nat.mod_eq_of_lt hρ]) (by rw [Nat.mod_eq_of_lt hρ]; exact hneT) (by rw [Nat.mod_eq_of_lt hρ]; exact hneS)]
        exact h2

/-- **`prop:gluing-mixed-fold`, supplied-inner form, first chart of case (d).** -/
theorem mixed_fold_of_roots_d {F : Diagram} {χ₁ χ₂ : Chart} (T : TwoRoots F χ₁ χ₂)
    (hg2 : 2 ≤ Nat.gcd χ₁.ω.period.toNat χ₂.ω.period.toNat) (h₁ : χ₁.ω.case = .d)
    (h₂ : χ₂.ω.case = .d) :
    ∃ (χ' ψ : Chart) (μ : MarkedInner) (γ : Diagram → Diagram) (u : ℤ × ℤ),
      ψ.IsProperLegal ∧ ψ.IsChartOf χ₁.ω.E ∧
        ψ.period = (Nat.gcd χ₁.ω.period.toNat χ₂.ω.period.toNat : ℤ) ∧ ψ.ω.case = .d ∧
        ψ.ω.width = χ₁.ω.width % Nat.gcd χ₁.ω.period.toNat χ₂.ω.period.toNat ∧
      χ'.IsProperLegal ∧ χ'.IsChartOf F ∧ χ'.ω = ψ.ω.translate u ∧
        χ'.period = (Nat.gcd χ₁.ω.period.toNat χ₂.ω.period.toNat : ℤ) ∧
      μ.IsLegal ∧ μ.E = ψ.D ∧ (γ = id ∨ (γ = antitranspose ∧ μ.W = ∅)) ∧
      χ'.D = μ.compose (γ χ₁.D) := by
  obtain ⟨s, t, hph, hB, hC⟩ := mixed_class_hyps T (by omega) h₁ h₂
  have hW : χ₁.ω.W.Nonempty := by
    by_contra hcon
    have := MarkedInner.width_eq_zero_of_eq_empty (Finset.not_nonempty_iff_eq_empty.mp hcon)
    have := TwoRoots.width_pos_of_mixed T.proper₁ (Or.inr h₁)
    omega
  have hgp : Nat.gcd χ₁.ω.period.toNat χ₂.ω.period.toNat ∣ χ₁.ω.period.toNat :=
    Nat.gcd_dvd_left _ _
  have hglt : Nat.gcd χ₁.ω.period.toNat χ₂.ω.period.toNat < χ₁.ω.period.toNat := by
    refine lt_of_le_of_ne (Nat.le_of_dvd (by
      have := T.proper₁.2.2.2.period_pos; omega) hgp) (fun e => T.not_dvd₁ ?_)
    rw [← e]; exact Nat.gcd_dvd_right _ _
  exact mixed_fold_lift T.proper₁ T.chart₁ h₁ hW hph hg2 hgp hglt hB hC

/-- **`prop:gluing-mixed-fold`, supplied-inner form.**  Two same-case mixed proper legal roots
`χ₁`, `χ₂` of one diagram `F`, of nondividing periods whose gcd `g` exceeds one.  Then `F` has a
proper legal chart of period `g` whose marked inner is the mixed fold of the supplied inner `χ₁.ω.E`
(up to translation), of the same case and of width `w mod g`, and whose outer is the composite of a
legal mark on the outer of that fold with `γ (χ₁.D)`, `γ ∈ {id, AT}`.  The only hypotheses are
the two roots: the class hypotheses of `mixed_fold` are derived from the generic bits of
`lem:gluing-periods` (ii) and the fixed boundary.  Case (c) is the rotated comparison. -/
theorem mixed_fold_of_roots {F : Diagram} {χ₁ χ₂ : Chart} (T : TwoRoots F χ₁ χ₂)
    (hg2 : 2 ≤ Nat.gcd χ₁.ω.period.toNat χ₂.ω.period.toNat)
    (hsame : χ₁.ω.case = χ₂.ω.case) (hmix : χ₁.ω.case.IsMixed) :
    ∃ (χ' ψ : Chart) (μ : MarkedInner) (γ : Diagram → Diagram) (u : ℤ × ℤ),
      ψ.IsProperLegal ∧ ψ.IsChartOf χ₁.ω.E ∧
        ψ.period = (Nat.gcd χ₁.ω.period.toNat χ₂.ω.period.toNat : ℤ) ∧
        ψ.ω.case = χ₁.ω.case ∧
        ψ.ω.width = χ₁.ω.width % Nat.gcd χ₁.ω.period.toNat χ₂.ω.period.toNat ∧
      χ'.IsProperLegal ∧ χ'.IsChartOf F ∧ χ'.ω = ψ.ω.translate u ∧
        χ'.period = (Nat.gcd χ₁.ω.period.toNat χ₂.ω.period.toNat : ℤ) ∧
      μ.IsLegal ∧ μ.E = ψ.D ∧ (γ = id ∨ (γ = antitranspose ∧ μ.W = ∅)) ∧
      χ'.D = μ.compose (γ χ₁.D) := by
  rcases hmix with hc | hd
  · have hc2 : χ₂.ω.case = .c := hsame ▸ hc
    have T' := T.rotate
    have hg' : 2 ≤ Nat.gcd χ₁.rotate.ω.period.toNat χ₂.rotate.ω.period.toNat := by
      rw [TwoRoots.rotate_period, TwoRoots.rotate_period]; exact hg2
    obtain ⟨χ'', ψ, μ, γ, u, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13⟩ :=
      mixed_fold_of_roots_d T' hg' (TwoRoots.rotate_case_d hc) (TwoRoots.rotate_case_d hc2)
    rw [TwoRoots.rotate_period, TwoRoots.rotate_period] at k3 k5 k9
    rw [show χ₁.rotate.ω.width = χ₁.ω.width from MarkedInner.width_rotate _] at k5
    have hX : IsConnectedSkew χ₁.D := T.proper₁.1
    have hγX : IsConnectedSkew (γ (SkewGluing.rotate χ₁.D)) := by
      have hR := isConnectedSkew_rotate hX
      rcases k12 with h | ⟨h, -⟩
      · rw [h]; exact hR
      · rw [h]; exact isConnectedSkew_antitranspose hR
    refine ⟨χ''.rotate, ψ.rotate, μ.rotate, γ, -u, k1.rotate, ?_, k3, ?_, ?_, k6.rotate, ?_, ?_,
      ?_, MarkedInner.isLegal_rotate k10, ?_, ?_, ?_⟩
    · have := TwoRoots.chart_rotate k1 k2
      change ψ.rotate.IsChartOf (SkewGluing.rotate (SkewGluing.rotate χ₁.ω.E)) at this
      rwa [SkewGluing.rotate_rotate] at this
    · change ψ.ω.case.rotate = _
      rw [k4, hc]; rfl
    · change ψ.ω.rotate.width = _
      rw [MarkedInner.width_rotate]; exact k5
    · have := TwoRoots.chart_rotate k6 k7
      rwa [SkewGluing.rotate_rotate] at this
    · change χ''.ω.rotate = ψ.ω.rotate.translate (-u)
      rw [k8, MarkedInner.rotate_translate]
    · change χ''.ω.rotate.period = _
      rw [MarkedInner.period_rotate]; exact k9
    · change SkewGluing.rotate μ.E = SkewGluing.rotate ψ.D
      rw [k11]
    · rcases k12 with h | ⟨h, h2⟩
      · exact Or.inl h
      · refine Or.inr ⟨h, ?_⟩
        change SkewGluing.rotate μ.upper = ∅
        simp [MarkedInner.upper, h2, SkewGluing.translate, SkewGluing.rotate]
    · change SkewGluing.rotate χ''.D = μ.rotate.compose (γ χ₁.D)
      rw [k13]
      change SkewGluing.rotate (μ.compose (γ (SkewGluing.rotate χ₁.D))) = _
      rw [← MarkedInner.rotate_compose hγX.2.1 μ]
      rcases k12 with h | ⟨h, -⟩
      · rw [h]; change μ.rotate.compose (SkewGluing.rotate (SkewGluing.rotate χ₁.D)) = _
        rw [SkewGluing.rotate_rotate]; rfl
      · rw [h]
        change μ.rotate.compose (SkewGluing.rotate (antitranspose (SkewGluing.rotate χ₁.D))) = _
        rw [rotate_antitranspose_rotate]
  · have hd2 : χ₂.ω.case = .d := hsame ▸ hd
    obtain ⟨χ', ψ, μ, γ, u, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13⟩ :=
      mixed_fold_of_roots_d T hg2 hd hd2
    exact ⟨χ', ψ, μ, γ, u, k1, k2, k3, by rw [k4, hd], k5, k6, k7, k8, k9, k10, k11, k12, k13⟩

end FoldSupplied

end SkewGluing
