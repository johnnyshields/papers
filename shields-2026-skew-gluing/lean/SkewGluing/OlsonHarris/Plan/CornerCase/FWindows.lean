import SkewGluing.OlsonHarris.Plan.CornerCase.FWords
import SkewGluing.OlsonHarris.Plan.CornerCase.WordWindows
import SkewGluing.OlsonHarris.Plan.CornerCase.Windows

/-!
# The southeast word of a corner composite reads the outer

Formalizes `shields-2026-skew-gluing.tex`, «Diagonal geometry» (`lem:gluing-coding`,
`eq:gluing-holes`, `eq:gluing-caps`, `eq:gluing-interface`) as used in thesis Lemma 5.5.5
(`OlsonHarris2024HopfApplications`).

For a legal mark `ω` of case (c) with phases `s`, `t`, a connected outer `D` of span `r` and
`F = D ∘_ω E` of span `r q + w`, the southeast word `B = wordB F` has period `q` except at the
residues `t`, `s`; at the residue `s` of the block `j` it reads the bit `B^D_j` of the outer, at the
residue `t` it reads `1 - A^D_j`; and `B_q = 0` (`1 ≤ t`), `B_w = 1` (`s < w`).  The outer's bits
are extended by `B^D_0 = 0`, `B^D_r = 1`, `A^D_0 = 1`, `A^D_r = 0` (`Bext`, `Aext`).

`corner_window_classification`: the windows `[k, k + m q)` of `F` that start a ribbon removable on
the right are exactly the windows at the residue `s` over the right windows of `D`, and at the
residue `t` over the left windows of `D`.

Sorry-free.
-/

namespace SkewGluing

namespace Plan

namespace Corner

open MarkedInner

/-- The southeast word of the outer, extended by `B_0 = 0` and `B_r = 1`. -/
def Bext (D : Diagram) (j : ℤ) : ℤ :=
  if j = 0 then 0 else if j = (span D : ℤ) then 1 else wordB D j

/-- The northwest word of the outer, extended by `A_0 = 1` and `A_r = 0`. -/
def Aext (D : Diagram) (j : ℤ) : ℤ :=
  if j = 0 then 1 else if j = (span D : ℤ) then 0 else wordA D j

variable {ω : MarkedInner} {D : Diagram}

/-- The facts about the southeast word of the corner composite, in the form consumed by
`window_classification` (with `q = ω.period`, `w = ω.widthZ`, `r = span D`, `B = wordB F`). -/
theorem corner_word_facts (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D) (hcc : ω.case = .c)
    {s t : ℤ} (hph : ω.IsPhases s t) :
    (∀ j, 0 ≤ j → j * ω.period + s ≤ (span D : ℤ) * ω.period + ω.widthZ - 1 →
      wordB (ω.compose D) (j * ω.period + s) = Bext D j) ∧
    (∀ j, 0 ≤ j → j * ω.period + t ≤ (span D : ℤ) * ω.period + ω.widthZ - 1 →
      1 ≤ j * ω.period + t →
      wordB (ω.compose D) (j * ω.period + t) = 1 - Aext D j) ∧
    (∀ x, 1 ≤ x → x + ω.period ≤ (span D : ℤ) * ω.period + ω.widthZ - 1 →
      x % ω.period ≠ s → x % ω.period ≠ t →
      wordB (ω.compose D) x = wordB (ω.compose D) (x + ω.period)) ∧
    (1 ≤ t → wordB (ω.compose D) ω.period = 0) ∧
    (s < ω.widthZ → wordB (ω.compose D) ω.widthZ = 1) := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph
  have hlt := h.phases_lt (Or.inl hcc) hph
  have hr1 : 1 ≤ (span D : ℤ) := by
    have h0 := hD.2.1
    have : 0 < span D := Finset.card_pos.mpr (h0.image _)
    omega
  have hN : (span (ω.compose D) : ℤ) = (span D : ℤ) * ω.period + ω.widthZ := by
    have := h.span_compose_eq hD
    have h2 := span_eq_of_isConnectedSkew hD
    rw [this, h2]
  obtain ⟨c1, c2, c3, c4, -, -⟩ := h.caps_c hD hcc hph
  have hr0' : span D ≠ 0 := by omega
  have hbig : ∀ j : ℤ, (span D : ℤ) < j → ((span D : ℤ) + 1) * ω.period ≤ j * ω.period :=
    fun j hj => by nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j hj0 hj
    by_cases hj1 : j = 0
    · subst hj1
      simpa [Bext] using c2
    · by_cases hjr : j = (span D : ℤ)
      · have hsw : s < ω.widthZ := by
          rw [hjr] at hj
          omega
        have e : (span (ω.compose D) : ℤ) - ω.widthZ + s = j * ω.period + s := by
          rw [hN, hjr]; ring
        have hB : Bext D j = 1 := by simp [Bext, hjr, hr0']
        rw [hB, ← e]
        exact c4 hsw
      · have hjlt : j < (span D : ℤ) := by
          rcases lt_or_gt_of_ne hjr with h1 | h1
          · exact h1
          · exfalso
            have := hbig j h1
            nlinarith
        have := (h.interface_c hD hcc hph (j := j) (by omega) hjlt).1
        simp only [Bext, hj1, hjr, ite_false]
        exact this
  · intro j hj0 hj hpos
    by_cases hj1 : j = 0
    · subst hj1
      simp only [zero_mul, zero_add] at hpos ⊢
      have := c1 hpos
      simp only [Aext, ite_true]
      rw [this]; ring
    · by_cases hjr : j = (span D : ℤ)
      · have e : (span (ω.compose D) : ℤ) - ω.widthZ + t = j * ω.period + t := by
          rw [hN, hjr]; ring
        have hA : Aext D j = 0 := by simp [Aext, hjr, hr0']
        rw [hA, ← e, c3]; ring
      · have hjlt : j < (span D : ℤ) := by
          rcases lt_or_gt_of_ne hjr with h1 | h1
          · exact h1
          · exfalso
            have := hbig j h1
            nlinarith
        have := (h.interface_c hD hcc hph (j := j) (by omega) hjlt).2
        simp only [Aext, hj1, hjr, ite_false]
        exact this
  · -- periodicity
    intro x hx1 hx2 hs' ht'
    have hper := (h.periodExcept_c hD hcc hph).2
    have hL : (((span (ω.compose D) - 1 : ℕ)) : ℤ) = (span D : ℤ) * ω.period + ω.widthZ - 1 := by
      have : 1 ≤ span (ω.compose D) := by
        have : (1 : ℤ) ≤ span (ω.compose D) := by
          rw [hN]
          nlinarith
        exact_mod_cast this
      rw [Nat.cast_sub this, hN]; simp
    have hpq : ((ω.period.toNat : ℕ) : ℤ) = ω.period := Int.toNat_of_nonneg (by omega)
    unfold PeriodWords.PeriodExcept at hper
    have := hper x (by
      rw [Finset.mem_Icc, hL, hpq]
      exact ⟨hx1, by omega⟩) (by
      simp only [holesB, hcc, Finset.mem_insert, Finset.mem_singleton, not_or]
      rw [hpq]
      exact ⟨ht', hs'⟩)
    rw [hpq] at this
    exact this
  · -- `B_q = 0`
    intro ht1'
    obtain ⟨hG, hF, hsp⟩ := h.rotate_data hD hcc
    have hph' := h.isPhases_rotate hph
    have hcd := rotate_case_d hcc
    have hDr := isConnectedSkew_rotate hD
    have hlt' := h.rotate.phases_lt (Or.inr hcd) hph'
    have hc' := mix_classRows h.rotate hDr hcd hph' hlt'
    have hmin' := h.rotate.minContent_compose' hDr
    have hsDr := span_eq_of_isConnectedSkew hDr
    have hspr : (span (SkewGluing.rotate D) : ℤ) = span D := by rw [span_rotate]
    have hNG : (span (ω.rotate.compose (SkewGluing.rotate D)) : ℤ) =
        (span D : ℤ) * ω.period + ω.widthZ := by rw [← hsp]; exact hN
    have e1 : wordB (ω.compose D) ω.period = wordA (ω.rotate.compose (SkewGluing.rotate D))
        ((span (ω.rotate.compose (SkewGluing.rotate D)) : ℤ) - ω.period) := by
      have := wordB_rotate hG ω.period
      rw [← hF] at this
      exact this
    have e2 := hc'.wordA_class' hmin' (J := maxContent (SkewGluing.rotate D))
      (a := ω.rotate.widthZ)
      (k := (span (ω.rotate.compose (SkewGluing.rotate D)) : ℤ) - ω.period) (by
        rw [hNG, widthZ_rotate]
        change _ = (_ - _) * ω.period + _
        nlinarith) (by rw [widthZ_rotate]; omega) (by rw [widthZ_rotate]; exact hq)
      (Or.inl ⟨minContent_le (maxContent_mem hDr.2.1), le_rfl⟩) (fun h0 => by
        rw [widthZ_rotate] at h0; omega)
    rw [e1, e2]
    have := mix_classBitLo_w h.rotate hDr hcd hph' (by
      rw [widthZ_rotate]; omega)
    rw [widthZ_rotate] at this ⊢
    exact this
  · -- `B_w = 1`
    intro hsw
    obtain ⟨hG, hF, hsp⟩ := h.rotate_data hD hcc
    have hph' := h.isPhases_rotate hph
    have hcd := rotate_case_d hcc
    have hDr := isConnectedSkew_rotate hD
    have hlt' := h.rotate.phases_lt (Or.inr hcd) hph'
    have hc' := mix_classRows h.rotate hDr hcd hph' hlt'
    have hmin' := h.rotate.minContent_compose' hDr
    have hsDr := span_eq_of_isConnectedSkew hDr
    have hspr : (span (SkewGluing.rotate D) : ℤ) = span D := by rw [span_rotate]
    have hNG : (span (ω.rotate.compose (SkewGluing.rotate D)) : ℤ) =
        (span D : ℤ) * ω.period + ω.widthZ := by rw [← hsp]; exact hN
    have e1 : wordB (ω.compose D) ω.widthZ = wordA (ω.rotate.compose (SkewGluing.rotate D))
        ((span (ω.rotate.compose (SkewGluing.rotate D)) : ℤ) - ω.widthZ) := by
      have := wordB_rotate hG ω.widthZ
      rw [← hF] at this
      exact this
    have e2 := hc'.wordA_class' hmin' (J := maxContent (SkewGluing.rotate D) + 1)
      (a := 0) (k := (span (ω.rotate.compose (SkewGluing.rotate D)) : ℤ) - ω.widthZ) (by
        rw [hNG]
        change _ = (_ - _) * ω.period + _
        nlinarith) le_rfl (by change (0 : ℤ) < ω.period; omega)
      (Or.inr ⟨rfl, by rw [widthZ_rotate]; omega⟩) (fun _ => by
        have := minContent_le (maxContent_mem hDr.2.1)
        omega)
    rw [e1, e2]
    exact mix_classBitLo_zero h.rotate hDr hcd hph' (by omega)

end Corner

end Plan

end SkewGluing
