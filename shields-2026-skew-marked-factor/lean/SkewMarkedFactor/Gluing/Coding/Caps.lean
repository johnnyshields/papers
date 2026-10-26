/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
-- TODO-COPIED: skew-gluing/lean/SkewGluing/Coding/Caps.lean
import SkewMarkedFactor.Gluing.Coding.Periodic

/-!
# End caps and the interface of the parent boundary words

Formalizes `shields-2026-skew-gluing.tex`, «Diagonal geometry» (`lem:gluing-coding`,
`eq:gluing-caps`, `eq:gluing-interface`, and the bits `B_w = 1`, `B_q = 0` of case (d)).

Positions are the southwest-normalized contents, `N = N_F = r q + w`.  A bit at the content `0`
or `N` is not defined, so the bits `A_t` (initial, `t ≥ 1`) and `B_{N-w+s}`, `A_{N-w+s}` (terminal,
`s < w`) are stated only where the position lies in `1, …, N - 1`.

Sorry-free.
-/

namespace SkewMarkedFactor.Gluing

namespace MarkedInner

variable {ω : MarkedInner} {D : Diagram}

/-- **`eq:gluing-caps`, case (a).**  Initial bits `A_t = 1` (for `t ≥ 1`), `B_s = 0`; terminal bits
`A_{N-w+t} = 0`, `B_{N-w+s} = 1` (for `s < w`). -/
theorem IsLegalNonempty.caps_a (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D)
    (hca : ω.case = .a) {s t : ℤ} (hph : ω.IsPhases s t) :
    (1 ≤ t → wordA (ω.compose D) t = 1) ∧ wordB (ω.compose D) s = 0 ∧
    wordA (ω.compose D) ((span (ω.compose D) : ℤ) - ω.widthZ + t) = 0 ∧
    (s < ω.widthZ → wordB (ω.compose D) ((span (ω.compose D) : ℤ) - ω.widthZ + s) = 1) := by
  have hmix : ¬ ω.case.IsMixed := by simp [AttachCase.IsMixed, hca]
  have hz := (ordT_eq_zero_iff hmix).mpr hca
  have hmM : minContent D ≤ maxContent D := minContent_le (maxContent_mem hD.2.1)
  have hc := ord_classRows h hD hmix
  have hmin := h.minContent_compose' hD
  have hN := h.span_compose_eq hD
  have hq := h.width_lt_period
  have hw := h.width_pos
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph
  have cl := ord_caps_lo h hD hmix hph
  have ch := ord_caps_hi h hD hmix hph
  have vm : ∀ a, ValidClass (minContent D) (maxContent D) ω.widthZ (minContent D) a :=
    fun a => Or.inl ⟨le_refl _, hmM⟩
  have vM : ∀ a, a < ω.widthZ →
      ValidClass (minContent D) (maxContent D) ω.widthZ (maxContent D + 1) a :=
    fun a ha => Or.inr ⟨rfl, ha⟩
  refine ⟨fun h1 => ?_, ?_, ?_, fun h1 => ?_⟩
  · rw [hc.wordA_class' hmin (J := minContent D) (a := t) (by ring) ht1 (by omega) (vm t)
      (fun h0 => by omega)]
    exact cl.1 hz h1
  · rw [hc.wordB_class' hmin (J := minContent D) (a := s) (by ring) (by omega) (by omega) (vm s)
      (fun h0 => by omega)]
    exact ch.1 hz
  · rw [hc.wordA_class' hmin (J := maxContent D + 1) (a := t) (by rw [hN]; ring) ht1 (by omega)
      (vM t ht2) (fun h0 => by omega)]
    exact cl.2.2.1 hz
  · rw [hc.wordB_class' hmin (J := maxContent D + 1) (a := s) (by rw [hN]; ring) (by omega)
      (by omega) (vM s h1) (fun h0 => by omega)]
    exact ch.2.2.1 hz h1

/-- **`eq:gluing-caps`, case (b).**  Initial bits `B_t = 0` (for `t ≥ 1`), `A_s = 1`; terminal bits
`B_{N-w+t} = 1`, `A_{N-w+s} = 0` (for `s < w`).  **Differs from the paper's route.** The paper
obtains case (b) from case (a) by antitransposition; here both ordinary cases are read from the same
class formulas. -/
theorem IsLegalNonempty.caps_b (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D)
    (hcb : ω.case = .b) {s t : ℤ} (hph : ω.IsPhases s t) :
    (1 ≤ t → wordB (ω.compose D) t = 0) ∧ wordA (ω.compose D) s = 1 ∧
    wordB (ω.compose D) ((span (ω.compose D) : ℤ) - ω.widthZ + t) = 1 ∧
    (s < ω.widthZ → wordA (ω.compose D) ((span (ω.compose D) : ℤ) - ω.widthZ + s) = 0) := by
  have hmix : ¬ ω.case.IsMixed := by simp [AttachCase.IsMixed, hcb]
  have hz : ω.ordT = 1 := by simp [ordT, hcb]
  have hmM : minContent D ≤ maxContent D := minContent_le (maxContent_mem hD.2.1)
  have hc := ord_classRows h hD hmix
  have hmin := h.minContent_compose' hD
  have hN := h.span_compose_eq hD
  have hq := h.width_lt_period
  have hw := h.width_pos
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph
  have cl := ord_caps_lo h hD hmix hph
  have ch := ord_caps_hi h hD hmix hph
  have vm : ∀ a, ValidClass (minContent D) (maxContent D) ω.widthZ (minContent D) a :=
    fun a => Or.inl ⟨le_refl _, hmM⟩
  have vM : ∀ a, a < ω.widthZ →
      ValidClass (minContent D) (maxContent D) ω.widthZ (maxContent D + 1) a :=
    fun a ha => Or.inr ⟨rfl, ha⟩
  refine ⟨fun h1 => ?_, ?_, ?_, fun h1 => ?_⟩
  · rw [hc.wordB_class' hmin (J := minContent D) (a := t) (by ring) ht1 (by omega) (vm t)
      (fun h0 => by omega)]
    exact ch.2.1 hz h1
  · rw [hc.wordA_class' hmin (J := minContent D) (a := s) (by ring) (by omega) (by omega) (vm s)
      (fun h0 => by omega)]
    exact cl.2.1 hz
  · rw [hc.wordB_class' hmin (J := maxContent D + 1) (a := t) (by rw [hN]; ring) ht1 (by omega)
      (vM t ht2) (fun h0 => by omega)]
    exact ch.2.2.2 hz
  · rw [hc.wordA_class' hmin (J := maxContent D + 1) (a := s) (by rw [hN]; ring) (by omega)
      (by omega) (vM s h1) (fun h0 => by omega)]
    exact cl.2.2.2 hz h1

/-- **`eq:gluing-caps`, case (d), and `B_w = 1`, `B_q = 0`.**  Initial bits `A_t = 1` (for `t ≥ 1`),
`A_s = 1`; terminal bits `A_{N-w+t} = 0`, `A_{N-w+s} = 0` (for `s < w`); and the southeast word has
`B_w = 1`, `B_q = 0`. -/
theorem IsLegalNonempty.caps_d (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D)
    (hcd : ω.case = .d) {s t : ℤ} (hph : ω.IsPhases s t) :
    (1 ≤ t → wordA (ω.compose D) t = 1) ∧ wordA (ω.compose D) s = 1 ∧
    wordA (ω.compose D) ((span (ω.compose D) : ℤ) - ω.widthZ + t) = 0 ∧
    (s < ω.widthZ → wordA (ω.compose D) ((span (ω.compose D) : ℤ) - ω.widthZ + s) = 0) ∧
    wordB (ω.compose D) ω.widthZ = 1 ∧ wordB (ω.compose D) ω.period = 0 := by
  have hmM : minContent D ≤ maxContent D := minContent_le (maxContent_mem hD.2.1)
  have hlt := h.phases_lt (Or.inr hcd) hph
  have hc := mix_classRows h hD hcd hph hlt
  have hmin := h.minContent_compose' hD
  have hN := h.span_compose_eq hD
  have hq := h.width_lt_period
  have hw := h.width_pos
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph
  have vm : ∀ a, ValidClass (minContent D) (maxContent D) ω.widthZ (minContent D) a :=
    fun a => Or.inl ⟨le_refl _, hmM⟩
  have vM : ∀ a, a < ω.widthZ →
      ValidClass (minContent D) (maxContent D) ω.widthZ (maxContent D + 1) a :=
    fun a ha => Or.inr ⟨rfl, ha⟩
  refine ⟨fun h1 => ?_, ?_, ?_, fun h1 => ?_, ?_, ?_⟩
  · rw [hc.wordA_class' hmin (J := minContent D) (a := t) (by ring) ht1 (by omega) (vm t)
      (fun h0 => by omega)]
    exact mix_classBitLo_init_t h hD hcd hph h1
  · rw [hc.wordA_class' hmin (J := minContent D) (a := s) (by ring) (by omega) (by omega) (vm s)
      (fun h0 => by omega)]
    exact mix_classBitLo_init_s h hD hcd hph
  · rw [hc.wordA_class' hmin (J := maxContent D + 1) (a := t) (by rw [hN]; ring) ht1 (by omega)
      (vM t ht2) (fun h0 => by omega)]
    exact mix_classBitLo_term_t h hD hcd hph
  · rw [hc.wordA_class' hmin (J := maxContent D + 1) (a := s) (by rw [hN]; ring) (by omega)
      (by omega) (vM s h1) (fun h0 => by omega)]
    exact mix_classBitLo_term_s h hD hcd hph h1
  · rw [hc.wordB_class' hmin (J := minContent D) (a := ω.widthZ) (by ring) (by omega) hq (vm _)
      (fun h0 => by omega)]
    exact mix_classBitHi_w h hcd _
  · have vq : ValidClass (minContent D) (maxContent D) ω.widthZ (minContent D + 1) 0 := by
      unfold ValidClass
      omega
    rw [hc.wordB_class' hmin (J := minContent D + 1) (a := 0) (by ring) (le_refl _) (by omega)
      vq (fun _ => by omega), mix_classBitHi h hcd _ 0 (le_refl _) (by omega)]
    simp

/-- **`eq:gluing-interface`, case (d).**  For `1 ≤ j < N_D` the two exceptional bits of the parent
in the block `j` read the outer: `A_{jq+t} = A^D_j` and `A_{jq+s} = 1 - B^D_j`. -/
theorem IsLegalNonempty.interface_d (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D)
    (hcd : ω.case = .d) {s t : ℤ} (hph : ω.IsPhases s t) {j : ℤ} (hj1 : 1 ≤ j)
    (hj2 : j < (span D : ℤ)) :
    wordA (ω.compose D) (j * ω.period + t) = wordA D j ∧
    wordA (ω.compose D) (j * ω.period + s) = 1 - wordB D j := by
  have hmM : minContent D ≤ maxContent D := minContent_le (maxContent_mem hD.2.1)
  have hlt := h.phases_lt (Or.inr hcd) hph
  have hc := mix_classRows h hD hcd hph hlt
  have hmin := h.minContent_compose' hD
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hsp := span_eq_of_isConnectedSkew hD
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph
  have hv : ∀ a, ValidClass (minContent D) (maxContent D) ω.widthZ (minContent D + j) a :=
    fun a => Or.inl ⟨by omega, by omega⟩
  constructor
  · rw [hc.wordA_class' hmin (J := minContent D + j) (a := t) (by ring) ht1 (by omega) (hv t)
      (fun h0 => by omega)]
    rw [mix_classBitLo_t h hD hcd hph (by omega) (by omega)]
    unfold wordA
    congr 1
  · rw [hc.wordA_class' hmin (J := minContent D + j) (a := s) (by ring) (by omega) (by omega)
      (hv s) (fun h0 => by omega)]
    rw [mix_classBitLo_s h hD hcd hph (by omega) (by omega)]
    unfold wordB
    congr 2

end MarkedInner

end SkewMarkedFactor.Gluing
