import SkewGluing.Coding.Reversal

/-!
# Case (c) of `lem:gluing-coding`

Formalizes `shields-2026-skew-gluing.tex`, «Diagonal geometry» (`lem:gluing-coding`,
`eq:gluing-holes`, `eq:gluing-caps`, `eq:gluing-interface`, case (c)).

**Differs from the paper's route.**  The paper obtains case (c) by antitransposition; here the
rotation `ω.compose D = rotate (ω*.compose D*)` reverses the words of the case-(d) composite
`ω*.compose D*`, whose phases are `(w - t, w - s)`.  The resulting interface of case (c) reads
`B_{jq+t} = 1 - A^D_j`, `B_{jq+s} = B^D_j`.

Sorry-free.
-/

namespace SkewGluing

theorem emod_shift {N x q w r : ℤ} (hN : N = r * q + w) : (N - x - q) % q = (w - x) % q := by
  have : N - x - q = (w - x) + (r - 1) * q := by rw [hN]; ring
  rw [this, Int.add_mul_emod_self_right]

namespace MarkedInner

variable {ω : MarkedInner} {D : Diagram}

/-- The case-(d) composite whose rotation is the case-(c) composite. -/
theorem IsLegalNonempty.rotate_data (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D)
    (hcc : ω.case = .c) :
    IsConnectedSkew (ω.rotate.compose (SkewGluing.rotate D)) ∧
    ω.compose D = SkewGluing.rotate (ω.rotate.compose (SkewGluing.rotate D)) ∧
    span (ω.compose D) = span (ω.rotate.compose (SkewGluing.rotate D)) := by
  have hG := h.rotate.isConnectedSkew_compose_d (isConnectedSkew_rotate hD) (rotate_case_d hcc)
  have hF := compose_rotate_c hcc hD.2.1
  refine ⟨hG, hF, ?_⟩
  rw [hF, span_rotate]

/-- **`lem:gluing-coding`, holes, case (c).**  Both words have period `q` except at the residues of
the table `eq:gluing-holes`: none for `A`, and `t, s` for `B`.  **Differs from the paper's route.**
The paper uses antitransposition; here the words of the rotated case-(d) composite are reversed. -/
theorem IsLegalNonempty.periodExcept_c (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D)
    (hcc : ω.case = .c) {s t : ℤ} (hph : ω.IsPhases s t) :
    PeriodWords.PeriodExcept (span (ω.compose D) - 1) ω.period.toNat
      (holesA ω.case s t) (wordA (ω.compose D)) ∧
    PeriodWords.PeriodExcept (span (ω.compose D) - 1) ω.period.toNat
      (holesB ω.case s t) (wordB (ω.compose D)) := by
  obtain ⟨hG, hF, hsp⟩ := h.rotate_data hD hcc
  have hcd := rotate_case_d hcc
  have hph' := h.isPhases_rotate hph
  have hper := h.rotate.periodExcept_d (isConnectedSkew_rotate hD) hcd hph'
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hN := h.span_compose_eq hD
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph
  have hmM := minContent_le (maxContent_mem hD.2.1)
  have hL : (((span (ω.compose D) - 1 : ℕ)) : ℤ) = (span (ω.compose D) : ℤ) - 1 := by
    have := mul_le_mul_of_nonneg_right
      (show 1 ≤ maxContent D - minContent D + 1 by omega) (show 0 ≤ ω.period by omega)
    omega
  have hpq : ((ω.period.toNat : ℕ) : ℤ) = ω.period := Int.toNat_of_nonneg (by omega)
  have hpr : ω.rotate.period = ω.period := rfl
  rw [hpr, ← hsp] at hper
  obtain ⟨hA, hB⟩ := hper
  have hcdc : ω.rotate.case = .d := hcd
  simp only [holesA, holesB, hcdc, hcc] at hA hB ⊢
  have hwA : ∀ k, wordA (ω.compose D) k =
      wordB (ω.rotate.compose (SkewGluing.rotate D)) ((span (ω.compose D) : ℤ) - k) := fun k => by
    have := wordA_rotate hG k
    rw [← hF] at this
    rw [this, hsp]
  have hwB : ∀ k, wordB (ω.compose D) k =
      wordA (ω.rotate.compose (SkewGluing.rotate D)) ((span (ω.compose D) : ℤ) - k) := fun k => by
    have := wordB_rotate hG k
    rw [← hF] at this
    rw [this, hsp]
  refine ⟨?_, ?_⟩
  · exact periodExcept_reverse (S := ∅) (f := wordB (ω.rotate.compose (SkewGluing.rotate D)))
      (N := (span (ω.compose D) : ℤ)) (by omega) hwA hB (fun x hx => by simp)
  · refine periodExcept_reverse (S := {ω.widthZ - s, ω.widthZ - t})
      (f := wordA (ω.rotate.compose (SkewGluing.rotate D)))
      (N := (span (ω.compose D) : ℤ)) (by omega) hwB hA (fun x hx => ?_)
    rw [hpq] at hx ⊢
    rw [emod_shift hN]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx ⊢
    refine ⟨fun h1 => hx.2 ?_, fun h1 => hx.1 ?_⟩
    · exact emod_reflect (q := ω.period) (w := ω.widthZ) (x := x) (c := s) (by omega)
        (by omega) (by omega) (by omega) h1
    · exact emod_reflect (q := ω.period) (w := ω.widthZ) (x := x) (c := t) (by omega)
        (by omega) (by omega) (by omega) h1

/-- **`eq:gluing-caps`, case (c).**  **Differs from the paper's route.**  Rotation reverses the
words and exchanges `A` and `B`, so the case-(c) analogues of the case-(d) statements concern the
word `B` of the composite: initial `B_t = 0` (for `t ≥ 1`), `B_s = 0`; terminal `B_{N-w+t} = 1`,
`B_{N-w+s} = 1` (for `s < w`); and `A_{N-w} = 1`, `A_{N-q} = 0`. -/
theorem IsLegalNonempty.caps_c (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D)
    (hcc : ω.case = .c) {s t : ℤ} (hph : ω.IsPhases s t) :
    (1 ≤ t → wordB (ω.compose D) t = 0) ∧ wordB (ω.compose D) s = 0 ∧
    wordB (ω.compose D) ((span (ω.compose D) : ℤ) - ω.widthZ + t) = 1 ∧
    (s < ω.widthZ → wordB (ω.compose D) ((span (ω.compose D) : ℤ) - ω.widthZ + s) = 1) ∧
    wordA (ω.compose D) ((span (ω.compose D) : ℤ) - ω.widthZ) = 1 ∧
    wordA (ω.compose D) ((span (ω.compose D) : ℤ) - ω.period) = 0 := by
  obtain ⟨hG, hF, hsp⟩ := h.rotate_data hD hcc
  have hcd := rotate_case_d hcc
  have hph' := h.isPhases_rotate hph
  have hq := h.width_lt_period
  have hw := h.width_pos
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph
  have hwA : ∀ k, wordA (ω.compose D) k =
      wordB (ω.rotate.compose (SkewGluing.rotate D)) ((span (ω.compose D) : ℤ) - k) := fun k => by
    have := wordA_rotate hG k
    rw [← hF] at this
    rw [this, hsp]
  have hwB : ∀ k, wordB (ω.compose D) k =
      wordA (ω.rotate.compose (SkewGluing.rotate D)) ((span (ω.compose D) : ℤ) - k) := fun k => by
    have := wordB_rotate hG k
    rw [← hF] at this
    rw [this, hsp]
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := h.rotate.caps_d (isConnectedSkew_rotate hD) hcd hph'
  simp only [← hsp, widthZ_rotate] at c3 c4
  simp only [widthZ_rotate] at c5
  have hpr : ω.rotate.period = ω.period := rfl
  rw [hpr] at c6
  refine ⟨fun h1 => ?_, ?_, ?_, fun h1 => ?_, ?_, ?_⟩
  · rw [hwB]
    have e : (span (ω.compose D) : ℤ) - t =
        (span (ω.compose D) : ℤ) - ω.widthZ + (ω.widthZ - t) := by
      ring
    rw [e]
    exact c4 (by omega)
  · rw [hwB]
    have e : (span (ω.compose D) : ℤ) - s =
        (span (ω.compose D) : ℤ) - ω.widthZ + (ω.widthZ - s) := by
      ring
    rw [e]
    exact c3
  · rw [hwB]
    have e : (span (ω.compose D) : ℤ) - ((span (ω.compose D) : ℤ) - ω.widthZ + t) =
        ω.widthZ - t := by
      ring
    rw [e]
    exact c2
  · rw [hwB]
    have e : (span (ω.compose D) : ℤ) - ((span (ω.compose D) : ℤ) - ω.widthZ + s) =
        ω.widthZ - s := by
      ring
    rw [e]
    exact c1 (by omega)
  · rw [hwA]
    have e : (span (ω.compose D) : ℤ) - ((span (ω.compose D) : ℤ) - ω.widthZ) = ω.widthZ := by ring
    rw [e]
    exact c5
  · rw [hwA]
    have e : (span (ω.compose D) : ℤ) - ((span (ω.compose D) : ℤ) - ω.period) = ω.period := by ring
    rw [e]
    exact c6

/-- **`eq:gluing-interface`, case (c).**  **Differs from the paper's route.**  For `1 ≤ j < N_D`
the exceptional bits of the word `B` of the parent in the block `j` read the outer:
`B_{jq+s} = B^D_j` and `B_{jq+t} = 1 - A^D_j`. -/
theorem IsLegalNonempty.interface_c (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D)
    (hcc : ω.case = .c) {s t : ℤ} (hph : ω.IsPhases s t) {j : ℤ} (hj1 : 1 ≤ j)
    (hj2 : j < (span D : ℤ)) :
    wordB (ω.compose D) (j * ω.period + s) = wordB D j ∧
    wordB (ω.compose D) (j * ω.period + t) = 1 - wordA D j := by
  obtain ⟨hG, hF, hsp⟩ := h.rotate_data hD hcc
  have hcd := rotate_case_d hcc
  have hph' := h.isPhases_rotate hph
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hN := h.span_compose_eq hD
  have hsD := span_eq_of_isConnectedSkew hD
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph
  have hwB : ∀ k, wordB (ω.compose D) k =
      wordA (ω.rotate.compose (SkewGluing.rotate D)) ((span (ω.compose D) : ℤ) - k) := fun k => by
    have := wordB_rotate hG k
    rw [← hF] at this
    rw [this, hsp]
  have hspR : (span (SkewGluing.rotate D) : ℤ) = span D := by rw [span_rotate]
  obtain ⟨i1, i2⟩ := h.rotate.interface_d (isConnectedSkew_rotate hD) hcd hph'
    (j := (span D : ℤ) - j) (by omega) (by omega)
  have hNr : (span (ω.compose D) : ℤ) = (span D : ℤ) * ω.period + ω.widthZ := by
    rw [hN, hsD]
  constructor
  · rw [hwB]
    have e : (span (ω.compose D) : ℤ) - (j * ω.period + s) =
        ((span D : ℤ) - j) * ω.rotate.period + (ω.widthZ - s) := by
      rw [hNr]
      change _ = _ * ω.period + _
      ring
    rw [e, i1, wordA_rotate hD]
    congr 1
    ring
  · rw [hwB]
    have e : (span (ω.compose D) : ℤ) - (j * ω.period + t) =
        ((span D : ℤ) - j) * ω.rotate.period + (ω.widthZ - t) := by
      rw [hNr]
      change _ = _ * ω.period + _
      ring
    rw [e, i2, wordB_rotate hD]
    congr 2
    ring

end MarkedInner

end SkewGluing
