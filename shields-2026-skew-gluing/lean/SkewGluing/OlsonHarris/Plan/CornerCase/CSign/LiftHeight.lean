import SkewGluing.OlsonHarris.Plan.CornerCase.CSign.FHeight
import SkewGluing.OlsonHarris.Plan.CornerCase.Lift

/-!
# The heights of the lifted border strips

Formalizes `shields-2026-skew-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `eq:gluing-offsets`): thesis Lemma 5.5.11 (`OlsonHarris2024HopfApplications`).

For a legal mark `ω` of case (c) with phases `s`, `t`, a connected outer `D` of span `r`, and a
ribbon `A` of size `m` with least content `μ + j` removable on the right (respectively on the
left), the height of the lift `cornerLift ω D m s A` (respectively `cornerLift ω D m t A`) is, with
`S_i = profS D (μ + i)` and `p = v₁`,
`ht = -m p + S_j - S_{j+m}` (respectively `-m p + S_j - S_{j+m} - 1`).

The border strip starts at the position `j q + s` (respectively `j q + t`) of the southeast word
of the composite and has `m q` cells; its height is the difference `h_{n₀} - h_{n₀ + m q - 1}` of
the last rows of its end diagonals (`ribbonHeight_windowRibbon`).  At a window start of a ribbon
removable on the right the word has the bit `B = 0`, so the start may be moved one diagonal
back, which puts both ends on the residue `s - 1 ∈ [t, s - 1]` and `corner_hi_diff` applies; for
a ribbon removable on the left both ends are moved to the residue `t`, and the bit at the first
diagonal after the window is `B = 1 - A^D_{j+m} = 1`.

Sorry-free.
-/

namespace SkewGluing

namespace Plan

namespace Corner

namespace CSign

open MarkedInner

variable {ω : MarkedInner} {D : Diagram}

theorem wordB_eq_diff (F : Diagram) (k : ℤ) :
    wordB F k = diagHi F (minContent F + k - 1) - diagHi F (minContent F + k) := rfl

/-- The height of the lift of a ribbon removable on the right. -/
theorem ribbonHeight_cornerLift_right (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D)
    (hc : ω.case = .c) {s t : ℤ} (hph : ω.IsPhases s t) {m : ℕ} (hm : 0 < m) {A : Diagram}
    {j : ℤ} (hj0 : 0 ≤ j) (hjm : j + m ≤ (span D : ℤ)) (hB : Bext D j = 0)
    (hmc : minContent A = minContent D + j) :
    (ribbonHeight (cornerLift ω D m s A) : ℤ) =
      -(m : ℤ) * ω.rowShift + profS D (minContent D + j) - profS D (minContent D + (j + m)) := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph
  have hlt := h.phases_lt (Or.inl hc) hph
  have hq0 : 0 < ω.period := by omega
  have hF : IsConnectedSkew (ω.compose D) := h.1.isConnectedSkew_compose hD
  have hminF := h.minContent_compose' hD
  have hspanF : (span (ω.compose D) : ℤ) = (span D : ℤ) * ω.period + ω.widthZ := by
    rw [h.span_compose_eq hD, span_eq_of_isConnectedSkew hD]
  have hN0 : 0 < m * ω.period.toNat := Nat.mul_pos hm (by omega)
  have hNcast : ((m * ω.period.toNat : ℕ) : ℤ) = m * ω.period := by
    push_cast; rw [Int.toNat_of_nonneg hq0.le]
  have hm1 : (1 : ℤ) ≤ m := by exact_mod_cast hm
  have hbig : ((j + m : ℤ)) * ω.period ≤ (span D : ℤ) * ω.period := by nlinarith
  have hj1 : j * ω.period ≥ 0 := by nlinarith
  have hjm1 : (j + m) * ω.period = j * ω.period + m * ω.period := by ring
  have hmq : (1 : ℤ) * ω.period ≤ m * ω.period := by nlinarith
  have hcF : ∀ k : ℤ, k ∈ contents (ω.compose D) ↔
      minContent (ω.compose D) ≤ k ∧ k < minContent (ω.compose D) + span (ω.compose D) :=
    fun k => contents_iff hF
  have hstart : minContent ω.E + minContent A * ω.period + s =
      minContent (ω.compose D) + (j * ω.period + s) := by
    rw [hmc, hminF]; ring
  have hlift : cornerLift ω D m s A = windowRibbon (ω.compose D)
      (minContent (ω.compose D) + (j * ω.period + s)) (m * ω.period.toNat) := by
    unfold cornerLift
    rw [hstart]
  rw [hlift, ribbonHeight_windowRibbon hF hN0 ((hcF _).mpr ⟨by omega, by omega⟩)
    ((hcF _).mpr ⟨by rw [hNcast]; omega, by rw [hNcast]; omega⟩), hNcast]
  obtain ⟨hPs, -⟩ := corner_word_facts h hD hc hph
  have hB0 : wordB (ω.compose D) (j * ω.period + s) = 0 := by
    rw [hPs j hj0 (by
      have : (span D : ℤ) * ω.period + ω.widthZ - 1 ≥ (j + 1) * ω.period + s - 1 + 0 := by
        nlinarith
      nlinarith), hB]
  rw [wordB_eq_diff] at hB0
  have e1 : minContent (ω.compose D) + (j * ω.period + s) - 1 =
      minContent (ω.compose D) + (j * ω.period + (s - 1)) := by ring
  rw [e1] at hB0
  have hd := corner_hi_diff h hD hc hph (i := j) (a := s - 1) m (by omega) le_rfl hj0 hjm
  have e2 : minContent (ω.compose D) + (j * ω.period + s) + (m * ω.period) - 1 =
      minContent (ω.compose D) + ((j + m) * ω.period + (s - 1)) := by ring
  rw [e2]
  omega

/-- The height of the lift of a ribbon removable on the left. -/
theorem ribbonHeight_cornerLift_left (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D)
    (hc : ω.case = .c) {s t : ℤ} (hph : ω.IsPhases s t) {m : ℕ} (hm : 0 < m) {A : Diagram}
    {j : ℤ} (hj0 : 0 ≤ j) (hjm : j + m ≤ (span D : ℤ)) (hA : Aext D (j + m) = 0)
    (hmc : minContent A = minContent D + j) :
    (ribbonHeight (cornerLift ω D m t A) : ℤ) =
      -(m : ℤ) * ω.rowShift + profS D (minContent D + j) - profS D (minContent D + (j + m)) -
        1 := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph
  have hlt := h.phases_lt (Or.inl hc) hph
  have hq0 : 0 < ω.period := by omega
  have hF : IsConnectedSkew (ω.compose D) := h.1.isConnectedSkew_compose hD
  have hminF := h.minContent_compose' hD
  have hspanF : (span (ω.compose D) : ℤ) = (span D : ℤ) * ω.period + ω.widthZ := by
    rw [h.span_compose_eq hD, span_eq_of_isConnectedSkew hD]
  have hN0 : 0 < m * ω.period.toNat := Nat.mul_pos hm (by omega)
  have hNcast : ((m * ω.period.toNat : ℕ) : ℤ) = m * ω.period := by
    push_cast; rw [Int.toNat_of_nonneg hq0.le]
  have hm1 : (1 : ℤ) ≤ m := by exact_mod_cast hm
  have hbig : ((j + m : ℤ)) * ω.period ≤ (span D : ℤ) * ω.period := by nlinarith
  have hj1 : j * ω.period ≥ 0 := by nlinarith
  have hjm1 : (j + m) * ω.period = j * ω.period + m * ω.period := by ring
  have hmq : (1 : ℤ) * ω.period ≤ m * ω.period := by nlinarith
  have hcF : ∀ k : ℤ, k ∈ contents (ω.compose D) ↔
      minContent (ω.compose D) ≤ k ∧ k < minContent (ω.compose D) + span (ω.compose D) :=
    fun k => contents_iff hF
  have hstart : minContent ω.E + minContent A * ω.period + t =
      minContent (ω.compose D) + (j * ω.period + t) := by
    rw [hmc, hminF]; ring
  have hlift : cornerLift ω D m t A = windowRibbon (ω.compose D)
      (minContent (ω.compose D) + (j * ω.period + t)) (m * ω.period.toNat) := by
    unfold cornerLift
    rw [hstart]
  rw [hlift, ribbonHeight_windowRibbon hF hN0 ((hcF _).mpr ⟨by omega, by omega⟩)
    ((hcF _).mpr ⟨by rw [hNcast]; omega, by rw [hNcast]; omega⟩), hNcast]
  obtain ⟨-, hPt, -⟩ := corner_word_facts h hD hc hph
  have hB1 : wordB (ω.compose D) ((j + m) * ω.period + t) = 1 := by
    have := hPt (j + m) (by omega) (by nlinarith) (by nlinarith)
    have hA' : Aext D (j + m) = 0 := hA
    rw [this, hA']; norm_num
  rw [wordB_eq_diff] at hB1
  have hd := corner_hi_diff h hD hc hph (i := j) (a := t) m le_rfl (by omega) hj0 hjm
  have e2 : minContent (ω.compose D) + (j * ω.period + t) + (m * ω.period) - 1 =
      minContent (ω.compose D) + ((j + m) * ω.period + t) - 1 := by ring
  rw [e2]
  omega

end CSign

end Corner

end Plan

end SkewGluing
