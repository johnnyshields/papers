import SkewGluing.OlsonHarris.Plan.CornerCase.CSign.Height
import SkewGluing.OlsonHarris.Plan.CornerCase.FWindows

/-!
# The last rows of a corner composite

Formalizes `shields-2026-skew-gluing.tex`, «Diagonal geometry» (`lem:gluing-local` (3),
`eq:gluing-mixed-profile`) as used in thesis Lemma 5.5.11 (`OlsonHarris2024HopfApplications`).

For a legal mark `ω` of case (c) with phases `s`, `t`, a connected outer `D` of span `r` and
`F = D ∘_ω E`, the last rows `h_n` of the diagonals of `F` on two diagonals `i q + a` and
`(i + m) q + a` of the same residue `a ∈ [t, s - 1]` differ by `-m p + S_i - S_{i+m}`
(`corner_hi_diff`), where `p = v₁` is the row displacement, and `S_i = profS D (μ + i)` is the
quantity `h_{i-1} - ℓ_i + 1` of the outer (`S = 1` at the ends).  It follows from the mixed profile
of the rotated case-(d) composite, `F = (D* ∘_{ω*} E*)*`, whose last rows are `J p + h_a`
and whose heights on the residues `t* ≤ a < s*` are `Ω_a + S_J - 1`.

Sorry-free.
-/

namespace SkewGluing

namespace Plan

namespace Corner

namespace CSign

open MarkedInner

variable {ω : MarkedInner} {D : Diagram}

theorem profS_rotate {D : Diagram} (hD : D.Nonempty) (X : ℤ) :
    profS (SkewGluing.rotate D) X = profS D (1 - X) := by
  have e1 : diagLo (SkewGluing.rotate D) X = - diagHi D (-X) := by
    have := diagLo_rotate (D := D) (-X)
    rwa [neg_neg] at this
  have e2 : diagHi (SkewGluing.rotate D) (X - 1) = - diagLo D (-(X - 1)) := diagHi_rotate (X - 1)
  have e3 : -(X - 1) = 1 - X := by ring
  have e4 : 1 - X - 1 = -X := by ring
  unfold profS
  rw [minContent_rotate hD, maxContent_rotate hD, e1, e2, e3, e4]
  split_ifs <;> omega

theorem diagHi_compose_c (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D) (hc : ω.case = .c)
    (i a : ℤ) :
    diagHi (ω.compose D) (minContent (ω.compose D) + (i * ω.period + a)) =
      - diagLo (ω.rotate.compose (SkewGluing.rotate D))
        (minContent ω.rotate.E + ((1 - minContent D - i) * ω.period + (ω.widthZ - 1 - a))) := by
  rw [h.minContent_compose' hD, compose_rotate_c hc hD.2.1, diagHi_rotate, h.minContent_rotate]
  congr 2
  ring

/-- **The last rows of a corner composite on one residue.**  See the module docstring. -/
theorem corner_hi_diff (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D) (hc : ω.case = .c)
    {s t : ℤ} (hph : ω.IsPhases s t) {i a : ℤ} (m : ℕ) (hta : t ≤ a) (has : a ≤ s - 1)
    (hi0 : 0 ≤ i) (him : i + m ≤ (span D : ℤ)) :
    diagHi (ω.compose D) (minContent (ω.compose D) + (i * ω.period + a)) -
        diagHi (ω.compose D) (minContent (ω.compose D) + ((i + m) * ω.period + a)) =
      -(m : ℤ) * ω.rowShift + profS D (minContent D + i) - profS D (minContent D + (i + m)) := by
  have hcd := rotate_case_d hc
  have hph' := h.isPhases_rotate hph
  have hlt' := h.rotate.phases_lt (Or.inr hcd) hph'
  have hDr := isConnectedSkew_rotate hD
  have hne : D.Nonempty := hD.2.1
  have hq := h.width_lt_period
  have hw := h.width_pos
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph
  have hsp := span_eq_of_isConnectedSkew hD
  have hminr := SkewGluing.minContent_rotate hne
  have hmaxr := SkewGluing.maxContent_rotate hne
  rw [diagHi_compose_c h hD hc, diagHi_compose_c h hD hc]
  have hmp := fun (J : ℤ) (hv : ValidClass (minContent (SkewGluing.rotate D))
      (maxContent (SkewGluing.rotate D)) ω.rotate.widthZ J (ω.widthZ - 1 - a)) =>
    h.rotate.mixed_profile hDr hcd hph' hlt' (J := J) (a := ω.widthZ - 1 - a)
      (by omega) (by change _ < ω.period; omega) hv
  have hw' : ω.rotate.widthZ = ω.widthZ := widthZ_rotate ω
  have v1 : ValidClass (minContent (SkewGluing.rotate D)) (maxContent (SkewGluing.rotate D))
      ω.rotate.widthZ (1 - minContent D - i) (ω.widthZ - 1 - a) := by
    unfold ValidClass; rw [hminr, hmaxr, hw']; omega
  have v2 : ValidClass (minContent (SkewGluing.rotate D)) (maxContent (SkewGluing.rotate D))
      ω.rotate.widthZ (1 - minContent D - (i + m)) (ω.widthZ - 1 - a) := by
    unfold ValidClass; rw [hminr, hmaxr, hw']; omega
  obtain ⟨hhi1, -, -, hreg1, -⟩ := hmp _ v1
  obtain ⟨hhi2, -, -, hreg2, -⟩ := hmp _ v2
  have r1 := hreg1 (by omega) (by omega)
  have r2 := hreg2 (by omega) (by omega)
  have p1 : profS (SkewGluing.rotate D) (1 - minContent D - i) = profS D (minContent D + i) := by
    rw [profS_rotate hne]; congr 1; ring
  have p2 : profS (SkewGluing.rotate D) (1 - minContent D - (i + m)) =
      profS D (minContent D + (i + m)) := by
    rw [profS_rotate hne]; congr 1; ring
  rw [p1] at r1
  rw [p2] at r2
  unfold height at r1 r2
  have hr : ω.rotate.rowShift = ω.rowShift := rfl
  rw [hr] at hhi1 hhi2
  change _ = _ + (1 - minContent D - i) * ω.rowShift at hhi1
  change _ = _ + (1 - minContent D - (i + m)) * ω.rowShift at hhi2
  simp only [period_rotate] at r1 r2 hhi1 hhi2
  nlinarith

end CSign

end Corner

end Plan

end SkewGluing
