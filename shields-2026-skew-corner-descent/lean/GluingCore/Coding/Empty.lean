-- TODO-COPIED from skew-factor-gluing/lean/SkewGluing/Coding/Empty.lean
import GluingCore.Coding.Caps

/-!
# The empty mark: boundary words of a composite

Formalizes `shields-2026-skew-factor-gluing.tex`, «Diagonal geometry» (`lem:gluing-coding`, the
width-zero statement: "both boundaries have the sole possible exceptional residue zero in the
horizontal convention", and "empty composition repeats the inner words away from its joining
steps, which read the two outer bits").

For the empty mark `W₋ = ∅`, `v = v_H`, the composite `D ∘_ω E` has `N = r q`, its words repeat the
words of `E` in every block, and the bits at the joining steps `jq` are the bits `A^D_j`, `B^D_j` of
the outer.

Sorry-free.
-/

namespace GluingCore

namespace MarkedInner

variable {ω : MarkedInner} {D : Diagram}

theorem IsLegalEmpty.span_compose_eq (h : ω.IsLegalEmpty) (hD : IsConnectedSkew D) :
    (span (ω.compose D) : ℤ) = (maxContent D - minContent D + 1) * ω.period := by
  have := span_compose hD h.1
  have hw := h.width_zero
  unfold widthZ at hw
  rw [span_eq_of_isConnectedSkew hD] at this
  omega

theorem IsLegalEmpty.minContent_compose' (h : ω.IsLegalEmpty) (hD : IsConnectedSkew D) :
    minContent (ω.compose D) = minContent ω.E + minContent D * ω.period :=
  h.1.minContent_compose hD

/-- **`lem:gluing-coding`, width zero.**  For the empty mark both boundary words of the composite
have period `q` except at the residue zero. -/
theorem IsLegalEmpty.periodExcept (h : ω.IsLegalEmpty) (hD : IsConnectedSkew D) :
    PeriodWords.PeriodExcept (span (ω.compose D) - 1) ω.period.toNat {0}
      (wordA (ω.compose D)) ∧
    PeriodWords.PeriodExcept (span (ω.compose D) - 1) ω.period.toNat {0}
      (wordB (ω.compose D)) := by
  have hq := h.period_pos
  have hw := h.width_zero
  have hmM : minContent D ≤ maxContent D := minContent_le (maxContent_mem hD.2.1)
  have hc := h.classRows hD
  have hmin := h.minContent_compose' hD
  have hN : (span (ω.compose D) : ℤ) = (maxContent D - minContent D + 1) * ω.period + ω.widthZ := by
    rw [h.span_compose_eq hD, hw]; ring
  refine ⟨periodExcept_of_classBit hc hN (fun J a h0 h1 hv hJ => hc.wordA_class hmin h0 h1 hv hJ)
    ?_, periodExcept_of_classBit hc hN
      (fun J a h0 h1 hv hJ => hc.wordB_class hmin h0 h1 hv hJ) ?_⟩
  · intro J a h0 h1 hS hv hv' hJ
    have ha : a ≠ 0 := by simpa using hS
    unfold classBitLo
    simp only [ha, ite_false]
    omega
  · intro J a h0 h1 hS hv hv' hJ
    have ha : a ≠ 0 := by simpa using hS
    unfold classBitHi
    simp only [ha, ite_false]
    omega

/-- **`lem:gluing-coding`, width zero, the joining steps.**  For the empty mark the bits of the
composite at the joining step `jq` are the bits of the outer: `A_{jq} = A^D_j`, `B_{jq} = B^D_j`
for `1 ≤ j < N_D`. -/
theorem IsLegalEmpty.joining (h : ω.IsLegalEmpty) (hD : IsConnectedSkew D) {j : ℤ}
    (hj1 : 1 ≤ j) (hj2 : j < (span D : ℤ)) :
    wordA (ω.compose D) (j * ω.period) = wordA D j ∧
    wordB (ω.compose D) (j * ω.period) = wordB D j := by
  have hq := h.period_pos
  have hw := h.width_zero
  have hc := h.classRows hD
  have hmin := h.minContent_compose' hD
  have hsp := span_eq_of_isConnectedSkew hD
  have hp := h.rowShift_eq
  have hcase := h.case_a
  have hv : ValidClass (minContent D) (maxContent D) ω.widthZ (minContent D + j) 0 :=
    Or.inl ⟨by omega, by omega⟩
  have hR : ∀ J, ω.oRowLo D J = J * ω.rowShift + diagLo D J ∧
      ω.oRowHi D J = J * ω.rowShift + diagHi D J := by
    intro J; simp [oRowLo, oRowHi, hcase]
  have hv1 : ValidClass (minContent D) (maxContent D) ω.widthZ (minContent D + j - 1)
      (ω.period - 1) :=
    Or.inl ⟨by omega, by omega⟩
  have hpp : (minContent D + j - 1) * ω.rowShift =
      (minContent D + j) * ω.rowShift - ω.rowShift := by
    ring
  have hE := h.ends
  have hmj : minContent D + j - 1 + 1 = minContent D + j := by ring
  have hRj := hR (minContent D + j)
  have hRj1 := hR (minContent D + j - 1)
  constructor
  · rw [hc.wordA_class' hmin (J := minContent D + j) (a := 0) (by ring) (le_refl _) hq hv
      (fun _ => by omega)]
    unfold classBitLo wordA bitA
    simp only [ite_true]
    omega
  · rw [hc.wordB_class' hmin (J := minContent D + j) (a := 0) (by ring) (le_refl _) hq hv
      (fun _ => by omega)]
    unfold classBitHi wordB bitB
    simp only [ite_true]
    omega

end MarkedInner

end GluingCore
