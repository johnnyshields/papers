import SkewGluing.OlsonHarris.Plan.EdgeCase.TFun
import SkewGluing.OlsonHarris.Plan.EdgeCase.HatShapes
import SkewGluing.OlsonHarris.Plan.MarkFacts.HatMark
import SkewGluing.OlsonHarris.Plan.MurnaghanNakayama
import SkewGluing.Local.Final
import SkewGluing.Local.Statements

/-!
# `p_{mq}^⊥` kills the hat factors

Formalizes `shields-2026-skew-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `eq:gluing-offsets`, `def:gluing-graph`): thesis Lemma 5.4.4
(`OlsonHarris2024HopfApplications`): `W`, `\overline W` and `\overline O` have no removable
ribbon of size divisible by `q`.

**Differs from the paper's route.**  A ribbon of size `n` occupies `n` diagonals, so no ribbon
fits in a diagram with fewer than `n` diagonals; `W` and `\overline W` lie on the `w < q`
diagonals of `W₋`, and `\overline O` on the private diagonals `[w + 1, q - 1]`, because the
middle has one cell on each marked diagonal and on the diagonal `w`.  The thesis argues through
loose end ribbons.

Uses `pDeriv_cellSchur_left`.

Sorry-free.
-/

set_option linter.style.openClassical false

namespace SkewGluing

namespace Plan

open scoped Classical

theorem content_mem_hatMiddleFin {ω : MarkedInner} (hω : ω.IsLegal) {x : ℤ × ℤ}
    (hx : x ∈ hatMiddleFin ω) :
    minContent ω.E + ω.width + 1 ≤ content x ∧ content x ≤ minContent ω.E + ω.period - 1 := by
  rw [MarkedInner.mem_hatMiddleFin] at hx
  obtain ⟨hx1, hx2⟩ := hx
  have hxE : x ∈ ω.E := (Finset.mem_sdiff.mp hx1).1
  have hxE' : x + eCell ∈ ω.E := (Finset.mem_sdiff.mp hx2).1
  have hcE := hω.copy_content hxE
  have hce : content (x + eCell) = content x := MarkedInner.content_eCell_add x
  have hne : x ≠ x + eCell := by
    intro h
    have := congrArg Prod.fst h
    simp [eCell] at this
  by_cases hW : ω.W = ∅
  · have hw : ω.width = 0 := by simp [MarkedInner.width, hW, span, contents]
    have hE := hω.1.1
    constructor
    · by_contra hlt
      have hc : content x = minContent ω.E := by omega
      exact hne ((MarkedInner.eq_sw_of_content hE hxE hc).trans
        (MarkedInner.eq_sw_of_content hE hxE' (by rw [hce]; exact hc)).symm)
    · omega
  · have hWn : ω.W.Nonempty := Finset.nonempty_iff_ne_empty.mpr hW
    obtain ⟨-, hthin, hsing, -⟩ := hω.gluing_local_one hWn
    have hwz : ω.widthZ = (ω.width : ℤ) := rfl
    constructor
    · by_contra hlt
      by_cases hc1 : content x ≤ minContent ω.E + ω.widthZ - 1
      · exact hne (hthin x hx1 (x + eCell) hx2 hce.symm (Or.inl hc1))
      · have hc : content x = minContent ω.E + ω.widthZ := by omega
        have h1 := diagLo_le (D := ω.E) (i := x.1) (j := x.2) (k := minContent ω.E + ω.widthZ)
          hxE (by simp only [content] at hc; omega)
        have h2 := le_diagHi (D := ω.E) (i := x.1) (j := x.2) (k := minContent ω.E + ω.widthZ)
          hxE (by simp only [content] at hc; omega)
        have h3 := diagLo_le (D := ω.E) (i := (x + eCell).1) (j := (x + eCell).2)
          (k := minContent ω.E + ω.widthZ) hxE' (by simp only [content, eCell] at hc ⊢; simp; omega)
        have h4 := le_diagHi (D := ω.E) (i := (x + eCell).1) (j := (x + eCell).2)
          (k := minContent ω.E + ω.widthZ) hxE' (by simp only [content, eCell] at hc ⊢; simp; omega)
        simp only [Prod.fst_add, eCell] at h3 h4
        omega
    · by_contra hgt
      exact hne (hthin x hx1 (x + eCell) hx2 hce.symm (Or.inr (by omega)))

theorem pDeriv_cellSchur_hat_aux {ω : MarkedInner} (hω : ω.IsLegal) {m : ℕ} (hm : 0 < m) :
    pDeriv (m * ω.period.toNat) (cellSchur ω.W) = 0 ∧
      pDeriv (m * ω.period.toNat) (cellSchur (hatMarkFin ω)) = 0 ∧
      pDeriv (m * ω.period.toNat) (cellSchur (hatMiddleFin ω)) = 0 := by
  have hq := hω.period_pos
  have hwq : (ω.width : ℤ) < ω.period := hω.2.2.1.2
  have hn : 0 < m * ω.period.toNat := Nat.mul_pos hm (by omega)
  have hqn : ω.period.toNat ≤ m * ω.period.toNat := Nat.le_mul_of_pos_left _ hm
  refine ⟨?_, ?_, ?_⟩
  · apply pDeriv_cellSchur_eq_zero_of_span_lt
    change ω.width < _
    omega
  · apply pDeriv_cellSchur_eq_zero_of_span_lt
    have := SkewGluing.MarkedInner.span_hatMarkFin_le ω
    omega
  · apply pDeriv_cellSchur_eq_zero_of_span_lt
    have := hω.span_hatMiddleFin_lt
    omega

end Plan

end SkewGluing
