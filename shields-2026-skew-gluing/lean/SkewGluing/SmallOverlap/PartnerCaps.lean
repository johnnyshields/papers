import SkewGluing.SmallOverlap.SmallArith

/-!
# The caps of a mixed root, read on the diagram

Formalizes `shields-2026-skew-gluing.tex`, «Diagonal geometry» (`lem:gluing-coding`,
`eq:gluing-caps`), in the form used for the partner of a width-one root: the bits of the boundary
words of the diagram `F` itself at the positions fixed by a mixed root.

Sorry-free.
-/

namespace SkewGluing

open MarkedInner

namespace SmallOverlap

theorem _root_.SkewGluing.Chart.IsProperRoot.caps_d_F {χ : Chart} {F : Diagram} {Q : ℕ}
    (h : χ.IsProperRoot F Q) (hW : χ.ω.W.Nonempty) (hcd : χ.ω.case = .d) {s t : ℤ}
    (hph : χ.ω.IsPhases s t) :
    wordB F (χ.ω.width : ℤ) = 1 ∧ wordB F (Q : ℤ) = 0 := by
  have hlegal : χ.ω.IsLegalNonempty := ⟨h.1.2.2.2, hW⟩
  obtain ⟨-, -, -, -, c5, c6⟩ := hlegal.caps_d h.1.1 hcd hph
  obtain ⟨hr, hN, hwq, hp2⟩ := h.arith
  have hw1 := hlegal.width_pos
  have hs : span χ.parent = span F := h.span_eq.symm
  have hQ : χ.ω.period = (Q : ℤ) := h.2.2
  have hwZ : χ.ω.widthZ = (χ.ω.width : ℤ) := rfl
  have hsd : (2 : ℤ) ≤ span χ.D := by exact_mod_cast hr
  have hQ2 : (2 : ℤ) ≤ Q := by exact_mod_cast hp2
  have hw0 : (0 : ℤ) ≤ χ.ω.width := by positivity
  have hQF : (Q : ℤ) < span F := by nlinarith
  rw [hwZ] at c5
  rw [hQ] at c6
  refine ⟨?_, ?_⟩
  · rw [h.wordB_eq (by omega) (by omega)]; exact c5
  · rw [h.wordB_eq (by omega) hQF]; exact c6

theorem _root_.SkewGluing.Chart.IsProperRoot.caps_c_F {χ : Chart} {F : Diagram} {Q : ℕ}
    (h : χ.IsProperRoot F Q) (hW : χ.ω.W.Nonempty) (hcc : χ.ω.case = .c) {s t : ℤ}
    (hph : χ.ω.IsPhases s t) :
    wordA F ((span F : ℤ) - χ.ω.width) = 1 ∧ wordA F ((span F : ℤ) - Q) = 0 ∧
    (1 ≤ t → wordB F t = 0) ∧ wordB F s = 0 ∧
    wordB F ((span F : ℤ) - χ.ω.width + t) = 1 ∧
    (s < χ.ω.width → wordB F ((span F : ℤ) - χ.ω.width + s) = 1) := by
  have hlegal : χ.ω.IsLegalNonempty := ⟨h.1.2.2.2, hW⟩
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hlegal.caps_c h.1.1 hcc hph
  obtain ⟨hr, hN, hwq, hp2⟩ := h.arith
  have hw1 := hlegal.width_pos
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph
  have hs : span χ.parent = span F := h.span_eq.symm
  have hQ : χ.ω.period = (Q : ℤ) := h.2.2
  have hwZ : χ.ω.widthZ = (χ.ω.width : ℤ) := rfl
  have hsd : (2 : ℤ) ≤ span χ.D := by exact_mod_cast hr
  have hQ2 : (2 : ℤ) ≤ Q := by exact_mod_cast hp2
  have hw0 : (0 : ℤ) ≤ χ.ω.width := by positivity
  have hQF : (Q : ℤ) < span F := by nlinarith
  have hspc : ((span (χ.ω.compose χ.D) : ℕ) : ℤ) = span F := by
    have : span (χ.ω.compose χ.D) = span F := h.span_eq.symm
    rw [this]
  rw [hwZ] at c3 c4 c5
  rw [hQ] at c6
  simp only [Chart.parent] at hs
  rw [hspc] at c3 c4 c5 c6
  refine ⟨?_, ?_, fun h1 => ?_, ?_, ?_, fun h1 => ?_⟩
  · rw [h.wordA_eq (by omega) (by omega)]; exact c5
  · rw [h.wordA_eq (by omega) (by omega)]; exact c6
  · rw [h.wordB_eq (by omega) (by omega)]; exact c1 h1
  · rw [h.wordB_eq (by omega) (by omega)]; exact c2
  · rw [h.wordB_eq (by omega) (by omega)]; exact c3
  · rw [h.wordB_eq (by omega) (by omega)]; exact c4 h1

end SmallOverlap
end SkewGluing
