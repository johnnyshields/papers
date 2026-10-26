/- TODO-COPIED: adapted from
`skew-factor-gluing/lean/SkewGluing/Aligned/CaseD/Rows.lean`. -/
import GluingCore.Aligned.CaseD.Walk

/-!
# Aligned marks, case (d): diagrams given by their diagonal rows

Formalizes `shields-2026-skew-factor-gluing.tex`, «Equal and divisible periods»
(`lem:gluing-aligned`).

`alD_connected_of_rows` is the diagonal criterion in the form used for the lower mark `μ`
of `lem:gluing-aligned`: a diagram whose diagonal `j` consists of the rows `[fLo j, fHi j]`
(`0 ≤ j < n`), with the stepping and end conditions of the criterion, is a connected skew
diagram.  `alD_L`, `alD_H` are the first and last rows of the diagonals of a connected skew
diagram `V`, indexed from its least content.

Sorry-free.
-/

namespace GluingCore

theorem alD_connected_of_rows (F : Diagram) (c₀ n : ℤ) (fLo fHi : ℤ → ℤ) (hn : 1 ≤ n)
    (hmem : ∀ j r, (r, r + (c₀ + j)) ∈ F ↔ 0 ≤ j ∧ j < n ∧ fLo j ≤ r ∧ r ≤ fHi j)
    (hne : ∀ j, 0 ≤ j → j < n → fLo j ≤ fHi j)
    (hstL : ∀ j, 1 ≤ j → j < n → fLo (j - 1) - fLo j = 0 ∨ fLo (j - 1) - fLo j = 1)
    (hstH : ∀ j, 1 ≤ j → j < n → fHi (j - 1) - fHi j = 0 ∨ fHi (j - 1) - fHi j = 1)
    (hfirst : fLo 0 = fHi 0) (hlast : fLo (n - 1) = fHi (n - 1)) : IsConnectedSkew F := by
  have hc : ClassRows F c₀ 1 0 0 (n - 1) (fun j _ => fLo j) (fun j _ => fHi j) := by
    refine ⟨by norm_num, le_refl _, by norm_num, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro j a r h0 h1
      have ha : a = 0 := by omega
      subst ha
      have e : j * 1 + 0 = j := by ring
      rw [e, hmem]
      unfold ValidClass
      constructor
      · rintro ⟨x1, x2, x3, x4⟩; exact ⟨Or.inl ⟨x1, by omega⟩, x3, x4⟩
      · rintro ⟨x1 | x1, x3, x4⟩
        · exact ⟨x1.1, by omega, x3, x4⟩
        · omega
    · intro j a h0 h1 hv
      unfold ValidClass at hv
      rcases hv with hv | hv
      · exact hne j hv.1 (by omega)
      · omega
    · intro j a h1 h2; omega
    · intro j hv1 hv2
      unfold ValidClass at hv1 hv2
      have h1 : 0 ≤ j ∧ j ≤ n - 1 := by omega
      have h2 : 0 ≤ j + 1 ∧ j + 1 ≤ n - 1 := by omega
      have := hstL (j + 1) (by omega) (by omega)
      have := hstH (j + 1) (by omega) (by omega)
      simp only [add_sub_cancel_right] at *
      simp only [sub_self] at *
      refine ⟨?_, ?_⟩ <;> assumption
    · exact hfirst
    · intro h; omega
    · intro _; exact hlast
  exact hc.isConnectedSkew

/-- The first row of the diagonal of relative content `j` of a diagram `V`. -/
def alD_L (V : Diagram) (j : ℤ) : ℤ := diagLo V (minContent V + j)

/-- The last row of the diagonal of relative content `j` of a diagram `V`. -/
def alD_H (V : Diagram) (j : ℤ) : ℤ := diagHi V (minContent V + j)

section Basic

variable {V : Diagram}

theorem alD_mem_V (hV : IsConnectedSkew V) (r j : ℤ) :
    (r, r + (minContent V + j)) ∈ V ↔
      0 ≤ j ∧ j < (span V : ℤ) ∧ alD_L V j ≤ r ∧ r ≤ alD_H V j := by
  have hs := isConnectedSkew_iff_diagonal.mp hV
  have hsp := span_eq_of_isConnectedSkew hV
  rw [hs.mem_iff, hs.mem_contents_iff]
  unfold alD_L alD_H
  omega

theorem alD_L_le_H (hV : IsConnectedSkew V) {j : ℤ} (h0 : 0 ≤ j) (h1 : j < (span V : ℤ)) :
    alD_L V j ≤ alD_H V j := by
  have hs := isConnectedSkew_iff_diagonal.mp hV
  have hsp := span_eq_of_isConnectedSkew hV
  have := diagLo_le_diagHi (D := V) (k := minContent V + j)
    (hs.mem_contents_iff.mpr ⟨by omega, by omega⟩)
  exact this

theorem alD_step (hV : IsConnectedSkew V) {j : ℤ} (h0 : 1 ≤ j) (h1 : j < (span V : ℤ)) :
    (alD_L V (j - 1) - alD_L V j = 0 ∨ alD_L V (j - 1) - alD_L V j = 1) ∧
    (alD_H V (j - 1) - alD_H V j = 0 ∨ alD_H V (j - 1) - alD_H V j = 1) := by
  have hs := isConnectedSkew_iff_diagonal.mp hV
  have hsp := span_eq_of_isConnectedSkew hV
  have m1 : minContent V + j ∈ contents V := hs.mem_contents_iff.mpr ⟨by omega, by omega⟩
  have m2 : minContent V + j - 1 ∈ contents V :=
    hs.mem_contents_iff.mpr ⟨by omega, by omega⟩
  have := hs.2.2.2.1 _ m1 m2
  simp only [bitA, bitB, Finset.mem_insert, Finset.mem_singleton] at this
  have e : minContent V + (j - 1) = minContent V + j - 1 := by ring
  unfold alD_L alD_H
  rw [e]
  exact this

theorem alD_end0 (hV : IsConnectedSkew V) : alD_L V 0 = alD_H V 0 := by
  have hs := isConnectedSkew_iff_diagonal.mp hV
  have hne := hV.2.1
  have := hs.2.2.2.2 _ (minContent_mem hne) (Or.inl (fun hm => by
    have := minContent_le hm; omega))
  simpa [alD_L, alD_H] using this

theorem alD_endN (hV : IsConnectedSkew V) :
    alD_L V ((span V : ℤ) - 1) = alD_H V ((span V : ℤ) - 1) := by
  have hs := isConnectedSkew_iff_diagonal.mp hV
  have hne := hV.2.1
  have hsp := span_eq_of_isConnectedSkew hV
  have := hs.2.2.2.2 _ (maxContent_mem hne) (Or.inr (fun hm => by
    have := le_maxContent hm; omega))
  have e : minContent V + ((span V : ℤ) - 1) = maxContent V := by omega
  unfold alD_L alD_H
  rw [e]
  exact this

end Basic

end GluingCore
