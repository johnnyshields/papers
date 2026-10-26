/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
-- TODO-COPIED: skew-gluing/lean/SkewGluing/Coding.lean
import SkewMarkedFactor.Gluing.Coding.CaseC

/-!
# The coding of a composite's boundary words

Formalizes `shields-2026-skew-gluing.tex`, «Diagonal geometry» (`lem:gluing-coding`,
`eq:gluing-holes`, `eq:gluing-caps`, `eq:gluing-interface`, `eq:gluing-ordinary-endpoints`).

The parent boundary words are `wordA F k = ℓ_{k-1} - ℓ_k` and `wordB F k = h_{k-1} - h_k` on the
southwest-normalized positions `1, …, N - 1` (`SkewMarkedFactor.Gluing.Coding.Words`).  For a legal mark with a
nonempty copy, middle phases `s, t` (`MarkedInner.IsPhases`), and a connected outer `D`:

* `MarkedInner.IsLegalNonempty.gluing_coding_periodic` (`eq:gluing-holes`): both words of
  `F = D ∘_ω E` have `PeriodWords.PeriodExcept` period `q` except at the residues `holesA`, `holesB`
  of the table; the cases are `periodExcept_ordinary` (a), (b), `periodExcept_d`, `periodExcept_c`;
* `MarkedInner.IsLegalNonempty.caps_a`, `caps_b`, `caps_c`, `caps_d` (`eq:gluing-caps`, and
  `B_w = 1`, `B_q = 0` of case (d));
* `MarkedInner.IsLegalNonempty.interface_d`, `interface_c` (`eq:gluing-interface`);
* `MarkedInner.IsLegalNonempty.ordinary_endpoints_a` (`eq:gluing-ordinary-endpoints`);
* `MarkedInner.IsLegalEmpty.periodExcept`, `MarkedInner.IsLegalEmpty.joining` (width zero);
* `MarkedInner.IsLegalNonempty.wordB_gcd_mixed_ordinary`: the periodicity in the form consumed by
  `PeriodWords.periodExcept_gcd_one_hole`.

Sorry-free.
-/

namespace SkewMarkedFactor.Gluing

namespace MarkedInner

variable {ω : MarkedInner} {D : Diagram}

/-- **`lem:gluing-coding`, `eq:gluing-holes`.**  For a legal mark with a nonempty copy and a
connected outer `D`, the parent boundary words `A` and `B` of `F = D ∘_ω E` on the positions
`1, …, N - 1` have period `q` except at the residues of the table `eq:gluing-holes`, for the middle
phases `s, t`. -/
theorem IsLegalNonempty.gluing_coding_periodic (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D)
    {s t : ℤ} (hph : ω.IsPhases s t) :
    PeriodWords.PeriodExcept (span (ω.compose D) - 1) ω.period.toNat
      (holesA ω.case s t) (wordA (ω.compose D)) ∧
    PeriodWords.PeriodExcept (span (ω.compose D) - 1) ω.period.toNat
      (holesB ω.case s t) (wordB (ω.compose D)) := by
  cases hc : ω.case
  · have e := h.periodExcept_ordinary hD (by simp [AttachCase.IsMixed, hc]) hph
    rwa [hc] at e
  · have e := h.periodExcept_ordinary hD (by simp [AttachCase.IsMixed, hc]) hph
    rwa [hc] at e
  · have e := h.periodExcept_c hD hc hph
    rwa [hc] at e
  · have e := h.periodExcept_d hD hc hph
    rwa [hc] at e

/-- The periodicity of `eq:gluing-holes`, in the form consumed by `lem:gluing-periods`.  A parent
with a chart of mixed case (d), period `a`, and an ordinary chart, period `b`, in the same parent
has, when neither period divides the other and the word is long enough, the period `gcd a b` on the
word `B`: the word `B` of the mixed chart has the full period `a`, and that of the ordinary chart
has period `b` except at one residue. -/
theorem IsLegalNonempty.wordB_gcd_mixed_ordinary {ω' : MarkedInner} {D' : Diagram}
    (h : ω.IsLegalNonempty) (h' : ω'.IsLegalNonempty) (hD : IsConnectedSkew D)
    (hD' : IsConnectedSkew D') (hF : ω.compose D = ω'.compose D') (hcd : ω.case = .d)
    (hmix' : ¬ ω'.case.IsMixed) {s t s' t' : ℤ} (hph : ω.IsPhases s t) (hph' : ω'.IsPhases s' t')
    (hab : ¬ ω.period.toNat ∣ ω'.period.toNat) (hba : ¬ ω'.period.toNat ∣ ω.period.toNat)
    (hL : 2 * max ω.period.toNat ω'.period.toNat ≤ span (ω.compose D) - 1) :
    PeriodWords.PeriodExcept (span (ω.compose D) - 1)
      (Nat.gcd ω.period.toNat ω'.period.toNat) ∅ (wordB (ω.compose D)) := by
  have hq := h.1.period_pos
  have hq' := h'.1.period_pos
  have ha : 0 < ω.period.toNat := by omega
  have hb : 0 < ω'.period.toNat := by omega
  have e1 := (h.periodExcept_d hD hcd hph).2
  have e2 := (h'.periodExcept_ordinary hD' hmix' hph').2
  simp only [holesB, hcd] at e1
  rw [← hF] at e2
  have hres : ∃ r : ℤ, holesB ω'.case s' t' = {r} := by
    cases hc : ω'.case
    · exact ⟨s', by simp [holesB]⟩
    · exact ⟨t', by simp [holesB]⟩
    · exact absurd (Or.inl hc) hmix'
    · exact absurd (Or.inr hc) hmix'
  obtain ⟨r, hr⟩ := hres
  rw [hr] at e2
  exact PeriodWords.periodExcept_gcd_one_hole ha hb hab hba r hL e1 e2

end MarkedInner

/-! ### Checked examples

The outer `(4, 3, 3) / (2, 1)` has span `6`.  Its composites with the paper's marked inners show the
holes of `eq:gluing-holes` and the exceptional bits of `eq:gluing-caps` and
`eq:gluing-interface`. -/

section Examples

open MarkedInner

/-- The outer diagram `(4, 3, 3) / (2, 1)`, connected skew of span six. -/
def codingOuter : Diagram := skewOf [4, 3, 3] [2, 1]

example : IsConnectedSkew codingOuter ∧ span codingOuter = 6 := by decide +kernel

/-- Case (a), the chart figure's mark (`q = 3`, `w = 2`, phases `t = 1`, `s = 2`): `A` has period
three except at the residue one, `B` except at the residue two. -/
example : PeriodWords.PeriodExcept 19 3 {1} (wordA (compose codingOuter chartFigureInner)) ∧
    PeriodWords.PeriodExcept 19 3 {2} (wordB (compose codingOuter chartFigureInner)) := by
  decide +kernel

/-- The caps of case (a) for the chart figure's mark: `A_t = 1`, `B_s = 0`, `A_{N-w+t} = 0`. -/
example : wordA (compose codingOuter chartFigureInner) 1 = 1 ∧
    wordB (compose codingOuter chartFigureInner) 2 = 0 ∧
    wordA (compose codingOuter chartFigureInner) 19 = 0 := by decide +kernel

/-- Case (d), the singleton hook mark (`q = 2`, `w = 1`, `t = 0`, `s = 1`): `B` has the full period
two, `A` has period two except at the residues `0` and `1`, and `B_w = 1`, `B_q = 0`. -/
example : PeriodWords.PeriodExcept 12 2 {0, 1} (wordA (compose codingOuter hookInner)) ∧
    PeriodWords.PeriodExcept 12 2 ∅ (wordB (compose codingOuter hookInner)) ∧
    wordB (compose codingOuter hookInner) 1 = 1 ∧
    wordB (compose codingOuter hookInner) 2 = 0 := by decide +kernel

/-- The interface of case (d): `A_{jq+t} = A^D_j` and `A_{jq+s} = 1 - B^D_j`. -/
example : ∀ j ∈ Finset.Icc (1 : ℤ) 5,
    wordA (compose codingOuter hookInner) (2 * j + 0) = wordA codingOuter j ∧
    wordA (compose codingOuter hookInner) (2 * j + 1) = 1 - wordB codingOuter j := by
  decide +kernel

/-- Case (c), the rotated hook mark: `B` has period two except at residues `0`, `1`, `A` has the
full period, and the interface reads `B_{jq+t} = 1 - A^D_j`, `B_{jq+s} = B^D_j`. -/
example : PeriodWords.PeriodExcept 12 2 ∅ (wordA (compose codingOuter hookInner.rotate)) ∧
    PeriodWords.PeriodExcept 12 2 {0, 1} (wordB (compose codingOuter hookInner.rotate)) := by
  decide +kernel

example : ∀ j ∈ Finset.Icc (1 : ℤ) 5,
    wordB (compose codingOuter hookInner.rotate) (2 * j + 0) = 1 - wordA codingOuter j ∧
    wordB (compose codingOuter hookInner.rotate) (2 * j + 1) = wordB codingOuter j := by
  decide +kernel

/-- Width zero: the empty mark on the row `(3)` gives period three except at the residue zero, and
the bits at the joining steps are the bits of the outer. -/
example : PeriodWords.PeriodExcept 17 3 {0} (wordA (compose codingOuter rowEmptyInner)) ∧
    PeriodWords.PeriodExcept 17 3 {0} (wordB (compose codingOuter rowEmptyInner)) := by
  decide +kernel

example : ∀ j ∈ Finset.Icc (1 : ℤ) 5,
    wordA (compose codingOuter rowEmptyInner) (3 * j) = wordA codingOuter j ∧
    wordB (compose codingOuter rowEmptyInner) (3 * j) = wordB codingOuter j := by
  decide +kernel

end Examples

end SkewMarkedFactor.Gluing
