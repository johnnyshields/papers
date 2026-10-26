/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.InflateLegalA
import SkewClassInflation.InflateLegalB
import SkewClassInflation.InflateLegalC
import SkewClassInflation.InflateLegalD

/-!
# The inflated mark is legal

Formalizes the positive-width case \(0<w<q-1\) of `lem:inflate-chart` in
`shields-2026-skew-class-inflation.tex`.  A legal mark \(\omega\) with a nonempty copy, of period
\(q\) and width \(w\) with \(w+1<q\), has a legal inflated mark with the same inner-and-mark
inflation \(\mathcal I(E),\mathcal I(W)\), the same displacement and the same attachment case,
provided the two private pinches hold: the diagonal of content \(w+1\) of \(E\) starts in the row
that the diagonal of content \(w\) starts in, and the diagonals of contents \(q-2\) and \(q-1\)
end in the same row.  The pinches are necessary.  Its period is \(q\), its width is \(w+1\), and
its middle phases, with the lower tail on the marked residues \([\sigma,w-1]\) and the upper tail
on \([0,\tau-1]\), are \((\tau,\sigma+1)\), \((\tau+1,\sigma)\), \((\tau+1,\sigma+1)\) and
\((\tau,\sigma)\) in the cases (a), (b), (c), (d).  Sorry-free.
-/

namespace SkewClassInflation

open SkewGluing MarkedInner

/-- The increase of the lower-tail start \(\sigma\) of the middle phases under inflation. -/
def sigmaShift : AttachCase → ℤ
  | .a => 1
  | .b => 0
  | .c => 1
  | .d => 0

/-- The increase of the upper-tail end \(\tau\) of the middle phases under inflation. -/
def tauShift : AttachCase → ℤ
  | .a => 0
  | .b => 1
  | .c => 1
  | .d => 0

/-- **Inflation of a legal mark of positive width below `q - 1`.**  The inflated mark is legal,
has the same period and attachment case, width one larger, and middle phases
\((s+\mathrm{sigmaShift},t+\mathrm{tauShift})\). -/
theorem inflate_mark_isLegal {ω : MarkedInner} (h : ω.IsLegalNonempty) {s t : ℤ}
    (hp : ω.IsPhases s t) (hw1 : ω.widthZ + 1 < ω.period)
    (h1 : ω.lo (ω.widthZ + 1) = ω.lo ω.widthZ)
    (h2 : ω.hi (ω.period - 2) = ω.hi (ω.period - 1)) :
    (inflateMarked ω).IsLegalNonempty ∧
      (inflateMarked ω).IsPhases (s + sigmaShift ω.case) (t + tauShift ω.case) ∧
      (inflateMarked ω).widthZ = ω.widthZ + 1 ∧ (inflateMarked ω).period = ω.period ∧
      (inflateMarked ω).case = ω.case := by
  have key : ∀ {c : AttachCase}, ω.case = c →
      (inflateMarked ω).IsLegal ∧
        (inflateMarked ω).IsPhases (s + sigmaShift c) (t + tauShift c) ∧
        (inflateMarked ω).widthZ = ω.widthZ + 1 := by
    intro c hc
    cases c
    · obtain ⟨a1, a2, a3, -, -⟩ := inflate_isLegal_a h hc hp hw1 h1 h2
      exact ⟨a1, by simpa [sigmaShift, tauShift] using a2, a3⟩
    · obtain ⟨a1, a2, a3, -, -⟩ := inflate_isLegal_b h hc hp hw1 h1 h2
      exact ⟨a1, by simpa [sigmaShift, tauShift] using a2, a3⟩
    · obtain ⟨a1, a2, a3, -, -⟩ := inflate_isLegal_c h hc hp hw1 h1 h2
      exact ⟨a1, by simpa [sigmaShift, tauShift] using a2, a3⟩
    · obtain ⟨a1, a2, a3, -, -⟩ := inflate_isLegal_d h hc hp hw1 h1 h2
      exact ⟨a1, by simpa [sigmaShift, tauShift] using a2, a3⟩
  obtain ⟨k1, k2, k3⟩ := key rfl
  exact ⟨⟨k1, inflateMarked_W_nonempty h.2⟩, k2, k3, rfl, rfl⟩

end SkewClassInflation
