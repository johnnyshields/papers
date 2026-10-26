import SkewGluing.Decoder.Words
import SkewGluing.Coding

/-!
# The compiler table: native positions, ports and phases

Formalizes `shields-2026-skew-gluing.tex`, «Reconstructing a chart from its two words»
(`ge:eq:ports`).

For a legal marked inner `ω` of period `f` and width `a`, and an outer of span `m`, the composite
has span `m f + a`.  A position `k` of its closed words reads, away from the variable slots, the
native word of the inner at the position `natPos f m k`: positions in the first `f` stay, positions
in the last block `(m - 1) f + 1, …` shift down by `(m - 1) f`, and the middle ones reduce to
`1, …, f`.  The variable slots sit at the residues `holesB` (row word `X`) and `holesA` (column
word `Y`) of `SkewGluing.holesB`, `SkewGluing.holesA`; the empty mark is read as case (a) with
phases `(0, 0)`.  `portDecode` inverts the port table: it reads the two outer words `(x_j, y_j)` off
the slots of block `j`.

Sorry-free.
-/

namespace SkewGluing

/-- The position of the inner word that the composite word of span `m f + a` repeats at position
`k`, away from the variable slots. -/
def natPos (f m k : ℤ) : ℤ := if k ≤ 0 then 0 else k - f * min ((k - 1) / f) (m - 1)

/-- The two outer words `(x_j, y_j) = (X_A(j), Y_A(j))` read off the variable slots of block `j`
of a closed pair of words, by the table `ge:eq:ports`. -/
def portDecode (x : AttachCase) (s t f : ℤ) (P : Diagram) (j : ℤ) : ℤ × ℤ :=
  match x with
  | .a => (Xw P (j * f + s), Yw P (j * f + t))
  | .b => (1 - Yw P (j * f + s), 1 - Xw P (j * f + t))
  | .c => (Xw P (j * f + s), 1 - Xw P (j * f + t))
  | .d => (1 - Yw P (j * f + s), Yw P (j * f + t))

namespace MarkedInner

/-- `(s, t)` are the phases of the full marked inner: the middle phases of a nonempty mark, and
`(0, 0)` for the empty mark. -/
def HasPhases (ω : MarkedInner) (s t : ℤ) : Prop :=
  (ω.W = ∅ ∧ s = 0 ∧ t = 0) ∨ (ω.W.Nonempty ∧ ω.IsPhases s t)

end MarkedInner

end SkewGluing
