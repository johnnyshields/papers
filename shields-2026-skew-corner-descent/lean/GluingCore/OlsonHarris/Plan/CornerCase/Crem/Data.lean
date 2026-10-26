-- TODO-COPIED from skew-factor-gluing/lean/SkewGluing/OlsonHarris/Plan/CornerCase/Crem/Data.lean
import GluingCore.Local
import GluingCore.OlsonHarris.Plan.CornerCase.Lift

/-!
# Row intervals of the pieces of a case-(c) mark

Formalizes `shields-2026-skew-factor-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `eq:gluing-offsets`, `def:gluing-graph`): the shapes `W`, `\overline W`,
`\overline O` of thesis §5.3.1 and §5.5 (`OlsonHarris2024HopfApplications`) for a legal mark of
case (c), read on the diagonals of `E`.

On a marked diagonal `a < w` both copies are northwest-justified (`lem:gluing-local` (2)), so
`ℓ_{a+q} = ℓ_a + p` and `h_{a+q} - p - h_a` is `1`, `0`, `-1` for `a < t`, `t ≤ a < s`, `s ≤ a`.
Hence `W` has the rows `[ℓ_a, h_a - [s ≤ a]]`, `\overline W` the rows `[ℓ_a, h_a - [t ≤ a]]`,
and `\overline O` the rows `[ℓ_a, h_a - 1]` on the private diagonals `w ≤ a < q`.

Sorry-free.
-/

namespace GluingCore

namespace Plan

namespace Corner

namespace Rem

open MarkedInner

variable {ω : MarkedInner}

theorem lo_shift (h : ω.IsLegalNonempty) (hc : ω.case = .c) {a : ℤ} (h0 : 0 ≤ a)
    (h1 : a ≤ ω.widthZ - 1) : ω.lo (a + ω.period) = ω.lo a + ω.rowShift := by
  have := h.sides_c hc h0 h1
  unfold dLo at this
  omega

/-- The size of the offset `h_{a+q} - p - h_a` on a marked diagonal of a case-(c) mark. -/
theorem hi_shift (h : ω.IsLegalNonempty) (hc : ω.case = .c) {s t : ℤ} (hph : ω.IsPhases s t)
    {a : ℤ} (h0 : 0 ≤ a) (h1 : a ≤ ω.widthZ - 1) :
    ω.hi (a + ω.period) = ω.hi a + ω.rowShift +
      (if a < t then 1 else if a < s then 0 else -1) := by
  obtain ⟨hs1, hs2, ht1, ht2, hS, hT⟩ := id hph
  have hlt := h.phases_lt (Or.inl hc) hph
  have hdl := h.sides_c hc h0 h1
  have tl := hS a h0 h1
  have tu := hT a h0 h1
  have th1 := h.thin_lower a h0 h1
  have th2 := h.thin_upper h0 h1
  unfold TailLower at tl
  unfold TailUpper at tu
  have e : ω.dHi a = ω.hi (a + ω.period) - ω.rowShift - ω.hi a := rfl
  split_ifs with ha1 ha2 <;> omega

theorem mem_W_cell (h : ω.IsLegalNonempty) (hc : ω.case = .c) {s t : ℤ} (hph : ω.IsPhases s t)
    {a r : ℤ} :
    ω.cell a r ∈ ω.W ↔ 0 ≤ a ∧ a ≤ ω.widthZ - 1 ∧ ω.lo a ≤ r ∧
      r ≤ ω.hi a - (if s ≤ a then 1 else 0) := by
  rw [h.mem_W]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨h1, h2, h3, ?_⟩
    have := hi_shift h hc hph h1 h2
    have hlt := h.phases_lt (Or.inl hc) hph
    split_ifs at this ⊢ <;> omega
  · rintro ⟨h1, h2, h3, h4⟩
    have := hi_shift h hc hph h1 h2
    have := lo_shift h hc h1 h2
    have hlt := h.phases_lt (Or.inl hc) hph
    refine ⟨h1, h2, h3, ?_, ?_, ?_⟩ <;> split_ifs at * <;> omega

end Rem

end Corner

end Plan

end GluingCore
