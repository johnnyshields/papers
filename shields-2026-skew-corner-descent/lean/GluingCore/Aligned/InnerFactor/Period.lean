/- TODO-COPIED: adapted from
`skew-factor-gluing/lean/SkewGluing/Aligned/InnerFactor/Period.lean`. -/
import GluingCore.Aligned.InnerFactor.Agree

/-!
# Repetition of a composite with a legal mark

Formalizes `shields-2026-skew-factor-gluing.tex`, «Equal and divisible periods»
(`prop:gluing-divisible`), via the two windows of `lem:gluing-local` (3).

For a legal mark `η` of period `Q` and width `w'` and a connected outer `C`, the first `Q` and the
last `Q` diagonals of `C ∘_η B` are the diagonals `[0, Q - 1]` and `[w', Q + w' - 1]` of `B`,
placed at the origins of the southwest and northeast cells of `C`.  So on the contents
`[min + w', min + Q - 1]` the cells of `C ∘_η B` repeat under the difference of the two origins
(`IsLegal.compose_repeat`), a translation of content `(N_C - 1) Q`.

Sorry-free.
-/

namespace GluingCore

open MarkedInner

namespace MarkedInner

variable {η : MarkedInner} {C : Diagram}

/-- The repetition of the composite on the overlap of its two windows. -/
theorem IsLegal.compose_repeat (hη : η.IsLegal) (hC : IsConnectedSkew C) {y : ℤ × ℤ}
    (h0 : minContent (η.compose C) + η.widthZ ≤ content y)
    (h1 : content y ≤ minContent (η.compose C) + η.period - 1) :
    y ∈ η.compose C ↔ y + (η.origin C (ne C) - η.origin C (sw C)) ∈ η.compose C := by
  have hCne := hC.2.1
  have hmin := hη.minContent_compose hC
  have hF := hη.compose_first_window hC
  have hL := hη.compose_last_window hC
  have hc1 : content (η.origin C (sw C)) = minContent C * η.period := by
    rw [content_origin, content_sw hCne]
  have hc2 : content (η.origin C (ne C)) = maxContent C * η.period := by
    rw [content_origin, content_ne hCne]
  have hmM : minContent C ≤ maxContent C := minContent_le (maxContent_mem hCne)
  have hq := hη.period_pos
  have hmul := mul_le_mul_of_nonneg_right hmM hq.le
  have e1 := Finset.ext_iff.mp hF y
  have e2 := Finset.ext_iff.mp hL (y + (η.origin C (ne C) - η.origin C (sw C)))
  simp only [Finset.mem_filter, mem_translate] at e1 e2
  have cτ : content (y + (η.origin C (ne C) - η.origin C (sw C))) =
      content y + (maxContent C * η.period - minContent C * η.period) := by
    rw [content_add, content_sub, hc1, hc2]
  have hw0 : (0 : ℤ) ≤ η.width := by positivity
  have hyB : y - η.origin C (sw C) ∈ η.E ↔ y ∈ η.compose C := by
    have := e1
    rw [content_sub, hc1] at this
    constructor
    · intro hy
      have := this.mpr ⟨hy, by omega⟩
      exact this.1
    · intro hy
      exact (this.mp ⟨hy, by omega⟩).1
  have hyB' : y + (η.origin C (ne C) - η.origin C (sw C)) - η.origin C (ne C) ∈ η.E ↔
      y + (η.origin C (ne C) - η.origin C (sw C)) ∈ η.compose C := by
    have := e2
    rw [content_sub, hc2, cτ] at this
    constructor
    · intro hy
      have := this.mpr ⟨hy, by unfold widthZ at h0; omega⟩
      exact this.1
    · intro hy
      exact (this.mp ⟨hy, by unfold widthZ at h0; omega⟩).1
  have e : y + (η.origin C (ne C) - η.origin C (sw C)) - η.origin C (ne C) =
      y - η.origin C (sw C) := by abel
  rw [e] at hyB'
  rw [← hyB, ← hyB']

theorem content_ne_sub_sw_origin (η : MarkedInner) (hC : IsConnectedSkew C) :
    content (η.origin C (ne C) - η.origin C (sw C)) =
      (maxContent C - minContent C) * η.period := by
  have hCne := hC.2.1
  rw [content_sub, content_origin, content_origin, content_ne hCne, content_sw hCne]
  ring

end MarkedInner

end GluingCore
