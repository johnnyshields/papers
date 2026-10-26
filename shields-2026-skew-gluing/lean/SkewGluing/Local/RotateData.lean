import SkewGluing.Local.Diagonals

/-!
# Rotation of the diagonal data

Formalizes `shields-2026-skew-gluing.tex`, «Diagonal geometry» (`lem:gluing-local`).

Rotating a marked inner reverses the diagonals: `ℓ*_a = -h_{N-1-a}` and `h*_a = -ℓ_{N-1-a}`,
with `N = q + w`, while the displacement `v`, the period and the width are unchanged.  This is
what turns every statement about the lower copy into one about the upper copy.

Sorry-free.
-/

namespace SkewGluing

namespace MarkedInner

variable {ω : MarkedInner}

theorem IsLegalNonempty.rotate (h : ω.IsLegalNonempty) : ω.rotate.IsLegalNonempty := by
  refine ⟨isLegal_rotate h.1, ?_⟩
  change (SkewGluing.rotate ω.upper).Nonempty
  have : ω.upper.Nonempty := h.2.image _
  exact this.image _

theorem widthZ_rotate (ω : MarkedInner) : ω.rotate.widthZ = ω.widthZ := by
  unfold widthZ; rw [width_rotate]

theorem rowShift_rotate (ω : MarkedInner) : ω.rotate.rowShift = ω.rowShift := rfl

theorem IsLegalNonempty.minContent_rotate (h : ω.IsLegalNonempty) :
    minContent ω.rotate.E = -(minContent ω.E + ω.period + ω.widthZ - 1) := by
  have hne : ω.E.Nonempty := h.isConnectedSkew_E.2.1
  have := SkewGluing.minContent_rotate hne
  have h2 := h.maxContent_E
  change minContent (SkewGluing.rotate ω.E) = _
  omega

theorem IsLegalNonempty.lo_rotate (h : ω.IsLegalNonempty) (a : ℤ) :
    ω.rotate.lo a = -ω.hi (ω.period + ω.widthZ - 1 - a) := by
  unfold lo
  rw [h.minContent_rotate]
  have e : -(minContent ω.E + ω.period + ω.widthZ - 1) + a =
      -(minContent ω.E + (ω.period + ω.widthZ - 1 - a)) := by ring
  change diagLo (SkewGluing.rotate ω.E) _ = _
  rw [e, diagLo_rotate]
  rfl

theorem IsLegalNonempty.hi_rotate (h : ω.IsLegalNonempty) (a : ℤ) :
    ω.rotate.hi a = -ω.lo (ω.period + ω.widthZ - 1 - a) := by
  unfold hi
  rw [h.minContent_rotate]
  change diagHi (SkewGluing.rotate ω.E) _ = _
  rw [diagHi_rotate]
  have e : -(-(minContent ω.E + ω.period + ω.widthZ - 1) + a) =
      minContent ω.E + (ω.period + ω.widthZ - 1 - a) := by ring
  rw [e]
  rfl

end MarkedInner

end SkewGluing
