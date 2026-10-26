import SkewGluing.SmallOverlap.Construct

/-!
# The composite of a singleton mark: the basic facts

Formalizes `shields-2026-skew-gluing.tex`, «Period words, line inners, and small
overlaps» (`lem:gluing-small`), the singleton construction.

For the singleton mark `singletonMark (fromBits (g + 1) a b) cs` of `SingletonInnerData g a b`
with end bits of the attachment case `cs`, and a connected outer `D`: the mark is a legal mark with
a nonempty copy, of width one, period `g` and phases `1, 0`; the composite has span
`N_D g + 1`; and its boundary words on the positions `1, …, g - 1` are the bits `a`, `b`.

Sorry-free.
-/

namespace SkewGluing

open MarkedInner

namespace SmallOverlap

variable {g : ℕ} {a b : ℕ → ℤ}

theorem SingletonInnerData.isLegalNonempty (h : SingletonInnerData g a b) (cs : AttachCase)
    (hc : CaseBits cs (a 1) (a g)) :
    (singletonMark (fromBits (g + 1) a b) cs).IsLegalNonempty :=
  ⟨h.isLegal cs hc, by rw [h.singletonMark_W cs]; exact ⟨_, Finset.mem_singleton_self _⟩⟩

theorem SingletonInnerData.widthZ (h : SingletonInnerData g a b) (cs : AttachCase) :
    (singletonMark (fromBits (g + 1) a b) cs).widthZ = 1 := by
  unfold MarkedInner.widthZ; rw [h.singletonMark_width cs]; rfl

theorem SingletonInnerData.minContent_E (h : SingletonInnerData g a b) :
    minContent (fromBits (g + 1) a b) = 0 := minContent_fromBits h.bits

theorem SingletonInnerData.span_compose (h : SingletonInnerData g a b) (cs : AttachCase)
    (hc : CaseBits cs (a 1) (a g)) {D : Diagram} (hD : IsConnectedSkew D) :
    (span ((singletonMark (fromBits (g + 1) a b) cs).compose D) : ℤ) = span D * g + 1 := by
  rw [MarkedInner.span_compose hD (h.isLegal cs hc), h.singletonMark_period cs,
    h.singletonMark_width cs]
  simp

/-- The words of the composite on the positions `1, …, g - 1` are the bits of the inner. -/
theorem SingletonInnerData.compose_first (h : SingletonInnerData g a b) (cs : AttachCase)
    (hc : CaseBits cs (a 1) (a g)) {D : Diagram} (hD : IsConnectedSkew D) {x : ℕ} (hx1 : 1 ≤ x)
    (hx2 : x < g) :
    wordA ((singletonMark (fromBits (g + 1) a b) cs).compose D) x = a x ∧
    wordB ((singletonMark (fromBits (g + 1) a b) cs).compose D) x = b x := by
  have hq := h.singletonMark_period cs
  obtain ⟨e1, e2⟩ := wordAB_compose_first (h.isLegal cs hc) hD (k := x) (by omega)
    (by rw [hq]; omega)
  refine ⟨?_, ?_⟩
  · rw [e1, SingletonInnerData.singletonMark_E, h.minContent_E]
    have := bitA_fromBits h.bits (k := x) hx1 (by omega)
    rw [h.minContent_E] at this
    simpa using this
  · rw [e2, SingletonInnerData.singletonMark_E, h.minContent_E]
    have := bitB_fromBits h.bits (k := x) hx1 (by omega)
    rw [h.minContent_E] at this
    simpa using this

end SmallOverlap
end SkewGluing
