/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.InflateLegalTranslate
import SkewGluing.Local

/-!
# Translation invariance of the middle phases

Supports `lem:inflate-chart` in `shields-2026-skew-class-inflation.tex`.  The diagonal data
`lo`, `hi` of a legal mark move by the row component of a translation, so the middle phases
are translation invariant.  Sorry-free.
-/

namespace SkewClassInflation

open SkewGluing MarkedInner

variable {ω : MarkedInner}

theorem lo_translate (h : ω.IsLegalNonempty) (u : ℤ × ℤ) {a : ℤ} (h0 : 0 ≤ a)
    (h1 : a ≤ ω.period + ω.widthZ - 1) : (ω.translate u).lo a = ω.lo a + u.1 := by
  have hE : ω.E.Nonempty := h.isConnectedSkew_E.2.1
  have hk : minContent ω.E + a ∈ contents ω.E := by
    rw [h.contents_E, Finset.mem_Icc]; omega
  have := diagLo_translate (D := ω.E) u _ hk
  unfold MarkedInner.lo
  change diagLo (SkewGluing.translate u ω.E) (minContent (SkewGluing.translate u ω.E) + a) = _
  rw [minContent_translate hE, show minContent ω.E + content u + a =
    minContent ω.E + a + content u by ring, this]

theorem hi_translate (h : ω.IsLegalNonempty) (u : ℤ × ℤ) {a : ℤ} (h0 : 0 ≤ a)
    (h1 : a ≤ ω.period + ω.widthZ - 1) : (ω.translate u).hi a = ω.hi a + u.1 := by
  have hE : ω.E.Nonempty := h.isConnectedSkew_E.2.1
  have hk : minContent ω.E + a ∈ contents ω.E := by
    rw [h.contents_E, Finset.mem_Icc]; omega
  have := diagHi_translate (D := ω.E) u _ hk
  unfold MarkedInner.hi
  change diagHi (SkewGluing.translate u ω.E) (minContent (SkewGluing.translate u ω.E) + a) = _
  rw [minContent_translate hE, show minContent ω.E + content u + a =
    minContent ω.E + a + content u by ring, this]

theorem isPhases_translate_iff (h : ω.IsLegalNonempty) (u : ℤ × ℤ) {s t : ℤ} :
    (ω.translate u).IsPhases s t ↔ ω.IsPhases s t := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  have e1 : (ω.translate u).widthZ = ω.widthZ := by
    unfold MarkedInner.widthZ; rw [width_translate]
  have e2 : (ω.translate u).period = ω.period := period_translate u ω
  have e3 : (ω.translate u).rowShift = ω.rowShift := rfl
  have key : ∀ a : ℤ, 0 ≤ a → a ≤ ω.widthZ - 1 →
      ((ω.translate u).TailLower a ↔ ω.TailLower a) ∧
      ((ω.translate u).TailUpper a ↔ ω.TailUpper a) := by
    intro a h0 h1
    unfold MarkedInner.TailLower MarkedInner.TailUpper MarkedInner.dLo MarkedInner.dHi
    rw [e2, e3, lo_translate h u h0 (by omega), lo_translate h u (by omega) (by omega),
      hi_translate h u h0 (by omega), hi_translate h u (by omega) (by omega)]
    omega
  unfold MarkedInner.IsPhases
  rw [e1]
  constructor
  · rintro ⟨a1, a2, a3, a4, a5, a6⟩
    exact ⟨a1, a2, a3, a4, fun a h0 h1 => (key a h0 h1).1.symm.trans (a5 a h0 h1),
      fun a h0 h1 => (key a h0 h1).2.symm.trans (a6 a h0 h1)⟩
  · rintro ⟨a1, a2, a3, a4, a5, a6⟩
    exact ⟨a1, a2, a3, a4, fun a h0 h1 => (key a h0 h1).1.trans (a5 a h0 h1),
      fun a h0 h1 => (key a h0 h1).2.trans (a6 a h0 h1)⟩

end SkewClassInflation
