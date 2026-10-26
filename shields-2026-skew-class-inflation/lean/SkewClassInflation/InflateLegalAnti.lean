/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewGluing.Antitranspose
import SkewGluing.Local

/-!
# Diagonal data of an antitransposed mark

Supports `lem:inflate-chart` in `shields-2026-skew-class-inflation.tex`, case (b).  The first and
last rows of the diagonal of content \(k\) of the antitransposed diagram are \(-\mathrm{hi}\,k-k\)
and \(-\mathrm{lo}\,k-k\), so the offsets `dLo`, `dHi` of the antitransposed mark are the
negatives of `dHi`, `dLo`, and the middle phases are unchanged.  Sorry-free.
-/

namespace SkewClassInflation

open SkewGluing MarkedInner

variable {ω : MarkedInner}

theorem diagLo_antitranspose {D : Diagram} {k : ℤ} (hk : k ∈ contents D) :
    diagLo (antitranspose D) k = -diagHi D k - k := by
  apply diagLo_eq_of
  · rw [mem_antitranspose]
    have := diagHi_mem hk
    convert this using 2 <;> simp <;> ring
  · intro i hi
    rw [mem_antitranspose] at hi
    have := le_diagHi (D := D) (k := k) hi (by ring)
    simp only at this
    omega

theorem diagHi_antitranspose {D : Diagram} {k : ℤ} (hk : k ∈ contents D) :
    diagHi (antitranspose D) k = -diagLo D k - k := by
  apply diagHi_eq_of
  · rw [mem_antitranspose]
    have := diagLo_mem hk
    convert this using 2 <;> simp <;> ring
  · intro i hi
    rw [mem_antitranspose] at hi
    have := diagLo_le (D := D) (k := k) hi (by ring)
    simp only at this
    omega

theorem anti_lo (h : ω.IsLegalNonempty) {a : ℤ} (h0 : 0 ≤ a)
    (h1 : a ≤ ω.period + ω.widthZ - 1) :
    ω.anti.lo a = -ω.hi a - (minContent ω.E + a) := by
  have hk : minContent ω.E + a ∈ contents ω.E := by
    rw [h.contents_E, Finset.mem_Icc]; omega
  unfold MarkedInner.lo MarkedInner.hi
  rw [anti_E, minContent_antitranspose, diagLo_antitranspose hk]

theorem anti_hi (h : ω.IsLegalNonempty) {a : ℤ} (h0 : 0 ≤ a)
    (h1 : a ≤ ω.period + ω.widthZ - 1) :
    ω.anti.hi a = -ω.lo a - (minContent ω.E + a) := by
  have hk : minContent ω.E + a ∈ contents ω.E := by
    rw [h.contents_E, Finset.mem_Icc]; omega
  unfold MarkedInner.lo MarkedInner.hi
  rw [anti_E, minContent_antitranspose, diagHi_antitranspose hk]

theorem rowShift_anti (ω : MarkedInner) : ω.anti.rowShift = -(ω.rowShift + ω.period) := by
  have := ω.v_eq
  unfold MarkedInner.rowShift
  change -ω.v.2 = _
  rw [show ω.v.2 = ω.rowShift + ω.period from by rw [this]]
  rfl

theorem widthZ_anti (ω : MarkedInner) : ω.anti.widthZ = ω.widthZ := by
  unfold MarkedInner.widthZ; rw [width_anti]

theorem dLo_anti (h : ω.IsLegalNonempty) {a : ℤ} (h0 : 0 ≤ a) (h1 : a ≤ ω.widthZ - 1) :
    ω.anti.dLo a = -ω.dHi a := by
  have hq := h.width_lt_period
  unfold MarkedInner.dLo MarkedInner.dHi
  rw [period_anti, rowShift_anti, anti_lo h (a := a + ω.period) (by omega) (by omega),
    anti_lo h h0 (by omega)]
  ring

theorem dHi_anti (h : ω.IsLegalNonempty) {a : ℤ} (h0 : 0 ≤ a) (h1 : a ≤ ω.widthZ - 1) :
    ω.anti.dHi a = -ω.dLo a := by
  have hq := h.width_lt_period
  unfold MarkedInner.dLo MarkedInner.dHi
  rw [period_anti, rowShift_anti, anti_hi h (a := a + ω.period) (by omega) (by omega),
    anti_hi h h0 (by omega)]
  ring

theorem isPhases_anti (h : ω.IsLegalNonempty) {s t : ℤ} :
    ω.anti.IsPhases s t ↔ ω.IsPhases s t := by
  have key : ∀ a : ℤ, 0 ≤ a → a ≤ ω.widthZ - 1 →
      (ω.anti.TailLower a ↔ ω.TailLower a) ∧ (ω.anti.TailUpper a ↔ ω.TailUpper a) := by
    intro a h0 h1
    unfold MarkedInner.TailLower MarkedInner.TailUpper
    rw [dLo_anti h h0 h1, dHi_anti h h0 h1]
    omega
  unfold MarkedInner.IsPhases
  rw [widthZ_anti]
  constructor
  · rintro ⟨a1, a2, a3, a4, a5, a6⟩
    exact ⟨a1, a2, a3, a4, fun a h0 h1 => (key a h0 h1).1.symm.trans (a5 a h0 h1),
      fun a h0 h1 => (key a h0 h1).2.symm.trans (a6 a h0 h1)⟩
  · rintro ⟨a1, a2, a3, a4, a5, a6⟩
    exact ⟨a1, a2, a3, a4, fun a h0 h1 => (key a h0 h1).1.trans (a5 a h0 h1),
      fun a h0 h1 => (key a h0 h1).2.trans (a6 a h0 h1)⟩

end SkewClassInflation
