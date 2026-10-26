/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.FullWindowTiling
import SkewGluing.ContentBand

/-!
# Connected skew first bands at private full-window cuts

Supports `shields-2026-skew-corner-descent.tex`, «The full-window boundary»
(`lem:boundary-full-window`).

A singleton private endpoint makes the first complete content band connected skew.
An arbitrary content cut need not be skew, so the singleton condition is retained.

Sorry-free.
-/

namespace SkewCornerDescent

open SkewGluing

/-- The first complete band inherits the parent's diagonal intervals and step bits. -/
theorem firstContentBand_hasDiagonalShape {D : Diagram} (hD : HasDiagonalShape D)
    (δ : ℤ) (hδ : 0 < δ)
    (hsmall : ∀ k, 0 ≤ k → k < δ → k ∈ contents D)
    (hzero : minContent D = 0)
    (hcut : diagLo D (δ - 1) = diagHi D (δ - 1)) :
    HasDiagonalShape (firstContentBand D δ) := by
  have hn : 1 ≤ δ.toNat := by omega
  have hncast : (δ.toNat : ℤ) = δ := Int.toNat_of_nonneg hδ.le
  apply Plan.MarkFacts.hasDiagonalShape_of_intervals
    (c := 0) (n := δ.toNat) (L := diagLo D) (R := diagHi D) hn
  · intro a r
    simp only [firstContentBand, Finset.mem_filter, content_mk_add, zero_add,
      hD.mem_iff, hncast]
    constructor
    · rintro ⟨⟨_, hl, hr⟩, ha0, haδ⟩
      exact ⟨ha0, haδ, hl, hr⟩
    · rintro ⟨ha0, haδ, hl, hr⟩
      exact ⟨⟨hsmall a ha0 haδ, hl, hr⟩, ha0, haδ⟩
  · intro a ha0 han
    exact diagLo_le_diagHi (hsmall a ha0 (by rwa [hncast] at han))
  · intro a ha1 han
    have hab := hD.2.2.2.1 a (hsmall a (by omega) (by rwa [hncast] at han))
      (hsmall (a - 1) (by omega) (by rw [hncast] at han; omega))
    simpa only [bitA, Finset.mem_insert, Finset.mem_singleton] using hab.1
  · intro a ha1 han
    have hab := hD.2.2.2.1 a (hsmall a (by omega) (by rwa [hncast] at han))
      (hsmall (a - 1) (by omega) (by rw [hncast] at han; omega))
    simpa only [bitB, Finset.mem_insert, Finset.mem_singleton] using hab.2
  · exact hD.2.2.2.2 0 (hsmall 0 (by omega) hδ)
      (Or.inl (by intro hm; have := minContent_le hm; omega))
  · simpa only [hncast] using hcut

/-- A private singleton terminal diagonal makes the actual first band connected skew. -/
theorem firstContentBand_isConnectedSkew {D : Diagram} (hD : IsConnectedSkew D)
    (δ : ℤ) (hδ : 0 < δ)
    (hsmall : ∀ k, 0 ≤ k → k < δ → k ∈ contents D)
    (hzero : minContent D = 0)
    (hcut : diagLo D (δ - 1) = diagHi D (δ - 1)) :
    IsConnectedSkew (firstContentBand D δ) := by
  exact isConnectedSkew_iff_diagonal.mpr
    (firstContentBand_hasDiagonalShape (isConnectedSkew_iff_diagonal.mp hD)
      δ hδ hsmall hzero hcut)

/-- The actual first complete band occupies exactly its stated content interval. -/
theorem firstContentBand_contents {D : Diagram} (δ : ℤ)
    (hsmall : ∀ k, 0 ≤ k → k < δ → k ∈ contents D) :
    contents (firstContentBand D δ) = Finset.Ico 0 δ := by
  ext k
  rw [mem_contents_iff, Finset.mem_Ico]
  constructor
  · rintro ⟨i, hi⟩
    simpa only [content_mk_add] using (Finset.mem_filter.mp hi).2
  · rintro ⟨hk0, hkδ⟩
    exact ⟨diagLo D k, Finset.mem_filter.mpr
      ⟨diagLo_mem (hsmall k hk0 hkδ), by simpa only [content_mk_add] using ⟨hk0, hkδ⟩⟩⟩

/-- The first complete band's span is the requested number of content diagonals. -/
theorem firstContentBand_span {D : Diagram} (δ : ℤ)
    (hsmall : ∀ k, 0 ≤ k → k < δ → k ∈ contents D) :
    span (firstContentBand D δ) = δ.toNat := by
  rw [span, firstContentBand_contents δ hsmall, Int.card_Ico]
  simp only [sub_zero]

end SkewCornerDescent
