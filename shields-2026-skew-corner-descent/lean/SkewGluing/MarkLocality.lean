/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewGluing.Mark

/-!
# Legal-mark diagonal geometry

Formalizes `shields-2026-skew-corner-descent.tex`, «Marked inners and finite end caps»
(`sec:marks`, `eq:local-properties`).

Gluing along a common diagonal preserves connected skewness. The middle of a legal nonempty
mark is connected and has at most one cell on each marked diagonal.

TODO-COPIED: selected gluing and thinness proofs from
skew-factor-gluing/lean/SkewGluing/MarkLocality.

Sorry-free.
-/

namespace SkewGluing

def glueAt (A B : Diagram) (m : ℤ) : Diagram :=
  A.filter (fun x => content x ≤ m) ∪ B.filter (fun x => m ≤ content x)

theorem mem_glueAt {A B : Diagram} {m : ℤ} {x : ℤ × ℤ} :
    x ∈ glueAt A B m ↔ (content x ≤ m ∧ x ∈ A) ∨ (m ≤ content x ∧ x ∈ B) := by
  simp only [glueAt, Finset.mem_union, Finset.mem_filter]
  tauto

section Glue

variable {A B : Diagram} {m : ℤ}

theorem mem_glueAt_of_le (hag : ∀ x, content x = m → (x ∈ A ↔ x ∈ B)) {x : ℤ × ℤ}
    (hx : content x ≤ m) : x ∈ glueAt A B m ↔ x ∈ A := by
  rw [mem_glueAt]
  constructor
  · rintro (⟨_, h⟩ | ⟨h1, h⟩)
    · exact h
    · exact (hag x (le_antisymm hx h1)).mpr h
  · intro h; exact Or.inl ⟨hx, h⟩

theorem mem_glueAt_of_ge (hag : ∀ x, content x = m → (x ∈ A ↔ x ∈ B)) {x : ℤ × ℤ}
    (hx : m ≤ content x) : x ∈ glueAt A B m ↔ x ∈ B := by
  rw [mem_glueAt]
  constructor
  · rintro (⟨h1, h⟩ | ⟨_, h⟩)
    · exact (hag x (le_antisymm h1 hx)).mp h
    · exact h
  · intro h; exact Or.inr ⟨hx, h⟩

theorem diagRows_glueAt_of_le (hag : ∀ x, content x = m → (x ∈ A ↔ x ∈ B)) {k : ℤ}
    (hk : k ≤ m) : diagRows (glueAt A B m) k = diagRows A k := by
  ext i
  rw [mem_diagRows, mem_diagRows, mem_glueAt_of_le hag (by simp only [content]; omega)]

theorem diagRows_glueAt_of_ge (hag : ∀ x, content x = m → (x ∈ A ↔ x ∈ B)) {k : ℤ}
    (hk : m ≤ k) : diagRows (glueAt A B m) k = diagRows B k := by
  ext i
  rw [mem_diagRows, mem_diagRows, mem_glueAt_of_ge hag (by simp only [content]; omega)]

theorem mem_contents_glueAt (hag : ∀ x, content x = m → (x ∈ A ↔ x ∈ B)) {k : ℤ} :
    k ∈ contents (glueAt A B m) ↔ (k ≤ m ∧ k ∈ contents A) ∨ (m ≤ k ∧ k ∈ contents B) := by
  rw [mem_contents_iff, mem_contents_iff, mem_contents_iff]
  constructor
  · rintro ⟨i, hi⟩
    rw [mem_glueAt] at hi
    simp only [content] at hi
    rcases hi with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by omega, i, h2⟩
    · exact Or.inr ⟨by omega, i, h2⟩
  · rintro (⟨h1, i, hi⟩ | ⟨h1, i, hi⟩)
    · exact ⟨i, (mem_glueAt_of_le hag (by simp only [content]; omega)).mpr hi⟩
    · exact ⟨i, (mem_glueAt_of_ge hag (by simp only [content]; omega)).mpr hi⟩

theorem diagLo_glueAt_of_le (hag : ∀ x, content x = m → (x ∈ A ↔ x ∈ B)) {k : ℤ}
    (hk : k ≤ m) : diagLo (glueAt A B m) k = diagLo A k := by
  unfold diagLo; rw [diagRows_glueAt_of_le hag hk]

theorem diagLo_glueAt_of_ge (hag : ∀ x, content x = m → (x ∈ A ↔ x ∈ B)) {k : ℤ}
    (hk : m ≤ k) : diagLo (glueAt A B m) k = diagLo B k := by
  unfold diagLo; rw [diagRows_glueAt_of_ge hag hk]

theorem diagHi_glueAt_of_le (hag : ∀ x, content x = m → (x ∈ A ↔ x ∈ B)) {k : ℤ}
    (hk : k ≤ m) : diagHi (glueAt A B m) k = diagHi A k := by
  unfold diagHi; rw [diagRows_glueAt_of_le hag hk]

theorem diagHi_glueAt_of_ge (hag : ∀ x, content x = m → (x ∈ A ↔ x ∈ B)) {k : ℤ}
    (hk : m ≤ k) : diagHi (glueAt A B m) k = diagHi B k := by
  unfold diagHi; rw [diagRows_glueAt_of_ge hag hk]

/-- **Gluing along a diagonal.**  If `A` and `B` are connected skew diagrams that have the
same cells on a content `m` occupied by both, then the diagram that follows `A` below `m` and
`B` above `m` is again connected skew.  (This is the diagonal criterion applied to a union of
overlapping diagonal windows, as in the proof of `eq:local-properties`.) -/
theorem isConnectedSkew_glueAt (hA : IsConnectedSkew A) (hB : IsConnectedSkew B)
    (hmA : m ∈ contents A) (hmB : m ∈ contents B)
    (hag : ∀ x, content x = m → (x ∈ A ↔ x ∈ B)) : IsConnectedSkew (glueAt A B m) := by
  rw [isConnectedSkew_iff_diagonal] at hA hB ⊢
  have hcont := @mem_contents_glueAt A B m hag
  have hcA : ∀ k, k ∈ contents A ↔ minContent A ≤ k ∧ k ≤ maxContent A := fun k =>
    hA.mem_contents_iff
  have hcB : ∀ k, k ∈ contents B ↔ minContent B ≤ k ∧ k ≤ maxContent B := fun k =>
    hB.mem_contents_iff
  have hCc : ∀ k, k ∈ contents (glueAt A B m) ↔ minContent A ≤ k ∧ k ≤ maxContent B := by
    intro k
    rw [hcont, hcA, hcB]
    have h1 := (hcA m).mp hmA
    have h2 := (hcB m).mp hmB
    omega
  have hAm := (hcA m).mp hmA
  have hBm := (hcB m).mp hmB
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨(diagLo A m, diagLo A m + m), ?_⟩
    rw [mem_glueAt]
    exact Or.inl ⟨by simp only [content]; omega, diagLo_mem hmA⟩
  · intro x hx y hy k hk
    rw [Finset.mem_Icc] at hk
    have hx' := (hCc _).mp (content_mem_contents hx)
    have hy' := (hCc _).mp (content_mem_contents hy)
    rw [hCc]
    omega
  · intro x hx y hy hxy i hi
    rw [Finset.mem_Icc] at hi
    rw [mem_glueAt] at hx hy ⊢
    have hc : content x = content y := hxy
    rcases hx with ⟨hx1, hx2⟩ | ⟨hx1, hx2⟩
    · have hy2 : y ∈ A := by
        rcases hy with ⟨_, h⟩ | ⟨h1, h⟩
        · exact h
        · exact (hag y (by omega)).mpr h
      refine Or.inl ⟨by simp only [content] at hx1 ⊢; omega, ?_⟩
      have := hA.2.2.1 x hx2 y hy2 hxy i (Finset.mem_Icc.mpr hi)
      simpa [hxy] using this
    · have hy2 : y ∈ B := by
        rcases hy with ⟨h1, h⟩ | ⟨_, h⟩
        · exact (hag y (by omega)).mp h
        · exact h
      refine Or.inr ⟨by simp only [content] at hx1 ⊢; omega, ?_⟩
      have := hB.2.2.1 x hx2 y hy2 hxy i (Finset.mem_Icc.mpr hi)
      simpa [hxy] using this
  · intro k hk hk1
    rw [hCc] at hk hk1
    by_cases hkm : k ≤ m
    · have hkm1 : k - 1 ≤ m := by omega
      have hkA : k ∈ contents A := (hcA k).mpr ⟨hk.1, by have := (hcA m).mp hmA; omega⟩
      have hk1A : k - 1 ∈ contents A := (hcA _).mpr ⟨hk1.1, by omega⟩
      have := hA.2.2.2.1 k hkA hk1A
      unfold bitA bitB
      rw [diagLo_glueAt_of_le hag hkm, diagLo_glueAt_of_le hag hkm1,
        diagHi_glueAt_of_le hag hkm, diagHi_glueAt_of_le hag hkm1]
      exact this
    · have hkm : m ≤ k - 1 := by omega
      have hkB : k ∈ contents B := (hcB k).mpr ⟨by have := (hcB m).mp hmB; omega, hk.2⟩
      have hk1B : k - 1 ∈ contents B := (hcB _).mpr ⟨by have := (hcB m).mp hmB; omega, by omega⟩
      have := hB.2.2.2.1 k hkB hk1B
      unfold bitA bitB
      rw [diagLo_glueAt_of_ge hag (by omega : m ≤ k), diagLo_glueAt_of_ge hag hkm,
        diagHi_glueAt_of_ge hag (by omega : m ≤ k), diagHi_glueAt_of_ge hag hkm]
      exact this
  · intro k hk hend
    have hk' := (hCc k).mp hk
    rcases lt_trichotomy k m with hkm | hkm | hkm
    · rw [diagLo_glueAt_of_le hag hkm.le, diagHi_glueAt_of_le hag hkm.le]
      apply hA.2.2.2.2 k ((hcA k).mpr ⟨hk'.1, by omega⟩)
      rcases hend with h | h
      · left
        rw [hcA]; rw [hCc] at h; omega
      · right
        rw [hcA]; rw [hCc] at h; omega
    · subst hkm
      rcases hend with h | h
      · rw [diagLo_glueAt_of_le hag le_rfl, diagHi_glueAt_of_le hag le_rfl]
        apply hA.2.2.2.2 k hmA
        left
        rw [hcA]; rw [hCc] at h; omega
      · rw [diagLo_glueAt_of_ge hag le_rfl, diagHi_glueAt_of_ge hag le_rfl]
        apply hB.2.2.2.2 k hmB
        right
        rw [hcB]; rw [hCc] at h; omega
    · rw [diagLo_glueAt_of_ge hag hkm.le, diagHi_glueAt_of_ge hag hkm.le]
      apply hB.2.2.2.2 k ((hcB k).mpr ⟨by omega, hk'.2⟩)
      rcases hend with h | h
      · left
        rw [hcB]; rw [hCc] at h; omega
      · right
        rw [hcB]; rw [hCc] at h; omega

end Glue

/-! ### Content ranges and the middle of a legal mark -/

theorem exists_cell_of_mem_contents {D : Diagram} {k : ℤ} (h : k ∈ contents D) :
    ∃ x ∈ D, content x = k := by
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp h
  exact ⟨x, hx, rfl⟩

theorem exists_cell_of_connectedSkew {D : Diagram} (h : IsConnectedSkew D) {d : ℤ}
    (h0 : minContent D ≤ d) (h1 : d ≤ maxContent D) : ∃ z ∈ D, content z = d := by
  have h' := isConnectedSkew_iff_diagonal.mp h
  have : d ∈ contents D := h'.mem_contents_iff.mpr ⟨h0, h1⟩
  exact exists_cell_of_mem_contents this

namespace MarkedInner

variable {ω : MarkedInner}

theorem mem_upper {x : ℤ × ℤ} : x ∈ ω.upper ↔ x - ω.v ∈ ω.W := mem_translate

/-- The contents of the copy `W₋` of a nonempty mark are `[c₀, c₀ + w - 1]`, where `c₀` is the
least content of `E`. -/
theorem IsNonemptyMark.W_range (hE : IsConnectedSkew ω.E) (h : ω.IsNonemptyMark) :
    minContent ω.W = minContent ω.E ∧
      maxContent ω.W = minContent ω.E + ω.width - 1 := by
  obtain ⟨hne, hW, hWE, -, hsw, -, -⟩ := h
  have hEne : ω.E.Nonempty := hE.2.1
  have hmin : minContent ω.W = minContent ω.E := by
    have hs : contents ω.W ⊆ contents ω.E := Finset.image_subset_image hWE
    apply le_antisymm
    · have : content (sw ω.E) ∈ contents ω.W := content_mem_contents hsw
      rw [content_sw hEne] at this
      exact minContent_le this
    · exact minContent_le (hs (minContent_mem hne))
  have hspan := span_eq_of_isConnectedSkew hW
  refine ⟨hmin, ?_⟩
  have : (ω.width : ℤ) = span ω.W := rfl
  omega

theorem IsNonemptyMark.exists_cell_W (hE : IsConnectedSkew ω.E) (h : ω.IsNonemptyMark) {d : ℤ}
    (h0 : minContent ω.E ≤ d) (h1 : d ≤ minContent ω.E + ω.width - 1) :
    ∃ z ∈ ω.W, content z = d := by
  obtain ⟨h2, h3⟩ := h.W_range hE
  exact exists_cell_of_connectedSkew h.2.1 (by omega) (by omega)

/-- The contents of the copy `W₊`. -/
theorem IsNonemptyMark.content_upper (hE : IsConnectedSkew ω.E) (h : ω.IsNonemptyMark)
    {x : ℤ × ℤ} (hx : x ∈ ω.upper) :
    minContent ω.E + ω.period ≤ content x ∧
      content x ≤ minContent ω.E + ω.period + ω.width - 1 := by
  obtain ⟨h2, h3⟩ := h.W_range hE
  have h4 : minContent ω.W ≤ content (x - ω.v) := minContent_le (content_mem_contents
    (mem_upper.mp hx))
  have h5 : content (x - ω.v) ≤ maxContent ω.W := le_maxContent (content_mem_contents
    (mem_upper.mp hx))
  rw [content_sub] at h4 h5
  have : ω.period = content ω.v := rfl
  omega

theorem IsNonemptyMark.content_W (hE : IsConnectedSkew ω.E) (h : ω.IsNonemptyMark)
    {x : ℤ × ℤ} (hx : x ∈ ω.W) :
    minContent ω.E ≤ content x ∧ content x ≤ minContent ω.E + ω.width - 1 := by
  obtain ⟨h2, h3⟩ := h.W_range hE
  have h4 : minContent ω.W ≤ content x := minContent_le (content_mem_contents hx)
  have h5 : content x ≤ maxContent ω.W := le_maxContent (content_mem_contents hx)
  omega

theorem IsNonemptyMark.maxContent_E (hE : IsConnectedSkew ω.E) (h : ω.IsNonemptyMark) :
    maxContent ω.E = minContent ω.E + ω.period + ω.width - 1 := by
  obtain ⟨h2, h3⟩ := h.W_range hE
  have := h.maxContent_eq hE
  have : ω.period = content ω.v := rfl
  omega

/-- A legal mark with a nonempty copy `W₋` is a nonempty mark. -/
theorem IsLegal.isNonemptyMark (h : ω.IsLegal) (hW : ω.W.Nonempty) : ω.IsNonemptyMark := by
  rcases h.1.2 with h' | h'
  · exact absurd h'.1 hW.ne_empty
  · exact h'

/-- **The middle of a legal mark is connected skew** (the first assertion of
`eq:local-properties` for a single mark, used with the window comparison): III makes the
two removals connected skew, and `w < q` lets the diagonal `w` serve as the gluing diagonal. -/
theorem IsLegal.middle_connected (h : ω.IsLegal) (hW : ω.W.Nonempty) :
    IsConnectedSkew ω.middle := by
  have hnon := h.isNonemptyMark hW
  have hE := h.1.1
  obtain ⟨hwq0, hwq⟩ := h.2.2.1
  obtain ⟨hI, hII⟩ := h.2.2.2.1
  obtain ⟨h2, h3⟩ := hnon.W_range hE
  have hmaxE := hnon.maxContent_E hE
  have hq : ω.period = content ω.v := rfl
  set c0 := minContent ω.E with hc0
  have hW1 : ∀ x ∈ ω.W, content x ≤ c0 + ω.width - 1 := fun x hx =>
    (hnon.content_W hE hx).2
  have hU1 : ∀ x ∈ ω.upper, c0 + ω.period ≤ content x := fun x hx =>
    (hnon.content_upper hE hx).1
  have hag : ∀ x, content x = c0 + ω.width →
      (x ∈ ω.E \ ω.W ↔ x ∈ ω.E \ ω.upper) := by
    intro x hx
    have a1 : x ∉ ω.W := fun h => by have := hW1 x h; omega
    have a2 : x ∉ ω.upper := fun h => by have := hU1 x h; omega
    simp [Finset.mem_sdiff, a1, a2]
  have heq : ω.middle = glueAt (ω.E \ ω.W) (ω.E \ ω.upper) (c0 + ω.width) := by
    ext x
    rw [mem_glueAt]
    unfold middle
    simp only [Finset.mem_sdiff, Finset.mem_union]
    have f1 : content x ≤ c0 + ω.width → x ∉ ω.upper := fun hx h => by
      have := hU1 x h; omega
    have f2 : c0 + (ω.width : ℤ) ≤ content x → x ∉ ω.W := fun hx h => by
      have := hW1 x h; omega
    have f3 : content x ≤ c0 + ω.width ∨ c0 + (ω.width : ℤ) ≤ content x := by omega
    tauto
  rw [heq]
  obtain ⟨x, hx, hc⟩ := exists_cell_of_connectedSkew hE (d := c0 + ω.width)
    (by omega) (by omega)
  have a1 : x ∉ ω.W := fun h => by have := hW1 x h; omega
  have a2 : x ∉ ω.upper := fun h => by have := hU1 x h; omega
  exact isConnectedSkew_glueAt hI hII
    (hc ▸ content_mem_contents (Finset.mem_sdiff.mpr ⟨hx, a1⟩))
    (hc ▸ content_mem_contents (Finset.mem_sdiff.mpr ⟨hx, a2⟩)) hag

end MarkedInner

namespace MarkedInner

variable {ω : MarkedInner}

theorem mem_middle {x : ℤ × ℤ} : x ∈ ω.middle ↔ x ∈ ω.E ∧ x ∉ ω.W ∧ x ∉ ω.upper := by
  unfold middle
  simp only [Finset.mem_sdiff, Finset.mem_union, not_or]

theorem content_sub_eCell (x : ℤ × ℤ) : content (x - eCell) = content x := by
  simp [content, eCell]

theorem content_neg_eCell_add (x : ℤ × ℤ) : content (x + -eCell) = content x := by
  simp [content, eCell]


theorem cell_eq_of_content {c : ℤ × ℤ} {d : ℤ} (h : content c = d) : c = (c.1, c.1 + d) := by
  ext <;> simp [content] at h ⊢
  all_goals omega

/-- Condition IV at the unshifted copies: a cell `x` of the hatted middle is not adjacent to a
cell `y` of the hatted mark `Ŵ₋`, the latter given by a diagonal pair `(y, y + e)` with one cell
in `W₋` and the other in `E`. -/
theorem IsLegal.no_hat_adjacent (h : ω.IsLegal) {x y : ℤ × ℤ} (hx : x ∈ ω.middle)
    (hx' : x + eCell ∈ ω.middle) (hadj : CellAdj x y)
    (hy : (y ∈ ω.W ∧ y + eCell ∈ ω.E) ∨ (y + eCell ∈ ω.W ∧ y ∈ ω.E)) : False := by
  have hIV := h.2.2.2.2
  have hxm : x ∈ hatMiddle (translate ((0 : ℤ) • ω.v) ω.middle) := by
    simp only [hatMiddle, zero_smul, translate_zero, Set.mem_ofPred_eq]
    exact ⟨hx, hx'⟩
  have hper : ∀ z, z ∈ ω.E → z ∈ ω.periodicUnion := fun z hz =>
    show ∃ k : ℤ, z - k • ω.v ∈ ω.E from ⟨0, by simpa using hz⟩
  have hym : y ∈ ω.hatMark (translate ((0 : ℤ) • ω.v) ω.W) := by
    simp only [hatMark, zero_smul, translate_zero, Set.mem_union, Set.mem_ofPred_eq]
    rcases hy with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr ⟨h1, hper _ h2⟩
    · exact Or.inl ⟨hper _ h2, h1⟩
  exact hIV 0 0 x hxm y hym hadj

/-- **Southeast tails are thin.**  There is no middle cell `z` on a marked diagonal of `W₋`
with `z + e` in the middle and `z - e` in `W₋` (so that `z` and `z + e` are the first two cells of
a southeast tail), provided the preceding diagonal has at most one middle cell.  Otherwise the
western neighbor of `z` is a cell of `W₋` whose diagonal successor lies in `E`, and it is adjacent
to the hatted middle cell `z`, against IV; if it were a middle cell, the preceding diagonal would
carry two. -/
theorem IsLegal.not_se_config (h : ω.IsLegal) (hW : ω.W.Nonempty) {z : ℤ × ℤ}
    (hz : z ∈ ω.middle) (hz' : z + eCell ∈ ω.middle) (hu : z - eCell ∈ ω.W)
    (hd : content z ≤ minContent ω.E + ω.width - 1)
    (hthin : ∀ a ∈ ω.middle, ∀ b ∈ ω.middle, content a = content z - 1 →
      content b = content z - 1 → a = b) : False := by
  have hnon := h.isNonemptyMark hW
  have hsk := h.1.1.1
  have hWsk := hnon.2.1.1
  obtain ⟨-, hwq⟩ := h.2.2.1
  obtain ⟨hzE, hzW, hzU⟩ := mem_middle.mp hz
  have hz'E := (mem_middle.mp hz').1
  have huE := hnon.2.2.1 hu
  have hupper : ∀ c : ℤ × ℤ, content c < minContent ω.E + ω.period → c ∉ ω.upper :=
    fun c hc hh => by have := (hnon.content_upper h.1.1 hh).1; omega
  obtain ⟨i, j⟩ := z
  simp only [eCell, Prod.mk_add_mk, Prod.mk_sub_mk] at hz' hu hz'E huE
  have hw₀E : (i, j - 1) ∈ ω.E :=
    hsk.mem huE hzE (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hs₀E : (i + 1, j) ∈ ω.E :=
    hsk.mem hzE hz'E (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hc0 : content ((i, j - 1)) < minContent ω.E + ω.period := by
    simp only [content] at hd ⊢; omega
  have hc1 : content ((i + 1, j)) < minContent ω.E + ω.period := by
    simp only [content] at hd ⊢; omega
  by_cases hw₀ : (i, j - 1) ∈ ω.W
  · refine h.no_hat_adjacent (x := (i, j)) hz (by simpa [eCell] using hz') (y := (i, j - 1))
      ?_ (Or.inl ⟨hw₀, by simpa [eCell] using hs₀E⟩)
    rw [cellAdj_iff]; exact Or.inl ⟨rfl, Or.inl (by simp)⟩
  · have hw₀O : (i, j - 1) ∈ ω.middle := mem_middle.mpr ⟨hw₀E, hw₀, hupper _ hc0⟩
    have hs₀W : (i + 1, j) ∉ ω.W := fun hh =>
      hw₀ (hWsk.mem hu hh (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
    have hs₀O : (i + 1, j) ∈ ω.middle := mem_middle.mpr ⟨hs₀E, hs₀W, hupper _ hc1⟩
    have := hthin _ hw₀O _ hs₀O (by simp only [content] at hc0 ⊢; omega)
      (by simp only [content] at hc1 ⊢; omega)
    simp at this

/-- **Northwest tails are thin.**  The mirror of `IsLegal.not_se_config`: there is no middle
cell `a` on a marked diagonal of `W₋` with `a - e` in the middle and `a + e` in `W₋`, provided
the preceding diagonal has at most one middle cell. -/
theorem IsLegal.not_nw_config (h : ω.IsLegal) (hW : ω.W.Nonempty) {a : ℤ × ℤ}
    (ha : a ∈ ω.middle) (ha' : a - eCell ∈ ω.middle) (hu : a + eCell ∈ ω.W)
    (hd : content a ≤ minContent ω.E + ω.width - 1)
    (hthin : ∀ c ∈ ω.middle, ∀ b ∈ ω.middle, content c = content a - 1 →
      content b = content a - 1 → c = b) : False := by
  have hnon := h.isNonemptyMark hW
  have hsk := h.1.1.1
  have hWsk := hnon.2.1.1
  obtain ⟨-, hwq⟩ := h.2.2.1
  obtain ⟨haE, haW, haU⟩ := mem_middle.mp ha
  have ha'E := (mem_middle.mp ha').1
  have huE := hnon.2.2.1 hu
  have hupper : ∀ c : ℤ × ℤ, content c < minContent ω.E + ω.period → c ∉ ω.upper :=
    fun c hc hh => by have := (hnon.content_upper h.1.1 hh).1; omega
  obtain ⟨i, j⟩ := a
  simp only [eCell, Prod.mk_add_mk, Prod.mk_sub_mk] at ha' hu ha'E huE
  have hs₀E : (i + 1, j) ∈ ω.E :=
    hsk.mem haE huE (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hw₀E : (i, j - 1) ∈ ω.E :=
    hsk.mem ha'E hs₀E (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hc0 : content ((i, j - 1)) < minContent ω.E + ω.period := by
    simp only [content] at hd ⊢; omega
  have hc1 : content ((i + 1, j)) < minContent ω.E + ω.period := by
    simp only [content] at hd ⊢; omega
  by_cases hs₀ : (i + 1, j) ∈ ω.W
  · refine h.no_hat_adjacent (x := (i - 1, j - 1)) ha' (by simpa [eCell] using ha)
      (y := (i, j - 1)) ?_ (Or.inr ⟨by simpa [eCell] using hs₀, hw₀E⟩)
    rw [cellAdj_iff]; exact Or.inr ⟨rfl, Or.inr (by simp)⟩
  · have hs₀O : (i + 1, j) ∈ ω.middle := mem_middle.mpr ⟨hs₀E, hs₀, hupper _ hc1⟩
    have hw₀W : (i, j - 1) ∉ ω.W := fun hh =>
      haW (hWsk.mem hh hu (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
    have hw₀O : (i, j - 1) ∈ ω.middle := mem_middle.mpr ⟨hw₀E, hw₀W, hupper _ hc0⟩
    have := hthin _ hw₀O _ hs₀O (by simp only [content] at hc0 ⊢; omega)
      (by simp only [content] at hc1 ⊢; omega)
    simp at this


theorem rotate_W_nonempty (hW : ω.W.Nonempty) : ω.rotate.W.Nonempty :=
  (hW.image _).image _

/-- **`eq:local-properties` (1), second assertion, on the marked diagonals of `W₋`.**  The middle
of a legal mark has at most one cell on each content of `W₋`.  Proved by strong induction on the
diagonal: two middle cells on one diagonal lie on one side of `W₋`; the one next to `W₋` then
yields a configuration excluded by `IsLegal.not_se_config` or `IsLegal.not_nw_config`, which use
IV and the induction hypothesis on the preceding diagonal.

**Differs from the paper's route.**  The side of the tail and the adjacent hatted pair are read
from cells and skewness, instead of from the endpoint steps of the diagonal criterion. -/
theorem IsLegal.thin_lower (h : ω.IsLegal) (hW : ω.W.Nonempty) :
    ∀ n : ℕ, ∀ x ∈ ω.middle, ∀ y ∈ ω.middle, content x = minContent ω.E + n →
      content y = content x → (n : ℤ) ≤ ω.width - 1 → x = y := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x hx y hy hcx hcy hn
  by_contra hxy
  have hnon := h.isNonemptyMark hW
  have hEc := h.1.1
  obtain ⟨-, hwq⟩ := h.2.2.1
  have hmid := isConnectedSkew_iff_diagonal.mp (h.middle_connected hW)
  have hn1 : 1 ≤ n := by
    by_contra h0
    have hn0 : n = 0 := by omega
    subst hn0
    have := eq_sw_of_content hEc (mem_middle.mp hx).1 (by simpa using hcx)
    exact (mem_middle.mp hx).2.1 (this ▸ hnon.2.2.2.2.1)
  have hupper : ∀ c : ℤ × ℤ, content c < minContent ω.E + ω.period → c ∉ ω.upper :=
    fun c hc hh => by have := (hnon.content_upper hEc hh).1; omega
  have hthin : ∀ a ∈ ω.middle, ∀ b ∈ ω.middle, content a = content x - 1 →
      content b = content x - 1 → a = b := by
    intro a ha b hb hca hcb
    exact ih (n - 1) (by omega) a ha b hb (by omega) (by omega) (by omega)
  obtain ⟨x₁, hx₁, y₁, hy₁, hc₁, hc₂, hlt⟩ : ∃ x₁ ∈ ω.middle, ∃ y₁ ∈ ω.middle,
      content x₁ = content x ∧ content y₁ = content x ∧ x₁.1 < y₁.1 := by
    rcases lt_trichotomy x.1 y.1 with h1 | h1 | h1
    · exact ⟨x, hx, y, hy, rfl, hcy, h1⟩
    · exact absurd (Prod.ext h1 (by simp only [content] at hcy; omega)) hxy
    · exact ⟨y, hy, x, hx, hcy, rfl, h1⟩
  obtain ⟨w', hw', hcw⟩ := hnon.exists_cell_W hEc (d := content x) (by omega) (by omega)
  have hw'E : w' ∈ ω.E := hnon.2.2.1 hw'
  have hw'O : w' ∉ ω.middle := fun hh => (mem_middle.mp hh).2.1 hw'
  have hcell : ∀ c : ℤ × ℤ, content c = content x → c = (c.1, c.1 + content x) :=
    fun c hc => cell_eq_of_content hc
  have hcc : ∀ r : ℤ, content ((r, r + content x)) = content x := fun r => by
    simp [content]
  have hpe : ∀ r : ℤ, (r, r + content x) + eCell = (r + 1, r + 1 + content x) := fun r => by
    ext <;> simp [eCell]
    all_goals ring
  have hpm : ∀ r : ℤ, (r, r + content x) - eCell = (r - 1, r - 1 + content x) := fun r => by
    ext <;> simp [eCell]
    all_goals ring
  have hiv : ∀ r₀ r₁' : ℤ, (r₀, r₀ + content x) ∈ ω.middle → (r₁', r₁' + content x) ∈ ω.middle →
      ∀ i : ℤ, r₀ ≤ i → i ≤ r₁' → (i, i + content x) ∈ ω.middle := by
    intro r₀ r₁' h₀ h₁ i h1 h2
    have := hmid.2.2.1 _ h₀ _ h₁ (by rw [hcc, hcc]) i (Finset.mem_Icc.mpr ⟨h1, h2⟩)
    rwa [hcc] at this
  have hx₁c : (x₁.1, x₁.1 + content x) ∈ ω.middle := by rw [← hcell _ hc₁]; exact hx₁
  have hy₁c : (y₁.1, y₁.1 + content x) ∈ ω.middle := by rw [← hcell _ hc₂]; exact hy₁
  have hw'c : w' = (w'.1, w'.1 + content x) := hcell _ hcw
  have hsk := hEc.1
  rcases lt_trichotomy w'.1 x₁.1 with hρ | hρ | hρ
  · -- the middle lies southeast of `W₋`
    let S := (Finset.Icc (w'.1 + 1) x₁.1).filter (fun r => (r, r + content x) ∈ ω.middle)
    have hSne : S.Nonempty := ⟨x₁.1, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩,
      hx₁c⟩⟩
    have hr₁ := Finset.min'_mem S hSne
    have hr₁le : ∀ r ∈ S, S.min' hSne ≤ r := fun r hr => Finset.min'_le S r hr
    set r₁ := S.min' hSne with hr₁def
    obtain ⟨hr₁I, hr₁O⟩ := Finset.mem_filter.mp hr₁
    rw [Finset.mem_Icc] at hr₁I
    have huE : (r₁ - 1, r₁ - 1 + content x) ∈ ω.E := by
      have hz : (r₁, r₁ + content x) ∈ ω.E := (mem_middle.mp hr₁O).1
      rw [hw'c] at hw'E
      exact hsk.mem hw'E hz (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    have huW : (r₁ - 1, r₁ - 1 + content x) ∈ ω.W := by
      by_contra hnW
      have hO : (r₁ - 1, r₁ - 1 + content x) ∈ ω.middle :=
        mem_middle.mpr ⟨huE, hnW, hupper _ (by rw [hcc]; omega)⟩
      by_cases hρ1 : w'.1 + 1 ≤ r₁ - 1
      · have := hr₁le (r₁ - 1) (Finset.mem_filter.mpr
          ⟨Finset.mem_Icc.mpr ⟨hρ1, by omega⟩, hO⟩)
        omega
      · have : r₁ - 1 = w'.1 := by omega
        rw [this, ← hw'c] at hO
        exact hw'O hO
    have hzz : (r₁ + 1, r₁ + 1 + content x) ∈ ω.middle :=
      hiv r₁ y₁.1 hr₁O (by rw [← hcell _ hc₂]; exact hy₁) (r₁ + 1) (by omega) (by omega)
    refine h.not_se_config hW (z := (r₁, r₁ + content x)) hr₁O (by rw [hpe]; exact hzz)
      (by rw [hpm]; exact huW) (by rw [hcc]; omega) ?_
    intro a ha b hb hca hcb
    exact hthin a ha b hb (by rw [hcc] at hca; exact hca) (by rw [hcc] at hcb; exact hcb)
  · exact hw'O (by rw [hw'c, hρ]; exact hx₁c)
  · rcases lt_trichotomy w'.1 y₁.1 with hρ' | hρ' | hρ'
    · exact hw'O (by rw [hw'c]; exact hiv x₁.1 y₁.1 hx₁c hy₁c _ (by omega) (by omega))
    · exact hw'O (by rw [hw'c, hρ']; exact hy₁c)
    · -- the middle lies northwest of `W₋`
      let S := (Finset.Icc y₁.1 (w'.1 - 1)).filter (fun r => (r, r + content x) ∈ ω.middle)
      have hSne : S.Nonempty := ⟨y₁.1, Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩, hy₁c⟩⟩
      have hr₂ := Finset.max'_mem S hSne
      have hr₂le : ∀ r ∈ S, r ≤ S.max' hSne := fun r hr => Finset.le_max' S r hr
      set r₂ := S.max' hSne with hr₂def
      obtain ⟨hr₂I, hr₂O⟩ := Finset.mem_filter.mp hr₂
      rw [Finset.mem_Icc] at hr₂I
      have huE : (r₂ + 1, r₂ + 1 + content x) ∈ ω.E := by
        have hz : (r₂, r₂ + content x) ∈ ω.E := (mem_middle.mp hr₂O).1
        rw [hw'c] at hw'E
        exact hsk.mem hz hw'E (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      have huW : (r₂ + 1, r₂ + 1 + content x) ∈ ω.W := by
        by_contra hnW
        have hO : (r₂ + 1, r₂ + 1 + content x) ∈ ω.middle :=
          mem_middle.mpr ⟨huE, hnW, hupper _ (by rw [hcc]; omega)⟩
        by_cases hρ1 : r₂ + 1 ≤ w'.1 - 1
        · have := hr₂le (r₂ + 1) (Finset.mem_filter.mpr
            ⟨Finset.mem_Icc.mpr ⟨by omega, hρ1⟩, hO⟩)
          omega
        · have : r₂ + 1 = w'.1 := by omega
          rw [this, ← hw'c] at hO
          exact hw'O hO
      have hzz : (r₂ - 1, r₂ - 1 + content x) ∈ ω.middle :=
        hiv x₁.1 r₂ hx₁c hr₂O (r₂ - 1) (by omega) (by omega)
      refine h.not_nw_config hW (a := (r₂, r₂ + content x)) hr₂O
        (by rw [hpm]; exact hzz) (by rw [hpe]; exact huW) (by rw [hcc]; omega) ?_
      intro a ha b hb hca hcb
      exact hthin a ha b hb (by rw [hcc] at hca; exact hca) (by rw [hcc] at hcb; exact hcb)

/-- **`eq:local-properties` (1), second assertion.**  The middle of a legal mark with `W₋ ≠ ∅` has
at most one cell on each marked diagonal, that is, on each content of `W₋` or of `W₊`.  The
case of `W₊` is the rotation of the case of `W₋`. -/
theorem IsLegal.middle_subsingleton (h : ω.IsLegal) (hW : ω.W.Nonempty) {x y : ℤ × ℤ}
    (hx : x ∈ ω.middle) (hy : y ∈ ω.middle) (hc : content x = content y)
    (hm : content x ≤ minContent ω.E + ω.width - 1 ∨ minContent ω.E + ω.period ≤ content x) :
    x = y := by
  have hnon := h.isNonemptyMark hW
  have hEc := h.1.1
  have hEne : ω.E.Nonempty := hEc.2.1
  rcases hm with hm | hm
  · have hx0 := minContent_le (content_mem_contents (mem_middle.mp hx).1)
    exact h.thin_lower hW (content x - minContent ω.E).toNat x hx y hy (by omega) hc.symm
      (by omega)
  · have hmax := hnon.maxContent_E hEc
    have hx1 := le_maxContent (content_mem_contents (mem_middle.mp hx).1)
    have hrot : (-x) ∈ ω.rotate.middle := by rw [middle_rotate, mem_rotate, neg_neg]; exact hx
    have hroty : (-y) ∈ ω.rotate.middle := by rw [middle_rotate, mem_rotate, neg_neg]; exact hy
    have hm' : minContent ω.rotate.E = -maxContent ω.E := minContent_rotate hEne
    have hcx : content (-x) = -content x := by simp only [content, Prod.fst_neg, Prod.snd_neg]; ring
    have hcy : content (-y) = -content y := by simp only [content, Prod.fst_neg, Prod.snd_neg]; ring
    have := (isLegal_rotate h).thin_lower (rotate_W_nonempty hW)
      (maxContent ω.E - content x).toNat (-x) hrot (-y) hroty
      (by rw [hm', hcx]; omega) (by rw [hcx, hcy, hc]) (by rw [width_rotate]; omega)
    exact neg_injective this

end MarkedInner

end SkewGluing
