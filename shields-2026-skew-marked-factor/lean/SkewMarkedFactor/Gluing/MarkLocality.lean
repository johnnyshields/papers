/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
-- TODO-COPIED: skew-gluing/lean/SkewGluing/MarkLocality.lean
import SkewMarkedFactor.Gluing.Composition

/-!
# Window locality of legal marks, and the structure of equal-period marks

Formalizes `shields-2026-skew-gluing.tex`, «Local common-factor gluing» (`sec:gluing`),
`lem:gluing-mark-locality` with the sharpness remark after it, and the width-zero and the
structural parts of `lem:gluing-equal`.

* `glueAt`, `isConnectedSkew_glueAt`: gluing two connected skew diagrams along a common
  diagonal (the diagonal criterion on a union of overlapping windows).
* `MarkedInner.IsLegal.middle_connected`: the middle of a legal mark is connected skew.
* `MarkWindows`, `LocalMark`, `mark_locality`, `mark_locality_exists`,
  `mark_locality_middle_hatMark`: `lem:gluing-mark-locality`, in full: legality of the mark
  `(E, W₋, v, case)` transfers to `(E', W₋, v + τ, case)` and back, and the middles are connected
  skew with the same hatted mark.
* `sharpRow`, `sharpHook`, `sharpRowMark`, `sharpHookMark`: the sharpness remark, the row `(3)`
  and the hook `(2, 1)` (`decide` examples).
* `vV`, `compose_emptyMarks_antitranspose`: the two edge displacements differ by `e`, and the
  two empty-overlap readings compose to the same cells (`eq:gluing-gauge`).
* `MarkedInner.IsLegal.displacement_adjacent`, `MarkedInner.exists_displacement_pair`,
  `MarkedInner.IsLegal.double_cases`, `MarkedInner.IsLegal.not_isMixed_of_ne`,
  `MarkedInner.IsLegal.eq_of_isMixed`, `MarkedInner.IsLegal.eq_of_displacement`: at positive
  width the displacements of legal marks of a given width are at most two and differ by `e`,
  a double is ordinary with cases (a) and (b), and maximality fixes the mark at each
  displacement.

The structural part uses the assertion of `lem:gluing-local` (1) that the middle has at most one
cell on each marked diagonal; it is proved here as `MarkedInner.IsLegal.middle_subsingleton`
(by strong induction on the diagonal, using condition IV, with the case of `W₊` obtained by
rotation), so the module does not depend on the proof of `lem:gluing-local`.

Sorry-free.
-/

set_option linter.style.longFile 2200

namespace SkewMarkedFactor.Gluing

/-! ### Gluing two connected skew diagrams along a diagonal -/

/-- The diagram that agrees with `A` on the contents `≤ m` and with `B` on the contents
`≥ m`. -/
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
overlapping diagonal windows, as in the proof of `lem:gluing-mark-locality`.) -/
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
`lem:gluing-mark-locality` for a single mark, used with the window comparison): III makes the
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

/-! ### The hypotheses of `lem:gluing-mark-locality` -/

/-- The hypotheses of `lem:gluing-mark-locality` on the pair `E`, `E'`: southwest-normalized
connected diagrams of span `N`, the width `w ≥ 1` with `2w < N`, the same cells on the contents
`[0, w]`, and `E'` equal to `E + τ` on the contents `[N - w - 1, N - 1]`, where `c(τ) = 0`. -/
structure MarkWindows (E E' : Diagram) (τ : ℤ × ℤ) (N w : ℕ) : Prop where
  conn : IsConnectedSkew E
  conn' : IsConnectedSkew E'
  sw_eq : sw E = (0, 0)
  sw_eq' : sw E' = (0, 0)
  span_eq : span E = N
  span_eq' : span E' = N
  one_le : 1 ≤ w
  two_mul_lt : 2 * w < N
  lower : ∀ x, 0 ≤ content x → content x ≤ w → (x ∈ E ↔ x ∈ E')
  upper : ∀ x, (N : ℤ) - w - 1 ≤ content x → content x ≤ N - 1 →
    (x ∈ E' ↔ x ∈ translate τ E)
  content_tau : content τ = 0

/-- The data of a candidate mark in `lem:gluing-mark-locality`: `W₋ ⊆ E` on the contents
`[0, w - 1]`, and a translation `v` of content `N - w`. -/
structure LocalMark (E : Diagram) (N w : ℕ) (W : Diagram) (v : ℤ × ℤ) : Prop where
  subset : W ⊆ E
  content_mem : ∀ x ∈ W, 0 ≤ content x ∧ content x ≤ (w : ℤ) - 1
  content_v : content v = (N : ℤ) - w

theorem range_of_sw {D : Diagram} {N : ℕ} (h : IsConnectedSkew D) (hs : sw D = (0, 0))
    (hN : span D = N) :
    (∀ x ∈ D, 0 ≤ content x ∧ content x ≤ (N : ℤ) - 1) ∧
      (∀ k : ℤ, 0 ≤ k → k ≤ (N : ℤ) - 1 → ∃ x ∈ D, content x = k) := by
  have hne : D.Nonempty := h.2.1
  have hmin : minContent D = 0 := by
    have := content_sw hne
    rw [hs] at this
    simpa [content] using this.symm
  have hspan := span_eq_of_isConnectedSkew h
  rw [hN, hmin] at hspan
  have hmax : maxContent D = (N : ℤ) - 1 := by omega
  have h' := isConnectedSkew_iff_diagonal.mp h
  refine ⟨fun x hx => ?_, fun k hk0 hk1 => ?_⟩
  · have h1 := minContent_le (content_mem_contents hx)
    have h2 := le_maxContent (content_mem_contents hx)
    omega
  · have : k ∈ contents D := h'.mem_contents_iff.mpr ⟨by omega, by omega⟩
    obtain ⟨i, hi⟩ := mem_contents_iff.mp this
    exact ⟨_, hi, by simp [content]⟩

namespace MarkWindows

variable {E E' : Diagram} {τ : ℤ × ℤ} {N w : ℕ}

theorem range (M : MarkWindows E E' τ N w) :
    ∀ x ∈ E, 0 ≤ content x ∧ content x ≤ (N : ℤ) - 1 :=
  (range_of_sw M.conn M.sw_eq M.span_eq).1

theorem range' (M : MarkWindows E E' τ N w) :
    ∀ x ∈ E', 0 ≤ content x ∧ content x ≤ (N : ℤ) - 1 :=
  (range_of_sw M.conn' M.sw_eq' M.span_eq').1

theorem exists_cell (M : MarkWindows E E' τ N w) {k : ℤ} (h0 : 0 ≤ k) (h1 : k ≤ (N : ℤ) - 1) :
    ∃ x ∈ E, content x = k :=
  (range_of_sw M.conn M.sw_eq M.span_eq).2 k h0 h1

theorem exists_cell' (M : MarkWindows E E' τ N w) {k : ℤ} (h0 : 0 ≤ k) (h1 : k ≤ (N : ℤ) - 1) :
    ∃ x ∈ E', content x = k :=
  (range_of_sw M.conn' M.sw_eq' M.span_eq').2 k h0 h1

/-- The agreement on the lower window, for every cell of content at most `w`. -/
theorem lower_ext (M : MarkWindows E E' τ N w) {x : ℤ × ℤ} (hx : content x ≤ w) :
    x ∈ E ↔ x ∈ E' := by
  by_cases h0 : 0 ≤ content x
  · exact M.lower x h0 hx
  · constructor
    · intro h; exact absurd (M.range x h).1 h0
    · intro h; exact absurd (M.range' x h).1 h0

/-- The agreement on the upper window, for every cell of content at least `N - w - 1`. -/
theorem upper_ext (M : MarkWindows E E' τ N w) {x : ℤ × ℤ} (hx : (N : ℤ) - w - 1 ≤ content x) :
    x ∈ E' ↔ x - τ ∈ E := by
  by_cases h1 : content x ≤ (N : ℤ) - 1
  · rw [← mem_translate]; exact M.upper x hx h1
  · have hc : content (x - τ) = content x := by
      simp only [content, Prod.fst_sub, Prod.snd_sub]
      have := M.content_tau
      simp only [content] at this
      omega
    constructor
    · intro h; exact absurd (M.range' x h).2 h1
    · intro h
      have := (M.range _ h).2
      omega

theorem ne_eq (M : MarkWindows E E' τ N w) : ne E' = ne E + τ := by
  have hE : E.Nonempty := M.conn.2.1
  have hE' : E'.Nonempty := M.conn'.2.1
  have hcN : content (ne E) = (N : ℤ) - 1 := by
    have hmin : minContent E = 0 := by
      have := content_sw hE
      rw [M.sw_eq] at this
      simpa [content] using this.symm
    have hspan := span_eq_of_isConnectedSkew M.conn
    rw [M.span_eq, hmin] at hspan
    rw [content_ne hE]; omega
  have hmem : ne E + τ ∈ E' := by
    rw [M.upper_ext (by rw [content_add, hcN, M.content_tau]; have := M.two_mul_lt; omega)]
    simpa using ne_mem hE
  have hcmax : content (ne E + τ) = maxContent E' := by
    have hmin : minContent E' = 0 := by
      have := content_sw hE'
      rw [M.sw_eq'] at this
      simpa [content] using this.symm
    have hspan := span_eq_of_isConnectedSkew M.conn'
    rw [M.span_eq', hmin] at hspan
    rw [content_add, hcN, M.content_tau]; omega
  exact (MarkedInner.eq_ne_of_content M.conn' hmem hcmax).symm

/-- The symmetric hypotheses, with the roles of `E` and `E'` exchanged. -/
theorem symm (M : MarkWindows E E' τ N w) : MarkWindows E' E (-τ) N w where
  conn := M.conn'
  conn' := M.conn
  sw_eq := M.sw_eq'
  sw_eq' := M.sw_eq
  span_eq := M.span_eq'
  span_eq' := M.span_eq
  one_le := M.one_le
  two_mul_lt := M.two_mul_lt
  lower x h0 h1 := (M.lower x h0 h1).symm
  upper x h0 _ := by
    have hc : content (x + τ) = content x := by
      rw [content_add, M.content_tau, add_zero]
    rw [mem_translate, sub_neg_eq_add, M.upper_ext (by rw [hc]; exact h0), add_sub_cancel_right]
  content_tau := by
    have := M.content_tau
    simp only [content] at this ⊢
    simp only [Prod.fst_neg, Prod.snd_neg]
    omega

theorem content_ne_eq (M : MarkWindows E E' τ N w) : content (ne E) = (N : ℤ) - 1 := by
  have hE : E.Nonempty := M.conn.2.1
  have hmin : minContent E = 0 := by
    have := content_sw hE
    rw [M.sw_eq] at this
    simpa [content] using this.symm
  have hspan := span_eq_of_isConnectedSkew M.conn
  rw [M.span_eq, hmin] at hspan
  rw [content_ne hE]; omega

end MarkWindows

/-! ### Transport of the mark data -/

namespace LocalMark

variable {E E' : Diagram} {τ : ℤ × ℤ} {N w : ℕ} {W : Diagram} {v : ℤ × ℤ}

theorem content_upper (L : LocalMark E N w W v) {x : ℤ × ℤ} (hx : x ∈ translate v W) :
    (N : ℤ) - w ≤ content x ∧ content x ≤ (N : ℤ) - 1 := by
  have h := L.content_mem _ (mem_translate.mp hx)
  have h2 := L.content_v
  rw [MarkedInner.content_sub] at h
  omega

/-- The candidate mark of `E'` obtained by `W₋` and `v + τ`. -/
theorem shift (M : MarkWindows E E' τ N w) (L : LocalMark E N w W v) :
    LocalMark E' N w W (v + τ) where
  subset x hx := by
    rw [← M.lower_ext (by have := (L.content_mem x hx).2; omega)]
    exact L.subset hx
  content_mem := L.content_mem
  content_v := by rw [content_add, M.content_tau, add_zero]; exact L.content_v

end LocalMark

namespace MarkWindows

variable {E E' : Diagram} {τ : ℤ × ℤ} {N w : ℕ} {W : Diagram} {v : ℤ × ℤ}

theorem mem_upper_shift {x : ℤ × ℤ} : x ∈ translate (v + τ) W ↔ x - τ ∈ translate v W := by
  rw [mem_translate, mem_translate]
  have : x - (v + τ) = x - τ - v := by abel
  rw [this]

/-- The middle in the lower window: for `c(x) ≤ w`, membership in the middles of `E` and `E'`
agree. -/
theorem mem_middle_low (M : MarkWindows E E' τ N w) (L : LocalMark E N w W v) {x : ℤ × ℤ}
    (hx : content x ≤ w) :
    x ∈ E \ (W ∪ translate v W) ↔ x ∈ E' \ (W ∪ translate (v + τ) W) := by
  have hN := M.two_mul_lt
  have h1 : x ∉ translate v W := fun h => by have := L.content_upper h; omega
  have h2 : x ∉ translate (v + τ) W := fun h => by
    have := (L.shift M).content_upper h; omega
  simp only [Finset.mem_sdiff, Finset.mem_union, h1, h2, or_false]
  rw [M.lower_ext hx]

/-- The middle in the upper window: for `c(x) ≥ N - w - 1`, membership in the middle of `E'`
is membership of `x - τ` in the middle of `E`. -/
theorem mem_middle_high (M : MarkWindows E E' τ N w) (L : LocalMark E N w W v) {x : ℤ × ℤ}
    (hx : (N : ℤ) - w - 1 ≤ content x) :
    x ∈ E' \ (W ∪ translate (v + τ) W) ↔ x - τ ∈ E \ (W ∪ translate v W) := by
  have hN := M.two_mul_lt
  have hc : content (x - τ) = content x := by
    rw [MarkedInner.content_sub, M.content_tau, sub_zero]
  have h1 : x ∉ W := fun h => by have := (L.content_mem x h).2; omega
  have h2 : x - τ ∉ W := fun h => by have := (L.content_mem _ h).2; omega
  simp only [Finset.mem_sdiff, Finset.mem_union, h1, h2, false_or, mem_upper_shift]
  rw [M.upper_ext hx]

end MarkWindows

/-! ### Extreme contents of the middle and the attachments -/

theorem minContent_eq_of_agree {O O' : Diagram} {k₀ : ℤ} (hO : ∃ x ∈ O, content x = k₀)
    (hag : ∀ x, content x ≤ k₀ → (x ∈ O ↔ x ∈ O')) : minContent O = minContent O' := by
  obtain ⟨x₀, hx₀, hc₀⟩ := hO
  have hx₀' : x₀ ∈ O' := (hag x₀ hc₀.le).mp hx₀
  obtain ⟨z, hz, hzc⟩ := exists_cell_of_mem_contents (minContent_mem ⟨x₀, hx₀⟩)
  obtain ⟨z', hz', hzc'⟩ := exists_cell_of_mem_contents (minContent_mem ⟨x₀, hx₀'⟩)
  have h1 : minContent O ≤ content x₀ := minContent_le (content_mem_contents hx₀)
  have h2 : minContent O' ≤ content x₀ := minContent_le (content_mem_contents hx₀')
  have h3 : minContent O' ≤ content z := minContent_le
    (content_mem_contents ((hag z (by omega)).mp hz))
  have h4 : minContent O ≤ content z' := minContent_le
    (content_mem_contents ((hag z' (by omega)).mpr hz'))
  omega

theorem maxContent_eq_of_shift {O O' : Diagram} {τ : ℤ × ℤ} (hτ : content τ = 0) {k₀ : ℤ}
    (hO : ∃ x ∈ O, content x = k₀)
    (hag : ∀ x, k₀ ≤ content x → (x ∈ O' ↔ x - τ ∈ O)) : maxContent O' = maxContent O := by
  obtain ⟨x₀, hx₀, hc₀⟩ := hO
  have hcs : ∀ x, content (x - τ) = content x := fun x => by
    rw [MarkedInner.content_sub, hτ, sub_zero]
  have hx₀' : x₀ + τ ∈ O' := by
    rw [hag _ (by rw [content_add, hτ]; omega), add_sub_cancel_right]; exact hx₀
  obtain ⟨z, hz, hzc⟩ := exists_cell_of_mem_contents (maxContent_mem ⟨x₀, hx₀⟩)
  obtain ⟨z', hz', hzc'⟩ := exists_cell_of_mem_contents (maxContent_mem ⟨x₀ + τ, hx₀'⟩)
  have h1 : content x₀ ≤ maxContent O := le_maxContent (content_mem_contents hx₀)
  have h2 : content (x₀ + τ) ≤ maxContent O' := le_maxContent (content_mem_contents hx₀')
  rw [content_add, hτ] at h2
  have hzτ : z + τ ∈ O' := by
    rw [hag _ (by rw [content_add, hτ]; omega), add_sub_cancel_right]; exact hz
  have h3 : content z ≤ maxContent O' := by
    have := le_maxContent (content_mem_contents hzτ)
    rwa [content_add, hτ, add_zero] at this
  have h4 : content z' ≤ maxContent O := by
    have := le_maxContent (content_mem_contents ((hag z' (by omega)).mp hz'))
    rwa [hcs] at this
  omega

namespace MarkWindows

variable {E E' : Diagram} {τ : ℤ × ℤ} {N w : ℕ} {W : Diagram} {v : ℤ × ℤ}

/-- The middle of `E` has a cell on the content `w`. -/
theorem exists_middle_cell (M : MarkWindows E E' τ N w) (L : LocalMark E N w W v) {k : ℤ}
    (hk0 : (w : ℤ) ≤ k) (hk1 : k ≤ (N : ℤ) - w - 1) :
    ∃ x ∈ E \ (W ∪ translate v W), content x = k := by
  have hN := M.two_mul_lt
  obtain ⟨x, hx, hc⟩ := M.exists_cell (k := k) (by omega) (by omega)
  refine ⟨x, ?_, hc⟩
  simp only [Finset.mem_sdiff, Finset.mem_union, not_or]
  refine ⟨hx, fun h => ?_, fun h => ?_⟩
  · have := (L.content_mem x h).2; omega
  · have := L.content_upper h; omega

theorem minContent_middle (M : MarkWindows E E' τ N w) (L : LocalMark E N w W v) :
    minContent (E \ (W ∪ translate v W)) = minContent (E' \ (W ∪ translate (v + τ) W)) := by
  have hN := M.two_mul_lt
  exact minContent_eq_of_agree (k₀ := w) (M.exists_middle_cell L le_rfl (by omega))
    (fun x hx => M.mem_middle_low L hx)

theorem maxContent_middle (M : MarkWindows E E' τ N w) (L : LocalMark E N w W v) :
    maxContent (E' \ (W ∪ translate (v + τ) W)) = maxContent (E \ (W ∪ translate v W)) := by
  have hN := M.two_mul_lt
  exact maxContent_eq_of_shift M.content_tau (k₀ := (N : ℤ) - w - 1)
    (M.exists_middle_cell L (by omega) le_rfl)
    (fun x hx => M.mem_middle_high L hx)

theorem le_minContent_middle (M : MarkWindows E E' τ N w) (L : LocalMark E N w W v) :
    minContent (E \ (W ∪ translate v W)) ≤ w := by
  have hN := M.two_mul_lt
  obtain ⟨x, hx, hc⟩ := M.exists_middle_cell L (k := w) le_rfl (by omega)
  have := minContent_le (content_mem_contents hx)
  omega

theorem le_maxContent_middle (M : MarkWindows E E' τ N w) (L : LocalMark E N w W v) :
    (N : ℤ) - w - 1 ≤ maxContent (E \ (W ∪ translate v W)) := by
  have hN := M.two_mul_lt
  obtain ⟨x, hx, hc⟩ := M.exists_middle_cell L (k := (N : ℤ) - w - 1) (by omega) le_rfl
  have := le_maxContent (content_mem_contents hx)
  omega

/-- A condition read at the southwest cell of the middle transfers from `E` to `E'`. -/
theorem exists_min_transfer (M : MarkWindows E E' τ N w) (L : LocalMark E N w W v)
    (P : ℤ × ℤ → Prop) :
    (∃ x ∈ E \ (W ∪ translate v W), content x = minContent (E \ (W ∪ translate v W)) ∧ P x) ↔
      ∃ x ∈ E' \ (W ∪ translate (v + τ) W),
        content x = minContent (E' \ (W ∪ translate (v + τ) W)) ∧ P x := by
  have hm := M.minContent_middle L
  have hle := M.le_minContent_middle L
  constructor
  · rintro ⟨x, hx, hc, hP⟩
    exact ⟨x, (M.mem_middle_low L (by omega)).mp hx, by omega, hP⟩
  · rintro ⟨x, hx, hc, hP⟩
    exact ⟨x, (M.mem_middle_low L (by omega)).mpr hx, by omega, hP⟩

/-- A condition read at the northeast cell of the middle transfers from `E` to `E'`, with the
cell moved by `τ`. -/
theorem exists_max_transfer (M : MarkWindows E E' τ N w) (L : LocalMark E N w W v)
    (P P' : ℤ × ℤ → Prop) (hP : ∀ y, P' y ↔ P (y - τ)) :
    (∃ x ∈ E \ (W ∪ translate v W), content x = maxContent (E \ (W ∪ translate v W)) ∧ P x) ↔
      ∃ x ∈ E' \ (W ∪ translate (v + τ) W),
        content x = maxContent (E' \ (W ∪ translate (v + τ) W)) ∧ P' x := by
  have hm := M.maxContent_middle L
  have hle := M.le_maxContent_middle L
  have hcs : ∀ x, content (x - τ) = content x := fun x => by
    rw [MarkedInner.content_sub, M.content_tau, sub_zero]
  constructor
  · rintro ⟨x, hx, hc, hPx⟩
    refine ⟨x + τ, ?_, ?_, ?_⟩
    · rw [M.mem_middle_high L (by rw [content_add, M.content_tau]; omega),
        add_sub_cancel_right]
      exact hx
    · rw [content_add, M.content_tau]; omega
    · rw [hP, add_sub_cancel_right]; exact hPx
  · rintro ⟨y, hy, hc, hPy⟩
    refine ⟨y - τ, ?_, ?_, (hP y).mp hPy⟩
    · exact (M.mem_middle_high L (by omega)).mp hy
    · rw [hcs]; omega

end MarkWindows

namespace MarkWindows

variable {E E' : Diagram} {τ : ℤ × ℤ} {N w : ℕ} {W : Diagram} {v : ℤ × ℤ}
  {cs : AttachCase}

theorem lowerH_iff (M : MarkWindows E E' τ N w) (L : LocalMark E N w W v) :
    (MarkedInner.mk E W v cs).LowerH ↔ (MarkedInner.mk E' W (v + τ) cs).LowerH :=
  M.exists_min_transfer L (fun x => (x.1, x.2 - 1) ∈ W)

theorem lowerV_iff (M : MarkWindows E E' τ N w) (L : LocalMark E N w W v) :
    (MarkedInner.mk E W v cs).LowerV ↔ (MarkedInner.mk E' W (v + τ) cs).LowerV :=
  M.exists_min_transfer L (fun x => (x.1 + 1, x.2) ∈ W)

theorem upperH_iff (M : MarkWindows E E' τ N w) (L : LocalMark E N w W v) :
    (MarkedInner.mk E W v cs).UpperH ↔ (MarkedInner.mk E' W (v + τ) cs).UpperH := by
  refine M.exists_max_transfer L (fun x => (x.1, x.2 + 1) ∈ translate v W)
    (fun x => (x.1, x.2 + 1) ∈ translate (v + τ) W) (fun y => ?_)
  rw [mem_translate, mem_translate]
  have : (y.1, y.2 + 1) - (v + τ) = ((y - τ).1, (y - τ).2 + 1) - v := by
    ext <;> simp <;> ring
  rw [this]

theorem upperV_iff (M : MarkWindows E E' τ N w) (L : LocalMark E N w W v) :
    (MarkedInner.mk E W v cs).UpperV ↔ (MarkedInner.mk E' W (v + τ) cs).UpperV := by
  refine M.exists_max_transfer L (fun x => (x.1 - 1, x.2) ∈ translate v W)
    (fun x => (x.1 - 1, x.2) ∈ translate (v + τ) W) (fun y => ?_)
  rw [mem_translate, mem_translate]
  have : (y.1 - 1, y.2) - (v + τ) = ((y - τ).1 - 1, (y - τ).2) - v := by
    ext <;> simp <;> ring
  rw [this]

theorem attachmentMatches_iff (M : MarkWindows E E' τ N w) (L : LocalMark E N w W v) :
    (MarkedInner.mk E W v cs).AttachmentMatches ↔
      (MarkedInner.mk E' W (v + τ) cs).AttachmentMatches := by
  unfold MarkedInner.AttachmentMatches
  rw [M.lowerH_iff L, M.lowerV_iff L, M.upperH_iff L, M.upperV_iff L]

/-- Condition I transfers from `E` to `E'`. -/
theorem isMaximal_transfer (M : MarkWindows E E' τ N w) (L : LocalMark E N w W v)
    (h : (MarkedInner.mk E W v cs).IsMaximal) :
    (MarkedInner.mk E' W (v + τ) cs).IsMaximal := by
  intro W' hW' hlt hsk hc x hx hsub
  have hN := M.two_mul_lt
  have hWpE' : W' ⊆ E' := Finset.mem_powerset.mp hW'
  have hcW : ∀ y ∈ W', 0 ≤ content y ∧ content y ≤ (w : ℤ) - 1 := by
    intro y hy
    have h1 : content y ∈ contents W' := content_mem_contents hy
    have h1' : content y ∈ contents W := by
      have : contents W' = contents W := hc
      rwa [this] at h1
    obtain ⟨z, hz, hzc⟩ := exists_cell_of_mem_contents h1'
    rw [← hzc]; exact L.content_mem z hz
  have hWpE : W' ∈ E.powerset := by
    rw [Finset.mem_powerset]
    intro y hy
    rw [M.lower_ext (by have := (hcW y hy).2; omega)]
    exact hWpE' hy
  refine h W' hWpE hlt hsk hc x hx ?_
  intro z hz
  have hz' : z - (ne E - x) ∈ W' := mem_translate.mp hz
  have hzE' : z + τ ∈ E' := by
    apply hsub
    rw [mem_translate, M.ne_eq]
    have : z + τ - (ne E + τ - x) = z - (ne E - x) := by abel
    rw [this]; exact hz'
  have hcz : content z = content (z - (ne E - x)) + (content (ne E) - content x) := by
    have : z = (z - (ne E - x)) + (ne E - x) := by abel
    conv_lhs => rw [this]
    rw [content_add, MarkedInner.content_sub, MarkedInner.content_sub (ne E) x]
  have h1 := hcW _ hz'
  have h2 := hcW x hx
  have h3 := M.content_ne_eq
  have := (M.upper_ext (x := z + τ) (by rw [content_add, M.content_tau]; omega)).mp hzE'
  rwa [add_sub_cancel_right] at this

/-- Condition III transfers from `E` to `E'`: the removals are read in windows. -/
theorem removalsConnected_transfer (M : MarkWindows E E' τ N w) (L : LocalMark E N w W v)
    (h : (MarkedInner.mk E W v cs).RemovalsConnected) :
    (MarkedInner.mk E' W (v + τ) cs).RemovalsConnected := by
  obtain ⟨h1, h2⟩ := h
  have hN := M.two_mul_lt
  have hW1 : IsConnectedSkew (E \ W) := h1
  have hW2 : IsConnectedSkew (E \ translate v W) := h2
  have hcs : ∀ x, content (x - τ) = content x := fun x => by
    rw [MarkedInner.content_sub, M.content_tau, sub_zero]
  constructor
  · change IsConnectedSkew (E' \ W)
    have hag : ∀ x, content x = w → (x ∈ E \ W ↔ x ∈ E') := by
      intro x hx
      have : x ∉ W := fun h => by have := (L.content_mem x h).2; omega
      simp only [Finset.mem_sdiff, this, not_false_eq_true, and_true]
      exact M.lower_ext (by omega)
    have heq : E' \ W = glueAt (E \ W) E' w := by
      ext x
      rw [mem_glueAt, Finset.mem_sdiff, Finset.mem_sdiff]
      have f1 : content x ≤ w → (x ∈ E ↔ x ∈ E') := fun hx => M.lower_ext hx
      have f2 : (w : ℤ) ≤ content x → x ∉ W := fun hx h => by
        have := (L.content_mem x h).2; omega
      have f3 : content x ≤ w ∨ (w : ℤ) ≤ content x := by omega
      tauto
    rw [heq]
    obtain ⟨x, hx, hc⟩ := M.exists_cell (k := w) (by omega) (by omega)
    have hxm : x ∈ E \ W := by
      rw [Finset.mem_sdiff]
      exact ⟨hx, fun h => by have := (L.content_mem x h).2; omega⟩
    refine isConnectedSkew_glueAt hW1 M.conn' ?_ ?_ hag
    · rw [← hc]; exact content_mem_contents hxm
    · rw [← hc]; exact content_mem_contents ((M.lower_ext (by omega)).mp hx)
  · change IsConnectedSkew (E' \ translate (v + τ) W)
    have hT : ∀ x, x ∈ translate τ (E \ translate v W) ↔ x - τ ∈ E ∧ x - τ ∉ translate v W :=
      fun x => by rw [mem_translate, Finset.mem_sdiff]
    have hag : ∀ x, content x = (N : ℤ) - w - 1 →
        (x ∈ E' ↔ x ∈ translate τ (E \ translate v W)) := by
      intro x hx
      have hxu : x - τ ∉ translate v W := fun h => by
        have := L.content_upper h; rw [hcs] at this; omega
      rw [hT, M.upper_ext (by omega)]
      simp only [hxu, not_false_eq_true, and_true]
    have heq : E' \ translate (v + τ) W =
        glueAt E' (translate τ (E \ translate v W)) ((N : ℤ) - w - 1) := by
      ext x
      rw [mem_glueAt, Finset.mem_sdiff, mem_upper_shift, hT]
      have f1 : content x ≤ (N : ℤ) - w - 1 → x - τ ∉ translate v W := fun hx h => by
        have := L.content_upper h; rw [hcs] at this; omega
      have f2 : (N : ℤ) - w - 1 ≤ content x → (x ∈ E' ↔ x - τ ∈ E) := fun hx =>
        M.upper_ext hx
      have f3 : content x ≤ (N : ℤ) - w - 1 ∨ (N : ℤ) - w - 1 ≤ content x := by omega
      tauto
    rw [heq]
    obtain ⟨x, hx, hc⟩ := M.exists_cell (k := (N : ℤ) - w - 1) (by omega) (by omega)
    have hxm : x ∈ E \ translate v W := by
      rw [Finset.mem_sdiff]
      exact ⟨hx, fun h => by have := L.content_upper h; omega⟩
    refine isConnectedSkew_glueAt M.conn' (isConnectedSkew_translate τ hW2) ?_ ?_ hag
    · obtain ⟨y, hy, hyc⟩ := M.exists_cell' (k := (N : ℤ) - w - 1) (by omega) (by omega)
      rw [← hyc]; exact content_mem_contents hy
    · rw [mem_contents_translate, M.content_tau, sub_zero, ← hc]
      exact content_mem_contents hxm

/-- The empty mark is excluded: its displacement has content `N`, not `N - w` with `w ≥ 1`. -/
theorem not_isEmptyMark (M : MarkWindows E E' τ N w) (L : LocalMark E N w W v) :
    ¬ (MarkedInner.mk E W v cs).IsEmptyMark := by
  rintro ⟨-, h2, -⟩
  have h2' : v = vH E := h2
  have hv := L.content_v
  have hN := M.one_le
  have h3 := M.content_ne_eq
  rw [h2'] at hv
  unfold vH at hv
  rw [M.sw_eq] at hv
  simp only [content, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add] at hv h3
  omega

/-- Well-formedness transfers from `E` to `E'`. -/
theorem isWellFormed_transfer (M : MarkWindows E E' τ N w) (L : LocalMark E N w W v)
    (h : (MarkedInner.mk E W v cs).IsWellFormed) :
    (MarkedInner.mk E' W (v + τ) cs).IsWellFormed := by
  obtain ⟨-, hm⟩ := h
  rcases hm with hemp | ⟨hne, hW, -, hUE, hsw, hneU, hatt⟩
  · exact absurd hemp (M.not_isEmptyMark L)
  · refine ⟨M.conn', Or.inr ⟨hne, hW, (L.shift M).subset, ?_, ?_, ?_,
      (M.attachmentMatches_iff L).mp hatt⟩⟩
    · intro y hy
      have hy' : y - τ ∈ translate v W := mem_upper_shift.mp hy
      have hc := L.content_upper hy'
      have hcs : content (y - τ) = content y := by
        rw [MarkedInner.content_sub, M.content_tau, sub_zero]
      exact (M.upper_ext (by omega)).mpr (hUE hy')
    · change sw E' ∈ W
      rw [M.sw_eq', ← M.sw_eq]; exact hsw
    · change ne E' ∈ translate (v + τ) W
      rw [M.ne_eq, mem_upper_shift, add_sub_cancel_right]; exact hneU

/-- Condition II transfers from `E` to `E'`. -/
theorem isNarrow_transfer (M : MarkWindows E E' τ N w)
    (h : (MarkedInner.mk E W v cs).IsNarrow) : (MarkedInner.mk E' W (v + τ) cs).IsNarrow := by
  unfold MarkedInner.IsNarrow MarkedInner.width MarkedInner.period at h ⊢
  simp only at h ⊢
  rw [content_add, M.content_tau, add_zero]
  exact h

theorem content_sub_tau (M : MarkWindows E E' τ N w) (x : ℤ × ℤ) :
    content (x - τ) = content x := by
  rw [MarkedInner.content_sub, M.content_tau, sub_zero]

/-- Near the marked contents `[0, w - 1]`, the finite windows `E ∪ (E - v)` and
`E' ∪ (E' - (v + τ))` have the same cells. -/
theorem mem_windowCells_iff (M : MarkWindows E E' τ N w) (L : LocalMark E N w W v)
    {z : ℤ × ℤ} (h0 : 0 ≤ content z) (h1 : content z ≤ (w : ℤ) - 1) :
    z ∈ (MarkedInner.mk E W v cs).windowCells ↔
      z ∈ (MarkedInner.mk E' W (v + τ) cs).windowCells := by
  have hN := M.two_mul_lt
  have hv := L.content_v
  unfold MarkedInner.windowCells
  simp only [Finset.mem_union, mem_translate]
  have e1 : z - -(v + τ) = (z + v) + τ := by abel
  have e2 : z - -v = z + v := by abel
  have hc : content (z + v) = content z + (N - w) := by rw [content_add, hv]
  rw [e1, e2, M.lower_ext (by omega : content z ≤ w),
    M.upper_ext (x := z + v + τ) (by rw [content_add, hc, M.content_tau]; omega),
    add_sub_cancel_right]

theorem hatMarkWindow_eq (M : MarkWindows E E' τ N w) (L : LocalMark E N w W v) :
    (MarkedInner.mk E' W (v + τ) cs).hatMarkWindow = (MarkedInner.mk E W v cs).hatMarkWindow := by
  ext y
  unfold MarkedInner.hatMarkWindow
  simp only [Finset.mem_union, Finset.mem_filter]
  have hc : content (y + eCell) = content y := MarkedInner.content_eCell_add y
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · have := L.content_mem _ h2
      exact Or.inl ⟨(M.mem_windowCells_iff L (by omega) (by omega)).mpr h1, h2⟩
    · have := L.content_mem _ h1
      exact Or.inr ⟨h1, (M.mem_windowCells_iff L (by omega) (by omega)).mpr h2⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · have := L.content_mem _ h2
      exact Or.inl ⟨(M.mem_windowCells_iff L (by omega) (by omega)).mp h1, h2⟩
    · have := L.content_mem _ h1
      exact Or.inr ⟨h1, (M.mem_windowCells_iff L (by omega) (by omega)).mp h2⟩

/-- Cells of the middle copies `O + k v` with `k ∈ {-1, 0}`, read near the marked contents. -/
theorem mem_middle_copy_iff (M : MarkWindows E E' τ N w) (L : LocalMark E N w W v)
    {k : ℤ} (hk : k ∈ ({-1, 0} : Finset ℤ)) {z : ℤ × ℤ}
    (h0 : -1 ≤ content z) (h1 : content z ≤ w) :
    z ∈ translate (k • (v + τ)) (MarkedInner.mk E' W (v + τ) cs).middle ↔
      z ∈ translate (k • v) (MarkedInner.mk E W v cs).middle := by
  have hN := M.two_mul_lt
  have hv := L.content_v
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl
  · simp only [neg_smul, one_smul, mem_translate]
    change z - -(v + τ) ∈ E' \ (W ∪ translate (v + τ) W) ↔ z - -v ∈ E \ (W ∪ translate v W)
    have e1 : z - -(v + τ) = (z + v) + τ := by abel
    have e2 : z - -v = z + v := by abel
    have hc : content (z + v) = content z + (N - w) := by rw [content_add, hv]
    rw [e1, e2, M.mem_middle_high L (by rw [content_add, hc, M.content_tau]; omega),
      add_sub_cancel_right]
  · simp only [zero_smul, translate_zero]
    exact (M.mem_middle_low L h1).symm

theorem hatWindowClear_transfer (M : MarkWindows E E' τ N w) (L : LocalMark E N w W v)
    (h : (MarkedInner.mk E W v cs).HatWindowClear) :
    (MarkedInner.mk E' W (v + τ) cs).HatWindowClear := by
  intro k hk x hx y hy hadj
  rw [M.hatMarkWindow_eq L] at hy
  have hyc : 0 ≤ content y ∧ content y ≤ (w : ℤ) - 1 := by
    unfold MarkedInner.hatMarkWindow at hy
    simp only [Finset.mem_union, Finset.mem_filter] at hy
    have hc : content (y + eCell) = content y := MarkedInner.content_eCell_add y
    rcases hy with ⟨-, h2⟩ | ⟨h1, -⟩
    · have := L.content_mem _ h2; omega
    · exact L.content_mem _ h1
  have hxc := content_adj hadj
  rw [Finset.mem_filter] at hx
  have hc : content (x + eCell) = content x := MarkedInner.content_eCell_add x
  refine h k hk x ?_ y hy hadj
  rw [Finset.mem_filter]
  exact ⟨(M.mem_middle_copy_iff L hk (by omega) (by omega)).mp hx.1,
    (M.mem_middle_copy_iff L hk (by omega) (by omega)).mp hx.2⟩

/-- Legality transfers from `E` to `E'`, for the same copies `W₋` and the displacement
`v + τ`. -/
theorem isLegal_transfer (M : MarkWindows E E' τ N w) (L : LocalMark E N w W v)
    (h : (MarkedInner.mk E W v cs).IsLegal) : (MarkedInner.mk E' W (v + τ) cs).IsLegal := by
  obtain ⟨hwf, hI, hII, hIII, hIV⟩ := h
  have hwf' := M.isWellFormed_transfer L hwf
  have hII' := M.isNarrow_transfer hII
  refine ⟨hwf', M.isMaximal_transfer L hI, hII', M.removalsConnected_transfer L hIII, ?_⟩
  exact (MarkedInner.noHatAdjacency_iff_window hwf' hII').mpr
    (M.hatWindowClear_transfer L ((MarkedInner.noHatAdjacency_iff_window hwf hII).mp hIV))

/-- The periodic union `𝐄` meets the marked contents `[0, w - 1]` in the same cells for the two
marks. -/
theorem mem_periodicUnion_iff (M : MarkWindows E E' τ N w) (L : LocalMark E N w W v)
    {z : ℤ × ℤ} (h0 : 0 ≤ content z) (h1 : content z ≤ (w : ℤ) - 1) :
    z ∈ (MarkedInner.mk E W v cs).periodicUnion ↔
      z ∈ (MarkedInner.mk E' W (v + τ) cs).periodicUnion := by
  have hN := M.two_mul_lt
  have hv := L.content_v
  simp only [MarkedInner.periodicUnion, Set.mem_ofPred_eq]
  have hcv : ∀ k : ℤ, content (z - k • v) = content z - k * ((N : ℤ) - w) := fun k => by
    rw [MarkedInner.content_sub, MarkedInner.content_smul, hv]
  have hcv' : ∀ k : ℤ, content (z - k • (v + τ)) = content z - k * ((N : ℤ) - w) := fun k => by
    rw [MarkedInner.content_sub, MarkedInner.content_smul, content_add, M.content_tau, hv,
      add_zero]
  have idx : ∀ k : ℤ, (z - k • v ∈ E ∨ z - k • (v + τ) ∈ E') → -1 ≤ k ∧ k ≤ 0 := by
    intro k hk
    have hr : 0 ≤ content z - k * ((N : ℤ) - w) ∧
        content z - k * ((N : ℤ) - w) ≤ (N : ℤ) - 1 := by
      rcases hk with hk | hk
      · have := M.range _ hk; rw [hcv] at this; exact this
      · have := M.range' _ hk; rw [hcv'] at this; exact this
    exact MarkedInner.periodic_index (c0 := 0) (q := (N : ℤ) - w) (w := w) (yc := content z)
      (j := k) (by omega) (by omega) h0 (by omega) (by omega) (by omega)
  have hcz : content (z + v) = content z + ((N : ℤ) - w) := by rw [content_add, hv]
  have hlow : content z ≤ w := by omega
  constructor
  · rintro ⟨k, hk⟩
    have hk' := idx k (Or.inl hk)
    have : k = -1 ∨ k = 0 := by omega
    rcases this with rfl | rfl
    · refine ⟨-1, ?_⟩
      simp only [neg_smul, one_smul, sub_neg_eq_add] at hk ⊢
      rw [← add_assoc]
      exact (M.upper_ext (by rw [content_add, hcz, M.content_tau]; omega)).mpr
        (by rwa [add_sub_cancel_right])
    · refine ⟨0, ?_⟩
      simp only [zero_smul, sub_zero] at hk ⊢
      exact (M.lower_ext hlow).mp hk
  · rintro ⟨k, hk⟩
    have hk' := idx k (Or.inr hk)
    have : k = -1 ∨ k = 0 := by omega
    rcases this with rfl | rfl
    · refine ⟨-1, ?_⟩
      simp only [neg_smul, one_smul, sub_neg_eq_add] at hk ⊢
      rw [← add_assoc] at hk
      have := (M.upper_ext (by rw [content_add, hcz, M.content_tau]; omega)).mp hk
      rwa [add_sub_cancel_right] at this
    · refine ⟨0, ?_⟩
      simp only [zero_smul, sub_zero] at hk ⊢
      exact (M.lower_ext hlow).mpr hk

/-- The hatted mark `Ŵ₋` is the same for the two marks. -/
theorem hatMark_eq (M : MarkWindows E E' τ N w) (L : LocalMark E N w W v) :
    (MarkedInner.mk E' W (v + τ) cs).hatMark W = (MarkedInner.mk E W v cs).hatMark W := by
  ext y
  unfold MarkedInner.hatMark
  simp only [Set.mem_union, Set.mem_ofPred_eq]
  have hc : content (y + eCell) = content y := MarkedInner.content_eCell_add y
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · have := L.content_mem _ h2
      exact Or.inl ⟨(M.mem_periodicUnion_iff L (by omega) (by omega)).mpr h1, h2⟩
    · have := L.content_mem _ h1
      exact Or.inr ⟨h1, (M.mem_periodicUnion_iff L (by omega) (by omega)).mpr h2⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · have := L.content_mem _ h2
      exact Or.inl ⟨(M.mem_periodicUnion_iff L (by omega) (by omega)).mp h1, h2⟩
    · have := L.content_mem _ h1
      exact Or.inr ⟨h1, (M.mem_periodicUnion_iff L (by omega) (by omega)).mp h2⟩

end MarkWindows

/-! ### `lem:gluing-mark-locality` -/

/-- **`lem:gluing-mark-locality`, the equivalence.**  Let `E` and `E'` be southwest-normalized
connected diagrams of span `N`, `w ≥ 1` with `2w < N`, with the same cells on the contents
`[0, w]`, and `E'` agreeing with `E + τ` on `[N - w - 1, N - 1]`, `c(τ) = 0`.  For every
`W₋ ⊆ E` on the contents `[0, w - 1]`, every translation `v` of content `N - w`, and every
attachment case, `(W₋, W₋ + v)` are the copies of a legal mark of `E` exactly when
`(W₋, W₋ + v + τ)` are the copies of a legal mark of `E'` with the same attachment case.

**Differs from the paper's route.**  Condition III is transferred by gluing connected skew
diagrams along a diagonal (`isConnectedSkew_glueAt`) rather than by checking the clauses of the
diagonal criterion window by window, and IV is compared in its finite-window form. -/
theorem mark_locality {E E' : Diagram} {τ : ℤ × ℤ} {N w : ℕ} (M : MarkWindows E E' τ N w)
    {W : Diagram} {v : ℤ × ℤ} (L : LocalMark E N w W v) (cs : AttachCase) :
    (MarkedInner.mk E W v cs).IsLegal ↔ (MarkedInner.mk E' W (v + τ) cs).IsLegal := by
  refine ⟨M.isLegal_transfer L, fun h => ?_⟩
  have := M.symm.isLegal_transfer (L.shift M) h
  rwa [add_neg_cancel_right] at this

/-- **`lem:gluing-mark-locality`, the equivalence, without fixing the attachment case.**  The
translations `v` and the sets `W₋` that are the copies of some legal mark of `E` are the same
as those for `E'`, with `v` replaced by `v + τ`. -/
theorem mark_locality_exists {E E' : Diagram} {τ : ℤ × ℤ} {N w : ℕ} (M : MarkWindows E E' τ N w)
    {W : Diagram} {v : ℤ × ℤ} (L : LocalMark E N w W v) :
    (∃ cs, (MarkedInner.mk E W v cs).IsLegal) ↔ ∃ cs, (MarkedInner.mk E' W (v + τ) cs).IsLegal :=
  ⟨fun ⟨cs, h⟩ => ⟨cs, (mark_locality M L cs).mp h⟩,
    fun ⟨cs, h⟩ => ⟨cs, (mark_locality M L cs).mpr h⟩⟩

/-- **`lem:gluing-mark-locality`, the consequences for a legal mark.**  For the marks of
`mark_locality`, the middles of both are connected skew, and the hatted mark `Ŵ₋` is the
same. -/
theorem mark_locality_middle_hatMark {E E' : Diagram} {τ : ℤ × ℤ} {N w : ℕ}
    (M : MarkWindows E E' τ N w) {W : Diagram} {v : ℤ × ℤ} (L : LocalMark E N w W v)
    {cs : AttachCase} (h : (MarkedInner.mk E W v cs).IsLegal) :
    IsConnectedSkew (MarkedInner.mk E W v cs).middle ∧
      IsConnectedSkew (MarkedInner.mk E' W (v + τ) cs).middle ∧
      (MarkedInner.mk E' W (v + τ) cs).hatMark W = (MarkedInner.mk E W v cs).hatMark W := by
  have h' := (mark_locality M L cs).mp h
  have hne : ∀ {E₁ : Diagram} {v₁ : ℤ × ℤ}, (MarkedInner.mk E₁ W v₁ cs).IsLegal →
      ¬ (MarkedInner.mk E₁ W v₁ cs).IsEmptyMark → W.Nonempty := by
    intro E₁ v₁ h₁ hn
    rcases h₁.1.2 with h' | h'
    · exact absurd h' hn
    · exact h'.1
  have hW := hne h (M.not_isEmptyMark L)
  exact ⟨h.middle_connected hW, h'.middle_connected hW, M.hatMark_eq L⟩

/-! ### Sharpness of the windows -/

section Sharpness

/-- The row `(3)`, southwest-normalized. -/
def sharpRow : Diagram := skewOf [3] []

/-- The hook `(2, 1)`, southwest-normalized. -/
def sharpHook : Diagram := translate (-1, 0) (skewOf [2, 1] [])

/-- The width-one mark of case (a) on the row `(3)`. -/
def sharpRowMark : MarkedInner where
  E := sharpRow
  W := {(0, 0)}
  v := (0, 2)
  case := .a

/-- The width-one mark of case (d) on the hook `(2, 1)`, with the same lower copy and the
displacement `(0, 2) + τ` for `τ = (-1, -1)`. -/
def sharpHookMark : MarkedInner where
  E := sharpHook
  W := {(0, 0)}
  v := (-1, 1)
  case := .d

example : sw sharpRow = (0, 0) ∧ sw sharpHook = (0, 0) := by decide
example : span sharpRow = 3 ∧ span sharpHook = 3 := by decide
example : IsConnectedSkew sharpRow ∧ IsConnectedSkew sharpHook := by decide

/-- The two diagrams agree on the content `0`. -/
example : sharpRow.filter (fun x => content x = 0) = sharpHook.filter (fun x => content x = 0) := by
  decide

/-- Up to translation by `τ = (-1, -1)`, with `c(τ) = 0`, they agree on `[1, 2]`. -/
example : translate (-1, -1) (sharpRow.filter (fun x => 1 ≤ content x ∧ content x ≤ 2)) =
    sharpHook.filter (fun x => 1 ≤ content x ∧ content x ≤ 2) := by decide

/-- The lower window cannot be shortened to `[0, w - 1]`: the diagrams differ on the content
`1 = w`. -/
example : sharpRow.filter (fun x => 0 ≤ content x ∧ content x ≤ 1) ≠
    sharpHook.filter (fun x => 0 ≤ content x ∧ content x ≤ 1) := by decide

example : sharpRowMark.IsLegal := by decide
example : sharpHookMark.IsLegal := by decide
example : sharpRowMark.width = 1 ∧ sharpHookMark.width = 1 := by decide

/-- The two legal marks have different attachment cases, so legality does not transfer. -/
example : ¬ ({ sharpHookMark with case := .a } : MarkedInner).IsLegal := by decide
example : ¬ ({ sharpRowMark with case := .d } : MarkedInner).IsLegal := by decide

end Sharpness

/-! ### Edge displacements: the width-zero part of `lem:gluing-equal` -/

/-- The vertical empty-overlap displacement `v_V = ne(E) - sw(E) + (-1, 0)`. -/
def vV (E : Diagram) : ℤ × ℤ := ne E - sw E + (-1, 0)

/-- **`lem:gluing-equal`, width zero.**  The two edge displacements differ by `e`:
`v_H = v_V + e`. -/
theorem vH_eq_vV_add_eCell (E : Diagram) : vH E = vV E + eCell := by
  unfold vH vV eCell
  ext <;> simp

theorem vH_sub_vV (E : Diagram) : vH E - vV E = eCell := by
  rw [vH_eq_vV_add_eCell]; abel

/-- The empty mark with the horizontal edge reading. -/
def emptyMarkH (E : Diagram) : MarkedInner where
  E := E
  W := ∅
  v := vH E
  case := .a

/-- The vertical edge reading of the empty mark, as the case-(b) datum with displacement `v_V`. -/
def emptyMarkV (E : Diagram) : MarkedInner where
  E := E
  W := ∅
  v := vV E
  case := .b

/-- The empty mark on `E` (horizontal edge reading) is legal for a connected skew diagram `E`. -/
theorem emptyMarkH_isLegal {E : Diagram} (hE : IsConnectedSkew E) : (emptyMarkH E).IsLegal := by
  have hne := hE.2.1
  have hper : (emptyMarkH E).period = (span E : ℤ) := by
    change content (vH E) = (span E : ℤ)
    unfold vH
    rw [content_add, MarkedInner.content_sub, content_ne hne, content_sw hne,
        span_eq_of_isConnectedSkew hE]
    simp [content]
  have hw : (emptyMarkH E).width = 0 := by
    simp [MarkedInner.width, emptyMarkH, span, contents]
  have hspan : 0 < span E := Finset.card_pos.mpr (hne.image _)
  have hW : (emptyMarkH E).W = ∅ := rfl
  have hup : (emptyMarkH E).upper = ∅ := by
    simp [MarkedInner.upper, emptyMarkH, translate]
  refine ⟨⟨hE, Or.inl ⟨rfl, rfl, rfl⟩⟩, MarkedInner.isMaximal_of_empty hW, ?_, ⟨?_, ?_⟩,
    MarkedInner.noHatAdjacency_of_empty hW⟩
  · refine ⟨by simp [hw], ?_⟩
    rw [hper, hw]
    simpa using hspan
  · change IsConnectedSkew (E \ ∅)
    simpa using hE
  · rw [hup, Finset.sdiff_empty]
    exact hE

/-- **`lem:gluing-equal`, width zero, `eq:gluing-gauge`.**  The two edge readings of the empty
overlap compose to the same cells: `D ∘_H E = AT(D) ∘_V E`, by the offset identity
`eq:gluing-gauge` and `v_H - v_V = e`; no transpose identity for empty overlaps is used. -/
theorem compose_emptyMarks_antitranspose {D : Diagram} (hD : D.Nonempty) (E : Diagram) :
    (emptyMarkH E).compose D = (emptyMarkV E).compose (antitranspose D) :=
  MarkedInner.compose_antitranspose_gauge hD rfl rfl rfl (vH_eq_vV_add_eCell E)

/-! ### The middle tails of a legal mark -/

/-- The statement of `IsLegal.middle_subsingleton`, as a decidable condition. -/
def MarkedInner.MiddleSubsingleton (ω : MarkedInner) : Prop :=
  ∀ x ∈ ω.middle, ∀ y ∈ ω.middle, content x = content y →
    (content x ≤ minContent ω.E + ω.width - 1 ∨ minContent ω.E + ω.period ≤ content x) → x = y

instance (ω : MarkedInner) : Decidable ω.MiddleSubsingleton := by
  unfold MarkedInner.MiddleSubsingleton; infer_instance

example : chartFigureInner.MiddleSubsingleton := by decide
example : hookInner.MiddleSubsingleton := by decide
example : rowInnerThree.MiddleSubsingleton := by decide
example : rowInnerFour.MiddleSubsingleton := by decide
example : gaugeInnerA.MiddleSubsingleton := by decide +kernel
example : gaugeInnerB.MiddleSubsingleton := by decide +kernel

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

/-- **`lem:gluing-local` (1), second assertion, on the marked diagonals of `W₋`.**  The middle
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

/-- **`lem:gluing-local` (1), second assertion.**  The middle of a legal mark with `W₋ ≠ ∅` has
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

/-- **First side lemma.**  A middle cell `x` on a marked diagonal of the lower copy has a cell of
`W₋` diagonally next to it, on its southeast or northwest. -/
theorem IsLegal.exists_side (h : ω.IsLegal) (hW : ω.W.Nonempty) {x : ℤ × ℤ}
    (hx : x ∈ ω.middle) (h0 : minContent ω.E ≤ content x)
    (h1 : content x ≤ minContent ω.E + ω.width - 1) :
    x + eCell ∈ ω.W ∨ x - eCell ∈ ω.W := by
  have hnon := h.isNonemptyMark hW
  have hE := h.1.1
  obtain ⟨-, hwq⟩ := h.2.2.1
  obtain ⟨z, hz, hzc⟩ := hnon.exists_cell_W hE h0 h1
  obtain ⟨hxE, hxW, hxU⟩ := mem_middle.mp hx
  have hzE : z ∈ ω.E := hnon.2.2.1 hz
  have hq : ω.period = content ω.v := rfl
  have key : ∀ y : ℤ × ℤ, y ∈ ω.E → content y = content x → y ≠ x → y ∈ ω.W := by
    intro y hyE hyc hyx
    by_contra hyW
    have hyU : y ∉ ω.upper := fun hu => by
      have := (hnon.content_upper hE hu).1
      omega
    exact hyx (h.middle_subsingleton hW (mem_middle.mpr ⟨hyE, hyW, hyU⟩) hx hyc
      (Or.inl (by omega)))
  obtain ⟨a, b⟩ := z
  obtain ⟨i, j⟩ := x
  simp only [content] at hzc ⊢
  have hsk := h.1.1.1
  rcases lt_trichotomy a i with hai | hai | hai
  · right
    have hmem : (i - 1, j - 1) ∈ ω.E :=
      hsk.mem hzE hxE (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    have := key _ hmem (by simp only [content]; omega) (by simp)
    simpa [eCell] using this
  · exact absurd (by
      have : b = j := by omega
      subst hai; subst this; exact hz) hxW
  · left
    have hmem : (i + 1, j + 1) ∈ ω.E :=
      hsk.mem hxE hzE (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    have := key _ hmem (by simp only [content]; omega) (by simp)
    simpa [eCell] using this

end MarkedInner

/-- **No crossing.**  In a skew diagram `W`, if the cell `x ∉ W` has `x + s ∈ W` for a diagonal
step `s = ±e`, then a cell `x'` adjacent to `x` on the next diagonal cannot have `x' - s ∈ W`:
the two cells of `W` would enclose `x`. -/
theorem no_cross {W : Diagram} (hW : IsSkew W) {x x' : ℤ × ℤ} (hx : x ∉ W)
    (hadj : x' = x + (0, 1) ∨ x' = x + (-1, 0)) (s : ℤ × ℤ) (hs : s = eCell ∨ s = -eCell)
    (h : x + s ∈ W) : x' + -s ∉ W := by
  intro h'
  obtain ⟨i, j⟩ := x
  apply hx
  rcases hs with rfl | rfl <;> rcases hadj with rfl | rfl <;>
    simp only [eCell, Prod.mk_add_mk, Prod.neg_mk, neg_neg, add_zero] at h h'
  · exact hW.mem (a := i + (-1 : ℤ)) h' h (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)
  · exact hW.mem (a := i + -1 + -1) h' h (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)
  · exact hW.mem h h' (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  · exact hW.mem h h' (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

namespace MarkedInner

variable {ω : MarkedInner}

/-- Adjacent cells on consecutive diagonals: the second is the eastern or northern neighbor. -/
theorem adj_next {x z : ℤ × ℤ} (hadj : CellAdj x z) (hc : content z = content x + 1) :
    z = x + (0, 1) ∨ z = x + (-1, 0) := by
  obtain ⟨i, j⟩ := x
  obtain ⟨a, b⟩ := z
  rw [cellAdj_iff] at hadj
  simp only [content] at hc
  simp only [Prod.mk_add_mk, Prod.mk.injEq]
  omega

/-- The side of a marked diagonal is preserved from one middle cell to the next. -/
theorem IsLegal.side_step (h : ω.IsLegal) (hW : ω.W.Nonempty) {x x' : ℤ × ℤ}
    (hx : x ∈ ω.middle) (hx' : x' ∈ ω.middle)
    (hadj : x' = x + (0, 1) ∨ x' = x + (-1, 0))
    (h1 : content x' ≤ minContent ω.E + ω.width - 1) (s : ℤ × ℤ)
    (hs : s = eCell ∨ s = -eCell) (hxs : x + s ∈ ω.W) : x' + s ∈ ω.W := by
  have hnon := h.isNonemptyMark hW
  have hWsk := hnon.2.1.1
  have h0 : minContent ω.E ≤ content x' :=
    minContent_le (content_mem_contents (mem_middle.mp hx').1)
  have hxW := (mem_middle.mp hx).2.1
  have hnc := no_cross hWsk hxW hadj s hs hxs
  rcases h.exists_side hW hx' h0 h1 with h2 | h2
  · rcases hs with rfl | rfl
    · exact h2
    · exact absurd h2 (by simpa using hnc)
  · rcases hs with rfl | rfl
    · exact absurd (by rw [sub_eq_add_neg] at h2; exact h2) hnc
    · rw [sub_eq_add_neg] at h2; exact h2

/-- A middle cell on the last marked diagonal of `W₋` exists, or not: the middle has a cell on the
diagonal `c₀ + w`. -/
theorem IsLegal.exists_middle_cell_w (h : ω.IsLegal) (hW : ω.W.Nonempty) :
    ∃ x ∈ ω.middle, content x = minContent ω.E + ω.width := by
  have hnon := h.isNonemptyMark hW
  have hE := h.1.1
  obtain ⟨h0, hwq⟩ := h.2.2.1
  have hmax := hnon.maxContent_E hE
  obtain ⟨x, hx, hc⟩ := exists_cell_of_connectedSkew hE (d := minContent ω.E + ω.width)
    (by omega) (by omega)
  refine ⟨x, mem_middle.mpr ⟨hx, fun hh => ?_, fun hh => ?_⟩, hc⟩
  · have := (hnon.content_W hE hh).2; omega
  · have := (hnon.content_upper hE hh).1; omega

/-- Propagation of the side along the middle, upward through the marked diagonals of `W₋`. -/
theorem IsLegal.side_chain (h : ω.IsLegal) (hW : ω.W.Nonempty) (s : ℤ × ℤ)
    (hs : s = eCell ∨ s = -eCell) :
    ∀ n : ℕ, ∀ x ∈ ω.middle, x + s ∈ ω.W →
      content x + n ≤ minContent ω.E + ω.width - 1 →
      ∃ y ∈ ω.middle, content y = content x + n ∧ y + s ∈ ω.W := by
  intro n
  induction n with
  | zero => intro x hx hxs _; exact ⟨x, hx, by simp, hxs⟩
  | succ n ih =>
    intro x hx hxs hn
    have hconn := isConnectedSkew_iff_diagonal.mp (h.middle_connected hW)
    obtain ⟨x₁, hx₁, hc₁⟩ := h.exists_middle_cell_w hW
    have hlt : content x < maxContent ω.middle := by
      have := le_maxContent (content_mem_contents hx₁)
      push_cast at hn
      omega
    obtain ⟨z, hz, hadj, hzc⟩ := hconn.exists_next hx hlt
    have hnext := adj_next hadj hzc
    have hzs := h.side_step hW hx hz hnext (by push_cast at hn; omega) s hs hxs
    obtain ⟨y, hy, hyc, hys⟩ := ih z hz hzs (by push_cast at hn; omega)
    exact ⟨y, hy, by push_cast; omega, hys⟩

theorem IsLegal.lowerH_side (h : ω.IsLegal) (hW : ω.W.Nonempty) {x : ℤ × ℤ}
    (hx : x ∈ ω.middle) (hc : content x = minContent ω.E + ω.width - 1) (hH : ω.LowerH) :
    ∃ x₀ ∈ ω.middle, content x₀ ≤ minContent ω.E + ω.width - 1 ∧ x₀ + -eCell ∈ ω.W := by
  obtain ⟨x₀, hx₀, hmin, hwest⟩ := hH
  have hnon := h.isNonemptyMark hW
  have hle : content x₀ ≤ minContent ω.E + ω.width - 1 := by
    have := minContent_le (content_mem_contents hx)
    omega
  have h0 : minContent ω.E ≤ content x₀ :=
    minContent_le (content_mem_contents (mem_middle.mp hx₀).1)
  refine ⟨x₀, hx₀, hle, ?_⟩
  rcases h.exists_side hW hx₀ h0 hle with h2 | h2
  · exfalso
    obtain ⟨i, j⟩ := x₀
    have hsk := hnon.2.1.1
    refine (mem_middle.mp hx₀).2.1 ?_
    simp only [eCell, Prod.mk_add_mk] at h2
    exact hsk.mem hwest h2 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  · rw [sub_eq_add_neg] at h2; exact h2

theorem IsLegal.lowerV_side (h : ω.IsLegal) (hW : ω.W.Nonempty) {x : ℤ × ℤ}
    (hx : x ∈ ω.middle) (hc : content x = minContent ω.E + ω.width - 1) (hV : ω.LowerV) :
    ∃ x₀ ∈ ω.middle, content x₀ ≤ minContent ω.E + ω.width - 1 ∧ x₀ + eCell ∈ ω.W := by
  obtain ⟨x₀, hx₀, hmin, hsouth⟩ := hV
  have hnon := h.isNonemptyMark hW
  have hle : content x₀ ≤ minContent ω.E + ω.width - 1 := by
    have := minContent_le (content_mem_contents hx)
    omega
  have h0 : minContent ω.E ≤ content x₀ :=
    minContent_le (content_mem_contents (mem_middle.mp hx₀).1)
  refine ⟨x₀, hx₀, hle, ?_⟩
  rcases h.exists_side hW hx₀ h0 hle with h2 | h2
  · exact h2
  · exfalso
    obtain ⟨i, j⟩ := x₀
    have hsk := hnon.2.1.1
    refine (mem_middle.mp hx₀).2.1 ?_
    simp only [eCell, Prod.mk_sub_mk] at h2
    exact hsk.mem h2 hsouth (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

/-- **Lower tail, southeast.**  If a middle cell `x` on the last marked diagonal of `W₋` has the
cell `x - e` of `W₋` on its northwest, the lower attachment is not vertical. -/
theorem IsLegal.not_lowerV_of_sub (h : ω.IsLegal) (hW : ω.W.Nonempty) {x : ℤ × ℤ}
    (hx : x ∈ ω.middle) (hc : content x = minContent ω.E + ω.width - 1)
    (hs : x - eCell ∈ ω.W) : ¬ ω.LowerV := by
  intro hV
  obtain ⟨x₀, hx₀, hle, hx₀s⟩ := h.lowerV_side hW hx hc hV
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = minContent ω.E + ω.width - 1 - content x₀ :=
    ⟨(minContent ω.E + ω.width - 1 - content x₀).toNat, Int.toNat_of_nonneg (by omega)⟩
  obtain ⟨y, hy, hyc, hys⟩ := h.side_chain hW eCell (Or.inl rfl) n x₀ hx₀ hx₀s (by omega)
  have hyx : y = x := h.middle_subsingleton hW hy hx (by omega) (Or.inl (by omega))
  subst hyx
  have hnon := h.isNonemptyMark hW
  refine (mem_middle.mp hx).2.1 ?_
  obtain ⟨i, j⟩ := y
  simp only [eCell, Prod.mk_add_mk, Prod.mk_sub_mk] at hys hs
  exact hnon.2.1.1.mem hs hys (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega)

/-- **Lower tail, northwest.**  If a middle cell `x` on the last marked diagonal of `W₋` has the
cell `x + e` of `W₋` on its southeast, the lower attachment is not horizontal. -/
theorem IsLegal.not_lowerH_of_add (h : ω.IsLegal) (hW : ω.W.Nonempty) {x : ℤ × ℤ}
    (hx : x ∈ ω.middle) (hc : content x = minContent ω.E + ω.width - 1)
    (hs : x + eCell ∈ ω.W) : ¬ ω.LowerH := by
  intro hH
  obtain ⟨x₀, hx₀, hle, hx₀s⟩ := h.lowerH_side hW hx hc hH
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = minContent ω.E + ω.width - 1 - content x₀ :=
    ⟨(minContent ω.E + ω.width - 1 - content x₀).toNat, Int.toNat_of_nonneg (by omega)⟩
  obtain ⟨y, hy, hyc, hys⟩ := h.side_chain hW (-eCell) (Or.inr rfl) n x₀ hx₀ hx₀s (by omega)
  have hyx : y = x := h.middle_subsingleton hW hy hx (by omega) (Or.inl (by omega))
  subst hyx
  have hnon := h.isNonemptyMark hW
  refine (mem_middle.mp hx).2.1 ?_
  obtain ⟨i, j⟩ := y
  simp only [eCell, Prod.mk_add_mk, Prod.neg_mk] at hys hs
  exact hnon.2.1.1.mem (c := i + 1) (d := j + 1) hys hs (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)

/-- **Upper tail, northwest of `W₊`.**  If a middle cell `x` on the first marked diagonal of
`W₊` has the cell `x + e` of `W₊` on its southeast, the upper attachment is not vertical.  This
is the rotation of `IsLegal.not_lowerV_of_sub`. -/
theorem IsLegal.not_upperV_of_add (h : ω.IsLegal) (hW : ω.W.Nonempty) {x : ℤ × ℤ}
    (hx : x ∈ ω.middle) (hc : content x = minContent ω.E + ω.period)
    (hs : x + eCell ∈ ω.upper) : ¬ ω.UpperV := by
  rw [← lowerV_rotate]
  have hnon := h.isNonemptyMark hW
  have hE := h.1.1
  have hEne : ω.E.Nonempty := hE.2.1
  have hmax := hnon.maxContent_E hE
  refine (isLegal_rotate h).not_lowerV_of_sub (rotate_W_nonempty hW) (x := -x) ?_ ?_ ?_
  · rw [middle_rotate, mem_rotate, neg_neg]; exact hx
  · have hm : minContent (SkewMarkedFactor.Gluing.rotate ω.E) = -maxContent ω.E :=
      minContent_rotate hEne
    have : ω.rotate.E = SkewMarkedFactor.Gluing.rotate ω.E := rfl
    rw [this, hm, width_rotate]
    simp only [content, Prod.fst_neg, Prod.snd_neg] at hc ⊢
    omega
  · change -x - eCell ∈ SkewMarkedFactor.Gluing.rotate ω.upper
    rw [mem_rotate]
    have : -(-x - eCell) = x + eCell := by abel
    rw [this]; exact hs

/-- **Upper tail, southeast of `W₊`.**  If a middle cell `x` on the first marked diagonal of
`W₊` has the cell `x - e` of `W₊` on its northwest, the upper attachment is not horizontal. -/
theorem IsLegal.not_upperH_of_sub (h : ω.IsLegal) (hW : ω.W.Nonempty) {x : ℤ × ℤ}
    (hx : x ∈ ω.middle) (hc : content x = minContent ω.E + ω.period)
    (hs : x - eCell ∈ ω.upper) : ¬ ω.UpperH := by
  rw [← lowerH_rotate]
  have hnon := h.isNonemptyMark hW
  have hE := h.1.1
  have hEne : ω.E.Nonempty := hE.2.1
  have hmax := hnon.maxContent_E hE
  refine (isLegal_rotate h).not_lowerH_of_add (rotate_W_nonempty hW) (x := -x) ?_ ?_ ?_
  · rw [middle_rotate, mem_rotate, neg_neg]; exact hx
  · have hm : minContent (SkewMarkedFactor.Gluing.rotate ω.E) = -maxContent ω.E :=
      minContent_rotate hEne
    have : ω.rotate.E = SkewMarkedFactor.Gluing.rotate ω.E := rfl
    rw [this, hm, width_rotate]
    simp only [content, Prod.fst_neg, Prod.snd_neg] at hc ⊢
    omega
  · change -x + eCell ∈ SkewMarkedFactor.Gluing.rotate ω.upper
    rw [mem_rotate]
    have : -(-x + eCell) = x - eCell := by abel
    rw [this]; exact hs

end MarkedInner

namespace MarkedInner

variable {ω : MarkedInner}

/-- The first diagonal of `W₊` is the singleton `{sw(E) + v}`. -/
theorem IsLegal.eq_of_upper_start (h : ω.IsLegal) (hW : ω.W.Nonempty) {y : ℤ × ℤ}
    (hy : y ∈ ω.upper) (hc : content y = minContent ω.E + ω.period) : y = sw ω.E + ω.v := by
  have hnon := h.isNonemptyMark hW
  have hE := h.1.1
  have hEne : ω.E.Nonempty := hE.2.1
  obtain ⟨h2, h3⟩ := hnon.W_range hE
  have hq : ω.period = content ω.v := rfl
  have h1 : y - ω.v ∈ ω.W := mem_upper.mp hy
  have hc1 : content (y - ω.v) = minContent ω.W := by
    rw [content_sub]; omega
  have hsw : sw ω.E ∈ ω.W := hnon.2.2.2.2.1
  have hc2 : content (sw ω.E) = minContent ω.W := by rw [content_sw hEne]; omega
  have := eq_sw_of_content hnon.2.1 h1 hc1
  have := eq_sw_of_content hnon.2.1 hsw hc2
  have e : y - ω.v = sw ω.E := by simp_all
  rw [← e]; abel

/-- The last diagonal of `W₋` is the singleton `{ne(E) - v}`. -/
theorem IsLegal.eq_of_lower_end (h : ω.IsLegal) (hW : ω.W.Nonempty) {z : ℤ × ℤ}
    (hz : z ∈ ω.W) (hc : content z = minContent ω.E + ω.width - 1) : z = ne ω.E - ω.v := by
  have hnon := h.isNonemptyMark hW
  have hE := h.1.1
  have hEne : ω.E.Nonempty := hE.2.1
  obtain ⟨h2, h3⟩ := hnon.W_range hE
  have hmax := hnon.maxContent_E hE
  have hq : ω.period = content ω.v := rfl
  have hne : ne ω.E - ω.v ∈ ω.W := mem_upper.mp hnon.2.2.2.2.2.1
  have hc2 : content (ne ω.E - ω.v) = maxContent ω.W := by
    rw [content_sub, content_ne hEne]; omega
  have := eq_ne_of_content hnon.2.1 hz (by omega)
  have := eq_ne_of_content hnon.2.1 hne hc2
  simp_all

/-- **`lem:gluing-equal`: the displacement is read at an endpoint (III).**  For a legal mark with
`W₋ ≠ ∅`, the translated southwest cell `sw(E) + v` is an endpoint of the diagonal of `E` on
its content: deleting an interior cell would violate III for the removal of `W₊`.  Uses
conditions I–IV only through III. -/
theorem IsLegal.upper_start_endpoint (h : ω.IsLegal) (hW : ω.W.Nonempty) :
    (sw ω.E + ω.v).1 = diagLo ω.E (content (sw ω.E + ω.v)) ∨
      (sw ω.E + ω.v).1 = diagHi ω.E (content (sw ω.E + ω.v)) := by
  have hnon := h.isNonemptyMark hW
  have hE := h.1.1
  have hEne : ω.E.Nonempty := hE.2.1
  set p := sw ω.E + ω.v with hp
  have hpU : p ∈ ω.upper := mem_upper.mpr (by rw [hp, add_sub_cancel_right]; exact hnon.2.2.2.2.1)
  have hpE : p ∈ ω.E := hnon.2.2.2.1 hpU
  have hcp : content p = minContent ω.E + ω.period := by
    rw [hp, content_add, content_sw hEne]; rfl
  by_contra hcon
  rw [not_or] at hcon
  set k := content p with hk
  have hkE : k ∈ contents ω.E := content_mem_contents hpE
  have hlo := diagLo_le (D := ω.E) (k := k) (i := p.1) (j := p.2) hpE rfl
  have hhi := le_diagHi (D := ω.E) (k := k) (i := p.1) (j := p.2) hpE rfl
  have hlo' := diagLo_mem hkE
  have hhi' := diagHi_mem hkE
  have hB : IsConnectedSkew (ω.E \ ω.upper) := h.2.2.2.1.2
  have hB' := isConnectedSkew_iff_diagonal.mp hB
  have notU : ∀ r : ℤ, r ≠ p.1 → (r, r + k) ∉ ω.upper := by
    intro r hr hu
    have := h.eq_of_upper_start hW hu (by simp only [content]; omega)
    exact hr (congrArg Prod.fst this)
  have hm1 : (diagLo ω.E k, diagLo ω.E k + k) ∈ ω.E \ ω.upper :=
    Finset.mem_sdiff.mpr ⟨hlo', notU _ (by omega)⟩
  have hm2 : (diagHi ω.E k, diagHi ω.E k + k) ∈ ω.E \ ω.upper :=
    Finset.mem_sdiff.mpr ⟨hhi', notU _ (by omega)⟩
  have := hB'.2.2.1 _ hm1 _ hm2 (by simp [content]) p.1
    (Finset.mem_Icc.mpr ⟨by simp only; omega, by simp only; omega⟩)
  have hpp : (p.1, p.1 + content (diagLo ω.E k, diagLo ω.E k + k)) = p := by
    ext <;> simp [content, hk]
  rw [hpp] at this
  exact (Finset.mem_sdiff.mp this).2 hpU

/-- **The upper start diagonal has at most two cells.**  Uses `IsLegal.middle_subsingleton`:
the diagonal of `E` on the content `c₀ + q` consists of the cell `sw(E) + v` and at most one
middle cell. -/
theorem IsLegal.upper_start_thin (h : ω.IsLegal) (hW : ω.W.Nonempty) :
    diagHi ω.E (minContent ω.E + ω.period) ≤ diagLo ω.E (minContent ω.E + ω.period) + 1 := by
  by_contra hcon
  have hnon := h.isNonemptyMark hW
  have hE := h.1.1
  have hEne : ω.E.Nonempty := hE.2.1
  obtain ⟨-, hwq⟩ := h.2.2.1
  obtain ⟨h2, h3⟩ := hnon.W_range hE
  have hq : ω.period = content ω.v := rfl
  set k := minContent ω.E + ω.period with hk
  set p := sw ω.E + ω.v with hp
  have hpU : p ∈ ω.upper := mem_upper.mpr (by rw [hp, add_sub_cancel_right]; exact hnon.2.2.2.2.1)
  have hcp : content p = k := by
    rw [hp, content_add, content_sw hEne]; rfl
  have hpE : p ∈ ω.E := hnon.2.2.2.1 hpU
  have hkE : k ∈ contents ω.E := hcp ▸ content_mem_contents hpE
  have hE' := isConnectedSkew_iff_diagonal.mp hE
  have hlo := diagLo_le (D := ω.E) (k := k) (i := p.1) (j := p.2) hpE hcp
  have hmid : ∀ r : ℤ, diagLo ω.E k ≤ r → r ≤ diagHi ω.E k → r ≠ p.1 →
      (r, r + k) ∈ ω.middle := by
    intro r h1 h2' hr
    refine mem_middle.mpr ⟨hE'.mem_iff.mpr ⟨hkE, h1, h2'⟩, fun hw => ?_, fun hu => ?_⟩
    · have := (hnon.content_W hE hw).2
      simp only [content] at this; omega
    · have := h.eq_of_upper_start hW hu (by simp only [content]; omega)
      exact hr (congrArg Prod.fst this)
  have two : ∀ r r' : ℤ, diagLo ω.E k ≤ r → r ≤ diagHi ω.E k → r ≠ p.1 →
      diagLo ω.E k ≤ r' → r' ≤ diagHi ω.E k → r' ≠ p.1 → r = r' := by
    intro r r' a1 a2 a3 b1 b2 b3
    have := h.middle_subsingleton hW (hmid r a1 a2 a3) (hmid r' b1 b2 b3)
      (by simp only [content]; omega) (Or.inr (by simp only [content]; omega))
    simpa using this
  have hp1 : p.1 ≤ diagHi ω.E k := le_diagHi (D := ω.E) (k := k) (i := p.1) (j := p.2) hpE hcp
  by_cases ha : p.1 = diagLo ω.E k
  · have := two (diagLo ω.E k + 1) (diagLo ω.E k + 2) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)
    omega
  · by_cases hb : p.1 = diagLo ω.E k + 1
    · have := two (diagLo ω.E k) (diagLo ω.E k + 2) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega)
      omega
    · have := two (diagLo ω.E k) (diagLo ω.E k + 1) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega)
      omega

/-- **`lem:gluing-equal`: at positive width, two legal marks on one diagram with the same
width have displacements that agree or differ by `e`.**  Uses III (through
`IsLegal.upper_start_endpoint`) and `IsLegal.middle_subsingleton` (through
`IsLegal.upper_start_thin`).

**Differs from the paper's route.**  Only the endpoint condition at the southwest cell of the
upper copy is used, together with the bound on the middle; the mirrored condition at the
northeast cell is not needed for this bound. -/
theorem IsLegal.displacement_adjacent {ω' : MarkedInner} (h : ω.IsLegal) (h' : ω'.IsLegal)
    (hW : ω.W.Nonempty) (hW' : ω'.W.Nonempty) (hE : ω'.E = ω.E) (hw : ω'.width = ω.width) :
    ω'.v = ω.v ∨ ω'.v = ω.v + eCell ∨ ω.v = ω'.v + eCell := by
  have hEne : ω.E.Nonempty := h.1.1.2.1
  have hq : ω'.period = ω.period := by
    have h1 := h.1.span_eq
    have h2 := h'.1.span_eq
    rw [hE] at h2
    omega
  have e1 := h.upper_start_endpoint hW
  have e2 := h'.upper_start_endpoint hW'
  have hc1 : content (sw ω.E + ω.v) = minContent ω.E + ω.period := by
    rw [content_add, content_sw hEne]; rfl
  have hc2 : content (sw ω.E + ω'.v) = minContent ω.E + ω.period := by
    rw [content_add, content_sw hEne, ← hq]; rfl
  rw [hE] at e2
  rw [hc1] at e1
  rw [hc2] at e2
  have thin := h.upper_start_thin hW
  have hnon := h.isNonemptyMark hW
  have hpU : sw ω.E + ω.v ∈ ω.upper :=
    mem_upper.mpr (by rw [add_sub_cancel_right]; exact hnon.2.2.2.2.1)
  have hk : minContent ω.E + ω.period ∈ contents ω.E :=
    hc1 ▸ content_mem_contents (hnon.2.2.2.1 hpU)
  have lohi := diagLo_le_diagHi hk
  simp only [Prod.fst_add] at e1 e2
  have hcv : ω'.v.2 - ω'.v.1 = ω.v.2 - ω.v.1 := by
    have := hq
    simp only [period, content] at this
    exact this
  rcases (by omega : ω'.v.1 = ω.v.1 ∨ ω'.v.1 = ω.v.1 + 1 ∨ ω.v.1 = ω'.v.1 + 1) with a | a | a
  · exact Or.inl (Prod.ext (by omega) (by omega))
  · exact Or.inr (Or.inl (Prod.ext (by simp [eCell]; omega) (by simp [eCell]; omega)))
  · exact Or.inr (Or.inr (Prod.ext (by simp [eCell]; omega) (by simp [eCell]; omega)))

/-- **`lem:gluing-equal`: a double is ordinary, with cases (a) and (b).**  Let two legal marks
with nonempty `W₋` on the same diagram and of the same width have displacements differing by
`e`, `v' = v + e`.  Then the mark with the smaller displacement has case (b) and the one with
the larger displacement has case (a): the larger displacement places the upper copy southeast
and the lower copy northwest, so both attachments are horizontal, and the smaller one gives
both vertical.  In particular a mixed case cannot occur in a double.  Uses
`IsLegal.middle_subsingleton` (through the tail lemmas).

**Differs from the paper's route.**  The order of the middle tails is read from the cells
`sw(E) + v`, `sw(E) + v'`, `ne(E) - v`, `ne(E) - v'` directly, by propagating the side of the
tail along the middle (`IsLegal.side_chain`), instead of a noncrossing argument on diagonals. -/
theorem IsLegal.double_cases {ω' : MarkedInner} (h : ω.IsLegal) (h' : ω'.IsLegal)
    (hW : ω.W.Nonempty) (hW' : ω'.W.Nonempty) (hE : ω'.E = ω.E) (hw : ω'.width = ω.width)
    (hv : ω'.v = ω.v + eCell) : ω.case = .b ∧ ω'.case = .a := by
  have hnon := h.isNonemptyMark hW
  have hnon' := h'.isNonemptyMark hW'
  have hEc := h.1.1
  have hEne : ω.E.Nonempty := hEc.2.1
  obtain ⟨-, hwq⟩ := h.2.2.1
  obtain ⟨hr1, hr2⟩ := hnon.W_range hEc
  have hmax := hnon.maxContent_E hEc
  have hq : ω'.period = ω.period := by
    have h1 := h.1.span_eq
    have h2 := h'.1.span_eq
    rw [hE] at h2
    omega
  have hqv : ω.period = content ω.v := rfl
  have hqv' : ω'.period = content ω'.v := rfl
  have hEc' := h'.1.1
  have e0 : minContent ω'.E = minContent ω.E := by rw [hE]
  have hceE : content eCell = 0 := by simp [content, eCell]
  have hne1 : ∀ z : ℤ × ℤ, z + eCell = z → False := fun z hz => by
    have := congrArg Prod.fst hz
    simp [eCell] at this
  have hne2 : ∀ z : ℤ × ℤ, z - eCell = z → False := fun z hz => by
    have := congrArg Prod.fst hz
    simp [eCell] at this
  -- the cells `p = sw E + v`, `p + e = sw E + v'`, `q₁ = ne E - v`, `q₂ = q₁ - e = ne E - v'`
  set p := sw ω.E + ω.v with hp
  have hpU : p ∈ ω.upper := mem_upper.mpr (by rw [hp, add_sub_cancel_right]; exact hnon.2.2.2.2.1)
  have hswW' : sw ω.E ∈ ω'.W := by rw [← hE]; exact hnon'.2.2.2.2.1
  have hp'U : p + eCell ∈ ω'.upper := by
    rw [mem_upper, hv]
    have : p + eCell - (ω.v + eCell) = sw ω.E := by rw [hp]; abel
    rw [this]; exact hswW'
  have hpE : p ∈ ω.E := hnon.2.2.2.1 hpU
  have hp'E : p + eCell ∈ ω.E := hE ▸ hnon'.2.2.2.1 hp'U
  have hcp : content p = minContent ω.E + ω.period := by
    rw [hp, content_add, content_sw hEne]; rfl
  have hcp' : content (p + eCell) = minContent ω.E + ω.period := by
    rw [content_add, hceE, hcp]; ring
  have hq1W : ne ω.E - ω.v ∈ ω.W := mem_upper.mp hnon.2.2.2.2.2.1
  have hneU' : ne ω.E ∈ ω'.upper := by rw [← hE]; exact hnon'.2.2.2.2.2.1
  have hq2W : ne ω.E - ω'.v ∈ ω'.W := mem_upper.mp hneU'
  have hq2 : ne ω.E - ω'.v = (ne ω.E - ω.v) - eCell := by rw [hv]; abel
  have hq1E : ne ω.E - ω.v ∈ ω.E := hnon.2.2.1 hq1W
  have hq2E : (ne ω.E - ω.v) - eCell ∈ ω.E := by
    have := hnon'.2.2.1 hq2W
    rw [hE] at this
    rw [← hq2]; exact this
  have hcq1 : content (ne ω.E - ω.v) = minContent ω.E + ω.width - 1 := by
    rw [content_sub, content_ne hEne]; omega
  have hcq2 : content ((ne ω.E - ω.v) - eCell) = minContent ω.E + ω.width - 1 := by
    rw [content_sub_eCell, hcq1]
  have hq2W' : (ne ω.E - ω.v) - eCell ∈ ω'.W := by rw [← hq2]; exact hq2W
  have hatt := hnon.2.2.2.2.2.2
  have hatt' := hnon'.2.2.2.2.2.2
  obtain ⟨ha, hb, hc, hd⟩ := hatt
  obtain ⟨ha', hb', hc', hd'⟩ := hatt'
  constructor
  · -- the mark with the smaller displacement
    have hpmid : p + eCell ∈ ω.middle := by
      refine mem_middle.mpr ⟨hp'E, fun hh => ?_, fun hu => ?_⟩
      · have := (hnon.content_W hEc hh).2; omega
      · exact hne1 p (h.eq_of_upper_start hW hu hcp')
    have notUH : ¬ ω.UpperH := h.not_upperH_of_sub hW hpmid hcp' (by simpa using hpU)
    have hq2mid : (ne ω.E - ω.v) - eCell ∈ ω.middle := by
      refine mem_middle.mpr ⟨hq2E, fun hh => ?_, fun hu => ?_⟩
      · exact hne2 _ (h.eq_of_lower_end hW hh hcq2)
      · have := (hnon.content_upper hEc hu).1; omega
    have notLH : ¬ ω.LowerH :=
      h.not_lowerH_of_add hW hq2mid hcq2 (by simpa using hq1W)
    rcases hcs : ω.case with _ | _ | _ | _
    · exact absurd (ha hcs).1 notLH
    · rfl
    · exact absurd (hc hcs).1 notLH
    · exact absurd (hd hcs).2 notUH
  · -- the mark with the larger displacement
    have hpmid : p ∈ ω'.middle := by
      refine mem_middle.mpr ⟨hE ▸ hpE, fun hh => ?_, fun hu => ?_⟩
      · have := (hnon'.content_W hEc' hh).2; omega
      · have := h'.eq_of_upper_start hW' hu (by omega)
        have h2 : p = p + eCell := by
          calc p = sw ω'.E + ω'.v := this
            _ = sw ω.E + (ω.v + eCell) := by rw [hE, hv]
            _ = p + eCell := by rw [hp]; abel
        exact hne1 p h2.symm
    have notUV : ¬ ω'.UpperV := h'.not_upperV_of_add hW' hpmid (by omega) hp'U
    have hq1mid : ne ω.E - ω.v ∈ ω'.middle := by
      refine mem_middle.mpr ⟨hE ▸ hq1E, fun hh => ?_, fun hu => ?_⟩
      · have := h'.eq_of_lower_end hW' hh (by omega)
        have h2 : ne ω.E - ω.v = (ne ω.E - ω.v) - eCell := by
          calc ne ω.E - ω.v = ne ω'.E - ω'.v := this
            _ = ne ω.E - ω'.v := by rw [hE]
            _ = (ne ω.E - ω.v) - eCell := hq2
        exact hne2 _ h2.symm
      · have := (hnon'.content_upper hEc' hu).1; omega
    have notLV : ¬ ω'.LowerV :=
      h'.not_lowerV_of_sub hW' hq1mid (by omega) hq2W'
    rcases hcs : ω'.case with _ | _ | _ | _
    · rfl
    · exact absurd (hb' hcs).1 notLV
    · exact absurd (hc' hcs).2 notUV
    · exact absurd (hd' hcs).1 notLV

/-- For a legal mark with `W₋ ≠ ∅`, the lower attachment is not both horizontal and vertical. -/
theorem IsLegal.not_lowerH_and_lowerV (h : ω.IsLegal) (hW : ω.W.Nonempty) :
    ¬ (ω.LowerH ∧ ω.LowerV) := by
  rintro ⟨⟨x₁, hx₁, hc₁, hw₁⟩, ⟨x₂, hx₂, hc₂, hs₂⟩⟩
  have hconn := h.middle_connected hW
  have e1 := eq_sw_of_content hconn hx₁ hc₁
  have e2 := eq_sw_of_content hconn hx₂ hc₂
  have hx : x₁ = x₂ := by rw [e1, e2]
  subst hx
  obtain ⟨i, j⟩ := x₁
  refine (mem_middle.mp hx₁).2.1 ?_
  exact (h.isNonemptyMark hW).2.1.1.mem hw₁ hs₂ (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)

/-- For a legal mark with `W₋ ≠ ∅`, the upper attachment is not both horizontal and vertical. -/
theorem IsLegal.not_upperH_and_upperV (h : ω.IsLegal) (hW : ω.W.Nonempty) :
    ¬ (ω.UpperH ∧ ω.UpperV) := by
  rintro ⟨⟨x₁, hx₁, hc₁, hw₁⟩, ⟨x₂, hx₂, hc₂, hs₂⟩⟩
  have hconn := h.middle_connected hW
  have e1 := MarkedInner.eq_ne_of_content hconn hx₁ hc₁
  have e2 := MarkedInner.eq_ne_of_content hconn hx₂ hc₂
  have hx : x₁ = x₂ := by rw [e1, e2]
  subst hx
  obtain ⟨i, j⟩ := x₁
  refine (mem_middle.mp hx₁).2.2 ?_
  have hsk : IsSkew ω.upper := isSkew_translate _ (h.isNonemptyMark hW).2.1.1
  exact hsk.mem hs₂ hw₁ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

theorem case_eq_of_predicates {cs cs' : AttachCase} {LH LV UH UV : Prop}
    (exL : ¬ (LH ∧ LV)) (exU : ¬ (UH ∧ UV))
    (hn : (cs = .a → LH ∧ UH) ∧ (cs = .b → LV ∧ UV) ∧ (cs = .c → LH ∧ UV) ∧
      (cs = .d → LV ∧ UH))
    (hn' : (cs' = .a → LH ∧ UH) ∧ (cs' = .b → LV ∧ UV) ∧ (cs' = .c → LH ∧ UV) ∧
      (cs' = .d → LV ∧ UH)) : cs = cs' := by
  obtain ⟨ha, hb, hc, hd⟩ := hn
  obtain ⟨ha', hb', hc', hd'⟩ := hn'
  cases cs <;> cases cs' <;> first | rfl | (exfalso; simp_all)

/-- The attachment case of a legal mark is determined by `E`, `W₋` and `v`. -/
theorem IsLegal.case_unique {E W : Diagram} {v : ℤ × ℤ} {cs cs' : AttachCase}
    (h : (MarkedInner.mk E W v cs).IsLegal) (h' : (MarkedInner.mk E W v cs').IsLegal)
    (hW : W.Nonempty) : cs = cs' :=
  case_eq_of_predicates (h.not_lowerH_and_lowerV hW) (h.not_upperH_and_upperV hW)
    (h.isNonemptyMark hW).2.2.2.2.2.2 (h'.isNonemptyMark hW).2.2.2.2.2.2

/-- **`lem:gluing-equal`: maximality fixes the mark at each displacement.**  Two legal marks with
nonempty `W₋` on the same diagram and with the same displacement coincide: `W₋ = E ∩ (E - v)`
by `IsLegal.W_eq_fullIntersection` (condition I), and then the attachment case is determined. -/
theorem IsLegal.eq_of_displacement {ω' : MarkedInner} (h : ω.IsLegal) (h' : ω'.IsLegal)
    (hW : ω.W.Nonempty) (hW' : ω'.W.Nonempty) (hE : ω'.E = ω.E) (hv : ω'.v = ω.v) :
    ω' = ω := by
  have e1 := h.W_eq_fullIntersection hW
  have e2 := h'.W_eq_fullIntersection hW'
  have hW2 : ω'.W = ω.W := by
    rw [e2, e1]; unfold fullIntersection; rw [hE, hv]
  obtain ⟨E, W, v, cs⟩ := ω
  obtain ⟨E', W', v', cs'⟩ := ω'
  simp only at hE hv hW2 h' h hW
  subst hE hv hW2
  exact congrArg _ (h'.case_unique h hW')

/-- **`lem:gluing-equal`: at positive width the possible displacements are at most two, and
differ by `e`.**  For a fixed diagram `E` and width `w`, all displacements of legal marks with
`W₋ ≠ ∅` lie in `{v₀, v₀ + e}` for some `v₀`.  Uses `IsLegal.displacement_adjacent`. -/
theorem exists_displacement_pair (E : Diagram) (w : ℕ) :
    ∃ v₀ : ℤ × ℤ, ∀ ω : MarkedInner, ω.IsLegal → ω.W.Nonempty → ω.E = E → ω.width = w →
      ω.v = v₀ ∨ ω.v = v₀ + eCell := by
  by_cases hex : ∃ ω : MarkedInner, ω.IsLegal ∧ ω.W.Nonempty ∧ ω.E = E ∧ ω.width = w
  · obtain ⟨ω₁, h₁, hW₁, hE₁, hw₁⟩ := hex
    by_cases hlow : ∃ ω₂ : MarkedInner, ω₂.IsLegal ∧ ω₂.W.Nonempty ∧ ω₂.E = E ∧
        ω₂.width = w ∧ ω₂.v + eCell = ω₁.v
    · obtain ⟨ω₂, h₂, hW₂, hE₂, hw₂, hv₂⟩ := hlow
      refine ⟨ω₂.v, fun ω h hW hE hw => ?_⟩
      have a2 := h₂.displacement_adjacent h hW₂ hW (hE.trans hE₂.symm) (hw.trans hw₂.symm)
      have a1 := h₁.displacement_adjacent h hW₁ hW (hE.trans hE₁.symm) (hw.trans hw₁.symm)
      have hv2 := congrArg Prod.fst hv₂
      have hv2' := congrArg Prod.snd hv₂
      simp only [Prod.fst_add, Prod.snd_add, eCell] at hv2 hv2'
      rcases a2 with a | a | a
      · exact Or.inl a
      · exact Or.inr a
      · exfalso
        rcases a1 with b | b | b <;>
          · have b1 := congrArg Prod.fst b
            have b2 := congrArg Prod.snd b
            have a1' := congrArg Prod.fst a
            have a2' := congrArg Prod.snd a
            simp only [Prod.fst_add, Prod.snd_add, eCell] at b1 b2 a1' a2'
            omega
    · refine ⟨ω₁.v, fun ω h hW hE hw => ?_⟩
      rcases h₁.displacement_adjacent h hW₁ hW (hE.trans hE₁.symm) (hw.trans hw₁.symm) with
        a | a | a
      · exact Or.inl a
      · exact Or.inr a
      · exact absurd ⟨ω, h, hW, hE, hw, a.symm⟩ hlow
  · exact ⟨0, fun ω h hW hE hw => absurd ⟨ω, h, hW, hE, hw⟩ hex⟩

/-- **`lem:gluing-equal`: when two displacements exist, both marks are ordinary.**  Two legal
marks with `W₋ ≠ ∅` on one diagram, of one width and with different displacements, have the
cases (a) and (b) (the one with the larger displacement being (a)); so neither is mixed. -/
theorem IsLegal.not_isMixed_of_ne {ω' : MarkedInner} (h : ω.IsLegal) (h' : ω'.IsLegal)
    (hW : ω.W.Nonempty) (hW' : ω'.W.Nonempty) (hE : ω'.E = ω.E) (hw : ω'.width = ω.width)
    (hv : ω'.v ≠ ω.v) : ¬ ω.case.IsMixed ∧ ¬ ω'.case.IsMixed := by
  rcases h.displacement_adjacent h' hW hW' hE hw with a | a | a
  · exact absurd a hv
  · obtain ⟨c1, c2⟩ := h.double_cases h' hW hW' hE hw a
    simp [AttachCase.IsMixed, c1, c2]
  · obtain ⟨c1, c2⟩ := h'.double_cases h hW' hW hE.symm hw.symm a
    simp [AttachCase.IsMixed, c1, c2]

/-- **`lem:gluing-equal`: a mixed case cannot occur in a double.**  A legal mixed mark with
`W₋ ≠ ∅` is the only legal mark with `W₋ ≠ ∅` of its width on its diagram. -/
theorem IsLegal.eq_of_isMixed {ω' : MarkedInner} (h : ω.IsLegal) (h' : ω'.IsLegal)
    (hW : ω.W.Nonempty) (hW' : ω'.W.Nonempty) (hE : ω'.E = ω.E) (hw : ω'.width = ω.width)
    (hmix : ω.case.IsMixed) : ω' = ω := by
  by_cases hv : ω'.v = ω.v
  · exact h.eq_of_displacement h' hW hW' hE hv
  · exact absurd hmix (h.not_isMixed_of_ne h' hW hW' hE hw hv).1

end MarkedInner

/-! ### Checked instance: the ordinary double on `(4, 4, 2) / (2)` -/

/-- The two ordinary marks of `gaugeInnerA` and `gaugeInnerB` form a double, with the larger
displacement of case (a), as `IsLegal.double_cases` predicts. -/
example : gaugeInnerB.case = .b ∧ gaugeInnerA.case = .a :=
  MarkedInner.IsLegal.double_cases (ω := gaugeInnerB) (ω' := gaugeInnerA)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide) rfl (by decide)
    (by decide)

/-! ### A checked instance of `lem:gluing-mark-locality` -/

/-- The hypotheses of `lem:gluing-mark-locality` hold for the chart-figure diagram compared with
itself (`τ = 0`, `N = 5`, `w = 2`). -/
theorem chartFigure_markWindows : MarkWindows chartFigureInner.E chartFigureInner.E 0 5 2 where
  conn := by decide
  conn' := by decide
  sw_eq := by decide
  sw_eq' := by decide
  span_eq := by decide
  span_eq' := by decide
  one_le := by decide
  two_mul_lt := by decide
  lower _ _ _ := Iff.rfl
  upper x _ _ := by rw [translate_zero]
  content_tau := by simp [content]

theorem chartFigure_localMark :
    LocalMark chartFigureInner.E 5 2 chartFigureInner.W chartFigureInner.v where
  subset := by decide
  content_mem := by decide
  content_v := by decide

/-- The chart-figure mark is legal for the case (a), and so is its image under the window
comparison. -/
example :
    (MarkedInner.mk chartFigureInner.E chartFigureInner.W (chartFigureInner.v + 0) .a).IsLegal :=
  (mark_locality chartFigure_markWindows chartFigure_localMark .a).mp (by decide)

end SkewMarkedFactor.Gluing
