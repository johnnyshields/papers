/- TODO-COPIED: adapted from
`skew-factor-gluing/lean/SkewGluing/Aligned/InnerFactor/Rows.lean`. -/
import GluingCore.Local

/-!
# Diagrams given by their diagonal rows

Formalizes `shields-2026-skew-factor-gluing.tex`, «Equal and divisible periods»
(`prop:gluing-divisible`), via the diagonal criterion of `eq:gluing-bits`.

`rowsDiagram m M ℓ h` is the cell set whose diagonal of content `k ∈ [m, M]` has the rows
`[ℓ k, h k]`.  Under the stepping and end conditions of the diagonal criterion it is a connected
skew diagram whose diagonal rows are `ℓ` and `h`.  The inner factor of `prop:gluing-divisible` is
assembled from two windows of the outer diagram in this form.

Sorry-free.
-/

namespace GluingCore

/-- The cell set whose diagonal of content `k ∈ [m, M]` has the rows `[ℓ k, h k]`. -/
def rowsDiagram (m M : ℤ) (ℓ h : ℤ → ℤ) : Diagram :=
  (Finset.Icc m M).biUnion fun k => (Finset.Icc (ℓ k) (h k)).image fun i => (i, i + k)

/-- The stepping and end conditions of the diagonal criterion for the rows `[ℓ k, h k]`,
`m ≤ k ≤ M`. -/
structure RowsData (m M : ℤ) (ℓ h : ℤ → ℤ) : Prop where
  le : m ≤ M
  ne : ∀ k, m ≤ k → k ≤ M → ℓ k ≤ h k
  stepLo : ∀ k, m + 1 ≤ k → k ≤ M → ℓ (k - 1) - ℓ k = 0 ∨ ℓ (k - 1) - ℓ k = 1
  stepHi : ∀ k, m + 1 ≤ k → k ≤ M → h (k - 1) - h k = 0 ∨ h (k - 1) - h k = 1
  first : ℓ m = h m
  last : ℓ M = h M

theorem HasDiagonalShape.mem_iff' {D : Diagram} (h : HasDiagonalShape D) {x : ℤ × ℤ} :
    x ∈ D ↔ content x ∈ contents D ∧ diagLo D (content x) ≤ x.1 ∧ x.1 ≤ diagHi D (content x) := by
  obtain ⟨i, j⟩ := x
  have e : (i, j) = (i, i + (j - i)) := by ext <;> simp
  rw [e, h.mem_iff]
  simp [content]

namespace RowsDiagram

variable {m M : ℤ} {ℓ h : ℤ → ℤ}

theorem mem_iff {i k : ℤ} :
    (i, i + k) ∈ rowsDiagram m M ℓ h ↔ (m ≤ k ∧ k ≤ M) ∧ ℓ k ≤ i ∧ i ≤ h k := by
  unfold rowsDiagram
  simp only [Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨k', hk', i', hi', rfl, hk⟩
    have : k' = k := by omega
    subst this
    exact ⟨hk', hi'.1, hi'.2⟩
  · rintro ⟨hk, h1, h2⟩
    exact ⟨k, hk, i, ⟨h1, h2⟩, rfl, rfl⟩

theorem mem_iff' {x : ℤ × ℤ} :
    x ∈ rowsDiagram m M ℓ h ↔
      (m ≤ content x ∧ content x ≤ M) ∧ ℓ (content x) ≤ x.1 ∧ x.1 ≤ h (content x) := by
  obtain ⟨i, j⟩ := x
  have e : (i, j) = (i, i + (j - i)) := by ext <;> simp
  rw [e, mem_iff]
  simp [content]

theorem contents_mem {k : ℤ} (hd : RowsData m M ℓ h) :
    k ∈ contents (rowsDiagram m M ℓ h) ↔ m ≤ k ∧ k ≤ M := by
  rw [mem_contents_iff]
  constructor
  · rintro ⟨i, hi⟩
    exact (mem_iff.mp hi).1
  · intro hk
    exact ⟨ℓ k, mem_iff.mpr ⟨hk, le_refl _, hd.ne k hk.1 hk.2⟩⟩

theorem diagLo_eq (hd : RowsData m M ℓ h) {k : ℤ} (h1 : m ≤ k) (h2 : k ≤ M) :
    diagLo (rowsDiagram m M ℓ h) k = ℓ k := by
  apply diagLo_eq_of (l := ℓ k)
  · exact mem_iff.mpr ⟨⟨h1, h2⟩, le_refl _, hd.ne k h1 h2⟩
  · intro i hi
    exact (mem_iff.mp hi).2.1

theorem diagHi_eq (hd : RowsData m M ℓ h) {k : ℤ} (h1 : m ≤ k) (h2 : k ≤ M) :
    diagHi (rowsDiagram m M ℓ h) k = h k := by
  apply diagHi_eq_of (l := h k)
  · exact mem_iff.mpr ⟨⟨h1, h2⟩, hd.ne k h1 h2, le_refl _⟩
  · intro i hi
    exact (mem_iff.mp hi).2.2

theorem hasDiagonalShape (hd : RowsData m M ℓ h) : HasDiagonalShape (rowsDiagram m M ℓ h) := by
  have hc : ∀ k, k ∈ contents (rowsDiagram m M ℓ h) ↔ m ≤ k ∧ k ≤ M := fun k => contents_mem hd
  refine ⟨⟨(ℓ m, ℓ m + m), mem_iff.mpr ⟨⟨le_refl _, hd.le⟩, le_refl _, hd.ne m (le_refl _) hd.le⟩⟩,
    ?_, ?_, ?_, ?_⟩
  · intro x hx y hy k hk
    rw [Finset.mem_Icc] at hk
    have h1 := (hc _).mp (content_mem_contents hx)
    have h2 := (hc _).mp (content_mem_contents hy)
    rw [hc]
    omega
  · intro x hx y hy hxy i hi
    rw [Finset.mem_Icc] at hi
    obtain ⟨x1, x2⟩ := x
    obtain ⟨y1, y2⟩ := y
    have ex : (x1, x2) = (x1, x1 + content (x1, x2)) := by ext <;> simp [content]
    have ey : (y1, y2) = (y1, y1 + content (y1, y2)) := by ext <;> simp [content]
    rw [ex, mem_iff] at hx
    rw [ey, mem_iff] at hy
    simp only [content] at hxy hx hy ⊢
    have e2 : (i, i + (x2 - x1)) = (i, i + (x2 - x1)) := rfl
    rw [mem_iff]
    simp only at hi
    have : y2 - y1 = x2 - x1 := hxy.symm
    rw [this] at hy
    exact ⟨hx.1, by omega, by omega⟩
  · intro k hk hk1
    rw [hc] at hk hk1
    have a1 := diagLo_eq hd (k := k) hk.1 hk.2
    have a2 := diagLo_eq hd (k := k - 1) hk1.1 hk1.2
    have b1 := diagHi_eq hd (k := k) hk.1 hk.2
    have b2 := diagHi_eq hd (k := k - 1) hk1.1 hk1.2
    have s1 := hd.stepLo k (by omega) hk.2
    have s2 := hd.stepHi k (by omega) hk.2
    simp only [bitA, bitB, a1, a2, b1, b2, Finset.mem_insert, Finset.mem_singleton]
    exact ⟨s1, s2⟩
  · intro k hk hend
    rw [hc] at hk
    rw [diagLo_eq hd hk.1 hk.2, diagHi_eq hd hk.1 hk.2]
    rcases hend with hend | hend
    · rw [hc] at hend
      have : k = m := by omega
      subst this; exact hd.first
    · rw [hc] at hend
      have : k = M := by omega
      subst this; exact hd.last

theorem isConnectedSkew (hd : RowsData m M ℓ h) : IsConnectedSkew (rowsDiagram m M ℓ h) :=
  isConnectedSkew_iff_diagonal.mpr (hasDiagonalShape hd)

theorem minContent_eq (hd : RowsData m M ℓ h) : minContent (rowsDiagram m M ℓ h) = m := by
  apply minContent_eq_of (k := m)
  · rw [contents_mem hd]; exact ⟨le_refl _, hd.le⟩
  · intro k hk
    rw [contents_mem hd] at hk
    exact hk.1

theorem maxContent_eq (hd : RowsData m M ℓ h) : maxContent (rowsDiagram m M ℓ h) = M := by
  apply maxContent_eq_of (k := M)
  · rw [contents_mem hd]; exact ⟨hd.le, le_refl _⟩
  · intro k hk
    rw [contents_mem hd] at hk
    exact hk.2

theorem span_eq (hd : RowsData m M ℓ h) : (span (rowsDiagram m M ℓ h) : ℤ) = M - m + 1 := by
  rw [span_eq_of_isConnectedSkew (isConnectedSkew hd), minContent_eq hd, maxContent_eq hd]

end RowsDiagram

end GluingCore
