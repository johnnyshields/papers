/- TODO-COPIED: adapted from
`skew-factor-gluing/lean/SkewGluing/OrdinaryFold/Interval.lean`. -/
import GluingCore.Diagram

/-!
# Diagrams described by their diagonal intervals

Formalizes `shields-2026-skew-factor-gluing.tex`, «Diagonal geometry» (the diagonal criterion
after `eq:gluing-bits`), in the form used to build the inner of the fold in
`prop:gluing-ordinary-fold`.

`DiagSet S k₀ k₁ lo hi` says that the diagonal of content `k ∈ [k₀, k₁]` of the cell set `S` is
the row interval `[lo k, hi k]` and that `S` has no other cells.  `DiagShape` collects the
conditions of the diagonal criterion on `lo`, `hi`; then `S` is connected skew
(`DiagSet.isConnectedSkew`), with the expected contents, rows, southwest and northeast cells.

Sorry-free.
-/

namespace GluingCore

/-- The cell set `S` has, on the content `k ∈ [k₀, k₁]`, exactly the rows `[lo k, hi k]`. -/
def DiagSet (S : Diagram) (k₀ k₁ : ℤ) (lo hi : ℤ → ℤ) : Prop :=
  ∀ i k : ℤ, (i, i + k) ∈ S ↔ k₀ ≤ k ∧ k ≤ k₁ ∧ lo k ≤ i ∧ i ≤ hi k

/-- The conditions of the diagonal criterion on the endpoint functions `lo`, `hi` of the contents
`[k₀, k₁]`: nonempty diagonals, endpoint steps in `{0, 1}`, singleton end diagonals. -/
structure DiagShape (k₀ k₁ : ℤ) (lo hi : ℤ → ℤ) : Prop where
  le : k₀ ≤ k₁
  ne : ∀ k, k₀ ≤ k → k ≤ k₁ → lo k ≤ hi k
  stepLo : ∀ k, k₀ < k → k ≤ k₁ → lo (k - 1) - lo k = 0 ∨ lo (k - 1) - lo k = 1
  stepHi : ∀ k, k₀ < k → k ≤ k₁ → hi (k - 1) - hi k = 0 ∨ hi (k - 1) - hi k = 1
  endLo : lo k₀ = hi k₀
  endHi : lo k₁ = hi k₁

namespace DiagSet

variable {S : Diagram} {k₀ k₁ : ℤ} {lo hi : ℤ → ℤ}

theorem mem_iff (h : DiagSet S k₀ k₁ lo hi) {x : ℤ × ℤ} :
    x ∈ S ↔ k₀ ≤ content x ∧ content x ≤ k₁ ∧ lo (content x) ≤ x.1 ∧ x.1 ≤ hi (content x) := by
  obtain ⟨i, j⟩ := x
  have := h i (j - i)
  simp only [content]
  have e : i + (j - i) = j := by ring
  rw [e] at this
  exact this

theorem contents_eq (h : DiagSet S k₀ k₁ lo hi) (hs : DiagShape k₀ k₁ lo hi) :
    contents S = Finset.Icc k₀ k₁ := by
  ext k
  rw [mem_contents_iff, Finset.mem_Icc]
  constructor
  · rintro ⟨i, hi'⟩
    have := (h i k).mp hi'
    exact ⟨this.1, this.2.1⟩
  · rintro ⟨h1, h2⟩
    exact ⟨lo k, (h (lo k) k).mpr ⟨h1, h2, le_refl _, hs.ne k h1 h2⟩⟩

theorem nonempty (h : DiagSet S k₀ k₁ lo hi) (hs : DiagShape k₀ k₁ lo hi) : S.Nonempty :=
  ⟨(lo k₀, lo k₀ + k₀), (h _ _).mpr ⟨le_refl _, hs.le, le_refl _, hs.ne k₀ (le_refl _) hs.le⟩⟩

theorem minContent_eq (h : DiagSet S k₀ k₁ lo hi) (hs : DiagShape k₀ k₁ lo hi) :
    minContent S = k₀ := by
  have hmem : k₀ ∈ contents S := by
    rw [h.contents_eq hs, Finset.mem_Icc]; exact ⟨le_refl _, hs.le⟩
  have h1 := minContent_le hmem
  have h2 := minContent_mem (h.nonempty hs)
  rw [h.contents_eq hs, Finset.mem_Icc] at h2
  omega

theorem maxContent_eq (h : DiagSet S k₀ k₁ lo hi) (hs : DiagShape k₀ k₁ lo hi) :
    maxContent S = k₁ := by
  have hmem : k₁ ∈ contents S := by
    rw [h.contents_eq hs, Finset.mem_Icc]; exact ⟨hs.le, le_refl _⟩
  have h1 := le_maxContent hmem
  have h2 := maxContent_mem (h.nonempty hs)
  rw [h.contents_eq hs, Finset.mem_Icc] at h2
  omega

theorem diagLo_eq (h : DiagSet S k₀ k₁ lo hi) (hs : DiagShape k₀ k₁ lo hi) {k : ℤ} (h1 : k₀ ≤ k)
    (h2 : k ≤ k₁) : diagLo S k = lo k := by
  apply diagLo_eq_of ((h (lo k) k).mpr ⟨h1, h2, le_refl _, hs.ne k h1 h2⟩)
  intro i hi'
  exact ((h i k).mp hi').2.2.1

theorem diagHi_eq (h : DiagSet S k₀ k₁ lo hi) (hs : DiagShape k₀ k₁ lo hi) {k : ℤ} (h1 : k₀ ≤ k)
    (h2 : k ≤ k₁) : diagHi S k = hi k := by
  apply diagHi_eq_of ((h (hi k) k).mpr ⟨h1, h2, hs.ne k h1 h2, le_refl _⟩)
  intro i hi'
  exact ((h i k).mp hi').2.2.2

theorem hasDiagonalShape (h : DiagSet S k₀ k₁ lo hi) (hs : DiagShape k₀ k₁ lo hi) :
    HasDiagonalShape S := by
  have hc := h.contents_eq hs
  have hlo := fun k (h1 : k₀ ≤ k) (h2 : k ≤ k₁) => h.diagLo_eq hs h1 h2
  have hhi := fun k (h1 : k₀ ≤ k) (h2 : k ≤ k₁) => h.diagHi_eq hs h1 h2
  refine ⟨h.nonempty hs, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy k hk
    rw [Finset.mem_Icc] at hk
    have h1 := content_mem_contents hx
    have h2 := content_mem_contents hy
    rw [hc, Finset.mem_Icc] at h1 h2 ⊢
    omega
  · intro x hx y hy hxy i hi'
    rw [Finset.mem_Icc] at hi'
    have hx' := h.mem_iff.mp hx
    have hy' := h.mem_iff.mp hy
    rw [h]
    rw [← hxy] at hy'
    refine ⟨hx'.1, hx'.2.1, ?_, ?_⟩ <;> omega
  · intro k hk hk1
    rw [hc, Finset.mem_Icc] at hk hk1
    simp only [bitA, bitB, hlo k hk.1 hk.2, hlo (k - 1) hk1.1 hk1.2, hhi k hk.1 hk.2,
      hhi (k - 1) hk1.1 hk1.2, Finset.mem_insert, Finset.mem_singleton]
    exact ⟨hs.stepLo k (by omega) hk.2, hs.stepHi k (by omega) hk.2⟩
  · intro k hk hend
    rw [hc, Finset.mem_Icc] at hk
    rw [hlo k hk.1 hk.2, hhi k hk.1 hk.2]
    rcases hend with h1 | h1
    · have : k = k₀ := by
        by_contra hne
        apply h1
        rw [hc, Finset.mem_Icc]
        omega
      rw [this]; exact hs.endLo
    · have : k = k₁ := by
        by_contra hne
        apply h1
        rw [hc, Finset.mem_Icc]
        omega
      rw [this]; exact hs.endHi

theorem isConnectedSkew (h : DiagSet S k₀ k₁ lo hi) (hs : DiagShape k₀ k₁ lo hi) :
    IsConnectedSkew S :=
  isConnectedSkew_iff_diagonal.mpr (h.hasDiagonalShape hs)

theorem sw_eq (h : DiagSet S k₀ k₁ lo hi) (hs : DiagShape k₀ k₁ lo hi) :
    sw S = (lo k₀, lo k₀ + k₀) := by
  unfold sw
  rw [h.minContent_eq hs, h.diagLo_eq hs (le_refl _) hs.le]

theorem ne_eq (h : DiagSet S k₀ k₁ lo hi) (hs : DiagShape k₀ k₁ lo hi) :
    ne S = (lo k₁, lo k₁ + k₁) := by
  unfold ne
  rw [h.maxContent_eq hs, h.diagLo_eq hs hs.le (le_refl _)]

theorem span_eq (h : DiagSet S k₀ k₁ lo hi) (hs : DiagShape k₀ k₁ lo hi) :
    (span S : ℤ) = k₁ - k₀ + 1 := by
  have := span_eq_of_isConnectedSkew (h.isConnectedSkew hs)
  rw [h.minContent_eq hs, h.maxContent_eq hs] at this
  exact this

end DiagSet

end GluingCore
