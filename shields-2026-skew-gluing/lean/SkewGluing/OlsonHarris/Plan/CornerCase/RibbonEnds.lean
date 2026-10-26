import SkewGluing.OlsonHarris.Plan.Defs

/-!
# The ends of a ribbon removable on the right

Formalizes `shields-2026-skew-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `def:gluing-graph`): the border-strip description of the ribbons removable on the
right used in the proofs of thesis Lemmas 5.5.2 and 5.5.7 (iii) (`OlsonHarris2024HopfApplications`).

A ribbon `Y` of size `N` removable on the right from a connected skew diagram `X` has one cell on
each of `N` consecutive diagonals `[n₀, n₀ + N - 1]`, the last cell of `X` on that diagonal.  Its
first cell has no neighbor to the south in `X` and its last cell none to the east.  In terms of
the last rows `h_n = diagHi X n` of the diagonals: `n₀` is the least content of `X` or
`h_{n₀ - 1} = h_{n₀}`, and `n₀ + N - 1` is the greatest content of `X` or
`h_{n₀ + N - 1} - h_{n₀ + N} = 1`.

Sorry-free.
-/

namespace SkewGluing

namespace Plan

namespace Corner

/-- The border strip of `X` on the diagonals `n₀, …, n₀ + N - 1`: the last cell of each diagonal. -/
def windowRibbon (X : Diagram) (n0 : ℤ) (N : ℕ) : Diagram :=
  (Finset.Ico n0 (n0 + N)).image fun j => (diagHi X j, diagHi X j + j)

theorem mem_windowRibbon {X : Diagram} {n0 : ℤ} {N : ℕ} {y : ℤ × ℤ} :
    y ∈ windowRibbon X n0 N ↔ n0 ≤ content y ∧ content y < n0 + N ∧ y.1 = diagHi X (content y) := by
  unfold windowRibbon
  rw [Finset.mem_image]
  constructor
  · rintro ⟨j, hj, rfl⟩
    rw [Finset.mem_Ico] at hj
    simp only [content]
    refine ⟨by omega, by omega, ?_⟩
    have : diagHi X (diagHi X j + j - diagHi X j) = diagHi X j := by simp
    rw [this]
  · rintro ⟨h1, h2, h3⟩
    refine ⟨content y, Finset.mem_Ico.mpr ⟨h1, h2⟩, ?_⟩
    obtain ⟨a, b⟩ := y
    simp only [content] at h3 ⊢
    rw [← h3]
    ext <;> simp

theorem card_windowRibbon (X : Diagram) (n0 : ℤ) (N : ℕ) : (windowRibbon X n0 N).card = N := by
  unfold windowRibbon
  rw [Finset.card_image_of_injective]
  · simp
  · intro i j h
    simp only [Prod.mk.injEq] at h
    omega

/-- **The ends of a ribbon removable on the right.**  See the module docstring.  The ribbon is
the border strip on the diagonals `n₀, …, n₀ + N - 1`. -/
theorem rightRibbon_endpoints {X Y : Diagram} (hX : IsConnectedSkew X) {N : ℕ} (hN : 0 < N)
    (hY : Y ∈ rightRibbons X N) :
    ∃ n0 : ℤ, n0 ∈ contents X ∧ n0 + N - 1 ∈ contents X ∧
      (n0 - 1 ∉ contents X ∨ diagHi X (n0 - 1) = diagHi X n0) ∧
      (n0 + N ∉ contents X ∨ diagHi X (n0 + N - 1) - diagHi X (n0 + N) = 1) ∧
      Y = windowRibbon X n0 N := by
  have hs := isConnectedSkew_iff_diagonal.mp hX
  obtain ⟨hYX, hcard, hrib, hup⟩ := mem_rightRibbons.mp hY
  have hYne : Y.Nonempty := Finset.card_pos.mp (by omega)
  have hinj : ∀ y ∈ Y, ∀ y' ∈ Y, content y = content y' → y = y' := by
    have h1 : (Y.image content).card = Y.card := by
      have := hrib.2
      unfold span contents at this
      exact this.symm
    exact fun y hy y' hy' h => (Finset.card_image_iff.mp h1) hy hy' h
  -- every cell of `Y` is the last cell of `X` on its diagonal
  have hlast : ∀ y ∈ Y, y.1 = diagHi X (content y) := by
    intro y hy
    obtain ⟨a, b⟩ := y
    have hyX := hYX hy
    have h1 : a ≤ diagHi X (b - a) := le_diagHi hyX rfl
    by_contra hne
    have hlt : a < diagHi X (b - a) := lt_of_le_of_ne h1 (by simpa [content] using hne)
    have hlo : diagLo X (b - a) ≤ a := diagLo_le hyX rfl
    have hz : (a + 1, b + 1) ∈ X := by
      have e : (a + 1, b + 1) = (a + 1, a + 1 + (b - a)) := Prod.ext rfl (by simp only; omega)
      rw [e]
      exact hs.mem_iff.mpr ⟨content_mem_contents hyX, by omega, by omega⟩
    have hzY : (a + 1, b + 1) ∈ Y := hup.2 _ hz (a, b) hy (by simp) (by simp)
    have := hinj _ hzY (a, b) hy (by simp [content])
    simp at this
  have hYs := isConnectedSkew_iff_diagonal.mp hrib.1
  have hspan := span_eq_of_isConnectedSkew hrib.1
  have hspan' : (Y.card : ℤ) = (span Y : ℤ) := by rw [hrib.2]
  have hn1 : maxContent Y = minContent Y + N - 1 := by omega
  obtain ⟨y0, hy0, hy0c⟩ := Finset.mem_image.mp (minContent_mem hYne)
  obtain ⟨y1, hy1, hy1c⟩ := Finset.mem_image.mp (maxContent_mem hYne)
  have hn0X : minContent Y ∈ contents X := hy0c ▸ content_mem_contents (hYX hy0)
  have hn1X : minContent Y + N - 1 ∈ contents X := by
    rw [← hn1, ← hy1c]; exact content_mem_contents (hYX hy1)
  have hYw : Y = windowRibbon X (minContent Y) N := by
    refine Finset.eq_of_subset_of_card_le (fun y hy => ?_) (by rw [card_windowRibbon]; omega)
    rw [mem_windowRibbon]
    have h1 := minContent_le (content_mem_contents hy)
    have h2 := le_maxContent (content_mem_contents hy)
    exact ⟨h1, by omega, hlast y hy⟩
  refine ⟨minContent Y, hn0X, hn1X, ?_, ?_, hYw⟩
  · by_cases hm : minContent Y - 1 ∈ contents X
    · right
      have hb := (hs.2.2.2.1 _ hn0X (by simpa using hm)).2
      simp only [bitB, Finset.mem_insert, Finset.mem_singleton] at hb
      by_contra hne
      have h1 : diagHi X (minContent Y - 1 - 1 + 1) = diagHi X (minContent Y - 1) := by
        congr 1; ring
      have hr0 := hlast y0 hy0
      rw [hy0c] at hr0
      obtain ⟨a, b⟩ := y0
      simp only [content] at hy0c hr0
      have hz : (a + 1, b) ∈ X := by
        have e : (a + 1, b) = (a + 1, a + 1 + (minContent Y - 1)) := Prod.ext rfl
          (by simp only; omega)
        rw [e]
        exact hs.mem_iff.mpr ⟨hm, by have := diagLo_le_diagHi hm; omega, by omega⟩
      have hzY : (a + 1, b) ∈ Y := hup.2 _ hz (a, b) hy0 (by simp) (by simp)
      have := minContent_le (content_mem_contents hzY)
      simp only [content] at this
      omega
    · left; exact hm
  · by_cases hm : minContent Y + N ∈ contents X
    · right
      have hb := (hs.2.2.2.1 _ hm (by simpa using hn1X)).2
      simp only [bitB, Finset.mem_insert, Finset.mem_singleton] at hb
      by_contra hne
      have hr1 := hlast y1 hy1
      rw [hy1c, hn1] at hr1
      obtain ⟨a, b⟩ := y1
      simp only [content] at hy1c hr1
      have hz : (a, b + 1) ∈ X := by
        have e : (a, b + 1) = (a, a + (minContent Y + N)) := Prod.ext rfl (by simp only; omega)
        rw [e]
        exact hs.mem_iff.mpr ⟨hm, by have := diagLo_le_diagHi hm; omega, by omega⟩
      have hzY : (a, b + 1) ∈ Y := hup.2 _ hz (a, b) hy1 (by simp) (by simp)
      have := le_maxContent (content_mem_contents hzY)
      simp only [content] at this
      omega
    · left; exact hm

end Corner

end Plan

end SkewGluing
