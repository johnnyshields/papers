import SkewBase.ChartSize

/-!
# Diagrams from their diagonals: `lem:heights`

Formalizes `shields-2026-skew-base-computational.tex`, «The geometry of a chart and two complete
searches» (`sec:roots`): `lem:heights`.

`diagramOfRows m lo hi` is the diagram whose diagonal of content `t ∈ [0, m)` occupies the rows
`[lo t, hi t]`.  `HeightRecursion m h D` is the recursion of `lem:heights`: content `0` is the cell
`(0, 0)`, and if content `c` occupies the rows `[α, α + h(c) - 1]` then content `c + 1` occupies
`[α', α' + h(c + 1) - 1]` with `α' ∈ {α - 1, α}` and `α' + h(c + 1) - 1 ∈ {α + h(c) - 2,
α + h(c) - 1}`.  `heightRecursion_of_isConnectedSkew` shows that every connected skew diagram
with `sw D = (0, 0)` and the contents' heights `h` arises from it, and `eq_diagramOfRows` that it
is `diagramOfRows` of its own diagonals.

Sorry-free.
-/

namespace SkewBase

open SkewGluing

/-- The least content of the outer carries one cell. -/
theorem height_zero {D : Diagram} (hD : IsConnectedSkew D) (h0 : minContent D = 0) :
    height D 0 = 1 := by
  have hs := isConnectedSkew_iff_diagonal.mp hD
  have hm : (0 : ℤ) ∈ contents D := by rw [← h0]; exact minContent_mem hs.1
  have := hs.2.2.2.2 0 hm (Or.inl (fun hm' => by have := minContent_le hm'; omega))
  unfold height
  omega

/-- The diagram whose diagonal of content `t ∈ [0, m)` occupies the rows `[lo t, hi t]`. -/
def diagramOfRows (m : ℕ) (lo hi : ℤ → ℤ) : Diagram :=
  (Finset.Ico (0 : ℤ) m).biUnion fun t => (Finset.Icc (lo t) (hi t)).image fun i => (i, i + t)

theorem mem_diagramOfRows {m : ℕ} {lo hi : ℤ → ℤ} {i j : ℤ} :
    (i, j) ∈ diagramOfRows m lo hi ↔ 0 ≤ j - i ∧ j - i < m ∧ lo (j - i) ≤ i ∧ i ≤ hi (j - i) := by
  unfold diagramOfRows
  simp only [Finset.mem_biUnion, Finset.mem_Ico, Finset.mem_image, Finset.mem_Icc, Prod.mk.injEq]
  constructor
  · rintro ⟨t, ⟨h1, h2⟩, k, ⟨h3, h4⟩, rfl, rfl⟩
    refine ⟨by omega, by omega, ?_, ?_⟩ <;> simpa using ‹_›
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨j - i, ⟨h1, h2⟩, i, ⟨h3, h4⟩, rfl, by ring⟩

theorem diagramOfRows_congr {m : ℕ} {lo hi lo' hi' : ℤ → ℤ}
    (h : ∀ t : ℤ, 0 ≤ t → t < (m : ℤ) → lo t = lo' t ∧ hi t = hi' t) :
    diagramOfRows m lo hi = diagramOfRows m lo' hi' := by
  ext ⟨i, j⟩
  rw [mem_diagramOfRows, mem_diagramOfRows]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    have := h _ h1 h2
    exact ⟨h1, h2, this.1 ▸ h3, this.2 ▸ h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    have := h _ h1 h2
    exact ⟨h1, h2, this.1 ▸ h3, this.2 ▸ h4⟩

/-- A connected skew diagram with least content `0` is the diagram of its own diagonals. -/
theorem eq_diagramOfRows {D : Diagram} (hD : IsConnectedSkew D) (h0 : minContent D = 0) :
    D = diagramOfRows (span D) (diagLo D) (diagHi D) := by
  have hs := isConnectedSkew_iff_diagonal.mp hD
  have hsp := span_eq_of_isConnectedSkew hD
  ext ⟨i, j⟩
  rw [mem_diagramOfRows]
  have hj : j = i + (j - i) := by ring
  constructor
  · intro hx
    have hc := content_mem_contents hx
    rw [hs.mem_contents_iff] at hc
    simp only [content] at hc
    refine ⟨by omega, by omega, diagLo_le hx rfl, le_diagHi hx rfl⟩
  · rintro ⟨h1, h2, h3, h4⟩
    rw [hj, hs.mem_iff]
    refine ⟨?_, h3, h4⟩
    rw [hs.mem_contents_iff]
    omega

/-- The recursion of `lem:heights`. -/
def HeightRecursion (m : ℕ) (h : ℤ → ℤ) (D : Diagram) : Prop :=
  ∃ α : ℤ → ℤ, α 0 = 0 ∧ h 0 = 1 ∧
    (∀ c : ℤ, 0 ≤ c → c + 1 < m →
      (α (c + 1) = α c - 1 ∨ α (c + 1) = α c) ∧
      (α (c + 1) + h (c + 1) - 1 = α c + h c - 2 ∨
        α (c + 1) + h (c + 1) - 1 = α c + h c - 1)) ∧
    D = diagramOfRows m α (fun c => α c + h c - 1)

/-- **`lem:heights`.**  Every connected skew diagram with `sw D = (0, 0)` whose contents carry
the heights `h` arises from the recursion. -/
theorem heightRecursion_of_isConnectedSkew {D : Diagram} (hD : IsConnectedSkew D)
    (hsw : sw D = 0) {h : ℤ → ℤ} (hh : ∀ c : ℤ, 0 ≤ c → c < (span D : ℤ) → h c = height D c) :
    HeightRecursion (span D) h D := by
  have hs := isConnectedSkew_iff_diagonal.mp hD
  have hsp := span_eq_of_isConnectedSkew hD
  have h1 : diagLo D (minContent D) = 0 := by
    have := congrArg Prod.fst hsw
    simpa [sw] using this
  have h2 : minContent D = 0 := by
    have := congrArg Prod.snd hsw
    simp only [sw] at this
    simpa [h1] using this
  rw [h2] at h1
  have hmax : (0 : ℤ) < span D := by
    have := minContent_le (maxContent_mem hs.1)
    omega
  refine ⟨diagLo D, h1, ?_, ?_, ?_⟩
  · rw [hh 0 le_rfl hmax]; exact height_zero hD h2
  · intro c hc hc1
    have hcm : c + 1 ∈ contents D := by rw [hs.mem_contents_iff]; omega
    have hcm' : c + 1 - 1 ∈ contents D := by rw [hs.mem_contents_iff]; omega
    have hb := hs.2.2.2.1 (c + 1) hcm hcm'
    simp only [bitA, bitB, Finset.mem_insert, Finset.mem_singleton, add_sub_cancel_right] at hb
    rw [hh c hc (by omega), hh (c + 1) (by omega) hc1]
    unfold height
    omega
  · refine (eq_diagramOfRows hD h2).trans ?_
    apply diagramOfRows_congr
    intro t ht1 ht2
    refine ⟨rfl, ?_⟩
    rw [hh t ht1 ht2]
    unfold height
    ring

/-- The diagram of rows with a single cell on content `0` at `(0, 0)` has `sw = (0, 0)`. -/
theorem sw_diagramOfRows {m : ℕ} (hm : 0 < m) {lo hi : ℤ → ℤ} (hlo : lo 0 = 0) (hhi : hi 0 = 0) :
    sw (diagramOfRows m lo hi) = 0 := by
  set D := diagramOfRows m lo hi with hDdef
  have h00 : ((0 : ℤ), (0 : ℤ) + 0) ∈ D := by
    rw [hDdef, zero_add, mem_diagramOfRows]
    simp [hlo, hhi, hm]
  have hc0 : (0 : ℤ) ∈ contents D := mem_contents_iff.mpr ⟨0, h00⟩
  have hmin : minContent D = 0 := by
    apply minContent_eq_of hc0
    intro k hk
    obtain ⟨i, hi⟩ := mem_contents_iff.mp hk
    rw [hDdef, mem_diagramOfRows] at hi
    omega
  have hlow : diagLo D 0 = 0 := by
    apply diagLo_eq_of h00
    intro i hi
    rw [hDdef, mem_diagramOfRows] at hi
    simp only [add_zero, sub_self] at hi
    omega
  simp only [sw, hmin, hlow]
  rfl

end SkewBase
