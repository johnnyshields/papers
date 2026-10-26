import SkewGluing.OlsonHarris.Plan.CornerCase.OuterWindows

/-!
# Heights of border strips

Formalizes `shields-2026-skew-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `def:gluing-graph`): the height of a ribbon removable on the right or on the left,
read off the diagonals of the ambient diagram (thesis Lemma 5.2.9, used in thesis Lemma 5.5.11
of `OlsonHarris2024HopfApplications`).

The border strip `windowRibbon X n₀ N` of a connected skew diagram `X` has one cell on each of the
diagonals `n₀, …, n₀ + N - 1`, the last cell `h_n` of the diagonal; its rows are the integers
between `h_{n₀ + N - 1}` and `h_{n₀}`, so its height is `h_{n₀} - h_{n₀ + N - 1}`
(`ribbonHeight_windowRibbon`).  A ribbon removable on the left from `D` is the rotation of such a
strip of `D*`, hence its height is the difference of the first rows `ℓ` of its end diagonals
(`ribbonHeight_of_mem_leftRibbons`).

Sorry-free.
-/

namespace SkewGluing

namespace Plan

namespace Corner

namespace CSign

variable {X : Diagram}

theorem mem_rowSet_iff {D : Diagram} {r : ℤ} : r ∈ rowSet D ↔ ∃ y ∈ D, y.1 = r := by
  unfold rowSet
  rw [Finset.mem_image]

/-- The rows of a border strip are the integers between the last rows of its end diagonals. -/
theorem rowSet_windowRibbon (hX : IsConnectedSkew X) {n0 : ℤ} {N : ℕ} (hN : 0 < N)
    (h0 : n0 ∈ contents X) (h1 : n0 + N - 1 ∈ contents X) :
    rowSet (windowRibbon X n0 N) = Finset.Icc (diagHi X (n0 + N - 1)) (diagHi X n0) := by
  have hs := isConnectedSkew_iff_diagonal.mp hX
  have hcont : ∀ k, n0 ≤ k → k ≤ n0 + N - 1 → k ∈ contents X :=
    fun k hk1 hk2 => hs.between h0 h1 hk1 hk2
  have step : ∀ k, n0 ≤ k → k + 1 ≤ n0 + N - 1 →
      diagHi X k - diagHi X (k + 1) = 0 ∨ diagHi X k - diagHi X (k + 1) = 1 := by
    intro k hk1 hk2
    have := (hs.2.2.2.1 (k + 1) (hcont _ (by omega) hk2) (by simpa using hcont k hk1 (by omega))).2
    simpa [bitB] using this
  -- discrete intermediate value property
  have ivt : ∀ K : ℕ, n0 + K ≤ n0 + N - 1 → ∀ r, diagHi X (n0 + K) ≤ r → r ≤ diagHi X n0 →
      ∃ k : ℤ, n0 ≤ k ∧ k ≤ n0 + K ∧ diagHi X k = r := by
    intro K
    induction K with
    | zero =>
      intro _ r hr1 hr2
      exact ⟨n0, le_rfl, by simp, by simp at hr1; omega⟩
    | succ K ih =>
      intro hK r hr1 hr2
      have hst := step (n0 + K) (by omega) (by push_cast at hK; omega)
      by_cases hr : diagHi X (n0 + K) ≤ r
      · obtain ⟨k, a1, a2, a3⟩ := ih (by omega) r hr hr2
        exact ⟨k, a1, by push_cast; omega, a3⟩
      · have hc : ((K + 1 : ℕ) : ℤ) = K + 1 := by push_cast; ring
        rw [hc] at hr1 hK ⊢
        refine ⟨n0 + (K + 1), by omega, by omega, ?_⟩
        rw [← add_assoc] at hr1 ⊢
        omega
  ext r
  rw [mem_rowSet_iff, Finset.mem_Icc]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' := mem_windowRibbon.mp hy
    rw [hy'.2.2]
    have ma := hs.diagHi_anti (hcont n0 le_rfl (by omega)) (hcont _ hy'.1 (by omega)) hy'.1
    have mb := hs.diagHi_anti (hcont _ hy'.1 (by omega)) (hcont _ (by omega) le_rfl)
      (by omega : content y ≤ n0 + N - 1)
    exact ⟨mb.1, ma.1⟩
  · rintro ⟨hr1, hr2⟩
    obtain ⟨k, a1, a2, a3⟩ := ivt (N - 1) (by omega) r (by
      have : n0 + ((N - 1 : ℕ) : ℤ) = n0 + N - 1 := by omega
      rw [this]; exact hr1) hr2
    refine ⟨(diagHi X k, diagHi X k + k), mem_windowRibbon.mpr ⟨?_, ?_, ?_⟩, a3⟩
    · simp only [content]; omega
    · simp only [content]; omega
    · simp only [content]
      congr 1
      ring

/-- **The height of a border strip.**  `ht = h_{n₀} - h_{n₀ + N - 1}`. -/
theorem ribbonHeight_windowRibbon (hX : IsConnectedSkew X) {n0 : ℤ} {N : ℕ} (hN : 0 < N)
    (h0 : n0 ∈ contents X) (h1 : n0 + N - 1 ∈ contents X) :
    (ribbonHeight (windowRibbon X n0 N) : ℤ) = diagHi X n0 - diagHi X (n0 + N - 1) := by
  have hs := isConnectedSkew_iff_diagonal.mp hX
  have hanti := hs.diagHi_anti h0 h1 (by omega)
  unfold ribbonHeight numRows
  rw [rowSet_windowRibbon hX hN h0 h1, Int.card_Icc]
  have : 0 < (diagHi X n0 + 1 - diagHi X (n0 + N - 1)).toNat := by omega
  omega

/-- A ribbon of size `m` removable on the left from `D` has the least content `μ + j` of a window
`Aext_j = 1`, `Aext_{j+m} = 0`; its height is the difference of the first rows of the end
diagonals, `ℓ_{μ+j} - ℓ_{μ+j+m-1}`. -/
theorem ribbonHeight_of_mem_leftRibbons {D : Diagram} (hD : IsConnectedSkew D) {m : ℕ}
    (hm : 0 < m) {A : Diagram} (hA : A ∈ leftRibbons D m) {n0 : ℤ} (hn0 : minContent A = n0) :
    (ribbonHeight A : ℤ) = diagLo D n0 - diagLo D (n0 + m - 1) := by
  have hDr := isConnectedSkew_rotate hD
  have hAr : rotate A ∈ rightRibbons (rotate D) m :=
    rotate_mem_rightRibbons (X := rotate D) (by rwa [rotate_rotate])
  obtain ⟨j, h1', h2, -, -, hw⟩ := right_window_D_exists hDr hm hAr
  have hne : (rotate D).Nonempty := hDr.2.1
  have hsp : span (rotate D) = span D := span_rotate
  have hcR : ∀ k, k ∈ contents (rotate D) ↔
      minContent (rotate D) ≤ k ∧ k < minContent (rotate D) + span (rotate D) :=
    fun k => contents_iff hDr
  have hmin : minContent (rotate D) + j ∈ contents (rotate D) := (hcR _).mpr ⟨by omega, by omega⟩
  have hmax : minContent (rotate D) + j + m - 1 ∈ contents (rotate D) :=
    (hcR _).mpr ⟨by omega, by omega⟩
  have hht := ribbonHeight_windowRibbon hDr hm hmin (by
    have : minContent (rotate D) + j + m - 1 = minContent (rotate D) + j + m - 1 := rfl
    exact hmax)
  rw [← hw] at hht
  have hrh : ribbonHeight (rotate A) = ribbonHeight A := by
    have hrows : rowSet (rotate A) = (rowSet A).image (fun a : ℤ => -a) := by
      ext r
      rw [mem_rowSet_iff, Finset.mem_image]
      constructor
      · rintro ⟨y, hy, rfl⟩
        rw [mem_rotate] at hy
        exact ⟨(-y).1, mem_rowSet_iff.mpr ⟨-y, hy, rfl⟩, by simp⟩
      · rintro ⟨a, ha, rfl⟩
        obtain ⟨y, hy, rfl⟩ := mem_rowSet_iff.mp ha
        exact ⟨-y, mem_rotate.mpr (by simpa using hy), by simp⟩
    unfold ribbonHeight numRows
    rw [hrows, Finset.card_image_of_injective _ neg_injective]
  rw [← hrh]
  rw [hht, diagHi_rotate, diagHi_rotate]
  have hmc := minContent_of_rotate_window hD hm hw
  have hne' : D.Nonempty := hD.2.1
  have hmaxD : maxContent D = minContent D + span D - 1 := by
    have := span_eq_of_isConnectedSkew hD
    omega
  have e1 : -(minContent (rotate D) + j + (m : ℤ) - 1) = n0 := by
    rw [minContent_rotate hne', hmaxD, ← hn0, hmc]
    ring
  have e2 : -(minContent (rotate D) + j) = n0 + m - 1 := by
    rw [← e1]; ring
  rw [e1, e2]
  ring

/-! ### Checked examples -/

section Examples

/-- The border strip of `(3, 3, 2) / (1, 1)` on the diagonals `0, 1, 2` has two rows, and the
heights of its end diagonals differ by one. -/
example : ribbonHeight (windowRibbon (skewOf [3, 3, 2] [1, 1]) 0 3) = 1 ∧
    diagHi (skewOf [3, 3, 2] [1, 1]) 0 - diagHi (skewOf [3, 3, 2] [1, 1]) 2 = 1 := by
  decide +kernel

/-- A ribbon of size `2` removable on the left from `(4, 3, 3) / (2, 1)`: its height is the
difference of the first rows of its end diagonals. -/
example : ∀ A ∈ leftRibbons (skewOf [4, 3, 3] [2, 1]) 2,
    ribbonHeight A = (diagLo (skewOf [4, 3, 3] [2, 1]) (minContent A) -
      diagLo (skewOf [4, 3, 3] [2, 1]) (minContent A + 1)).toNat := by
  decide +kernel

end Examples

end CSign

end Corner

end Plan

end SkewGluing
