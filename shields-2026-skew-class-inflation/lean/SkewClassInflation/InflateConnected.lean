/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.CellInflation

/-!
# Inflation of an arbitrary connected skew diagram

Supports `lem:inflate-chart` in `shields-2026-skew-class-inflation.tex`.  Cell inflation
\(D\mapsto D\cup(D+(0,1))\) of a connected skew diagram \(D\) with contents
\([c_0,c_1]\) is a connected skew diagram with contents \([c_0,c_1+1]\) whose diagonal of
content \(k\) is the row interval \([\ell_k,h_{k-1}]\).  Sorry-free.
-/

namespace SkewClassInflation

open SkewGluing (Diagram IsConnectedSkew diagLo diagHi contents minContent maxContent)

theorem mem_inflateCells {D : Diagram} {a b : ℤ} :
    (a, b) ∈ inflateCells D ↔ (a, b) ∈ D ∨ (a, b - 1) ∈ D := by
  unfold inflateCells
  rw [Finset.mem_union, SkewGluing.mem_translate]
  simp only [Prod.mk_sub_mk, sub_zero]

variable {D : Diagram}

/-- The inflation of a connected skew diagram is connected skew, with the stated diagonals. -/
theorem inflateCells_diagonals (hD : IsConnectedSkew D) :
    IsConnectedSkew (inflateCells D) ∧
      ∀ i k : ℤ, (i, i + k) ∈ inflateCells D ↔
        minContent D ≤ k ∧ k ≤ maxContent D + 1 ∧
          diagLo D (min k (maxContent D)) ≤ i ∧
          i ≤ diagHi D (max (k - 1) (minContent D)) := by
  have hs := SkewGluing.isConnectedSkew_iff_diagonal.mp hD
  have hne : D.Nonempty := hs.1
  have hce := hs.contents_eq
  set c0 := minContent D with hc0
  set c1 := maxContent D with hc1
  have hc01 : c0 ≤ c1 := SkewGluing.minContent_le (SkewGluing.maxContent_mem hne)
  have hmem : ∀ i k : ℤ, (i, i + k) ∈ D ↔ c0 ≤ k ∧ k ≤ c1 ∧ diagLo D k ≤ i ∧ i ≤ diagHi D k := by
    intro i k
    rw [hs.mem_iff, hce, Finset.mem_Icc]
    tauto
  have hLH : ∀ k, c0 ≤ k → k ≤ c1 → diagLo D k ≤ diagHi D k := fun k h1 h2 =>
    SkewGluing.diagLo_le_diagHi (by rw [hce]; exact Finset.mem_Icc.mpr ⟨h1, h2⟩)
  have hcm : ∀ k, c0 ≤ k → k ≤ c1 → k ∈ contents D := fun k h1 h2 => by
    rw [hce]; exact Finset.mem_Icc.mpr ⟨h1, h2⟩
  have hLanti : ∀ k, c0 < k → k ≤ c1 →
      diagLo D k ≤ diagLo D (k - 1) ∧ diagLo D (k - 1) ≤ diagLo D k + 1 := by
    intro k h1 h2
    have := hs.diagLo_anti (a := k - 1) (b := k) (hcm _ (by omega) (by omega)) (hcm _ h1.le h2)
      (by omega)
    constructor <;> omega
  have hHanti : ∀ k, c0 < k → k ≤ c1 →
      diagHi D k ≤ diagHi D (k - 1) ∧ diagHi D (k - 1) ≤ diagHi D k + 1 := by
    intro k h1 h2
    have := hs.diagHi_anti (a := k - 1) (b := k) (hcm _ (by omega) (by omega)) (hcm _ h1.le h2)
      (by omega)
    constructor <;> omega
  have hrows : ∀ i k : ℤ, (i, i + k) ∈ inflateCells D ↔
      c0 ≤ k ∧ k ≤ c1 + 1 ∧ diagLo D (min k c1) ≤ i ∧ i ≤ diagHi D (max (k - 1) c0) := by
    intro i k
    rw [show i + k = i + k from rfl, mem_inflateCells, show i + k - 1 = i + (k - 1) by ring,
      hmem, hmem]
    constructor
    · rintro (⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩)
      · refine ⟨h1, by omega, ?_, ?_⟩
        · rw [min_eq_left h2]; exact h3
        · by_cases hk : c0 < k
          · rw [max_eq_left (by omega)]
            exact h4.trans (hHanti k hk h2).1
          · have : k = c0 := by omega
            subst this
            rw [max_eq_right (by omega)]; exact h4
      · refine ⟨by omega, by omega, ?_, ?_⟩
        · by_cases hk : k ≤ c1
          · rw [min_eq_left hk]
            exact (hLanti k (by omega) hk).1.trans h3
          · have : k = c1 + 1 := by omega
            rw [min_eq_right (by omega), show c1 = k - 1 by omega]; exact h3
        · rw [max_eq_left (by omega)]; exact h4
    · rintro ⟨h1, h2, h3, h4⟩
      by_cases hk0 : k = c0
      · subst hk0
        left
        rw [min_eq_left (by omega)] at h3
        rw [max_eq_right (by omega)] at h4
        exact ⟨le_refl _, by omega, h3, h4⟩
      by_cases hk1 : k = c1 + 1
      · subst hk1
        right
        rw [min_eq_right (by omega)] at h3
        rw [max_eq_left (by omega)] at h4
        exact ⟨by omega, by omega, by simpa using h3, by simpa using h4⟩
      · rw [min_eq_left (by omega)] at h3
        rw [max_eq_left (by omega)] at h4
        by_cases hi : i ≤ diagHi D k
        · left; exact ⟨by omega, by omega, h3, hi⟩
        · right
          have := hLanti k (by omega) (by omega)
          have := hLH k (by omega) (by omega)
          exact ⟨by omega, by omega, by omega, h4⟩
  refine ⟨?_, fun i k => (hrows i k).trans (by simp only [hc0, hc1])⟩
  apply SkewGluing.isConnectedSkew_of_rows _ c0 (c1 + 1) (fun k => diagLo D (min k c1))
    (fun k => diagHi D (max (k - 1) c0)) (by omega) hrows
  · intro k h1 h2
    by_cases hk : k ≤ c1
    · have h5 := hLH k h1 hk
      by_cases hk' : c0 < k
      · have h6 := (hHanti k hk' hk).1
        simp only [min_eq_left hk, max_eq_left (show c0 ≤ k - 1 by omega)]
        omega
      · have e : k = c0 := by omega
        rw [e] at h5 ⊢
        have : max (c0 - 1) c0 = c0 := max_eq_right (by omega)
        simp only [min_eq_left hc01, this]
        exact h5
    · have e : k = c1 + 1 := by omega
      rw [e]
      simp only [min_eq_right (show c1 ≤ c1 + 1 by omega), add_sub_cancel_right,
        max_eq_left hc01]
      exact hLH c1 hc01 le_rfl
  · intro k h1 h2
    by_cases hk : k ≤ c1
    · have := hLanti k h1 hk
      simp only [min_eq_left hk, min_eq_left (show k - 1 ≤ c1 by omega)]
      omega
    · have e : k = c1 + 1 := by omega
      rw [e]
      simp only [min_eq_right (show c1 ≤ c1 + 1 by omega), add_sub_cancel_right, min_self]
      omega
  · intro k h1 h2
    by_cases hk : c0 < k - 1
    · have h5 := hHanti (k - 1) hk (by omega)
      simp only [max_eq_left (show c0 ≤ k - 1 - 1 by omega), max_eq_left (show c0 ≤ k - 1 by omega)]
      omega
    · have e : k - 1 = c0 := by omega
      have e2 : max (k - 1 - 1) c0 = c0 := max_eq_right (by omega)
      rw [max_eq_left (show c0 ≤ k - 1 by omega), e2, e]
      omega
  · have e1 : max (c0 - 1) c0 = c0 := max_eq_right (by omega)
    simp only [min_eq_left hc01, e1]
    exact hs.2.2.2.2 c0 (hcm c0 le_rfl hc01) (Or.inl (by
      rw [hce, Finset.mem_Icc]; omega))
  · simp only [min_eq_right (show c1 ≤ c1 + 1 by omega), add_sub_cancel_right,
      max_eq_left hc01]
    exact hs.2.2.2.2 c1 (hcm c1 hc01 le_rfl) (Or.inr (by
      rw [hce, Finset.mem_Icc]; omega))

theorem isConnectedSkew_inflateCells (hD : IsConnectedSkew D) :
    IsConnectedSkew (inflateCells D) := (inflateCells_diagonals hD).1

end SkewClassInflation
