/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.InteriorBlockIntervals

/-!
# Cell diagrams of original interior intervals

Supports `shields-2026-skew-corner-descent.tex`, «Equal windows and the determinant defect»
(`sec:normal-chart`, `lem:actual-elimination`, `eq:minor-shape`). The connected profile of
an actual block is identified with its original cell interval by an explicit translation.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- Actual complementary cells in a consecutive row interval. -/
def interiorSliceCells {n : ℕ} (P : Profile n) (a m : ℕ) (h : a + m < n) : Diagram :=
  Finset.univ.biUnion fun j : Fin (m + 1) =>
    (Finset.Ico (P.zeta (interiorSliceIndex a m h j).castSucc +
      (interiorSliceIndex a m h j : ℕ))
      (P.xi (interiorSliceIndex a m h j).succ + (interiorSliceIndex a m h j : ℕ))).image
      fun b => (((interiorSliceIndex a m h j : ℕ) : ℤ), b)

theorem mem_interiorSliceCells {n : ℕ} (P : Profile n) (a m : ℕ) (h : a + m < n)
    (r b : ℤ) :
    (r, b) ∈ interiorSliceCells P a m h ↔ ∃ j : Fin (m + 1),
      ((interiorSliceIndex a m h j : ℕ) : ℤ) = r ∧
      P.zeta (interiorSliceIndex a m h j).castSucc +
        (interiorSliceIndex a m h j : ℕ) ≤ b ∧
      b < P.xi (interiorSliceIndex a m h j).succ + (interiorSliceIndex a m h j : ℕ) := by
  simp only [interiorSliceCells, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_image, Finset.mem_Ico, Prod.mk.injEq]
  constructor
  · rintro ⟨j, k, hk, hr, rfl⟩
    exact ⟨j, hr, hk⟩
  · rintro ⟨j, hr, hk⟩
    exact ⟨j, b, hk, hr, rfl⟩

/-- The normalized profile and the original interval are exactly the same translated cells. -/
theorem interiorSliceCells_eq_translate {n : ℕ} (P : Profile n) (a m : ℕ) (h : a + m < n)
    (hblock : ∀ i, interiorBlock P (interiorSliceIndex a m h i) =
      interiorBlock P (interiorSliceIndex a m h 0))
    (hne : P.zeta (interiorSliceIndex a m h 0).castSucc <
      P.xi (interiorSliceIndex a m h 0).succ) :
    interiorSliceCells P a m h = translate
      ((a : ℤ), P.zeta (interiorSliceIndex a m h (Fin.last m)).castSucc + a)
      (interiorSliceProfile P a m h hblock hne).cells := by
  obtain ⟨hxi, hzeta⟩ := interiorSliceProfile_beta P a m h hblock hne
  ext ⟨r, b⟩
  rw [mem_interiorSliceCells, mem_translate]
  change _ ↔ (r - a, b -
    (P.zeta (interiorSliceIndex a m h (Fin.last m)).castSucc + a)) ∈
      (interiorSliceProfile P a m h hblock hne).cells
  rw [Profile.mem_cells]
  rw [hxi, hzeta]
  simp only [interiorSliceBetaPair, interiorSliceIndex, Nat.cast_add]
  constructor
  · rintro ⟨j, hr, hlo, hhi⟩
    exact ⟨j, by omega, by omega, by omega⟩
  · rintro ⟨j, hr, hlo, hhi⟩
    exact ⟨j, by omega, by omega, by omega⟩

/-- Every actual interval is a subdiagram of the original southeast interior. -/
theorem interiorSliceCells_subset {n : ℕ} (P : Profile n) (a m : ℕ) (h : a + m < n) :
    interiorSliceCells P a m h ⊆ diagramInterior P.cells := by
  rintro ⟨r, b⟩ hx
  obtain ⟨j, hr, hlo, hhi⟩ := (mem_interiorSliceCells P a m h r b).mp hx
  exact (P.mem_interior_cells r b).mpr ⟨interiorSliceIndex a m h j, hr, hlo, hhi⟩

/-- The interval contains every original interior cell in its row range, not merely a subset. -/
theorem interiorSliceCells_eq_filter {n : ℕ} (P : Profile n) (a m : ℕ) (h : a + m < n) :
    interiorSliceCells P a m h =
      (diagramInterior P.cells).filter (fun x => (a : ℤ) ≤ x.1 ∧ x.1 ≤ ((a + m : ℕ) : ℤ)) := by
  ext ⟨r, b⟩
  rw [Finset.mem_filter]
  constructor
  · intro hx
    obtain ⟨j, hr, hlo, hhi⟩ := (mem_interiorSliceCells P a m h r b).mp hx
    refine ⟨interiorSliceCells_subset P a m h hx, ?_⟩
    have hj := j.isLt
    simp only [interiorSliceIndex, Nat.cast_add] at hr
    dsimp only
    constructor <;> omega
  · rintro ⟨hx, ha, hb⟩
    obtain ⟨i, hr, hlo, hhi⟩ := (P.mem_interior_cells r b).mp hx
    have hia : a ≤ i.val := by dsimp only at ha hb; omega
    have hib : i.val ≤ a + m := by dsimp only at ha hb; omega
    let j : Fin (m + 1) := ⟨i.val - a, by omega⟩
    have hj : interiorSliceIndex a m h j = i := by
      apply Fin.ext
      simp only [interiorSliceIndex, j]
      omega
    exact (mem_interiorSliceCells P a m h r b).mpr ⟨j, by rw [hj]; exact hr,
      by rw [hj]; exact hlo, by rw [hj]; exact hhi⟩

/-- The produced connected profile proves connectivity of the full original cell interval. -/
theorem interiorSliceCells_connected {n : ℕ} (P : Profile n) (a m : ℕ) (h : a + m < n)
    (hblock : ∀ i, interiorBlock P (interiorSliceIndex a m h i) =
      interiorBlock P (interiorSliceIndex a m h 0))
    (hne : P.zeta (interiorSliceIndex a m h 0).castSucc <
      P.xi (interiorSliceIndex a m h 0).succ) :
    IsConnectedSkew (interiorSliceCells P a m h) := by
  rw [interiorSliceCells_eq_translate P a m h hblock hne]
  exact isConnectedSkew_translate _ (interiorSliceProfile P a m h hblock hne).isConnectedSkew_cells

end SkewCornerDescent.Matrix
