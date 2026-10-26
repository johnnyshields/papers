/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.InteriorBlocks

/-!
# Connected profiles of actual interior blocks

Supports `shields-2026-skew-corner-descent.tex`, «Equal windows and the determinant defect»
(`sec:normal-chart`, `lem:actual-elimination`). A nonempty interval in one produced block
supplies a genuine connected profile. Its normalized Jacobi--Trudi matrix agrees entrywise
with the complete original complementary interval. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- Original indices of an interval of complementary rows. -/
def interiorSliceIndex {n : ℕ} (a m : ℕ) (h : a + m < n) (i : Fin (m + 1)) : Fin n :=
  ⟨a + i.val, by omega⟩

theorem interiorSliceIndex_strictMono {n : ℕ} (a m : ℕ) (h : a + m < n) :
    StrictMono (interiorSliceIndex a m h) := by
  intro i j hij
  change a + i.val < a + j.val
  exact Nat.add_lt_add_left (Fin.lt_def.mp hij) a

/-- Normalized beta lists of an actual nonempty interior interval in one ordered block. -/
def interiorSliceBetaPair {n : ℕ} (P : Profile n) (a m : ℕ) (h : a + m < n)
    (hblock : ∀ i, interiorBlock P (interiorSliceIndex a m h i) =
      interiorBlock P (interiorSliceIndex a m h 0))
    (hne : P.zeta (interiorSliceIndex a m h 0).castSucc <
      P.xi (interiorSliceIndex a m h 0).succ) : Profile.BetaPair m where
  xi i := P.xi (interiorSliceIndex a m h i).succ -
    P.zeta (interiorSliceIndex a m h (Fin.last m)).castSucc
  zeta i := P.zeta (interiorSliceIndex a m h i).castSucc -
    P.zeta (interiorSliceIndex a m h (Fin.last m)).castSucc
  xi_strictAnti := by
    intro i j hij
    have hx := P.xi_strictAnti (show (interiorSliceIndex a m h i).succ <
        (interiorSliceIndex a m h j).succ by
      change a + i.val + 1 < a + j.val + 1
      have hi := Fin.lt_def.mp hij
      omega)
    dsimp only
    omega
  zeta_strictAnti := by
    intro i j hij
    have hs := interiorSliceIndex_strictMono a m h hij
    have hz := P.zeta_strictAnti
      (show (interiorSliceIndex a m h i).castSucc <
          (interiorSliceIndex a m h j).castSucc from hs)
    dsimp only
    omega
  zeta_last := sub_self _
  zeta_le_xi_succ := by
    intro j
    have hb : interiorBlock P (interiorSliceIndex a m h j.succ) =
        interiorBlock P (interiorSliceIndex a m h j.castSucc) :=
      (hblock j.succ).trans (hblock j.castSucc).symm
    have hx := interior_block_adjacent_overlap P
      (i := interiorSliceIndex a m h j.castSucc) (j := interiorSliceIndex a m h j.succ)
      (by simp [interiorSliceIndex]; omega) hb
    omega
  xi_last_pos := by
    have hx := interior_block_row_nonempty P hne (hblock (Fin.last m))
    omega

/-- The interval's connected profile is produced by the canonical profile/beta-pair equivalence. -/
def interiorSliceProfile {n : ℕ} (P : Profile n) (a m : ℕ) (h : a + m < n)
    (hblock : ∀ i, interiorBlock P (interiorSliceIndex a m h i) =
      interiorBlock P (interiorSliceIndex a m h 0))
    (hne : P.zeta (interiorSliceIndex a m h 0).castSucc <
      P.xi (interiorSliceIndex a m h 0).succ) : Profile m :=
  Profile.ofBetaPair (interiorSliceBetaPair P a m h hblock hne)

/-- Both normalized endpoint lists agree with the produced interval profile. -/
theorem interiorSliceProfile_beta {n : ℕ} (P : Profile n) (a m : ℕ) (h : a + m < n)
    (hblock : ∀ i, interiorBlock P (interiorSliceIndex a m h i) =
      interiorBlock P (interiorSliceIndex a m h 0))
    (hne : P.zeta (interiorSliceIndex a m h 0).castSucc <
      P.xi (interiorSliceIndex a m h 0).succ) :
    (interiorSliceProfile P a m h hblock hne).xi =
        (interiorSliceBetaPair P a m h hblock hne).xi ∧
      (interiorSliceProfile P a m h hblock hne).zeta =
        (interiorSliceBetaPair P a m h hblock hne).zeta := by
  have hb := Profile.equivBetaPair.right_inv (interiorSliceBetaPair P a m h hblock hne)
  exact ⟨congrArg Profile.BetaPair.xi hb, congrArg Profile.BetaPair.zeta hb⟩

/-- The full original complementary interval is the connected profile's actual JT matrix. -/
theorem interiorSliceProfile_matrix {n : ℕ} (P : Profile n) (a m : ℕ) (h : a + m < n)
    (hblock : ∀ i, interiorBlock P (interiorSliceIndex a m h i) =
      interiorBlock P (interiorSliceIndex a m h 0))
    (hne : P.zeta (interiorSliceIndex a m h 0).castSucc <
      P.xi (interiorSliceIndex a m h 0).succ) :
    jtMatrix (fun i => P.xi (interiorSliceIndex a m h i).succ)
        (fun j => P.zeta (interiorSliceIndex a m h j).castSucc) =
      jtMatrix (interiorSliceProfile P a m h hblock hne).xi
        (interiorSliceProfile P a m h hblock hne).zeta := by
  obtain ⟨hxi, hzeta⟩ := interiorSliceProfile_beta P a m h hblock hne
  rw [hxi, hzeta]
  apply Matrix.ext
  intro i j
  change hh (P.xi (interiorSliceIndex a m h i).succ -
      P.zeta (interiorSliceIndex a m h j).castSucc) =
    hh ((P.xi (interiorSliceIndex a m h i).succ -
      P.zeta (interiorSliceIndex a m h (Fin.last m)).castSucc) -
      (P.zeta (interiorSliceIndex a m h j).castSucc -
      P.zeta (interiorSliceIndex a m h (Fin.last m)).castSucc))
  congr 1
  ring

end SkewCornerDescent.Matrix
