/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalClosureRows

/-!
# Actual source-copy beta coordinates in the horizontal closure

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`). Literal cell membership
produces the affine original row and column endpoint lists. The shared row retains the
translated copy's right endpoint and the unshifted copy's left endpoint. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- Row placement of the translated complete source copy in its actual closure profile. -/
def originalClosureUpperRow {n m : ℕ} (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (i : Fin (n + 1)) :
    Fin (m + 1) :=
  ⟨i.val, by have hm := (originalHorizontalClosure_profile_rows P Q v hQ).1; omega⟩

/-- Row placement of the unshifted complete source copy in its actual closure profile. -/
def originalClosureLowerRow {n m : ℕ} (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (i : Fin (n + 1)) :
    Fin (m + 1) :=
  ⟨n + i.val, by have hm := (originalHorizontalClosure_profile_rows P Q v hQ).1; omega⟩

/-- Every translated-copy right endpoint is the actual original endpoint with its common shift.
This includes the shared row, whose right endpoint belongs to the translated copy. -/
theorem originalHorizontalClosure_xi_upper {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (i : Fin (n + 1)) :
    Q.xi (originalClosureUpperRow P Q v hQ i) = P.xi i + P.xi 0 := by
  let q := originalClosureUpperRow P Q v hQ i
  have hlit : ((i : ℤ), P.xi i + i - 1 + P.xi 0) ∈ Q.cells := by
    apply (originalHorizontalClosure_profile_point P Q v hQ _ _).mpr
    right
    have he : P.xi i + i - 1 + P.xi 0 - P.xi 0 = P.xi i + i - 1 := by ring
    rw [he]
    exact P.row_right_mem_cells i
  have hlow := (Q.mem_cells_fin q _).mp hlit
  change Q.zeta q + (i : ℤ) ≤ P.xi i + i - 1 + P.xi 0 ∧
    P.xi i + i - 1 + P.xi 0 < Q.xi q + i at hlow
  have hright : ((i : ℤ), Q.xi q + i - 1) ∈ Q.cells := Q.row_right_mem_cells q
  rcases (originalHorizontalClosure_profile_point P Q v hQ _ _).mp hright with h | h
  · obtain ⟨a, ha, hcols⟩ := P.mem_cells.mp h
    have hi := i.isLt
    have ha0 : a = 0 := by
      apply Fin.ext
      change a.val = 0
      omega
    rw [ha0] at hcols
    simp only [Fin.val_zero, Nat.cast_zero, add_zero] at hcols
    have hp := P.xi_pos i
    change Q.xi q = P.xi i + P.xi 0
    omega
  · have hu := (P.mem_cells_fin i _).mp h
    change Q.xi q = P.xi i + P.xi 0
    omega

/-- Every translated-copy original complementary column has the same common affine shift.
The shared row is excluded because its left endpoint belongs to the unshifted copy. -/
theorem originalHorizontalClosure_zeta_upper {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (i : Fin n) :
    Q.zeta (originalClosureUpperRow P Q v hQ i.castSucc) = P.zeta i.castSucc + P.xi 0 := by
  let q := originalClosureUpperRow P Q v hQ i.castSucc
  have hlit : ((i : ℤ), P.zeta i.castSucc + i + P.xi 0) ∈ Q.cells := by
    apply (originalHorizontalClosure_profile_point P Q v hQ _ _).mpr
    right
    have he : P.zeta i.castSucc + i + P.xi 0 - P.xi 0 = P.zeta i.castSucc + i := by ring
    rw [he]
    exact P.row_left_mem_cells i.castSucc
  have hhigh := (Q.mem_cells_fin q _).mp hlit
  change Q.zeta q + (i : ℤ) ≤ P.zeta i.castSucc + i + P.xi 0 ∧
    P.zeta i.castSucc + i + P.xi 0 < Q.xi q + i at hhigh
  have hleft : ((i : ℤ), Q.zeta q + i) ∈ Q.cells := Q.row_left_mem_cells q
  rcases (originalHorizontalClosure_profile_point P Q v hQ _ _).mp hleft with h | h
  · have hb := P.row_bounds_of_mem_cells h
    have hi := i.isLt
    omega
  · have hl := (P.mem_cells_fin i.castSucc _).mp h
    simp only [Fin.val_castSucc] at hl
    change Q.zeta q = P.zeta i.castSucc + P.xi 0
    omega

/-- Every unshifted-copy original complementary row has its unchanged source beta coordinate. -/
theorem originalHorizontalClosure_xi_lower {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (i : Fin n) :
    Q.xi (originalClosureLowerRow P Q v hQ i.succ) = P.xi i.succ := by
  let q := originalClosureLowerRow P Q v hQ i.succ
  have hq : (q : ℤ) = (n : ℤ) + (i.succ : ℤ) := by
    dsimp only [q, originalClosureLowerRow]
    exact Nat.cast_add _ _
  have hlit : ((n : ℤ) + (i.succ : ℤ), P.xi i.succ + n + i.succ - 1) ∈ Q.cells := by
    apply (originalHorizontalClosure_profile_point P Q v hQ _ _).mpr
    left
    have hr : (n : ℤ) + i.succ - n = (i.succ : ℤ) := by ring
    have hc : P.xi i.succ + n + i.succ - 1 - n = P.xi i.succ + i.succ - 1 := by ring
    rw [hr, hc]
    exact P.row_right_mem_cells i.succ
  have hlow := (Q.mem_cells_fin q _).mp (by rw [hq]; exact hlit)
  rw [hq] at hlow
  have hright : ((n : ℤ) + (i.succ : ℤ), Q.xi q + (n + i.succ) - 1) ∈ Q.cells := by
    simpa only [hq] using Q.row_right_mem_cells q
  rcases (originalHorizontalClosure_profile_point P Q v hQ _ _).mp hright with h | h
  · have hr : (n : ℤ) + i.succ - n = (i.succ : ℤ) := by ring
    rw [hr] at h
    have hu := (P.mem_cells_fin i.succ _).mp h
    change Q.xi q = P.xi i.succ
    omega
  · have hb := P.row_bounds_of_mem_cells h
    have hi : 0 < (i.succ : ℤ) := by
      simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one]
      omega
    omega

/-- Every unshifted-copy left endpoint is unchanged, including the shared row and final cap. -/
theorem originalHorizontalClosure_zeta_lower {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (i : Fin (n + 1)) :
    Q.zeta (originalClosureLowerRow P Q v hQ i) = P.zeta i := by
  let q := originalClosureLowerRow P Q v hQ i
  have hq : (q : ℤ) = (n : ℤ) + (i : ℤ) := by
    dsimp only [q, originalClosureLowerRow]
    exact Nat.cast_add _ _
  have hlit : ((n : ℤ) + (i : ℤ), P.zeta i + n + i) ∈ Q.cells := by
    apply (originalHorizontalClosure_profile_point P Q v hQ _ _).mpr
    left
    have hr : (n : ℤ) + i - n = (i : ℤ) := by ring
    have hc : P.zeta i + n + i - n = P.zeta i + i := by ring
    rw [hr, hc]
    exact P.row_left_mem_cells i
  have hhigh := (Q.mem_cells_fin q _).mp (by rw [hq]; exact hlit)
  rw [hq] at hhigh
  have hleft : ((n : ℤ) + (i : ℤ), Q.zeta q + (n + i)) ∈ Q.cells := by
    simpa only [hq] using Q.row_left_mem_cells q
  rcases (originalHorizontalClosure_profile_point P Q v hQ _ _).mp hleft with h | h
  · have hr : (n : ℤ) + i - n = (i : ℤ) := by ring
    rw [hr] at h
    have hl := (P.mem_cells_fin i _).mp h
    change Q.zeta q = P.zeta i
    omega
  · obtain ⟨a, ha, hcols⟩ := P.mem_cells.mp h
    have haLt := a.isLt
    have hi0 : i.val = 0 := by omega
    have halast : a = Fin.last n := by
      apply Fin.ext
      change a.val = n
      omega
    rw [halast, P.zeta_last] at hcols
    simp only [Fin.val_last, zero_add] at hcols
    have hzi := P.zeta_strictAnti.antitone (Fin.zero_le i)
    have htop := P.xi_sub_zeta 0
    have hr := P.r_pos 0
    change Q.zeta q = P.zeta i
    omega

end SkewCornerDescent.Matrix
