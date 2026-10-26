/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.BetaProfiles
import SkewJacobiNegative.Gluing.RowInvariants
import SkewJacobiNegative.Overlaps.RowOverlaps

/-!
# Identification of the full-board representations

The complete generators, weak beta rows, and natural connected profiles used
in `sec:boards` of `shields-2026-skew-jacobi-negative.tex` represent the same
actual determinant.  The all-order overlap invariant retains its zero padding.
-/

namespace SkewJacobiNegative

/-- The two inherited generator conventions agree at every integer index. -/
theorem complete_eq_hh (k : ℤ) : complete k = Gluing.hh k := by
  rcases lt_trichotomy k 0 with hk | rfl | hk
  · rw [complete_of_neg hk, Gluing.hh_of_neg hk]
  · rw [complete_zero, Gluing.hh_zero]
  · let j : ℕ+ := ⟨k.toNat, by omega⟩
    have hj : (j : ℤ) = k := by dsimp [j]; omega
    rw [← hj, complete_nat, Gluing.hh_pnat]

namespace BetaDiagram
variable {n m : ℕ}

/-- Extend the actual finite beta coordinates only outside their used domain. -/
def toWeakRows (D : BetaDiagram n) : Overlaps.BetaRows n where
  xi i := if h : i < n then D.row ⟨i, h⟩ else 0
  zeta i := if h : i < n then D.col ⟨i, h⟩ else 0
  xi_lt i j hij hj := by
    have hi : i < n := hij.trans hj
    simpa only [dite_eq_left hi, dite_eq_left hj] using
      D.row_strictAnti (show (⟨i, hi⟩ : Fin n) < ⟨j, hj⟩ from hij)
  zeta_lt i j hij hj := by
    have hi : i < n := hij.trans hj
    simpa only [dite_eq_left hi, dite_eq_left hj] using
      D.col_strictAnti (show (⟨i, hi⟩ : Fin n) < ⟨j, hj⟩ from hij)
  zeta_le i hi := by
    simpa only [dite_eq_left hi] using (D.row_nonempty ⟨i, hi⟩).le

@[simp]
theorem toWeakRows_xiFin (D : BetaDiagram n) (i : Fin n) :
    D.toWeakRows.xiFin i = D.row i := by
  simp only [toWeakRows, Overlaps.BetaRows.xiFin, dite_eq_left i.isLt]

@[simp]
theorem toWeakRows_zetaFin (D : BetaDiagram n) (i : Fin n) :
    D.toWeakRows.zetaFin i = D.col i := by
  simp only [toWeakRows, Overlaps.BetaRows.zetaFin, dite_eq_left i.isLt]

/-- Weak-row determinants are the genuine full-board polynomial, not a specialization. -/
theorem toWeakRows_schur (D : BetaDiagram n) : D.toWeakRows.schur = D.schur := by
  change (Matrix.of fun i j : Fin n => Gluing.hh
    (D.toWeakRows.xiFin i - D.toWeakRows.zetaFin j)).det = D.matrix.det
  apply congrArg Matrix.det
  apply Matrix.ext
  intro i j
  simp only [matrix, Matrix.of_apply, toWeakRows_xiFin, toWeakRows_zetaFin]
  exact (complete_eq_hh _).symm

/-- The actual padded multiset of the intersections of consecutive rows. -/
def paddedRowOverlaps (D : BetaDiagram n) (k : ℕ) : Multiset ℕ :=
  D.toWeakRows.overlaps k

/-- All-order padded row overlaps are invariant under actual full Schur equality. -/
theorem paddedRowOverlaps_eq_of_schur_eq (D : BetaDiagram n) (E : BetaDiagram m)
    (he : D.schur = E.schur) (k : ℕ) : D.paddedRowOverlaps k = E.paddedRowOverlaps k := by
  have hn : n = m := D.row_count_of_schur_eq E he
  have hp := Overlaps.BetaRows.rowOverlaps_eq_of_schur_eq n m D.toWeakRows E.toWeakRows
    (by rw [D.toWeakRows_schur, E.toWeakRows_schur]; exact he) k
  apply Gluing.multiset_eq_of_count_pnat
  · intro v
    have hD := Multiset.count_filter_of_pos (p := (0 < ·)) (a := (v : ℕ)) v.pos
      (s := D.toWeakRows.overlaps k)
    have hE := Multiset.count_filter_of_pos (p := (0 < ·)) (a := (v : ℕ)) v.pos
      (s := E.toWeakRows.overlaps k)
    change Multiset.count (v : ℕ) (D.toWeakRows.overlaps k) =
      Multiset.count (v : ℕ) (E.toWeakRows.overlaps k)
    rw [← hD, ← hE]
    exact congrArg (Multiset.count (v : ℕ)) hp
  · simp only [paddedRowOverlaps, Overlaps.BetaRows.overlaps, Multiset.card_map,
      Finset.card_val, Finset.card_range]
    rw [hn]

/-- Normalize the actual beta pair by a common translation only. -/
def normalizedPair (D : BetaDiagram (n + 1)) (hD : D.Connected) :
    Gluing.Profile.BetaPair n where
  xi i := D.row i - D.col (Fin.last n)
  zeta i := D.col i - D.col (Fin.last n)
  xi_strictAnti i j hij := by
    change D.row j - D.col (Fin.last n) < D.row i - D.col (Fin.last n)
    exact sub_lt_sub_right (D.row_strictAnti hij) _
  zeta_strictAnti i j hij := by
    change D.col j - D.col (Fin.last n) < D.col i - D.col (Fin.last n)
    exact sub_lt_sub_right (D.col_strictAnti hij) _
  zeta_last := sub_self _
  zeta_le_xi_succ j := by
    have h := hD.2 j.castSucc (Nat.succ_lt_succ j.isLt)
    change D.col j.castSucc ≤ D.row j.succ at h
    change D.col j.castSucc - D.col (Fin.last n) ≤
      D.row j.succ - D.col (Fin.last n)
    exact sub_le_sub_right h _
  xi_last_pos := sub_pos.mpr (D.row_nonempty _)

/-- Connected full boards are natural profiles after the declared normalization. -/
def toProfile (D : BetaDiagram (n + 1)) (hD : D.Connected) : Gluing.Profile n :=
  Gluing.Profile.ofBetaPair (D.normalizedPair hD)

/-- The profile's upper coordinates are exactly the translated full beta coordinates. -/
theorem toProfile_xi (D : BetaDiagram (n + 1)) (hD : D.Connected) :
    (D.toProfile hD).xi = fun i => D.row i - D.col (Fin.last n) := by
  have h := congrArg (fun B : Gluing.Profile.BetaPair n => B.xi)
    (Gluing.Profile.equivBetaPair.right_inv (D.normalizedPair hD))
  simpa only [Gluing.Profile.equivBetaPair, Gluing.Profile.toBetaPair, toProfile,
    normalizedPair] using h

/-- The profile's lower coordinates use the same common translation. -/
theorem toProfile_zeta (D : BetaDiagram (n + 1)) (hD : D.Connected) :
    (D.toProfile hD).zeta = fun i => D.col i - D.col (Fin.last n) := by
  have h := congrArg (fun B : Gluing.Profile.BetaPair n => B.zeta)
    (Gluing.Profile.equivBetaPair.right_inv (D.normalizedPair hD))
  simpa only [Gluing.Profile.equivBetaPair, Gluing.Profile.toBetaPair, toProfile,
    normalizedPair] using h

/-- The natural profile and full board have precisely the same rational Schur polynomial. -/
theorem toProfile_schur (D : BetaDiagram (n + 1)) (hD : D.Connected) :
    (D.toProfile hD).schur = D.schur := by
  unfold Gluing.Profile.schur schur
  apply congrArg Matrix.det
  apply Matrix.ext
  intro i j
  simp only [matrix, Matrix.of_apply, D.toProfile_xi hD, D.toProfile_zeta hD]
  rw [← complete_eq_hh]
  congr 1
  ring

end BetaDiagram

namespace Gluing.Profile
variable {n : ℕ}

/-- The profile beta lists form the actual full-row diagram. -/
def toBetaDiagram (P : Gluing.Profile n) : BetaDiagram (n + 1) where
  row := P.xi
  col := P.zeta
  row_strictAnti := P.xi_strictAnti
  col_strictAnti := P.zeta_strictAnti
  row_nonempty i := P.toBetaPair.zeta_lt_xi i

/-- The profile determinant is identified entrywise with the full-row determinant. -/
theorem toBetaDiagram_schur (P : Gluing.Profile n) : P.toBetaDiagram.schur = P.schur := by
  unfold BetaDiagram.schur Gluing.Profile.schur
  apply congrArg Matrix.det
  apply Matrix.ext
  intro i j
  exact complete_eq_hh _

/-- Valid natural profiles always represent connected full boards. -/
theorem toBetaDiagram_connected (P : Gluing.Profile n) : P.toBetaDiagram.Connected := by
  refine ⟨by omega, ?_⟩
  intro i hi
  let j : Fin n := ⟨i.val, by omega⟩
  have h := P.zeta_le_xi_succ j
  change P.zeta i ≤ P.xi ⟨i.val + 1, hi⟩
  exact h

end Gluing.Profile

end SkewJacobiNegative
