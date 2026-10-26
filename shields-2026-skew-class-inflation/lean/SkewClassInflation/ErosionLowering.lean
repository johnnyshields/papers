/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.NoEscape
import SkewClassInflation.CellProfiles

/-!
# Erosion of an actual connected diagram

Formalizes `lem:erosion` in `shields-2026-skew-class-inflation.tex`.  The erosion
\(\mathcal E(S)=\{(i,j)\in S:(i,j+1)\in S\}\) removes the last cell of every row and keeps
the original row coordinates, so a row of length one becomes an empty row.  Its full
Jacobi--Trudi board is built from the inherited beta lists \((\xi_i-1,\zeta_j)\).  The ordinary
degree \(n+1\) part of \(s_S\), with \(h_j\mapsto h_{j-1}\) (including \(h_1\mapsto1\)), is the
determinant of that board, and the cell count drops by the number of rows.  Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative

/-- Erosion of a cell diagram: the cells whose eastern neighbor also lies in the diagram. -/
def erodeCells (S : SkewGluing.Diagram) : SkewGluing.Diagram :=
  S.filter fun x => (x.1, x.2 + 1) ∈ S

/-- The determinant of the eroded board in the inherited row coordinates,
with beta lists \((\xi_i-1,\zeta_j)\), empty rows included. -/
noncomputable def erodedSchur {n : ℕ} (P : Profile n) : CompleteRing :=
  (Matrix.of fun i j => complete (P.xi i - 1 - P.zeta j)).det

/-- The eroded cells of a profile diagram are the row intervals with beta lists
\((\xi_i-1,\zeta_i)\), empty when the row has length one. -/
theorem mem_erodeCells_profileCells {n : ℕ} (P : Profile n) (a b : ℤ) :
    (a, b) ∈ erodeCells (profileCells P) ↔
      ∃ i : Fin (n + 1), (i.val : ℤ) = a ∧ P.zeta i + i.val ≤ b ∧ b < P.xi i - 1 + i.val := by
  unfold erodeCells
  rw [Finset.mem_filter, mem_profileCells, mem_profileCells]
  constructor
  · rintro ⟨⟨i, hi, h1, h2⟩, ⟨i', hi', h3, h4⟩⟩
    have : i = i' := Fin.ext (by omega)
    subst this
    exact ⟨i, hi, h1, by omega⟩
  · rintro ⟨i, hi, h1, h2⟩
    exact ⟨⟨i, hi, h1, by omega⟩, ⟨i, hi, by omega, by omega⟩⟩

/-- The cells erosion removes are exactly the last cell of each of the `n + 1` nonempty rows. -/
theorem card_erodeCells_profileCells {n : ℕ} (P : Profile n) :
    (erodeCells (profileCells P)).card + (n + 1) = (profileCells P).card := by
  classical
  let R : Finset (ℤ × ℤ) :=
    Finset.univ.image fun i : Fin (n + 1) => ((i.val : ℤ), P.xi i - 1 + i.val)
  have hR : R.card = n + 1 := by
    rw [Finset.card_image_of_injective]
    · simp
    · intro i j h
      have := congrArg Prod.fst h
      exact Fin.ext (by simpa using this)
  have hdisj : Disjoint (erodeCells (profileCells P)) R := by
    rw [Finset.disjoint_left]
    rintro ⟨a, b⟩ h1 h2
    obtain ⟨i, hi, h3, h4⟩ := (mem_erodeCells_profileCells P a b).mp h1
    simp only [R, Finset.mem_univ, true_and, Finset.mem_image] at h2
    obtain ⟨j, hj⟩ := h2
    have e1 : (j.val : ℤ) = a := by simpa using congrArg Prod.fst hj
    have e2 : P.xi j - 1 + j.val = b := by simpa using congrArg Prod.snd hj
    have : i = j := Fin.ext (by omega)
    subst this
    omega
  have hU : erodeCells (profileCells P) ∪ R = profileCells P := by
    ext ⟨a, b⟩
    simp only [Finset.mem_union]
    constructor
    · rintro (h | h)
      · exact (Finset.mem_filter.mp h).1
      · simp only [R, Finset.mem_univ, true_and, Finset.mem_image] at h
        obtain ⟨i, hi⟩ := h
        have e1 : (i.val : ℤ) = a := by simpa using congrArg Prod.fst hi
        have e2 : P.xi i - 1 + i.val = b := by simpa using congrArg Prod.snd hi
        rw [mem_profileCells]
        have := P.r_pos i
        have := P.xi_sub_zeta i
        exact ⟨i, e1, by omega, by omega⟩
    · intro h
      obtain ⟨i, hi, h1, h2⟩ := (mem_profileCells P a b).mp h
      by_cases hb : b < P.xi i - 1 + i.val
      · exact Or.inl ((mem_erodeCells_profileCells P a b).mpr ⟨i, hi, h1, hb⟩)
      · right
        simp only [R, Finset.mem_univ, true_and, Finset.mem_image]
        exact ⟨i, by ext <;> simp <;> omega⟩
  have hc := Finset.card_union_of_disjoint hdisj
  rw [hU, hR] at hc
  omega

/-- **Erosion** (`lem:erosion`): the ordinary degree `n + 1` part of `s_S`, with
`h_j ↦ h_{j-1}`, is the full determinant of the eroded diagram. -/
theorem erosion_lowering {n : ℕ} (P : Profile n) :
    lowering 1 (n + 1) (profileSchur P) = erodedSchur P := by
  have h := lowering_shifted_det (Matrix.of fun i j : Fin (n + 1) => P.xi i - 1 - P.zeta j) 1
    one_pos
  have e : (Matrix.of fun i j : Fin (n + 1) => complete (P.xi i - P.zeta j)) =
      Matrix.of fun i j : Fin (n + 1) => complete (P.xi i - 1 - P.zeta j + ((1 : ℕ) : ℤ)) := by
    ext i j
    simp only [Matrix.of_apply]
    have : P.xi i - P.zeta j = P.xi i - 1 - P.zeta j + ((1 : ℕ) : ℤ) := by push_cast; ring
    rw [this]
  unfold profileSchur erodedSchur
  rw [e]
  simpa only [Fintype.card_fin, Matrix.of_apply] using h

/-- Erosion preserves whole Schur equality of connected diagrams with the same row count. -/
theorem erodedSchur_eq_of_profileSchur_eq {n : ℕ} {P Q : Profile n}
    (h : profileSchur P = profileSchur Q) : erodedSchur P = erodedSchur Q := by
  rw [← erosion_lowering, ← erosion_lowering, h]

/-- Without empty rows the eroded board is the board of the connected deflation. -/
theorem erodedSchur_eq_deflate {n : ℕ} (P : Profile n) (h : Profile.CanDeflate 1 P) :
    erodedSchur P = profileSchur (Profile.deflate 1 P h) := by
  rw [← erosion_lowering]
  conv_lhs => rw [← Profile.inflate_deflate 1 P h]
  exact lowering_inflated_profile _ 1 one_pos

end SkewClassInflation
