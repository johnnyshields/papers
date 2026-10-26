/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.DistinguishedContractionSets
import SkewClassInflation.ZeroContractionBoundaries
import SkewClassInflation.ProfileMergeReadings

/-!
# Boundary rows retained through distinguished contractions

The first-row and span inputs for the positional reconstruction in
`lem:total-contraction-inverse` of `shields-2026-skew-class-inflation.tex`.
The first row is retained when its adjacent gap is not contracted;
no assertion is made when that first gap is distinguished.  Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative SkewJacobiNegative.Staircase SkewJacobiNegative.GeneralHessenberg

/-- The actual total distinguished contraction has the original normalized span. -/
theorem contractAllMinimum_span {n : ℕ} (P : Profile n) (v : ℕ+) :
    (contractAllMinimum P v).2.xi 0 = P.xi 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases h : ∃ c : Fin (n + 1), P.g c = v.val
    · rw [show contractAllMinimum P v =
          contractAllMinimum (contract P (Classical.choose h)) v by
        simp only [contractAllMinimum, dite_eq_left h]]
      exact (ih _).trans (contract_xi_zero P (Classical.choose h))
    · rw [show contractAllMinimum P v = ⟨n + 1, P⟩ by
        simp only [contractAllMinimum, dite_eq_right h]]

/-- The largest upper beta cannot cancel against a distinguished translate of any column. -/
theorem first_upper_not_shifted_column {n : ℕ} (P : Profile n) (v : ℕ+) (hP : Thick P)
    (hr : ∀ i, v.val < P.r i) :
    P.xi 0 ∉ P.toBetaDiagram.colSet.image (fun x => x + (v.val : ℤ)) := by
  intro h
  obtain ⟨y, hy, he⟩ := Finset.mem_image.mp h
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hy
  have hindex : P.xi 0 - P.zeta j = (v.val : ℤ) := by
    change P.zeta j = y at hj
    omega
  obtain ⟨s, hs, _, _⟩ := (distinguished_index_iff_seam P hP v hr 0 j).mp hindex
  exact Fin.succ_ne_zero s hs.symm

/-- A nondistinguished first gap prevents cancellation of the first lower beta. -/
theorem first_lower_not_shifted_row {n : ℕ} (P : Profile n) (v : ℕ+) (hP : Thick P)
    (hr : ∀ i, v.val < P.r i) (hg : ∀ j : Fin n, j.val = 0 → P.g j ≠ v.val) :
    P.zeta 0 ∉ P.toBetaDiagram.rowSet.image (fun x => x - (v.val : ℤ)) := by
  intro h
  obtain ⟨x, hx, he⟩ := Finset.mem_image.mp h
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hx
  have hindex : P.xi i - P.zeta 0 = (v.val : ℤ) := by
    change P.xi i = x at hi
    omega
  obtain ⟨s, _, hs, hgap⟩ := (distinguished_index_iff_seam P hP v hr i 0).mp hindex
  have hs0 : s.val = 0 := by
    have hh := congrArg Fin.val hs
    simpa only [Fin.val_zero, Fin.val_castSucc] using hh.symm
  exact hg s hs0 hgap

/-- The entire first row survives when its first gap is not among the contracted seams. -/
theorem contractAllMinimum_first_row {n : ℕ} (P : Profile n) (v : ℕ+) (hP : Thick P)
    (hr : ∀ i, v.val < P.r i) (hg : ∀ j : Fin n, j.val = 0 → P.g j ≠ v.val) :
    (contractAllMinimum P v).2.r 0 = P.r 0 := by
  let C := (contractAllMinimum P v).2
  obtain ⟨hrows, hcols⟩ := contractAllMinimum_sets P v hP hr
  have hx := antitone_max_after_difference P.xi C.xi P.xi_strictAnti.antitone
    C.xi_strictAnti.antitone (P.toBetaDiagram.colSet.image (fun x => x + (v.val : ℤ)))
    hrows (first_upper_not_shifted_column P v hP hr)
  have hz := antitone_max_after_difference P.zeta C.zeta P.zeta_strictAnti.antitone
    C.zeta_strictAnti.antitone (P.toBetaDiagram.rowSet.image (fun x => x - (v.val : ℤ)))
    hcols (first_lower_not_shifted_row P v hP hr hg)
  have hCr := C.xi_sub_zeta 0
  have hPr := P.xi_sub_zeta 0
  rw [hx, hz] at hCr
  exact_mod_cast hCr.symm.trans hPr

end SkewClassInflation
