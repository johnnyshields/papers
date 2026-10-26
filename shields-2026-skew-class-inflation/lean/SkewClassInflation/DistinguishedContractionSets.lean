/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.ZeroContractionSets
import SkewClassInflation.SeamCoefficients

/-!
# Actual beta supports after all distinguished seams are contracted

The support invariant for the positional inverse in
`lem:total-contraction-inverse` of `shields-2026-skew-class-inflation.tex`.
A contraction removes beta coordinates differing by the distinguished
positive label.  The two translated set differences are invariant.
Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative SkewJacobiNegative.Staircase SkewJacobiNegative.GeneralHessenberg

/-- The original strict row bound survives every actual distinguished contraction. -/
theorem contractAllMinimum_rows_above {n : ℕ} (P : Profile n) (v : ℕ+)
    (hr : ∀ i, v.val < P.r i) : ∀ i, v.val < (contractAllMinimum P v).2.r i := by
  induction n with
  | zero => exact hr
  | succ n ih =>
    by_cases h : ∃ c : Fin (n + 1), P.g c = v.val
    · rw [show contractAllMinimum P v =
          contractAllMinimum (contract P (Classical.choose h)) v by
        simp only [contractAllMinimum, dite_eq_left h]]
      exact ih _ (contract_rows_above P v hr (Classical.choose h))
    · rw [show contractAllMinimum P v = ⟨n + 1, P⟩ by
        simp only [contractAllMinimum, dite_eq_right h]]
      exact hr

/-- A distinguished contraction preserves both translated residual supports. -/
theorem contract_distinguished_residualSets {n : ℕ} (P : Profile (n + 1)) (v : ℕ+)
    (c : Fin (n + 1)) (hc : P.g c = v.val) :
    (contract P c).toBetaDiagram.rowSet \
        ((contract P c).toBetaDiagram.colSet.image (fun x => x + (v.val : ℤ))) =
      P.toBetaDiagram.rowSet \ (P.toBetaDiagram.colSet.image (fun x => x + (v.val : ℤ))) ∧
    (contract P c).toBetaDiagram.colSet \
        ((contract P c).toBetaDiagram.rowSet.image (fun x => x - (v.val : ℤ))) =
      P.toBetaDiagram.colSet \ (P.toBetaDiagram.rowSet.image (fun x => x - (v.val : ℤ))) := by
  classical
  have hcoord : P.xi c.succ = P.zeta c.castSucc + (v.val : ℤ) := by
    have hh := P.xi_succ_sub_zeta_castSucc c
    rw [hc] at hh
    omega
  have hr : P.xi c.succ ∈ P.toBetaDiagram.rowSet :=
    Finset.mem_image.mpr ⟨c.succ, Finset.mem_univ _, rfl⟩
  have hz : P.zeta c.castSucc ∈ P.toBetaDiagram.colSet :=
    Finset.mem_image.mpr ⟨c.castSucc, Finset.mem_univ _, rfl⟩
  have hzi : P.xi c.succ ∈ P.toBetaDiagram.colSet.image (fun x => x + (v.val : ℤ)) :=
    Finset.mem_image.mpr ⟨_, hz, hcoord.symm⟩
  have hri : P.zeta c.castSucc ∈ P.toBetaDiagram.rowSet.image (fun x => x - (v.val : ℤ)) :=
    Finset.mem_image.mpr ⟨_, hr, by omega⟩
  rw [contract_rowSet, contract_colSet,
    Finset.image_erase (fun a b h => by omega), Finset.image_erase (fun a b h => by omega)]
  constructor
  · rw [← hcoord]
    exact erase_common_sdiff _ _ _ hr hzi
  · have he : P.xi c.succ - (v.val : ℤ) = P.zeta c.castSucc := by omega
    rw [he]
    exact erase_common_sdiff _ _ _ hz hri

/-- The two translated support differences survive the complete recursive contraction. -/
theorem contractAllMinimum_residualSets {n : ℕ} (P : Profile n) (v : ℕ+) :
    (contractAllMinimum P v).2.toBetaDiagram.rowSet \
        ((contractAllMinimum P v).2.toBetaDiagram.colSet.image (fun x => x + (v.val : ℤ))) =
      P.toBetaDiagram.rowSet \ (P.toBetaDiagram.colSet.image (fun x => x + (v.val : ℤ))) ∧
    (contractAllMinimum P v).2.toBetaDiagram.colSet \
        ((contractAllMinimum P v).2.toBetaDiagram.rowSet.image (fun x => x - (v.val : ℤ))) =
      P.toBetaDiagram.colSet \ (P.toBetaDiagram.rowSet.image (fun x => x - (v.val : ℤ))) := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    by_cases h : ∃ c : Fin (n + 1), P.g c = v.val
    · rw [show contractAllMinimum P v =
          contractAllMinimum (contract P (Classical.choose h)) v by
        simp only [contractAllMinimum, dite_eq_left h]]
      have hs := contract_distinguished_residualSets P v (Classical.choose h)
        (Classical.choose_spec h)
      have hi := ih (contract P (Classical.choose h))
      exact ⟨hi.1.trans hs.1, hi.2.trans hs.2⟩
    · rw [show contractAllMinimum P v = ⟨n + 1, P⟩ by
        simp only [contractAllMinimum, dite_eq_right h]]
      exact ⟨rfl, rfl⟩

/-- The actual final supports are precisely the uncanceled translated beta lists. -/
theorem contractAllMinimum_sets {n : ℕ} (P : Profile n) (v : ℕ+) (hP : Thick P)
    (hr : ∀ i, v.val < P.r i) :
    (contractAllMinimum P v).2.toBetaDiagram.rowSet =
      P.toBetaDiagram.rowSet \ (P.toBetaDiagram.colSet.image (fun x => x + (v.val : ℤ))) ∧
    (contractAllMinimum P v).2.toBetaDiagram.colSet =
      P.toBetaDiagram.colSet \ (P.toBetaDiagram.rowSet.image (fun x => x - (v.val : ℤ))) := by
  classical
  let C := (contractAllMinimum P v).2
  have hC := contractAllMinimum_thick hP v
  have hrows := contractAllMinimum_rows_above P v hr
  have hdis : Disjoint C.toBetaDiagram.rowSet
      (C.toBetaDiagram.colSet.image (fun x => x + (v.val : ℤ))) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hx
    obtain ⟨y, hy, hshift⟩ := Finset.mem_image.mp hy
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hy
    have he : C.xi i - C.zeta j = (v.val : ℤ) := by
      change C.xi i = x at hi
      change C.zeta j = y at hj
      omega
    obtain ⟨s, _, _, hs⟩ := (distinguished_index_iff_seam C hC v hrows i j).mp he
    exact contractAllMinimum_gap_ne P v s hs
  have hdis' : Disjoint C.toBetaDiagram.colSet
      (C.toBetaDiagram.rowSet.image (fun x => x - (v.val : ℤ))) := by
    apply Finset.disjoint_left.mpr
    intro y hy hx
    obtain ⟨x, hx, hshift⟩ := Finset.mem_image.mp hx
    exact Finset.disjoint_left.mp hdis hx (Finset.mem_image.mpr ⟨y, hy, by omega⟩)
  have hi := contractAllMinimum_residualSets P v
  rw [Finset.sdiff_eq_self_of_disjoint hdis, Finset.sdiff_eq_self_of_disjoint hdis'] at hi
  exact hi

/-- Translating the final column support exposes the symmetric cancellation formula. -/
theorem contractAllMinimum_shifted_colSet {n : ℕ} (P : Profile n) (v : ℕ+) (hP : Thick P)
    (hr : ∀ i, v.val < P.r i) :
    ((contractAllMinimum P v).2.toBetaDiagram.colSet.image (fun x => x + (v.val : ℤ))) =
      (P.toBetaDiagram.colSet.image (fun x => x + (v.val : ℤ))) \
        P.toBetaDiagram.rowSet := by
  rw [(contractAllMinimum_sets P v hP hr).2,
    Finset.image_sdiff _ _ (fun a b h => by omega), Finset.image_image]
  simp only [Function.comp_def, sub_add_cancel, Finset.image_id']

end SkewClassInflation
