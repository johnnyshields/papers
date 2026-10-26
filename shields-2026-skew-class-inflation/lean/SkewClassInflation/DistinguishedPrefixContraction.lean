/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.DistinguishedContractionBoundaries
import SkewClassInflation.ZeroPrefixContraction
import SkewClassInflation.ZeroCutReassembly

/-!
# Distinguished contraction behind an unchanged prefix

The positive-seam counterpart of the positional peeling step in
`lem:total-contraction-inverse` of `shields-2026-skew-class-inflation.tex`.
The proof compares actual translated beta supports; it does not assume a
choice of contraction order.  Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative SkewJacobiNegative.Staircase SkewJacobiNegative.GeneralHessenberg

/-- A positive endpoint merger deletes the lower block's largest upper beta. -/
theorem distinguished_merge_rowSet {n m : ℕ} (A : Profile n) (R : Profile m) (v : ℕ+)
    (ha : v.val < A.r (Fin.last n)) (hr : v.val < R.r 0) :
    (Profile.merge A R v.val ha hr).toBetaDiagram.rowSet =
      (A.toBetaDiagram.rowSet.image (fun x => x + R.xi 0 - (v.val : ℤ)) ∪
        R.toBetaDiagram.rowSet).erase (R.xi 0) := by
  have hdel : (Profile.join A R v.val ha hr).xi
      (⟨n, by omega⟩ : Fin (n + m + 1)).succ = R.xi 0 := by
    change (Profile.join A R v.val ha hr).xi ⟨n + 1, by omega⟩ = R.xi 0
    simpa only [Fin.val_zero, Nat.add_zero] using
      Profile.join_xi_right A R v.val ha hr (0 : Fin (m + 1))
  rw [Profile.merge, contract_rowSet, hdel, Profile.join_rowSet]

/-- The translated lower support loses exactly that same span coordinate. -/
theorem distinguished_merge_shifted_colSet {n m : ℕ} (A : Profile n) (R : Profile m) (v : ℕ+)
    (ha : v.val < A.r (Fin.last n)) (hr : v.val < R.r 0) :
    ((Profile.merge A R v.val ha hr).toBetaDiagram.colSet.image
      (fun x => x + (v.val : ℤ))) =
      (A.toBetaDiagram.colSet.image (fun x => x + R.xi 0) ∪
        R.toBetaDiagram.colSet.image (fun x => x + (v.val : ℤ))).erase (R.xi 0) := by
  have hdel : (Profile.join A R v.val ha hr).zeta
      (⟨n, by omega⟩ : Fin (n + m + 1)).castSucc = R.xi 0 - (v.val : ℤ) := by
    change (Profile.join A R v.val ha hr).zeta ⟨n, by omega⟩ = R.xi 0 - (v.val : ℤ)
    have hh := Profile.join_zeta_left A R v.val ha hr (Fin.last n)
    simpa only [Fin.val_last, A.zeta_last, zero_add] using hh
  rw [Profile.merge, contract_colSet, Finset.image_erase (fun a b h => by omega),
    hdel, sub_add_cancel, Profile.join_colSet, Finset.image_union, Finset.image_image]
  simp only [Function.comp_def, sub_add_cancel]

/-- Strict row bounds put every upper coordinate above the distinguished label. -/
theorem profile_rowSet_above {n : ℕ} (P : Profile n) (v : ℕ+)
    (hr : ∀ i, v.val < P.r i) {x : ℤ} (hx : x ∈ P.toBetaDiagram.rowSet) :
    (v.val : ℤ) < x := by
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hx
  have hmin := P.xi_strictAnti.antitone (Fin.le_last i)
  have hlast := P.xi_sub_zeta (Fin.last n)
  rw [P.zeta_last] at hlast
  have hb := hr (Fin.last n)
  change P.xi i = x at hi
  omega

/-- Strict first-row bounds keep every translated column below the normalized span. -/
theorem profile_shifted_colSet_below {n : ℕ} (P : Profile n) (v : ℕ+)
    (hr : v.val < P.r 0) {x : ℤ}
    (hx : x ∈ P.toBetaDiagram.colSet.image (fun y => y + (v.val : ℤ))) : x < P.xi 0 := by
  obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hx
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hy
  have hmax := P.zeta_strictAnti.antitone (Fin.zero_le j)
  have hrow := P.xi_sub_zeta 0
  change P.zeta j = y at hj
  omega

/-- An unchanged nondistinguished prefix can be merged after the remaining actual contraction. -/
theorem distinguished_prefix_contraction {n m : ℕ} (A : Profile n) (R : Profile m) (v : ℕ+)
    (hA : Thick A) (hR : Thick R) (hrA : ∀ i, v.val < A.r i)
    (hrR : ∀ i, v.val < R.r i) (hgA : ∀ j, A.g j ≠ v.val)
    (hJ : Thick (Profile.join A R v.val (hrA _) (hrR _))) :
    (contractAllMinimum (Profile.join A R v.val (hrA _) (hrR _)) v : ConnectedProfile) =
      ⟨n + (contractAllMinimum R v).1,
        Profile.merge A (contractAllMinimum R v).2 v.val (hrA _)
          (contractAllMinimum_rows_above R v hrR _)⟩ := by
  classical
  let C := (contractAllMinimum R v).2
  let AX := A.toBetaDiagram.rowSet.image (fun x => x + R.xi 0 - (v.val : ℤ))
  let AY := A.toBetaDiagram.colSet.image (fun x => x + R.xi 0)
  let RX := R.toBetaDiagram.rowSet
  let RY := R.toBetaDiagram.colSet.image (fun x => x + (v.val : ℤ))
  have hAX : ∀ x ∈ AX, R.xi 0 < x := by
    intro x hx
    obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hx
    have hb := profile_rowSet_above A v hrA hy
    omega
  have hAY : ∀ x ∈ AY, R.xi 0 ≤ x := by
    intro x hx
    obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hx
    have hb := (profile_colSet_bounds A hy).1
    omega
  have hdis : Disjoint AX AY := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨a, ha, hea⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, heb⟩ := Finset.mem_image.mp hy
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ha
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hb
    have hindex : A.xi i - A.zeta j = (v.val : ℤ) := by
      change A.xi i = a at hi
      change A.zeta j = b at hj
      omega
    obtain ⟨s, _, _, hs⟩ := (distinguished_index_iff_seam A hA v hrA i j).mp hindex
    exact hgA s hs
  have hsA : R.xi 0 ∈ AY := Finset.mem_image.mpr
    ⟨0, profile_zero_mem_colSet A, by simp⟩
  have hsR : R.xi 0 ∈ RX := Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  have hsets := touching_span_differences AX AY RX RY (R.xi 0) hdis hAX hAY
    (fun _ h => (profile_rowSet_bounds R h).2)
    (fun _ h => profile_shifted_colSet_below R v (hrR _) h) hsA hsR
  have hjoinRows : ∀ i, v.val < (Profile.join A R v.val (hrA _) (hrR _)).r i := by
    intro i
    change v.val < Profile.joinRows A R i
    unfold Profile.joinRows
    split_ifs
    · exact hrA _
    · exact hrR _
  have hJrows := (contractAllMinimum_sets _ v hJ hjoinRows).1
  have hJcols := contractAllMinimum_shifted_colSet _ v hJ hjoinRows
  have hCrows := (contractAllMinimum_sets R v hR hrR).1
  have hCcols := contractAllMinimum_shifted_colSet R v hR hrR
  have hspan := contractAllMinimum_span R v
  have hnAX : R.xi 0 ∉ AX := fun h => (lt_irrefl _) (hAX _ h)
  have hnCY : R.xi 0 ∉ C.toBetaDiagram.colSet.image (fun x => x + (v.val : ℤ)) := by
    intro h
    have hh := profile_shifted_colSet_below C v (contractAllMinimum_rows_above R v hrR _) h
    rw [hspan] at hh
    exact (lt_irrefl _) hh
  apply profileSigma_eq_of_full_sets
    (contractAllMinimum (Profile.join A R v.val (hrA _) (hrR _)) v).2
    (Profile.merge A C v.val (hrA _) (contractAllMinimum_rows_above R v hrR _))
  · rw [hJrows, Profile.join_rowSet, Profile.join_colSet, Finset.image_union,
      Finset.image_image]
    simp only [Function.comp_def, sub_add_cancel]
    change (AX ∪ RX) \ (AY ∪ RY) = _
    rw [hsets.1, ← hCrows, distinguished_merge_rowSet, hspan]
    change AX ∪ C.toBetaDiagram.rowSet.erase (R.xi 0) =
      (AX ∪ C.toBetaDiagram.rowSet).erase (R.xi 0)
    rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem hnAX]
  · apply Finset.image_injective (f := fun x : ℤ => x + (v.val : ℤ))
      (fun _ _ h => add_right_cancel h)
    rw [hJcols, Profile.join_colSet, Finset.image_union, Finset.image_image,
      Profile.join_rowSet]
    simp only [Function.comp_def, sub_add_cancel]
    change (AY ∪ RY) \ (AX ∪ RX) = _
    rw [hsets.2, ← hCcols, distinguished_merge_shifted_colSet, hspan]
    change AY.erase (R.xi 0) ∪ (C.toBetaDiagram.colSet.image (fun x => x + (v.val : ℤ))) =
      (AY ∪ C.toBetaDiagram.colSet.image (fun x => x + (v.val : ℤ))).erase (R.xi 0)
    rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem hnCY]

end SkewClassInflation
