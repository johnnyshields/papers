/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.ResidueHigherPolynomial
import SkewCornerDescent.Matrix.OriginalNormalDerivative

/-!
# Recovery from full triangular effective incoming coordinates

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`). Each
effective coordinate is monic in its own original higher generator with a full
strict lower rational correction. Finite linear combinations over the selected
lower field are still independent. No earlier coupling is frozen or discarded.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing
open scoped BigOperators

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Full strictly triangular higher coordinates remain linearly independent
for finite inventories over the actual selected lower field. -/
theorem triangular_higher_linear_zero
    (L : ResidueHigherIndex c.top → OtherField c.top)
    (s : Finset (ResidueHigherIndex c.top))
    (hL : ∀ j ∈ s, ∃ R ∈ residueLowerField c.top j.val,
      L j = residueGenerator c.top ⟨j.val, ne_of_gt j.prop⟩ + R)
    (a : ResidueHigherIndex c.top → residueLowerField c.top c.top)
    (hsum : (∑ j ∈ s, (a j : OtherField c.top) * L j) = 0) :
    ∀ j ∈ s, a j = 0 := by
  classical
  by_contra hnot
  push Not at hnot
  obtain ⟨j₀, hj₀, ha₀⟩ := hnot
  let t := s.filter fun j => a j ≠ 0
  have ht : t.Nonempty := ⟨j₀, Finset.mem_filter.mpr ⟨hj₀, ha₀⟩⟩
  let j := t.max' ht
  have hj : j ∈ t := Finset.max'_mem t ht
  have haj : a j ≠ 0 := (Finset.mem_filter.mp hj).2
  have hsumt : (∑ l ∈ t, (a l : OtherField c.top) * L l) = 0 := by
    rw [Finset.sum_subset (Finset.filter_subset (fun l => a l ≠ 0) s)]
    · exact hsum
    · intro l hl hlt
      have hal : a l = 0 := by
        by_contra hn
        exact hlt (Finset.mem_filter.mpr ⟨hl, hn⟩)
      rw [hal]
      simp
  have haLower (l : ResidueHigherIndex c.top) :
      (a l : OtherField c.top) ∈ residueLowerField c.top j.val :=
    residueLowerField_mono j.prop.le (a l).property
  have hderivLower (l : ResidueHigherIndex c.top) :
      residueGeneratorDeriv c.top ⟨j.val, ne_of_gt j.prop⟩ (a l : OtherField c.top) = 0 :=
    residueGeneratorDeriv_lower c.top ⟨j.val, ne_of_gt j.prop⟩ (haLower l)
  have hLj : residueGeneratorDeriv c.top ⟨j.val, ne_of_gt j.prop⟩ (L j) = 1 := by
    obtain ⟨R, hR, he⟩ := hL j (Finset.mem_filter.mp hj).1
    rw [he, map_add, residueGeneratorDeriv_generator,
      residueGeneratorDeriv_lower c.top ⟨j.val, ne_of_gt j.prop⟩ hR]
    simp
  have hLl (l : ResidueHigherIndex c.top) (hl : l ∈ t) (hne : l ≠ j) :
      residueGeneratorDeriv c.top ⟨j.val, ne_of_gt j.prop⟩ (L l) = 0 := by
    have hle : l ≤ j := Finset.le_max' t l hl
    have hlt : l.val < j.val := lt_of_le_of_ne hle (fun he => hne (Subtype.ext he))
    obtain ⟨R, hR, he⟩ := hL l (Finset.mem_filter.mp hl).1
    have hg : residueGenerator c.top ⟨l.val, ne_of_gt l.prop⟩ ∈
        residueLowerField c.top j.val := by
      have hg := c.residue_other_mem_lower j.val l.val (ne_of_gt l.prop) hlt
      rw [c.residueMap_other l.val (ne_of_gt l.prop)] at hg
      exact hg
    apply residueGeneratorDeriv_lower c.top ⟨j.val, ne_of_gt j.prop⟩
    rw [he]
    exact (residueLowerField c.top j.val).add_mem hg (residueLowerField_mono hlt.le hR)
  have hd := congrArg (residueGeneratorDeriv c.top ⟨j.val, ne_of_gt j.prop⟩) hsumt
  rw [map_sum, map_zero, Finset.sum_eq_single j] at hd
  · rw [Derivation.leibniz, hderivLower, hLj] at hd
    have hz : (a j : OtherField c.top) = 0 := by
      simpa only [smul_eq_mul, mul_one, mul_zero, add_zero] using hd
    exact haj (Subtype.ext hz)
  · intro l hl hne
    rw [Derivation.leibniz, hderivLower, hLl l hl hne]
    simp
  · intro h
    exact (h hj).elim

private theorem triangular_inventory_sum {ι : Type*} [Fintype ι]
    (L : ResidueHigherIndex c.top → OtherField c.top)
    (index : ι → ResidueHigherIndex c.top) (a : ι → residueLowerField c.top c.top)
    (s : Finset (ResidueHigherIndex c.top)) (hs : ∀ i, index i ∈ s) :
    (∑ j ∈ s, ((∑ i, if index i = j then a i else 0 :
      residueLowerField c.top c.top) : OtherField c.top) * L j) =
      ∑ i, (a i : OtherField c.top) * L (index i) := by
  classical
  have hcast (j) : ((∑ i, if index i = j then a i else 0 :
      residueLowerField c.top c.top) : OtherField c.top) =
      ∑ i, if index i = j then (a i : OtherField c.top) else 0 := by
    change (Subfield.subtype _) (∑ i, if index i = j then a i else 0) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases he : index i = j <;> simp [he]
  simp_rw [hcast, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single (index i)]
  · simp
  · intro j _ hji
    rw [ite_eq_right (Ne.symm hji), zero_mul]
  · intro h
    exact (h (hs i)).elim

/-- Distinct original high indices can be recovered after the complete earlier
prefix has replaced raw generators by common monic effective coordinates. -/
theorem triangular_higher_linear_support_eq {ι κ : Type*} [Fintype ι] [Fintype κ]
    (L : ResidueHigherIndex c.top → OtherField c.top)
    (left : ι → ResidueHigherIndex c.top) (right : κ → ResidueHigherIndex c.top)
    (hL : ∀ j ∈ Finset.univ.image left ∪ Finset.univ.image right,
      ∃ R ∈ residueLowerField c.top j.val,
        L j = residueGenerator c.top ⟨j.val, ne_of_gt j.prop⟩ + R)
    (hleft : Function.Injective left) (hright : Function.Injective right)
    (a : ι → residueLowerField c.top c.top) (b : κ → residueLowerField c.top c.top)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ j, b j ≠ 0)
    (hvalue : (∑ i, (a i : OtherField c.top) * L (left i)) =
      ∑ j, (b j : OtherField c.top) * L (right j)) :
    Finset.univ.image left = Finset.univ.image right := by
  classical
  let s := Finset.univ.image left ∪ Finset.univ.image right
  let A := fun j => ∑ i, if left i = j then a i else 0
  let B := fun j => ∑ i, if right i = j then b i else 0
  have hls (i) : left i ∈ s := Finset.mem_union_left _
    (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  have hrs (j) : right j ∈ s := Finset.mem_union_right _
    (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
  have hsum : (∑ j ∈ s, ((A j - B j : residueLowerField c.top c.top) :
      OtherField c.top) * L j) = 0 := by
    simp only [Subfield.coe_sub, sub_mul, Finset.sum_sub_distrib]
    rw [triangular_inventory_sum c L left a s hls,
      triangular_inventory_sum c L right b s hrs, hvalue, sub_self]
  have hcoeff := c.triangular_higher_linear_zero L s hL (fun j => A j - B j) hsum
  have hA (i) : A (left i) = a i := by
    dsimp only [A]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      exact ite_eq_right (fun he => hji (hleft he))
    · intro h
      exact (h (Finset.mem_univ i)).elim
  have hB (j) : B (right j) = b j := by
    dsimp only [B]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      exact ite_eq_right (fun he => hij (hright he))
    · intro h
      exact (h (Finset.mem_univ j)).elim
  apply Finset.Subset.antisymm
  · intro z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
    by_contra hnot
    have hzero : B (left i) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      exact ite_eq_right (fun he => hnot (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, he⟩))
    have he := hcoeff (left i) (hls i)
    rw [hA, hzero, sub_zero] at he
    exact ha i he
  · intro z hz
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hz
    by_contra hnot
    have hzero : A (right j) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      exact ite_eq_right (fun he => hnot (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, he⟩))
    have he := hcoeff (right j) (hrs j)
    rw [hzero, hB, zero_sub] at he
    exact hb j (neg_eq_zero.mp he)

end SkewCornerDescent.Matrix.SelectedCoordinate
