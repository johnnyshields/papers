/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalResponseClassDefects

/-!
# Every internal primitive class is active

Formalizes `shields-2026-skew-corner-descent.tex` (`lem:residue-classifier`,
`thm:primitive-short`). At selected multiplicity one the complete original source
has fewer internal positions than its coprime outer count. A balanced class
therefore has no internal occurrences. Distinct literal response values supply
two active classes. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- At primitive multiplicity every retained internal occurrence belongs to an
active full-function equality class, including negative class exponents. -/
theorem originalPrimitive_internal_active {n m : ℕ} (P : Profile n) (W : Profile m)
    (a b : ℕ) (hcoprime : b.Coprime a)
    (hcount : originalSelectedCount (hD := hD) P = b)
    (i : Fin (originalSelectedCount (hD := hD) P - 1)) :
    c.originalResponseClassExponent P W a b
      (c.originalResponseClassOf P ⟨i.val + 1, by have := i.isLt; omega⟩) ≠ 0 := by
  classical
  let x := c.originalInternalResidue P i
  let countP := (Finset.univ.filter fun j => c.originalInternalResidue P j = x).card
  let countW := (Finset.univ.filter fun j => c.originalInternalResidue W j = x).card
  have hpos : 0 < countP := Finset.card_pos.mpr ⟨i, by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; rfl⟩
  have hle : countP ≤ b - 1 := by
    have hbound := Finset.card_filter_le (s := Finset.univ)
      (p := fun j => c.originalInternalResidue P j = x)
    simpa only [Finset.card_univ, Fintype.card_fin, hcount] using hbound
  intro hz
  have heq : (a : ℤ) * countP = (b : ℤ) * countW := by
    have hzero : (a : ℤ) * countP - (b : ℤ) * countW = 0 := hz
    exact sub_eq_zero.mp hzero
  have heqN : a * countP = b * countW := by exact_mod_cast heq
  have hdiv : b ∣ a * countP := by rw [heqN]; exact dvd_mul_right _ _
  have hzP := Nat.eq_zero_of_dvd_of_lt (hcoprime.dvd_of_dvd_mul_left hdiv)
    (show countP < b by omega)
  omega

/-- A nonconstant original internal word in a primitive chart supplies two
unbalanced actual classes. No plane classification or positivity is assumed. -/
theorem originalPrimitive_nonconstant_active {n m : ℕ} (P : Profile n) (W : Profile m)
    (a b : ℕ) (hcoprime : b.Coprime a)
    (hcount : originalSelectedCount (hD := hD) P = b)
    (hnonconstant : ∃ i j, c.originalInternalResidue P i ≠ c.originalInternalResidue P j) :
    ∃ X Y : c.OriginalResponseClass P, X ≠ Y ∧
      c.originalResponseClassExponent P W a b X ≠ 0 ∧
      c.originalResponseClassExponent P W a b Y ≠ 0 := by
  obtain ⟨i, j, hne⟩ := hnonconstant
  let X := c.originalResponseClassOf P ⟨i.val + 1, by have := i.isLt; omega⟩
  let Y := c.originalResponseClassOf P ⟨j.val + 1, by have := j.isLt; omega⟩
  refine ⟨X, Y, ?_, c.originalPrimitive_internal_active P W a b hcoprime hcount i,
    c.originalPrimitive_internal_active P W a b hcoprime hcount j⟩
  intro hXY
  exact hne (congrArg Subtype.val hXY)

/-- Every actual primitive internal position equals the unique active class;
the inactivity of all other classes cannot hide a balanced internal occurrence. -/
theorem originalPrimitive_internal_eq_unique_active {n m : ℕ} (P : Profile n) (W : Profile m)
    (a b : ℕ) (hcop : Nat.Coprime b a)
    (hcount : originalSelectedCount (hD := hD) P = b)
    (active : c.OriginalResponseClass P)
    (hother : ∀ X, X ≠ active → c.originalResponseClassExponent P W a b X = 0) :
    ∀ i, c.originalInternalResidue P i = active.val := by
  intro i
  by_contra hne
  have hX : c.originalResponseClassOf P ⟨i.val+1, by have := i.isLt; omega⟩ ≠ active :=
    fun he => hne (congrArg Subtype.val he)
  exact c.originalPrimitive_internal_active P W a b hcop hcount i (hother _ hX)

end SkewCornerDescent.Matrix.SelectedCoordinate
