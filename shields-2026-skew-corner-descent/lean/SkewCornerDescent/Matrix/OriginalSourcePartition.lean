/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalSourceIndices

/-!
# Exact original complementary partitions

Supports `shields-2026-skew-corner-descent.tex`, «Equal windows and the determinant defect»
(`sec:normal-chart`, `lem:actual-elimination`). Actual divisibility determines the retained
endpoints; every other original row and column occurs exactly once. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

attribute [local instance] Classical.propDecidable

variable {D : Diagram} {hD : IsConnectedSkew D}

abbrev OriginalSelectedBlocks {n : ℕ} (P : Profile n) :=
  {b : OriginalBlocks P // originalBlockSelected (hD := hD) P b}

abbrev OriginalRemainingIndices {n : ℕ} (P : Profile n) :=
  Σ b : OriginalBlocks P, Fin (originalRemovedSize (hD := hD) P b)

/-- Rows omitted from a selected block are its literal first row. -/
noncomputable def complementaryRowPartition {n : ℕ} (P : Profile n) :
    OriginalSelectedBlocks (hD := hD) P ⊕ OriginalRemainingIndices (hD := hD) P →
      Σ b : OriginalBlocks P, Fin (interiorBlockLength P b.val + 1)
  | .inl b => ⟨b.val, 0⟩
  | .inr j => ⟨j.1, originalRemovedRowPosition (hD := hD) P j.1 j.2⟩

/-- Columns omitted from a selected block are its literal last column. -/
noncomputable def complementaryColPartition {n : ℕ} (P : Profile n) :
    OriginalSelectedBlocks (hD := hD) P ⊕ OriginalRemainingIndices (hD := hD) P →
      Σ b : OriginalBlocks P, Fin (interiorBlockLength P b.val + 1)
  | .inl b => ⟨b.val, Fin.last _⟩
  | .inr j => ⟨j.1, originalRemovedColPosition (hD := hD) P j.1 j.2⟩

/-- Remaining rows advance by one exactly at selected blocks. -/
theorem originalRemovedRowPosition_val {n : ℕ} (P : Profile n) (b : OriginalBlocks P)
    (j : Fin (originalRemovedSize (hD := hD) P b)) :
    (originalRemovedRowPosition (hD := hD) P b j).val =
      if originalBlockSelected (hD := hD) P b then j.val + 1 else j.val := by
  by_cases hs : originalBlockSelected (hD := hD) P b
  · simp only [originalRemovedRowPosition, dite_eq_left hs, ite_eq_left hs]
  · simp only [originalRemovedRowPosition, dite_eq_right hs, ite_eq_right hs]

/-- Remaining columns keep their original positions. -/
theorem originalRemovedColPosition_val {n : ℕ} (P : Profile n) (b : OriginalBlocks P)
    (j : Fin (originalRemovedSize (hD := hD) P b)) :
    (originalRemovedColPosition (hD := hD) P b j).val = j.val := rfl

/-- A complementary row cannot occur twice, even across the retained/removed seam. -/
theorem complementaryRowPartition_injective {n : ℕ} (P : Profile n) :
    Function.Injective (complementaryRowPartition (hD := hD) P) := by
  rintro (b | ⟨b, j⟩) (d | ⟨d, k⟩) he
  · have hb : b.val = d.val := congrArg Sigma.fst he
    exact congrArg Sum.inl (Subtype.ext hb)
  · have hb : b.val = d := congrArg Sigma.fst he
    subst d
    have hv := congrArg (fun z => z.2.val) he
    change 0 = (originalRemovedRowPosition (hD := hD) P b.val k).val at hv
    rw [originalRemovedRowPosition_val, ite_eq_left b.property] at hv
    omega
  · have hb : b = d.val := congrArg Sigma.fst he
    subst b
    have hv := congrArg (fun z => z.2.val) he
    change (originalRemovedRowPosition (hD := hD) P d.val j).val = 0 at hv
    rw [originalRemovedRowPosition_val, ite_eq_left d.property] at hv
    omega
  · have hb : b = d := congrArg Sigma.fst he
    subst d
    have hv := congrArg (fun z => z.2.val) he
    change (originalRemovedRowPosition (hD := hD) P b j).val =
      (originalRemovedRowPosition (hD := hD) P b k).val at hv
    rw [originalRemovedRowPosition_val, originalRemovedRowPosition_val] at hv
    have hj : j = k := Fin.ext (by split_ifs at hv <;> omega)
    subst k
    rfl

/-- A complementary column cannot occur twice at its literal last-column seam. -/
theorem complementaryColPartition_injective {n : ℕ} (P : Profile n) :
    Function.Injective (complementaryColPartition (hD := hD) P) := by
  rintro (b | ⟨b, j⟩) (d | ⟨d, k⟩) he
  · have hb : b.val = d.val := congrArg Sigma.fst he
    exact congrArg Sum.inl (Subtype.ext hb)
  · have hb : b.val = d := congrArg Sigma.fst he
    subst d
    have hv := congrArg (fun z => z.2.val) he
    change interiorBlockLength P b.val = k.val at hv
    have hk := k.isLt
    simp only [originalRemovedSize, ite_eq_left b.property] at hk
    omega
  · have hb : b = d.val := congrArg Sigma.fst he
    subst b
    have hv := congrArg (fun z => z.2.val) he
    change j.val = interiorBlockLength P d.val at hv
    have hj := j.isLt
    simp only [originalRemovedSize, ite_eq_left d.property] at hj
    omega
  · have hb : b = d := congrArg Sigma.fst he
    subst d
    have hv := congrArg (fun z => z.2.val) he
    change j.val = k.val at hv
    have hj : j = k := Fin.ext hv
    subst k
    rfl

/-- Every complementary original row is retained or removed, with no missing index. -/
theorem complementaryRowPartition_surjective {n : ℕ} (P : Profile n) :
    Function.Surjective (complementaryRowPartition (hD := hD) P) := by
  rintro ⟨b, j⟩
  by_cases hs : originalBlockSelected (hD := hD) P b
  · by_cases hj : j.val = 0
    · refine ⟨.inl ⟨b, hs⟩, ?_⟩
      change ⟨b, 0⟩ = (⟨b, j⟩ : Σ d : OriginalBlocks P, Fin (interiorBlockLength P d.val + 1))
      congr 1
      exact Fin.ext hj.symm
    · have hjlt := j.isLt
      let k : Fin (originalRemovedSize (hD := hD) P b) := ⟨j.val - 1, by
        simp only [originalRemovedSize, ite_eq_left hs]
        omega⟩
      refine ⟨.inr ⟨b, k⟩, ?_⟩
      change ⟨b, originalRemovedRowPosition (hD := hD) P b k⟩ =
        (⟨b, j⟩ : Σ d : OriginalBlocks P, Fin (interiorBlockLength P d.val + 1))
      congr 1
      apply Fin.ext
      rw [originalRemovedRowPosition_val, ite_eq_left hs]
      change j.val - 1 + 1 = j.val
      omega
  · let k : Fin (originalRemovedSize (hD := hD) P b) := ⟨j.val, by
      simpa only [originalRemovedSize, ite_eq_right hs] using j.isLt⟩
    refine ⟨.inr ⟨b, k⟩, ?_⟩
    change ⟨b, originalRemovedRowPosition (hD := hD) P b k⟩ =
      (⟨b, j⟩ : Σ d : OriginalBlocks P, Fin (interiorBlockLength P d.val + 1))
    congr 1
    apply Fin.ext
    rw [originalRemovedRowPosition_val, ite_eq_right hs]

/-- Every complementary original column is retained or removed, including the last endpoint. -/
theorem complementaryColPartition_surjective {n : ℕ} (P : Profile n) :
    Function.Surjective (complementaryColPartition (hD := hD) P) := by
  rintro ⟨b, j⟩
  by_cases hs : originalBlockSelected (hD := hD) P b
  · by_cases hj : j.val = interiorBlockLength P b.val
    · refine ⟨.inl ⟨b, hs⟩, ?_⟩
      change ⟨b, Fin.last _⟩ =
        (⟨b, j⟩ : Σ d : OriginalBlocks P, Fin (interiorBlockLength P d.val + 1))
      congr 1
      exact Fin.ext hj.symm
    · have hjlt := j.isLt
      let k : Fin (originalRemovedSize (hD := hD) P b) := ⟨j.val, by
        simp only [originalRemovedSize, ite_eq_left hs]
        omega⟩
      refine ⟨.inr ⟨b, k⟩, ?_⟩
      change ⟨b, originalRemovedColPosition (hD := hD) P b k⟩ =
        (⟨b, j⟩ : Σ d : OriginalBlocks P, Fin (interiorBlockLength P d.val + 1))
      congr 1
  · let k : Fin (originalRemovedSize (hD := hD) P b) := ⟨j.val, by
      simpa only [originalRemovedSize, ite_eq_right hs] using j.isLt⟩
    refine ⟨.inr ⟨b, k⟩, ?_⟩
    change ⟨b, originalRemovedColPosition (hD := hD) P b k⟩ =
      (⟨b, j⟩ : Σ d : OriginalBlocks P, Fin (interiorBlockLength P d.val + 1))
    congr 1

/-- The produced complementary row partition is an exact original-source equivalence. -/
noncomputable def complementaryRowEquiv {n : ℕ} (P : Profile n) :
    OriginalSelectedBlocks (hD := hD) P ⊕ OriginalRemainingIndices (hD := hD) P ≃ Fin n :=
  (Equiv.ofBijective (complementaryRowPartition (hD := hD) P)
    ⟨complementaryRowPartition_injective P, complementaryRowPartition_surjective P⟩).trans
      (originalBlockIndexEquiv P)

/-- The produced complementary column partition is an exact original-source equivalence. -/
noncomputable def complementaryColEquiv {n : ℕ} (P : Profile n) :
    OriginalSelectedBlocks (hD := hD) P ⊕ OriginalRemainingIndices (hD := hD) P ≃ Fin n :=
  (Equiv.ofBijective (complementaryColPartition (hD := hD) P)
    ⟨complementaryColPartition_injective P, complementaryColPartition_surjective P⟩).trans
      (originalBlockIndexEquiv P)

/-- The global corner is adjoined once, without duplicating any complementary index. -/
def cornerOptionEquiv (α β : Type) : Option α ⊕ β ≃ Option (α ⊕ β) where
  toFun
    | .inl none => none
    | .inl (some a) => some (.inl a)
    | .inr b => some (.inr b)
  invFun
    | none => .inl none
    | some (.inl a) => .inl (some a)
    | some (.inr b) => .inr b
  left_inv x := by rcases x with ((_ | _) | _) <;> rfl
  right_inv x := by rcases x with (_ | (_ | _)) <;> rfl

/-- Full original rows split into actual retained endpoints and the complete removed source. -/
noncomputable def originalRowSplitEquiv {n : ℕ} (P : Profile n) :
    Option (OriginalSelectedBlocks (hD := hD) P) ⊕
      OriginalRemainingIndices (hD := hD) P ≃ Fin (n + 1) :=
  (cornerOptionEquiv _ _).trans
    ((Equiv.optionCongr (complementaryRowEquiv (hD := hD) P)).trans
      (finSuccEquiv' 0).symm)

/-- Full original columns retain the global last column and selected literal last columns. -/
noncomputable def originalColSplitEquiv {n : ℕ} (P : Profile n) :
    Option (OriginalSelectedBlocks (hD := hD) P) ⊕
      OriginalRemainingIndices (hD := hD) P ≃ Fin (n + 1) :=
  (cornerOptionEquiv _ _).trans
    ((Equiv.optionCongr (complementaryColEquiv (hD := hD) P)).trans
      (finSuccEquiv' (Fin.last n)).symm)

end SkewCornerDescent.Matrix.SelectedCoordinate
