/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalRemovalRegularity

/-!
# Original source index enumeration

Supports `shields-2026-skew-corner-descent.tex`, «Equal windows and the determinant defect»
(`sec:normal-chart`, `lem:actual-elimination`). Canonical blocks enumerate the entire
original complementary source, without repeated representatives or dropped empty rows.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- Complete source index at a position in one canonical original block. -/
def originalBlockIndex {n : ℕ} (P : Profile n)
    (j : Σ b : OriginalBlocks P, Fin (interiorBlockLength P b.val + 1)) : Fin n :=
  interiorSliceIndex (interiorBlockFirst P j.1.val).val (interiorBlockLength P j.1.val)
    (interiorBlock_interval_bound P j.1.val) j.2

/-- Each enumerated source index has exactly its representative's produced block label. -/
theorem originalBlockIndex_label {n : ℕ} (P : Profile n)
    (j : Σ b : OriginalBlocks P, Fin (interiorBlockLength P b.val + 1)) :
    interiorBlock P (originalBlockIndex P j) = interiorBlock P j.1.val := by
  have hfirst : interiorSliceIndex (interiorBlockFirst P j.1.val).val
      (interiorBlockLength P j.1.val) (interiorBlock_interval_bound P j.1.val) 0 = j.1.val := by
    apply Fin.ext
    simp only [interiorSliceIndex, Fin.val_zero, add_zero, j.1.property]
  exact (interiorBlock_slice_same P j.1.val j.2).trans (by rw [hfirst])

/-- The complete source enumeration is injective across blocks and within every block. -/
theorem originalBlockIndex_injective {n : ℕ} (P : Profile n) :
    Function.Injective (originalBlockIndex P) := by
  rintro ⟨b, j⟩ ⟨d, k⟩ he
  have hb : b = d := originalBlocks_label_injective P
    ((originalBlockIndex_label P ⟨b, j⟩).symm.trans
      ((congrArg (interiorBlock P) he).trans (originalBlockIndex_label P ⟨d, k⟩)))
  subst d
  have hv := congrArg Fin.val he
  change (interiorBlockFirst P b.val).val + j.val =
    (interiorBlockFirst P b.val).val + k.val at hv
  have hj : j = k := Fin.ext (by omega)
  subst k
  rfl

/-- Every original complementary index occurs in the canonical source enumeration. -/
theorem originalBlockIndex_surjective {n : ℕ} (P : Profile n) :
    Function.Surjective (originalBlockIndex P) := by
  intro i
  let b : OriginalBlocks P := ⟨interiorBlockFirst P i, interiorBlockFirst_idem P i⟩
  have hl : interiorBlock P b.val = interiorBlock P i :=
    (mem_interiorBlockFiber P i _).mp (interiorBlockFirst_mem P i)
  have hm : i ∈ interiorBlockFiber P b.val := (mem_interiorBlockFiber P b.val i).mpr hl.symm
  obtain ⟨ha, hb⟩ := (mem_interiorBlockFiber_iff P b.val i).mp hm
  have ha' := Fin.le_def.mp ha
  have hb' := Fin.le_def.mp hb
  let j : Fin (interiorBlockLength P b.val + 1) :=
    ⟨i.val - (interiorBlockFirst P b.val).val, by unfold interiorBlockLength; omega⟩
  refine ⟨⟨b, j⟩, ?_⟩
  apply Fin.ext
  change (interiorBlockFirst P b.val).val +
    (i.val - (interiorBlockFirst P b.val).val) = i.val
  omega

/-- The entire actual block source and the original complementary list are bijective. -/
noncomputable def originalBlockIndexEquiv {n : ℕ} (P : Profile n) :
    (Σ b : OriginalBlocks P, Fin (interiorBlockLength P b.val + 1)) ≃ Fin n :=
  Equiv.ofBijective (originalBlockIndex P)
    ⟨originalBlockIndex_injective P, originalBlockIndex_surjective P⟩

end SkewCornerDescent.Matrix
