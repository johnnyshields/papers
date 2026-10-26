/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalMonicTopUniqueness
import SkewCornerDescent.Matrix.OriginalPositiveInventories
import SkewCornerDescent.FinitePeriodicWords

/-!
# Finite classes of complete original diagonal response residues

Supports `shields-2026-skew-corner-descent.tex` (`lem:exposure`, `lem:dual-identities`).
Classes are the literal finite image of the whole original retained diagonal,
including both true caps. A representative comes from that actual matrix. Its top
is independent of the representative, and the period word retains every position.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The complete retained diagonal's distinct actual residue values, including
both true caps; equal values are merged only in this class set, not in the word. -/
noncomputable def originalResponseClasses {n : ℕ} (P : Profile n) :
    Finset (OtherField c.top) := by
  classical
  exact Finset.univ.image (fun i => c.regularResidue (c.originalHessenbergResponse P i i))

/-- A class is an actual original response value with its finite-image witness. -/
abbrev OriginalResponseClass {n : ℕ} (P : Profile n) := ↥(c.originalResponseClasses P)

noncomputable instance {n : ℕ} (P : Profile n) : Fintype (c.OriginalResponseClass P) := by
  classical
  infer_instance

noncomputable instance {n : ℕ} (P : Profile n) : DecidableEq (c.OriginalResponseClass P) :=
  Classical.decEq _

/-- Every original diagonal position supplies its own literal response class. -/
noncomputable def originalResponseClassOf {n : ℕ} (P : Profile n)
    (i : Fin (originalSelectedCount (hD := hD) P + 1)) : c.OriginalResponseClass P := by
  classical
  exact ⟨c.regularResidue (c.originalHessenbergResponse P i i), Finset.mem_image_of_mem _
    (Finset.mem_univ i)⟩

/-- A representative is selected from the complete original matrix, never from
an independently assigned response family. -/
noncomputable def originalResponseClassIndex {n : ℕ} (P : Profile n)
    (a : c.OriginalResponseClass P) : Fin (originalSelectedCount (hD := hD) P + 1) := by
  classical
  exact Classical.choose (Finset.mem_image.mp a.property)

/-- The representative's residue is exactly the class value. -/
theorem originalResponseClassIndex_spec {n : ℕ} (P : Profile n) (a : c.OriginalResponseClass P) :
    c.regularResidue (c.originalHessenbergResponse P (c.originalResponseClassIndex P a)
      (c.originalResponseClassIndex P a)) = a.val := by
  classical
  exact (Classical.choose_spec (Finset.mem_image.mp a.property)).2

/-- The top of the actual representative, invariant under equal response values. -/
noncomputable def originalResponseClassTop {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P) (a : c.OriginalResponseClass P) : ℕ+ :=
  c.originalHessenbergTop P hB (c.originalResponseClassIndex P a)
    (c.originalResponseClassIndex P a) le_rfl

/-- Every actual class retains a top strictly above the selected generator. -/
theorem originalResponseClassTop_gt {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P) (a : c.OriginalResponseClass P) :
    c.top < c.originalResponseClassTop P hB a := by
  let i := c.originalResponseClassIndex P a
  have hd := c.originalHessenbergDistance_gt_top P hB i i le_rfl
  have hc := c.originalHessenbergTop_coe P hB i i le_rfl
  exact_mod_cast (show (c.top : ℤ) < (c.originalResponseClassTop P hB a : ℤ) by
    dsimp only [originalResponseClassTop]
    dsimp only [i] at hd hc
    omega)

/-- Classifying a literal position preserves its actual protected endpoint top. -/
theorem originalResponseClassTop_of {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (i : Fin (originalSelectedCount (hD := hD) P + 1)) :
    c.originalResponseClassTop P hB (c.originalResponseClassOf P i) =
      c.originalHessenbergTop P hB i i le_rfl := by
  apply c.originalHessenberg_top_eq_of_residue_eq P P hB hB
  exact c.originalResponseClassIndex_spec P (c.originalResponseClassOf P i)

/-- Every represented actual class is a unit on the selected chart, with its
component bound supplied by the source rather than by the class representation. -/
theorem originalResponseClass_ne_zero {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (a : c.OriginalResponseClass P) : a.val ≠ 0 := by
  rw [← c.originalResponseClassIndex_spec P a]
  exact c.originalHessenberg_residue_ne_zero P hB hmax _

/-- The actual internal-period word in the finite class set. Each literal start
remains, including repeated occurrences of the same field value. -/
noncomputable def originalResponseClassWord {n : ℕ} (P : Profile n)
    (j : ℕ) [NeZero j] (hperiod : j ≤ originalSelectedCount (hD := hD) P - 1) :
    ZMod j → c.OriginalResponseClass P := fun z =>
  c.originalResponseClassOf P ⟨z.val + 1, by have := ZMod.val_lt z; omega⟩

/-- Reading class values recovers the literal original period response cycle. -/
theorem originalResponseClassWord_val {n : ℕ} (P : Profile n)
    (j : ℕ) [NeZero j] (hperiod : j ≤ originalSelectedCount (hD := hD) P - 1) :
    (fun z => (c.originalResponseClassWord P j hperiod z).val) =
      finiteWordCycle (n := j) (c.originalInternalResidue P) hperiod := by
  rfl

end SkewCornerDescent.Matrix.SelectedCoordinate
