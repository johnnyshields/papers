/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCofactorIndependence.KernelDilation

/-!
# Nullity increments of actual unit kernels

`cor:nullity-increment` follows from the actual kernel linear equivalence and
the exact orbit count of the off-grid residue space.  The subtraction-free
identity also records that the displayed natural-number numerator cannot
underflow.
-/

noncomputable section
namespace SkewCofactorIndependence
namespace BetaDiagram
variable {n : ℕ}

/-- The actual available-position restriction preserves every off-grid residue coordinate. -/
theorem offGridRestriction_finrank (D : BetaDiagram (n + 1)) (t : ℕ+)
    (hn : 1 ≤ n) (hD : D.Normalized) :
    Module.finrank ℚ (D.arithmeticOffGrid t) =
      Module.finrank ℚ (offGridResidueSpace (t : ℕ) D.endpointModulus D.span) := by
  let : NeZero D.endpointModulus := ⟨ne_of_gt (D.endpointModulus_pos hn)⟩
  let : NeZero (t : ℕ) := ⟨t.ne_zero⟩
  have he : offGridResidueSpace (t : ℕ) D.endpointModulus D.span ≃ₗ[ℚ]
      (D.offGridRestriction t).range :=
    LinearEquiv.ofBijective (D.offGridRestriction t).rangeRestrict
      ⟨fun x y h => D.offGridRestriction_injective t hn hD (congrArg Subtype.val h),
        by rintro ⟨c, φ, rfl⟩; exact ⟨φ, rfl⟩⟩
  rw [← D.offGridRestriction_range t]
  exact he.finrank_eq.symm

/-- The base nullity is retained in its entirety. -/
theorem dilation_nullity_add (D : BetaDiagram (n + 1)) (t : ℕ+)
    (hn : 1 ≤ n) (hconn : D.Connected) (hz : D.ZeroFree) (hD : D.Normalized)
    (hind : LinearIndependent ℚ (fun ij : Fin (n + 1) × Fin (n + 1) =>
      D.cofactor ij.1 ij.2)) :
    Module.finrank ℚ (D.dilate t).unitKernel = Module.finrank ℚ D.unitKernel +
      Module.finrank ℚ (offGridResidueSpace (t : ℕ) D.endpointModulus D.span) := by
  let : NeZero D.endpointModulus := ⟨ne_of_gt (D.endpointModulus_pos hn)⟩
  let : NeZero (t : ℕ) := ⟨t.ne_zero⟩
  rw [← (D.dilationKernelEquiv t hn hconn hz hD hind).finrank_eq,
    Module.finrank_prod]

/-- The exact subtraction-free form of `eq:nullity-increment`. -/
theorem dilation_nullity_exact (D : BetaDiagram (n + 1)) (t : ℕ+)
    (hn : 1 ≤ n) (hconn : D.Connected) (hz : D.ZeroFree) (hD : D.Normalized)
    (hind : LinearIndependent ℚ (fun ij : Fin (n + 1) × Fin (n + 1) =>
      D.cofactor ij.1 ij.2)) :
    letI : NeZero D.endpointModulus := ⟨ne_of_gt (D.endpointModulus_pos hn)⟩
    letI : NeZero (t : ℕ) := ⟨t.ne_zero⟩
    2 * Module.finrank ℚ (D.dilate t).unitKernel +
        fixedCount ((t : ℕ) * D.endpointModulus) ((t : ℕ) * D.span) =
      2 * Module.finrank ℚ D.unitKernel +
        ((t : ℕ) - 1) * D.endpointModulus + fixedCount D.endpointModulus D.span := by
  let : NeZero D.endpointModulus := ⟨ne_of_gt (D.endpointModulus_pos hn)⟩
  let : NeZero (t : ℕ) := ⟨t.ne_zero⟩
  have h := offGrid_dimension_exact (t : ℕ) D.endpointModulus D.span
  rw [D.dilation_nullity_add t hn hconn hz hD hind]
  omega

/-- Natural-number nullity difference, with safe order of subtraction in the numerator. -/
theorem dilation_nullity_increment (D : BetaDiagram (n + 1)) (t : ℕ+)
    (hn : 1 ≤ n) (hconn : D.Connected) (hz : D.ZeroFree) (hD : D.Normalized)
    (hind : LinearIndependent ℚ (fun ij : Fin (n + 1) × Fin (n + 1) =>
      D.cofactor ij.1 ij.2)) :
    letI : NeZero D.endpointModulus := ⟨ne_of_gt (D.endpointModulus_pos hn)⟩
    letI : NeZero (t : ℕ) := ⟨t.ne_zero⟩
    Module.finrank ℚ (D.dilate t).unitKernel - Module.finrank ℚ D.unitKernel =
      (((t : ℕ) - 1) * D.endpointModulus + fixedCount D.endpointModulus D.span -
        fixedCount ((t : ℕ) * D.endpointModulus) ((t : ℕ) * D.span)) / 2 := by
  let : NeZero D.endpointModulus := ⟨ne_of_gt (D.endpointModulus_pos hn)⟩
  let : NeZero (t : ℕ) := ⟨t.ne_zero⟩
  rw [D.dilation_nullity_add t hn hconn hz hD hind, Nat.add_sub_cancel_left,
    offGrid_dimension]

/-- The manuscript's signed subtraction is exact when read in the integers. -/
theorem dilation_nullity_increment_int (D : BetaDiagram (n + 1)) (t : ℕ+)
    (hn : 1 ≤ n) (hconn : D.Connected) (hz : D.ZeroFree) (hD : D.Normalized)
    (hind : LinearIndependent ℚ (fun ij : Fin (n + 1) × Fin (n + 1) =>
      D.cofactor ij.1 ij.2)) :
    letI : NeZero D.endpointModulus := ⟨ne_of_gt (D.endpointModulus_pos hn)⟩
    letI : NeZero (t : ℕ) := ⟨t.ne_zero⟩
    2 * ((Module.finrank ℚ (D.dilate t).unitKernel : ℤ) -
        (Module.finrank ℚ D.unitKernel : ℤ)) =
      ((t : ℤ) - 1) * (D.endpointModulus : ℤ) -
        (fixedCount ((t : ℕ) * D.endpointModulus) ((t : ℕ) * D.span) : ℤ) +
        (fixedCount D.endpointModulus D.span : ℤ) := by
  let : NeZero D.endpointModulus := ⟨ne_of_gt (D.endpointModulus_pos hn)⟩
  let : NeZero (t : ℕ) := ⟨t.ne_zero⟩
  have h := D.dilation_nullity_exact t hn hconn hz hD hind
  have ht : (((t : ℕ) - 1 : ℕ) : ℤ) = (t : ℤ) - 1 := by
    exact Nat.cast_sub t.property
  have hi := congrArg (fun k : ℕ => (k : ℤ)) h
  push_cast at hi
  rw [ht] at hi
  linarith

/-- Modulus one gives the floor formula for every positive dilation, including one and two. -/
theorem dilation_nullity_modulus_one (D : BetaDiagram (n + 1)) (t : ℕ+)
    (hn : 1 ≤ n) (hconn : D.Connected) (hz : D.ZeroFree) (hD : D.Normalized)
    (hind : LinearIndependent ℚ (fun ij : Fin (n + 1) × Fin (n + 1) =>
      D.cofactor ij.1 ij.2)) (hg : D.endpointModulus = 1) :
    Module.finrank ℚ (D.dilate t).unitKernel - Module.finrank ℚ D.unitKernel =
      ((t : ℕ) - 1) / 2 := by
  let : NeZero (t : ℕ) := ⟨t.ne_zero⟩
  rw [D.dilation_nullity_add t hn hconn hz hD hind, Nat.add_sub_cancel_left,
    hg, offGrid_dimension_modulus_one]

/-- Nullity decomposition for arbitrary beta translations, without a normalization hypothesis. -/
theorem dilation_nullity_add_general (D : BetaDiagram (n + 1)) (t : ℕ+)
    (hn : 1 ≤ n) (hconn : D.Connected) (hz : D.ZeroFree)
    (hind : LinearIndependent ℚ (fun ij : Fin (n + 1) × Fin (n + 1) =>
      D.cofactor ij.1 ij.2)) :
    Module.finrank ℚ (D.dilate t).unitKernel = Module.finrank ℚ D.unitKernel +
      Module.finrank ℚ (offGridResidueSpace (t : ℕ)
        D.normalizeBetas.endpointModulus D.normalizeBetas.span) := by
  let : NeZero D.normalizeBetas.endpointModulus :=
    ⟨ne_of_gt (D.normalizeBetas.endpointModulus_pos hn)⟩
  let : NeZero (t : ℕ) := ⟨t.ne_zero⟩
  rw [← (D.dilationKernelEquivGeneral t hn hconn hz hind).finrank_eq,
    Module.finrank_prod]

/-- `cor:nullity-increment` is invariant under the common translation used to normalize a core. -/
theorem dilation_nullity_increment_general (D : BetaDiagram (n + 1)) (t : ℕ+)
    (hn : 1 ≤ n) (hconn : D.Connected) (hz : D.ZeroFree)
    (hind : LinearIndependent ℚ (fun ij : Fin (n + 1) × Fin (n + 1) =>
      D.cofactor ij.1 ij.2)) :
    letI : NeZero D.normalizeBetas.endpointModulus :=
      ⟨ne_of_gt (D.normalizeBetas.endpointModulus_pos hn)⟩
    letI : NeZero (t : ℕ) := ⟨t.ne_zero⟩
    Module.finrank ℚ (D.dilate t).unitKernel - Module.finrank ℚ D.unitKernel =
      (((t : ℕ) - 1) * D.normalizeBetas.endpointModulus +
        fixedCount D.normalizeBetas.endpointModulus D.normalizeBetas.span -
        fixedCount ((t : ℕ) * D.normalizeBetas.endpointModulus)
          ((t : ℕ) * D.normalizeBetas.span)) / 2 := by
  let : NeZero D.normalizeBetas.endpointModulus :=
    ⟨ne_of_gt (D.normalizeBetas.endpointModulus_pos hn)⟩
  let : NeZero (t : ℕ) := ⟨t.ne_zero⟩
  rw [D.dilation_nullity_add_general t hn hconn hz hind, Nat.add_sub_cancel_left,
    offGrid_dimension]

/-- The modulus-one specialization also holds in the core's original, unnormalized coordinates. -/
theorem dilation_nullity_modulus_one_general (D : BetaDiagram (n + 1)) (t : ℕ+)
    (hn : 1 ≤ n) (hconn : D.Connected) (hz : D.ZeroFree)
    (hind : LinearIndependent ℚ (fun ij : Fin (n + 1) × Fin (n + 1) =>
      D.cofactor ij.1 ij.2)) (hg : D.normalizeBetas.endpointModulus = 1) :
    Module.finrank ℚ (D.dilate t).unitKernel - Module.finrank ℚ D.unitKernel =
      ((t : ℕ) - 1) / 2 := by
  let : NeZero (t : ℕ) := ⟨t.ne_zero⟩
  rw [D.dilation_nullity_add_general t hn hconn hz hind, Nat.add_sub_cancel_left,
    hg, offGrid_dimension_modulus_one]

end BetaDiagram
end SkewCofactorIndependence
