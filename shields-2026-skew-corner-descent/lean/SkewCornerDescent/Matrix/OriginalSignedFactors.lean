/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalRemovedCancellation
import SkewCornerDescent.Matrix.OriginalResidueFactorization

/-!
# Fixed original determinant signs and full removed factors

Supports `shields-2026-skew-corner-descent.tex`, «Equal windows and the determinant defect»
(`sec:normal-chart`, `lem:actual-words`, `lem:residue-classifier`). Both source orientation
signs are retained as produced integer units. Equal actual corner powers cancel the entire
removed determinants, not normal-dependent inverse entries. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

attribute [local instance] Classical.propDecidable

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The complete normal-germ determinant factorization has a fixed produced integer sign. -/
theorem originalHessenberg_local_signed_factorization {n : ℕ} (P : Profile n) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      algebraMap Lambda c.RegularRing P.schur =
        (ε : c.RegularRing) *
          algebraMap Lambda c.RegularRing (originalRemovedMatrix (hD := hD) P).det *
          (c.originalHessenbergResponse P).det := by
  let σ := Equiv.Perm.sign ((originalHessenbergCols (hD := hD) P).symm.trans
    (originalHessenbergRows (hD := hD) P))
  let τ := Equiv.Perm.sign ((originalColSplitEquiv (hD := hD) P).symm.trans
    (originalRowSplitEquiv (hD := hD) P))
  let ε : ℤ := (σ : ℤ) * (τ : ℤ)
  have hε : ε = 1 ∨ ε = -1 := Int.isUnit_iff.mp (σ.isUnit.mul τ.isUnit)
  have hsq : (ε : c.RegularRing) ^ 2 = 1 := by
    rcases hε with h | h
    · simp only [h, Int.cast_one, one_pow]
    · simp only [h, Int.reduceNeg, Int.cast_neg, Int.cast_one, sq_eq_one_iff, or_true]
  have he := c.originalHessenbergResponse_local_det P
  rw [originalSplitMatrix_det (hD := hD) P, map_mul] at he
  have hs : (ε : c.RegularRing) * algebraMap Lambda c.RegularRing P.schur =
      algebraMap Lambda c.RegularRing (originalRemovedMatrix (hD := hD) P).det *
        (c.originalHessenbergResponse P).det := by
    simpa only [ε, Int.cast_mul, map_intCast, mul_assoc] using he
  refine ⟨ε, hε, ?_⟩
  calc
    _ = (ε : c.RegularRing) * ((ε : c.RegularRing) *
        algebraMap Lambda c.RegularRing P.schur) := by
      rw [← mul_assoc, ← pow_two, hsq, one_mul]
    _ = _ := by rw [hs, ← mul_assoc]

/-- At residue the same fixed sign accompanies the complete removed factor and every original
retained diagonal response. No maximal-span or factorization premise is required. -/
theorem originalHessenberg_residue_signed_factorization {n : ℕ} (P : Profile n) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      c.residueMap P.schur =
        (ε : OtherField c.top) * c.residueMap (originalRemovedMatrix (hD := hD) P).det *
          ∏ i, c.regularResidue (c.originalHessenbergResponse P i i) := by
  obtain ⟨ε, hε, he⟩ := c.originalHessenberg_local_signed_factorization P
  have hr := congrArg c.regularResidue he
  have hm : c.regularResidue (c.originalHessenbergResponse P).det =
      ((c.originalHessenbergResponse P).map c.regularResidue).det :=
    RingHom.map_det c.regularResidue _
  rw [map_mul, map_mul, map_intCast, c.regularResidue_polynomial,
    c.regularResidue_polynomial, hm,
    c.originalHessenbergResponse_residue_det] at hr
  exact ⟨ε, hε, hr⟩

/-- The actual lower scalar ratio is a produced fixed determinant sign whenever the two
corner inventories have equal corresponding powers. All multiplicity and removed-factor
cancellations are supplied inside the proof. -/
theorem originalHessenberg_residue_pair_normalization {n m : ℕ} (P : Profile n) (Q : Profile m)
    (hP : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (hQ : ∀ C ∈ edgeComponents (diagramInterior Q.cells), span C ≤ (c.top : ℕ))
    (b v : ℕ)
    (hcorner : (jtMatrix (fun j : Fin n => P.xi j.succ)
          (fun j => P.zeta j.castSucc)).det ^ v =
      (jtMatrix (fun j : Fin m => Q.xi j.succ)
          (fun j => Q.zeta j.castSucc)).det ^ b) :
    ∃ aP aQ : residueLowerField c.top c.top, ∃ ε : ℤ,
      (ε = 1 ∨ ε = -1) ∧ aP ≠ 0 ∧ aQ ≠ 0 ∧
        c.residueMap P.schur = (aP : OtherField c.top) *
          ∏ i, c.regularResidue (c.originalHessenbergResponse P i i) ∧
        c.residueMap Q.schur = (aQ : OtherField c.top) *
          ∏ i, c.regularResidue (c.originalHessenbergResponse Q i i) ∧
        aP ^ v / aQ ^ b = (ε : residueLowerField c.top c.top) := by
  obtain ⟨εP, hεP, hfP⟩ := c.originalHessenberg_residue_signed_factorization P
  obtain ⟨εQ, hεQ, hfQ⟩ := c.originalHessenberg_residue_signed_factorization Q
  obtain ⟨hdP, hdP0⟩ := c.originalRemoved_residue_lower_scalar P hP
  obtain ⟨hdQ, hdQ0⟩ := c.originalRemoved_residue_lower_scalar Q hQ
  let dP := c.residueMap (originalRemovedMatrix (hD := hD) P).det
  let dQ := c.residueMap (originalRemovedMatrix (hD := hD) Q).det
  let aP : residueLowerField c.top c.top :=
    ⟨(εP : OtherField c.top) * dP, (residueLowerField c.top c.top).mul_mem
      ((residueLowerField c.top c.top).intCast_mem εP) hdP⟩
  let aQ : residueLowerField c.top c.top :=
    ⟨(εQ : OtherField c.top) * dQ, (residueLowerField c.top c.top).mul_mem
      ((residueLowerField c.top c.top).intCast_mem εQ) hdQ⟩
  let ε := εP ^ v * εQ ^ b
  have hunitP : IsUnit εP := Int.isUnit_iff.mpr hεP
  have hunitQ : IsUnit εQ := Int.isUnit_iff.mpr hεQ
  have hε : ε = 1 ∨ ε = -1 := Int.isUnit_iff.mp ((hunitP.pow v).mul (hunitQ.pow b))
  have hpair := congrArg c.residueMap
    (originalRemovedMatrix_pair_power (hD := hD) P Q b v hcorner)
  rw [map_pow, map_pow] at hpair
  change dP ^ v = dQ ^ b at hpair
  have hinv : ((εQ : OtherField c.top) ^ b)⁻¹ = (εQ : OtherField c.top) ^ b := by
    rcases hεQ with h | h
    · simp only [h, Int.cast_one, one_pow, inv_one]
    · simp only [h, Int.reduceNeg, Int.cast_neg, Int.cast_one, ← inv_pow, inv_neg, inv_one]
  refine ⟨aP, aQ, ε, hε, ?_, ?_, hfP, hfQ, ?_⟩
  · intro hz
    have he := congrArg (fun z : residueLowerField c.top c.top => (z : OtherField c.top)) hz
    exact (mul_ne_zero (hunitP.map (Int.castRingHom (OtherField c.top))).ne_zero hdP0) he
  · intro hz
    have he := congrArg (fun z : residueLowerField c.top c.top => (z : OtherField c.top)) hz
    exact (mul_ne_zero (hunitQ.map (Int.castRingHom (OtherField c.top))).ne_zero hdQ0) he
  · apply Subtype.ext
    change ((εP : OtherField c.top) * dP) ^ v /
      ((εQ : OtherField c.top) * dQ) ^ b = (ε : OtherField c.top)
    rw [mul_pow, mul_pow, mul_div_mul_comm, hpair, div_self (pow_ne_zero b hdQ0),
      mul_one, div_eq_mul_inv, hinv]
    simp only [ε, Int.cast_mul, Int.cast_pow]

end SkewCornerDescent.Matrix.SelectedCoordinate
