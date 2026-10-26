/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.RegularResidue
import SkewCornerDescent.Matrix.BlockResponse

/-!
# Complete block elimination in the actual local ring

Supports `shields-2026-skew-corner-descent.tex`, «Equal windows and the determinant defect»
(`sec:normal-chart`, `lem:actual-elimination`). A removed polynomial block whose determinant
avoids the selected prime has a produced inverse in the actual local ring. Embedding and
residue commute with its complete Schur complement, including every inverse entry. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- Entrywise transport of a produced square-matrix inverse. -/
@[instance_reducible]
def mappedInverse {R S n : Type*} [CommRing R] [CommRing S]
    [Fintype n] [DecidableEq n] (f : R →+* S) (P : Matrix n n R)
    [Invertible P] : Invertible (P.map f) :=
  Invertible.map f.mapMatrix P

/-- A ring homomorphism transports the full retained response and its full inverse. -/
theorem map_retainedResponse {R S m n : Type*} [CommRing R] [CommRing S]
    [Fintype n] [DecidableEq n] (f : R →+* S)
    (A : Matrix m m R) (B : Matrix m n R) (C : Matrix n m R) (P : Matrix n n R)
    [Invertible P] :
    let _ := mappedInverse f P
    (retainedResponse A B C P).map f =
      retainedResponse (A.map f) (B.map f) (C.map f) (P.map f) := by
  let := mappedInverse f P
  let := Invertible.map f.mapMatrix P
  have hi : (⅟P).map f = ⅟(P.map f) := map_invOf f.mapMatrix P
  ext i j
  simp only [retainedResponse, Matrix.map_apply, Matrix.sub_apply, map_sub,
    Matrix.mul_apply, map_sum, map_mul]
  simp_rw [show ∀ k l, f ((⅟P) k l) = (⅟(P.map f)) k l from
    fun k l => congrFun (congrFun hi k) l]

namespace SelectedCoordinate

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The removed block's determinant is a genuine unit of the selected local ring. -/
theorem regularMatrix_det_isUnit (P : Matrix n n Lambda)
    (hP : ¬ cellSchur D hD.1 ∣ P.det) :
    IsUnit ((algebraMap Lambda c.RegularRing).mapMatrix P).det := by
  rw [← RingHom.map_det]
  apply IsLocalization.map_units c.RegularRing
    (⟨P.det, ?_⟩ : c.selectedIdeal.primeCompl)
  change P.det ∉ c.selectedIdeal
  rwa [c.mem_selectedIdeal]

/-- Construct the complete removed inverse from the proved regular determinant. -/
@[instance_reducible]
noncomputable def regularMatrixInverse (P : Matrix n n Lambda)
    (hP : ¬ cellSchur D hD.1 ∣ P.det) :
    Invertible (P.map (algebraMap Lambda c.RegularRing)) :=
  ((Matrix.isUnit_iff_isUnit_det _).mpr (c.regularMatrix_det_isUnit P hP)).invertible

/-- The complete retained matrix is formed before taking its residue. -/
noncomputable def localRetainedResponse {m : Type*}
    (A : Matrix m m Lambda) (B : Matrix m n Lambda) (C : Matrix n m Lambda)
    (P : Matrix n n Lambda) (hP : ¬ cellSchur D hD.1 ∣ P.det) : Matrix m m c.RegularRing :=
  let _ := c.regularMatrixInverse P hP
  retainedResponse (A.map (algebraMap Lambda c.RegularRing))
    (B.map (algebraMap Lambda c.RegularRing)) (C.map (algebraMap Lambda c.RegularRing))
    (P.map (algebraMap Lambda c.RegularRing))

/-- Full block determinant factorization holds already in the local ring. -/
theorem local_det_eq_removed_mul_response {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m m Lambda) (B : Matrix m n Lambda) (C : Matrix n m Lambda)
    (P : Matrix n n Lambda) (hP : ¬ cellSchur D hD.1 ∣ P.det) :
    algebraMap Lambda c.RegularRing (Matrix.fromBlocks A B C P).det =
      algebraMap Lambda c.RegularRing P.det * (c.localRetainedResponse A B C P hP).det := by
  let := c.regularMatrixInverse P hP
  rw [RingHom.map_det, RingHom.map_det]
  change ((Matrix.fromBlocks A B C P).map (algebraMap Lambda c.RegularRing)).det = _
  rw [Matrix.fromBlocks_map]
  exact det_eq_removed_mul_response (A.map (algebraMap Lambda c.RegularRing))
    (B.map (algebraMap Lambda c.RegularRing)) (C.map (algebraMap Lambda c.RegularRing))
    (P.map (algebraMap Lambda c.RegularRing))

/-- The residue block inverse is produced by specializing the complete local inverse. -/
@[instance_reducible]
noncomputable def regularResidueMatrixInverse (P : Matrix n n Lambda)
    (hP : ¬ cellSchur D hD.1 ∣ P.det) : Invertible (P.map c.residueMap) := by
  letI := c.regularMatrixInverse P hP
  have hmap : (P.map (algebraMap Lambda c.RegularRing)).map c.regularResidue =
      P.map c.residueMap := by
    ext i j
    exact c.regularResidue_polynomial (P i j)
  exact hmap ▸ mappedInverse c.regularResidue (P.map (algebraMap Lambda c.RegularRing))

set_option backward.isDefEq.respectTransparency false in
/-- The complete block response specializes by the actual residue homomorphism. -/
theorem localRetainedResponse_residue {m : Type*}
    (A : Matrix m m Lambda) (B : Matrix m n Lambda) (C : Matrix n m Lambda)
    (P : Matrix n n Lambda) (hP : ¬ cellSchur D hD.1 ∣ P.det) :
    let _ := c.regularResidueMatrixInverse P hP
    (c.localRetainedResponse A B C P hP).map c.regularResidue =
      retainedResponse (A.map c.residueMap) (B.map c.residueMap)
        (C.map c.residueMap) (P.map c.residueMap) := by
  let := c.regularMatrixInverse P hP
  let := c.regularResidueMatrixInverse P hP
  have hmap (x : Lambda) : c.regularResidue (algebraMap Lambda c.RegularRing x) =
      c.residueMap x := c.regularResidue_polynomial x
  unfold localRetainedResponse
  simp only [retainedResponse, Matrix.invOf_eq_nonsing_inv]
  have h := map_retainedResponse c.regularResidue
    (A.map (algebraMap Lambda c.RegularRing)) (B.map (algebraMap Lambda c.RegularRing))
    (C.map (algebraMap Lambda c.RegularRing)) (P.map (algebraMap Lambda c.RegularRing))
  simp only [retainedResponse, Matrix.invOf_eq_nonsing_inv] at h
  simpa only [Matrix.map_map, Function.comp_def, hmap] using h

/-- The complete original-field block inverse is produced from its regular local inverse. -/
@[instance_reducible]
noncomputable def regularEmbeddedMatrixInverse (P : Matrix n n Lambda)
    (hP : ¬ cellSchur D hD.1 ∣ P.det) : Invertible (P.map originalMap) := by
  letI := c.regularMatrixInverse P hP
  have hmap : (P.map (algebraMap Lambda c.RegularRing)).map c.regularEmbedding =
      P.map originalMap := by
    ext i j
    exact c.regularEmbedding_polynomial (P i j)
  exact hmap ▸ mappedInverse c.regularEmbedding (P.map (algebraMap Lambda c.RegularRing))

set_option backward.isDefEq.respectTransparency false in
/-- The local retained response embeds as the complete original-field response. -/
theorem localRetainedResponse_embedding {m : Type*}
    (A : Matrix m m Lambda) (B : Matrix m n Lambda) (C : Matrix n m Lambda)
    (P : Matrix n n Lambda) (hP : ¬ cellSchur D hD.1 ∣ P.det) :
    let _ := c.regularEmbeddedMatrixInverse P hP
    (c.localRetainedResponse A B C P hP).map c.regularEmbedding =
      retainedResponse (A.map originalMap) (B.map originalMap)
        (C.map originalMap) (P.map originalMap) := by
  let := c.regularMatrixInverse P hP
  let := c.regularEmbeddedMatrixInverse P hP
  have hmap (x : Lambda) : c.regularEmbedding (algebraMap Lambda c.RegularRing x) =
      originalMap x := c.regularEmbedding_polynomial x
  unfold localRetainedResponse
  simp only [retainedResponse, Matrix.invOf_eq_nonsing_inv]
  have h := map_retainedResponse c.regularEmbedding
    (A.map (algebraMap Lambda c.RegularRing)) (B.map (algebraMap Lambda c.RegularRing))
    (C.map (algebraMap Lambda c.RegularRing)) (P.map (algebraMap Lambda c.RegularRing))
  simp only [retainedResponse, Matrix.invOf_eq_nonsing_inv] at h
  simpa only [Matrix.map_map, Function.comp_def, hmap] using h

end SelectedCoordinate
end SkewCornerDescent.Matrix
