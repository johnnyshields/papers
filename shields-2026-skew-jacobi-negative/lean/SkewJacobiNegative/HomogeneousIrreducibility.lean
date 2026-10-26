/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.GammaEncoding
import SkewJacobiNegative.ConnectedIrreducibility

/-!
# The determinant with an independent unit variable

The polynomial `P_D` and its irreducibility in `sec:five-base` of
`shields-2026-skew-jacobi-negative.tex`.  The proof reflects the actual
connected affine diagram's irreducibility through an odd-variable renaming.
The renaming has an explicit algebra-homomorphism left inverse; in particular
units, rather than only zero polynomials, are reflected.
-/

namespace SkewJacobiNegative

open MvPolynomial

/-- Includes the independent variable with index zero. -/
def homOddIndex (j : ℕ) : ℕ+ := ⟨2 * j + 1, by omega⟩

theorem homOddIndex_injective : Function.Injective homOddIndex := by
  intro i j h
  have := congrArg (fun k : ℕ+ => (k : ℕ)) h
  dsimp [homOddIndex] at this
  omega

/-- Retraction on the odd variables; the even variables can also be evaluated. -/
noncomputable def homOddRetraction : CompleteRing →ₐ[ℚ] Gluing.HomLambda :=
  aeval fun j : ℕ+ => X ((j : ℕ) / 2)

/-- The full polynomial ring map, including `H₀ ↦ h₁`. -/
noncomputable def homOddRename : Gluing.HomLambda →ₐ[ℚ] CompleteRing :=
  rename homOddIndex

@[simp] theorem homOddRetraction_rename (p : Gluing.HomLambda) :
    homOddRetraction (homOddRename p) = p := by
  have he : homOddRetraction.comp homOddRename = AlgHom.id ℚ Gluing.HomLambda := by
    apply MvPolynomial.algHom_ext
    intro j
    change homOddRetraction (rename homOddIndex (X j)) = X j
    rw [rename_X]
    change (aeval (fun k : ℕ+ => X ((k : ℕ) / 2))) (X (homOddIndex j)) = X j
    rw [aeval_X]
    congr 1
    dsimp [homOddIndex]
    omega
  exact congrArg (fun f : Gluing.HomLambda →ₐ[ℚ] Gluing.HomLambda => f p) he

theorem homOddRename_isUnit_iff (p : Gluing.HomLambda) :
    IsUnit (homOddRename p) ↔ IsUnit p :=
  ⟨fun h => by simpa using h.map homOddRetraction, fun h => h.map homOddRename⟩

@[simp] theorem homOddRename_hTilde (j : ℤ) :
    homOddRename (Gluing.hTilde j) = complete (2 * j + 1) := by
  by_cases hj : j < 0
  · have hh : 2 * j + 1 < 0 := by omega
    simp [Gluing.hTilde, hj, complete_of_neg hh]
  · have hh : 0 < 2 * j + 1 := by omega
    rw [Gluing.hTilde, if_neg hj, complete_of_pos hh]
    simp only [homOddRename, rename_X]
    congr 1
    apply Subtype.ext
    dsimp [homOddIndex]
    omega

namespace BetaDiagram

variable {n : ℕ}

/-- The actual full-order homogeneous matrix, not a specialized complete matrix. -/
noncomputable def homMatrix (D : BetaDiagram n) :
    Matrix (Fin n) (Fin n) Gluing.HomLambda :=
  Matrix.of fun i j => Gluing.hTilde (D.row i - D.col j)

/-- The manuscript's `P_D`, with every nonnegative generator independent. -/
noncomputable def homSchur (D : BetaDiagram n) : Gluing.HomLambda := D.homMatrix.det

/-- An exponent for each positive diagonal label, with multiplicities. -/
noncomputable def homDiagonalExponent (D : BetaDiagram n) : ℕ →₀ ℕ :=
  ∑ i : Fin n, Finsupp.single (D.rowLength i).toNat 1

@[simp] theorem homOddRename_homSchur (D : BetaDiagram n) :
    homOddRename D.homSchur = D.gamma.schur := by
  rw [homSchur, AlgHom.map_det]
  congr 1
  apply Matrix.ext
  intro i j
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, homMatrix, matrix,
    Matrix.of_apply, homOddRename_hTilde, gamma]
  congr 1
  ring

@[simp] theorem dehom_homSchur (D : BetaDiagram n) :
    Gluing.dehom D.homSchur = D.schur := by
  rw [homSchur, schur, AlgHom.map_det]
  congr 1
  apply Matrix.ext
  intro i j
  simp [AlgHom.mapMatrix_apply, Matrix.map_apply, homMatrix, matrix,
    Gluing.dehom_hTilde, complete_eq_hh]

/-- All determinant terms have full row degree, including index-zero entries. -/
theorem homSchur_isHomogeneous (D : BetaDiagram n) : D.homSchur.IsHomogeneous n := by
  classical
  rw [homSchur, Matrix.det_apply']
  refine IsHomogeneous.sum _ _ _ fun σ _ => ?_
  have hsign : ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : Gluing.HomLambda)).IsHomogeneous 0 := by
    rw [show ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : Gluing.HomLambda)) =
      C (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℚ) by simp]
    exact isHomogeneous_C _ _
  have hprod := IsHomogeneous.prod Finset.univ
    (fun i : Fin n => Gluing.hTilde (D.row (σ i) - D.col i))
    (fun _ => 1) (fun i _ => Gluing.isHomogeneous_hTilde _)
  simpa [homMatrix] using hsign.mul hprod

/-- The renamed diagonal is exactly the diagonal of the actual affine diagram. -/
theorem homDiagonalExponent_rename (D : BetaDiagram n) :
    D.homDiagonalExponent.mapDomain homOddIndex = D.gamma.diagonalExponent := by
  classical
  rw [homDiagonalExponent, Finsupp.mapDomain_finsetSum,
    diagonalExponent_eq_rowLengths, Base.exponentVector, List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  have hpos := D.gamma.rowLength_pos i
  simp only [Finsupp.mapDomain_single, Function.comp_apply]
  have hnat : 0 < (D.gamma.rowLength i).toNat := by omega
  simp only [Base.completeIndexExponent, dite_eq_left hnat]
  congr 1
  apply Subtype.ext
  dsimp [homOddIndex, rowLength, gamma]
  have h := D.row_nonempty i
  omega

/-- The coefficient one is unchanged even when other labels coincide. -/
theorem homSchur_diagonal_coefficient_one (D : BetaDiagram n) :
    D.homSchur.coeff D.homDiagonalExponent = 1 := by
  have hc := coeff_rename_mapDomain homOddIndex homOddIndex_injective
    D.homSchur D.homDiagonalExponent
  change (homOddRename D.homSchur).coeff
    (D.homDiagonalExponent.mapDomain homOddIndex) = D.homSchur.coeff D.homDiagonalExponent at hc
  rw [homOddRename_homSchur, homDiagonalExponent_rename, diagonal_coefficient_one] at hc
  exact hc.symm

@[simp] theorem homDiagonalExponent_zero (D : BetaDiagram n) :
    D.homDiagonalExponent 0 = 0 := by
  classical
  rw [homDiagonalExponent, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro i _
  have h := D.rowLength_pos i
  have hh : (D.rowLength i).toNat ≠ 0 := by omega
  simp [Finsupp.single_apply, hh]

/-- The diagonal witness excludes a factor of the independent unit variable. -/
theorem homSchur_unitVariable_not_dvd (D : BetaDiagram n) :
    ¬ (X 0 : Gluing.HomLambda) ∣ D.homSchur := by
  classical
  rintro ⟨p, hp⟩
  have hc := D.homSchur_diagonal_coefficient_one
  rw [hp, coeff_X_mul'] at hc
  simp [Finsupp.mem_support_iff] at hc

/-- The polynomial has ordinary degree equal to its full row count. -/
theorem homSchur_totalDegree (D : BetaDiagram n) : D.homSchur.totalDegree = n := by
  apply D.homSchur_isHomogeneous.totalDegree
  intro hz
  have hc := D.homSchur_diagonal_coefficient_one
  rw [hz] at hc
  simp at hc

/-- No irreducibility premise is imported: the connected affine diagram supplies it. -/
theorem homSchur_irreducible (D : BetaDiagram n) (hD : D.Connected) :
    Irreducible D.homSchur := by
  have hi := D.gamma.schur_irreducible ((D.gamma_connected_iff).mpr hD)
  refine ⟨?_, ?_⟩
  · intro hu
    exact hi.not_isUnit (by simpa using hu.map homOddRename)
  · intro a b hab
    have hm : D.gamma.schur = homOddRename a * homOddRename b := by
      rw [← homOddRename_homSchur, hab, map_mul]
    rcases hi.isUnit_or_isUnit hm with ha | hb
    · exact Or.inl ((homOddRename_isUnit_iff a).mp ha)
    · exact Or.inr ((homOddRename_isUnit_iff b).mp hb)

/-- Equality at the full homogeneous order is faithful for arbitrary mates. -/
theorem homSchur_eq_iff (D E : BetaDiagram n) : D.homSchur = E.homSchur ↔ D.schur = E.schur := by
  refine ⟨fun h => by simpa using congrArg Gluing.dehom h, fun h => ?_⟩
  exact Gluing.dehom_injOn_isHomogeneous D.homSchur_isHomogeneous E.homSchur_isHomogeneous
    (by simpa using h)

end BetaDiagram
end SkewJacobiNegative
