/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.Base.CompleteRing
import Shields.Combinatorics.Young.LGVTableau
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import SkewJacobiNegative.Base.RowMultisets
import SkewJacobiNegative.Base.SymmetricSpecialization

/-!
# Tableau specialization of the free complete generators

Specializes the free complete generators of "Capped cofactors and admissible convex weights"
(`sec:coordinates`) to the tableau-defined complete functions.  The shared Jacobi--Trudi
identity supplies the determinant-to-tableau bridge. Sorry-free.
-/

namespace SkewJacobiNegative.Base

variable {R : Type*} [CommRing R]

/-- The finite-alphabet tableau specialization of the independent complete generators. -/
noncomputable def tableauSpecialization (b : ℕ) (β : ℕ → R) : CompleteRing →+* R :=
  specialize (fun k : ℕ+ => Shields.completeHom b (k : ℕ) β)

@[simp]
theorem tableauSpecialization_complete_nat (b k : ℕ) (β : ℕ → R) :
    tableauSpecialization b β (complete (k : ℤ)) = Shields.completeHom b k β := by
  cases k with
  | zero => simp [tableauSpecialization, Shields.completeHom_zero]
  | succ k =>
      let p : ℕ+ := ⟨k + 1, Nat.succ_pos k⟩
      change specialize (fun l : ℕ+ => Shields.completeHom b (l : ℕ) β)
        (complete (p : ℕ)) = Shields.completeHom b (p : ℕ) β
      exact specialize_complete _ p

theorem tableauSpecialization_complete_neg (b : ℕ) (β : ℕ → R)
    {k : ℤ} (hk : k < 0) : tableauSpecialization b β (complete k) = 0 := by
  rw [complete_of_neg hk, map_zero]

/-- Signed integer differences agree with the shared zero-below-diagonal coefficient convention. -/
theorem tableauSpecialization_complete_sub (b p q : ℕ) (β : ℕ → R) :
    tableauSpecialization b β (complete ((p : ℤ) - (q : ℤ))) =
      Shields.jtCoeff (fun k => Shields.completeHom b k β) p q := by
  by_cases h : q ≤ p
  · have hd : (p : ℤ) - (q : ℤ) = ((p - q : ℕ) : ℤ) := by omega
    rw [hd, tableauSpecialization_complete_nat, Shields.jtCoeff, ite_eq_left h]
  · have hd : (p : ℤ) - (q : ℤ) < 0 := by omega
    rw [tableauSpecialization_complete_neg b β hd, Shields.jtCoeff, ite_eq_right h]

/-- Specialization commutes with the shared Jacobi--Trudi entry constructor. -/
theorem tableauSpecialization_jtCoeff (b p q : ℕ) (β : ℕ → R) :
    tableauSpecialization b β (Shields.jtCoeff (fun k => complete (k : ℤ)) p q) =
      Shields.jtCoeff (fun k => Shields.completeHom b k β) p q := by
  unfold Shields.jtCoeff
  split_ifs <;> simp only [tableauSpecialization_complete_nat, map_zero]

/-- The free-generator determinant specializes to the actual bounded-tableau skew Schur sum. -/
theorem tableauSpecialization_jacobiTrudiDet
    (b m : ℕ) (β : ℕ → R) (lam mu : YoungDiagram)
    (hmu : mu ≤ lam) (hrow : ∀ i, m ≤ i → lam.rowLen i = 0) :
    tableauSpecialization b β
        (Shields.jacobiTrudiDet (fun k => complete (k : ℤ)) lam mu m) =
      Shields.skewSchur lam mu b β := by
  rw [Shields.jacobiTrudiDet, RingHom.map_det]
  have hmatrix : (tableauSpecialization b β).mapMatrix
      (Matrix.of fun u v : Fin m => Shields.jtCoeff (fun k => complete (k : ℤ))
        (lam.rowLen u + v) (mu.rowLen v + u)) =
      Matrix.of (fun u v : Fin m => Shields.jtCoeff
        (fun k => Shields.completeHom b k β) (lam.rowLen u + v) (mu.rowLen v + u)) := by
    ext u v
    simpa using tableauSpecialization_jtCoeff b (lam.rowLen u + v) (mu.rowLen v + u) β
  rw [hmatrix]
  exact Shields.jacobiTrudiDet_eq_skewSchur β lam mu hmu hrow

/-- The polynomial alphabet agrees with the variable indexed by every bounded letter. -/
noncomputable def finitePolynomialAlphabet (b : ℕ) (i : ℕ) :
    MvPolynomial (Fin b) ℤ :=
  if hi : i < b then MvPolynomial.X ⟨i, hi⟩ else 0

@[simp]
theorem finitePolynomialAlphabet_apply (b : ℕ) (i : Fin b) :
    finitePolynomialAlphabet b i = MvPolynomial.X i := by
  simp [finitePolynomialAlphabet, i.isLt]

/-- The tableau and multiset definitions agree on every complete function and alphabet. -/
theorem completeHom_polynomial (b k : ℕ) :
    Shields.completeHom b k (finitePolynomialAlphabet b) =
      MvPolynomial.hsymm (Fin b) ℤ k :=
  completeHom_eq_hsymm b k

/-- The shared tableau specialization is precisely the faithful finite symmetric specialization. -/
theorem tableauSpecialization_polynomial (b : ℕ) (p : CompleteRing) :
    tableauSpecialization b (finitePolynomialAlphabet b) p = symmetricSpecialization b p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [tableauSpecialization, specialize, symmetricSpecialization]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p k hp =>
      simp only [map_mul, hp]
      apply congrArg (fun q : MvPolynomial (Fin b) ℤ => symmetricSpecialization b p * q)
      simp only [tableauSpecialization, specialize, symmetricSpecialization,
        MvPolynomial.eval₂Hom_X', MvPolynomial.aeval_X]
      exact completeHom_polynomial b (k : ℕ)

end SkewJacobiNegative.Base
