/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewSchurReconstruction.CompleteRing
import Vendor.AlgebraicCombinatorics.SymmetricFunctions.Definitions

/-!
# Finite-alphabet specializations of the free complete generators

Formalizes the independent generators in «Capped cofactors and admissible convex weights»
(`sec:coordinates`) of `shields-2026-skew-boundary-reconstruction.tex`.
The finite-alphabet algebraic-independence theorem is imported from the shared
AlgebraicCombinatorics library.  The family of finite alphabets separates the free ring.
Sorry-free.
-/

namespace SkewSchurReconstruction

open MvPolynomial

/-- The first `n` positive generator indices. -/
def firstGenerator (n : ℕ) (i : Fin n) : ℕ+ := ⟨i.val + 1, by omega⟩

/-- Evaluation of formal complete generators on an alphabet of size `n`. -/
noncomputable def symmetricSpecialization (n : ℕ) :
    CompleteRing →ₐ[ℤ] MvPolynomial (Fin n) ℤ :=
  aeval fun k : ℕ+ => hsymm (Fin n) ℤ (k : ℕ)

/-- The specialization restricted to the first `n` complete generators. -/
noncomputable def boundedSymmetricSpecialization (n : ℕ) :
    MvPolynomial (Fin n) ℤ →ₐ[ℤ] MvPolynomial (Fin n) ℤ :=
  aeval fun i : Fin n => hsymm (Fin n) ℤ (i.val + 1)

theorem firstGenerator_injective (n : ℕ) : Function.Injective (firstGenerator n) := by
  intro i j hij
  apply Fin.ext
  have := congrArg (fun k : ℕ+ => (k : ℕ)) hij
  dsimp [firstGenerator] at this
  omega

/-- Algebraic independence is consumed as a theorem, not as a hypothesis field. -/
theorem boundedSymmetricSpecialization_injective (n : ℕ) :
    Function.Injective (boundedSymmetricSpecialization n) := by
  exact (algebraicIndependent_iff_injective_aeval.mp
    (AlgebraicCombinatorics.SymmetricPolynomials.hsymm_algebraicIndependent
      (K := ℤ) (N := n)))

@[simp]
theorem symmetricSpecialization_rename (n : ℕ) (p : MvPolynomial (Fin n) ℤ) :
    symmetricSpecialization n (rename (firstGenerator n) p) =
      boundedSymmetricSpecialization n p := by
  simp only [symmetricSpecialization, boundedSymmetricSpecialization, aeval_rename]
  rfl

/-- A finite bound on generator indices permits faithful specialization. -/
theorem symmetricSpecialization_injective_on {n : ℕ} {p q : CompleteRing}
    (hp : (p.vars : Set ℕ+) ⊆ Set.range (firstGenerator n))
    (hq : (q.vars : Set ℕ+) ⊆ Set.range (firstGenerator n))
    (heq : symmetricSpecialization n p = symmetricSpecialization n q) : p = q := by
  obtain ⟨p', rfl⟩ := exists_rename_eq_of_vars_subset_range p _ (firstGenerator_injective n) hp
  obtain ⟨q', rfl⟩ := exists_rename_eq_of_vars_subset_range q _ (firstGenerator_injective n) hq
  rw [symmetricSpecialization_rename, symmetricSpecialization_rename] at heq
  exact congrArg (rename (firstGenerator n)) (boundedSymmetricSpecialization_injective n heq)

/-- Every free-generator polynomial involves finitely many initial generator indices. -/
theorem exists_generator_bound (p : CompleteRing) :
    ∃ n : ℕ, (p.vars : Set ℕ+) ⊆ Set.range (firstGenerator n) := by
  classical
  refine ⟨p.vars.sup (fun k : ℕ+ => (k : ℕ)), ?_⟩
  intro k hk
  have hle : (k : ℕ) ≤ p.vars.sup (fun j : ℕ+ => (j : ℕ)) := Finset.le_sup hk
  refine ⟨⟨(k : ℕ) - 1, by have := k.pos; omega⟩, ?_⟩
  apply Subtype.ext
  change (k : ℕ) - 1 + 1 = (k : ℕ)
  exact Nat.sub_add_cancel k.pos

/-- Equality in the manuscript ring is equivalent to equality on every finite alphabet. -/
theorem symmetricSpecialization_separates (p q : CompleteRing) :
    p = q ↔ ∀ n, symmetricSpecialization n p = symmetricSpecialization n q := by
  constructor
  · rintro rfl n
    rfl
  · intro h
    obtain ⟨n, hn⟩ := exists_generator_bound (p - q)
    have hz : ((0 : CompleteRing).vars : Set ℕ+) ⊆ Set.range (firstGenerator n) := by simp
    have heq : symmetricSpecialization n (p - q) = symmetricSpecialization n 0 := by
      rw [map_sub, h n, sub_self, map_zero]
    exact sub_eq_zero.mp (symmetricSpecialization_injective_on hn hz heq)

end SkewSchurReconstruction
