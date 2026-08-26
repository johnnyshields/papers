/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

module

public import Vendor.MathlibPR.PR39834.SchurTriangulation
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# VENDORED FROM AN UNMERGED MATHLIB PULL REQUEST

**This file is not our mathematics.**  It reproduces the two *new* files added by
an open Mathlib pull request, so that work depending on them can proceed before
the PR merges.

* **Source PR:** `feat(LinearAlgebra): unitary block-triangular Schur
  triangulation` --
  <https://github.com/leanprover-community/mathlib4/pull/39837>
* **PR author:** Matteo Cipollina (GitHub `or4nge19`), co-authored with
  `kuotsanhsu` (`learningstud@gmail.com`).
* **Context:** part 3/3 of
  <https://github.com/leanprover-community/mathlib4/pull/39139>
  (`feat(LinearAlgebra): Schur triangulation`).  Parts 1/3 and 2/3 are vendored
  in `MathlibPR/PR39834/SchurTriangulation.lean`, which this file imports.
* **Licence:** Apache 2.0, as all of Mathlib.  The copyright and `Authors:` line
  above are upstream's and are preserved deliberately.

Both upstream files are **new**, so unlike `MathlibPR/PR39834/SchurTriangulation.lean` this
one copies them whole rather than selecting declarations absent from the pin:

* `Mathlib/Analysis/InnerProductSpace/Triangularizable.lean` -- Gram-Schmidt
  preserves `Basis.flag`, giving an orthonormal triangularizing basis;
* `Mathlib/LinearAlgebra/Matrix/SchurTriangulation.lean` -- the matrix-level
  wrapper.

**When the PR merges: delete this file** and bump the Mathlib pin.

## Why this part is vendored

It was initially skipped on the ground that nothing here needs orthonormality.
That was right about orthonormality and wrong about the file's contents: the
matrix-level statement `Matrix.exists_unitaryGroup_blockTriangular` lives here,

    exists U : unitaryGroup n K, exists T, T.BlockTriangular id and A = U * T * star U,

and it performs the `Fin (finrank) -> n` reindexing that the endomorphism-level
statements of part 2/3 leave to the caller.  The unitarity is incidental; the
reindexing is the point.
-/

@[expose] public section

/-! ### From `Mathlib/Analysis/InnerProductSpace/Triangularizable.lean` -/

open Set Submodule Module
open scoped InnerProductSpace

namespace InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

private theorem gramSchmidtOrthonormalBasis_toBasis_flag_le [FiniteDimensional 𝕜 E]
    {n : ℕ} (b : Basis (Fin n) 𝕜 E) (k : Fin (n + 1)) :
    (gramSchmidtOrthonormalBasis (Module.finrank_eq_card_basis b) b).toBasis.flag k ≤
      b.flag k := by
  let u := gramSchmidtOrthonormalBasis (Module.finrank_eq_card_basis b) b
  have hu (i : Fin n) : u i = gramSchmidtNormed 𝕜 b i :=
    gramSchmidtOrthonormalBasis_apply _ ((gramSchmidtNormed_linearIndependent
      (𝕜 := 𝕜) b.linearIndependent).ne_zero i)
  rw [Basis.flag_le_iff]
  intro i hi
  change u i ∈ b.flag k
  rw [hu i, gramSchmidtNormed]
  refine Submodule.smul_mem _ _ ?_
  rw [Basis.flag]
  exact span_mono (image_mono fun j hj =>
    lt_of_le_of_lt (Fin.castSucc_le_castSucc_iff.mpr hj) hi)
    (gramSchmidt_mem_span 𝕜 b le_rfl)

private theorem flag_le_gramSchmidtOrthonormalBasis_toBasis_flag [FiniteDimensional 𝕜 E]
    {n : ℕ} (b : Basis (Fin n) 𝕜 E) (k : Fin (n + 1)) :
    b.flag k ≤
      (gramSchmidtOrthonormalBasis (Module.finrank_eq_card_basis b) b).toBasis.flag k := by
  let u := gramSchmidtOrthonormalBasis (Module.finrank_eq_card_basis b) b
  have hu (i : Fin n) : u i = gramSchmidtNormed 𝕜 b i :=
    gramSchmidtOrthonormalBasis_apply _ ((gramSchmidtNormed_linearIndependent
      (𝕜 := 𝕜) b.linearIndependent).ne_zero i)
  rw [Basis.flag_le_iff]
  intro i hi
  rw [Basis.flag]
  have hb : b i ∈ span 𝕜 (gramSchmidtNormed 𝕜 b '' Set.Iic i) := by
    rw [span_gramSchmidtNormed, span_gramSchmidt_Iic]
    exact subset_span ⟨i, by simp, rfl⟩
  refine span_mono (Set.image_subset_iff.2 ?_) hb
  intro j hj
  change gramSchmidtNormed 𝕜 b j ∈ u.toBasis '' {i | i.castSucc < k}
  rw [← hu j]
  exact ⟨j, lt_of_le_of_lt (Fin.castSucc_le_castSucc_iff.mpr hj) hi, rfl⟩

/-- `gramSchmidtOrthonormalBasis` preserves each initial `Basis.flag`. -/
theorem _root_.Module.Basis.flag_gramSchmidtOrthonormalBasis_toBasis [FiniteDimensional 𝕜 E]
    {n : ℕ} (b : Basis (Fin n) 𝕜 E) (k : Fin (n + 1)) :
    (gramSchmidtOrthonormalBasis (Module.finrank_eq_card_basis b) b).toBasis.flag k =
      b.flag k :=
  le_antisymm (gramSchmidtOrthonormalBasis_toBasis_flag_le b k)
    (flag_le_gramSchmidtOrthonormalBasis_toBasis_flag b k)

end InnerProductSpace

namespace Module.End

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {n : ℕ} {f : End 𝕜 E}

/-- An invariant `Basis.flag` admits an orthonormal basis with the same invariant flags. -/
theorem exists_orthonormalBasis_forall_flag_mem_invtSubmodule_of_forall_flag_mem_invtSubmodule
    [FiniteDimensional 𝕜 E] (b : Basis (Fin n) 𝕜 E)
    (hb : ∀ k : Fin (n + 1), b.flag k ∈ f.invtSubmodule) :
    ∃ u : OrthonormalBasis (Fin n) 𝕜 E, ∀ k : Fin (n + 1),
      u.toBasis.flag k ∈ f.invtSubmodule := by
  let u := InnerProductSpace.gramSchmidtOrthonormalBasis (Module.finrank_eq_card_basis b) b
  refine ⟨u, fun k => ?_⟩
  rw [Module.Basis.flag_gramSchmidtOrthonormalBasis_toBasis b k]
  exact hb k

/-- `f` has a block-upper-triangular matrix in some orthonormal `finrank`-indexed basis. -/
theorem exists_orthonormalBasis_blockTriangular_toMatrix_finrank
    [IsAlgClosed 𝕜] [FiniteDimensional 𝕜 E] (f : End 𝕜 E) :
    ∃ u : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E,
      (LinearMap.toMatrix u.toBasis u.toBasis f).BlockTriangular id := by
  obtain ⟨n, b, hb⟩ := exists_basis_forall_flag_mem_invtSubmodule f
  have hn : n = finrank 𝕜 E := by
    simpa [Fintype.card_fin] using (Module.finrank_eq_card_basis b).symm
  subst hn
  obtain ⟨u, hu⟩ :=
    exists_orthonormalBasis_forall_flag_mem_invtSubmodule_of_forall_flag_mem_invtSubmodule b hb
  exact ⟨u, forall_flag_mem_invtSubmodule_iff_blockTriangular_toMatrix.mp hu⟩

end Module.End

/-! ### From `Mathlib/LinearAlgebra/Matrix/SchurTriangulation.lean` -/

namespace Matrix

open Module
open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜] [IsAlgClosed 𝕜]
variable {n : Type*} [Fintype n] [LinearOrder n] (A : Matrix n n 𝕜)

theorem exists_orthonormalBasis_blockTriangular_toEuclideanLin :
    ∃ b : OrthonormalBasis n 𝕜 (EuclideanSpace 𝕜 n),
      (LinearMap.toMatrixOrthonormal b (toEuclideanLin A)).BlockTriangular id := by
  let f : Module.End 𝕜 (EuclideanSpace 𝕜 n) := toEuclideanLin A
  obtain ⟨b, hb⟩ := Module.End.exists_orthonormalBasis_blockTriangular_toMatrix_finrank f
  let e : Fin (finrank 𝕜 (EuclideanSpace 𝕜 n)) ≃o n :=
    Fintype.orderIsoFinOfCardEq n (finrank_euclideanSpace.symm)
  let e' : Fin (finrank 𝕜 (EuclideanSpace 𝕜 n)) ≃ n := e.toEquiv
  let b' := b.reindex e'
  refine ⟨b', ?_⟩
  intro i j hji
  calc LinearMap.toMatrixOrthonormal b' f i j
      = LinearMap.toMatrixOrthonormal b f (e'.symm i) (e'.symm j) := by
        change LinearMap.toMatrixOrthonormal (b.reindex e') f i j =
          LinearMap.toMatrixOrthonormal b f (e'.symm i) (e'.symm j)
        rw [LinearMap.toMatrixOrthonormal_reindex b e' f]
        rfl
    _ = 0 := hb (e.symm.lt_iff_lt.mpr hji)

/-- **Schur triangulation**: unitary similarity to a block-upper-triangular matrix. -/
theorem exists_unitaryGroup_blockTriangular :
    ∃ U : Matrix.unitaryGroup n 𝕜, ∃ T : Matrix n n 𝕜,
      T.BlockTriangular id ∧ A = U * T * star (U : Matrix n n 𝕜) := by
  obtain ⟨b, hb⟩ := exists_orthonormalBasis_blockTriangular_toEuclideanLin A
  let c := EuclideanSpace.basisFun n 𝕜
  let U : Matrix.unitaryGroup n 𝕜 :=
    ⟨c.toBasis.toMatrix b.toBasis, c.toMatrix_orthonormalBasis_mem_unitary b⟩
  let T : Matrix n n 𝕜 := LinearMap.toMatrixOrthonormal b (toEuclideanLin A)
  have hUT : (U : Matrix n n 𝕜) * T = A * U := by
    let cb := c.toBasis
    let bb := b.toBasis
    calc cb.toMatrix bb * LinearMap.toMatrix bb bb (toEuclideanLin A)
        = LinearMap.toMatrix cb cb (toEuclideanLin A) * cb.toMatrix bb := by simp
      _ = LinearMap.toMatrix cb cb (toLin cb cb A) * (U : Matrix n n 𝕜) := rfl
      _ = A * U := by simp
  refine ⟨U, T, hb, ?_⟩
  calc A
      = A * U * star (U : Matrix n n 𝕜) := by simp [mul_assoc]
    _ = U * T * star (U : Matrix n n 𝕜) := by rw [← hUT]

end Matrix
