/-
Copyright (c) 2026 Alexander Bentkamp, Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Matteo Cipollina, Yury Kudryashov, Patrick Massot
-/

module

public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.LinearAlgebra.Basis.Flag
public import Mathlib.LinearAlgebra.Basis.Fin
public import Mathlib.LinearAlgebra.Eigenspace.Zero
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# VENDORED FROM AN UNMERGED MATHLIB PULL REQUEST

**This file is not our mathematics.**  It reproduces the declarations added by an
open Mathlib pull request, so that work depending on them can proceed before the
PR merges.

* **Source PR:** `feat(LinearAlgebra): triangularizability via flags and
  block-triangular matrices` --
  <https://github.com/leanprover-community/mathlib4/pull/39834>
* **PR author:** Matteo Cipollina (GitHub `or4nge19`), co-authored with
  `kuotsanhsu` (`learningstud@gmail.com`).
* **Context:** part 2/3 of
  <https://github.com/leanprover-community/mathlib4/pull/39139>
  (`feat(LinearAlgebra): Schur triangulation`), and it subsumes part 1/3,
  <https://github.com/leanprover-community/mathlib4/pull/39829>
  (`feat(LinearAlgebra): basis flag lemmas and genEigenspace map`), whose
  additions to `Eigenspace/Basic.lean` and `Basis/Flag.lean` appear below.
  Part 3/3, <https://github.com/leanprover-community/mathlib4/pull/39837>, adds
  the *unitary* Gram-Schmidt refinement and is deliberately **not** vendored:
  nothing here needs orthonormality.
* **Licence:** Apache 2.0, as all of Mathlib.  The copyright and `Authors:` line
  above are upstream's and are preserved deliberately.

Upstream modifies three existing Mathlib files.  We cannot, so their new
declarations are collected here -- **only those absent from the pinned
Mathlib** -- carrying upstream's own section and `variable` scaffolding, in
upstream's namespaces (`Module.Basis`, `Module.End`) and under upstream's names.
Consuming code is therefore written exactly as it will be against a merged
Mathlib.

**When the PR merges: delete this file** and bump the Mathlib pin.  Nothing else
changes.  If the pin is bumped first, Lean reports duplicate declarations, which
is the intended failure mode -- it forces the deletion instead of letting a stale
copy shadow upstream.

## What it provides

`Module.End.exists_blockTriangular_toMatrix_iff_iSup_maxGenEigenspace_eq_top`,
which with the pinned `Module.End.iSup_maxGenEigenspace_eq_top` gives: over an
algebraically closed field, every endomorphism of a finite-dimensional space has
a basis in which its matrix is `Matrix.BlockTriangular id`.
-/

@[expose] public section

/-! ### From `Mathlib/LinearAlgebra/Basis/Flag.lean` -/

open Set Submodule

namespace Module.Basis

section Semiring

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] {n : ℕ} {b : Basis (Fin n) R M}
  {i j : Fin (n + 1)}



theorem flag_map {M₂ : Type*} [AddCommMonoid M₂] [Module R M₂]
    (b : Basis (Fin n) R M) (e : M ≃ₗ[R] M₂) (k : Fin (n + 1)) :
    (b.map e).flag k = (b.flag k).map (e : M →ₗ[R] M₂) := by
  -- ADAPTED to the pinned Mathlib: upstream's `simp` set leaves
  -- `span R (⇑(b.map e) '' S) = span R ((fun i => e (b i)) '' S)`, closed here by
  -- rewriting the coercion of `Basis.map` pointwise.
  simp only [flag, Submodule.map_span, Set.image_image]
  congr 1


end Semiring

section Ring

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] {n : ℕ}

/-- The span of the new head vector lies in the successor flag of `Basis.mkFinCons`. -/
theorem span_singleton_le_mkFinCons_flag_succ {v : M} {W : Submodule R M}
    {bW : Basis (Fin n) R W} {hli hsp} (k : Fin (n + 1)) :
    R ∙ v ≤ (Basis.mkFinCons v bW hli hsp).flag k.succ := by
  rw [Submodule.span_singleton_le_iff_mem]
  convert (Basis.mkFinCons v bW hli hsp).self_mem_flag (i := 0) (k := k.succ) ?_
  · simp [coe_mkFinCons, Fin.cons_zero]
  · simp

theorem map_flag_le_mkFinCons_flag_succ {v : M} {W : Submodule R M}
    {bW : Basis (Fin n) R W} {hli hsp} (k : Fin (n + 1)) :
    (bW.flag k).map W.subtype ≤ (Basis.mkFinCons v bW hli hsp).flag k.succ := by
  rw [Submodule.map_le_iff_le_comap]
  exact bW.flag_le_iff.2 fun i hi => by
    convert (Basis.mkFinCons v bW hli hsp).self_mem_flag (i := i.succ) (k := k.succ)
      (Fin.succ_lt_succ_iff.mpr hi) using 1
    · simp [coe_mkFinCons, Fin.cons_succ]

end Ring

section CommRing

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}

/-- `x ∈ b.flag k` iff `b.repr x i = 0` for `k ≤ i.castSucc`. -/
theorem mem_flag_iff_repr_eq_zero [Nontrivial R] (b : Basis (Fin n) R M) {k : Fin (n + 1)} {x : M} :
    x ∈ b.flag k ↔ ∀ i : Fin n, k ≤ i.castSucc → b.repr x i = 0 := by
  constructor
  · intro hx i hi
    have hmem : x ∈ LinearMap.ker (b.coord i) := b.flag_le_ker_coord hi hx
    simpa [Module.Basis.coord_apply] using (LinearMap.mem_ker.mp hmem)
  · intro h
    rw [← b.sum_repr x]
    exact Submodule.sum_mem _ fun i _ => by
      by_cases hi : i.castSucc < k
      · exact Submodule.smul_mem _ _ (b.self_mem_flag hi)
      · rw [h i (le_of_not_gt hi), zero_smul]
        exact Submodule.zero_mem _

end CommRing

section DivisionRing

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] {n : ℕ}




end DivisionRing

end Module.Basis

/-! ### From `Mathlib/LinearAlgebra/Eigenspace/Basic.lean` -/

namespace Module

namespace End

open Module Set

variable {K R : Type*} {V M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Field K]
  [AddCommGroup V] [Module K V]




lemma map_genEigenspace_le {N : Type*} [AddCommGroup N] [Module R N]
    {f : End R M} {g : End R N} (φ : M →ₗ[R] N) (hφ : g.comp φ = φ.comp f)
    (μ : R) (k : ℕ∞) :
    (f.genEigenspace μ k).map φ ≤ g.genEigenspace μ k := by
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨l, hl, hx⟩ := (mem_genEigenspace (f := f) (μ := μ) (k := k)).mp hx
  apply (mem_genEigenspace (f := g) (μ := μ) (k := k)).mpr
  refine ⟨l, hl, ?_⟩
  rw [LinearMap.mem_ker] at hx ⊢
  have hsub (x : M) : (g - μ • 1) (φ x) = φ ((f - μ • 1) x) := by
    have hfg : g (φ x) = φ (f x) := LinearMap.congr_fun hφ x
    simp [LinearMap.sub_apply, hfg]
  have hpow (l : ℕ) (x : M) :
      ((g - μ • 1) ^ l) (φ x) = φ (((f - μ • 1) ^ l) x) := by
    induction l with
    | zero => simp
    | succ l ih =>
        rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih, hsub]
  rw [hpow, hx, map_zero]

/-- `map_genEigenspace_le` as `MapsTo`. -/
lemma mapsTo_genEigenspace_of_comp {N : Type*} [AddCommGroup N] [Module R N]
    {f : End R M} {g : End R N} (φ : M →ₗ[R] N) (hφ : g.comp φ = φ.comp f) (μ : R) (k : ℕ∞) :
    MapsTo φ (f.genEigenspace μ k) (g.genEigenspace μ k) := by
  intro x hx
  exact mem_of_le_of_mem (map_genEigenspace_le (φ := φ) hφ μ k) (Submodule.mem_map_of_mem hx)

















































end End

end Module

/-! ### From `Mathlib/LinearAlgebra/Eigenspace/Triangularizable.lean` -/

open Set Function Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

namespace Module.End

variable {n : ℕ} {f : End K V} {b : Basis (Fin n) K V}

theorem forall_flag_mem_invtSubmodule_iff_forall_mem_toFlag :
    (∀ k : Fin (n + 1), b.flag k ∈ f.invtSubmodule) ↔
      ∀ ⦃p : Submodule K V⦄, p ∈ b.toFlag → p ∈ f.invtSubmodule := by
  constructor
  · intro hf p hp
    rw [Basis.mem_toFlag] at hp
    obtain ⟨k, rfl⟩ := hp
    exact hf k
  · intro hf k
    exact hf (Basis.mem_toFlag b |>.2 ⟨k, rfl⟩)

/-- A triangularizing basis gives an invariant complete flag. -/
theorem exists_invariantFlag_of_forall_flag_mem_invtSubmodule
    (hb : ∀ k : Fin (n + 1), b.flag k ∈ f.invtSubmodule) :
    ∃ c : Flag (Submodule K V), ∀ ⦃p : Submodule K V⦄, p ∈ c → p ∈ f.invtSubmodule :=
  ⟨b.toFlag, forall_flag_mem_invtSubmodule_iff_forall_mem_toFlag.mp hb⟩

private theorem forall_flag_mem_invtSubmodule_map {V₂ : Type*} [AddCommGroup V₂] [Module K V₂]
    (hb : ∀ k : Fin (n + 1), b.flag k ∈ f.invtSubmodule) (e : V ≃ₗ[K] V₂) :
    ∀ k : Fin (n + 1), (b.map e).flag k ∈ (e.conj f).invtSubmodule := by
  intro k
  rw [Module.Basis.flag_map]
  exact LinearEquiv.map_mem_invtSubmodule_conj_iff.mpr (hb k)

theorem forall_flag_mem_invtSubmodule_iff_blockTriangular_toMatrix :
    (∀ k : Fin (n + 1), b.flag k ∈ f.invtSubmodule) ↔
      (LinearMap.toMatrix b b f).BlockTriangular id := by
  constructor
  · intro hf i j hji
    rw [LinearMap.toMatrix_apply]
    have hmem : f (b j) ∈ LinearMap.ker (b.coord i) := by
      apply b.flag_le_ker_coord
      · exact Fin.castSucc_lt_iff_succ_le.mp (show j.castSucc < i.castSucc from hji)
      · exact (hf j.succ : b.flag j.succ ≤ (b.flag j.succ).comap f)
          (b.self_mem_flag (Fin.castSucc_lt_succ_iff.mpr le_rfl))
    simpa [Module.Basis.coord_apply] using LinearMap.mem_ker.mp hmem
  · intro hf k
    rw [Module.End.mem_invtSubmodule]
    exact b.flag_le_iff.2 fun i hik => by
      change f (b i) ∈ b.flag k
      rw [b.mem_flag_iff_repr_eq_zero]
      intro l hlk
      rw [← LinearMap.toMatrix_apply b b f l i]
      exact hf (Fin.castSucc_lt_castSucc_iff.mp (lt_of_lt_of_le hik hlk))

private theorem charpoly_splits_of_forall_flag_mem_invtSubmodule [FiniteDimensional K V]
    (hb : ∀ k : Fin (n + 1), b.flag k ∈ f.invtSubmodule) :
    f.charpoly.Splits := by
  rw [← LinearMap.charpoly_toMatrix (f := f) b]
  rw [Matrix.charpoly_of_upperTriangular _
    (forall_flag_mem_invtSubmodule_iff_blockTriangular_toMatrix.mp hb)]
  exact Polynomial.Splits.prod fun i _ => by
    simpa [sub_eq_add_neg] using Polynomial.Splits.X_add_C (-(LinearMap.toMatrix b b f i i))

/-- If the generalized eigenspaces of `f` span the whole space, then the same holds for the map
induced by `f` on a quotient by an invariant submodule. -/
theorem iSup_genEigenspace_mapQ_eq_top {p : Submodule K V} {f : End K V}
    (hfp : p ≤ p.comap f) {k : ℕ∞} (hf : ⨆ μ, f.genEigenspace μ k = ⊤) :
    ⨆ μ, Module.End.genEigenspace (p.mapQ p f hfp : End K (V ⧸ p)) μ k = ⊤ := by
  rw [← top_le_iff]
  calc
    ⊤ = (⊤ : Submodule K V).map p.mkQ := by
      rw [Submodule.map_top]
      exact (LinearMap.range_eq_top.mpr p.mkQ_surjective).symm
    _ = (⨆ μ, f.genEigenspace μ k).map p.mkQ := by rw [hf]
    _ = ⨆ μ, (f.genEigenspace μ k).map p.mkQ := by rw [Submodule.map_iSup]
    _ ≤ ⨆ μ, Module.End.genEigenspace (p.mapQ p f hfp : End K (V ⧸ p)) μ k :=
      iSup_mono fun μ =>
        Module.End.map_genEigenspace_le p.mkQ (Submodule.mapQ_mkQ p p f (h := hfp)) μ k

/-- Maximal-generalized-eigenspace version -/
theorem iSup_maxGenEigenspace_mapQ_eq_top {p : Submodule K V} {f : End K V}
    (hfp : p ≤ p.comap f) (hf : ⨆ μ, f.maxGenEigenspace μ = ⊤) :
    ⨆ μ, Module.End.maxGenEigenspace (p.mapQ p f hfp : End K (V ⧸ p)) μ = ⊤ :=
  iSup_genEigenspace_mapQ_eq_top hfp hf

private theorem forall_flag_mem_invtSubmodule_mkFinCons_of_sub_mem_span_singleton
    {n : ℕ} {f : End K V}
    {v : V} {μ : K} {W : Submodule K V} {g : End K W} {bW : Basis (Fin n) K W}
    {hli hsp} (hg : ∀ k : Fin (n + 1), bW.flag k ∈ g.invtSubmodule)
    (hv : f v = μ • v)
    (hfg : ∀ w : W, f (w : V) - (g w : V) ∈ K ∙ v) :
    ∀ k : Fin (n + 2), (Basis.mkFinCons v bW hli hsp).flag k ∈ f.invtSubmodule := by
  intro k
  refine Fin.cases (by simp) (fun k => ?_) k
  rw [Module.End.mem_invtSubmodule]
  exact (Basis.mkFinCons v bW hli hsp).flag_le_iff.2 fun i hi => by
    change f (Basis.mkFinCons v bW hli hsp i) ∈ (Basis.mkFinCons v bW hli hsp).flag k.succ
    revert hi
    refine Fin.cases (fun _ => ?_) ?_ i
    · rw [show Basis.mkFinCons v bW hli hsp 0 = v by simp, hv]
      exact Submodule.smul_mem _ _ <|
        Basis.span_singleton_le_mkFinCons_flag_succ k (Submodule.mem_span_singleton_self v)
    intro i hi
    rw [show Basis.mkFinCons v bW hli hsp i.succ = (bW i : V) by simp]
    have hgw := (hg k : bW.flag k ≤ (bW.flag k).comap g)
      (bW.self_mem_flag (Fin.succ_lt_succ_iff.mp hi))
    have hdecomp : f (bW i : V) = (f (bW i : V) - (g (bW i) : V)) + (g (bW i) : V) := by
      abel
    rw [hdecomp]
    exact Submodule.add_mem _ (Basis.span_singleton_le_mkFinCons_flag_succ k (hfg (bW i)))
      (Basis.map_flag_le_mkFinCons_flag_succ k ⟨_, hgw, rfl⟩)


private lemma exists_hasEigenvalue_of_iSup_maxGenEigenspace_eq_top [Nontrivial M] {f : End R M}
    (hf : ⨆ μ, f.maxGenEigenspace μ = ⊤) :
    ∃ μ, f.HasEigenvalue μ :=
  exists_hasEigenvalue_of_genEigenspace_eq_top ⊤ hf

-- This is Lemma 5.21 of [axler2024], although we are no longer following that proof.
/-- In finite dimensions, over an algebraically closed field, every linear endomorphism has an
eigenvalue. -/

private theorem exists_basis_forall_flag_mem_invtSubmodule_of_subsingleton [Subsingleton V]
    (f : End K V) :
    ∃ n, ∃ b : Basis (Fin n) K V, ∀ k : Fin (n + 1), b.flag k ∈ f.invtSubmodule := by
  refine ⟨0, (Module.Basis.empty V : Basis (Fin 0) K V), ?_⟩
  intro k
  change (Module.Basis.empty V : Basis (Fin 0) K V).flag k ≤
    ((Module.Basis.empty V : Basis (Fin 0) K V).flag k).comap f
  intro x hx
  change f x ∈ (Module.Basis.empty V : Basis (Fin 0) K V).flag k
  convert hx using 1

private theorem mkFinCons_linearIndependent_of_isCompl {N : Submodule K V} {y : V}
    (hy : y ≠ 0) (hN : IsCompl (K ∙ y) N) :
    ∀ (c : K), ∀ x ∈ N, c • y + x = 0 → c = 0 := by
  intro c x hx hcx
  have hcy_eq : c • y = -x := add_eq_zero_iff_eq_neg.mp hcx
  have hcyN : c • y ∈ N := by
    rw [hcy_eq]
    exact N.neg_mem hx
  have hcyL : c • y ∈ K ∙ y :=
    Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self y)
  have hcy0 : c • y = 0 := hN.disjoint.le_bot ⟨hcyL, hcyN⟩
  by_contra hc
  exact hy <| by simpa [hcy0] using (inv_smul_smul₀ hc y).symm

private theorem mkFinCons_span_of_isCompl {N : Submodule K V} {y : V}
    (hN : IsCompl (K ∙ y) N) :
    ∀ z : V, ∃ c : K, z + c • y ∈ N := by
  intro z
  have hz : z ∈ K ∙ y ⊔ N := by
    rw [hN.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨_, hu, w, hw, huz⟩ := Submodule.mem_sup.mp hz
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hu
  refine ⟨-a, ?_⟩
  rw [← huz]
  simpa [add_assoc, add_comm, add_left_comm] using hw

/-- If the maximal generalized eigenspaces of a finite-dimensional endomorphism span the whole
space, then there is a basis whose associated flag is invariant. -/
theorem exists_basis_forall_flag_mem_invtSubmodule_of_iSup_maxGenEigenspace_eq_top {V : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {f : End K V}
    (hf : ⨆ μ, f.maxGenEigenspace μ = ⊤) :
    ∃ n, ∃ b : Basis (Fin n) K V, ∀ k : Fin (n + 1), b.flag k ∈ f.invtSubmodule := by
  by_cases hV : Nontrivial V
  · obtain ⟨μ, hμ⟩ := exists_hasEigenvalue_of_iSup_maxGenEigenspace_eq_top hf
    obtain ⟨v, hv⟩ := Module.End.HasEigenvalue.exists_hasEigenvector hμ
    let L : Submodule K V := K ∙ v
    have hL : L ≤ L.comap f := by
      rw [Submodule.span_singleton_le_iff_mem]
      change f v ∈ L
      rw [hv.apply_eq_smul]
      exact Submodule.smul_mem L μ (Submodule.mem_span_singleton_self v)
    let qf : End K (V ⧸ L) := L.mapQ L f hL
    have hqf : ⨆ μ, qf.maxGenEigenspace μ = ⊤ :=
      iSup_maxGenEigenspace_mapQ_eq_top hL hf
    obtain ⟨n, bq, hbq⟩ :=
      exists_basis_forall_flag_mem_invtSubmodule_of_iSup_maxGenEigenspace_eq_top (f := qf) hqf
    obtain ⟨W, hW⟩ := L.exists_isCompl
    let e : (V ⧸ L) ≃ₗ[K] W := Submodule.quotientEquivOfIsCompl L W hW
    let g : End K W := e.conj qf
    let hli := mkFinCons_linearIndependent_of_isCompl hv.2 hW
    let hsp := mkFinCons_span_of_isCompl (y := v) hW
    refine ⟨n + 1, Basis.mkFinCons v (bq.map e) hli hsp, ?_⟩
    exact forall_flag_mem_invtSubmodule_mkFinCons_of_sub_mem_span_singleton
      (forall_flag_mem_invtSubmodule_map hbq e)
      hv.apply_eq_smul
      (by
        intro w
        have hq : L.mkQ (f (w : V)) = L.mkQ (g w : V) := by
          calc
            L.mkQ (f (w : V)) = qf (L.mkQ (w : V)) := by
              rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.mapQ_apply]
            _ = qf (e.symm w) := by simp [e, Submodule.mkQ_apply]
            _ = e.symm (g w) := by simp [g]
            _ = L.mkQ (g w : V) := by simp [e, Submodule.mkQ_apply]
        change f (w : V) - (g w : V) ∈ L
        rw [← Submodule.ker_mkQ L]
        exact LinearMap.mem_ker.mpr (by
          simpa using congr_arg (fun x => x - L.mkQ (g w : V)) hq))
  · haveI : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
    exact exists_basis_forall_flag_mem_invtSubmodule_of_subsingleton f
termination_by Module.finrank K V
decreasing_by
  have hdim := Submodule.finrank_quotient_add_finrank L
  rw [finrank_span_singleton hv.2] at hdim
  rw [← hdim]
  exact Nat.lt_add_of_pos_right Nat.zero_lt_one

/-- If the maximal generalized eigenspaces of a finite-dimensional endomorphism span the whole
space, then the endomorphism has an upper triangular matrix in some basis. -/
theorem exists_blockTriangular_toMatrix_of_iSup_maxGenEigenspace_eq_top [FiniteDimensional K V]
    {f : End K V} (hf : ⨆ μ, f.maxGenEigenspace μ = ⊤) :
    ∃ n, ∃ b : Basis (Fin n) K V, (LinearMap.toMatrix b b f).BlockTriangular id := by
  obtain ⟨n, b, hb⟩ := exists_basis_forall_flag_mem_invtSubmodule_of_iSup_maxGenEigenspace_eq_top hf
  exact ⟨n, b, forall_flag_mem_invtSubmodule_iff_blockTriangular_toMatrix.mp hb⟩

private lemma finrank_finset_sup_maxGenEigenspace [FiniteDimensional K V]
    (f : End K V) (s : Finset K) :
    finrank K (s.sup (fun μ => f.maxGenEigenspace μ) : Submodule K V) =
      ∑ μ ∈ s, finrank K (f.maxGenEigenspace μ) := by
  classical
  have hind := Module.End.independent_maxGenEigenspace f
  induction s using Finset.induction_on with
  | empty => simp
  | insert μ s hμ ih =>
      have hdisj : Disjoint (f.maxGenEigenspace μ)
          (s.sup (fun μ => f.maxGenEigenspace μ) : Submodule K V) := by
        have hs := hind.supIndep' (insert μ s)
        simpa [hμ] using
          (Finset.supIndep_iff_disjoint_erase.mp hs μ (Finset.mem_insert_self μ s))
      have hfin := Submodule.finrank_sup_add_finrank_inf_eq (f.maxGenEigenspace μ)
        (s.sup (fun μ => f.maxGenEigenspace μ) : Submodule K V)
      rw [hdisj.eq_bot, finrank_bot, add_zero] at hfin
      rw [Finset.sup_insert, Finset.sum_insert hμ, hfin, ih]

/-- If the characteristic polynomial of a finite-dimensional endomorphism splits, then its maximal
generalized eigenspaces span the whole space. -/
theorem iSup_maxGenEigenspace_eq_top_of_charpoly_splits [FiniteDimensional K V]
    {f : End K V} (hf : f.charpoly.Splits) :
    ⨆ μ, f.maxGenEigenspace μ = ⊤ := by
  classical -- needed
  let s := f.charpoly.roots.toFinset
  have hs : (s.sup (fun μ => f.maxGenEigenspace μ) : Submodule K V) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    calc
      finrank K (s.sup (fun μ => f.maxGenEigenspace μ) : Submodule K V)
          = ∑ μ ∈ s, finrank K (f.maxGenEigenspace μ) :=
            finrank_finset_sup_maxGenEigenspace f s
      _ = ∑ μ ∈ s, f.charpoly.rootMultiplicity μ := by
            refine Finset.sum_congr rfl fun μ _ => ?_
            exact LinearMap.finrank_maxGenEigenspace_eq f μ
      _ = ∑ μ ∈ s, f.charpoly.roots.count μ := by
            refine Finset.sum_congr rfl fun μ _ => ?_
            rw [Polynomial.count_roots]
      _ = f.charpoly.roots.card := by
            exact Multiset.sum_count_eq_card (by simp [s])
      _ = f.charpoly.natDegree := hf.natDegree_eq_card_roots.symm
      _ = finrank K V := LinearMap.charpoly_natDegree f
  rw [← top_le_iff, ← hs]
  exact Finset.sup_le fun μ _ => le_iSup f.maxGenEigenspace μ

theorem iSup_maxGenEigenspace_eq_top_of_forall_flag_mem_invtSubmodule [FiniteDimensional K V]
    (hb : ∀ k : Fin (n + 1), b.flag k ∈ f.invtSubmodule) :
    ⨆ μ, f.maxGenEigenspace μ = ⊤ :=
  iSup_maxGenEigenspace_eq_top_of_charpoly_splits
    (charpoly_splits_of_forall_flag_mem_invtSubmodule hb)

theorem exists_basis_forall_flag_mem_invtSubmodule_iff_iSup_maxGenEigenspace_eq_top
    [FiniteDimensional K V]
    (f : End K V) :
    (∃ n, ∃ b : Basis (Fin n) K V, ∀ k : Fin (n + 1), b.flag k ∈ f.invtSubmodule) ↔
      ⨆ μ, f.maxGenEigenspace μ = ⊤ :=
  ⟨fun ⟨_, _, hb⟩ => iSup_maxGenEigenspace_eq_top_of_forall_flag_mem_invtSubmodule hb,
    exists_basis_forall_flag_mem_invtSubmodule_of_iSup_maxGenEigenspace_eq_top⟩

/-- In finite dimensions, existence of a basis in which the matrix of `f` is upper triangular is
equivalent to spanning by maximal generalized eigenspaces. -/
theorem exists_blockTriangular_toMatrix_iff_iSup_maxGenEigenspace_eq_top [FiniteDimensional K V]
    (f : End K V) :
    (∃ n, ∃ b : Basis (Fin n) K V, (LinearMap.toMatrix b b f).BlockTriangular id) ↔
      ⨆ μ, f.maxGenEigenspace μ = ⊤ := by
  rw [← exists_basis_forall_flag_mem_invtSubmodule_iff_iSup_maxGenEigenspace_eq_top f]
  constructor
  · rintro ⟨n, b, hb⟩
    exact ⟨n, b, forall_flag_mem_invtSubmodule_iff_blockTriangular_toMatrix.mpr hb⟩
  · rintro ⟨n, b, hb⟩
    exact ⟨n, b, forall_flag_mem_invtSubmodule_iff_blockTriangular_toMatrix.mp hb⟩

section finiteDimensional

variable [FiniteDimensional K V]

/-- If the maximal generalized eigenspaces of a finite-dimensional endomorphism span the whole
space, then the endomorphism admits an invariant complete flag. -/
theorem exists_invariantFlag_of_iSup_maxGenEigenspace_eq_top
    {f : End K V} (hf : ⨆ μ, f.maxGenEigenspace μ = ⊤) :
    ∃ c : Flag (Submodule K V), ∀ ⦃p : Submodule K V⦄, p ∈ c → p ∈ f.invtSubmodule := by
  obtain ⟨_, b, hb⟩ := exists_basis_forall_flag_mem_invtSubmodule_of_iSup_maxGenEigenspace_eq_top hf
  exact exists_invariantFlag_of_forall_flag_mem_invtSubmodule (b := b) hb

end finiteDimensional

/-- In finite dimensions, over an algebraically closed field, the generalized eigenspaces of any
linear endomorphism span the whole space. -/
theorem exists_basis_forall_flag_mem_invtSubmodule [IsAlgClosed K] [FiniteDimensional K V]
    (f : End K V) :
    ∃ n, ∃ b : Basis (Fin n) K V, ∀ k : Fin (n + 1), b.flag k ∈ f.invtSubmodule :=
  exists_basis_forall_flag_mem_invtSubmodule_of_iSup_maxGenEigenspace_eq_top
    (iSup_maxGenEigenspace_eq_top f)

/-- In finite dimensions over an algebraically closed field, every endomorphism admits an invariant
complete flag. -/
theorem exists_invariantFlag [IsAlgClosed K] [FiniteDimensional K V] (f : End K V) :
    ∃ c : Flag (Submodule K V), ∀ ⦃p : Submodule K V⦄, p ∈ c → p ∈ f.invtSubmodule :=
  exists_invariantFlag_of_iSup_maxGenEigenspace_eq_top (iSup_maxGenEigenspace_eq_top f)

end Module.End

namespace Submodule

variable {p : Submodule K V} {f : Module.End K V}
