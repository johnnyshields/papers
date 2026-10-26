/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
-- TODO-COPIED: skew-gluing/lean/SkewGluing/OlsonHarris/Plan/MurnaghanNakayama/Ferrers.lean
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.MurnaghanNakayama.RightMul

/-!
# Multiplication by a power sum on a Schur function of a Ferrers shape

Formalizes `shields-2026-skew-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `def:gluing-graph`): thesis §5.1.3 (`OlsonHarris2024HopfApplications`), Thm. 5.1.13
for one power sum.

`pPoly_mul_cellSchur_ferrers_eq`: `p_m s_μ = Σ_λ (-1)^{ht(λ/μ)} s_λ`.  An element of `Λ` is
determined by its evaluations in `N` variables for all large `N`
(`eq_of_evalComplete_eq_of_ge`); in `N` variables the identity is the determinantal identity of
`Shift` together with the sorting of `RightMul`.

Sorry-free.
-/

namespace SkewMarkedFactor.Gluing

namespace Plan

namespace MN

open MvPolynomial

open AlgebraicCombinatorics.SymmetricPolynomials in
/-- Elements of `Λ` are determined by their evaluations at `N` variables for all `N ≥ N₀`. -/
theorem eq_of_evalComplete_eq_of_ge {f g : Lambda} (N0 : ℕ)
    (h : ∀ a, N0 ≤ a → evalComplete a (varAlphabet a) f = evalComplete a (varAlphabet a) g) :
    f = g := by
  rw [← sub_eq_zero]
  set d : Lambda := f - g with hd
  set N : ℕ := max (d.vars.sup fun k : ℕ+ => (k : ℕ)) N0 with hN
  have hd0 : evalComplete N (varAlphabet N) d = 0 := by
    rw [hd, map_sub, h N (le_max_right _ _), sub_self]
  let φ : Fin N → ℕ+ := fun j => ⟨j + 1, Nat.succ_pos _⟩
  have hφ : Function.Injective φ := by
    intro i j hij
    exact Fin.ext (by simpa [φ] using congrArg PNat.val hij)
  have hsub : ↑d.vars ⊆ Set.range φ := by
    intro k hk
    have hkN : (k : ℕ) ≤ N :=
      (Finset.le_sup (f := fun k : ℕ+ => (k : ℕ)) (Finset.mem_coe.mp hk)).trans
        (le_max_left _ _)
    exact ⟨⟨k - 1, by have := k.pos; omega⟩, PNat.eq (by simp [φ]; have := k.pos; omega)⟩
  obtain ⟨q, hq⟩ := exists_rename_eq_of_vars_subset_range d φ hφ hsub
  rw [← hq, evalComplete, aeval_rename] at hd0
  have hind := hsymm_algebraicIndependent (K := ℚ) (N := N)
  rw [algebraicIndependent_iff_injective_aeval] at hind
  have : q = 0 := by
    apply hind
    rw [map_zero, ← hd0]
    have hfun : (fun j : Fin N => hsymm (Fin N) ℚ (j + 1))
        = (fun k : ℕ+ => Shields.completeHom N (k : ℕ) (varAlphabet N)) ∘ φ := by
      funext j
      exact (completeHom_varAlphabet N (j + 1)).symm
    rw [hfun]
  rw [← hq, this, map_zero]

open scoped Classical in
/-- **Murnaghan–Nakayama rule I for one power sum, on Ferrers shapes.**
`p_m · s_μ = Σ_λ (-1)^{ht(λ/μ)} s_λ`, the sum over the partitions `λ ⊇ μ` such that `λ / μ` is a
ribbon with `m` cells. -/
theorem pPoly_mul_cellSchur_ferrers_eq (mu : YoungDiagram) {m : ℕ} (hm : 0 < m) :
    pPoly m * cellSchur (skewDiagram mu ⊥) =
      ∑ᶠ lam : YoungDiagram,
        if mu ≤ lam ∧ IsRibbon (skewDiagram lam mu) ∧ (skewDiagram lam mu).card = m then
          (ribbonSign (skewDiagram lam mu) : Lambda) * cellSchur (skewDiagram lam ⊥)
        else 0 := by
  set T : Finset YoungDiagram := (ribbonAdditions_finite mu hm).toFinset with hTdef
  have hT : ∀ lam, lam ∈ T ↔ lam ∈ ribbonAdditions mu m := fun lam => by
    simp [hTdef]
  rw [finsum_eq_sum_of_support_subset (s := T)]
  swap
  · intro lam hlam
    rw [Function.mem_support] at hlam
    rw [Finset.mem_coe, hT]
    by_contra hcon
    exact hlam (ite_eq_right_iff.mpr fun h => absurd h hcon)
  have hsum : ∀ lam ∈ T, (if mu ≤ lam ∧ IsRibbon (skewDiagram lam mu) ∧
      (skewDiagram lam mu).card = m then
        (ribbonSign (skewDiagram lam mu) : Lambda) * cellSchur (skewDiagram lam ⊥) else 0) =
      (ribbonSign (skewDiagram lam mu) : Lambda) * cellSchur (skewDiagram lam ⊥) := by
    intro lam hlam
    have h' : mu ≤ lam ∧ IsRibbon (skewDiagram lam mu) ∧ (skewDiagram lam mu).card = m :=
      (hT lam).mp hlam
    exact ite_eq_left_iff.mpr fun h => absurd h' h
  rw [Finset.sum_congr rfl hsum]
  refine eq_of_evalComplete_eq_of_ge (mu.colLen 0 + m) fun N hN => ?_
  -- rows
  have hbot : ∀ lam : YoungDiagram, (∀ i, N ≤ i → lam.rowLen i = 0) →
      cellSchur (skewDiagram lam ⊥) =
        jtDet (fun i : Fin N => (lam.rowLen i : ℤ) - i) (fun j : Fin N => -(j : ℤ)) := by
    intro lam hlam
    rw [cellSchur_skewDiagram_eq_jtDet bot_le hlam]
    congr 1
    funext j
    have : (⊥ : YoungDiagram).rowLen j = 0 := by
      by_contra h0
      have : ((j : ℕ), 0) ∈ (⊥ : YoungDiagram) :=
        YoungDiagram.mem_iff_lt_rowLen.mpr (Nat.pos_of_ne_zero h0)
      exact YoungDiagram.notMem_bot _ this
    simp [this]
  have hrows : ∀ lam ∈ T, ∀ i, N ≤ i → lam.rowLen i = 0 := by
    intro lam hlam i hi
    obtain ⟨hl, hrib, hcard⟩ := (hT lam).mp hlam
    obtain ⟨j, i1, hRM⟩ := RowMove.of_isRibbon hl hrib
    rw [hcard] at hRM
    have hj := hRM.j_lt hm
    have h2 := hRM.outside i (Or.inr (by omega))
    have h3 : mu.rowLen i = 0 := rowLen_eq_zero_of_colLen_le mu i (by omega)
    omega
  have hmu0 : ∀ i, N ≤ i → mu.rowLen i = 0 := fun i hi =>
    rowLen_eq_zero_of_colLen_le mu i (by omega)
  rw [map_mul, evalComplete_pPoly N m hm, hbot mu hmu0, evalComplete_jtDet]
  rw [psum_mul_det_eq_sum N _ (fun i => by have := i.isLt; omega) m]
  rw [map_sum]
  have h1 := sum_update_rows_eq hm hN T hT
  have h2 : ∑ k : Fin N, (hMat N (Function.update (fun i : Fin N => (mu.rowLen i : ℤ) - i) k
      ((mu.rowLen k : ℤ) - k + m))).det =
      evalComplete N (varAlphabet N) (∑ k : Fin N, jtDet (Function.update
        (fun i : Fin N => (mu.rowLen i : ℤ) - i) k ((mu.rowLen k : ℤ) - k + m))
          (fun j : Fin N => -(j : ℤ))) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => (evalComplete_jtDet N _).symm
  rw [h2, h1, map_sum]
  refine Finset.sum_congr rfl fun lam hlam => ?_
  rw [map_mul, hbot lam (hrows lam hlam)]
  simp

end MN

end Plan

end SkewMarkedFactor.Gluing
