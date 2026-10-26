/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.OrderedBlockSign
import SkewJacobiNegative.RestorationComponents

/-!
# Actual deletion signs as retained-coordinate crossing counts

The exact sign step in `eq:boundary-lowest-degree` of
`shields-2026-skew-class-inflation.tex`.  The permutations are the
actual sorted-coordinate regroupings used by the restoration theorem.
Their signs count only crossings between retained and restored betas.
Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative SkewJacobiNegative.BetaDiagram
open SkewJacobiNegative.BetaEndpointCounts
open scoped BigOperators

/-- The actual sorted regrouping has the crossing-count sign of its retained coordinates. -/
theorem regroup_sign_count {k : ℕ} (f : Fin k → ℤ) (hf : StrictAnti f)
    (Z : Finset ℤ) (hdis : Disjoint (Finset.univ.image f) Z)
    (g : Fin (k + Z.card) → ℤ) (hg : StrictAnti g)
    (he : Finset.univ.image g = (Finset.univ.image f) ∪ Z) :
    let e : Equiv.Perm (Fin (k + Z.card)) :=
      (finSumFinEquiv : (Fin k ⊕ Fin Z.card) ≃ Fin (k + Z.card)).symm.trans
        (regroup f hf.injective Z hdis g hg.injective he)
    e.sign = ∏ j : Fin Z.card,
      (-1 : ℤˣ) ^ (Finset.univ.filter (fun i : Fin k => f i < descending Z rfl j)).card := by
  classical
  intro e
  have hleft (i : Fin k) : g (e (i.castAdd Z.card)) = f i := by
    simp only [e, Equiv.trans_apply, finSumFinEquiv_symm_apply_castAdd, regroup_apply,
      Sum.elim_inl]
  have hright (j : Fin Z.card) : g (e (j.natAdd k)) = descending Z rfl j := by
    simp only [e, Equiv.trans_apply, finSumFinEquiv_symm_apply_natAdd, regroup_apply,
      Sum.elim_inr]
  have hmonoL : StrictMono (fun i : Fin k => e (i.castAdd Z.card)) := by
    intro i j hij
    by_contra hn
    have hh := hg.antitone (le_of_not_gt hn)
    rw [hleft, hleft] at hh
    exact (not_le_of_gt (hf hij)) hh
  have hmonoR : StrictMono (fun j : Fin Z.card => e (j.natAdd k)) := by
    intro i j hij
    by_contra hn
    have hh := hg.antitone (le_of_not_gt hn)
    rw [hright, hright] at hh
    exact (not_le_of_gt (descending_strictAnti Z rfl hij)) hh
  have hcmp (i : Fin k) (j : Fin Z.card) :
      e (i.castAdd Z.card) < e (j.natAdd k) ↔ descending Z rfl j < f i := by
    constructor
    · intro hij
      have hh := hg hij
      simpa only [hleft, hright] using hh
    · intro hij
      by_contra hn
      have hh := hg.antitone (le_of_not_gt hn)
      rw [hleft, hright] at hh
      exact (not_le_of_gt hij) hh
  rw [sign_ordered_blocks e hmonoL hmonoR, Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro j _
  have hpoint (i : Fin k) :
      (if e (i.castAdd Z.card) < e (j.natAdd k) then (1 : ℤˣ) else -1) =
        if f i < descending Z rfl j then -1 else 1 := by
    have hne : f i ≠ descending Z rfl j := by
      intro hh
      have hi : f i ∈ Finset.univ.image f := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
      have hj : f i ∈ Z := hh ▸ descending_mem Z rfl j
      exact Finset.disjoint_left.mp hdis hi hj
    simp only [hcmp]
    split_ifs <;> first | rfl | omega
  simp_rw [hpoint]
  simp [Finset.prod_ite]

/-- The actual row and column regroupings have the sum of their retained crossing counts. -/
theorem deletionSign_count {k : ℕ} (C : BetaDiagram k) (Z : Finset ℤ)
    (hr : Disjoint C.rowSet Z) (hc : Disjoint C.colSet Z)
    (D : BetaDiagram (k + Z.card))
    (er : D.rowSet = C.rowSet ∪ Z) (ec : D.colSet = C.colSet ∪ Z) :
    C.deletionSign Z hr hc D er ec = ∏ j : Fin Z.card, (-1 : ℤˣ) ^
      ((Finset.univ.filter (fun i : Fin k => C.row i < descending Z rfl j)).card +
        (Finset.univ.filter (fun i : Fin k => C.col i < descending Z rfl j)).card) := by
  classical
  rw [deletionSign, regroup_sign_count C.row C.row_strictAnti Z hr D.row D.row_strictAnti er,
    regroup_sign_count C.col C.col_strictAnti Z hc D.col D.col_strictAnti ec,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  rw [pow_add]

end SkewClassInflation
