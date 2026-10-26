/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.ThinReadings
import SkewClassInflation.ComponentInventories
import SkewClassInflation.UnitJoinCoefficients

/-!
# Exact arbitrary-mate thin component recovery

Formalizes the cut-product recovery in `thm:two-row-thin-class` of
`shields-2026-skew-class-inflation.tex`.  The source product is computed
from the actual ordered zero-join construction.  Unique factorization
matches each genuine unknown cut component with a source thin power,
retaining all multiplicities and row counts.  Sorry-free.
-/

namespace SkewClassInflation.ThinParameters

open SkewJacobiNegative

variable (B : ThinParameters)

/-- The actual thin-power functions along a positive finite block word. -/
noncomputable def powerFunctions (l : List ℕ) (h : ∀ k ∈ l, 0 < k) : List CompleteRing :=
  l.attach.map (fun m => (B.innerPower m.val (h _ m.property)).toBetaDiagram.schur)

/-- The positive-word function inventory retains the original ordered head block. -/
theorem powerFunctions_cons (a : ℕ) (l : List ℕ) (h : ∀ k ∈ a :: l, 0 < k) :
    B.powerFunctions (a :: l) h =
      (B.innerPower a (h _ List.mem_cons_self)).toBetaDiagram.schur ::
        B.powerFunctions l (fun k hk => h k (List.mem_cons_of_mem _ hk)) := by
  simp [powerFunctions, List.attach_cons, List.map_map]

/-- A thin power's retained-unit polynomial has no unit variable, on the entire parameter domain. -/
theorem innerPower_unit_constant (a : ℕ) (ha : 0 < a) :
    (unitSchur (B.innerPower a ha)).coeff 0 = (B.innerPower a ha).toBetaDiagram.schur := by
  have hz := thick_positive_gaps_zeroFree (B.innerPower a ha) (B.innerPower_thick a ha)
    (fun _ => B.c_pos)
  rw [unitSchur_eq_C_of_zeroFree _ hz, Polynomial.coeff_C_zero]

/-- The actual chain constant coefficient is the product of its original thin block functions. -/
theorem chain_constant_coefficient (a : ℕ) (ha : 0 < a) (l : List ℕ)
    (h : ∀ k ∈ l, 0 < k) :
    (unitSchur (B.chain a ha l h).2).coeff 0 =
      ((B.innerPower a ha).toBetaDiagram.schur :: B.powerFunctions l h).prod := by
  induction l generalizing a with
  | nil => simp [chain, powerFunctions, B.innerPower_unit_constant]
  | cons b l ih =>
    change (unitSchur (Profile.zeroJoin (B.innerPower a ha)
      (B.chain b (h b List.mem_cons_self) l
        (fun k hk => h k (List.mem_cons_of_mem _ hk))).2)).coeff 0 = _
    rw [unitSchur_zeroJoin_constant, B.innerPower_unit_constant,
      ih b (h b List.mem_cons_self) (fun k hk => h k (List.mem_cons_of_mem _ hk)),
      B.powerFunctions_cons, List.prod_cons]
    simp only [List.prod_cons]

/-- The source constant coefficient for an arbitrary positive outer composition. -/
theorem diagram_constant_coefficient {M : ℕ} (α : Composition M) (hM : 0 < M) :
    (unitSchur (B.diagram α hM).2).coeff 0 =
      (B.powerFunctions α.blocks (fun _k hk => α.blocks_pos hk)).prod := by
  unfold diagram
  split
  · rename_i he
    have h := α.blocks_sum
    rw [he] at h
    simp only [List.sum_nil] at h
    omega
  · rename_i a l he
    have h := B.chain_constant_coefficient a
      (α.blocks_pos (by rw [he]; exact List.mem_cons_self)) l
      (fun k hk => α.blocks_pos (by rw [he]; exact List.mem_cons_of_mem _ hk))
    simpa only [he, B.powerFunctions_cons, List.prod_cons] using h

/-- Genuine source blocks carry their positive orders and their actual full determinants. -/
noncomputable def blockInventory {M : ℕ} (α : Composition M) : List (Σ k, BetaDiagram k) :=
  α.blocks.attach.map (fun m =>
    ⟨m.val + 1, (B.innerPower m.val (α.blocks_pos m.property)).toBetaDiagram⟩)

/-- Every factor in the source inventory is a nonempty connected full board. -/
theorem blockInventory_connected {M : ℕ} (α : Composition M)
    (X : Σ k, BetaDiagram k) (hX : X ∈ B.blockInventory α) : X.2.Connected := by
  obtain ⟨m, _, rfl⟩ := List.mem_map.mp hX
  exact (B.innerPower m.val (α.blocks_pos m.property)).toBetaDiagram_connected

/-- The source inventory and the literal product coefficient are the same polynomials. -/
theorem blockInventory_product {M : ℕ} (α : Composition M) :
    ((B.blockInventory α).map (fun X => X.2.schur)).prod =
      (B.powerFunctions α.blocks (fun _k hk => α.blocks_pos hk)).prod := by
  simp only [blockInventory, powerFunctions, List.map_map, Function.comp_def]

/-- An arbitrary full mate has exactly the source's thin component functions and sizes. -/
theorem arbitrary_mate_component_matching {M k : ℕ} (α : Composition M) (hM : 0 < M)
    (Q : Profile k)
    (he : Q.toBetaDiagram.schur = (B.diagram α hM).2.toBetaDiagram.schur) :
    Multiset.Rel (fun X Y : Σ n, BetaDiagram n => X.2.schur = Y.2.schur ∧ X.1 = Y.1)
      (zeroCutInventory Q : Multiset _) (B.blockInventory α : Multiset _) := by
  have hn := Nat.succ.inj
    (Q.toBetaDiagram.row_count_of_schur_eq (B.diagram α hM).2.toBetaDiagram he)
  subst k
  have hQ : Staircase.Thick Q := GeneralHessenberg.hessenberg_thick _
    (hessenberg_of_equal_schur (B.diagram α hM).2.toBetaDiagram Q.toBetaDiagram
      (B.diagram α hM).2.toBetaDiagram_connected Q.toBetaDiagram_connected he.symm
      (B.diagram_thick α hM).hessenberg)
  apply BetaDiagram.product_component_matching _ _
    (zeroCutInventory_connected Q) (B.blockInventory_connected α)
  rw [zeroCutInventory_product Q hQ, unitSchur_eq_of_schur_eq Q (B.diagram α hM).2 he,
    B.diagram_constant_coefficient, B.blockInventory_product]

end SkewClassInflation.ThinParameters
