/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.SaturationSourceData
import SkewClassInflation.ZeroJoinRecurrence
import SkewClassInflation.FactorMatching
import SkewClassInflation.DistinguishedCutInventory

/-!
# Actual cut coefficients for arbitrary repeated-block sources

The product coefficient in `eq:cut-components` of
`shields-2026-skew-class-inflation.tex`.  All factors are the actual
connected repeated powers, not abstract polynomial surrogates.
Sorry-free.
-/

namespace SkewClassInflation.SaturationInner

open SkewJacobiNegative SkewJacobiNegative.Staircase

variable (A : SaturationInner)

/-- The larger seam is a genuine positive complete-generator index, even when `c = 0`. -/
def largeLabel : ℕ+ := ⟨A.d, by have := A.c_lt_d; omega⟩

/-- A repeated inner power contains no occurrence of the distinguished larger-seam generator. -/
theorem power_excludes_large_label (m : ℕ) (hm : 0 < m) :
    A.largeLabel ∉ (A.power m hm).toBetaDiagram.schur.vars := by
  apply not_mem_vars_det
  intro i j hmem
  change A.largeLabel ∈ (complete ((A.power m hm).xi i - (A.power m hm).zeta j)).vars at hmem
  have he := (mem_vars_complete_iff _ A.largeLabel).mp hmem
  obtain ⟨s, _, _, hs⟩ := (distinguished_index_iff_seam (A.power m hm)
    (A.power_thick m hm) A.largeLabel (A.power_rows_above_seam m hm) i j).mp he.symm
  change A.c = A.d at hs
  exact (ne_of_lt A.c_lt_d) hs

/-- Actual positive powers along a finite ordered source word. -/
noncomputable def powerFunctions (l : List ℕ) (hl : ∀ m ∈ l, 0 < m) : List CompleteRing :=
  l.attach.map (fun m => (A.power m.val (hl _ m.property)).toBetaDiagram.schur)

/-- Prepending a part prepends its actual power polynomial, retaining every repeated occurrence. -/
theorem powerFunctions_cons (a : ℕ) (l : List ℕ) (hl : ∀ m ∈ a :: l, 0 < m) :
    A.powerFunctions (a :: l) hl =
      (A.power a (hl _ List.mem_cons_self)).toBetaDiagram.schur ::
        A.powerFunctions l (fun m hm => hl m (List.mem_cons_of_mem _ hm)) := by
  simp [powerFunctions, List.attach_cons, List.map_map]

/-- Erasing the larger seam cuts the literal chain into exactly its original power factors. -/
theorem chain_constant_coefficient (a : ℕ) (ha : 0 < a)
    (l : List ℕ) (hl : ∀ m ∈ l, 0 < m) :
    eraseGenerator A.largeLabel (A.chain a ha l hl).2.toBetaDiagram.schur =
      ((A.power a ha).toBetaDiagram.schur :: A.powerFunctions l hl).prod := by
  induction l generalizing a with
  | nil =>
    change eraseGenerator A.largeLabel (A.power a ha).toBetaDiagram.schur = _
    rw [eraseGenerator_eq_self _ _ (A.power_excludes_large_label a ha)]
    simp [powerFunctions]
  | cons b l ih =>
    let P := A.power a ha
    let Q := A.chain b (hl b List.mem_cons_self) l
      (fun j hj => hl j (List.mem_cons_of_mem _ hj))
    have hp : A.d < P.r (Fin.last (a * A.k)) := A.power_rows_above_seam a ha _
    have hq : A.d < Q.2.r 0 := by
      rw [A.chain_first]
      have := A.first_bound
      omega
    have hJ : Staircase.Thick (Profile.join P Q.2 A.d hp hq) := A.chain_thick a ha (b :: l) hl
    have hd : eraseGenerator A.largeLabel (complete A.d) = 0 := by
      rw [eraseGenerator_complete]
      change (if (A.d : ℤ) = (A.d : ℤ) then (0 : CompleteRing) else complete A.d) = 0
      rw [ite_eq_left rfl]
    change eraseGenerator A.largeLabel (Profile.join P Q.2 A.d hp hq).toBetaDiagram.schur = _
    rw [Profile.join_schur P Q.2 A.d hp hq hJ, map_sub, map_mul, map_mul, hd,
      zero_mul, sub_zero, eraseGenerator_eq_self _ _ (A.power_excludes_large_label a ha)]
    rw [ih b (hl b List.mem_cons_self) (fun j hj => hl j (List.mem_cons_of_mem _ hj)),
      A.powerFunctions_cons, List.prod_cons, List.prod_cons]
    simp only [List.prod_cons]

/-- The source constant coefficient is the product of its actual connected block functions. -/
theorem diagram_constant_coefficient {M : ℕ} (α : Composition M) (hM : 0 < M) :
    eraseGenerator A.largeLabel (A.diagram α hM).2.toBetaDiagram.schur =
      (A.powerFunctions α.blocks (fun _ hm => α.blocks_pos hm)).prod := by
  unfold diagram
  split
  · rename_i he
    have hs := α.blocks_sum
    rw [he] at hs
    simp only [List.sum_nil] at hs
    omega
  · rename_i a l he
    have ha := α.blocks_pos (by rw [he]; exact List.mem_cons_self)
    have hl : ∀ m ∈ l, 0 < m := fun _ hm =>
      α.blocks_pos (by rw [he]; exact List.mem_cons_of_mem _ hm)
    simpa only [he, A.powerFunctions_cons, List.prod_cons] using
      A.chain_constant_coefficient a ha l hl

/-- Source block factors retain their actual full row counts and their positive multiplicities. -/
noncomputable def blockInventory {M : ℕ} (α : Composition M) : List (Σ k, BetaDiagram k) :=
  α.blocks.attach.map (fun m =>
    ⟨m.val * A.k + 1, (A.power m.val (α.blocks_pos m.property)).toBetaDiagram⟩)

/-- Every source factor is connected without a single-copy rigidity hypothesis. -/
theorem blockInventory_connected {M : ℕ} (α : Composition M)
    (X : Σ k, BetaDiagram k) (hX : X ∈ A.blockInventory α) : X.2.Connected := by
  obtain ⟨m, _, rfl⟩ := List.mem_map.mp hX
  exact (A.power m.val (α.blocks_pos m.property)).toBetaDiagram_connected

/-- The actual source inventory agrees with its literal power-product coefficient. -/
theorem blockInventory_product {M : ℕ} (α : Composition M) :
    ((A.blockInventory α).map (fun X => X.2.schur)).prod =
      (A.powerFunctions α.blocks (fun _ hm => α.blocks_pos hm)).prod := by
  simp only [blockInventory, powerFunctions, List.map_map, Function.comp_def]

/-- Every arbitrary mate has exactly the original connected power factors, with multiplicity. -/
theorem arbitrary_mate_component_matching {M n : ℕ} (α : Composition M) (hM : 0 < M)
    (P : Profile n)
    (he : P.toBetaDiagram.schur = (A.diagram α hM).2.toBetaDiagram.schur) :
    Multiset.Rel (fun X Y : Σ k, BetaDiagram k => X.2.schur = Y.2.schur ∧ X.1 = Y.1)
      (distinguishedCutInventory P A.largeLabel : Multiset _)
      (A.blockInventory α : Multiset _) := by
  have hdata := A.source_mate_reduction α hM P he
  apply BetaDiagram.product_component_matching _ _
    (distinguishedCutInventory_connected P A.largeLabel) (A.blockInventory_connected α)
  rw [distinguishedCutInventory_product P hdata.2.1 A.largeLabel hdata.2.2.1,
    he, A.diagram_constant_coefficient, A.blockInventory_product]

end SkewClassInflation.SaturationInner
