/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.LabeledPartitionOrders

/-!
# Exact labeled coarsening counts, including repeated parts

The arbitrary-length counting input for the even-discrepancy
reconstruction argument in `thm:sharp-inflation` of
`shields-2026-skew-class-inflation.tex`.  Every distinct order has the
same actual index-permutation fiber.  Multiplying the genuine partition
coefficient by that fiber counts labeled retained orders exactly.
Sorry-free.
-/

namespace SkewClassInflation

/-- The actual natural word read from one labeled ordering. -/
def labeledOrderWord {n : ℕ} (f : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) : List ℕ :=
  List.ofFn (f ∘ σ)

/-- Actual index permutations presenting a specified natural word. -/
noncomputable def labeledOrderFiber {n : ℕ} (f : Fin n → ℕ) (w : List ℕ) :
    Finset (Equiv.Perm (Fin n)) := by
  classical
  exact Finset.univ.filter (fun σ => labeledOrderWord f σ = w)

/-- All actual word fibers have the same size, by right translation of index permutations. -/
theorem labeledOrderFiber_card {n : ℕ} (f : Fin n → ℕ) (τ : Equiv.Perm (Fin n)) :
    (labeledOrderFiber f (labeledOrderWord f τ)).card =
      (labeledOrderFiber f (List.ofFn f)).card := by
  classical
  symm
  refine Finset.card_bij (fun σ _ => σ * τ) ?_ ?_ ?_
  · intro σ hσ
    have he := (Finset.mem_filter.mp hσ).2
    have hfun : f ∘ σ = f := List.ofFn_injective he
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    apply congrArg List.ofFn
    funext i
    exact congrFun hfun (τ i)
  · intro σ _ ρ _ he
    exact mul_right_cancel he
  · intro ρ hρ
    have he := (Finset.mem_filter.mp hρ).2
    have hfun : f ∘ ρ = f ∘ τ := List.ofFn_injective he
    refine ⟨ρ * τ⁻¹, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, by simp⟩
    apply congrArg List.ofFn
    funext i
    have hh := congrFun hfun (τ⁻¹ i)
    change f (ρ (τ⁻¹ i)) = f (τ (τ⁻¹ i)) at hh
    rw [show τ (τ⁻¹ i) = i from τ.apply_symm_apply i] at hh
    exact hh

/-- Actual labeled coarsenings retaining precisely the composition's available cuts. -/
noncomputable def labeledCoarseningOrders {N n : ℕ} (α : Composition N) (f : Fin n → ℕ+) :
    Finset (Equiv.Perm (Fin n)) := by
  classical
  exact Finset.univ.filter (fun σ =>
    wordProperCuts (labeledOrderWord (fun i => (f i).val) σ) ⊆ properCuts α)

/-- The labeled count is exactly the genuine partition coefficient times its common fiber. -/
theorem labeledCoarseningOrders_card {N n : ℕ} (α : Composition N) (f : Fin n → ℕ+)
    (hsum : (List.ofFn (fun i => (f i).val)).sum = N) :
    (labeledCoarseningOrders α f).card =
      (coarseningInventory α).count ((List.ofFn f : List ℕ+) : Multiset ℕ+) *
        (labeledOrderFiber (fun i => (f i).val) (List.ofFn (fun i => (f i).val))).card := by
  classical
  let g := fun σ : Equiv.Perm (Fin n) => labeledOrderWord (fun i => (f i).val) σ
  let A := (partitionOrders (List.ofFn f)).filter (fun w => wordProperCuts w ⊆ properCuts α)
  have horder (σ : Equiv.Perm (Fin n)) : g σ ∈ partitionOrders (List.ofFn f) := by
    rw [partitionOrders_ofFn_perms]
    exact Finset.mem_image.mpr ⟨σ, Finset.mem_univ _, rfl⟩
  have hfilter : Finset.univ.filter (fun σ => g σ ∈ A) = labeledCoarseningOrders α f := by
    ext σ
    simp only [A, labeledCoarseningOrders, Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_iff_right (horder σ)
  have hcount := Finset.sum_card_fiberwise_eq_card_filter Finset.univ A g
  rw [hfilter] at hcount
  rw [← hcount]
  have heach : ∀ w ∈ A, (Finset.univ.filter (fun σ => g σ = w)).card =
      (labeledOrderFiber (fun i => (f i).val) (List.ofFn (fun i => (f i).val))).card := by
    intro w hw
    have ho := (Finset.mem_filter.mp hw).1
    rw [partitionOrders_ofFn_perms] at ho
    obtain ⟨τ, _, rfl⟩ := Finset.mem_image.mp ho
    exact labeledOrderFiber_card (fun i => (f i).val) τ
  rw [Finset.sum_congr rfl heach, Finset.sum_const, nsmul_eq_mul]
  have hsum' : ((List.ofFn f).map PNat.val).sum = N := by
    simpa only [List.map_ofFn, Function.comp_def] using hsum
  rw [coarseningInventory_count_orders α (List.ofFn f) hsum']
  rfl

/-- Equal actual inventories preserve every labeled retained-order count, without distinct parts. -/
theorem labeledCoarseningOrders_card_invariant {N n : ℕ} (α β : Composition N)
    (he : coarseningInventory α = coarseningInventory β) (f : Fin n → ℕ+)
    (hsum : (List.ofFn (fun i => (f i).val)).sum = N) :
    (labeledCoarseningOrders α f).card = (labeledCoarseningOrders β f).card := by
  rw [labeledCoarseningOrders_card α f hsum, labeledCoarseningOrders_card β f hsum, he]

end SkewClassInflation
