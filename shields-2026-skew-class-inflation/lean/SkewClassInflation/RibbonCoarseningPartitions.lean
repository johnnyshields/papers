/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.RibbonCoarseningEquivalence
import Mathlib.Data.Finsupp.Multiset

/-!
# Ribbon equality as equality of actual coarsening partitions

The partition-multiplicity formulation of the ribbon classification used
in `lem:overlap-power-rigidity` of `shields-2026-skew-class-inflation.tex`.
Each unordered coarsening is a multiset of positive parts.  Its canonical
exponent vector identifies its monomial, and rational coefficients retain
its exact multiplicity.  Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative

/-- A positive row word with its actual values retained as positive indices. -/
def positiveWord (w : List ℕ) (hw : ∀ a ∈ w, 0 < a) : List ℕ+ :=
  w.attach.map (fun a => (⟨a.val, hw a.val a.property⟩ : ℕ+))

/-- The conversion preserves each original ordered part. -/
theorem positiveWord_cons (a : ℕ) (w : List ℕ) (hw : ∀ b ∈ a :: w, 0 < b) :
    positiveWord (a :: w) hw =
      ⟨a, hw a List.mem_cons_self⟩ ::
        positiveWord w (fun b hb => hw b (List.mem_cons_of_mem _ hb)) := by
  let f : {b : ℕ // b ∈ a :: w} → ℕ+ := fun b => ⟨b.val, hw b.val b.property⟩
  let g : {b : ℕ // b ∈ w} → ℕ+ := fun b =>
    ⟨b.val, hw b.val (List.mem_cons_of_mem _ b.property)⟩
  let j : ℕ+ := ⟨a, hw a List.mem_cons_self⟩
  change (a :: w).attach.map f = j :: w.attach.map g
  rw [List.attach_cons, List.map_cons, List.map_map]
  rfl

/-- Reading the positive values returns the literal original row word. -/
theorem positiveWord_values (w : List ℕ) (hw : ∀ a ∈ w, 0 < a) :
    (positiveWord w hw).map PNat.val = w := by
  let f : {a : ℕ // a ∈ w} → ℕ+ := fun a => ⟨a.val, hw a.val a.property⟩
  change (w.attach.map f).map PNat.val = w
  rw [List.map_map]
  change w.attach.map Subtype.val = w
  exact List.attach_map_subtype_val w

/-- Conversion retains the full number of rows, not merely their total weight. -/
theorem positiveWord_length (w : List ℕ) (hw : ∀ a ∈ w, 0 < a) :
    (positiveWord w hw).length = w.length := by
  let f : {a : ℕ // a ∈ w} → ℕ+ := fun a => ⟨a.val, hw a.val a.property⟩
  change (w.attach.map f).length = w.length
  rw [List.length_map, List.length_attach]

/-- Equal positive words give equal positive-index words independently of positivity proofs. -/
theorem positiveWord_congr {u v : List ℕ} (hu : ∀ a ∈ u, 0 < a)
    (hv : ∀ a ∈ v, 0 < a) (he : u = v) : positiveWord u hu = positiveWord v hv := by
  cases he
  rfl

private theorem partitionExponent_cons (a : ℕ+) (μ : Multiset ℕ+) :
    (a ::ₘ μ).toFinsupp = Finsupp.single a 1 + μ.toFinsupp := by
  classical
  ext j
  by_cases hj : j = a
  · subst j
    simp only [Multiset.toFinsupp_apply, Multiset.count_cons, Finsupp.add_apply,
      Finsupp.single_eq_same, ite_true]
    omega
  · have haj : a ≠ j := Ne.symm hj
    simp only [Multiset.toFinsupp_apply, Multiset.count_cons, Finsupp.add_apply,
      Finsupp.single_apply, hj, haj, ite_false, add_zero, zero_add]

private theorem positiveWord_generator_monomial (w : List ℕ+) :
    (w.map (fun j => (MvPolynomial.X j : CompleteRing))).prod =
      MvPolynomial.monomial (w : Multiset ℕ+).toFinsupp 1 := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [List.map_cons, List.prod_cons, ih]
    change MvPolynomial.X a * MvPolynomial.monomial (w : Multiset ℕ+).toFinsupp 1 =
      MvPolynomial.monomial (a ::ₘ (w : Multiset ℕ+)).toFinsupp 1
    rw [partitionExponent_cons, MvPolynomial.X, MvPolynomial.monomial_mul_monomial, one_mul]

/-- The actual complete product is exactly the monomial of its unordered positive parts. -/
theorem positiveWord_monomial (w : List ℕ) (hw : ∀ a ∈ w, 0 < a) :
    (w.map (fun a : ℕ => complete a)).prod =
      MvPolynomial.monomial (positiveWord w hw : Multiset ℕ+).toFinsupp 1 := by
  rw [← positiveWord_generator_monomial]
  apply congrArg List.prod
  calc
    w.map (fun a : ℕ => complete a) =
        ((positiveWord w hw).map PNat.val).map (fun a : ℕ => complete a) :=
      congrArg (List.map (fun a : ℕ => complete a)) (positiveWord_values w hw).symm
    _ = (positiveWord w hw).map (fun j => MvPolynomial.X j) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro j _
      exact complete_nat j

/-- The actual unordered partition produced by one specified adjacent-boundary decision. -/
def coarseningPartition {n : ℕ} (r : Fin (n + 1) → ℕ) (hr : ∀ i, 0 < r i)
    (S : Fin n → Bool) : Multiset ℕ+ :=
  (positiveWord (coarsenRows r S) (coarsenRows_pos r hr S) : Multiset ℕ+)

/-- A specified coarsening retains its exact number of actual parts. -/
theorem coarseningPartition_card {n : ℕ} (r : Fin (n + 1) → ℕ) (hr : ∀ i, 0 < r i)
    (S : Fin n → Bool) :
    (coarseningPartition r hr S).card = (coarsenRows r S).length := by
  change (positiveWord (coarsenRows r S) (coarsenRows_pos r hr S)).length = _
  exact positiveWord_length _ _

/-- Forgetting positivity retains every original natural part of the actual coarsening. -/
theorem coarseningPartition_values {n : ℕ} (r : Fin (n + 1) → ℕ) (hr : ∀ i, 0 < r i)
    (S : Fin n → Bool) :
    (coarseningPartition r hr S).map PNat.val = (coarsenRows r S : Multiset ℕ) := by
  change (positiveWord (coarsenRows r S) (coarsenRows_pos r hr S) : Multiset ℕ+).map PNat.val = _
  rw [Multiset.map_coe]
  exact congrArg (fun w : List ℕ => (w : Multiset ℕ))
    (positiveWord_values _ (coarsenRows_pos r hr S))

/-- The actual multiset of unordered positive coarsenings, retaining repeated partitions. -/
noncomputable def coarseningPartitions {n : ℕ} (r : Fin (n + 1) → ℕ) (hr : ∀ i, 0 < r i) :
    Multiset (Multiset ℕ+) :=
  Finset.univ.val.map (coarseningPartition r hr)

/-- Every actual partition multiplicity is the exact number of masks producing that partition. -/
theorem coarseningPartitions_count_filter {n : ℕ} (r : Fin (n + 1) → ℕ)
    (hr : ∀ i, 0 < r i) (μ : Multiset ℕ+) :
    (coarseningPartitions r hr).count μ =
      (Finset.univ.filter (fun S : Fin n → Bool => coarseningPartition r hr S = μ)).card := by
  classical
  rw [coarseningPartitions, Multiset.count_map]
  change (Finset.univ.filter (fun S : Fin n → Bool => μ = coarseningPartition r hr S)).card = _
  congr 1
  ext S
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact eq_comm

/-- Every specified decision is represented in the full inventory, with its multiplicity. -/
theorem coarseningPartition_mem {n : ℕ} (r : Fin (n + 1) → ℕ) (hr : ∀ i, 0 < r i)
    (S : Fin n → Bool) : coarseningPartition r hr S ∈ coarseningPartitions r hr :=
  Multiset.mem_map.mpr ⟨S, by simp, rfl⟩

/-- Cardinality counts actual coarsenings with multiplicity, not distinct partition values. -/
theorem coarseningPartitions_card {n : ℕ} (r : Fin (n + 1) → ℕ) (hr : ∀ i, 0 < r i) :
    (coarseningPartitions r hr).card = 2 ^ n := by
  rw [coarseningPartitions, Multiset.card_map]
  change Fintype.card (Fin n → Bool) = 2 ^ n
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-- Every unordered coarsening is an actual positive partition of the original total weight. -/
theorem coarsening_partition_weight {n : ℕ} (r : Fin (n + 1) → ℕ) (hr : ∀ i, 0 < r i)
    (μ : Multiset ℕ+) (hμ : μ ∈ coarseningPartitions r hr) :
    (μ.map PNat.val).sum = ∑ i, r i := by
  obtain ⟨S, _, rfl⟩ := Multiset.mem_map.mp hμ
  rw [coarseningPartition_values]
  exact coarsenRows_sum r S

/-- Turn a partition inventory into its actual polynomial with multiplicity as coefficient. -/
noncomputable def partitionPolynomial (M : Multiset (Multiset ℕ+)) : CompleteRing :=
  (M.map (fun μ => MvPolynomial.monomial μ.toFinsupp (1 : ℚ))).sum

/-- Coefficients in the independent-generator basis are the exact natural multiplicities. -/
theorem partitionPolynomial_coefficient (M : Multiset (Multiset ℕ+)) (μ : Multiset ℕ+) :
    (partitionPolynomial M).coeff μ.toFinsupp = (M.count μ : ℚ) := by
  classical
  refine Multiset.induction_on M ?_ ?_
  · simp [partitionPolynomial]
  · intro ν M ih
    unfold partitionPolynomial at ⊢
    rw [Multiset.map_cons, Multiset.sum_cons]
    change (MvPolynomial.monomial ν.toFinsupp (1 : ℚ) + partitionPolynomial M).coeff
      μ.toFinsupp = _
    simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, MvPolynomial.coeff_monomial, ih]
    by_cases hν : ν = μ
    · subst ν
      simp only [ite_true, Multiset.count_cons, Nat.cast_add, Nat.cast_one]
      ring
    · have hExp : ν.toFinsupp ≠ μ.toFinsupp := by
        intro he
        exact hν (Multiset.toFinsupp.injective he)
      simp only [hExp, ite_false, zero_add, Multiset.count_cons, Ne.symm hν, add_zero]

/-- Rational monomial coefficients lose no unordered coarsening and no multiplicity. -/
theorem partitionPolynomial_injective : Function.Injective partitionPolynomial := by
  classical
  intro M N he
  apply Multiset.ext.mpr
  intro μ
  have hh := congrArg (fun p : CompleteRing => p.coeff μ.toFinsupp) he
  rw [partitionPolynomial_coefficient, partitionPolynomial_coefficient] at hh
  exact_mod_cast hh

/-- The unsigned polynomial retains the actual coarsening partition multiset. -/
theorem unsignedCoarsening_eq_partitionPolynomial {n : ℕ}
    (r : Fin (n + 1) → ℕ) (hr : ∀ i, 0 < r i) :
    unsignedCoarseningPolynomial r = partitionPolynomial (coarseningPartitions r hr) := by
  unfold partitionPolynomial coarseningPartitions
  rw [Multiset.map_map]
  change (Finset.univ.val.map (fun S : Fin n → Bool =>
      ((coarsenRows r S).map (fun a : ℕ => complete a)).prod)).sum = _
  apply congrArg (fun f : (Fin n → Bool) → CompleteRing => (Finset.univ.val.map f).sum)
  funext S
  exact positiveWord_monomial _ (coarsenRows_pos r hr S)

/-- The coefficient of a partition is the number of actual coarsenings realizing that partition. -/
theorem coarsening_partition_count {n : ℕ} (r : Fin (n + 1) → ℕ) (hr : ∀ i, 0 < r i)
    (μ : Multiset ℕ+) :
    (unsignedCoarseningPolynomial r).coeff μ.toFinsupp =
      ((coarseningPartitions r hr).count μ : ℚ) := by
  rw [unsignedCoarsening_eq_partitionPolynomial r hr, partitionPolynomial_coefficient]

/-- Actual ribbon equality is equivalent to equality of unordered coarsenings with multiplicity. -/
theorem ribbon_eq_iff_coarseningPartitions {n m : ℕ}
    (r : Fin (n + 1) → ℕ) (s : Fin (m + 1) → ℕ)
    (hr : ∀ i, 0 < r i) (hs : ∀ i, 0 < s i) :
    ribbonWord (List.ofFn r) = ribbonWord (List.ofFn s) ↔
      coarseningPartitions r hr = coarseningPartitions s hs := by
  rw [ribbon_eq_iff_unsignedCoarsening r s hr hs,
    unsignedCoarsening_eq_partitionPolynomial r hr,
    unsignedCoarsening_eq_partitionPolynomial s hs]
  exact partitionPolynomial_injective.eq_iff

end SkewClassInflation
