/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.RibbonCoarseningRecursion

/-!
# Unordered ribbon endpoints from actual coarsening multiplicities

Formalizes `lem:ribbon-endpoints` of
`shields-2026-skew-class-inflation.tex`.  The original row partition and
its next-length coarsenings determine the incidence count of every row
value at adjacent boundaries, hence its endpoint multiplicity.
Repeated parts and coincident merger values are retained.  Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative

/-- Deficits in the next-length coarsenings, relative to the actual original row partition. -/
def coarseningDeficit (rows : Multiset ℕ+) (M : Multiset (Multiset ℕ+)) (v : ℕ+) : ℕ :=
  let k := rows.card
  let N := rows.count v
  (M.map (fun μ => if μ.card + 1 = k then N - μ.count v else 0)).sum

/-- The deficit statistic is additive in the complete partition inventory. -/
theorem coarseningDeficit_add (rows : Multiset ℕ+) (M N : Multiset (Multiset ℕ+)) (v : ℕ+) :
    coarseningDeficit rows (M + N) v = coarseningDeficit rows M v + coarseningDeficit rows N v := by
  simp only [coarseningDeficit, Multiset.map_add, Multiset.sum_add]

/-- A retained common prefix cancels from both the cardinality and multiplicity deficits. -/
theorem coarseningDeficit_prefix (rows : Multiset ℕ+) (M : Multiset (Multiset ℕ+)) (a v : ℕ+) :
    coarseningDeficit (a ::ₘ rows) (M.map (fun μ => a ::ₘ μ)) v =
      coarseningDeficit rows M v := by
  dsimp only [coarseningDeficit]
  rw [Multiset.map_map]
  apply congrArg (fun f : Multiset ℕ+ → ℕ => (M.map f).sum)
  funext μ
  have hc : (a ::ₘ μ).card + 1 = (a ::ₘ rows).card ↔ μ.card + 1 = rows.card := by
    simp only [Multiset.card_cons]
    omega
  have hn : (a ::ₘ rows).count v - (a ::ₘ μ).count v = rows.count v - μ.count v := by
    rw [Multiset.count_cons, Multiset.count_cons, Nat.add_sub_add_right]
  simp only [Function.comp_apply, hc, hn]

/-- The statistic uses every actual cut decision rather than a deduplicated partition set. -/
theorem coarseningDeficit_eq_sum (rows : Multiset ℕ+) {n : ℕ}
    (r : Fin (n + 1) → ℕ) (hr : ∀ i, 0 < r i) (v : ℕ+) :
    coarseningDeficit rows (coarseningPartitions r hr) v =
      ∑ S : Fin n → Bool, if (coarseningPartition r hr S).card + 1 = rows.card then
        rows.count v - (coarseningPartition r hr S).count v else 0 := by
  simp only [coarseningDeficit, coarseningPartitions, Multiset.map_map,
    Function.comp_apply, Finset.sum]

private theorem deficit_merge_count (rows : Multiset ℕ+) (a b v : ℕ+) :
    (a ::ₘ b ::ₘ rows).count v - ((a + b) ::ₘ rows).count v =
      (if v = a then 1 else 0) + (if v = b then 1 else 0) := by
  have ha : a ≠ a + b := by
    intro he
    have hh := congrArg PNat.val he
    simp only [PNat.add_coe] at hh
    have := b.pos
    omega
  have hb : b ≠ a + b := by
    intro he
    have hh := congrArg PNat.val he
    simp only [PNat.add_coe] at hh
    have := a.pos
    omega
  by_cases hv : v = a + b
  · subst v
    simp only [Multiset.count_cons, Ne.symm ha, Ne.symm hb, ite_true, ite_false, add_zero]
    omega
  · simp only [Multiset.count_cons, hv, ite_false, add_zero]
    omega

/-- The two original endpoints, counted with multiplicity even for a one-row ribbon. -/
def ribbonEndpointPartition {n : ℕ} (r : Fin (n + 1) → ℕ+) : Multiset ℕ+ :=
  r 0 ::ₘ r (Fin.last n) ::ₘ 0

/-- Next-length coarsenings count precisely the incidences at the first adjacent boundary. -/
theorem coarseningDeficit_positive_rec {n : ℕ} (r : Fin (n + 2) → ℕ+) (v : ℕ+) :
    coarseningDeficit (List.ofFn r : Multiset ℕ+)
        (coarseningPartitions (PNat.val ∘ r) (fun i => (r i).pos)) v =
      coarseningDeficit (List.ofFn (fun i : Fin (n + 1) => r i.succ) : Multiset ℕ+)
        (coarseningPartitions (fun i : Fin (n + 1) => (r i.succ).val)
          (fun i => (r i.succ).pos)) v +
        (if v = r 0 then 1 else 0) + (if v = r (0 : Fin (n + 1)).succ then 1 else 0) := by
  let tail : Fin (n + 1) → ℕ+ := fun i => r i.succ
  let rest : Fin n → ℕ+ := fun i => r i.succ.succ
  let merged : Fin (n + 1) → ℕ+ := Fin.cons (r 0 + r (0 : Fin (n + 1)).succ) rest
  have hrows : (List.ofFn r : Multiset ℕ+) = r 0 ::ₘ (List.ofFn tail : Multiset ℕ+) := by
    rw [List.ofFn_succ]
    rfl
  have htwo : (List.ofFn r : Multiset ℕ+) =
      r 0 ::ₘ r (0 : Fin (n + 1)).succ ::ₘ (List.ofFn rest : Multiset ℕ+) := by
    rw [List.ofFn_succ, List.ofFn_succ]
    rfl
  have hmergedRows : (List.ofFn merged : Multiset ℕ+) =
      (r 0 + r (0 : Fin (n + 1)).succ) ::ₘ (List.ofFn rest : Multiset ℕ+) := by
    rw [List.ofFn_cons]
    rfl
  have hcard : (List.ofFn r : Multiset ℕ+).card = n + 2 := by
    change (List.ofFn r).length = n + 2
    exact List.length_ofFn
  have htop : coarseningDeficit (List.ofFn r : Multiset ℕ+)
      (coarseningPartitions (PNat.val ∘ merged) (fun i => (merged i).pos)) v =
        (if v = r 0 then 1 else 0) + (if v = r (0 : Fin (n + 1)).succ then 1 else 0) := by
    calc
      _ = (List.ofFn r : Multiset ℕ+).count v -
          (rowPartition (PNat.val ∘ merged) (fun i => (merged i).pos)).count v := by
        rw [coarseningDeficit_eq_sum]
        calc
          _ = ∑ S : Fin n → Bool,
              if (coarseningPartition (PNat.val ∘ merged) (fun i => (merged i).pos) S).card = n + 1
              then (List.ofFn r : Multiset ℕ+).count v -
                (coarseningPartition (PNat.val ∘ merged) (fun i => (merged i).pos) S).count v
              else 0 := by
            apply Finset.sum_congr rfl
            intro S _
            have hc :
                (coarseningPartition (PNat.val ∘ merged) (fun i => (merged i).pos) S).card + 1 =
                    (List.ofFn r : Multiset ℕ+).card ↔
                (coarseningPartition (PNat.val ∘ merged) (fun i => (merged i).pos) S).card =
                    n + 1 := by
              rw [hcard]
              omega
            simp only [hc]
          _ = _ := sum_coarsening_top (PNat.val ∘ merged) (fun i => (merged i).pos)
            (fun μ => (List.ofFn r : Multiset ℕ+).count v - μ.count v)
      _ = _ := by
        rw [rowPartition_positive, htwo, hmergedRows]
        exact deficit_merge_count _ _ _ _
  have hprefix : coarseningDeficit (List.ofFn r : Multiset ℕ+)
      ((coarseningPartitions (fun i : Fin (n + 1) => (r i.succ).val)
        (fun i => (r i.succ).pos)).map
        (fun μ => r 0 ::ₘ μ)) v =
      coarseningDeficit (List.ofFn tail : Multiset ℕ+)
        (coarseningPartitions (fun i : Fin (n + 1) => (r i.succ).val)
          (fun i => (r i.succ).pos)) v := by
    rw [hrows, coarseningDeficit_prefix]
  rw [coarseningPartitions_positive_split, coarseningDeficit_add, htop, hprefix]
  dsimp only [tail]
  omega

/-- Internal rows have two boundary incidences; endpoints account for the remainder. -/
theorem coarseningDeficit_endpoint_count {n : ℕ} (r : Fin (n + 1) → ℕ+) (v : ℕ+) :
    coarseningDeficit (List.ofFn r : Multiset ℕ+)
        (coarseningPartitions (PNat.val ∘ r) (fun i => (r i).pos)) v +
      (ribbonEndpointPartition r).count v = 2 * (List.ofFn r : Multiset ℕ+).count v := by
  induction n with
  | zero =>
    rw [coarseningPartitions_positive_one]
    simp only [List.ofFn_succ, List.ofFn_zero]
    by_cases hv : v = r 0 <;>
      simp [coarseningDeficit, ribbonEndpointPartition, hv]
  | succ n ih =>
    have hh := ih (fun i : Fin (n + 1) => r i.succ)
    rw [coarseningDeficit_positive_rec]
    have hrows : (List.ofFn r : Multiset ℕ+) =
        r 0 ::ₘ (List.ofFn (fun i : Fin (n + 1) => r i.succ) : Multiset ℕ+) := by
      rw [List.ofFn_succ]
      rfl
    rw [hrows, Multiset.count_cons]
    simp only [ribbonEndpointPartition, Multiset.count_cons, Multiset.count_zero,
      Fin.succ_last, Nat.succ_eq_add_one, Function.comp_def] at hh ⊢
    omega

/-- The actual coarsening inventory determines the full unordered pair of positive endpoints. -/
theorem ribbonEndpoints_of_coarsening_eq {n m : ℕ}
    (r : Fin (n + 1) → ℕ+) (s : Fin (m + 1) → ℕ+)
    (he : coarseningPartitions (PNat.val ∘ r) (fun i => (r i).pos) =
      coarseningPartitions (PNat.val ∘ s) (fun i => (s i).pos)) :
    ribbonEndpointPartition r = ribbonEndpointPartition s := by
  classical
  have hrows := coarseningPartitions_rowPartition (PNat.val ∘ r) (PNat.val ∘ s)
    (fun i => (r i).pos) (fun i => (s i).pos) he
  rw [rowPartition_positive, rowPartition_positive] at hrows
  apply Multiset.ext.mpr
  intro v
  have hr := coarseningDeficit_endpoint_count r v
  have hs := coarseningDeficit_endpoint_count s v
  rw [he, hrows] at hr
  omega

/-- Ribbon equality preserves the actual unordered pair of endpoint parts.

**Differs from the paper's route.** Recovers endpoint incidences from the maximal
and next-length coarsening partitions, without using factor-reversal classification. -/
theorem ribbon_endpoints_of_eq {n m : ℕ}
    (r : Fin (n + 1) → ℕ) (s : Fin (m + 1) → ℕ)
    (hr : ∀ i, 0 < r i) (hs : ∀ i, 0 < s i)
    (he : ribbonWord (List.ofFn r) = ribbonWord (List.ofFn s)) :
    (r 0 ::ₘ r (Fin.last n) ::ₘ 0 : Multiset ℕ) =
      s 0 ::ₘ s (Fin.last m) ::ₘ 0 := by
  let rp : Fin (n + 1) → ℕ+ := fun i => ⟨r i, hr i⟩
  let sp : Fin (m + 1) → ℕ+ := fun i => ⟨s i, hs i⟩
  have hm := (ribbon_eq_iff_coarseningPartitions r s hr hs).mp he
  have hp : coarseningPartitions (PNat.val ∘ rp) (fun i => (rp i).pos) =
      coarseningPartitions (PNat.val ∘ sp) (fun i => (sp i).pos) := hm
  have hh := congrArg (Multiset.map PNat.val) (ribbonEndpoints_of_coarsening_eq rp sp hp)
  simp only [ribbonEndpointPartition, Multiset.map_cons, Multiset.map_zero] at hh
  exact hh

end SkewClassInflation
