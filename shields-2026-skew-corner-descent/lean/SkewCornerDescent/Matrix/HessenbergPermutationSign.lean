/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.HessenbergAdmissibleIntervals

/-!
# Exact selected-cost sign of a complete Hessenberg permutation

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The forced complete intervals give a bijection between inversion pairs and
selected subdiagonal occurrences. Both their cardinality and the full permutation
sign are proved; no interval partition or sign formula is supplied. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

/-- At an ordered pair of source states, inversion is exactly membership in the
complete upper interval. Injectivity excludes equality of the two target columns. -/
theorem hessenberg_inversion_iff {N : ℕ} (σ : Equiv.Perm (Fin N))
    (hσ : ∀ k : Fin N, k.val ≤ (σ k).val + 1) (i k : Fin N) (hik : i.val < k.val) :
    (σ k).val ≤ (σ i).val ↔ k.val ≤ (σ i).val := by
  have hne : (σ k).val ≠ (σ i).val := by
    intro h
    have he : k = i := σ.injective (Fin.ext h)
    have hv := congrArg Fin.val he
    omega
  constructor
  · intro h
    have hb := hσ k
    omega
  · intro h
    have hf := hessenberg_forced_subdiagonals σ hσ i (by omega) k hik h
    omega

private theorem sign_eq_aux {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    Equiv.Perm.sign σ = Equiv.Perm.signAux σ := by
  induction σ using Equiv.Perm.swap_induction_on with
  | one => simp only [map_one, Equiv.Perm.signAux_one]
  | swap_mul σ x y hxy ih =>
    rw [map_mul, Equiv.Perm.signAux_mul, Equiv.Perm.sign_swap hxy,
      Equiv.Perm.signAux_swap hxy, ih]

/-- Every inversion pair is exactly one actual selected subdiagonal occurrence.
The pair's upper endpoint is supplied by the complete permutation's forced interval. -/
theorem hessenberg_inversions_card {N : ℕ} (σ : Equiv.Perm (Fin N))
    (hσ : ∀ k : Fin N, k.val ≤ (σ k).val + 1) :
    ((Equiv.Perm.finPairsLT N).filter (fun a => σ a.1 ≤ σ a.2)).card =
      (Finset.univ.filter (fun k : Fin N => (σ k).val < k.val)).card := by
  classical
  let S := (Equiv.Perm.finPairsLT N).filter (fun a => σ a.1 ≤ σ a.2)
  have hmem (a : Σ _ : Fin N, Fin N) : a ∈ S ↔
      a.2.val < a.1.val ∧ a.1.val ≤ (σ a.2).val := by
    simp only [S, Finset.mem_filter, Equiv.Perm.mem_finPairsLT, Fin.lt_def, Fin.le_def]
    constructor
    · rintro ⟨hlt, h⟩
      exact ⟨hlt, (hessenberg_inversion_iff σ hσ _ _ hlt).mp h⟩
    · rintro ⟨hlt, h⟩
      exact ⟨hlt, (hessenberg_inversion_iff σ hσ _ _ hlt).mpr h⟩
  change S.card = _
  apply Finset.card_bij (fun a _ => a.1)
  · intro a ha
    obtain ⟨hlt, hle⟩ := (hmem a).mp ha
    have hf := hessenberg_forced_subdiagonals σ hσ a.2 (by omega) a.1 hlt hle
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
  · rintro ⟨k, i⟩ ha ⟨l, j⟩ hb he
    change k = l at he
    subst l
    obtain ⟨hi, hik⟩ := (hmem ⟨k, i⟩).mp ha
    obtain ⟨hj, hjk⟩ := (hmem ⟨k, j⟩).mp hb
    change i.val < k.val at hi
    change k.val ≤ (σ i).val at hik
    change j.val < k.val at hj
    change k.val ≤ (σ j).val at hjk
    have hf := hessenberg_forced_subdiagonals σ hσ i (by omega) k hi hik
    have hlower : (σ k).val < k.val := by omega
    obtain ⟨u, _, hu⟩ := hessenberg_lower_interval_unique σ hσ k hlower
    have heq : i = j := (hu i ⟨hi, hik⟩).trans (hu j ⟨hj, hjk⟩).symm
    subst j
    rfl
  · intro k hk
    have hlower := (Finset.mem_filter.mp hk).2
    obtain ⟨i, hi, hik⟩ := permutation_lower_crossing σ k hlower
    exact ⟨⟨k, i⟩, (hmem _).mpr ⟨hi, hik⟩, rfl⟩

/-- The full original permutation sign is the exact parity of its selected cost,
including singleton diagonal intervals and the empty permutation. -/
theorem hessenberg_permutation_sign {N : ℕ} (σ : Equiv.Perm (Fin N))
    (hσ : ∀ k : Fin N, k.val ≤ (σ k).val + 1) :
    Equiv.Perm.sign σ = (-1 : ℤˣ) ^
      (Finset.univ.filter (fun k : Fin N => (σ k).val < k.val)).card := by
  classical
  rw [sign_eq_aux]
  unfold Equiv.Perm.signAux
  rw [Finset.prod_ite]
  simp only [Finset.prod_const, one_pow, mul_one]
  rw [hessenberg_inversions_card σ hσ]

end SkewCornerDescent.Matrix
