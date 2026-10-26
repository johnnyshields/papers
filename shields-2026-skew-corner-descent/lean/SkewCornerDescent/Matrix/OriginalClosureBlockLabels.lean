/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalClosureCuts

/-!
# Produced original block labels in both closure copies

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`). Counting the literal
cut list identifies every upper label with its source label and every lower label with
its source label plus the complete upper cut count and central cut. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- The canonical original block label counts precisely the preceding actual cuts. -/
theorem interiorBlock_eq_sum {n : ℕ} (P : Profile n) (i : Fin n) :
    interiorBlock P i = ∑ k : Fin n, if k ∈ interiorCuts P ∧ k ≤ i then 1 else 0 := by
  classical
  rw [Finset.sum_boole]
  unfold interiorBlock
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- The actual upper-copy block labels agree with the source's canonical block labels. -/
theorem originalHorizontalClosure_block_upper {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (i : Fin n) :
    interiorBlock Q (originalClosureComplementaryEquiv P Q v hQ (.inl i)) =
      interiorBlock P i := by
  classical
  let e := originalClosureComplementaryEquiv P Q v hQ
  rw [interiorBlock_eq_sum Q, ← e.sum_comp]
  rw [Fintype.sum_sum_type]
  have hup : (∑ k : Fin n, if e (.inl k) ∈ interiorCuts Q ∧ e (.inl k) ≤ e (.inl i)
      then 1 else 0) = interiorBlock P i := by
    rw [interiorBlock_eq_sum]
    apply Finset.sum_congr rfl
    intro k _
    have ho : e (.inl k) ≤ e (.inl i) ↔ k ≤ i := by rfl
    have hc : e (.inl k) ∈ interiorCuts Q ↔ k ∈ interiorCuts P :=
      originalHorizontalClosure_cut_upper P Q v hQ k
    simp only [hc, ho]
  have hlo : (∑ k : Fin n, if e (.inr k) ∈ interiorCuts Q ∧ e (.inr k) ≤ e (.inl i)
      then 1 else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    have ho : ¬ e (.inr k) ≤ e (.inl i) := by
      change ¬ n + k.val ≤ i.val
      have hi := i.isLt
      omega
    simp only [ho, and_false, ite_false]
  change _ + _ = interiorBlock P i
  rw [hup, hlo, add_zero]

/-- Every lower-copy label includes all upper cuts and the genuine central cut. -/
theorem originalHorizontalClosure_block_lower {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (i : Fin n) :
    interiorBlock Q (originalClosureComplementaryEquiv P Q v hQ (.inr i)) =
      (interiorCuts P).card + 1 + interiorBlock P i := by
  classical
  let e := originalClosureComplementaryEquiv P Q v hQ
  rw [interiorBlock_eq_sum Q, ← e.sum_comp]
  rw [Fintype.sum_sum_type]
  have hup : (∑ k : Fin n, if e (.inl k) ∈ interiorCuts Q ∧ e (.inl k) ≤ e (.inr i)
      then 1 else 0) = (interiorCuts P).card := by
    have he : ∀ k : Fin n, e (.inl k) ≤ e (.inr i) := by
      intro k
      change k.val ≤ n + i.val
      have hk := k.isLt
      omega
    have hc : ∀ k : Fin n, e (.inl k) ∈ interiorCuts Q ↔ k ∈ interiorCuts P := by
      intro k
      exact originalHorizontalClosure_cut_upper P Q v hQ k
    simp_rw [hc, he, and_true]
    simp only [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter, Nat.cast_id]
  have hlo : (∑ k : Fin n, if e (.inr k) ∈ interiorCuts Q ∧ e (.inr k) ≤ e (.inr i)
      then 1 else 0) = 1 + interiorBlock P i := by
    have he : ∀ k : Fin n, e (.inr k) ≤ e (.inr i) ↔ k ≤ i := by
      intro k
      change n + k.val ≤ n + i.val ↔ k.val ≤ i.val
      omega
    have hc : ∀ k : Fin n, e (.inr k) ∈ interiorCuts Q ↔ k.val = 0 ∨
        k ∈ interiorCuts P := by
      intro k
      exact originalHorizontalClosure_cut_lower P Q v hQ k
    simp_rw [hc, he]
    have hs (k : Fin n) : (if (k.val = 0 ∨ k ∈ interiorCuts P) ∧ k ≤ i then 1 else 0 : ℕ) =
        (if k.val = 0 then 1 else 0) + (if k ∈ interiorCuts P ∧ k ≤ i then 1 else 0) := by
      by_cases hk : k.val = 0
      · have hc : k ∉ interiorCuts P := by
          intro hc
          have hp := (Finset.mem_filter.mp hc).2.1
          omega
        have hki : k ≤ i := by change k.val ≤ i.val; omega
        simp only [hk, hc, hki, true_or, true_and, ite_true, false_and, ite_false, add_zero]
      · simp only [hk, false_or, ite_false, zero_add]
    simp_rw [hs]
    rw [Finset.sum_add_distrib, ← interiorBlock_eq_sum]
    have hz : (∑ k : Fin n, if k.val = 0 then 1 else 0 : ℕ) = 1 := by
      let first : Fin n := ⟨0, by have hi := i.isLt; omega⟩
      have heq : ∀ k : Fin n, k.val = 0 ↔ k = first := by
        intro k
        exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
      simp_rw [heq]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [hz]
  change _ + _ = _
  rw [hup, hlo]
  omega

end SkewCornerDescent.Matrix
