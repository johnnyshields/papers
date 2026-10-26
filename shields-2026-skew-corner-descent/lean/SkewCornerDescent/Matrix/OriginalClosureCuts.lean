/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalClosureMatrix

/-!
# Literal block cuts of the horizontal closure

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`). The actual lower
adjacent original entries reproduce every source cut in each copy, with one additional
cut at their common row. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- The upper copy's actual preceding complementary index is the source predecessor. -/
theorem originalHorizontalClosure_previous_upper {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (i : Fin n) :
    previousIndex (originalClosureComplementaryEquiv P Q v hQ (.inl i)) =
      originalClosureComplementaryEquiv P Q v hQ (.inl (previousIndex i)) := by
  apply Fin.ext
  rfl

/-- Every positive lower-copy index has its actual predecessor in the same complete copy. -/
theorem originalHorizontalClosure_previous_lower {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (i : Fin n) (hi : 0 < i.val) :
    previousIndex (originalClosureComplementaryEquiv P Q v hQ (.inr i)) =
      originalClosureComplementaryEquiv P Q v hQ (.inr (previousIndex i)) := by
  apply Fin.ext
  change n + i.val - 1 = n + (i.val - 1)
  omega

/-- The upper copy has precisely the source cuts, including the absence of a cut at zero. -/
theorem originalHorizontalClosure_cut_upper {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (i : Fin n) :
    originalClosureComplementaryEquiv P Q v hQ (.inl i) ∈ interiorCuts Q ↔
      i ∈ interiorCuts P := by
  simp only [interiorCuts, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [originalHorizontalClosure_previous_upper P Q v hQ,
    originalHorizontalClosure_complementary_xi_upper P Q v hQ,
    originalHorizontalClosure_complementary_zeta_upper P Q v hQ]
  change (0 < i.val ∧ _ < _) ↔ (0 < i.val ∧ _ < _)
  omega

/-- At every positive index the lower copy has precisely the source cut. -/
theorem originalHorizontalClosure_cut_lower_positive {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (i : Fin n) (hi : 0 < i.val) :
    originalClosureComplementaryEquiv P Q v hQ (.inr i) ∈ interiorCuts Q ↔
      i ∈ interiorCuts P := by
  simp only [interiorCuts, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [originalHorizontalClosure_previous_lower P Q v hQ i hi,
    originalHorizontalClosure_complementary_xi_lower P Q v hQ,
    originalHorizontalClosure_complementary_zeta_lower P Q v hQ]
  change (0 < n + i.val ∧ _ < _) ↔ (0 < i.val ∧ _ < _)
  omega

/-- The two complete source copies are separated by a genuine additional original cut. -/
theorem originalHorizontalClosure_cut_central {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (hn : 0 < n) :
    originalClosureComplementaryEquiv P Q v hQ (.inr ⟨0, hn⟩) ∈ interiorCuts Q := by
  let first : Fin n := ⟨0, hn⟩
  let last : Fin n := ⟨n - 1, by omega⟩
  have hp : previousIndex (originalClosureComplementaryEquiv P Q v hQ (.inr first)) =
      originalClosureComplementaryEquiv P Q v hQ (.inl last) := by
    apply Fin.ext
    change n + 0 - 1 = n - 1
    omega
  simp only [interiorCuts, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨?_, ?_⟩
  · change 0 < n + 0
    omega
  · rw [hp, originalHorizontalClosure_complementary_xi_lower P Q v hQ,
      originalHorizontalClosure_complementary_zeta_upper P Q v hQ]
    have hr := P.xi_strictAnti (show (0 : Fin (n + 1)) < first.succ by
      change 0 < 0 + 1; omega)
    have hc := P.zeta_nonneg last.castSucc
    change P.xi first.succ < P.zeta last.castSucc + P.xi 0
    omega

/-- The entire actual lower cut list is the source list plus its genuine central cut. -/
theorem originalHorizontalClosure_cut_lower {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (i : Fin n) :
    originalClosureComplementaryEquiv P Q v hQ (.inr i) ∈ interiorCuts Q ↔
      i.val = 0 ∨ i ∈ interiorCuts P := by
  by_cases hi : i.val = 0
  · have he : i = ⟨0, by have := i.isLt; omega⟩ := Fin.ext hi
    rw [he]
    exact iff_of_true (originalHorizontalClosure_cut_central P Q v hQ (by omega)) (Or.inl rfl)
  · rw [originalHorizontalClosure_cut_lower_positive P Q v hQ i (by omega)]
    exact (or_iff_right hi).symm

end SkewCornerDescent.Matrix
