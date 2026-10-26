/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalClosureBlockLabels
import SkewCornerDescent.Matrix.InteriorBlockIntervals

/-!
# Complete original block intervals in the horizontal closure

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`). Every actual block
fiber stays in its complete source copy. Its first and last original indices are the
literal copies of the source endpoints. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- Actual complementary placement in either complete source copy; `true` is the upper copy. -/
def originalClosureComplementaryCopy {n m : ℕ} (P : Profile n) (Q : Profile m)
    (v : ℤ × ℤ) (hQ : originalHorizontalClosure P = translate v Q.cells)
    (upper : Bool) (i : Fin n) : Fin m :=
  originalClosureComplementaryEquiv P Q v hQ (if upper then .inl i else .inr i)

/-- Each literal source placement preserves the full original index order. -/
theorem originalHorizontalClosure_complementary_copy_strictMono {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (upper : Bool) :
    StrictMono (originalClosureComplementaryCopy P Q v hQ upper) := by
  intro i j hij
  cases upper with
  | true => exact hij
  | false =>
    change n + i.val < n + j.val
    have h := Fin.lt_def.mp hij
    omega

/-- The exact label of a copied original index includes only the produced copy offset. -/
theorem originalHorizontalClosure_complementary_copy_label {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (upper : Bool) (i : Fin n) :
    interiorBlock Q (originalClosureComplementaryCopy P Q v hQ upper i) =
      if upper then interiorBlock P i else (interiorCuts P).card + 1 + interiorBlock P i := by
  cases upper with
  | true => exact originalHorizontalClosure_block_upper P Q v hQ i
  | false => exact originalHorizontalClosure_block_lower P Q v hQ i

/-- An actual closure block contains exactly its complete source fiber, and no other-copy index. -/
theorem originalHorizontalClosure_block_fiber {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (upper : Bool) (i : Fin n)
    (q : Fin m) :
    interiorBlock Q q = interiorBlock Q (originalClosureComplementaryCopy P Q v hQ upper i) ↔
      ∃ j : Fin n, q = originalClosureComplementaryCopy P Q v hQ upper j ∧
        interiorBlock P j = interiorBlock P i := by
  constructor
  · intro h
    obtain ⟨s, rfl⟩ := (originalClosureComplementaryEquiv P Q v hQ).surjective q
    have hi : interiorBlock P i ≤ (interiorCuts P).card := Finset.card_filter_le _ _
    cases upper with
    | true =>
      rcases s with j | j
      · refine ⟨j, rfl, ?_⟩
        exact (originalHorizontalClosure_block_upper P Q v hQ j).symm.trans
          (h.trans (originalHorizontalClosure_block_upper P Q v hQ i))
      · have hj := originalHorizontalClosure_block_lower P Q v hQ j
        have he := originalHorizontalClosure_complementary_copy_label P Q v hQ true i
        simp only [ite_true] at he
        omega
    | false =>
      rcases s with j | j
      · have hj : interiorBlock P j ≤ (interiorCuts P).card := Finset.card_filter_le _ _
        have he := originalHorizontalClosure_complementary_copy_label P Q v hQ false i
        simp only [Bool.false_eq_true, ite_false] at he
        have hq := originalHorizontalClosure_block_upper P Q v hQ j
        omega
      · refine ⟨j, rfl, ?_⟩
        have hj := originalHorizontalClosure_block_lower P Q v hQ j
        have he := originalHorizontalClosure_complementary_copy_label P Q v hQ false i
        simp only [Bool.false_eq_true, ite_false] at he
        omega
  · rintro ⟨j, rfl, hj⟩
    rw [originalHorizontalClosure_complementary_copy_label,
      originalHorizontalClosure_complementary_copy_label, hj]

/-- The actual first complementary index is the literal copy of the source first index. -/
theorem originalHorizontalClosure_block_first {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (upper : Bool) (i : Fin n) :
    interiorBlockFirst Q (originalClosureComplementaryCopy P Q v hQ upper i) =
      originalClosureComplementaryCopy P Q v hQ upper (interiorBlockFirst P i) := by
  let copy := originalClosureComplementaryCopy P Q v hQ upper
  have hf := (mem_interiorBlockFiber P i _).mp (interiorBlockFirst_mem P i)
  have hc := (originalHorizontalClosure_block_fiber P Q v hQ upper i (copy _)).mpr
    ⟨interiorBlockFirst P i, rfl, hf⟩
  have hle := (mem_interiorBlockFiber_iff Q (copy i) _).mp
    ((mem_interiorBlockFiber Q (copy i) _).mpr hc)
  apply le_antisymm hle.1
  have hm := (mem_interiorBlockFiber Q (copy i) _).mp (interiorBlockFirst_mem Q (copy i))
  obtain ⟨j, hj, hji⟩ := (originalHorizontalClosure_block_fiber P Q v hQ upper i _).mp hm
  rw [hj]
  apply (originalHorizontalClosure_complementary_copy_strictMono P Q v hQ upper).monotone
  exact ((mem_interiorBlockFiber_iff P i j).mp
    ((mem_interiorBlockFiber P i j).mpr hji)).1

/-- The actual last complementary index is the literal copy of the source last index. -/
theorem originalHorizontalClosure_block_last {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (upper : Bool) (i : Fin n) :
    interiorBlockLast Q (originalClosureComplementaryCopy P Q v hQ upper i) =
      originalClosureComplementaryCopy P Q v hQ upper (interiorBlockLast P i) := by
  let copy := originalClosureComplementaryCopy P Q v hQ upper
  have hf := (mem_interiorBlockFiber P i _).mp (interiorBlockLast_mem P i)
  have hc := (originalHorizontalClosure_block_fiber P Q v hQ upper i (copy _)).mpr
    ⟨interiorBlockLast P i, rfl, hf⟩
  have hle := (mem_interiorBlockFiber_iff Q (copy i) _).mp
    ((mem_interiorBlockFiber Q (copy i) _).mpr hc)
  apply le_antisymm ?_ hle.2
  have hm := (mem_interiorBlockFiber Q (copy i) _).mp (interiorBlockLast_mem Q (copy i))
  obtain ⟨j, hj, hji⟩ := (originalHorizontalClosure_block_fiber P Q v hQ upper i _).mp hm
  rw [hj]
  apply (originalHorizontalClosure_complementary_copy_strictMono P Q v hQ upper).monotone
  exact ((mem_interiorBlockFiber_iff P i j).mp
    ((mem_interiorBlockFiber P i j).mpr hji)).2

/-- Every complete source block retains its exact size in either actual closure copy. -/
theorem originalHorizontalClosure_block_length {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (upper : Bool) (i : Fin n) :
    interiorBlockLength Q (originalClosureComplementaryCopy P Q v hQ upper i) =
      interiorBlockLength P i := by
  unfold interiorBlockLength
  rw [originalHorizontalClosure_block_first, originalHorizontalClosure_block_last]
  cases upper with
  | true => rfl
  | false =>
    change n + (interiorBlockLast P i).val - (n + (interiorBlockFirst P i).val) = _
    omega

end SkewCornerDescent.Matrix
