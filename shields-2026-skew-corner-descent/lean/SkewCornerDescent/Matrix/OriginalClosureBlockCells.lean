/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalClosureBlockDeterminants
import SkewCornerDescent.Matrix.InteriorBlockComponents

/-!
# Literal cells of every copied original block

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`). Each complete
original complementary block is an actual translated source block. This identity
includes empty and unselected blocks, not only selected function classes. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- Source-copy displacement in the normalized actual closure profile. -/
def originalClosureBlockDisplacement {n : ℕ} (P : Profile n) (upper : Bool) : ℤ × ℤ :=
  if upper then (0, P.xi 0) else (n, n)

/-- All original coordinates obey one actual affine copy displacement. -/
theorem originalHorizontalClosure_copy_coordinates {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (upper : Bool) (i : Fin n) :
    let w := originalClosureBlockDisplacement P upper
    let q := originalClosureComplementaryCopy P Q v hQ upper i
    (q : ℤ) = (i : ℤ) + w.1 ∧
      Q.xi q.succ = P.xi i.succ + w.2 - w.1 ∧
      Q.zeta q.castSucc = P.zeta i.castSucc + w.2 - w.1 := by
  cases upper with
  | true =>
    refine ⟨?_, ?_, ?_⟩
    · change (i : ℤ) = (i : ℤ) + 0
      omega
    · change Q.xi (originalClosureComplementaryEquiv P Q v hQ (.inl i)).succ =
        P.xi i.succ + P.xi 0 - 0
      simpa only [sub_zero] using originalHorizontalClosure_complementary_xi_upper P Q v hQ i
    · change Q.zeta (originalClosureComplementaryEquiv P Q v hQ (.inl i)).castSucc =
        P.zeta i.castSucc + P.xi 0 - 0
      simpa only [sub_zero] using originalHorizontalClosure_complementary_zeta_upper P Q v hQ i
  | false =>
    refine ⟨?_, ?_, ?_⟩
    · change ((n + i.val : ℕ) : ℤ) = (i : ℤ) + n
      rw [Nat.cast_add]
      omega
    · change Q.xi (originalClosureComplementaryEquiv P Q v hQ (.inr i)).succ =
        P.xi i.succ + n - n
      simpa only [add_sub_cancel_right] using
        originalHorizontalClosure_complementary_xi_lower P Q v hQ i
    · change Q.zeta (originalClosureComplementaryEquiv P Q v hQ (.inr i)).castSucc =
        P.zeta i.castSucc + n - n
      simpa only [add_sub_cancel_right] using
        originalHorizontalClosure_complementary_zeta_lower P Q v hQ i

/-- Every full copied original block agrees as literal cells, before any class identification. -/
theorem originalHorizontalClosure_block_cells {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (upper : Bool) (i : Fin n) :
    interiorBlockCells Q (originalClosureComplementaryCopy P Q v hQ upper i) =
      translate (originalClosureBlockDisplacement P upper) (interiorBlockCells P i) := by
  let w := originalClosureBlockDisplacement P upper
  ext ⟨r, b⟩
  rw [mem_interiorBlockCells, mem_translate]
  change _ ↔ (r - w.1, b - w.2) ∈ interiorBlockCells P i
  rw [mem_interiorBlockCells]
  constructor
  · rintro ⟨q, hq, hr, hlo, hhi⟩
    obtain ⟨j, hj, hji⟩ := (originalHorizontalClosure_block_fiber P Q v hQ upper i q).mp hq
    rw [hj] at hr hlo hhi
    obtain ⟨hv, hx, hz⟩ := originalHorizontalClosure_copy_coordinates P Q v hQ upper j
    change ((originalClosureComplementaryCopy P Q v hQ upper j) : ℤ) = (j : ℤ) + w.1 at hv
    change Q.xi (originalClosureComplementaryCopy P Q v hQ upper j).succ =
      P.xi j.succ + w.2 - w.1 at hx
    change Q.zeta (originalClosureComplementaryCopy P Q v hQ upper j).castSucc =
      P.zeta j.castSucc + w.2 - w.1 at hz
    refine ⟨j, hji, ?_, ?_, ?_⟩ <;> omega
  · rintro ⟨j, hj, hr, hlo, hhi⟩
    let q := originalClosureComplementaryCopy P Q v hQ upper j
    have hq := (originalHorizontalClosure_block_fiber P Q v hQ upper i q).mpr ⟨j, rfl, hj⟩
    obtain ⟨hv, hx, hz⟩ := originalHorizontalClosure_copy_coordinates P Q v hQ upper j
    change (q : ℤ) = (j : ℤ) + w.1 at hv
    change Q.xi q.succ = P.xi j.succ + w.2 - w.1 at hx
    change Q.zeta q.castSucc = P.zeta j.castSucc + w.2 - w.1 at hz
    refine ⟨q, hq, ?_, ?_, ?_⟩ <;> omega

end SkewCornerDescent.Matrix
