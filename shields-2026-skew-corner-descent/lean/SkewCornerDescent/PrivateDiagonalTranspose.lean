/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.ProfileTransposeWindows

/-!
# Actual private diagonals under normalized whole-diagram transpose

Supports `shields-2026-skew-corner-descent.tex` (`cor:row-pencil`).
Equality of the diagonal extremes means that its actual cells are unique.
This criterion transports under transposition and translation, including empty
diagonals. Sorry-free.
-/

namespace SkewCornerDescent

open SkewGluing

/-- Equality of actual diagonal extremes is equivalent to uniqueness of all
cells on that diagonal, with the empty diagonal included. -/
theorem private_diagonal_iff_unique (D : Diagram) (k : ℤ) :
    diagLo D k = diagHi D k ↔
      ∀ x ∈ D, ∀ y ∈ D, content x = k → content y = k → x = y := by
  constructor
  · intro he x hx y hy hxc hyc
    rcases x with ⟨i, j⟩
    rcases y with ⟨r, s⟩
    have h1 := diagLo_le hx hxc
    have h2 := le_diagHi hx hxc
    have h3 := diagLo_le hy hyc
    have h4 := le_diagHi hy hyc
    simp only [content] at hxc hyc
    apply Prod.ext <;> dsimp <;> omega
  · intro hu
    by_cases hk : k ∈ contents D
    · have he := hu _ (diagLo_mem hk) _ (diagHi_mem hk)
        (by simp only [content]; ring) (by simp only [content]; ring)
      exact congrArg Prod.fst he
    · have hne : ¬ (diagRows D k).Nonempty := fun h => hk (mem_contents.mpr h)
      simp only [diagLo, diagHi, dite_eq_right hne]

/-- A private diagonal remains private after transposing the entire diagram. -/
theorem private_diagonal_transpose (D : Diagram) (k : ℤ) :
    diagLo (transpose D) (-k) = diagHi (transpose D) (-k) ↔ diagLo D k = diagHi D k := by
  rw [private_diagonal_iff_unique, private_diagonal_iff_unique]
  constructor
  · intro hu x hx y hy hxc hyc
    have hx' : x.swap ∈ transpose D := by simpa only [mem_transpose, Prod.swap_swap] using hx
    have hy' : y.swap ∈ transpose D := by simpa only [mem_transpose, Prod.swap_swap] using hy
    have cx : content x.swap = -k := by
      simp only [content, Prod.fst_swap, Prod.snd_swap] at hxc ⊢
      omega
    have cy : content y.swap = -k := by
      simp only [content, Prod.fst_swap, Prod.snd_swap] at hyc ⊢
      omega
    have he := congrArg Prod.swap (hu _ hx' _ hy' cx cy)
    simpa only [Prod.swap_swap] using he
  · intro hu x hx y hy hxc hyc
    have hx' := mem_transpose.mp hx
    have hy' := mem_transpose.mp hy
    have cx : content x.swap = k := by
      simp only [content, Prod.fst_swap, Prod.snd_swap] at hxc ⊢
      omega
    have cy : content y.swap = k := by
      simp only [content, Prod.fst_swap, Prod.snd_swap] at hyc ⊢
      omega
    have he := congrArg Prod.swap (hu _ hx' _ hy' cx cy)
    simpa only [Prod.swap_swap] using he

/-- Translation moves a private diagonal by exactly the translation's content. -/
theorem private_diagonal_translate (D : Diagram) (a : ℤ × ℤ) (k : ℤ) :
    diagLo (translate a D) (k + content a) = diagHi (translate a D) (k + content a) ↔
      diagLo D k = diagHi D k := by
  rw [private_diagonal_iff_unique, private_diagonal_iff_unique]
  constructor
  · intro hu x hx y hy hxc hyc
    have hx' : x + a ∈ translate a D := mem_translate.mpr (by simpa using hx)
    have hy' : y + a ∈ translate a D := mem_translate.mpr (by simpa using hy)
    have cx : content (x + a) = k + content a := by
      simp only [content, Prod.fst_add, Prod.snd_add] at hxc ⊢
      omega
    have cy : content (y + a) = k + content a := by
      simp only [content, Prod.fst_add, Prod.snd_add] at hyc ⊢
      omega
    exact add_right_cancel (hu _ hx' _ hy' cx cy)
  · intro hu x hx y hy hxc hyc
    have hx' := mem_translate.mp hx
    have hy' := mem_translate.mp hy
    have cx : content (x - a) = k := by
      simp only [content, Prod.fst_sub, Prod.snd_sub] at hxc ⊢
      omega
    have cy : content (y - a) = k := by
      simp only [content, Prod.fst_sub, Prod.snd_sub] at hyc ⊢
      omega
    have he := congrArg (fun z : ℤ × ℤ => z + a) (hu _ hx' _ hy' cx cy)
    simpa only [sub_add_cancel] using he

/-- The actual normalizing translation supplies the reflected private cut
index of every whole transposed profile. -/
theorem private_diagonal_transpose_profile {n m : ℕ} (P : Profile n) (T : Profile m)
    (a : ℤ × ℤ) (ha : transpose P.cells = translate a T.cells) (k : ℤ) :
    diagLo T.cells (P.xi 0 - 1 - k) = diagHi T.cells (P.xi 0 - 1 - k) ↔
      diagLo P.cells k = diagHi P.cells k := by
  have hc := (transpose_profile_endpoints P T a ha).2
  have he : P.xi 0 - 1 - k + content a = -k := by omega
  have h := private_diagonal_translate T.cells a (P.xi 0 - 1 - k)
  rw [he, ← ha, private_diagonal_transpose] at h
  exact h.symm

/-- The adjacent private diagonals of the original ordinary full cuts supply
the two required private cut diagonals on the actual transposed profile. -/
theorem complete_transpose_private_cuts {n m : ℕ} (P : Profile n) (T : Profile m)
    (a : ℤ × ℤ) (ha : transpose P.cells = translate a T.cells) (q : ℤ)
    (hq : diagLo P.cells (q - 1) = diagHi P.cells (q - 1))
    (hLq : diagLo P.cells (P.xi 0 - q - 1) =
      diagHi P.cells (P.xi 0 - q - 1)) :
    diagLo T.cells q = diagHi T.cells q ∧
      diagLo T.cells (T.xi 0 - q) = diagHi T.cells (T.xi 0 - q) := by
  have hxi := (transpose_profile_endpoints P T a ha).1
  constructor
  · have h := (private_diagonal_transpose_profile P T a ha (P.xi 0 - q - 1)).mpr hLq
    have he : P.xi 0 - 1 - (P.xi 0 - q - 1) = q := by omega
    simpa only [he] using h
  · have h := (private_diagonal_transpose_profile P T a ha (q - 1)).mpr hq
    have he : P.xi 0 - 1 - (q - 1) = T.xi 0 - q := by omega
    simpa only [he] using h

end SkewCornerDescent
