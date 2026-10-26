/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewGluing.Diagram

/-!
# Literal period supplied by equal complete cell windows

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:actual-words`).

Complete window equality identifies actual cells across one displacement throughout
the overlap. Successive translations preserve membership whenever the final cell lies
inside the stated content support. No equality of Schur functions is used.

Sorry-free.
-/

namespace SkewCornerDescent

open SkewGluing

/-- Content is additive under an integral multiple of a cell displacement. -/
theorem content_add_zsmul (x v : ℤ × ℤ) (j : ℤ) :
    content (x + j • v) = content x + j * content v := by
  simp only [content, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]
  ring

/-- Complete equal windows identify one actual cell translation throughout their overlap. -/
theorem literalWindow_step {D : Diagram} {L q : ℤ} {v x : ℤ × ℤ}
    (hv : content v = q)
    (hwindow : D.filter (fun x => q ≤ content x ∧ content x < L) =
      translate v (D.filter fun x => 0 ≤ content x ∧ content x < L - q))
    (hx : 0 ≤ content x ∧ content x < L - q) :
    x + v ∈ D ↔ x ∈ D := by
  have hc := content_add x v
  have hupper : q ≤ content (x + v) ∧ content (x + v) < L := by
    rw [hc, hv]
    constructor <;> omega
  have he := congrArg (fun A : Diagram => x + v ∈ A) hwindow
  simpa only [Finset.mem_filter, mem_translate, add_sub_cancel_right,
    and_true, hupper, hx] using Iff.of_eq he

/-- Actual cell membership propagates to every translate still within the support. -/
theorem literalWindow_iterate {D : Diagram} {L q : ℤ} {v : ℤ × ℤ}
    (hq : 0 < q) (hv : content v = q)
    (hwindow : D.filter (fun x => q ≤ content x ∧ content x < L) =
      translate v (D.filter fun x => 0 ≤ content x ∧ content x < L - q))
    (x : ℤ × ℤ) (hx0 : 0 ≤ content x) (j : ℕ)
    (hfinal : content x + (j : ℤ) * q < L) :
    x + (j : ℤ) • v ∈ D ↔ x ∈ D := by
  induction j with
  | zero => simp only [Nat.cast_zero, zero_smul, add_zero]
  | succ j ih =>
    have hnonneg : (0 : ℤ) ≤ j := by exact_mod_cast Nat.zero_le j
    have hprev : content x + (j : ℤ) * q < L := by
      rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul] at hfinal
      nlinarith
    have hbound : 0 ≤ content (x + (j : ℤ) • v) ∧
        content (x + (j : ℤ) • v) < L - q := by
      rw [content_add_zsmul, hv]
      rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul] at hfinal
      constructor <;> nlinarith
    have he : x + ((j + 1 : ℕ) : ℤ) • v = (x + (j : ℤ) • v) + v := by
      rw [Nat.cast_add, Nat.cast_one, add_smul, one_smul]
      abel
    rw [he, literalWindow_step hv hwindow hbound, ih hprev]

/-- Every supported actual cell descends by the window translation to the first period band. -/
theorem literalWindow_cell_reconstruction {D : Diagram} {L q : ℤ} {v : ℤ × ℤ}
    (hq : 0 < q) (hv : content v = q)
    (hbound : ∀ x ∈ D, 0 ≤ content x ∧ content x < L)
    (hwindow : D.filter (fun x => q ≤ content x ∧ content x < L) =
      translate v (D.filter fun x => 0 ≤ content x ∧ content x < L - q)) :
    ∀ x ∈ D, ∃ j : ℕ, ∃ y ∈ D,
      0 ≤ content y ∧ content y < q ∧ x = y + (j : ℤ) • v := by
  have reconstruct : ∀ m : ℕ, ∀ x : ℤ × ℤ, (content x).toNat = m → x ∈ D →
      ∃ j : ℕ, ∃ y ∈ D, 0 ≤ content y ∧ content y < q ∧
        x = y + (j : ℤ) • v := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro x hm hx
      obtain ⟨hx0, hxL⟩ := hbound x hx
      by_cases hxq : content x < q
      · exact ⟨0, x, hx, hx0, hxq,
          by simp only [Nat.cast_zero, zero_smul, add_zero]⟩
      · let z := x - v
        have hzc : content z = content x - q := by
          simp only [z, content, Prod.fst_sub, Prod.snd_sub] at *
          linarith
        have hzb : 0 ≤ content z ∧ content z < L - q := by rw [hzc]; omega
        have hzx : z + v = x := sub_add_cancel x v
        have hzD : z ∈ D := (literalWindow_step hv hwindow hzb).mp (by rwa [hzx])
        have hless : (content z).toNat < m := by rw [← hm]; omega
        obtain ⟨j, y, hy, hy0, hyq, he⟩ := ih (content z).toNat hless z rfl hzD
        refine ⟨j + 1, y, hy, hy0, hyq, ?_⟩
        rw [← hzx, he, Nat.cast_add, Nat.cast_one, add_smul, one_smul]
        abel
  intro x hx
  exact reconstruct (content x).toNat x rfl hx

end SkewCornerDescent
