/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
-- TODO-COPIED: skew-boundary-reconstruction/lean/SkewSchurReconstruction/BoundaryOperations.lean
import SkewCofactorIndependence.Base.Diagrams

/-!
# First-row deletion and northeast extension

Diagrammatic boundary operations from "Capped cofactors and admissible convex weights"
(`sec:coordinates`, `lem:extension-cofactors`): deletion, positive northeast extension,
and the extended coordinate grids.  Empty parents extend to a single row.
Translation equivalence is preserved by both operations.  Sorry-free.
-/

namespace SkewCofactorIndependence.Base
namespace Diagram

variable {n m : ℕ}

/-- Delete the whole first row, including deletion of a single-row diagram. -/
def deleteFirstRow (X : Diagram (n + 1)) : Diagram n where
  outer i := X.outer i.succ
  inner i := X.inner i.succ
  outer_antitone := fun _ _ hij => X.outer_antitone (by
    change _ + 1 ≤ _ + 1
    exact Nat.add_le_add_right hij 1)
  inner_antitone := fun _ _ hij => X.inner_antitone (by
    change _ + 1 ≤ _ + 1
    exact Nat.add_le_add_right hij 1)
  row_nonempty i := X.row_nonempty i.succ

@[simp] theorem deleteFirstRow_outer (X : Diagram (n + 1)) (i : Fin n) :
    X.deleteFirstRow.outer i = X.outer i.succ := rfl

@[simp] theorem deleteFirstRow_inner (X : Diagram (n + 1)) (i : Fin n) :
    X.deleteFirstRow.inner i = X.inner i.succ := rfl

theorem top_pos (X : Diagram n) (hn : 0 < n) : 0 < X.top := by
  have h := X.row_nonempty ⟨0, hn⟩
  rw [top_of_pos X hn]
  omega

private theorem antitone_fin_cases {f : Fin n → ℕ} (hf : Antitone f)
    (a : ℕ) (ha : ∀ i, f i ≤ a) : Antitone (Fin.cases a f) := by
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · intro _
      simp
    · intro _
      simpa using ha j
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · intro hij
      change i.val + 1 ≤ 0 at hij
      omega
    · intro hij
      apply hf
      change i.val ≤ j.val
      change i.val + 1 ≤ j.val + 1 at hij
      omega

/-- The outer boundary of the new row; the empty-parent case is a row of length `k`. -/
def extensionTop (X : Diagram n) (k : ℕ) : ℕ :=
  if 0 < n then X.top + k - 1 else k

theorem extensionTop_eq (X : Diagram n) (k : ℕ) (hn : 0 < n) :
    X.extensionTop k = X.top + k - 1 := by
  simp [extensionTop, hn]

theorem outer_le_extensionTop (X : Diagram n) (k : ℕ) (hk : 0 < k)
    (i : Fin n) : X.outer i ≤ X.extensionTop k := by
  have hi := i.isLt
  have hn : 0 < n := by omega
  have h := X.outer_le_top i
  rw [extensionTop_eq X k hn]
  omega

theorem inner_le_extensionInner (X : Diagram n) (i : Fin n) :
    X.inner i ≤ X.top - 1 := by
  have h := X.row_nonempty i
  have ht := X.outer_le_top i
  omega

/-- Attach a positive row northeast of the old top row, with unit overlap. -/
def extendNortheast (X : Diagram n) (k : ℕ) (hk : 0 < k) : Diagram (n + 1) where
  outer := Fin.cases (X.extensionTop k) X.outer
  inner := Fin.cases (X.top - 1) X.inner
  outer_antitone := antitone_fin_cases X.outer_antitone _
    (X.outer_le_extensionTop k hk)
  inner_antitone := antitone_fin_cases X.inner_antitone _ X.inner_le_extensionInner
  row_nonempty := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · change X.top - 1 < X.extensionTop k
      by_cases hn : 0 < n
      · have ht := X.top_pos hn
        rw [extensionTop_eq X k hn]
        omega
      · have hn0 : n = 0 := by omega
        subst n
        simpa [extensionTop] using hk
    · exact X.row_nonempty i

@[simp] theorem extendNortheast_outer_zero (X : Diagram n) (k : ℕ) (hk : 0 < k) :
    (X.extendNortheast k hk).outer 0 = X.extensionTop k := rfl

@[simp] theorem extendNortheast_inner_zero (X : Diagram n) (k : ℕ) (hk : 0 < k) :
    (X.extendNortheast k hk).inner 0 = X.top - 1 := rfl

@[simp] theorem extendNortheast_outer_succ (X : Diagram n) (k : ℕ) (hk : 0 < k)
    (i : Fin n) : (X.extendNortheast k hk).outer i.succ = X.outer i := rfl

@[simp] theorem extendNortheast_inner_succ (X : Diagram n) (k : ℕ) (hk : 0 < k)
    (i : Fin n) : (X.extendNortheast k hk).inner i.succ = X.inner i := rfl

theorem extendNortheast_top (X : Diagram n) (k : ℕ) (hk : 0 < k) :
    (X.extendNortheast k hk).top = X.extensionTop k := by
  rw [top_of_pos _ (Nat.succ_pos n)]
  rfl

@[simp] theorem deleteFirstRow_extendNortheast (X : Diagram n) (k : ℕ) (hk : 0 < k) :
    (X.extendNortheast k hk).deleteFirstRow = X := by
  cases X
  rfl

theorem extendNortheast_rowLength_zero (X : Diagram n) (k : ℕ) (hk : 0 < k) :
    (X.extendNortheast k hk).rowLength 0 = k := by
  change X.extensionTop k - (X.top - 1) = k
  by_cases hn : 0 < n
  · have ht := X.top_pos hn
    rw [extensionTop_eq X k hn]
    omega
  · have hn0 : n = 0 := by omega
    subst n
    simp [extensionTop]

theorem extendNortheast_overlap_zero (X : Diagram n) (k : ℕ) (hk : 0 < k)
    (hn : 0 < n) :
    (X.extendNortheast k hk).overlap 0 (by change 0 + 1 < n + 1; omega) = 1 := by
  have ht := X.top_pos hn
  change (X.outer ⟨0, hn⟩ : ℤ) - (X.top - 1 : ℕ) = 1
  rw [← top_of_pos X hn]
  omega

theorem extendNortheast_connected (X : Diagram n) (k : ℕ) (hk : 0 < k)
    (hX : X.Connected) : (X.extendNortheast k hk).Connected := by
  refine ⟨Nat.succ_pos n, ?_⟩
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · intro hi
    change X.top - 1 < X.outer ⟨0, by omega⟩
    rw [← top_of_pos X hX.1]
    have ht := X.top_pos hX.1
    omega
  · intro hi
    have hn : i.val + 1 < n := by
      change i.val + 1 + 1 < n + 1 at hi
      omega
    change X.inner i < X.outer ⟨i.val + 1, hn⟩
    exact hX.2 i hn

/-- The empty parent is not connected, but its positive extension is. -/
theorem extendNortheast_empty_connected (X : Diagram 0) (k : ℕ) (hk : 0 < k) :
    (X.extendNortheast k hk).Connected := by
  refine ⟨by omega, ?_⟩
  intro i hi
  have h := i.isLt
  omega

/-- Row grid of the extension: `(0, k + A₀, …)`. -/
theorem extendNortheast_rowParam_succ (X : Diagram n) (k : ℕ) (hk : 0 < k)
    (i : Fin n) :
    (X.extendNortheast k hk).rowParam i.succ = (k : ℤ) + X.rowParam i := by
  have hi := i.isLt
  have hn : 0 < n := by omega
  have ht := X.top_pos hn
  simp only [rowParam, extendNortheast_top, extendNortheast_outer_succ, Fin.val_succ]
  rw [extensionTop_eq X k hn]
  omega

theorem extendNortheast_rowParam_zero (X : Diagram n) (k : ℕ) (hk : 0 < k) :
    (X.extendNortheast k hk).rowParam 0 = 0 := by
  exact rowParam_zero _ (Nat.succ_pos n)

/-- The first positive cap shift of a northeast extension is its row length. -/
theorem extendNortheast_capShift_one (X : Diagram n) (k : ℕ) (hk : 0 < k) :
    (X.extendNortheast k hk).capShift (0 : Fin (n + 1)).succ = k := by
  rw [capShift_succ]
  simp only [extendNortheast_top, extendNortheast_inner_zero, Fin.val_zero, Nat.cast_zero,
    add_zero]
  by_cases hn : 0 < n
  · have ht := X.top_pos hn
    rw [extensionTop_eq X k hn]
    omega
  · have hn0 : n = 0 := by omega
    subst n
    simp [extensionTop]

/-- Remaining positive cap shifts are the old positive shifts increased by `k`. -/
theorem extendNortheast_capShift_succ_succ (X : Diagram n) (k : ℕ) (hk : 0 < k)
    (i : Fin n) :
    (X.extendNortheast k hk).capShift i.succ.succ = (k : ℤ) + X.capShift i.succ := by
  have hi := i.isLt
  have hn : 0 < n := by omega
  have ht := X.top_pos hn
  rw [capShift_succ, capShift_succ]
  simp only [extendNortheast_top, extendNortheast_inner_succ, Fin.val_succ]
  rw [extensionTop_eq X k hn]
  omega

theorem extendNortheast_capShift_zero (X : Diagram n) (k : ℕ) (hk : 0 < k) :
    (X.extendNortheast k hk).capShift 0 = 0 := capShift_zero _

end Diagram

namespace TranslationEquivalent

variable {n m : ℕ}

/-- Deleting corresponding first rows preserves translation equivalence. -/
theorem deleteFirstRow {X : Diagram (n + 1)} {Y : Diagram (m + 1)}
    (h : TranslationEquivalent X Y) :
    TranslationEquivalent X.deleteFirstRow Y.deleteFirstRow := by
  rcases h with ⟨hn, t, ht⟩
  refine ⟨by omega, t, ?_⟩
  intro i j hij
  exact ht i.succ j.succ (by simpa using congrArg (fun a : ℕ => a + 1) hij)

/-- Attaching equal positive rows preserves translation equivalence. -/
theorem extendNortheast {X : Diagram n} {Y : Diagram m}
    (h : TranslationEquivalent X Y) (k : ℕ) (hk : 0 < k) :
    TranslationEquivalent (X.extendNortheast k hk) (Y.extendNortheast k hk) := by
  rcases h with ⟨hn, t, ht⟩
  subst m
  by_cases hn : 0 < n
  · have hx := X.top_pos hn
    have hy := Y.top_pos hn
    have htop := (ht ⟨0, hn⟩ ⟨0, hn⟩ rfl).1
    rw [← X.top_of_pos hn, ← Y.top_of_pos hn] at htop
    refine ⟨rfl, t, ?_⟩
    intro i j hij
    have heq : i = j := Fin.ext hij
    subst j
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [Diagram.extendNortheast_outer_zero, Diagram.extendNortheast_inner_zero]
      rw [X.extensionTop_eq k hn, Y.extensionTop_eq k hn]
      constructor <;> omega
    · simpa only [Diagram.extendNortheast_outer_succ, Diagram.extendNortheast_inner_succ]
        using ht i i rfl
  · have hn0 : n = 0 := by omega
    subst n
    refine ⟨rfl, 0, ?_⟩
    intro i j hij
    have heq : i = j := Fin.ext hij
    subst j
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [Diagram.extensionTop]
    · exact Fin.elim0 i

end TranslationEquivalent
end SkewCofactorIndependence.Base
