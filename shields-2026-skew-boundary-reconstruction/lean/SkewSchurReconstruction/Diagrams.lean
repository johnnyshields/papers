/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic

/-!
# Skew diagram coordinates

Formalizes the diagram coordinates in "Capped cofactors and admissible convex weights"
(`sec:coordinates`, `eq:Adef`, `eq:dexplicit`) and the grid lemmas in
"Strict-Monge geometry of cofactor actions" (`sec:geometry`, `lem:grid-order`,
`lem:diagonal-feasible`).  Row lengths and signed adjacent overlaps recover the
boundaries up to translation.  Empty diagrams are allowed.  Sorry-free.
-/

namespace SkewSchurReconstruction

/-- Two partition boundaries with no empty rows. -/
structure Diagram (n : ℕ) where
  /-- The outer partition boundary, in row order. -/
  outer : Fin n → ℕ
  /-- The inner partition boundary removed from the outer shape. -/
  inner : Fin n → ℕ
  outer_antitone : Antitone outer
  inner_antitone : Antitone inner
  row_nonempty : ∀ i, inner i < outer i

namespace Diagram

variable {n m l : ℕ}

/-- The first outer boundary, or zero for the empty diagram. -/
def top (X : Diagram n) : ℕ :=
  if hn : 0 < n then X.outer ⟨0, hn⟩ else 0

/-- The normalized row coordinate in `eq:Adef`. -/
def rowParam (X : Diagram n) (i : Fin n) : ℤ :=
  (X.top : ℤ) - X.outer i + i.val

/-- The normalized capped column coordinate in `eq:dexplicit`. -/
def capShift (X : Diagram n) (j : Fin (n + 1)) : ℤ :=
  if hj : j.val = 0 then 0
  else (X.top : ℤ) - X.inner ⟨j.val - 1, by omega⟩ + j.val - 1

/-- Adjacent nonempty rows share a column. -/
def Connected (X : Diagram n) : Prop :=
  0 < n ∧ ∀ i : Fin n, ∀ hi : i.val + 1 < n,
    X.inner i < X.outer ⟨i.val + 1, hi⟩

/-- The number of cells in a row. -/
def rowLength (X : Diagram n) (i : Fin n) : ℕ := X.outer i - X.inner i

/-- Signed adjacent overlap; unlike natural subtraction this retains a negative gap. -/
def overlap (X : Diagram n) (i : Fin n) (hi : i.val + 1 < n) : ℤ :=
  (X.outer ⟨i.val + 1, hi⟩ : ℤ) - X.inner i

@[simp] theorem top_of_pos (X : Diagram n) (hn : 0 < n) :
    X.top = X.outer ⟨0, hn⟩ := by
  simp [top, hn]

@[simp] theorem top_empty (X : Diagram 0) : X.top = 0 := by
  simp [top]

theorem outer_le_top (X : Diagram n) (i : Fin n) : X.outer i ≤ X.top := by
  have hi := i.isLt
  have hn : 0 < n := by omega
  rw [top_of_pos X hn]
  exact X.outer_antitone (show (⟨0, hn⟩ : Fin n) ≤ i from by
    change 0 ≤ i.val
    exact Nat.zero_le _)

@[simp] theorem rowParam_zero (X : Diagram n) (hn : 0 < n) :
    X.rowParam ⟨0, hn⟩ = 0 := by
  simp [rowParam, top_of_pos X hn]

@[simp] theorem capShift_zero (X : Diagram n) : X.capShift 0 = 0 := by
  simp [capShift]

@[simp] theorem capShift_succ (X : Diagram n) (i : Fin n) :
    X.capShift i.succ = (X.top : ℤ) - X.inner i + i.val := by
  simp [capShift, Fin.val_succ]
  omega

/-- Strict order of the row grid in `lem:grid-order`. -/
theorem rowParam_strictMono (X : Diagram n) : StrictMono X.rowParam := by
  intro i j hij
  have hout := X.outer_antitone (le_of_lt hij)
  have hval : i.val < j.val := hij
  dsimp [rowParam]
  omega

theorem rowParam_nonneg (X : Diagram n) (i : Fin n) : 0 ≤ X.rowParam i := by
  have hout := X.outer_le_top i
  dsimp [rowParam]
  omega

theorem capShift_succ_pos (X : Diagram n) (i : Fin n) : 0 < X.capShift i.succ := by
  have hout := X.outer_le_top i
  have hrow := X.row_nonempty i
  rw [capShift_succ]
  omega

/-- Strict order of the cap grid in `lem:grid-order`. -/
theorem capShift_strictMono (X : Diagram n) : StrictMono X.capShift := by
  intro j k hjk
  have hval : j.val < k.val := hjk
  have hk : k.val ≠ 0 := by omega
  by_cases hj : j.val = 0
  · have hp : k.val - 1 < n := by omega
    have hout := X.outer_le_top ⟨k.val - 1, hp⟩
    have hrow := X.row_nonempty ⟨k.val - 1, hp⟩
    simp only [capShift, dite_eq_left hj, dite_eq_right hk]
    omega
  · have hpj : j.val - 1 < n := by omega
    have hpk : k.val - 1 < n := by omega
    have hinner := X.inner_antitone
      (show (⟨j.val - 1, hpj⟩ : Fin n) ≤ ⟨k.val - 1, hpk⟩ from by
        change j.val - 1 ≤ k.val - 1
        omega)
    simp only [capShift, dite_eq_right hj, dite_eq_right hk]
    omega

theorem capShift_nonneg (X : Diagram n) (j : Fin (n + 1)) :
    0 ≤ X.capShift j := by
  have h := X.capShift_strictMono.monotone (show (0 : Fin (n + 1)) ≤ j by simp)
  simpa using h

/-- Connectedness gives the diagonal matching inequality `lem:diagonal-feasible`. -/
theorem diagonal_feasible (X : Diagram n) (hX : X.Connected) (i : Fin n) :
    X.rowParam i ≤ X.capShift i.castSucc := by
  by_cases hi : i.val = 0
  · have heq : i = ⟨0, hX.1⟩ := Fin.ext hi
    subst i
    simp [rowParam, capShift, top_of_pos X hX.1]
  · have hp : i.val - 1 < n := by omega
    have hn : (i.val - 1) + 1 < n := by omega
    have hc := hX.2 ⟨i.val - 1, hp⟩ hn
    have heq : (⟨(i.val - 1) + 1, hn⟩ : Fin n) = i := by
      apply Fin.ext
      change i.val - 1 + 1 = i.val
      omega
    rw [heq] at hc
    simp only [rowParam, capShift, Fin.val_castSucc, dite_eq_right hi]
    omega

theorem rowLength_pos (X : Diagram n) (i : Fin n) : 0 < X.rowLength i := by
  have h := X.row_nonempty i
  dsimp [rowLength]
  omega

/-- Ordered nonempty row lengths, independent of any polynomial observation. -/
def rowLengthList (X : Diagram n) : List ℕ := List.ofFn X.rowLength

theorem rowLengthList_pos (X : Diagram n) : ∀ k ∈ X.rowLengthList, 0 < k := by
  intro k hk
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hk
  exact X.rowLength_pos i

/-- Row length as a nontruncated difference of coordinates. -/
theorem rowLength_eq_coordinates (X : Diagram n) (i : Fin n) :
    (X.rowLength i : ℤ) = X.capShift i.succ - X.rowParam i := by
  have h := X.row_nonempty i
  rw [capShift_succ]
  dsimp [rowLength, rowParam]
  omega

theorem overlap_pos (X : Diagram n) (hX : X.Connected) (i : Fin n)
    (hi : i.val + 1 < n) : 0 < X.overlap i hi := by
  have h := hX.2 i hi
  dsimp [overlap]
  omega

/-- The shifted diagonal entry is adjacent overlap less one. -/
theorem overlap_eq_coordinates (X : Diagram n) (i : Fin n)
    (hi : i.val + 1 < n) :
    X.overlap i hi - 1 = X.capShift i.succ - X.rowParam ⟨i.val + 1, hi⟩ := by
  rw [capShift_succ]
  dsimp [overlap, rowParam]
  omega

end Diagram

variable {n m : ℕ}

/-- Equality of both boundaries after a single integral translation. -/
def TranslationEquivalent (X : Diagram n) (Y : Diagram m) : Prop :=
  n = m ∧ ∃ t : ℤ, ∀ (i : Fin n) (j : Fin m), i.val = j.val →
    (X.outer i : ℤ) = (Y.outer j : ℤ) + t ∧
    (X.inner i : ℤ) = (Y.inner j : ℤ) + t

namespace TranslationEquivalent

variable {n m l : ℕ}

theorem refl (X : Diagram n) : TranslationEquivalent X X := by
  refine ⟨rfl, 0, ?_⟩
  intro i j hij
  have heq : i = j := Fin.ext hij
  subst j
  simp

theorem symm {X : Diagram n} {Y : Diagram m} (h : TranslationEquivalent X Y) :
    TranslationEquivalent Y X := by
  rcases h with ⟨hn, t, ht⟩
  refine ⟨hn.symm, -t, ?_⟩
  intro j i hij
  obtain ⟨ho, hi⟩ := ht i j hij.symm
  constructor <;> omega

theorem trans {X : Diagram n} {Y : Diagram m} {Z : Diagram l}
    (hXY : TranslationEquivalent X Y) (hYZ : TranslationEquivalent Y Z) :
    TranslationEquivalent X Z := by
  rcases hXY with ⟨hn, t, ht⟩
  rcases hYZ with ⟨hm, u, hu⟩
  refine ⟨hn.trans hm, t + u, ?_⟩
  intro i k hik
  let j : Fin m := ⟨i.val, by omega⟩
  obtain ⟨ho₁, hi₁⟩ := ht i j rfl
  obtain ⟨ho₂, hi₂⟩ := hu j k hik
  constructor <;> omega

/-- Equivalence relation on diagrams with a fixed number of rows. -/
theorem equivalence (n : ℕ) : Equivalence (@TranslationEquivalent n n) :=
  ⟨refl, fun h => symm h, fun h₁ h₂ => trans h₁ h₂⟩

end TranslationEquivalent

namespace Diagram

variable {n : ℕ}

/-- Equal normalized row and cap grids identify the boundaries up to translation. -/
theorem translationEquivalent_of_coordinates (X Y : Diagram n)
    (hrow : ∀ i, X.rowParam i = Y.rowParam i)
    (hcap : ∀ j, X.capShift j = Y.capShift j) : TranslationEquivalent X Y := by
  refine ⟨rfl, (X.top : ℤ) - Y.top, ?_⟩
  intro i j hij
  have heq : i = j := Fin.ext hij
  subst j
  have hr := hrow i
  have hc := hcap i.succ
  rw [capShift_succ, capShift_succ] at hc
  dsimp [rowParam] at hr
  constructor <;> omega

/-- Ordered row lengths and signed adjacent overlaps recover a diagram up to translation.
Connected diagrams have positive overlaps, but the recovery also applies to diagrams with gaps. -/
theorem translationEquivalent_of_rowLength_overlap (X Y : Diagram n)
    (hlen : ∀ i, X.rowLength i = Y.rowLength i)
    (hover : ∀ (i : Fin n) (hi : i.val + 1 < n), X.overlap i hi = Y.overlap i hi) :
    TranslationEquivalent X Y := by
  by_cases hn : 0 < n
  · let t : ℤ := (X.outer ⟨0, hn⟩ : ℤ) - Y.outer ⟨0, hn⟩
    have recover : ∀ k : ℕ, ∀ i : Fin n, i.val = k →
        (X.outer i : ℤ) = (Y.outer i : ℤ) + t ∧
        (X.inner i : ℤ) = (Y.inner i : ℤ) + t := by
      intro k
      induction k with
      | zero =>
        intro i hi
        have heq : i = ⟨0, hn⟩ := Fin.ext hi
        subst i
        have hl := hlen ⟨0, hn⟩
        have hx := X.row_nonempty ⟨0, hn⟩
        have hy := Y.row_nonempty ⟨0, hn⟩
        dsimp [rowLength] at hl
        dsimp [t]
        constructor <;> omega
      | succ k ih =>
        intro i hi
        have hk : k < n := by omega
        let p : Fin n := ⟨k, hk⟩
        obtain ⟨hpo, hpi⟩ := ih p rfl
        have hp : p.val + 1 < n := by dsimp [p]; omega
        have heq : (⟨p.val + 1, hp⟩ : Fin n) = i := by
          apply Fin.ext
          dsimp [p]
          omega
        have ho := hover p hp
        dsimp [overlap] at ho
        rw [heq] at ho
        have hl := hlen i
        have hx := X.row_nonempty i
        have hy := Y.row_nonempty i
        dsimp [rowLength] at hl
        constructor <;> omega
    refine ⟨rfl, t, ?_⟩
    intro i j hij
    have heq : i = j := Fin.ext hij
    subst j
    exact recover i.val i rfl
  · refine ⟨rfl, 0, ?_⟩
    intro i j hij
    omega

end Diagram
end SkewSchurReconstruction
