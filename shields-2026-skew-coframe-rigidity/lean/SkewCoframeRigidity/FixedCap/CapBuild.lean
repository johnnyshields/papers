/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.FixedCap.CutSeries
import SkewCoframeRigidity.FixedCap.Reduction

/-!
# The recursive cap

Formalizes `sc:fcp-recursive-cap` of `shields-2026-skew-coframe-rigidity.tex`.  For a diagram `B`
with a cut after its first `q` proper rows and columns, and an integer `t` below every prefix row
and column, the lists `{c - t} ∪ (rows P - t)` and `(cols P - t) ∪ {0}` form an actual connected
normalized cap `capOf B q t`, where `P` is the prefix.  Sorry-free.
-/

namespace SkewCoframeRigidity.FixedCap

open SkewCofactorIndependence SkewCoframeRigidity SkewCoframeRigidity.Coframe Polynomial
open scoped Polynomial Matrix

variable {n : ℕ}

/-- The recursive cap of the first `q` proper rows and columns of `B`, translated down by `t`. -/
def capOf (B : BetaDiagram (n + 1)) (q : ℕ) (hq : q ≤ n) (t : ℤ)
    (ht : t < B.row ⟨q, by omega⟩) (hcol : ∀ i : Fin (n + 1), i.val < q → t < B.col i) :
    BetaDiagram (q + 1) where
  row i := B.row (Fin.castLE (by omega) i) - t
  col i := if i.val < q then B.col (Fin.castLE (by omega) i) - t else 0
  row_strictAnti := fun i j hij => by
    have := B.row_strictAnti (show Fin.castLE (by omega : q + 1 ≤ n + 1) i <
      Fin.castLE (by omega : q + 1 ≤ n + 1) j from hij)
    change B.row (Fin.castLE _ j) - t < B.row (Fin.castLE _ i) - t
    omega
  col_strictAnti := fun i j hij => by
    have hij' : i.val < j.val := hij
    change (if j.val < q then B.col (Fin.castLE _ j) - t else 0) <
      (if i.val < q then B.col (Fin.castLE _ i) - t else 0)
    by_cases hj : j.val < q
    · have hi : i.val < q := by omega
      rw [if_pos hj, if_pos hi]
      have := B.col_strictAnti (show Fin.castLE (by omega : q + 1 ≤ n + 1) i <
        Fin.castLE (by omega : q + 1 ≤ n + 1) j from hij)
      omega
    · have hi : i.val < q := by omega
      rw [if_neg hj, if_pos hi]
      have := hcol (Fin.castLE (by omega : q + 1 ≤ n + 1) i) (by simp; omega)
      omega
  row_nonempty := fun i => by
    by_cases hi : i.val < q
    · rw [if_pos hi]
      have := B.row_nonempty (Fin.castLE (by omega : q + 1 ≤ n + 1) i)
      omega
    · rw [if_neg hi]
      have hiq : i.val = q := by omega
      have : B.row (Fin.castLE (by omega : q + 1 ≤ n + 1) i) = B.row ⟨q, by omega⟩ := by
        congr 1; exact Fin.ext hiq
      omega

section CapOf

variable (B : BetaDiagram (n + 1)) (q : ℕ) (hq : q ≤ n) (t : ℤ)
  (ht : t < B.row ⟨q, by omega⟩) (hcol : ∀ i : Fin (n + 1), i.val < q → t < B.col i)

@[simp] theorem capOf_row (i : Fin (q + 1)) :
    (capOf B q hq t ht hcol).row i = B.row (Fin.castLE (by omega) i) - t := rfl

theorem capOf_col_of_lt (i : Fin (q + 1)) (hi : i.val < q) :
    (capOf B q hq t ht hcol).col i = B.col (Fin.castLE (by omega) i) - t := by
  change (if i.val < q then _ else _) = _
  rw [if_pos hi]

theorem capOf_isNorm : IsNorm (capOf B q hq t ht hcol) := by
  change (if (Fin.last q).val < q then _ else _) = 0
  rw [if_neg (by simp)]

theorem capOf_connected (hB : B.Connected) : (capOf B q hq t ht hcol).Connected := by
  refine ⟨Nat.succ_pos q, fun i hi => ?_⟩
  have hiq : i.val < q := by omega
  rw [capOf_col_of_lt B q hq t ht hcol i hiq, capOf_row]
  have h1 := hB.2 ⟨i.val, by omega⟩ (by simp; omega)
  exact sub_le_sub_right h1 t

end CapOf

end SkewCoframeRigidity.FixedCap
