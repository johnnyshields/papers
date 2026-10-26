/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.SaturationPowers
import SkewClassInflation.SeparatedJoins
import SkewClassInflation.InflationClasses

/-!
# Actual separated repeated-block source diagrams

The complete source construction `F_alpha` in `eq:repeated-blocks`
and its row-count reading in `eq:saturation-readings` of
`shields-2026-skew-class-inflation.tex`.  Every join uses the actual
larger seam and the original endpoint rows, for arbitrary interior
words and zero or positive inner gaps.  Sorry-free.
-/

namespace SkewClassInflation.SaturationInner

open SkewJacobiNegative

variable (A : SaturationInner)

private def chainData (a : ℕ) (ha : 0 < a) :
    (l : List ℕ) → (∀ b ∈ l, 0 < b) → {D : ConnectedProfile // D.2.r 0 = A.r 0}
  | [], _ => ⟨⟨a * A.k, A.power a ha⟩, A.power_first a ha⟩
  | b :: l, hl =>
    let R := chainData b (hl b List.mem_cons_self) l
      (fun j hj => hl j (List.mem_cons_of_mem _ hj))
    let P := A.power a ha
    let hp : A.d < P.r (Fin.last (a * A.k)) := by
      rw [A.power_last]
      have := A.last_bound
      omega
    let hq : A.d < R.val.2.r 0 := by
      rw [R.property]
      have := A.first_bound
      omega
    ⟨⟨a * A.k + R.val.1 + 1, Profile.join P R.val.2 A.d hp hq⟩, by
      have he := Profile.joinRows_left P R.val.2 (0 : Fin (a * A.k + 1))
      exact he.trans (A.power_first a ha)⟩

/-- The complete larger-seam chain of the specified positive copy multiplicities. -/
def chain (a : ℕ) (ha : 0 < a) (l : List ℕ) (hl : ∀ b ∈ l, 0 < b) : ConnectedProfile :=
  (A.chainData a ha l hl).val

/-- The first source row is always the original first endpoint. -/
theorem chain_first (a : ℕ) (ha : 0 < a) (l : List ℕ) (hl : ∀ b ∈ l, 0 < b) :
    (A.chain a ha l hl).2.r 0 = A.r 0 := (A.chainData a ha l hl).property

/-- The source gap count includes precisely one additional position at each outer cut. -/
theorem chain_row_count (a : ℕ) (ha : 0 < a) (l : List ℕ) (hl : ∀ b ∈ l, 0 < b) :
    (A.chain a ha l hl).1 + 1 = (a + l.sum) * A.k + l.length + 1 := by
  induction l generalizing a with
  | nil => simp [chain, chainData]
  | cons b l ih =>
    have hh := ih b (hl b List.mem_cons_self)
      (fun j hj => hl j (List.mem_cons_of_mem _ hj))
    change a * A.k + (A.chain b (hl b List.mem_cons_self) l
      (fun j hj => hl j (List.mem_cons_of_mem _ hj))).1 + 1 + 1 = _
    simp only [List.sum_cons, List.length_cons]
    nlinarith

/-- The first gap of the entire source is internal to its nonempty first repeated block. -/
theorem chain_first_gap (a : ℕ) (ha : 0 < a) (l : List ℕ) (hl : ∀ b ∈ l, 0 < b)
    (j : Fin (A.chain a ha l hl).1) (hj : j.val = 0) :
    (A.chain a ha l hl).2.g j = A.c := by
  cases l with
  | nil => rfl
  | cons b l =>
    have hak : 0 < a * A.k := Nat.mul_pos ha A.k_pos
    change Profile.joinGaps (A.power a ha)
      (A.chain b (hl b List.mem_cons_self) l
        (fun j hj => hl j (List.mem_cons_of_mem _ hj))).2 A.d j = A.c
    simp only [Profile.joinGaps, dite_eq_left (show j.val < a * A.k by omega)]
    rfl

/-- The actual larger-seam source is Hessenberg on the entire standing domain. -/
theorem chain_thick (a : ℕ) (ha : 0 < a) (l : List ℕ) (hl : ∀ b ∈ l, 0 < b) :
    Staircase.Thick (A.chain a ha l hl).2 := by
  induction l generalizing a with
  | nil => exact A.power_thick a ha
  | cons b l ih =>
    let R := A.chain b (hl b List.mem_cons_self) l
      (fun j hj => hl j (List.mem_cons_of_mem _ hj))
    apply Profile.join_thick
    · rw [A.power_last]
      have := A.last_bound
      omega
    · change A.d < R.2.r 0
      rw [A.chain_first]
      have := A.first_bound
      omega
    · exact A.power_thick a ha
    · exact ih b _ _
    · intro j _
      change A.c + A.d < (A.power a ha).r (Fin.last (a * A.k))
      rw [A.power_last]
      exact A.last_bound
    · intro j hj
      have hg := A.chain_first_gap b (hl b List.mem_cons_self) l
        (fun j hj => hl j (List.mem_cons_of_mem _ hj)) j hj
      change A.d + R.2.g j < R.2.r 0
      rw [hg, A.chain_first]
      have := A.first_bound
      omega

/-- The literal general repeated-block diagram for a positive outer composition. -/
def diagram {M : ℕ} (α : Composition M) (hM : 0 < M) : ConnectedProfile :=
  match he : α.blocks with
  | [] => False.elim (by have hs := α.blocks_sum; rw [he] at hs; simp at hs; omega)
  | a :: l => A.chain a (α.blocks_pos (by rw [he]; exact List.mem_cons_self)) l
      (fun j hj => α.blocks_pos (by rw [he]; exact List.mem_cons_of_mem _ hj))

/-- The general source row count is its total repeated-inner order plus the outer length. -/
theorem diagram_row_count {M : ℕ} (α : Composition M) (hM : 0 < M) :
    (A.diagram α hM).1 + 1 = M * A.k + α.length := by
  unfold diagram
  split
  · rename_i he
    have hs := α.blocks_sum
    rw [he] at hs
    simp only [List.sum_nil] at hs
    omega
  · rename_i a l he
    have ha : 0 < a := α.blocks_pos (by rw [he]; exact List.mem_cons_self)
    have hl : ∀ j ∈ l, 0 < j :=
      fun j hj => α.blocks_pos (by rw [he]; exact List.mem_cons_of_mem _ hj)
    have hh := A.chain_row_count a ha l hl
    have hs : a + l.sum = M := by simpa only [he, List.sum_cons] using α.blocks_sum
    have hlen : α.length = l.length + 1 := by simp [Composition.length, he]
    rw [hs] at hh
    omega

/-- Every actual general source is a connected Hessenberg profile without an assumed class input. -/
theorem diagram_thick {M : ℕ} (α : Composition M) (hM : 0 < M) :
    Staircase.Thick (A.diagram α hM).2 := by
  unfold diagram
  split
  · rename_i he
    have hs := α.blocks_sum
    rw [he] at hs
    simp only [List.sum_nil] at hs
    omega
  · exact A.chain_thick _ _ _ _

end SkewClassInflation.SaturationInner
