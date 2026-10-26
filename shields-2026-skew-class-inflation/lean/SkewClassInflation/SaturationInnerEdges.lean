/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.SaturationPrepend
import SkewClassInflation.RibbonReversal

/-!
# Recovering the original inner from both exterior row fragments

The orientation-separation input to `eq:saturation-cardinality` in
`shields-2026-skew-class-inflation.tex`.  Exterior fragments retain all
original internal rows, regardless of coincident merger values.  Thus an
equality between opposite source orientations forces literal symmetry
of the given original inner.  Sorry-free.
-/

namespace SkewClassInflation.SaturationInner

open SkewJacobiNegative

variable (A : SaturationInner)

/-- The first inner's nonterminal original rows survive every positive power unchanged. -/
theorem power_first_inner_rows (m : ℕ) (hm : 0 < m) (i : Fin (m * A.k + 1))
    (hi : i.val < A.k) : (A.power m hm).r i = A.r ⟨i.val, by omega⟩ := by
  have hmk : A.k ≤ m * A.k := by
    have hh := Nat.mul_le_mul_right A.k (show 1 ≤ m by omega)
    simpa only [one_mul] using hh
  change A.powerRows m i = _
  unfold powerRows
  simp only [Nat.mod_eq_of_lt hi]
  by_cases hz : i.val = 0
  · rw [ite_eq_left hz]
    exact congrArg A.r (Fin.ext hz.symm)
  · have hlast : i.val ≠ m * A.k := by omega
    rw [ite_eq_right hz, ite_eq_right hlast, ite_eq_right hz]

/-- The final inner's noninitial original rows survive at their actual distance from the end. -/
theorem power_last_inner_rows (m : ℕ) (hm : 0 < m) (i : Fin A.k) :
    (A.power m hm).r ⟨m * A.k - i.val, by omega⟩ = A.r ⟨A.k - i.val, by omega⟩ := by
  have hmk : A.k ≤ m * A.k := by
    have hh := Nat.mul_le_mul_right A.k (show 1 ≤ m by omega)
    simpa only [one_mul] using hh
  by_cases hi0 : i.val = 0
  · simp only [hi0, Nat.sub_zero]
    exact A.power_last m hm
  · have hi : 0 < i.val := Nat.pos_of_ne_zero hi0
    have hbound := i.isLt
    have hmul : m * A.k = (m - 1) * A.k + A.k := by
      calc
        m * A.k = ((m - 1) + 1) * A.k := by rw [Nat.sub_add_cancel (by omega : 1 ≤ m)]
        _ = (m - 1) * A.k + A.k := by ring
    have hidx : m * A.k - i.val = (m - 1) * A.k + (A.k - i.val) := by omega
    have hmod : (m * A.k - i.val) % A.k = A.k - i.val := by
      rw [hidx, Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_mod,
        Nat.mod_eq_of_lt (by omega : A.k - i.val < A.k)]
    change A.powerRows m ⟨m * A.k - i.val, by omega⟩ = _
    simp only [powerRows, hmod]
    split_ifs <;> first | rfl | (congr 1; apply Fin.ext; omega) | omega

/-- Every nonempty source chain has room for the full original exterior fragments. -/
theorem chain_order_ge_inner (a : ℕ) (ha : 0 < a) (l : List ℕ) (hl : ∀ b ∈ l, 0 < b) :
    A.k ≤ (A.chain a ha l hl).1 := by
  have hs := A.chain_row_count a ha l hl
  have hka := Nat.mul_le_mul_right A.k (show 1 ≤ a by omega)
  have ham := Nat.mul_le_mul_right A.k (show a ≤ a + l.sum by omega)
  simp only [one_mul] at hka
  omega

/-- The first exterior fragment of every complete source is the given original inner. -/
theorem chain_first_inner_rows (a : ℕ) (ha : 0 < a) (l : List ℕ) (hl : ∀ b ∈ l, 0 < b) :
    ∀ (i : Fin ((A.chain a ha l hl).1 + 1)) (hi : i.val < A.k),
      (A.chain a ha l hl).2.r i = A.r ⟨i.val, by omega⟩ := by
  intro i hi
  cases l with
  | nil => exact A.power_first_inner_rows a ha i hi
  | cons b l =>
    let R := A.chain b (hl b List.mem_cons_self) l
      (fun j hj => hl j (List.mem_cons_of_mem _ hj))
    have hka := Nat.mul_le_mul_right A.k (show 1 ≤ a by omega)
    simp only [one_mul] at hka
    change Profile.joinRows (A.power a ha) R.2 i = _
    unfold Profile.joinRows
    rw [dite_eq_left (by change i.val < a * A.k + 1; omega)]
    exact A.power_first_inner_rows a ha _ hi

/-- The last exterior fragment is the same original inner read from its actual last row. -/
theorem chain_last_inner_rows (a : ℕ) (ha : 0 < a) (l : List ℕ) (hl : ∀ b ∈ l, 0 < b) :
    ∀ i : Fin A.k,
      (A.chain a ha l hl).2.r ⟨(A.chain a ha l hl).1 - i.val, by omega⟩ =
        A.r ⟨A.k - i.val, by omega⟩ := by
  induction l generalizing a with
  | nil => exact A.power_last_inner_rows a ha
  | cons b l ih =>
    intro i
    let R := A.chain b (hl b List.mem_cons_self) l
      (fun j hj => hl j (List.mem_cons_of_mem _ hj))
    have hdim : A.k ≤ R.1 := A.chain_order_ge_inner b _ l _
    have hi := i.isLt
    have hrow := Profile.joinRows_right (A.power a ha) R.2
      (⟨R.1 - i.val, by omega⟩ : Fin (R.1 + 1))
    change Profile.joinRows (A.power a ha) R.2
      ⟨a * A.k + R.1 + 1 - i.val, by omega⟩ = _
    have hidx : (⟨a * A.k + R.1 + 1 - i.val, by omega⟩ : Fin (a * A.k + R.1 + 2)) =
        ⟨a * A.k + 1 + (R.1 - i.val), by omega⟩ := Fin.ext (by
          change a * A.k + R.1 + 1 - i.val = a * A.k + 1 + (R.1 - i.val)
          omega)
    rw [hidx, hrow]
    exact ih b _ _ i

/-- Every actual general source contains at least one full original inner order. -/
theorem diagram_order_ge_inner {M : ℕ} (α : Composition M) (hM : 0 < M) :
    A.k ≤ (A.diagram α hM).1 := by
  unfold diagram
  split
  · rename_i he
    have hs := α.blocks_sum
    rw [he, List.sum_nil] at hs
    omega
  · exact A.chain_order_ge_inner _ _ _ _

/-- The first original inner fragment is read directly from the actual source rows. -/
theorem diagram_first_inner_rows {M : ℕ} (α : Composition M) (hM : 0 < M) :
    ∀ (i : Fin ((A.diagram α hM).1 + 1)) (hi : i.val < A.k),
      (A.diagram α hM).2.r i = A.r ⟨i.val, by omega⟩ := by
  have hex : ∃ a l, α.blocks = a :: l := by
    cases he : α.blocks with
    | nil =>
      have hs := α.blocks_sum
      rw [he, List.sum_nil] at hs
      omega
    | cons a l => exact ⟨a, l, rfl⟩
  obtain ⟨a, l, he⟩ := hex
  let ha : 0 < a := α.blocks_pos (by rw [he]; exact List.mem_cons_self)
  let hl : ∀ b ∈ l, 0 < b :=
    fun b hb => α.blocks_pos (by rw [he]; exact List.mem_cons_of_mem _ hb)
  have hd := A.diagram_eq_chain α hM a ha l hl he
  have hh := congrArg (fun D : ConnectedProfile =>
    ∀ (i : Fin (D.1 + 1)) (hi : i.val < A.k), D.2.r i = A.r ⟨i.val, by omega⟩) hd
  exact Eq.mpr hh (A.chain_first_inner_rows a ha l hl)

/-- The last original inner fragment is read directly at its distance from the source's end. -/
theorem diagram_last_inner_rows {M : ℕ} (α : Composition M) (hM : 0 < M) :
    ∀ i : Fin A.k,
      (A.diagram α hM).2.r ⟨(A.diagram α hM).1 - i.val, by omega⟩ =
        A.r ⟨A.k - i.val, by omega⟩ := by
  have hex : ∃ a l, α.blocks = a :: l := by
    cases he : α.blocks with
    | nil =>
      have hs := α.blocks_sum
      rw [he, List.sum_nil] at hs
      omega
    | cons a l => exact ⟨a, l, rfl⟩
  obtain ⟨a, l, he⟩ := hex
  let ha : 0 < a := α.blocks_pos (by rw [he]; exact List.mem_cons_self)
  let hl : ∀ b ∈ l, 0 < b :=
    fun b hb => α.blocks_pos (by rw [he]; exact List.mem_cons_of_mem _ hb)
  have hd := A.diagram_eq_chain α hM a ha l hl he
  intro i
  have hh := congrArg (fun D : ConnectedProfile =>
    D.2.r ⟨D.1 - i.val, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) hd
  exact hh.trans (A.chain_last_inner_rows a ha l hl i)

end SkewClassInflation.SaturationInner
