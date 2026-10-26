/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.SaturationContraction
import SkewClassInflation.DistinguishedPeeling
import SkewClassInflation.ProfileMergeInverse
import SkewClassInflation.SaturationPrepend

/-!
# Literal simultaneous contraction of the constructed source

The source-side positional data in `eq:split-positions` of
`shields-2026-skew-class-inflation.tex`.  The actual total contraction
of every source chain is its full repeated power in the original
orientation, including a one-copy source.  Sorry-free.
-/

namespace SkewClassInflation.SaturationInner

open SkewJacobiNegative SkewJacobiNegative.Staircase

variable (A : SaturationInner)

/-- Contracting every actual larger seam of the literal chain gives its literal total power. -/
theorem chain_total_contraction (a : ℕ) (ha : 0 < a)
    (l : List ℕ) (hl : ∀ b ∈ l, 0 < b) :
    (contractAllMinimum (A.chain a ha l hl).2 A.largeLabel : ConnectedProfile) =
      ⟨(a + l.sum) * A.k, A.power (a + l.sum) (by omega)⟩ := by
  induction l generalizing a with
  | nil =>
    exact contractAllMinimum_self (A.power a ha) A.largeLabel
      (by intro j; change A.c ≠ A.d; exact Nat.ne_of_lt A.c_lt_d)
  | cons b l ih =>
    let hb : 0 < b := hl b List.mem_cons_self
    let htail : ∀ j ∈ l, 0 < j := fun j hj => hl j (List.mem_cons_of_mem _ hj)
    let S := A.chain b hb l htail
    let C := (contractAllMinimum S.2 A.largeLabel : ConnectedProfile)
    have hp : A.d < (A.power a ha).r (Fin.last (a * A.k)) := A.power_rows_above_seam a ha _
    have hrows : ∀ i, A.largeLabel.val < S.2.r i := A.chain_rows_above_seam b hb l htail
    have hprefix := distinguished_prefix_contraction (A.power a ha) S.2 A.largeLabel
      (A.power_thick a ha) (A.chain_thick b hb l htail)
      (A.power_rows_above_seam a ha) hrows
      (by intro j; change A.c ≠ A.d; exact Nat.ne_of_lt A.c_lt_d)
      (A.chain_thick a ha (b :: l) hl)
    have htailCore : C = ⟨(b + l.sum) * A.k, A.power (b + l.sum) (by omega)⟩ :=
      ih b hb htail
    have htrans := Profile.merge_right_congr (A.power a ha) C
      (⟨(b + l.sum) * A.k, A.power (b + l.sum) (by omega)⟩ : ConnectedProfile) A.d
      hp (contractAllMinimum_rows_above S.2 A.largeLabel hrows _)
      (A.power_rows_above_seam (b + l.sum) (by omega) _) htailCore
    exact hprefix.trans (htrans.trans (A.merge_powers a (b + l.sum) ha (by omega)))

/-- The actual total-contracted full source is the full power with the same original orientation. -/
theorem diagram_total_contraction {M : ℕ} (α : Composition M) (hM : 0 < M) :
    (contractAllMinimum (A.diagram α hM).2 A.largeLabel : ConnectedProfile) =
      ⟨M * A.k, A.power M hM⟩ := by
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
  have hcore := congrArg (fun D : ConnectedProfile =>
    (contractAllMinimum D.2 A.largeLabel : ConnectedProfile)) hd
  have hsum : a + l.sum = M := by
    have hh := α.blocks_sum
    rw [he, List.sum_cons] at hh
    exact hh
  have hpower : (⟨(a + l.sum) * A.k, A.power (a + l.sum) (by omega)⟩ : ConnectedProfile) =
      ⟨M * A.k, A.power M hM⟩ := by cases hsum; rfl
  exact hcore.trans ((A.chain_total_contraction a ha l hl).trans hpower)

end SkewClassInflation.SaturationInner
