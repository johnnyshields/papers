/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.SaturationLiteralContraction

/-!
# Actual prefix ends in the full contracted source

Formalizes `eq:split-positions` of
`shields-2026-skew-class-inflation.tex`.  The total contraction of
the literal first outer parts determines the split index.  That same
index in the actual complete source core is its endpoint-merger row.
All positions are retained when numerical row lengths coincide.
Sorry-free.
-/

namespace SkewClassInflation

/-- The actual first outer parts, at their true partial total weight. -/
def compositionPrefix {M : ℕ} (α : Composition M) (j : ℕ) : Composition (α.sizeUpTo j) where
  blocks := α.blocks.take j
  blocks_pos hi := α.blocks_pos (List.mem_of_mem_take hi)
  blocks_sum := rfl

/-- A genuine bounded prefix retains exactly its stated number of original parts. -/
theorem compositionPrefix_length {M : ℕ} (α : Composition M) (j : ℕ) (hj : j ≤ α.length) :
    (compositionPrefix α j).length = j := by
  change (α.blocks.take j).length = j
  rw [List.length_take, Nat.min_eq_left hj]

namespace SaturationInner

open SkewJacobiNegative SkewJacobiNegative.Staircase

variable (A : SaturationInner)

/-- A proper positive whole-copy position in a power is exactly its literal merger row. -/
theorem power_split_row (M : ℕ) (hM : 0 < M) (s : ℕ) (hs : 0 < s) (hsM : s < M) :
    (A.power M hM).r ⟨s * A.k, by
      have hh := Nat.mul_lt_mul_of_pos_right hsM A.k_pos
      omega⟩ = A.merger := by
  have hp := Nat.mul_pos hs A.k_pos
  have hlt := Nat.mul_lt_mul_of_pos_right hsM A.k_pos
  change A.powerRows M ⟨s * A.k, by omega⟩ = _
  simp only [powerRows, ite_eq_right (Nat.ne_of_gt hp),
    ite_eq_right (Nat.ne_of_lt hlt), Nat.mul_mod_left, ite_true]

/-- The actual prefix core has exactly the manuscript's one-based split row count. -/
theorem prefix_core_row_count {M : ℕ} (α : Composition M) (j : ℕ)
    (hj0 : 0 < j) (hj : j ≤ α.length) :
    ∃ hp : 0 < α.sizeUpTo j,
      (contractAllMinimum (A.diagram (compositionPrefix α j) hp).2 A.largeLabel).1 + 1 =
        1 + A.k * α.sizeUpTo j := by
  have hp : 0 < α.sizeUpTo j := (Composition.length_pos_iff (compositionPrefix α j)).mp (by
    rw [compositionPrefix_length α j hj]
    exact hj0)
  refine ⟨hp, ?_⟩
  have hh := congrArg Sigma.fst (A.diagram_total_contraction (compositionPrefix α j) hp)
  change (contractAllMinimum (A.diagram (compositionPrefix α j) hp).2 A.largeLabel).1 =
    α.sizeUpTo j * A.k at hh
  rw [hh]
  ring

/-- Every proper prefix ends at its displayed merger row in the actual complete core. -/
theorem prefix_split_position {M : ℕ} (α : Composition M) (hM : 0 < M)
    (j : ℕ) (hj0 : 0 < j) (hj : j < α.length) :
    ∃ hp : 0 < α.sizeUpTo j,
    ∃ i : Fin ((contractAllMinimum (A.diagram α hM).2 A.largeLabel).1 + 1),
      i.val + 1 = 1 + A.k * α.sizeUpTo j ∧
      (contractAllMinimum (A.diagram α hM).2 A.largeLabel).2.r i = A.merger ∧
      (contractAllMinimum (A.diagram (compositionPrefix α j) hp).2 A.largeLabel).1 + 1 =
        i.val + 1 := by
  obtain ⟨hp, hprefix⟩ := A.prefix_core_row_count α j hj0 hj.le
  let s := α.sizeUpTo j
  have hsM : s < M := (α.sizeUpTo_strict_mono hj).trans_le (α.sizeUpTo_le (j + 1))
  have hprod : s * A.k < M * A.k := Nat.mul_lt_mul_of_pos_right hsM A.k_pos
  let C := (contractAllMinimum (A.diagram α hM).2 A.largeLabel : ConnectedProfile)
  have hC := A.diagram_total_contraction α hM
  have hdim : C.1 = M * A.k := congrArg Sigma.fst hC
  let i : Fin (C.1 + 1) := ⟨s * A.k, by rw [hdim]; omega⟩
  refine ⟨hp, i, ?_, ?_, ?_⟩
  · change s * A.k + 1 = 1 + A.k * s
    ring
  · have hh := congrArg (fun D : ConnectedProfile =>
      D.2.r ⟨min (s * A.k) D.1, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩) hC
    change C.2.r ⟨min (s * A.k) C.1, by omega⟩ =
      (A.power M hM).r ⟨min (s * A.k) (M * A.k), by omega⟩ at hh
    have hleft : (⟨min (s * A.k) C.1, by omega⟩ : Fin (C.1 + 1)) = i := by
      apply Fin.ext
      change min (s * A.k) C.1 = s * A.k
      rw [hdim, Nat.min_eq_left hprod.le]
    have hright : (⟨min (s * A.k) (M * A.k), by omega⟩ : Fin (M * A.k + 1)) =
        ⟨s * A.k, by omega⟩ := Fin.ext (Nat.min_eq_left hprod.le)
    rw [hleft, hright] at hh
    exact hh.trans (A.power_split_row M hM s hp hsM)
  · change _ = s * A.k + 1
    rw [hprefix]
    change 1 + A.k * s = s * A.k + 1
    ring

end SaturationInner
end SkewClassInflation
