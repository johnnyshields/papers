/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.ThinCompositions

/-!
# Prepending an actual thin block

The ordered assembly used in `thm:two-row-thin-class` of
`shields-2026-skew-class-inflation.tex`.  Composition concatenation is
identified with the literal zero join, including the dependent row
count.  Sorry-free.
-/

namespace SkewClassInflation.ThinParameters

variable (B : ThinParameters)

/-- A nonempty composition supplies the remaining literal chain after one fixed block. -/
theorem chain_blocks {m M : ℕ} (hm : 0 < m) (α : Composition M) (hM : 0 < M) :
    B.chain m hm α.blocks (fun _ h => α.blocks_pos h) =
      ConnectedProfile.zeroJoin ⟨m, B.innerPower m hm⟩ (B.diagram α hM) := by
  unfold diagram
  split
  · rename_i he
    have hs := α.blocks_sum
    rw [he] at hs
    simp only [List.sum_nil] at hs
    omega
  · rename_i a l he
    simp only [he, chain]

/-- The constructed diagram of a prepended part is the actual zero join of its two diagrams. -/
theorem diagram_prepend {m M : ℕ} (hm : 0 < m) (α : Composition M) (hM : 0 < M) :
    B.diagram ((Composition.single m hm).append α) (by omega) =
      ConnectedProfile.zeroJoin ⟨m, B.innerPower m hm⟩ (B.diagram α hM) := by
  change B.chain m hm α.blocks (fun _ h => α.blocks_pos h) = _
  exact B.chain_blocks hm α hM

end SkewClassInflation.ThinParameters
