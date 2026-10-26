/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalProjectionBlocks

/-!
# Actual within-component beta coordinate span bounds

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
Complete original row and column endpoints in one nonempty component lie
between its actual extreme contents. An empty block is its isolated literal
unit vertex. The geometric maximal-span assumption supplies the bound in both
cases. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- Actual endpoints in one original block have row-minus-column difference
at most the geometric maximal component span. Literal empty vertices are
retained and contribute difference zero. -/
theorem interior_same_block_entry_span_le {n : ℕ} (P : Profile n) (N : ℕ)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ N)
    (i j : Fin n) (hlabel : interiorBlock P j = interiorBlock P i) :
    P.xi j.succ - P.zeta i.castSucc ≤ (N : ℤ) := by
  by_cases hi : P.zeta i.castSucc < P.xi i.succ
  · have hj := interior_block_row_nonempty P hi hlabel
    let C := interiorBlockCells P i
    have hright : ((j : ℤ), P.xi j.succ + (j : ℤ) - 1) ∈ C := by
      apply (mem_interiorBlockCells P i _ _).mpr
      exact ⟨j, hlabel, rfl, by omega, by omega⟩
    have hleft : ((i : ℤ), P.zeta i.castSucc + (i : ℤ)) ∈ C := by
      apply (mem_interiorBlockCells P i _ _).mpr
      exact ⟨i, rfl, rfl, le_rfl, by omega⟩
    have hR : P.xi j.succ - 1 ∈ contents C := by
      apply Finset.mem_image.mpr
      exact ⟨_, hright, by dsimp only [content]; omega⟩
    have hL : P.zeta i.castSucc ∈ contents C := by
      apply Finset.mem_image.mpr
      exact ⟨_, hleft, by dsimp only [content]; omega⟩
    have hu := le_maxContent hR
    have hl := minContent_le hL
    have hs := span_eq_of_isConnectedSkew (interiorBlockCells_connected P i hi)
    change (span C : ℤ) = maxContent C - minContent C + 1 at hs
    have hN : (span C : ℤ) ≤ (N : ℤ) := by
      exact_mod_cast hmax C (interiorBlockCells_mem_components P i hi)
    omega
  · have he : P.xi i.succ = P.zeta i.castSucc := by
      have := P.zeta_le_xi_succ i
      omega
    have hj := interior_empty_row_isolated P i he j hlabel
    subst j
    rw [he, sub_self]
    exact_mod_cast Nat.zero_le N

end SkewCornerDescent.Matrix
