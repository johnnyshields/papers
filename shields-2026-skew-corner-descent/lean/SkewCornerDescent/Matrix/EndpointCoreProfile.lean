/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.EndpointCoreBorders

/-!
# Original source profiles on the complete endpoint core frame

Supports `shields-2026-skew-corner-descent.tex` (`lem:shared-core`).
The core uses exactly the original rows after the first and columns before the
last. Both boundary endpoints and every zero-index pivot remain. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- The unchanged source profile is exactly the complete empty-border endpoint
frame, with its whole original corner core and both unmatched endpoints. -/
theorem endpointCoreFrame_base_profile {b : ℕ} (U : Profile (b + 1)) :
    endpointCoreFrame (fun (_ : Fin 0 ⊕ Unit) => U.xi 0)
      (fun i => U.xi (commonCoreFinEquiv b i).succ) (fun i : Fin 0 => i.elim0)
      (fun i : Fin 0 => i.elim0) (fun j => U.zeta (commonCoreFinEquiv b j).castSucc)
      (fun (_ : Unit ⊕ Fin 0) => U.zeta (Fin.last (b + 1))) =
      originalProfileFrame U 0 b 0 (by omega) := by
  apply endpointCoreFrame_eq_originalProfileFrame U (by omega) 0
  all_goals simp only [add_zero]
  · rintro ((i | u) | (i | i))
    · exact i.elim0
    · cases u
      rfl
    · change U.xi _ = U.xi (commonCoreFinEquiv b i).succ
      apply congrArg U.xi
      apply Fin.ext
      simp [Equiv.trans_apply, commonCoreFiniteRows_core, Nat.add_comm]
    · exact i.elim0
  · intro j
    obtain ⟨j, rfl⟩ := (commonCoreColumnEquiv (Fin 0) (Fin b) (Fin 0)).surjective j
    simp only [endpointBorderCols, Function.comp_apply, Equiv.symm_apply_apply]
    rcases j with j | (j | j)
    · exact j.elim0
    · change U.zeta _ = U.zeta (commonCoreFinEquiv b j).castSucc
      apply congrArg U.zeta
      apply Fin.ext
      simp [Equiv.trans_apply, commonCoreFiniteCols_core]
    · rcases j with u | j
      · cases u
        change U.zeta _ = U.zeta (Fin.last (b + 1))
        apply congrArg U.zeta
        apply Fin.ext
        simp [Equiv.trans_apply, commonCoreFiniteCols_border]
      · exact j.elim0

end SkewCornerDescent.Matrix
