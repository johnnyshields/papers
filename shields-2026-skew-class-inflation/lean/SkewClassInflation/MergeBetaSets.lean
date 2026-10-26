/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.ZeroContractionSets
import SkewClassInflation.ProfileMergeReadings

/-!
# Exact full beta supports after a zero merger

The literal merger operations underlying `eq:thin-substitution` in
`shields-2026-skew-class-inflation.tex`.  A zero merger erases the
shared joining beta from each complete list.  Sorry-free.
-/

namespace SkewClassInflation.Profile

open SkewJacobiNegative SkewJacobiNegative.GeneralHessenberg

/-- The first upper coordinate of the right block is the actual joining coordinate. -/
theorem zeroJoin_seam_xi {n m : ℕ} (P : Profile n) (Q : Profile m) :
    (zeroJoin P Q).xi (⟨n, by omega⟩ : Fin (n + m + 1)).succ = Q.xi 0 := by
  exact join_xi_right P Q 0 (P.r_pos _) (Q.r_pos _) 0

/-- Both entries at a zero seam coincide with the right block span. -/
theorem zeroJoin_seam_zeta {n m : ℕ} (P : Profile n) (Q : Profile m) :
    (zeroJoin P Q).zeta (⟨n, by omega⟩ : Fin (n + m + 1)).castSucc = Q.xi 0 := by
  have he := (zeroJoin P Q).xi_succ_sub_zeta_castSucc
    (⟨n, by omega⟩ : Fin (n + m + 1))
  have hg : (zeroJoin P Q).g ⟨n, by omega⟩ = 0 := joinGaps_middle P Q 0
  rw [hg, zeroJoin_seam_xi] at he
  omega

/-- The actual merger deletes the first right upper beta after translating the whole left block. -/
theorem merge_rowSet {n m : ℕ} (P : Profile n) (Q : Profile m) (d : ℕ)
    (hP : d < P.r (Fin.last n)) (hQ : d < Q.r 0) :
    (merge P Q d hP hQ).toBetaDiagram.rowSet =
      ((P.toBetaDiagram.rowSet.image (fun x => x + Q.xi 0 - d)) ∪
        Q.toBetaDiagram.rowSet).erase (Q.xi 0) := by
  rw [merge, contract_rowSet]
  have hx := join_xi_right P Q d hP hQ (0 : Fin (m + 1))
  change (join P Q d hP hQ).xi
    (⟨n, by omega⟩ : Fin (n + m + 1)).succ = Q.xi 0 at hx
  rw [hx, join_rowSet]

/-- The lower deletion differs from the upper deletion by exactly the joining seam. -/
theorem merge_colSet {n m : ℕ} (P : Profile n) (Q : Profile m) (d : ℕ)
    (hP : d < P.r (Fin.last n)) (hQ : d < Q.r 0) :
    (merge P Q d hP hQ).toBetaDiagram.colSet =
      ((P.toBetaDiagram.colSet.image (fun x => x + Q.xi 0 - d)) ∪
        Q.toBetaDiagram.colSet).erase (Q.xi 0 - d) := by
  rw [merge, contract_colSet]
  have hz := join_zeta_left P Q d hP hQ (Fin.last n)
  change (join P Q d hP hQ).zeta
    (⟨n, by omega⟩ : Fin (n + m + 1)).castSucc =
      P.zeta (Fin.last n) + Q.xi 0 - d at hz
  rw [P.zeta_last, zero_add] at hz
  rw [hz, join_colSet]

end SkewClassInflation.Profile
