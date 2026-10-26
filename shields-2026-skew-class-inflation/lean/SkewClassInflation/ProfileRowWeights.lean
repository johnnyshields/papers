/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.ProfileJoinCells
import SkewClassInflation.JoinGapProducts
import SkewClassInflation.JoinBetaSets

/-!
# Full row weight under literal profile joins

The joining calculation for `eq:saturation-readings` in
`shields-2026-skew-class-inflation.tex`.  Sorry-free.
-/

namespace SkewClassInflation.Profile

open SkewJacobiNegative

/-- Joining retains every row and changes no cell count, regardless of the overlap seam. -/
theorem join_row_weight {n m : ℕ} (P : Profile n) (Q : Profile m) (d : ℕ)
    (hP : d < P.r (Fin.last n)) (hQ : d < Q.r 0) :
    (∑ i : Fin (n + m + 2), ((join P Q d hP hQ).r i : ℤ)) =
      (∑ i : Fin (n + 1), (P.r i : ℤ)) + ∑ i : Fin (m + 1), (Q.r i : ℤ) := by
  have he := profile_span_sum (join P Q d hP hQ)
  rw [join_span, sum_join_gaps] at he
  have hp := profile_span_sum P
  have hq := profile_span_sum Q
  linarith only [he, hp, hq]

end SkewClassInflation.Profile
