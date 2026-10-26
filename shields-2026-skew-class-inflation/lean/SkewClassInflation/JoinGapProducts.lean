/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.ProfileJoins

/-!
# Complete products and sums of literal joining gaps

The multiplicity readings in `eq:saturation-readings` and
`eq:thin-readings` of `shields-2026-skew-class-inflation.tex`.
Every gap position is retained and the distinguished joining position
is inserted exactly once, independently of coincident numerical labels.
Sorry-free.
-/

namespace SkewClassInflation.Profile

open SkewJacobiNegative
open scoped BigOperators

/-- A gap product retains both original words and inserts precisely the one joining factor. -/
@[to_additive]
theorem prod_join_gaps {R : Type*} [CommMonoid R] {n m : ℕ}
    (P : Profile n) (Q : Profile m) (d : ℕ)
    (hp : d < P.r (Fin.last n)) (hq : d < Q.r 0) (f : ℕ → R) :
    (∏ j : Fin (n + m + 1), f ((join P Q d hp hq).g j)) =
      (∏ j : Fin n, f (P.g j)) * (∏ j : Fin m, f (Q.g j)) * f d := by
  classical
  let c : Fin (n + m + 1) := ⟨n, by omega⟩
  rw [Fin.prod_univ_succAbove _ c, Fin.prod_univ_add]
  have hl : (∏ i : Fin n, f ((join P Q d hp hq).g (c.succAbove (i.castAdd m)))) =
      ∏ i : Fin n, f (P.g i) := by
    apply Finset.prod_congr rfl
    intro i _
    have hi : (i.castAdd m).castSucc < c := by change i.val < n; exact i.isLt
    rw [Fin.succAbove_of_castSucc_lt _ _ hi]
    change f (joinGaps P Q d ⟨i.val, by omega⟩) = _
    rw [joinGaps_left]
  have hr : (∏ i : Fin m, f ((join P Q d hp hq).g (c.succAbove (i.natAdd n)))) =
      ∏ i : Fin m, f (Q.g i) := by
    apply Finset.prod_congr rfl
    intro i _
    have hi : c ≤ (i.natAdd n).castSucc := by change n ≤ n + i.val; omega
    rw [Fin.succAbove_of_le_castSucc _ _ hi]
    have he : (i.natAdd n).succ =
        (⟨n + 1 + i.val, by have := i.isLt; omega⟩ : Fin (n + m + 1)) := by
      apply Fin.ext
      simp
      omega
    rw [he]
    change f (joinGaps P Q d ⟨n + 1 + i.val, by omega⟩) = _
    rw [joinGaps_right]
  rw [hl, hr]
  have hc : (join P Q d hp hq).g c = d := joinGaps_middle P Q d
  rw [hc]
  ac_rfl

end SkewClassInflation.Profile
