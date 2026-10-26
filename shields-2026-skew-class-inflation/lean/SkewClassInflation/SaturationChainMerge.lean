/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.SaturationChains
import SkewClassInflation.SaturationPowerMerge
import SkewClassInflation.ProfileCompositionAssociativity

/-!
# Literal contraction of the first larger source seam

The ordered source contraction in `eq:total-contraction` and
`eq:saturation-substitution` of `shields-2026-skew-class-inflation.tex`.
The first two copy multiplicities merge without disturbing later rows or cuts.
Sorry-free.
-/

namespace SkewClassInflation.SaturationInner

open SkewJacobiNegative

variable (A : SaturationInner)

/-- Contracting the first larger seam combines precisely the first two copy multiplicities. -/
theorem merge_power_chain (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (l : List ℕ) (hl : ∀ m ∈ l, 0 < m) :
    let R := A.chain b hb l hl
    let hR : A.d < R.2.r 0 := by
      rw [A.chain_first]
      have := A.first_bound
      omega
    (⟨a * A.k + R.1, Profile.merge (A.power a ha) R.2 A.d
      (A.power_rows_above_seam a ha _) hR⟩ : ConnectedProfile) =
        A.chain (a + b) (by omega) l hl := by
  intro R hR
  cases l with
  | nil => exact A.merge_powers a b ha hb
  | cons c l =>
    let hc := hl c List.mem_cons_self
    let htail : ∀ m ∈ l, 0 < m := fun m hm => hl m (List.mem_cons_of_mem _ hm)
    let T := A.chain c hc l htail
    let P := A.power a ha
    let Q := A.power b hb
    let U := A.power (a + b) (by omega)
    have hp : A.d < P.r (Fin.last (a * A.k)) := A.power_rows_above_seam a ha _
    have hq : A.d < Q.r 0 := A.power_rows_above_seam b hb _
    have hqlast : A.d < Q.r (Fin.last (b * A.k)) := A.power_rows_above_seam b hb _
    have hu : A.d < U.r (Fin.last ((a + b) * A.k)) := A.power_rows_above_seam (a + b) _ _
    have ht : A.d < T.2.r 0 := by
      rw [A.chain_first]
      have := A.first_bound
      omega
    have hpowers := A.merge_powers a b ha hb
    have hmerged : A.d < (Profile.merge P Q A.d hp hq).r (Fin.last (a * A.k + b * A.k)) := by
      have he := congrArg (fun D : ConnectedProfile => A.d < D.2.r (Fin.last D.1)) hpowers
      exact he.mpr hu
    have hassoc := profile_merge_join_assoc P Q T.2 A.d A.d hp hq hqlast ht hmerged
    have he := congrArg (fun D : ConnectedProfile => profileCells D.2) hassoc
    have hcells := congrArg (fun D : ConnectedProfile => profileCells D.2) hpowers
    apply profileCells_translation_injective _ _ 0 0
    rw [SkewGluing.translate_zero, SkewGluing.translate_zero]
    change profileCells (Profile.merge P (Profile.join Q T.2 A.d hqlast ht) A.d hp _) =
      profileCells (Profile.join U T.2 A.d hu ht)
    rw [he, profileCells_join, profileCells_join, hcells]
    have hn : a * A.k + b * A.k = (a + b) * A.k := by ring
    simp only [hn]
    rfl

end SkewClassInflation.SaturationInner
