/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.ProfileMergeCells

/-!
# Literal associativity between joins and endpoint mergers

The profile assembly underlying `eq:total-contraction` and
`eq:saturation-substitution` of `shields-2026-skew-class-inflation.tex`.
Actual cell unions prove the identity across different dependent row counts.
Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative SkewGluing

private theorem translate_union (v : ℤ × ℤ) (D E : Diagram) :
    translate v (D ∪ E) = translate v D ∪ translate v E := Finset.image_union _ _

/-- Merging at the first seam commutes with retaining the next literal joining seam. -/
theorem profile_merge_join_assoc {n m k : ℕ} (P : Profile n) (Q : Profile m) (R : Profile k)
    (d e : ℕ) (hP : d < P.r (Fin.last n)) (hQ : d < Q.r 0)
    (hQlast : e < Q.r (Fin.last m)) (hR : e < R.r 0)
    (hMerged : e < (Profile.merge P Q d hP hQ).r (Fin.last (n + m))) :
    let J := Profile.join Q R e hQlast hR
    let hJ : d < J.r 0 := by
      change d < Profile.joinRows Q R 0
      have he := Profile.joinRows_left Q R (0 : Fin (m + 1))
      change Profile.joinRows Q R 0 = Q.r 0 at he
      rw [he]
      exact hQ
    (⟨n + (m + k + 1), Profile.merge P J d hP hJ⟩ : ConnectedProfile) =
      ⟨n + m + k + 1, Profile.join (Profile.merge P Q d hP hQ) R e hMerged hR⟩ := by
  intro J hJ
  apply profileCells_translation_injective _ _ 0 0
  rw [SkewGluing.translate_zero, SkewGluing.translate_zero]
  change profileCells (Profile.merge P (Profile.join Q R e hQlast hR) d hP hJ) = _
  rw [profileCells_merge, profileCells_join, profileCells_join, profileCells_merge,
    Profile.join_span]
  simp only [translate_union, SkewGluing.translate_translate]
  rw [Finset.union_assoc]
  congr 1
  · congr 1
    ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring
  · congr 1
    · congr 1
      ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring

end SkewClassInflation
