/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.SaturationMarkedCells
import SkewClassInflation.SaturationPowerMerge
import SkewClassInflation.ProfileMergeCells
import SkewClassInflation.OrdinaryComposition

/-!
# Literal horizontal composition of the general marked inner

The east-step construction in `eq:saturation-translations` and
`prop:saturation-chart` of `shields-2026-skew-class-inflation.tex`.
The affine cell composition and the actual endpoint-merger recurrence
produce the same finite union at every positive copy count.  Sorry-free.
-/

namespace SkewClassInflation.SaturationInner

open SkewJacobiNegative SkewGluing

variable (A : SaturationInner)

private theorem translate_union (v : ℤ × ℤ) (D E : Diagram) :
    translate v (D ∪ E) = translate v D ∪ translate v E := Finset.image_union _ _

/-- The actual one-copy power is the complete original profile, including its finite order. -/
theorem power_one_profile :
    (⟨1 * A.k, A.power 1 (by decide)⟩ : ConnectedProfile) = ⟨A.k, A.profile⟩ := by
  apply profileSigma_eq_of_words
  · exact A.power_one_word
  · change List.ofFn (fun _ : Fin (1 * A.k) => A.c) = List.ofFn (fun _ : Fin A.k => A.c)
    simp only [Nat.one_mul]

/-- The two profile presentations have the identical actual one-copy cell set. -/
theorem power_one_cells : profileCells (A.power 1 (by decide)) = profileCells A.profile :=
  congrArg (fun D : ConnectedProfile => profileCells D.2) A.power_one_profile

/-- An actual east step gives the displayed mark-identifying translation. -/
theorem markedInner_origin_east (D : Diagram) :
    A.markedInner.origin D (0, 1) =
      (-(A.k : ℤ), A.profile.xi 0 - A.k - A.d) := by
  simp only [MarkedInner.origin, markedInner, content, sub_zero,
    one_smul, zero_smul, add_zero]

/-- An actual north step subtracts the diagonal unit from the east-step translation. -/
theorem markedInner_origin_north (D : Diagram) :
    A.markedInner.origin D (-1, 0) =
      (-(A.k : ℤ) - 1, A.profile.xi 0 - A.k - A.d - 1) := by
  simp [MarkedInner.origin, markedInner, content, eCell, sub_eq_add_neg]

/-- A one-cell outer places exactly the actual marked inner at the base origin. -/
theorem row_compose_one : A.markedInner.compose (rowCells 0 1) = A.innerCells := by
  have hm : ¬ A.markedInner.case.IsMixed := by change ¬ AttachCase.a.IsMixed; decide
  ext x
  rw [MarkedInner.compose_of_ordinary (rowCells_nonempty (by omega : (0 : ℤ) < 1)) hm]
  constructor
  · rintro ⟨⟨a, b⟩, hab, hx⟩
    rw [mem_rowCells] at hab
    have ha : a = 0 := hab.1
    have hb : b = 0 := by omega
    subst a b
    simpa only [MarkedInner.origin, markedInner, content, Prod.fst, Prod.snd, sub_self,
      zero_smul, zero_add, translate_zero] using hx
  · intro hx
    refine ⟨(0, 0), (mem_rowCells.mpr ⟨rfl, le_rfl, by omega⟩), ?_⟩
    simpa only [MarkedInner.origin, markedInner, content, Prod.fst, Prod.snd, sub_self,
      zero_smul, zero_add, translate_zero] using hx

/-- Adjoining an east cell adds exactly one translated literal inner copy. -/
theorem row_compose_succ (m : ℕ) (hm : 0 < m) :
    A.markedInner.compose (rowCells 0 ((m + 1 : ℕ) : ℤ)) =
      A.innerCells ∪ translate A.markedInner.v (A.markedInner.compose (rowCells 0 m)) := by
  have hrow : rowCells 0 ((m + 1 : ℕ) : ℤ) =
      rowCells 0 1 ∪ translate (0, 1) (rowCells 0 m) := by
    ext ⟨a, b⟩
    rw [Finset.mem_union, mem_translate]
    simp only [mem_rowCells, Prod.mk_sub_mk, sub_zero]
    omega
  have h1 := rowCells_nonempty (by omega : (0 : ℤ) < 1)
  have hm' := rowCells_nonempty (by exact_mod_cast hm : (0 : ℤ) < m)
  rw [hrow, ordinary_compose_union A.markedInner rfl (rowCells 0 1)
    (translate (0, 1) (rowCells 0 m)) h1 (hm'.image _),
    ordinary_compose_translate A.markedInner rfl (rowCells 0 m) hm' (0, 1),
    A.row_compose_one]
  have ho : A.markedInner.origin (rowCells 0 m) (0, 1) = A.markedInner.v := by
    simp only [MarkedInner.origin, markedInner, content, sub_zero,
      one_smul, zero_smul, add_zero]
  rw [ho]

/-- A horizontal outer gives the actual full overlapped power in its fixed literal origin. -/
theorem row_compose_eq_power (m : ℕ) (hm : 0 < m) :
    A.markedInner.compose (rowCells 0 m) =
      translate (((1 - (m : ℤ)) * A.k), -(m : ℤ) * A.k) (profileCells (A.power m hm)) := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  induction a with
  | zero =>
    change A.markedInner.compose (rowCells 0 1) =
      translate (((1 - (1 : ℤ)) * A.k), -(1 : ℤ) * A.k)
        (profileCells (A.power 1 (by decide)))
    rw [A.row_compose_one, A.power_one_cells]
    simp only [sub_self, zero_mul, neg_mul, one_mul, innerCells]
  | succ a ih =>
    rw [A.row_compose_succ (a + 1) (by omega), ih (by omega)]
    have hmerge := congrArg (fun D : ConnectedProfile => profileCells D.2)
      (A.merge_powers (a + 1) 1 (by omega) (by decide))
    rw [← hmerge, profileCells_merge, translate_union,
      translate_translate, translate_translate, translate_translate, A.power_one_cells]
    have hspan : (A.power 1 (by decide)).xi 0 = A.profile.xi 0 :=
      congrArg (fun D : ConnectedProfile => D.2.xi 0) A.power_one_profile
    rw [hspan, innerCells]
    rw [Finset.union_comm]
    congr 2 <;> ext <;>
      simp only [markedInner, Prod.fst_add, Prod.snd_add, Nat.cast_succ, Nat.cast_mul] <;> ring

end SkewClassInflation.SaturationInner
