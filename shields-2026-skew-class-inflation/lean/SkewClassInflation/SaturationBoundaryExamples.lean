/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.SaturationContraction
import SkewClassInflation.SaturationRibbonReduction

/-!
# Nonrigid inners and separation of their two-copy parents

The actual examples `eq:ambiguous-inners` in `rem:saturation-boundaries`
of `shields-2026-skew-class-inflation.tex`.  One-copy ambiguity is proved
from the complete coarsening inventory.  The strict-seam parents are
distinguished by their actual total contractions, without assuming the
general saturation theorem.  Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative

/-- The first displayed nonrigid inner, in the full strictly separated parameter domain. -/
def ambiguousInnerZero : SaturationInner where
  k := 4
  k_pos := by decide
  r := ![4, 7, 4, 10, 7]
  c := 1
  d := 2
  c_lt_d := by decide
  first_bound := by decide
  last_bound := by decide
  interior_bound i hi hl := by fin_cases i <;> simp_all

/-- The second displayed inner, in the same standing domain. -/
def ambiguousInnerOne : SaturationInner where
  k := 4
  k_pos := by decide
  r := ![4, 10, 7, 4, 7]
  c := 1
  d := 2
  c_lt_d := by decide
  first_bound := by decide
  last_bound := by decide
  interior_bound i hi hl := by fin_cases i <;> simp_all

/-- Their actual one-copy deflated ribbons have identical coarsenings with multiplicity. -/
theorem ambiguous_inner_ribbon_eq :
    ribbonWord (List.ofFn (fun i => (ambiguousInnerOne.power 1 (by decide)).r i - 1)) =
      ribbonWord (List.ofFn (fun i => (ambiguousInnerZero.power 1 (by decide)).r i - 1)) := by
  apply (ribbon_eq_iff_coarseningPartitions _ _
    (by intro i; fin_cases i <;> decide)
    (by intro i; fin_cases i <;> decide)).mpr
  decide +kernel

/-- The two distinct actual one-copy inners have the same full Schur function. -/
theorem ambiguous_inner_schur_eq :
    (ambiguousInnerOne.power 1 (by decide)).toBetaDiagram.schur =
      (ambiguousInnerZero.power 1 (by decide)).toBetaDiagram.schur := by
  apply (constant_gap_equality_iff _ _ 1
    (ambiguousInnerOne.power_thick 1 (by decide))
    (ambiguousInnerZero.power_thick 1 (by decide))
    (ambiguousInnerOne.powerRows_above_gap 1)
    (ambiguousInnerZero.powerRows_above_gap 1) (fun _ => rfl) (fun _ => rfl)).mpr
  exact ambiguous_inner_ribbon_eq

/-- The one-copy equality is neither literal equality nor global rotation. -/
theorem ambiguous_inner_nonrotation :
    List.ofFn (ambiguousInnerOne.power 1 (by decide)).r ≠
        List.ofFn (ambiguousInnerZero.power 1 (by decide)).r ∧
      List.ofFn (ambiguousInnerOne.power 1 (by decide)).r ≠
        List.ofFn (ambiguousInnerZero.power 1 (by decide)).rotate.r := by
  decide +kernel

/-- One-copy endpoint recovery remains meaningful even when full rigidity fails. -/
theorem ambiguous_inner_endpoints :
    ((ambiguousInnerOne.power 1 (by decide)).r 0 ::ₘ
      (ambiguousInnerOne.power 1 (by decide)).r (Fin.last 4) ::ₘ 0 : Multiset ℕ) =
      ambiguousInnerZero.r 0 ::ₘ ambiguousInnerZero.r (Fin.last 4) ::ₘ 0 :=
  ambiguousInnerZero.power_mate_endpoints 1 (by decide)
    (ambiguousInnerOne.power 1 (by decide)) ambiguous_inner_schur_eq

/-- The next-length partition that distinguishes the two strictly overlapped powers. -/
def ambiguousMergeWitness : Multiset ℕ+ :=
  3 ::ₘ 3 ::ₘ 3 ::ₘ 6 ::ₘ 6 ::ₘ 8 ::ₘ 9 ::ₘ 15 ::ₘ 0

/-- The merger discrepancy is an exact multiplicity discrepancy, not a numeric evaluation. -/
theorem ambiguous_power_partition_counts :
    (coarseningPartitions
      (fun i => (ambiguousInnerZero.power 2 (by decide)).r i - 1)
      (by intro i; fin_cases i <;> decide)).count ambiguousMergeWitness = 1 ∧
    (coarseningPartitions
      (fun i => (ambiguousInnerOne.power 2 (by decide)).r i - 1)
      (by intro i; fin_cases i <;> decide)).count ambiguousMergeWitness = 2 := by
  decide +kernel

/-- Strictly overlapping the equal one-copy inners separates their actual power functions. -/
theorem ambiguous_power_schur_ne :
    (ambiguousInnerOne.power 2 (by decide)).toBetaDiagram.schur ≠
      (ambiguousInnerZero.power 2 (by decide)).toBetaDiagram.schur := by
  intro he
  have hr := ambiguousInnerZero.power_mate_ribbon 2 (by decide)
    (ambiguousInnerOne.power 2 (by decide)) he
  have hc := (ribbon_eq_iff_coarseningPartitions _ _
    (ambiguousInnerOne.powerRows_above_gap 2 |> fun h i => Nat.sub_pos_of_lt (h i))
    (ambiguousInnerZero.powerRows_above_gap 2 |> fun h i => Nat.sub_pos_of_lt (h i))).mp hr
  have hh := congrArg (fun M : Multiset (Multiset ℕ+) => M.count ambiguousMergeWitness) hc
  have hbad : (2 : ℕ) = 1 := ambiguous_power_partition_counts.2.symm.trans
    (hh.trans ambiguous_power_partition_counts.1)
  omega

/-- At a strictly larger seam, even the two-copy source functions are different.

**Differs from the paper's route.** Uses the actual total-contraction functions
and a specific coarsening multiplicity discrepancy, rather than full class rigidity. -/
theorem ambiguous_parent_schur_ne :
    (ambiguousInnerOne.diagram (Composition.ones 2) (by decide)).2.toBetaDiagram.schur ≠
      (ambiguousInnerZero.diagram (Composition.ones 2) (by decide)).2.toBetaDiagram.schur := by
  intro he
  have hz := ambiguousInnerZero.arbitrary_mate_total_contraction
    (Composition.ones 2) (by decide)
    (ambiguousInnerOne.diagram (Composition.ones 2) (by decide)).2 he
  have ho := ambiguousInnerOne.arbitrary_mate_total_contraction
    (Composition.ones 2) (by decide)
    (ambiguousInnerOne.diagram (Composition.ones 2) (by decide)).2 rfl
  exact ambiguous_power_schur_ne (ho.symm.trans hz)

/-- At equal joining and internal gaps, the two complete copies are joined literally. -/
def SaturationInner.equalGapDouble (A : SaturationInner) : Profile (A.k + A.k + 1) :=
  Profile.join A.profile A.profile A.c (A.row_above_gap _) (A.row_above_gap _)

private theorem profile_thick (A : SaturationInner) : Staircase.Thick A.profile := by
  intro j l hjl
  have he := congrArg Fin.val hjl
  simp only [Fin.val_succ, Fin.val_castSucc] at he
  have hl := l.isLt
  have hh := A.interior_bound j.succ (by simp)
    (by simp only [Fin.val_succ]; omega)
  change A.c + A.c < A.r j.succ
  omega

/-- Equal-gap doubling preserves the actual Hessenberg separation at both new incidences. -/
theorem SaturationInner.equalGapDouble_thick (A : SaturationInner) :
    Staircase.Thick A.equalGapDouble := by
  apply Profile.join_thick _ _ _ _ _ (profile_thick A) (profile_thick A)
  · intro j hj
    change A.c + A.c < A.r (Fin.last A.k)
    have := A.last_bound
    have := A.c_lt_d
    omega
  · intro j hj
    change A.c + A.c < A.r 0
    have := A.first_bound
    have := A.c_lt_d
    omega

/-- Every actual joining and internal gap equals the same original gap. -/
theorem SaturationInner.equalGapDouble_gaps (A : SaturationInner) (j) :
    A.equalGapDouble.g j = A.c := by
  change Profile.joinGaps A.profile A.profile A.c j = A.c
  unfold Profile.joinGaps
  split_ifs <;> rfl

/-- No row disappears on deflating the equal-gap double. -/
theorem SaturationInner.equalGapDouble_rows (A : SaturationInner) (i) :
    A.c < A.equalGapDouble.r i := by
  change A.c < Profile.joinRows A.profile A.profile i
  unfold Profile.joinRows
  split_ifs <;> exact A.row_above_gap _

/-- The two equal-gap parents retain the actual one-copy ambiguity. -/
theorem ambiguous_equal_gap_schur_eq :
    ambiguousInnerOne.equalGapDouble.toBetaDiagram.schur =
      ambiguousInnerZero.equalGapDouble.toBetaDiagram.schur := by
  apply (constant_gap_equality_iff _ _ 1
    ambiguousInnerOne.equalGapDouble_thick ambiguousInnerZero.equalGapDouble_thick
    ambiguousInnerOne.equalGapDouble_rows ambiguousInnerZero.equalGapDouble_rows
    ambiguousInnerOne.equalGapDouble_gaps ambiguousInnerZero.equalGapDouble_gaps).mpr
  have h1 : List.ofFn (fun i => ambiguousInnerOne.equalGapDouble.r i - 1) =
      [3, 9, 6, 3, 6, 3, 9, 6, 3, 6] := by decide +kernel
  have h0 : List.ofFn (fun i => ambiguousInnerZero.equalGapDouble.r i - 1) =
      [3, 6, 3, 9, 6, 3, 6, 3, 9, 6] := by decide +kernel
  rw [h1, h0]
  norm_num only [ribbonWord, ribbonTail]
  ring

/-- The equal-gap equality is a genuine nonrotation equality of full row words. -/
theorem ambiguous_equal_gap_nonrotation :
    List.ofFn ambiguousInnerOne.equalGapDouble.r ≠
        List.ofFn ambiguousInnerZero.equalGapDouble.r ∧
      List.ofFn ambiguousInnerOne.equalGapDouble.r ≠
        List.ofFn ambiguousInnerZero.equalGapDouble.rotate.r := by
  decide +kernel

/-- The two strictly separated parents are distinct and not global rotations either. -/
theorem ambiguous_parent_nonrotation :
    List.ofFn (ambiguousInnerOne.diagram (Composition.ones 2) (by decide)).2.r ≠
        List.ofFn (ambiguousInnerZero.diagram (Composition.ones 2) (by decide)).2.r ∧
      List.ofFn (ambiguousInnerOne.diagram (Composition.ones 2) (by decide)).2.r ≠
        List.ofFn (ambiguousInnerZero.diagram (Composition.ones 2) (by decide)).2.rotate.r := by
  decide +kernel

end SkewClassInflation
