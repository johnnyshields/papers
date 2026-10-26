/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewSchurReconstruction.StaircaseReversal

/-!
# The unbounded staircase locus family

Formalizes the exact family in "Reversal pairs on the locus"
(`subsec:locus-family`, `cor:locus-family`).  Actual prefix-times-tail cofactors,
parent square costs, and cancellation in the two zero polynomial relations give
the complete support, finite raw valuations, normalized positive floor,
minimizing shifts, and floor gap for every positive family parameter.  Sorry-free.
-/

namespace SkewSchurReconstruction

open scoped BigOperators

variable {N : ℕ}

/-- The explicit family word `(2,2^k,3^k,2)`. -/
def locusFamilyWord (k : ℕ) (i : Fin (2 * k + 2)) : ℕ :=
  if i.val ≤ k then 2 else if i.val ≤ 2 * k then 3 else 2

theorem locusFamilyWord_binary (k : ℕ) :
    ∀ i, locusFamilyWord k i = 2 ∨ locusFamilyWord k i = 3 := by
  intro i
  unfold locusFamilyWord
  split_ifs <;> simp

theorem locusFamilyWord_first (k : ℕ) : locusFamilyWord k ⟨0, by omega⟩ = 2 := by
  simp [locusFamilyWord]

theorem locusFamilyWord_last (k : ℕ) : locusFamilyWord k (Fin.last (2 * k + 1)) = 2 := by
  simp only [locusFamilyWord, Fin.val_last]
  split_ifs <;> omega

private theorem family_last_index (k : ℕ) :
    (⟨2 * k + 2 - 1, by omega⟩ : Fin (2 * k + 2)) = Fin.last (2 * k + 1) := by
  apply Fin.ext
  change 2 * k + 2 - 1 = 2 * k + 1
  omega

private theorem family_last_letter (k : ℕ) :
    locusFamilyWord k (⟨2 * k + 2 - 1, by omega⟩ : Fin (2 * k + 2)) = 2 := by
  rw [family_last_index]
  exact locusFamilyWord_last k

private abbrev familyOne (k : ℕ) : Fin (2 * k + 3) := ⟨1, by omega⟩

private abbrev familyTwo (k : ℕ) : Fin (2 * k + 3) := ⟨2, by omega⟩

private theorem square_weight_apply (i : ℕ) : squareWeight.weight i = (i : ℝ) ^ 2 := rfl

private theorem square_complete_valuation (a : ℤ) (ha : 0 ≤ a) :
    monomialValuation squareWeight.generatorWeight (complete a) =
      (((a.toNat : ℝ) ^ 2 : ℝ) : WithTop ℝ) := by
  simpa only [square_weight_apply] using complete_monomialValuation squareWeight a ha

private theorem square_ratio_kernel_valuation (d : ℤ) (hd : 0 ≤ d) :
    monomialValuation squareWeight.generatorWeight
      (complete (3 + d) - complete 1 * complete (2 + d)) =
        ((1 + ((2 + d).toNat : ℝ) ^ 2 : ℝ) : WithTop ℝ) := by
  have h := (boundary_ratio_kernel squareWeight 2 1 d
    (by norm_num) (by norm_num) hd).2.2
  norm_num only [Int.toNat_one] at h
  simpa only [square_weight_apply, Int.toNat_one, Nat.cast_one, one_pow,
    ← WithTop.coe_add] using h

theorem locusFamilyWord_nonpalindromic (k : ℕ) (hk : 0 < k) :
    locusFamilyWord k ≠ reversedWord (locusFamilyWord k) := by
  intro h
  have he := congrFun h (⟨1, by omega⟩ : Fin (2 * k + 2))
  change (if 1 ≤ k then 2 else if 1 ≤ 2 * k then 3 else 2) =
    (if 2 * k + 2 - (1 + 1) ≤ k then 2 else
      if 2 * k + 2 - (1 + 1) ≤ 2 * k then 3 else 2) at he
  split_ifs at he <;> omega

theorem locusFamily_diagrams_connected (k : ℕ) :
    (staircaseDiagram (locusFamilyWord k) (locusFamilyWord_binary k)).Connected :=
  staircase_connected _ _ (by omega)

theorem locusFamily_diagrams_not_translationEquivalent (k : ℕ) (hk : 0 < k) :
    ¬ TranslationEquivalent
      (staircaseDiagram (locusFamilyWord k) (locusFamilyWord_binary k))
      (staircaseDiagram (reversedWord (locusFamilyWord k))
        (reversedWord_binary _ (locusFamilyWord_binary k))) :=
  staircase_not_translationEquivalent _ _ _ _ (by omega) (locusFamilyWord_nonpalindromic k hk)

theorem locusFamily_ratioIdentity (k : ℕ) :
    RatioIdentity
      (gridDefect (staircaseDiagram (locusFamilyWord k) (locusFamilyWord_binary k))
        (staircaseDiagram (reversedWord (locusFamilyWord k))
          (reversedWord_binary _ (locusFamilyWord_binary k)))) 2 1 :=
  staircase_ratioIdentity _ _ (by omega) (locusFamilyWord_first k)
    (family_last_letter k)

theorem locusFamily_schurFunction_ne_reverse (k : ℕ) (hk : 0 < k) :
    (staircaseDiagram (locusFamilyWord k) (locusFamilyWord_binary k)).schurFunction ≠
      (staircaseDiagram (reversedWord (locusFamilyWord k))
        (reversedWord_binary _ (locusFamilyWord_binary k))).schurFunction :=
  staircase_schurFunction_ne_reverse _ _ (by omega) (locusFamilyWord_first k)
    (family_last_letter k) (locusFamilyWord_nonpalindromic k hk)

private theorem finite_interval_count {a b s : ℕ} (hb : b < s) :
    ((Finset.univ : Finset (Fin s)).filter (fun i => a ≤ i.val ∧ i.val ≤ b)).card =
      b + 1 - a := by
  classical
  have hcard :
      ((Finset.univ : Finset (Fin s)).filter (fun i => a ≤ i.val ∧ i.val ≤ b)).card =
        (Finset.Icc a b).card := by
    refine Finset.card_bij (fun i _ => i.val) ?_ ?_ ?_
    · intro i hi
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Icc] using hi
    · intro i _ j _ h
      exact Fin.ext h
    · intro i hi
      obtain ⟨ha, hi⟩ := Finset.mem_Icc.mp hi
      refine ⟨⟨i, by omega⟩, ?_, rfl⟩
      simp [ha, hi]
  rw [hcard]
  simp

theorem locusFamily_count_three (k : ℕ) :
    ((Finset.univ : Finset (Fin (2 * k + 2))).filter
      (fun i => locusFamilyWord k i = 3)).card = k := by
  have he :
      ((Finset.univ : Finset (Fin (2 * k + 2))).filter (fun i => locusFamilyWord k i = 3)) =
        Finset.univ.filter (fun i => k + 1 ≤ i.val ∧ i.val ≤ 2 * k) := by
    apply Finset.ext
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change ((if i.val ≤ k then 2 else if i.val ≤ 2 * k then 3 else 2) = 3) ↔
      (k + 1 ≤ i.val ∧ i.val ≤ 2 * k)
    split_ifs <;> omega
  rw [he, finite_interval_count (by omega)]
  omega

theorem locusFamily_square_sum (k : ℕ) :
    (∑ i : Fin (2 * k + 2), (locusFamilyWord k i) ^ 2) = 13 * k + 8 := by
  have ht : ∀ i : Fin (2 * k + 2),
      (locusFamilyWord k i) ^ 2 = 4 + 5 * (if locusFamilyWord k i = 3 then 1 else 0) := by
    intro i
    rcases locusFamilyWord_binary k i with h | h <;> norm_num [h]
  simp_rw [ht]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.card_filter, locusFamily_count_three]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_cast
  omega

theorem locusFamily_parent_square_energy (k : ℕ) :
    Diagram.parentAction squareWeight
      (staircaseDiagram (locusFamilyWord k) (locusFamilyWord_binary k)) 0 =
        13 * (k : ℝ) + 8 := by
  rw [Diagram.parentAction_zero squareWeight _ (locusFamily_diagrams_connected k)]
  simp only [staircase_rowLength]
  change (∑ i : Fin (2 * k + 2), ((locusFamilyWord k i : ℕ) : ℝ) ^ 2) = _
  have h := locusFamily_square_sum k
  exact_mod_cast h

theorem locusFamily_terminal_cofactor (k : ℕ) :
    (staircaseDiagram (locusFamilyWord k) (locusFamilyWord_binary k)).cofactor
      (Fin.last (2 * k + 2)) =
      complete 1 ^ k := by
  rw [staircase_cofactor_last _ _ (by omega) (locusFamilyWord_first k),
    staircase_terminal_product_count (locusFamilyWord k) (locusFamilyWord_binary k),
    locusFamily_count_three]
  have hs : (-1 : CompleteRing) ^ (2 * k + 2) = 1 := by
    rw [show 2 * k + 2 = 2 * (k + 1) by omega, pow_mul]
    norm_num
  rw [hs, one_mul]

theorem locusFamily_penultimate_cofactor (k : ℕ) :
    (staircaseDiagram (locusFamilyWord k) (locusFamilyWord_binary k)).cofactor
      (Fin.last (2 * k + 1)).castSucc = -complete 2 * complete 1 ^ k := by
  rw [staircase_cofactor_penultimate _ _ (by omega) (locusFamilyWord_first k)
    (locusFamilyWord_last k),
    staircase_terminal_product_count (locusFamilyWord k) (locusFamilyWord_binary k),
    locusFamily_count_three]
  have hs : (-1 : CompleteRing) ^ (2 * k + 1) = -1 := by
    rw [pow_add, pow_mul]
    norm_num
  rw [hs]
  ring

/-- Left member of the explicit staircase locus family. -/
def locusFamilyLeft (k : ℕ) : Diagram (2 * k + 2) :=
  staircaseDiagram (locusFamilyWord k) (locusFamilyWord_binary k)

/-- Right member of the family, with the reversed row-length word. -/
def locusFamilyRight (k : ℕ) : Diagram (2 * k + 2) :=
  staircaseDiagram (reversedWord (locusFamilyWord k))
    (reversedWord_binary _ (locusFamilyWord_binary k))

theorem locusFamilyRight_first (k : ℕ) : reversedWord (locusFamilyWord k) 0 = 2 := by
  simpa [reversedWord] using locusFamilyWord_last k

theorem locusFamilyLeft_connected (k : ℕ) : (locusFamilyLeft k).Connected :=
  locusFamily_diagrams_connected k

theorem locusFamilyRight_connected (k : ℕ) : (locusFamilyRight k).Connected :=
  staircase_connected _ (reversedWord_binary _ (locusFamilyWord_binary k)) (by omega)

@[simp] theorem locusFamilyLeft_capShift (k : ℕ) (j : Fin (2 * k + 3)) :
    (locusFamilyLeft k).capShift j = 2 * (j.val : ℤ) :=
  staircase_capShift _ _ (by omega) (locusFamilyWord_first k) j

@[simp] theorem locusFamilyRight_capShift (k : ℕ) (j : Fin (2 * k + 3)) :
    (locusFamilyRight k).capShift j = 2 * (j.val : ℤ) :=
  staircase_capShift _ _ (by omega) (locusFamilyRight_first k) j

/-- The square-weight difference of the actual parent cofactors at one column. -/
noncomputable def locusFamilyCostDifference (k : ℕ) (j : Fin (2 * k + 3)) : ℝ :=
  leastWeight squareWeight.generatorWeight ((locusFamilyLeft k).cofactor j) -
    leastWeight squareWeight.generatorWeight ((locusFamilyRight k).cofactor j)

theorem locusFamilyCostDifference_zero (k : ℕ) : locusFamilyCostDifference k 0 = 0 := by
  have h := staircase_square_initial_reversal (locusFamilyWord k) (locusFamilyWord_binary k)
    (by omega) (locusFamilyWord_first k) (family_last_letter k)
  exact sub_eq_zero.mpr h

theorem locusFamilyCostDifference_increment (k : ℕ) (i : Fin (2 * k + 2)) :
    locusFamilyCostDifference k i.succ - locusFamilyCostDifference k i.castSucc =
      4 * ((reversedWord (locusFamilyWord k) i : ℝ) - (locusFamilyWord k i : ℝ)) := by
  have hx := staircase_cofactor_square_increment (locusFamilyWord k) (locusFamilyWord_binary k)
    (by omega) (locusFamilyWord_first k) i
  have hy := staircase_cofactor_square_increment (reversedWord (locusFamilyWord k))
    (reversedWord_binary _ (locusFamilyWord_binary k)) (by omega) (locusFamilyRight_first k) i
  unfold locusFamilyCostDifference locusFamilyLeft locusFamilyRight
  linear_combination hx - hy

/-- Exact square-weight separation of the parent cofactors, including the two vanishing end gaps. -/
theorem locusFamilyCostDifference_eq (k : ℕ) (j : Fin (2 * k + 3)) :
    locusFamilyCostDifference k j =
      4 * ((min (j.val - 1) (2 * k + 1 - j.val) : ℕ) : ℝ) := by
  have hstep : ∀ l : ℕ, ∀ j : Fin (2 * k + 3), j.val = l →
      locusFamilyCostDifference k j = 4 * ((min (l - 1) (2 * k + 1 - l) : ℕ) : ℝ) := by
    intro l
    induction l with
    | zero =>
      intro j hj
      have he : j = 0 := Fin.ext hj
      subst j
      simp [locusFamilyCostDifference_zero]
    | succ l ih =>
      intro j hj
      have hjb := j.isLt
      let i : Fin (2 * k + 2) := ⟨l, by omega⟩
      have he : i.succ = j := by apply Fin.ext; dsimp [i]; omega
      have hprev := ih i.castSucc rfl
      have hinc := locusFamilyCostDifference_increment k i
      rw [← he]
      change locusFamilyCostDifference k i.succ =
        4 * ((min (l + 1 - 1) (2 * k + 1 - (l + 1)) : ℕ) : ℝ)
      by_cases h0 : l = 0
      · have hx : locusFamilyWord k i = 2 := by simp [locusFamilyWord, i, h0]
        have hy : reversedWord (locusFamilyWord k) i = 2 := by
          change (if 2 * k + 2 - (l + 1) ≤ k then 2 else
            if 2 * k + 2 - (l + 1) ≤ 2 * k then 3 else 2) = 2
          split_ifs <;> omega
        rw [hx, hy] at hinc
        simp only [h0] at hprev ⊢
        norm_num at hinc hprev ⊢
        linarith
      · by_cases hlow : l ≤ k
        · have hx : locusFamilyWord k i = 2 := by simp [locusFamilyWord, i, hlow]
          have hy : reversedWord (locusFamilyWord k) i = 3 := by
            change (if 2 * k + 2 - (l + 1) ≤ k then 2 else
              if 2 * k + 2 - (l + 1) ≤ 2 * k then 3 else 2) = 3
            split_ifs <;> omega
          rw [hx, hy] at hinc
          have ho : min (l - 1) (2 * k + 1 - l) = l - 1 := by omega
          have hn : min (l + 1 - 1) (2 * k + 1 - (l + 1)) = l := by omega
          have hc : (l : ℝ) = ((l - 1 : ℕ) : ℝ) + 1 := by
            exact_mod_cast (show l = (l - 1) + 1 by omega)
          rw [ho] at hprev
          rw [hn]
          norm_num at hinc
          linarith
        · by_cases hhigh : l ≤ 2 * k
          · have hx : locusFamilyWord k i = 3 := by simp [locusFamilyWord, i, hlow, hhigh]
            have hy : reversedWord (locusFamilyWord k) i = 2 := by
              change (if 2 * k + 2 - (l + 1) ≤ k then 2 else
                if 2 * k + 2 - (l + 1) ≤ 2 * k then 3 else 2) = 2
              split_ifs <;> omega
            rw [hx, hy] at hinc
            have ho : min (l - 1) (2 * k + 1 - l) = 2 * k + 1 - l := by omega
            have hn : min (l + 1 - 1) (2 * k + 1 - (l + 1)) = 2 * k - l := by omega
            have hc : ((2 * k + 1 - l : ℕ) : ℝ) = ((2 * k - l : ℕ) : ℝ) + 1 := by
              exact_mod_cast (show 2 * k + 1 - l = (2 * k - l) + 1 by omega)
            rw [ho] at hprev
            rw [hn]
            norm_num at hinc
            linarith
          · have hl : l = 2 * k + 1 := by dsimp [i] at *; omega
            have hx : locusFamilyWord k i = 2 := by simp [locusFamilyWord, i, hlow, hhigh]
            have hy : reversedWord (locusFamilyWord k) i = 2 := by
              change (if 2 * k + 2 - (l + 1) ≤ k then 2 else
                if 2 * k + 2 - (l + 1) ≤ 2 * k then 3 else 2) = 2
              split_ifs <;> omega
            rw [hx, hy] at hinc
            simp only [hl] at hprev ⊢
            norm_num at hinc hprev ⊢
            linarith
  exact hstep j.val j rfl

theorem locusFamily_gridDefect_at_column (k : ℕ) (j : Fin (2 * k + 3)) :
    gridDefect (locusFamilyLeft k) (locusFamilyRight k) (2 * (j.val : ℤ)) =
      (locusFamilyLeft k).cofactor j - (locusFamilyRight k).cofactor j := by
  have hx := (locusFamilyLeft k).cofactorGridVector_apply_capShift j
  have hy := (locusFamilyRight k).cofactorGridVector_apply_capShift j
  rw [locusFamilyLeft_capShift] at hx
  rw [locusFamilyRight_capShift] at hy
  simp only [gridDefect, Finsupp.sub_apply, hx, hy]

theorem locusFamily_middle_supported (k : ℕ) (j : Fin (2 * k + 3))
    (hlo : 2 ≤ j.val) (hhi : j.val ≤ 2 * k) :
    gridDefect (locusFamilyLeft k) (locusFamilyRight k) (2 * (j.val : ℤ)) ≠ 0 := by
  rw [locusFamily_gridDefect_at_column]
  apply sub_ne_zero.mpr
  intro he
  have hc := congrArg (leastWeight squareWeight.generatorWeight) he
  have hpos : 0 < min (j.val - 1) (2 * k + 1 - j.val) := by omega
  have hp : (0 : ℝ) < (min (j.val - 1) (2 * k + 1 - j.val) : ℕ) := by exact_mod_cast hpos
  have hd := locusFamilyCostDifference_eq k j
  unfold locusFamilyCostDifference at hd
  rw [hc, sub_self] at hd
  linarith

theorem locusFamily_zero_supported (k : ℕ) (hk : 0 < k) :
    gridDefect (locusFamilyLeft k) (locusFamilyRight k) 0 ≠ 0 := by
  have h := locusFamily_gridDefect_at_column k 0
  simp only [Fin.val_zero, Nat.cast_zero, mul_zero] at h
  rw [h]
  exact sub_ne_zero.mpr (locusFamily_schurFunction_ne_reverse k hk)

theorem locusFamily_terminal_defects_zero (k : ℕ) :
    gridDefect (locusFamilyLeft k) (locusFamilyRight k) (4 * k + 4) = 0 ∧
      gridDefect (locusFamilyLeft k) (locusFamilyRight k) (4 * k + 2) = 0 := by
  have he := staircase_terminal_cofactors_reverse (locusFamilyWord k) (locusFamilyWord_binary k)
    (by omega) (locusFamilyWord_first k) (locusFamilyWord_last k)
  have hlast := locusFamily_gridDefect_at_column k (Fin.last (2 * k + 2))
  have hpen := locusFamily_gridDefect_at_column k (Fin.last (2 * k + 1)).castSucc
  simp only [Fin.val_last, Fin.val_castSucc] at hlast hpen
  constructor
  · have hv : 2 * ((2 * k + 2 : ℕ) : ℤ) = 4 * (k : ℤ) + 4 := by
      push_cast
      ring
    rw [hv] at hlast
    exact hlast.trans (sub_eq_zero.mpr he.1)
  · have hv : 2 * ((2 * k + 1 : ℕ) : ℤ) = 4 * (k : ℤ) + 2 := by
      push_cast
      ring
    rw [hv] at hpen
    exact hpen.trans (sub_eq_zero.mpr he.2)

theorem locusFamily_square_costs_at_two (k : ℕ) (hk : 0 < k) :
    leastWeight squareWeight.generatorWeight ((locusFamilyLeft k).cofactor ⟨2, by omega⟩) =
        13 * (k : ℝ) ∧
    leastWeight squareWeight.generatorWeight ((locusFamilyRight k).cofactor ⟨2, by omega⟩) =
        13 * (k : ℝ) - 4 := by
  have hx0 := locusFamily_parent_square_energy k
  unfold Diagram.parentAction at hx0
  simp only [Diagram.capShift_zero, Int.toNat_zero, squareWeight.zero, add_zero] at hx0
  change leastWeight squareWeight.generatorWeight ((locusFamilyLeft k).cofactor 0) =
    13 * (k : ℝ) + 8 at hx0
  have hdiff0 := locusFamilyCostDifference_zero k
  unfold locusFamilyCostDifference at hdiff0
  have hxfirst := staircase_cofactor_square_increment (locusFamilyWord k) (locusFamilyWord_binary k)
    (by omega) (locusFamilyWord_first k) (0 : Fin (2 * k + 2))
  have hyfirst := staircase_cofactor_square_increment (reversedWord (locusFamilyWord k))
    (reversedWord_binary _ (locusFamilyWord_binary k)) (by omega) (locusFamilyRight_first k)
    (0 : Fin (2 * k + 2))
  have hxone := staircase_cofactor_square_increment (locusFamilyWord k) (locusFamilyWord_binary k)
    (by omega) (locusFamilyWord_first k) (⟨1, by omega⟩ : Fin (2 * k + 2))
  have hyone := staircase_cofactor_square_increment (reversedWord (locusFamilyWord k))
    (reversedWord_binary _ (locusFamilyWord_binary k)) (by omega) (locusFamilyRight_first k)
    (⟨1, by omega⟩ : Fin (2 * k + 2))
  have hxa : locusFamilyWord k (⟨1, by omega⟩ : Fin (2 * k + 2)) = 2 := by
    simp [locusFamilyWord, show 1 ≤ k by omega]
  have hya : reversedWord (locusFamilyWord k) (⟨1, by omega⟩ : Fin (2 * k + 2)) = 3 := by
    change (if 2 * k + 2 - (1 + 1) ≤ k then 2 else
      if 2 * k + 2 - (1 + 1) ≤ 2 * k then 3 else 2) = 3
    split_ifs <;> omega
  have hx0letter : locusFamilyWord k (0 : Fin (2 * k + 2)) = 2 := by
    have he : (0 : Fin (2 * k + 2)) = ⟨0, by omega⟩ := Fin.ext rfl
    rw [he]
    exact locusFamilyWord_first k
  rw [hx0letter] at hxfirst
  rw [locusFamilyRight_first] at hyfirst
  rw [hxa] at hxone
  rw [hya] at hyone
  change leastWeight _ ((locusFamilyLeft k).cofactor ⟨1, by omega⟩) -
    leastWeight _ ((locusFamilyLeft k).cofactor 0) = _ at hxfirst
  change leastWeight _ ((locusFamilyRight k).cofactor ⟨1, by omega⟩) -
    leastWeight _ ((locusFamilyRight k).cofactor 0) = _ at hyfirst
  change leastWeight _ ((locusFamilyLeft k).cofactor ⟨2, by omega⟩) -
    leastWeight _ ((locusFamilyLeft k).cofactor ⟨1, by omega⟩) = _ at hxone
  change leastWeight _ ((locusFamilyRight k).cofactor ⟨2, by omega⟩) -
    leastWeight _ ((locusFamilyRight k).cofactor ⟨1, by omega⟩) = _ at hyone
  norm_num at hxfirst hyfirst hxone hyone
  constructor <;> linarith

/-- The actual middle defect coordinate used in the family valuation census. -/
theorem locusFamily_defect_four_valuation (k : ℕ) (hk : 0 < k) :
    monomialValuation squareWeight.generatorWeight
      (gridDefect (locusFamilyLeft k) (locusFamilyRight k) 4) =
        ((13 * (k : ℝ) - 4 : ℝ) : WithTop ℝ) := by
  have hcost := locusFamily_square_costs_at_two k hk
  have hx := (locusFamilyLeft k).cofactor_ne_zero squareWeight (locusFamilyLeft_connected k)
    (⟨2, by omega⟩ : Fin (2 * k + 3))
  have hy := (locusFamilyRight k).cofactor_ne_zero squareWeight (locusFamilyRight_connected k)
    (⟨2, by omega⟩ : Fin (2 * k + 3))
  have hne : monomialValuation squareWeight.generatorWeight
      ((locusFamilyLeft k).cofactor ⟨2, by omega⟩) ≠
    monomialValuation squareWeight.generatorWeight
      ((locusFamilyRight k).cofactor ⟨2, by omega⟩) := by
    rw [monomialValuation_eq_coe hx, monomialValuation_eq_coe hy, hcost.1, hcost.2]
    intro h
    have hc := WithTop.coe_injective h
    linarith
  have hgrid := locusFamily_gridDefect_at_column k (⟨2, by omega⟩ : Fin (2 * k + 3))
  norm_num at hgrid
  rw [hgrid, monomialValuation_sub_eq_min hne, monomialValuation_eq_coe hx,
    monomialValuation_eq_coe hy, hcost.1, hcost.2]
  apply min_eq_right
  exact WithTop.coe_le_coe.mpr (by linarith)

/-- The shift set occurring as the actual family support at every positive scale. -/
noncomputable def locusFamilySupport (k : ℕ) : Finset ℤ :=
  (Finset.range (2 * k + 1)).image (fun j : ℕ => 2 * (j : ℤ))

theorem locusFamily_defect_support_subset (k : ℕ) :
    (gridDefect (locusFamilyLeft k) (locusFamilyRight k)).support ⊆ locusFamilySupport k := by
  intro d hd
  have hdn := Finsupp.mem_support_iff.mp hd
  have hj : ∃ j : Fin (2 * k + 3), 2 * (j.val : ℤ) = d := by
    by_cases hx : (locusFamilyLeft k).cofactorGridVector d = 0
    · have hy : (locusFamilyRight k).cofactorGridVector d ≠ 0 := by
        intro hy
        simp [gridDefect, hx, hy] at hdn
      obtain ⟨j, hj⟩ := (locusFamilyRight k).exists_capShift_of_gridVector_ne_zero d hy
      refine ⟨j, ?_⟩
      rwa [locusFamilyRight_capShift] at hj
    · obtain ⟨j, hj⟩ := (locusFamilyLeft k).exists_capShift_of_gridVector_ne_zero d hx
      refine ⟨j, ?_⟩
      rwa [locusFamilyLeft_capShift] at hj
  obtain ⟨j, hj⟩ := hj
  have hjb := j.isLt
  have hb : j.val ≤ 2 * k := by
    by_contra hb
    obtain he | he : j.val = 2 * k + 1 ∨ j.val = 2 * k + 2 := by omega
    · have hdv : d = 4 * k + 2 := by rw [← hj, he]; push_cast; ring
      rw [hdv, (locusFamily_terminal_defects_zero k).2] at hdn
      exact hdn rfl
    · have hdv : d = 4 * k + 4 := by rw [← hj, he]; push_cast; ring
      rw [hdv, (locusFamily_terminal_defects_zero k).1] at hdn
      exact hdn rfl
  exact Finset.mem_image.mpr ⟨j.val, Finset.mem_range.mpr (by omega), hj⟩

theorem locusFamily_defect_ne_zero (k : ℕ) (hk : 0 < k) :
    gridDefect (locusFamilyLeft k) (locusFamilyRight k) ≠ 0 := by
  intro h
  have hz := locusFamily_zero_supported k hk
  rw [h, Finsupp.zero_apply] at hz
  exact hz rfl

theorem locusFamily_lastDefectShift (k : ℕ) (hk : 0 < k) :
    lastDefectShift (locusFamilyLeft k) (locusFamilyRight k) (locusFamily_defect_ne_zero k hk) =
      4 * k := by
  let G := gridDefect (locusFamilyLeft k) (locusFamilyRight k)
  have he := lastDefectShift_mem (locusFamilyLeft k) (locusFamilyRight k)
    (locusFamily_defect_ne_zero k hk)
  have hs := locusFamily_defect_support_subset k he
  obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp hs
  have hjb := Finset.mem_range.mp hj
  have hlast := locusFamily_middle_supported k
    (⟨2 * k, by omega⟩ : Fin (2 * k + 3))
    (by change 2 ≤ 2 * k; omega) (by change 2 * k ≤ 2 * k; exact le_rfl)
  have hd : 2 * ((2 * k : ℕ) : ℤ) = 4 * k := by push_cast; ring
  rw [hd] at hlast
  have hle := le_lastDefectShift (locusFamilyLeft k) (locusFamilyRight k)
    (locusFamily_defect_ne_zero k hk) _ (Finsupp.mem_support_iff.mpr hlast)
  have hbound : 2 * (j : ℤ) ≤ 4 * k := by omega
  omega

theorem staircase_square_cost_lower_bound (w : Fin N → ℕ)
    (hw : ∀ i, w i = 2 ∨ w i = 3) (hN : 0 < N) (hfirst : w ⟨0, hN⟩ = 2)
    (j : Fin (N + 1)) :
    leastWeight squareWeight.generatorWeight ((staircaseDiagram w hw).cofactor 0) -
      8 * (j.val : ℝ) ≤
        leastWeight squareWeight.generatorWeight ((staircaseDiagram w hw).cofactor j) := by
  have hstep : ∀ l : ℕ, ∀ j : Fin (N + 1), j.val = l →
      leastWeight squareWeight.generatorWeight ((staircaseDiagram w hw).cofactor 0) -
        8 * (l : ℝ) ≤ leastWeight squareWeight.generatorWeight
          ((staircaseDiagram w hw).cofactor j) := by
    intro l
    induction l with
    | zero =>
      intro j hj
      have he : j = 0 := Fin.ext hj
      subst j
      simp
    | succ l ih =>
      intro j hj
      have hjb := j.isLt
      let i : Fin N := ⟨l, by omega⟩
      have he : i.succ = j := by apply Fin.ext; dsimp [i]; omega
      have hprev := ih i.castSucc rfl
      have hinc := staircase_cofactor_square_increment w hw hN hfirst i
      have hwi : (w i : ℝ) ≤ 3 := by rcases hw i with h | h <;> norm_num [h]
      rw [← he]
      push_cast
      linarith
  exact hstep j.val j rfl

theorem locusFamily_defect_valuation_lower_bound (k : ℕ) (j : Fin (2 * k + 3)) :
    ((13 * (k : ℝ) + 8 - 8 * (j.val : ℝ) : ℝ) : WithTop ℝ) ≤
      monomialValuation squareWeight.generatorWeight
        (gridDefect (locusFamilyLeft k) (locusFamilyRight k) (2 * (j.val : ℤ))) := by
  have hx0 := locusFamily_parent_square_energy k
  unfold Diagram.parentAction at hx0
  simp only [Diagram.capShift_zero, Int.toNat_zero, squareWeight.zero, add_zero] at hx0
  change leastWeight squareWeight.generatorWeight ((locusFamilyLeft k).cofactor 0) =
    13 * (k : ℝ) + 8 at hx0
  have hdiff0 := locusFamilyCostDifference_zero k
  unfold locusFamilyCostDifference at hdiff0
  have hy0 : leastWeight squareWeight.generatorWeight ((locusFamilyRight k).cofactor 0) =
      13 * (k : ℝ) + 8 := by linarith
  have hx := staircase_square_cost_lower_bound (locusFamilyWord k) (locusFamilyWord_binary k)
    (by omega) (locusFamilyWord_first k) j
  have hy := staircase_square_cost_lower_bound (reversedWord (locusFamilyWord k))
    (reversedWord_binary _ (locusFamilyWord_binary k)) (by omega) (locusFamilyRight_first k) j
  change leastWeight squareWeight.generatorWeight ((locusFamilyLeft k).cofactor 0) -
    8 * (j.val : ℝ) ≤ leastWeight squareWeight.generatorWeight
      ((locusFamilyLeft k).cofactor j) at hx
  change leastWeight squareWeight.generatorWeight ((locusFamilyRight k).cofactor 0) -
    8 * (j.val : ℝ) ≤ leastWeight squareWeight.generatorWeight
      ((locusFamilyRight k).cofactor j) at hy
  rw [hx0] at hx
  rw [hy0] at hy
  rw [locusFamily_gridDefect_at_column]
  have hval := monomialValuation_sub_ge squareWeight.generatorWeight
    ((locusFamilyLeft k).cofactor j) ((locusFamilyRight k).cofactor j)
  rw [monomialValuation_eq_coe ((locusFamilyLeft k).cofactor_ne_zero squareWeight
    (locusFamilyLeft_connected k) j),
    monomialValuation_eq_coe ((locusFamilyRight k).cofactor_ne_zero squareWeight
      (locusFamilyRight_connected k) j)] at hval
  exact (le_min (WithTop.coe_le_coe.mpr hx) (WithTop.coe_le_coe.mpr hy)).trans hval

/-- The actual column summand in the family's zeroth cap response. -/
noncomputable def locusFamilyZeroTerm (k : ℕ) (j : Fin (2 * k + 3)) : CompleteRing :=
  gridDefect (locusFamilyLeft k) (locusFamilyRight k) (2 * (j.val : ℤ)) * complete (2 * (j.val : ℤ))

/-- The actual column summand in the family's base-two, unit-cap ratio remainder. -/
noncomputable def locusFamilyRatioTerm (k : ℕ) (j : Fin (2 * k + 3)) : CompleteRing :=
  gridDefect (locusFamilyLeft k) (locusFamilyRight k) (2 * (j.val : ℤ)) *
    (complete (3 + 2 * (j.val : ℤ)) - complete 1 * complete (2 + 2 * (j.val : ℤ)))

theorem locusFamily_common_grid (k : ℕ) :
    ∀ j, (locusFamilyLeft k).capShift j = (locusFamilyRight k).capShift j := by
  intro j
  rw [locusFamilyLeft_capShift, locusFamilyRight_capShift]

theorem locusFamilyZeroTerm_sum (k : ℕ) : (∑ j, locusFamilyZeroTerm k j) = 0 := by
  have h := gridDefect_response_zero (locusFamilyLeft k) (locusFamilyRight k) (by omega) (by omega)
  rw [Diagram.gridDefect_response_eq_sum _ _ (locusFamily_common_grid k)] at h
  simpa only [locusFamilyZeroTerm, locusFamily_gridDefect_at_column, Diagram.cofactorDefect,
    locusFamilyLeft_capShift, zero_add] using h

theorem locusFamilyRatioTerm_sum (k : ℕ) : (∑ j, locusFamilyRatioTerm k j) = 0 := by
  have hr := locusFamily_ratioIdentity k
  have hz : gridResponse (gridDefect (locusFamilyLeft k) (locusFamilyRight k)) (2 + 1) -
      complete 1 * gridResponse (gridDefect (locusFamilyLeft k) (locusFamilyRight k)) 2 = 0 :=
    sub_eq_zero.mpr hr
  rw [Diagram.gridDefect_ratio_response_eq_sum _ _ (locusFamily_common_grid k)] at hz
  norm_num only at hz
  simpa only [locusFamilyRatioTerm, locusFamily_gridDefect_at_column, Diagram.cofactorDefect,
    locusFamilyLeft_capShift] using hz

theorem locusFamilyZeroTerm_valuation (k : ℕ) (j : Fin (2 * k + 3)) :
    monomialValuation squareWeight.generatorWeight (locusFamilyZeroTerm k j) =
      monomialValuation squareWeight.generatorWeight
        (gridDefect (locusFamilyLeft k) (locusFamilyRight k) (2 * (j.val : ℤ))) +
          ((4 * (j.val : ℝ) ^ 2 : ℝ) : WithTop ℝ) := by
  unfold locusFamilyZeroTerm
  rw [monomialValuation_mul, square_complete_valuation _ (by omega)]
  have hn : (2 * (j.val : ℤ)).toNat = 2 * j.val := by omega
  rw [hn]
  apply congrArg (fun c : ℝ =>
    monomialValuation squareWeight.generatorWeight
      (gridDefect (locusFamilyLeft k) (locusFamilyRight k) (2 * (j.val : ℤ))) +
        (c : WithTop ℝ))
  push_cast
  ring

theorem locusFamilyRatioTerm_valuation (k : ℕ) (j : Fin (2 * k + 3)) :
    monomialValuation squareWeight.generatorWeight (locusFamilyRatioTerm k j) =
      monomialValuation squareWeight.generatorWeight
        (gridDefect (locusFamilyLeft k) (locusFamilyRight k) (2 * (j.val : ℤ))) +
          ((1 + (2 + 2 * (j.val : ℝ)) ^ 2 : ℝ) : WithTop ℝ) := by
  unfold locusFamilyRatioTerm
  rw [monomialValuation_mul, square_ratio_kernel_valuation _ (by omega)]
  have hn : (2 + 2 * (j.val : ℤ)).toNat = 2 + 2 * j.val := by omega
  rw [hn]
  apply congrArg (fun c : ℝ =>
    monomialValuation squareWeight.generatorWeight
      (gridDefect (locusFamilyLeft k) (locusFamilyRight k) (2 * (j.val : ℤ))) +
        (c : WithTop ℝ))
  push_cast
  ring

theorem locusFamilyZeroTerm_later (k : ℕ) (j : Fin (2 * k + 3)) (hj : 3 ≤ j.val) :
    ((13 * (k : ℝ) + 12 : ℝ) : WithTop ℝ) <
      monomialValuation squareWeight.generatorWeight (locusFamilyZeroTerm k j) := by
  have hb := locusFamily_defect_valuation_lower_bound k j
  have hsum := add_le_add hb
    (show ((4 * (j.val : ℝ) ^ 2 : ℝ) : WithTop ℝ) ≤
      ((4 * (j.val : ℝ) ^ 2 : ℝ) : WithTop ℝ) from le_rfl)
  rw [← locusFamilyZeroTerm_valuation] at hsum
  have hjr : (3 : ℝ) ≤ (j.val : ℝ) := by exact_mod_cast hj
  apply lt_of_lt_of_le _ hsum
  rw [← WithTop.coe_add]
  apply WithTop.coe_lt_coe.mpr
  nlinarith

theorem locusFamilyRatioTerm_later (k : ℕ) (j : Fin (2 * k + 3)) (hj : 3 ≤ j.val) :
    ((13 * (k : ℝ) + 33 : ℝ) : WithTop ℝ) <
      monomialValuation squareWeight.generatorWeight (locusFamilyRatioTerm k j) := by
  have hb := locusFamily_defect_valuation_lower_bound k j
  have hsum := add_le_add hb
    (show ((1 + (2 + 2 * (j.val : ℝ)) ^ 2 : ℝ) : WithTop ℝ) ≤
      ((1 + (2 + 2 * (j.val : ℝ)) ^ 2 : ℝ) : WithTop ℝ) from le_rfl)
  rw [← locusFamilyRatioTerm_valuation] at hsum
  have hjr : (3 : ℝ) ≤ (j.val : ℝ) := by exact_mod_cast hj
  apply lt_of_lt_of_le _ hsum
  rw [← WithTop.coe_add]
  apply WithTop.coe_lt_coe.mpr
  nlinarith


private theorem first_three_cases (k : ℕ) (j : Fin (2 * k + 3)) (hj : j.val ≤ 2) :
    j = 0 ∨ j = familyOne k ∨ j = familyTwo k := by
  by_cases h0 : j.val = 0
  · exact Or.inl (Fin.ext h0)
  · by_cases h1 : j.val = 1
    · exact Or.inr (Or.inl (Fin.ext h1))
    · exact Or.inr (Or.inr (Fin.ext (show j.val = 2 by omega)))

private theorem no_unique_first_three (k : ℕ) (f : Fin (2 * k + 3) → CompleteRing)
    (hzero : (∑ j, f j) = 0) (T : ℝ)
    (hlater : ∀ j, 3 ≤ j.val → (T : WithTop ℝ) <
      monomialValuation squareWeight.generatorWeight (f j))
    (i : Fin (2 * k + 3)) (_hic : i.val ≤ 2)
    (hi : monomialValuation squareWeight.generatorWeight (f i) ≤ (T : WithTop ℝ))
    (hsmall : ∀ j, j.val ≤ 2 → j ≠ i →
      monomialValuation squareWeight.generatorWeight (f i) <
        monomialValuation squareWeight.generatorWeight (f j)) : False := by
  have hn : f i ≠ 0 := by
    intro hz
    rw [hz, monomialValuation_zero] at hi
    exact WithTop.not_top_le_coe T hi
  have hmin : ∀ j ∈ (Finset.univ : Finset (Fin (2 * k + 3))), j ≠ i →
      monomialValuation squareWeight.generatorWeight (f i) <
        monomialValuation squareWeight.generatorWeight (f j) := by
    intro j _ hji
    by_cases hj : j.val ≤ 2
    · exact hsmall j hj hji
    · exact lt_of_le_of_lt hi (hlater j (by omega))
  exact sum_ne_zero_of_unique_min Finset.univ f (Finset.mem_univ i) hn hmin hzero

private theorem balanced_three_profiles (k : ℕ) (f g : Fin (2 * k + 3) → CompleteRing)
    (hfzero : (∑ j, f j) = 0) (hgzero : (∑ j, g j) = 0) (a b t : ℝ)
    (hf0 : monomialValuation squareWeight.generatorWeight (f 0) = (a : WithTop ℝ))
    (hf1 : monomialValuation squareWeight.generatorWeight (f ⟨1, by omega⟩) =
      ((b + 4 : ℝ) : WithTop ℝ))
    (hf2 : monomialValuation squareWeight.generatorWeight (f ⟨2, by omega⟩) = (t : WithTop ℝ))
    (hg0 : monomialValuation squareWeight.generatorWeight (g 0) =
      ((a + 5 : ℝ) : WithTop ℝ))
    (hg1 : monomialValuation squareWeight.generatorWeight (g ⟨1, by omega⟩) =
      ((b + 17 : ℝ) : WithTop ℝ))
    (hg2 : monomialValuation squareWeight.generatorWeight (g ⟨2, by omega⟩) =
      ((t + 21 : ℝ) : WithTop ℝ))
    (hflater : ∀ j, 3 ≤ j.val → (t : WithTop ℝ) <
      monomialValuation squareWeight.generatorWeight (f j))
    (hglater : ∀ j, 3 ≤ j.val → ((t + 21 : ℝ) : WithTop ℝ) <
      monomialValuation squareWeight.generatorWeight (g j)) : a = t + 8 ∧ b = t - 4 := by
  have ha : min (b + 4) t < a := by
    by_contra h
    have hab : a ≤ b + 4 := (le_min_iff.mp (le_of_not_gt h)).1
    have hat : a ≤ t := (le_min_iff.mp (le_of_not_gt h)).2
    apply no_unique_first_three k g hgzero (t + 21) hglater 0 (by simp)
    · rw [hg0]
      exact WithTop.coe_le_coe.mpr (by linarith)
    · intro j hj hji
      rcases first_three_cases k j hj with he | he | he
      · exact (hji he).elim
      · subst j
        rw [hg0, hg1]
        exact WithTop.coe_lt_coe.mpr (by linarith)
      · subst j
        rw [hg0, hg2]
        exact WithTop.coe_lt_coe.mpr (by linarith)
  have hb : b + 4 = t := by
    rcases lt_trichotomy (b + 4) t with hlt | heq | hgt
    · have hba : b + 4 < a := by simpa [min_eq_left hlt.le] using ha
      exact (no_unique_first_three k f hfzero t hflater ⟨1, by omega⟩ (by simp)
        (by rw [hf1]; exact WithTop.coe_le_coe.mpr hlt.le) (by
          intro j hj hji
          rcases first_three_cases k j hj with he | he | he
          · subst j; rw [hf1, hf0]; exact WithTop.coe_lt_coe.mpr hba
          · exact (hji he).elim
          · subst j; rw [hf1, hf2]; exact WithTop.coe_lt_coe.mpr hlt)).elim
    · exact heq
    · have hta : t < a := by simpa [min_eq_right hgt.le] using ha
      exact (no_unique_first_three k f hfzero t hflater ⟨2, by omega⟩ (by simp)
        (by rw [hf2]) (by
          intro j hj hji
          rcases first_three_cases k j hj with he | he | he
          · subst j; rw [hf2, hf0]; exact WithTop.coe_lt_coe.mpr hta
          · subst j; rw [hf2, hf1]; exact WithTop.coe_lt_coe.mpr hgt
          · exact (hji he).elim)).elim
  have haa : a + 5 = t + 13 := by
    rcases lt_trichotomy (a + 5) (t + 13) with hlt | heq | hgt
    · exact (no_unique_first_three k g hgzero (t + 21) hglater 0 (by simp)
        (by rw [hg0]; exact WithTop.coe_le_coe.mpr (by linarith)) (by
          intro j hj hji
          rcases first_three_cases k j hj with he | he | he
          · exact (hji he).elim
          · subst j; rw [hg0, hg1]; exact WithTop.coe_lt_coe.mpr (by linarith)
          · subst j; rw [hg0, hg2]; exact WithTop.coe_lt_coe.mpr (by linarith))).elim
    · exact heq
    · exact (no_unique_first_three k g hgzero (t + 21) hglater ⟨1, by omega⟩ (by simp)
        (by rw [hg1]; exact WithTop.coe_le_coe.mpr (by linarith)) (by
          intro j hj hji
          rcases first_three_cases k j hj with he | he | he
          · subst j; rw [hg1, hg0]; exact WithTop.coe_lt_coe.mpr (by linarith)
          · exact (hji he).elim
          · subst j; rw [hg1, hg2]; exact WithTop.coe_lt_coe.mpr (by linarith))).elim
  constructor <;> linarith

private theorem family_leading_terms (k : ℕ) (hk : 0 < k) :
    let a := leastWeight squareWeight.generatorWeight
      (gridDefect (locusFamilyLeft k) (locusFamilyRight k) 0)
    monomialValuation squareWeight.generatorWeight (locusFamilyZeroTerm k 0) = (a : WithTop ℝ) ∧
    monomialValuation squareWeight.generatorWeight (locusFamilyRatioTerm k 0) =
      ((a + 5 : ℝ) : WithTop ℝ) ∧
    monomialValuation squareWeight.generatorWeight (locusFamilyZeroTerm k ⟨2, by omega⟩) =
      ((13 * (k : ℝ) + 12 : ℝ) : WithTop ℝ) ∧
    monomialValuation squareWeight.generatorWeight (locusFamilyRatioTerm k ⟨2, by omega⟩) =
      ((13 * (k : ℝ) + 33 : ℝ) : WithTop ℝ) := by
  dsimp
  have hz := monomialValuation_eq_coe (w := squareWeight.generatorWeight)
    (locusFamily_zero_supported k hk)
  have ht := locusFamily_defect_four_valuation k hk
  constructor
  · rw [locusFamilyZeroTerm_valuation]
    norm_num
    exact hz
  constructor
  · rw [locusFamilyRatioTerm_valuation]
    norm_num
    exact hz
  constructor
  · rw [locusFamilyZeroTerm_valuation]
    norm_num
    rw [ht]
    simpa only [WithTop.coe_add, WithTop.coe_mul, WithTop.coe_natCast,
      WithTop.coe_ofNat] using congrArg (fun x : ℝ => (x : WithTop ℝ))
        (show 13 * (k : ℝ) - 4 + 16 = 13 * (k : ℝ) + 12 by ring)
  · rw [locusFamilyRatioTerm_valuation]
    norm_num
    rw [ht]
    simpa only [WithTop.coe_add, WithTop.coe_mul, WithTop.coe_natCast,
      WithTop.coe_ofNat] using congrArg (fun x : ℝ => (x : WithTop ℝ))
        (show 13 * (k : ℝ) - 4 + 37 = 13 * (k : ℝ) + 33 by ring)

/-- The first positive defect is forced by the two actual zero polynomial relations. -/
theorem locusFamily_one_supported (k : ℕ) (hk : 0 < k) :
    gridDefect (locusFamilyLeft k) (locusFamilyRight k) 2 ≠ 0 := by
  intro hz
  let a := leastWeight squareWeight.generatorWeight
    (gridDefect (locusFamilyLeft k) (locusFamilyRight k) 0)
  obtain ⟨hf0, hg0, hf2, hg2⟩ := family_leading_terms k hk
  have hf1 : monomialValuation squareWeight.generatorWeight
      (locusFamilyZeroTerm k ⟨1, by omega⟩) = ⊤ := by
    rw [locusFamilyZeroTerm_valuation]
    norm_num
    simp [hz]
  have hg1 : monomialValuation squareWeight.generatorWeight
      (locusFamilyRatioTerm k ⟨1, by omega⟩) = ⊤ := by
    rw [locusFamilyRatioTerm_valuation]
    norm_num
    simp [hz]
  by_cases ha : a ≤ 13 * (k : ℝ) + 12
  · apply no_unique_first_three k (locusFamilyRatioTerm k) (locusFamilyRatioTerm_sum k)
      (13 * (k : ℝ) + 33) (locusFamilyRatioTerm_later k) 0 (by simp)
    · rw [hg0]
      exact WithTop.coe_le_coe.mpr (by dsimp [a] at ha; linarith)
    · intro j hj hji
      rcases first_three_cases k j hj with he | he | he
      · exact (hji he).elim
      · subst j
        rw [hg0, hg1]
        exact WithTop.coe_lt_top _
      · subst j
        rw [hg0, hg2]
        exact WithTop.coe_lt_coe.mpr (by dsimp [a] at ha; linarith)
  · apply no_unique_first_three k (locusFamilyZeroTerm k) (locusFamilyZeroTerm_sum k)
      (13 * (k : ℝ) + 12) (locusFamilyZeroTerm_later k) ⟨2, by omega⟩ (by simp)
    · rw [hf2]
    · intro j hj hji
      rcases first_three_cases k j hj with he | he | he
      · subst j
        rw [hf2, hf0]
        exact WithTop.coe_lt_coe.mpr (by dsimp [a] at ha; linarith)
      · subst j
        rw [hf2, hf1]
        exact WithTop.coe_lt_top _
      · exact (hji he).elim

/-- Exact actual defect valuations at the first two columns, with no ratio-gap input. -/
theorem locusFamily_leading_valuations (k : ℕ) (hk : 0 < k) :
    monomialValuation squareWeight.generatorWeight
      (gridDefect (locusFamilyLeft k) (locusFamilyRight k) 0) =
        ((13 * (k : ℝ) + 20 : ℝ) : WithTop ℝ) ∧
    monomialValuation squareWeight.generatorWeight
      (gridDefect (locusFamilyLeft k) (locusFamilyRight k) 2) =
        ((13 * (k : ℝ) + 8 : ℝ) : WithTop ℝ) := by
  let a := leastWeight squareWeight.generatorWeight
    (gridDefect (locusFamilyLeft k) (locusFamilyRight k) 0)
  let b := leastWeight squareWeight.generatorWeight
    (gridDefect (locusFamilyLeft k) (locusFamilyRight k) 2)
  obtain ⟨hf0, hg0, hf2, hg2⟩ := family_leading_terms k hk
  have hv1 := monomialValuation_eq_coe (w := squareWeight.generatorWeight)
    (locusFamily_one_supported k hk)
  have hf1 : monomialValuation squareWeight.generatorWeight (locusFamilyZeroTerm k ⟨1, by omega⟩) =
      ((b + 4 : ℝ) : WithTop ℝ) := by
    rw [locusFamilyZeroTerm_valuation]
    norm_num
    exact hv1
  have hg1 : monomialValuation squareWeight.generatorWeight (locusFamilyRatioTerm k ⟨1, by omega⟩) =
      ((b + 17 : ℝ) : WithTop ℝ) := by
    rw [locusFamilyRatioTerm_valuation]
    norm_num
    exact hv1
  have he21 : (13 * (k : ℝ) + 12) + 21 = 13 * (k : ℝ) + 33 := by ring
  rw [← he21] at hg2
  have hglater := locusFamilyRatioTerm_later k
  rw [← he21] at hglater
  have hab := balanced_three_profiles k (locusFamilyZeroTerm k) (locusFamilyRatioTerm k)
    (locusFamilyZeroTerm_sum k) (locusFamilyRatioTerm_sum k) a b (13 * (k : ℝ) + 12)
    hf0 hf1 hf2 hg0 hg1 hg2 (locusFamilyZeroTerm_later k) hglater
  constructor
  · rw [monomialValuation_eq_coe (locusFamily_zero_supported k hk)]
    change (a : WithTop ℝ) = _
    rw [hab.1]
    congr 1
    ring
  · rw [hv1]
    change (b : WithTop ℝ) = _
    rw [hab.2]
    congr 1
    ring

/-- The exact union-grid support of `cor:locus-family`. -/
theorem locusFamily_defect_support (k : ℕ) (hk : 0 < k) :
    (gridDefect (locusFamilyLeft k) (locusFamilyRight k)).support = locusFamilySupport k := by
  apply Finset.Subset.antisymm (locusFamily_defect_support_subset k)
  intro d hd
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hd
  have hb := Finset.mem_range.mp hj
  apply Finsupp.mem_support_iff.mpr
  by_cases h0 : j = 0
  · subst j
    simpa using locusFamily_zero_supported k hk
  · by_cases h1 : j = 1
    · subst j
      simpa using locusFamily_one_supported k hk
    · exact locusFamily_middle_supported k (⟨j, by omega⟩ : Fin (2 * k + 3))
        (by change 2 ≤ j; omega) (by change j ≤ 2 * k; omega)

theorem locusFamily_action_eq_zeroTerm (k : ℕ) (j : Fin (2 * k + 3)) :
    Diagram.defectAction squareWeight (locusFamilyLeft k) (locusFamilyRight k) j =
      monomialValuation squareWeight.generatorWeight (locusFamilyZeroTerm k j) := by
  rw [locusFamilyZeroTerm_valuation]
  unfold Diagram.defectAction Diagram.cofactorDefect
  rw [locusFamily_gridDefect_at_column, locusFamilyLeft_capShift]
  have hn : (2 * (j.val : ℤ)).toNat = 2 * j.val := by omega
  rw [hn, square_weight_apply]
  apply congrArg (fun c : ℝ =>
    monomialValuation squareWeight.generatorWeight
      ((locusFamilyLeft k).cofactor j - (locusFamilyRight k).cofactor j) + (c : WithTop ℝ))
  push_cast
  ring

theorem locusFamily_positive_floor (k : ℕ) (hk : 0 < k) :
    Diagram.positiveFloor squareWeight (locusFamilyLeft k) (locusFamilyRight k) =
      ((13 * (k : ℝ) + 12 : ℝ) : WithTop ℝ) := by
  have hf1 : monomialValuation squareWeight.generatorWeight (locusFamilyZeroTerm k ⟨1, by omega⟩) =
      ((13 * (k : ℝ) + 12 : ℝ) : WithTop ℝ) := by
    rw [locusFamilyZeroTerm_valuation]
    norm_num
    rw [(locusFamily_leading_valuations k hk).2]
    simpa only [WithTop.coe_add, WithTop.coe_mul, WithTop.coe_natCast,
      WithTop.coe_ofNat] using congrArg (fun x : ℝ => (x : WithTop ℝ))
        (show 13 * (k : ℝ) + 8 + 4 = 13 * (k : ℝ) + 12 by ring)
  have hf2 := (family_leading_terms k hk).2.2.1
  unfold Diagram.positiveFloor
  apply le_antisymm
  · have h := Finset.inf_le (f := Diagram.defectAction squareWeight (locusFamilyLeft k)
      (locusFamilyRight k))
      (show (⟨1, by omega⟩ : Fin (2 * k + 3)) ∈ Finset.univ.filter (fun j => 0 < j.val) by simp)
    rwa [locusFamily_action_eq_zeroTerm, hf1] at h
  · apply Finset.le_inf
    intro j hj
    have hp : 0 < j.val := by simpa using hj
    rw [locusFamily_action_eq_zeroTerm]
    by_cases h1 : j.val = 1
    · have he : j = ⟨1, by omega⟩ := Fin.ext h1
      rw [he, hf1]
    · by_cases h2 : j.val = 2
      · have he : j = ⟨2, by omega⟩ := Fin.ext h2
        rw [he, hf2]
      · exact (locusFamilyZeroTerm_later k j (by omega)).le

theorem locusFamily_floor_gap (k : ℕ) (hk : 0 < k) :
    monomialValuation squareWeight.generatorWeight
      (gridDefect (locusFamilyLeft k) (locusFamilyRight k) 0) =
        Diagram.positiveFloor squareWeight (locusFamilyLeft k) (locusFamilyRight k) +
          ((8 : ℝ) : WithTop ℝ) := by
  rw [(locusFamily_leading_valuations k hk).1, locusFamily_positive_floor k hk,
    ← WithTop.coe_add]
  congr 1
  ring

theorem locusFamily_positive_minimizer_columns (k : ℕ) (hk : 0 < k) :
    Finset.univ.filter (fun j : Fin (2 * k + 3) =>
      0 < j.val ∧ Diagram.defectAction squareWeight (locusFamilyLeft k) (locusFamilyRight k) j =
        Diagram.positiveFloor squareWeight (locusFamilyLeft k) (locusFamilyRight k)) =
      {⟨1, by omega⟩, ⟨2, by omega⟩} := by
  classical
  have h1 : Diagram.defectAction squareWeight (locusFamilyLeft k) (locusFamilyRight k)
      ⟨1, by omega⟩ = ((13 * (k : ℝ) + 12 : ℝ) : WithTop ℝ) := by
    rw [locusFamily_action_eq_zeroTerm, locusFamilyZeroTerm_valuation]
    norm_num
    rw [(locusFamily_leading_valuations k hk).2]
    simpa only [WithTop.coe_add, WithTop.coe_mul, WithTop.coe_natCast,
      WithTop.coe_ofNat] using congrArg (fun x : ℝ => (x : WithTop ℝ))
        (show 13 * (k : ℝ) + 8 + 4 = 13 * (k : ℝ) + 12 by ring)
  have h2 : Diagram.defectAction squareWeight (locusFamilyLeft k) (locusFamilyRight k)
      ⟨2, by omega⟩ = ((13 * (k : ℝ) + 12 : ℝ) : WithTop ℝ) := by
    rw [locusFamily_action_eq_zeroTerm]
    exact (family_leading_terms k hk).2.2.1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hp, he⟩
    by_cases hval1 : j.val = 1
    · exact Or.inl (Fin.ext hval1)
    · by_cases hval2 : j.val = 2
      · exact Or.inr (Fin.ext hval2)
      · have hlt := locusFamilyZeroTerm_later k j (by omega)
        rw [← locusFamily_action_eq_zeroTerm, he, locusFamily_positive_floor k hk] at hlt
        exact (lt_irrefl _ hlt).elim
  · rintro (rfl | rfl)
    · exact ⟨by simp, by rw [h1, locusFamily_positive_floor k hk]⟩
    · exact ⟨by simp, by rw [h2, locusFamily_positive_floor k hk]⟩

/-- The exact positive minimizing shift set T₀⁺ is `{2,4}`. -/
theorem locusFamily_positive_minimizer_shifts (k : ℕ) (hk : 0 < k) :
    (Finset.univ.filter (fun j : Fin (2 * k + 3) =>
      0 < j.val ∧ Diagram.defectAction squareWeight (locusFamilyLeft k) (locusFamilyRight k) j =
        Diagram.positiveFloor squareWeight (locusFamilyLeft k) (locusFamilyRight k))).image
      (locusFamilyLeft k).capShift = {(2 : ℤ), 4} := by
  rw [locusFamily_positive_minimizer_columns k hk]
  simp only [Finset.image_insert, Finset.image_singleton, locusFamilyLeft_capShift,
    Nat.cast_ofNat]
  norm_num

/-- The exact family support has `2*k` positive shifts. -/
theorem locusFamily_positive_support_card (k : ℕ) (hk : 0 < k) :
    ((gridDefect (locusFamilyLeft k) (locusFamilyRight k)).support.filter (fun d => 0 < d)).card =
      2 * k := by
  classical
  rw [locusFamily_defect_support k hk]
  have he : (locusFamilySupport k).filter (fun d => 0 < d) =
      ((Finset.range (2 * k + 1)).erase 0).image (fun j : ℕ => 2 * (j : ℤ)) := by
    ext d
    simp only [locusFamilySupport, Finset.mem_filter, Finset.mem_image, Finset.mem_erase,
      Finset.mem_range]
    constructor
    · rintro ⟨⟨j, hj, rfl⟩, hp⟩
      refine ⟨j, ⟨?_, hj⟩, rfl⟩
      omega
    · rintro ⟨j, ⟨hj0, hj⟩, rfl⟩
      exact ⟨⟨j, hj, rfl⟩, by omega⟩
  rw [he]
  have hi : Function.Injective (fun j : ℕ => 2 * (j : ℤ)) := by
    intro i j hij
    change (2 : ℤ) * (i : ℤ) = 2 * (j : ℤ) at hij
    exact_mod_cast (show (i : ℤ) = (j : ℤ) by omega)
  rw [Finset.card_image_of_injective _ hi,
    Finset.card_erase_of_mem (show 0 ∈ Finset.range (2 * k + 1) by simp)]
  simp

end SkewSchurReconstruction
