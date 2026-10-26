/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewSchurReconstruction.PrefixMinors
import SkewSchurReconstruction.CofactorMoments
import SkewSchurReconstruction.GeneratorMonomials

/-!
# Prefix elimination for two-cofactor reconstruction

Exact prefix residuals and the initial reconstruction data in "Reconstruction from the
first-row deletion" (`subsec:child-separation`, `lem:two-cofactor-reconstruction`).
All observations are actual determinants. Sorry-free.
-/

namespace SkewSchurReconstruction
namespace Diagram

open scoped BigOperators

theorem cofactor_zero_initialForm {n : ℕ} (X : Diagram n) (hX : X.Connected) :
    initialForm squareWeight.generatorWeight (X.cofactor 0) =
      (X.rowLengthList.map (fun k : ℕ => complete (k : ℤ))).prod := by
  rw [cofactor_initialForm squareWeight X hX]
  simp only [Fin.val_zero, pow_zero, one_mul, rowLengthList, List.map_ofFn, List.prod_ofFn]
  apply Finset.prod_congr rfl
  intro i _
  congr 1
  simpa [peelIndex] using (X.rowLength_eq_coordinates i).symm

/-- The first observation determines the unknown number of nonempty rows. -/
theorem row_count_eq_of_cofactor_zero_eq {n m : ℕ} (X : Diagram n) (Y : Diagram m)
    (hX : X.Connected) (hY : Y.Connected) (h0 : X.cofactor 0 = Y.cofactor 0) : n = m := by
  have hi := congrArg (initialForm squareWeight.generatorWeight) h0
  rw [cofactor_zero_initialForm X hX, cofactor_zero_initialForm Y hY] at hi
  have hc := length_eq_of_prod_complete_eq X.rowLengthList Y.rowLengthList
    X.rowLengthList_pos Y.rowLengthList_pos hi
  simpa only [rowLengthList, List.length_ofFn] using hc

/-- The first two observations determine the first nonzero cap shift without a shared grid. -/
theorem capShift_one_eq_of_two_cofactors_eq {n m : ℕ}
    (X : Diagram (n + 1)) (Y : Diagram (m + 1))
    (hX : X.Connected) (hY : Y.Connected)
    (h0 : X.cofactor 0 = Y.cofactor 0) (h1 : X.cofactor 1 = Y.cofactor 1) :
    X.capShift 1 = Y.capShift 1 := by
  have hd : X.cofactorDegreeDrop 0 = Y.cofactorDegreeDrop 0 := by
    simp only [cofactorDegreeDrop, Fin.castSucc_zero, Fin.succ_zero_eq_one,
      cofactorDegree, h0, h1]
  rw [cofactorDegreeDrop_eq X hX, cofactorDegreeDrop_eq Y hY,
    degreeDrop_eq_grid, degreeDrop_eq_grid] at hd
  simpa using hd

/-- A single-row parent is recovered from the two observations, including translation. -/
theorem translationEquivalent_single_row_of_two_cofactors_eq
    (X Y : Diagram 1) (hX : X.Connected) (hY : Y.Connected)
    (h0 : X.cofactor 0 = Y.cofactor 0) (h1 : X.cofactor 1 = Y.cofactor 1) :
    TranslationEquivalent X Y := by
  have hc := capShift_one_eq_of_two_cofactors_eq X Y hX hY h0 h1
  apply translationEquivalent_of_coordinates X Y
  · intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    change X.rowParam ⟨0, by omega⟩ = Y.rowParam ⟨0, by omega⟩
    rw [rowParam_zero X (by omega), rowParam_zero Y (by omega)]
  · intro j
    fin_cases j <;> simp_all

/-- The first `k+1` rows used by the prefix functional. -/
def prefixRows {n : ℕ} (k : ℕ) (hk : k + 1 < n) : Fin (k + 1) → Fin n :=
  fun i => ⟨i.val, by omega⟩

/-- The fixed prefix columns are `2,...,k+1`; the remaining column is variable. -/
def prefixColumns {n : ℕ} (k : ℕ) (hk : k + 1 < n) : Fin k → Fin (n + 1) :=
  fun i => ⟨i.val + 2, by omega⟩

/-- The manuscript's `T_j` with `k+1` prefix rows. -/
noncomputable def prefixMinor {n : ℕ} (X : Diagram n) (k : ℕ) (hk : k + 1 < n)
    (j : Fin (n + 1)) : CompleteRing :=
  columnPrefixMinor X.capMatrix (prefixRows k hk) (prefixColumns k hk) j

/-- The prefix residual uses only the first two observed cofactors. -/
noncomputable def prefixResidual {n : ℕ} (X : Diagram n) (k : ℕ) (hk : k + 1 < n) :
    CompleteRing :=
  X.prefixMinor k hk 0 * X.cofactor 0 + X.prefixMinor k hk 1 * X.cofactor 1

theorem prefixMinor_eq_zero_of_middle {n : ℕ} (X : Diagram n) (k : ℕ)
    (hk : k + 1 < n) (j : Fin (n + 1)) (hj0 : 2 ≤ j.val) (hjk : j.val ≤ k + 1) :
    X.prefixMinor k hk j = 0 := by
  let i : Fin k := ⟨j.val - 2, by omega⟩
  have hj : prefixColumns k hk i = j := by
    apply Fin.ext
    simp only [prefixColumns, i]
    omega
  rw [prefixMinor, ← hj]
  exact columnPrefixMinor_eq_zero_of_repeated X.capMatrix (prefixRows k hk)
    (prefixColumns k hk) i

/-- The exact residual is the negative tail; no initial-form formula is assumed. -/
theorem prefixResidual_eq_neg_tail {n : ℕ} (X : Diagram n) (k : ℕ)
    (hk : k + 1 < n) :
    X.prefixResidual k hk =
      -∑ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => k + 2 ≤ j.val),
        X.prefixMinor k hk j * X.cofactor j := by
  classical
  let : NeZero n := ⟨by omega⟩
  have hval1 : (1 : Fin (n + 1)).val = 1 := by
    change 1 % (n + 1) = 1
    exact Nat.mod_eq_of_lt (by omega)
  have hr := columnPrefixMinor_cofactor_relation X.capMatrix
    (prefixRows k hk) (prefixColumns k hk)
  have he : ∀ j : Fin (n + 1), X.cofactor j * X.prefixMinor k hk j =
      (if j = 0 then X.prefixMinor k hk 0 * X.cofactor 0 else 0) +
      (if j = 1 then X.prefixMinor k hk 1 * X.cofactor 1 else 0) +
      (if k + 2 ≤ j.val then X.prefixMinor k hk j * X.cofactor j else 0) := by
    intro j
    by_cases hj0 : j = 0
    · subst j
      simp [show ¬k + 2 ≤ 0 by omega, mul_comm]
    · by_cases hj1 : j = 1
      · subst j
        simp [Nat.mod_eq_of_lt (show 1 < n + 1 by omega), mul_comm]
      · by_cases hjk : k + 2 ≤ j.val
        · simp [hj0, hj1, hjk, mul_comm]
        · have hmiddle : X.prefixMinor k hk j = 0 := by
            apply prefixMinor_eq_zero_of_middle X k hk j
            · have h0 : j.val ≠ 0 := by intro h; exact hj0 (Fin.ext h)
              have h1 : j.val ≠ 1 := by
                intro h
                apply hj1
                apply Fin.ext
                rw [hval1]
                exact h
              omega
            · omega
          simp [hj0, hj1, hjk, hmiddle]
  change (∑ j, X.cofactor j * X.prefixMinor k hk j) = 0 at hr
  simp_rw [he] at hr
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hr
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hr
  rw [← Finset.sum_filter] at hr
  unfold prefixResidual
  exact eq_neg_of_add_eq_zero_left hr

private theorem prefixRows_strictMono {n k : ℕ} (hk : k + 1 < n) :
    StrictMono (prefixRows k hk) := by
  intro a b hab
  exact hab

private theorem prefixTailColumns_strictMono {n k : ℕ} (hk : k + 1 < n)
    (j : Fin (n + 1)) (hj : k + 2 ≤ j.val) :
    StrictMono (Fin.snoc (prefixColumns k hk) j) := by
  intro a b hab
  cases a using Fin.lastCases with
  | last =>
      have ha := b.isLt
      have hab' : k < b.val := hab
      omega
  | cast a =>
      cases b using Fin.lastCases with
      | last =>
          rw [Fin.snoc_castSucc, Fin.snoc_last]
          change a.val + 2 < j.val
          omega
      | cast b =>
          rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
          change a.val + 2 < b.val + 2
          have hab' : a.val < b.val := hab
          omega

private theorem prefixTail_feasible {n k : ℕ} (X : Diagram n) (hX : X.Connected)
    (hk : k + 1 < n) (j : Fin (n + 1)) (hj : k + 2 ≤ j.val) :
    ∀ i : Fin (k + 1), X.rowParam (prefixRows k hk i) ≤
      X.capShift ((Fin.snoc (prefixColumns k hk) j :
        Fin (k + 1) → Fin (n + 1)) i) := by
  intro i
  have hd := X.diagonal_feasible hX (prefixRows k hk i)
  apply hd.trans
  apply X.capShift_strictMono.monotone
  cases i using Fin.lastCases with
  | last =>
      rw [Fin.snoc_last]
      change k ≤ j.val
      omega
  | cast i =>
      rw [Fin.snoc_castSucc]
      change i.val ≤ i.val + 2
      omega

/-- The ordered tail minor is a genuine staircase determinant. -/
theorem prefixMinor_eq_staircase {n : ℕ} (X : Diagram n) (k : ℕ)
    (hk : k + 1 < n) (j : Fin (n + 1)) :
    X.prefixMinor k hk j =
      (staircaseMatrix (fun i => X.rowParam (prefixRows k hk i))
        (fun i => X.capShift ((Fin.snoc (prefixColumns k hk) j :
          Fin (k + 1) → Fin (n + 1)) i))).det := by
  congr 1

/-- Strict Monge computes the tail minor's actual initial monomial. -/
theorem prefixMinor_initialForm {n : ℕ} (w : ConvexWeight) (X : Diagram n)
    (hX : X.Connected) (k : ℕ) (hk : k + 1 < n) (j : Fin (n + 1))
    (hj : k + 2 ≤ j.val) :
    initialForm w.generatorWeight (X.prefixMinor k hk j) =
      ∏ i : Fin (k + 1), complete
        (X.capShift ((Fin.snoc (prefixColumns k hk) j :
          Fin (k + 1) → Fin (n + 1)) i) -
          X.rowParam (prefixRows k hk i)) := by
  rw [prefixMinor_eq_staircase]
  exact monge_minor_initialForm w
    (X.rowParam_strictMono.comp (prefixRows_strictMono hk))
    (X.capShift_strictMono.comp (prefixTailColumns_strictMono hk j hj))
    (prefixTail_feasible X hX hk j hj)

/-- Every tail minor is nonzero, independently of any reconstruction assumption. -/
theorem prefixMinor_ne_zero {n : ℕ} (w : ConvexWeight) (X : Diagram n)
    (hX : X.Connected) (k : ℕ) (hk : k + 1 < n) (j : Fin (n + 1))
    (hj : k + 2 ≤ j.val) : X.prefixMinor k hk j ≠ 0 := by
  rw [prefixMinor_eq_staircase]
  exact monge_minor_ne_zero w
    (X.rowParam_strictMono.comp (prefixRows_strictMono hk))
    (X.capShift_strictMono.comp (prefixTailColumns_strictMono hk j hj))
    (prefixTail_feasible X hX hk j hj)

/-- The fixed part of the increasing prefix matching. -/
noncomputable def prefixProduct {n : ℕ} (X : Diagram n) (k : ℕ) (hk : k + 1 < n) :
    CompleteRing :=
  ∏ i : Fin k, complete
    (X.capShift (prefixColumns k hk i) - X.rowParam (prefixRows k hk i.castSucc))

theorem prefixMinor_initialForm_split {n : ℕ} (w : ConvexWeight) (X : Diagram n)
    (hX : X.Connected) (k : ℕ) (hk : k + 1 < n) (j : Fin (n + 1))
    (hj : k + 2 ≤ j.val) :
    initialForm w.generatorWeight (X.prefixMinor k hk j) =
      X.prefixProduct k hk *
        complete (X.capShift j - X.rowParam (prefixRows k hk (Fin.last k))) := by
  rw [prefixMinor_initialForm w X hX k hk j hj, Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, prefixProduct]

/-- The tail minor's least weight is the cost of its increasing matching. -/
theorem prefixMinor_leastWeight {n : ℕ} (w : ConvexWeight) (X : Diagram n)
    (hX : X.Connected) (k : ℕ) (hk : k + 1 < n) (j : Fin (n + 1))
    (hj : k + 2 ≤ j.val) :
    leastWeight w.generatorWeight (X.prefixMinor k hk j) =
      ∑ i : Fin (k + 1), w.weight
        (X.capShift ((Fin.snoc (prefixColumns k hk) j :
          Fin (k + 1) → Fin (n + 1)) i) -
          X.rowParam (prefixRows k hk i)).toNat := by
  have hp := prefixMinor_ne_zero w X hX k hk j hj
  have hf := prefixTail_feasible X hX hk j hj
  have hh := complete_prod_convex_homogeneous Finset.univ
    (fun i : Fin (k + 1) => X.capShift ((Fin.snoc (prefixColumns k hk) j :
      Fin (k + 1) → Fin (n + 1)) i) -
      X.rowParam (prefixRows k hk i)) w (fun i _ => sub_nonneg.mpr (hf i))
  have hi : MvPolynomial.IsWeightedHomogeneous w.generatorWeight
      (initialForm w.generatorWeight (X.prefixMinor k hk j))
      (∑ i : Fin (k + 1), w.weight
        (X.capShift ((Fin.snoc (prefixColumns k hk) j :
          Fin (k + 1) → Fin (n + 1)) i) -
          X.rowParam (prefixRows k hk i)).toNat) := by
    rw [prefixMinor_initialForm w X hX k hk j hj]
    exact hh
  exact MvPolynomial.IsWeightedHomogeneous.inj_right (initialForm_ne_zero hp)
    (MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous _ _) hi

theorem prefixMinor_leastWeight_split {n : ℕ} (w : ConvexWeight) (X : Diagram n)
    (hX : X.Connected) (k : ℕ) (hk : k + 1 < n) (j : Fin (n + 1))
    (hj : k + 2 ≤ j.val) :
    leastWeight w.generatorWeight (X.prefixMinor k hk j) =
      (∑ i : Fin k, w.weight
        (X.capShift (prefixColumns k hk i) - X.rowParam (prefixRows k hk i.castSucc)).toNat) +
      w.weight (X.capShift j - X.rowParam (prefixRows k hk (Fin.last k))).toNat := by
  rw [prefixMinor_leastWeight w X hX k hk j hj, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

/-- Consecutive tail products have strictly increasing actual least weights. -/
theorem prefixTail_leastWeight_lt_succ {n : ℕ} (w : ConvexWeight) (X : Diagram n)
    (hX : X.Connected) (k : ℕ) (hk : k + 1 < n) (j : Fin n)
    (hj : k + 2 ≤ j.val) :
    leastWeight w.generatorWeight (X.prefixMinor k hk j.castSucc * X.cofactor j.castSucc) <
      leastWeight w.generatorWeight (X.prefixMinor k hk j.succ * X.cofactor j.succ) := by
  have hj' : k + 2 ≤ j.succ.val := by simp only [Fin.val_succ]; omega
  rw [leastWeight_mul (prefixMinor_ne_zero w X hX k hk j.castSucc hj)
      (X.cofactor_ne_zero w hX j.castSucc),
    leastWeight_mul (prefixMinor_ne_zero w X hX k hk j.succ hj')
      (X.cofactor_ne_zero w hX j.succ),
    prefixMinor_leastWeight_split w X hX k hk j.castSucc hj,
    prefixMinor_leastWeight_split w X hX k hk j.succ hj',
    cofactor_leastWeight w X hX, cofactor_leastWeight w X hX]
  have he := matching_weight_exchange w X j
  have hA : X.rowParam (prefixRows k hk (Fin.last k)) < X.rowParam j := by
    apply X.rowParam_strictMono
    change k < j.val
    omega
  have hd : X.capShift j.castSucc < X.capShift j.succ :=
    X.capShift_strictMono (by change j.val < j.val + 1; omega)
  have hmonge := w.strict_monge_int hA hd (X.diagonal_feasible hX j)
  unfold exchangeZero exchangeRow at he
  linarith

/-- The first tail term is strictly smaller than every later tail term. -/
theorem prefixTail_first_leastWeight_lt {n : ℕ} (w : ConvexWeight) (X : Diagram n)
    (hX : X.Connected) (k : ℕ) (hk : k + 1 < n) (j : Fin (n + 1))
    (hj : k + 2 ≤ j.val) (hne : j.val ≠ k + 2) :
    leastWeight w.generatorWeight
        (X.prefixMinor k hk ⟨k + 2, by omega⟩ * X.cofactor ⟨k + 2, by omega⟩) <
      leastWeight w.generatorWeight (X.prefixMinor k hk j * X.cofactor j) := by
  let f : Fin (n - (k + 2) + 1) → Fin (n + 1) :=
    fun i => ⟨k + 2 + i.val, by omega⟩
  have hf : StrictMono (fun i => leastWeight w.generatorWeight
      (X.prefixMinor k hk (f i) * X.cofactor (f i))) := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    let r : Fin n := ⟨k + 2 + i.val, by omega⟩
    have hcast : f i.castSucc = r.castSucc := Fin.ext rfl
    have hsucc : f i.succ = r.succ := by apply Fin.ext; simp [f, r]; omega
    rw [hcast, hsucc]
    exact prefixTail_leastWeight_lt_succ w X hX k hk r (by dsimp [r]; omega)
  let b : Fin (n - (k + 2) + 1) := ⟨j.val - (k + 2), by omega⟩
  have hb : (0 : Fin (n - (k + 2) + 1)) < b := by
    change 0 < j.val - (k + 2)
    omega
  have hfb : f b = j := by apply Fin.ext; dsimp [f, b]; omega
  have hf0 : f 0 = ⟨k + 2, by omega⟩ := Fin.ext (by simp [f])
  simpa only [hfb, hf0] using hf hb

/-- The exact tail sum has the first tail product as its initial form. -/
theorem prefixTail_sum_initialForm {n : ℕ} (w : ConvexWeight) (X : Diagram n)
    (hX : X.Connected) (k : ℕ) (hk : k + 1 < n) :
    initialForm w.generatorWeight
        (∑ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => k + 2 ≤ j.val),
          X.prefixMinor k hk j * X.cofactor j) =
      initialForm w.generatorWeight
        (X.prefixMinor k hk ⟨k + 2, by omega⟩ * X.cofactor ⟨k + 2, by omega⟩) := by
  classical
  let a : Fin (n + 1) := ⟨k + 2, by omega⟩
  have ha : a ∈ Finset.univ.filter (fun j : Fin (n + 1) => k + 2 ≤ j.val) := by
    simp [a]
  have hp := mul_ne_zero (prefixMinor_ne_zero w X hX k hk a (by dsimp [a]; exact le_rfl))
    (X.cofactor_ne_zero w hX a)
  refine (initialForm_sum_unique _
    (fun j => X.prefixMinor k hk j * X.cofactor j) ha hp ?_).1
  intro j hj hne
  have hj' : k + 2 ≤ j.val := (Finset.mem_filter.mp hj).2
  have hpj := mul_ne_zero (prefixMinor_ne_zero w X hX k hk j hj')
    (X.cofactor_ne_zero w hX j)
  rw [monomialValuation_eq_coe hp, monomialValuation_eq_coe hpj]
  apply WithTop.coe_lt_coe.mpr
  apply prefixTail_first_leastWeight_lt w X hX k hk j hj'
  intro he
  exact hne (Fin.ext he)

private theorem initialForm_neg_of_ne_zero {w : ℕ+ → ℝ} {p : CompleteRing}
    (hp : p ≠ 0) : initialForm w (-p) = -initialForm w p := by
  have hm : (-1 : CompleteRing) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have hh : MvPolynomial.IsWeightedHomogeneous w (-1 : CompleteRing) 0 := by
    simpa using MvPolynomial.isWeightedHomogeneous_C w (-1 : ℤ)
  rw [← neg_one_mul p, initialForm_mul hm hp,
    initialForm_eq_of_homogeneous hm hh, neg_one_mul]

/-- Prefix residuals do not vanish: their first tail product has an uncancelled initial form. -/
theorem prefixResidual_ne_zero {n : ℕ} (w : ConvexWeight) (X : Diagram n)
    (hX : X.Connected) (k : ℕ) (hk : k + 1 < n) :
    X.prefixResidual k hk ≠ 0 := by
  have hp := mul_ne_zero
    (prefixMinor_ne_zero w X hX k hk ⟨k + 2, by omega⟩ (by simp))
    (X.cofactor_ne_zero w hX ⟨k + 2, by omega⟩)
  have hs : (∑ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => k + 2 ≤ j.val),
      X.prefixMinor k hk j * X.cofactor j) ≠ 0 := by
    intro hz
    have hi := prefixTail_sum_initialForm w X hX k hk
    rw [hz, initialForm_zero] at hi
    exact initialForm_ne_zero hp hi.symm
  rw [prefixResidual_eq_neg_tail]
  exact neg_ne_zero.mpr hs

/-- The actual initial residual is the signed first-tail increasing monomial. -/
theorem prefixResidual_initialForm {n : ℕ} (w : ConvexWeight) (X : Diagram n)
    (hX : X.Connected) (k : ℕ) (hk : k + 1 < n) :
    initialForm w.generatorWeight (X.prefixResidual k hk) =
      -((X.prefixProduct k hk *
          complete (X.capShift ⟨k + 2, by omega⟩ -
            X.rowParam (prefixRows k hk (Fin.last k)))) *
        ((-1 : CompleteRing) ^ (k + 2) *
          ∏ i : Fin n, complete (X.peelIndex ⟨k + 2, by omega⟩ i))) := by
  let s : CompleteRing :=
    ∑ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => k + 2 ≤ j.val),
      X.prefixMinor k hk j * X.cofactor j
  have hs : s ≠ 0 := by
    have hr := prefixResidual_ne_zero w X hX k hk
    rw [prefixResidual_eq_neg_tail] at hr
    exact neg_ne_zero.mp hr
  rw [prefixResidual_eq_neg_tail, initialForm_neg_of_ne_zero hs,
    prefixTail_sum_initialForm w X hX k hk]
  rw [initialForm_mul
      (prefixMinor_ne_zero w X hX k hk ⟨k + 2, by omega⟩ (by simp))
      (X.cofactor_ne_zero w hX ⟨k + 2, by omega⟩),
    prefixMinor_initialForm_split w X hX k hk ⟨k + 2, by omega⟩ (by simp),
    cofactor_initialForm w X hX]

/-- A prefix functional at the observed columns uses only the recovered prefix coordinates. -/
theorem prefixMinor_eq_of_prefix_coordinates {n : ℕ} (X Y : Diagram n)
    (k : ℕ) (hk : k + 1 < n)
    (hrow : ∀ i : Fin (k + 1), X.rowParam (prefixRows k hk i) =
      Y.rowParam (prefixRows k hk i))
    (hcap : ∀ j : Fin (n + 1), j.val ≤ k + 1 → X.capShift j = Y.capShift j)
    (j : Fin (n + 1)) (hj : j.val ≤ k + 1) :
    X.prefixMinor k hk j = Y.prefixMinor k hk j := by
  unfold prefixMinor columnPrefixMinor
  apply congrArg Matrix.det
  apply Matrix.ext
  intro i a
  change complete (X.capShift ((Fin.snoc (prefixColumns k hk) j :
      Fin (k + 1) → Fin (n + 1)) a) - X.rowParam (prefixRows k hk i)) =
    complete (Y.capShift ((Fin.snoc (prefixColumns k hk) j :
      Fin (k + 1) → Fin (n + 1)) a) - Y.rowParam (prefixRows k hk i))
  have ha : ((Fin.snoc (prefixColumns k hk) j :
      Fin (k + 1) → Fin (n + 1)) a).val ≤ k + 1 := by
    cases a using Fin.lastCases with
    | last => simpa only [Fin.snoc_last] using hj
    | cast a =>
        rw [Fin.snoc_castSucc]
        change a.val + 2 ≤ k + 1
        omega
  rw [hrow i, hcap _ ha]

/-- Equal observations and recovered prefixes produce equal actual residuals. -/
theorem prefixResidual_eq_of_prefix_coordinates {n : ℕ} (X Y : Diagram n)
    (k : ℕ) (hk : k + 1 < n)
    (hrow : ∀ i : Fin (k + 1), X.rowParam (prefixRows k hk i) =
      Y.rowParam (prefixRows k hk i))
    (hcap : ∀ j : Fin (n + 1), j.val ≤ k + 1 → X.capShift j = Y.capShift j)
    (h0 : X.cofactor 0 = Y.cofactor 0) (h1 : X.cofactor 1 = Y.cofactor 1) :
    X.prefixResidual k hk = Y.prefixResidual k hk := by
  let : NeZero n := ⟨by omega⟩
  have ht0 := prefixMinor_eq_of_prefix_coordinates X Y k hk hrow hcap 0 (by simp)
  have ht1 := prefixMinor_eq_of_prefix_coordinates X Y k hk hrow hcap 1 (by
    have hv : (1 : Fin (n + 1)).val = 1 := by
      change 1 % (n + 1) = 1
      exact Nat.mod_eq_of_lt (by omega)
    rw [hv]
    omega)
  simp only [prefixResidual, ht0, ht1, h0, h1]

/-- Adjacent peel monomials satisfy the exact cross-multiplied single-row exchange. -/
theorem peelProduct_exchange {n : ℕ} (X : Diagram n) (j : Fin n) :
    (∏ i : Fin n, complete (X.peelIndex j.succ i)) * complete (X.exchangeRow j) =
      (∏ i : Fin n, complete (X.peelIndex j.castSucc i)) *
        complete (X.exchangeZero j) := by
  classical
  have he : (∏ i ∈ Finset.univ.erase j, complete (X.peelIndex j.succ i)) =
      ∏ i ∈ Finset.univ.erase j, complete (X.peelIndex j.castSucc i) := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [X.peelIndex_adjacent_eq j i (Finset.mem_erase.mp hi).1]
  rw [← Finset.mul_prod_erase Finset.univ
      (fun i => complete (X.peelIndex j.succ i)) (Finset.mem_univ j),
    ← Finset.mul_prod_erase Finset.univ
      (fun i => complete (X.peelIndex j.castSucc i)) (Finset.mem_univ j),
    peelIndex_succ_self, peelIndex_castSucc_self, he]
  ring

/-- The unsigned residual monomial, with the initial observation as its zeroth member. -/
noncomputable def unsignedPrefixMonomial {n : ℕ} (X : Diagram n) (t : Fin n) : CompleteRing :=
  (∏ i : Fin t.val, complete
    (X.capShift ⟨i.val + 2, by omega⟩ - X.rowParam ⟨i.val, by omega⟩)) *
  ∏ i : Fin n, complete (X.peelIndex t.succ i)

theorem unsignedPrefixMonomial_zero {n : ℕ} (X : Diagram (n + 1)) :
    X.unsignedPrefixMonomial 0 = ∏ i, complete (X.peelIndex 1 i) := by
  change X.unsignedPrefixMonomial (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1)) = _
  simp only [unsignedPrefixMonomial, Finset.univ_eq_empty, Finset.prod_empty, one_mul]
  rfl

/-- The prefix residual's initial form is its unsigned monomial times its prescribed unit sign. -/
theorem prefixResidual_initialForm_unsigned {n : ℕ} (w : ConvexWeight) (X : Diagram n)
    (hX : X.Connected) (k : ℕ) (hk : k + 1 < n) :
    initialForm w.generatorWeight (X.prefixResidual k hk) =
      (-1 : CompleteRing) ^ (k + 1) * X.unsignedPrefixMonomial ⟨k + 1, hk⟩ := by
  rw [prefixResidual_initialForm w X hX k hk]
  unfold unsignedPrefixMonomial
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]
  change -((X.prefixProduct k hk *
      complete (X.capShift ⟨k + 2, by omega⟩ -
        X.rowParam (prefixRows k hk (Fin.last k)))) *
      ((-1 : CompleteRing) ^ (k + 2) *
        ∏ i : Fin n, complete (X.peelIndex ⟨k + 2, by omega⟩ i))) =
    (-1 : CompleteRing) ^ (k + 1) *
      ((X.prefixProduct k hk *
        complete (X.capShift ⟨k + 2, by omega⟩ -
          X.rowParam (prefixRows k hk (Fin.last k)))) *
        ∏ i : Fin n, complete (X.peelIndex ⟨k + 2, by omega⟩ i))
  have hs : (-1 : CompleteRing) ^ (k + 2) = -((-1 : CompleteRing) ^ (k + 1)) := by
    rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
    ring
  rw [hs]
  ring

/-- Recovered prefixes and the observations determine the next unsigned residual monomial. -/
theorem unsignedPrefixMonomial_eq_of_prefix_coordinates {n : ℕ} (X Y : Diagram n)
    (hX : X.Connected) (hY : Y.Connected) (k : ℕ) (hk : k + 1 < n)
    (hrow : ∀ i : Fin (k + 1), X.rowParam (prefixRows k hk i) =
      Y.rowParam (prefixRows k hk i))
    (hcap : ∀ j : Fin (n + 1), j.val ≤ k + 1 → X.capShift j = Y.capShift j)
    (h0 : X.cofactor 0 = Y.cofactor 0) (h1 : X.cofactor 1 = Y.cofactor 1) :
    X.unsignedPrefixMonomial ⟨k + 1, hk⟩ =
      Y.unsignedPrefixMonomial ⟨k + 1, hk⟩ := by
  have hr := prefixResidual_eq_of_prefix_coordinates X Y k hk hrow hcap h0 h1
  have hi := congrArg (initialForm squareWeight.generatorWeight) hr
  rw [prefixResidual_initialForm_unsigned squareWeight X hX,
    prefixResidual_initialForm_unsigned squareWeight Y hY] at hi
  exact mul_left_cancel₀ (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hi

/-- The unsigned residual sequence changes by the actual reduced three-index exchange. -/
theorem unsignedPrefixMonomial_exchange {n : ℕ} (X : Diagram n)
    (k : ℕ) (hk : k + 1 < n) :
    X.unsignedPrefixMonomial ⟨k + 1, hk⟩ *
        complete (X.exchangeRow ⟨k + 1, hk⟩) =
      X.unsignedPrefixMonomial ⟨k, by omega⟩ *
        complete (X.capShift ⟨k + 2, by omega⟩ - X.rowParam ⟨k, by omega⟩) *
        complete (X.exchangeZero ⟨k + 1, hk⟩) := by
  let r : Fin n := ⟨k + 1, hk⟩
  have he := X.peelProduct_exchange r
  have hcast : r.castSucc = (⟨k, by omega⟩ : Fin n).succ := Fin.ext rfl
  rw [hcast] at he
  unfold unsignedPrefixMonomial
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]
  change ((∏ i : Fin k, complete
      (X.capShift ⟨i.val + 2, by omega⟩ - X.rowParam ⟨i.val, by omega⟩)) *
    complete (X.capShift ⟨k + 2, by omega⟩ - X.rowParam ⟨k, by omega⟩) *
    (∏ i : Fin n, complete (X.peelIndex r.succ i))) * complete (X.exchangeRow r) = _
  rw [mul_assoc, mul_assoc, he]
  ring

/-- Cross-multiplied free-generator exchanges determine all three ordered subscripts. -/
theorem exchange_indices_of_cross_product_eq {u rho z u' rho' z' : ℕ}
    (hu : rho < u) (hz : z < rho) (hu' : rho' < u') (hz' : z' < rho')
    (h : complete (u : ℤ) * complete (z : ℤ) * complete (rho' : ℤ) =
      complete (u' : ℤ) * complete (z' : ℤ) * complete (rho : ℤ)) :
    rho = rho' ∧ z = z' ∧ u = u' := by
  have hm : ([u, z, rho'].map (fun a : ℕ => complete (a : ℤ))).prod =
      ([u', z', rho].map (fun a : ℕ => complete (a : ℤ))).prod := by
    simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      mul_assoc] using h
  have hmset := (prod_complete_eq_iff [u, z, rho'] [u', z', rho]).mp hm
  have hcount : ∀ t : ℕ, 0 < t →
      ([u, z, rho'] : Multiset ℕ).count t = ([u', z', rho] : Multiset ℕ).count t := by
    intro t ht
    have hc := congrArg (fun s : Multiset ℕ => s.count t) hmset
    change (([u, z, rho'] : Multiset ℕ).filter (fun a => 0 < a)).count t =
      (([u', z', rho] : Multiset ℕ).filter (fun a => 0 < a)).count t at hc
    rw [Multiset.count_filter_of_pos ht, Multiset.count_filter_of_pos ht] at hc
    exact hc
  have hr0 : 0 < rho := by omega
  have hrr : rho = rho' := by
    by_contra hn
    have hn' : rho ≠ rho' := hn
    have hc := hcount rho hr0
    change (u ::ₘ z ::ₘ rho' ::ₘ (0 : Multiset ℕ)).count rho =
      (u' ::ₘ z' ::ₘ rho ::ₘ (0 : Multiset ℕ)).count rho at hc
    simp only [Multiset.count_cons,
      Multiset.count_zero, ite_eq_right (ne_of_lt hu),
      ite_eq_right (ne_of_gt hz), ite_eq_right hn'] at hc
    split_ifs at hc <;> omega
  subst rho'
  have huu : u = u' := by
    by_contra hn
    have hn' : u ≠ u' := hn
    have hu0 : 0 < u := by omega
    have huz : u ≠ z := by omega
    have huz' : u ≠ z' := by omega
    have hc := hcount u hu0
    change (u ::ₘ z ::ₘ rho ::ₘ (0 : Multiset ℕ)).count u =
      (u' ::ₘ z' ::ₘ rho ::ₘ (0 : Multiset ℕ)).count u at hc
    simp only [Multiset.count_cons,
      Multiset.count_zero, ite_eq_right huz,
      ite_eq_right huz', ite_eq_right hn', ite_eq_right (ne_of_gt hu)] at hc
    split_ifs at hc <;> omega
  subst u'
  have hzz : z = z' := by
    by_cases hz0 : z = 0
    · subst z
      by_contra hn
      have hz'0 : 0 < z' := by omega
      have hzu : z' ≠ u := by omega
      have hzr : z' ≠ rho := by omega
      have hc := hcount z' hz'0
      change (u ::ₘ 0 ::ₘ rho ::ₘ (0 : Multiset ℕ)).count z' =
        (u ::ₘ z' ::ₘ rho ::ₘ (0 : Multiset ℕ)).count z' at hc
      simp only [Multiset.count_cons,
        Multiset.count_zero, ite_eq_right hzu,
        ite_eq_right hzr, ite_eq_right (ne_of_gt hz'0)] at hc
      split_ifs at hc <;> omega
    · by_contra hn
      have hzpos : 0 < z := by omega
      have hzu : z ≠ u := by omega
      have hzr : z ≠ rho := by omega
      have hn' : z ≠ z' := hn
      have hc := hcount z hzpos
      change (u ::ₘ z ::ₘ rho ::ₘ (0 : Multiset ℕ)).count z =
        (u ::ₘ z' ::ₘ rho ::ₘ (0 : Multiset ℕ)).count z at hc
      simp only [Multiset.count_cons,
        Multiset.count_zero, ite_eq_right hzu,
        ite_eq_right hzr, ite_eq_right hn'] at hc
      split_ifs at hc <;> omega
  exact ⟨rfl, hzz, rfl⟩

theorem unsignedPrefixMonomial_ne_zero {n : ℕ} (X : Diagram n) (hX : X.Connected)
    (t : Fin n) : X.unsignedPrefixMonomial t ≠ 0 := by
  unfold unsignedPrefixMonomial
  apply mul_ne_zero
  · apply complete_prod_ne_zero
    intro i _
    apply sub_nonneg.mpr
    apply (X.diagonal_feasible hX ⟨i.val, by omega⟩).trans
    apply X.capShift_strictMono.monotone
    change i.val ≤ i.val + 2
    omega
  · exact complete_prod_ne_zero Finset.univ (fun i => X.peelIndex t.succ i)
      (fun i _ => X.peelIndex_nonneg hX t.succ i)

theorem unsignedPrefixMonomial_zero_eq_of_cofactor_one_eq {n : ℕ}
    (X Y : Diagram (n + 1)) (hX : X.Connected) (hY : Y.Connected)
    (h1 : X.cofactor 1 = Y.cofactor 1) :
    X.unsignedPrefixMonomial 0 = Y.unsignedPrefixMonomial 0 := by
  have hi := congrArg (initialForm squareWeight.generatorWeight) h1
  rw [cofactor_initialForm squareWeight X hX,
    cofactor_initialForm squareWeight Y hY] at hi
  have hv : (1 : Fin (n + 1 + 1)).val = 1 := by
    change 1 % (n + 1 + 1) = 1
    exact Nat.mod_eq_of_lt (by omega)
  rw [hv, pow_one, neg_one_mul, neg_one_mul] at hi
  rw [unsignedPrefixMonomial_zero, unsignedPrefixMonomial_zero]
  exact neg_injective hi

/-- Equality of two consecutive actual residual monomials recovers the next row and cap. -/
theorem next_coordinates_eq_of_unsignedPrefixMonomials {n : ℕ}
    (X Y : Diagram n) (hX : X.Connected) (hY : Y.Connected)
    (k : ℕ) (hk : k + 1 < n)
    (hprev : X.unsignedPrefixMonomial ⟨k, by omega⟩ =
      Y.unsignedPrefixMonomial ⟨k, by omega⟩)
    (hnext : X.unsignedPrefixMonomial ⟨k + 1, hk⟩ =
      Y.unsignedPrefixMonomial ⟨k + 1, hk⟩)
    (hd : X.capShift ⟨k + 1, by omega⟩ = Y.capShift ⟨k + 1, by omega⟩) :
    X.rowParam ⟨k + 1, hk⟩ = Y.rowParam ⟨k + 1, hk⟩ ∧
      X.capShift ⟨k + 2, by omega⟩ = Y.capShift ⟨k + 2, by omega⟩ := by
  let i : Fin n := ⟨k + 1, hk⟩
  let p : Fin n := ⟨k, by omega⟩
  let ux := X.capShift i.succ - X.rowParam p
  let uy := Y.capShift i.succ - Y.rowParam p
  let rx := X.exchangeRow i
  let ry := Y.exchangeRow i
  let zx := X.exchangeZero i
  let zy := Y.exchangeZero i
  have hzx : 0 ≤ zx := sub_nonneg.mpr (X.diagonal_feasible hX i)
  have hzy : 0 ≤ zy := sub_nonneg.mpr (Y.diagonal_feasible hY i)
  have hrx : zx < rx := by
    have he := X.capShift_strictMono (show i.castSucc < i.succ by
      change i.val < i.val + 1; omega)
    dsimp [zx, rx, exchangeZero, exchangeRow]
    omega
  have hry : zy < ry := by
    have he := Y.capShift_strictMono (show i.castSucc < i.succ by
      change i.val < i.val + 1; omega)
    dsimp [zy, ry, exchangeZero, exchangeRow]
    omega
  have hux : rx < ux := by
    have he := X.rowParam_strictMono (show p < i by change k < k + 1; omega)
    dsimp [rx, ux, exchangeRow]
    omega
  have huy : ry < uy := by
    have he := Y.rowParam_strictMono (show p < i by change k < k + 1; omega)
    dsimp [ry, uy, exchangeRow]
    omega
  have heX := unsignedPrefixMonomial_exchange X k hk
  have heY := unsignedPrefixMonomial_exchange Y k hk
  change X.unsignedPrefixMonomial i * complete rx =
    X.unsignedPrefixMonomial p * complete ux * complete zx at heX
  change Y.unsignedPrefixMonomial i * complete ry =
    Y.unsignedPrefixMonomial p * complete uy * complete zy at heY
  have hcross : complete ux * complete zx * complete ry =
      complete uy * complete zy * complete rx := by
    apply mul_left_cancel₀ (X.unsignedPrefixMonomial_ne_zero hX p)
    calc
      X.unsignedPrefixMonomial p * (complete ux * complete zx * complete ry) =
          (X.unsignedPrefixMonomial p * complete ux * complete zx) * complete ry := by ring
      _ = (X.unsignedPrefixMonomial i * complete rx) * complete ry := by
        rw [← heX]
      _ = (Y.unsignedPrefixMonomial i * complete ry) * complete rx := by
        rw [hnext]
        ring
      _ = (Y.unsignedPrefixMonomial p * complete uy * complete zy) * complete rx := by
        rw [heY]
      _ = X.unsignedPrefixMonomial p * (complete uy * complete zy * complete rx) := by
        rw [hprev]
        ring
  have hcastux : (ux.toNat : ℤ) = ux := by omega
  have hcastuy : (uy.toNat : ℤ) = uy := by omega
  have hcastrx : (rx.toNat : ℤ) = rx := by omega
  have hcastry : (ry.toNat : ℤ) = ry := by omega
  have hcastzx : (zx.toNat : ℤ) = zx := by omega
  have hcastzy : (zy.toNat : ℤ) = zy := by omega
  have hcrossnat : complete (ux.toNat : ℤ) * complete (zx.toNat : ℤ) *
      complete (ry.toNat : ℤ) =
      complete (uy.toNat : ℤ) * complete (zy.toNat : ℤ) * complete (rx.toNat : ℤ) := by
    simpa only [hcastux, hcastuy, hcastrx, hcastry, hcastzx, hcastzy] using hcross
  have hid := exchange_indices_of_cross_product_eq
    (show rx.toNat < ux.toNat by omega) (show zx.toNat < rx.toNat by omega)
    (show ry.toNat < uy.toNat by omega) (show zy.toNat < ry.toNat by omega) hcrossnat
  have hr : rx = ry := by omega
  have hz : zx = zy := by omega
  have hiCast : i.castSucc = (⟨k + 1, by omega⟩ : Fin (n + 1)) := Fin.ext rfl
  have hiSucc : i.succ = (⟨k + 2, by omega⟩ : Fin (n + 1)) := Fin.ext rfl
  dsimp [rx, ry, zx, zy, exchangeRow, exchangeZero] at hr hz
  rw [hiCast] at hz
  rw [hiSucc] at hr
  constructor <;> dsimp [i] at * <;> omega

/-- The actual two-cofactor observations recover every prefix and hence the translation class. -/
theorem translationEquivalent_of_two_cofactors_same_count {n : ℕ}
    (X Y : Diagram (n + 1)) (hX : X.Connected) (hY : Y.Connected)
    (h0 : X.cofactor 0 = Y.cofactor 0) (h1 : X.cofactor 1 = Y.cofactor 1) :
    TranslationEquivalent X Y := by
  have hd1 := capShift_one_eq_of_two_cofactors_eq X Y hX hY h0 h1
  have recover : ∀ k : ℕ, k < n + 1 →
      (∀ i : Fin (n + 1), i.val ≤ k → X.rowParam i = Y.rowParam i) ∧
      (∀ j : Fin (n + 1 + 1), j.val ≤ k + 1 → X.capShift j = Y.capShift j) := by
    intro k
    induction k with
    | zero =>
        intro _
        constructor
        · intro i hi
          have hi0 : i = ⟨0, Nat.zero_lt_succ n⟩ := by
            apply Fin.ext
            change i.val = 0
            omega
          rw [hi0, rowParam_zero X, rowParam_zero Y]
        · intro j hj
          by_cases hj0 : j.val = 0
          · have hj' : j = 0 := Fin.ext hj0
            subst j
            simp
          · have hj' : j = 1 := by apply Fin.ext; simp; omega
            subst j
            exact hd1
    | succ k ih =>
        intro hk
        obtain ⟨hrow, hcap⟩ := ih (by omega)
        have hk' : k + 1 < n + 1 := hk
        have hnew := unsignedPrefixMonomial_eq_of_prefix_coordinates X Y hX hY k hk'
          (fun i => hrow (prefixRows k hk' i) (by dsimp [prefixRows]; omega))
          hcap h0 h1
        have hprev : X.unsignedPrefixMonomial ⟨k, by omega⟩ =
            Y.unsignedPrefixMonomial ⟨k, by omega⟩ := by
          cases k with
          | zero => exact unsignedPrefixMonomial_zero_eq_of_cofactor_one_eq X Y hX hY h1
          | succ l =>
              apply unsignedPrefixMonomial_eq_of_prefix_coordinates X Y hX hY l (by omega)
              · intro i
                apply hrow
                dsimp [prefixRows]
                omega
              · intro j hj
                exact hcap j (by omega)
              · exact h0
              · exact h1
        have hc := next_coordinates_eq_of_unsignedPrefixMonomials X Y hX hY k hk'
          hprev hnew (hcap ⟨k + 1, by omega⟩ (by simp))
        constructor
        · intro i hi
          by_cases hik : i.val ≤ k
          · exact hrow i hik
          · have hi' : i = ⟨k + 1, hk'⟩ := by
              apply Fin.ext
              change i.val = k + 1
              omega
            rw [hi']
            exact hc.1
        · intro j hj
          by_cases hjk : j.val ≤ k + 1
          · exact hcap j hjk
          · have hj' : j = ⟨k + 2, by omega⟩ := by
              apply Fin.ext
              change j.val = k + 2
              omega
            rw [hj']
            exact hc.2
  obtain ⟨hrow, hcap⟩ := recover n (by omega)
  apply translationEquivalent_of_coordinates X Y
  · intro i
    exact hrow i (by omega)
  · intro j
    exact hcap j (by omega)

/-- `lem:two-cofactor-reconstruction`, with neither row count nor cap grid supplied. -/
theorem translationEquivalent_of_two_cofactors_eq {n m : ℕ}
    (X : Diagram (n + 1)) (Y : Diagram (m + 1)) (hX : X.Connected) (hY : Y.Connected)
    (h0 : X.cofactor 0 = Y.cofactor 0) (h1 : X.cofactor 1 = Y.cofactor 1) :
    TranslationEquivalent X Y := by
  have hn : n = m := by
    have hr := row_count_eq_of_cofactor_zero_eq X Y hX hY h0
    omega
  subst m
  exact translationEquivalent_of_two_cofactors_same_count X Y hX hY h0 h1

end Diagram
end SkewSchurReconstruction
