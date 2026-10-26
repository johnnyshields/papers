/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewSchurReconstruction.LaplaceFloor
import SkewSchurReconstruction.BoundaryReconstruction
import Mathlib.Algebra.Order.Ring.WithTop

/-!
# Two-cap exclusion and uniqueness

Formalizes "Two-cap exclusion" (`sec:two-cap`): `thm:two-cap`,
`cor:floor-supplies`, `cor:double-cap-kills`, and `cor:unique-ratio`.
The double-cap theorem uses actual extension observations and does not impose a
common inner boundary. Sorry-free.
-/

namespace SkewSchurReconstruction

open scoped BigOperators

private theorem square_leastWeight_mul_complete (p : CompleteRing) (hp : p ≠ 0)
    (k : ℤ) (hk : 0 ≤ k) :
    leastWeight squareWeight.generatorWeight (p * complete k) =
      leastWeight squareWeight.generatorWeight p + (k : ℝ) ^ 2 := by
  have hn := mul_ne_zero hp (complete_ne_zero_of_nonneg k hk)
  have h := monomialValuation_mul squareWeight.generatorWeight p (complete k)
  rw [monomialValuation_eq_coe hn, monomialValuation_eq_coe hp,
    complete_monomialValuation squareWeight k hk, ← WithTop.coe_add] at h
  have hc : (k.toNat : ℝ) = (k : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hk
  have hw : squareWeight.weight k.toNat = (k : ℝ) ^ 2 := by
    change (k.toNat : ℝ) ^ 2 = (k : ℝ) ^ 2
    rw [hc]
  exact (WithTop.coe_injective h).trans (congrArg (fun x => leastWeight
    squareWeight.generatorWeight p + x) hw)

/-- The exact cap-shift difference `eq:cap-shift`, using actual nonzero summand weights. -/
theorem cap_shift_square (G : ℤ →₀ CompleteRing) (d : ℤ)
    (h0 : G 0 ≠ 0) (hd : G d ≠ 0) (hshift : 0 ≤ d) (a b : ℕ) :
    (leastWeight squareWeight.generatorWeight (G d * complete ((b : ℤ) + d)) -
        leastWeight squareWeight.generatorWeight (G 0 * complete b)) -
      (leastWeight squareWeight.generatorWeight (G d * complete ((a : ℤ) + d)) -
        leastWeight squareWeight.generatorWeight (G 0 * complete a)) =
      2 * (d : ℝ) * ((b : ℝ) - a) := by
  rw [square_leastWeight_mul_complete _ hd _ (by omega),
    square_leastWeight_mul_complete _ h0 _ (by positivity),
    square_leastWeight_mul_complete _ hd _ (by omega),
    square_leastWeight_mul_complete _ h0 _ (by positivity)]
  push_cast
  ring

private theorem shifted_response_zero_leastWeight (G : ℤ →₀ CompleteRing)
    (h0 : G 0 ≠ 0) (hpos : ∀ d, G d ≠ 0 → 0 ≤ d) (gamma k : ℕ) (hk : gamma < k)
    (hbound : ∀ d, G d ≠ 0 →
      leastWeight squareWeight.generatorWeight (G 0) -
        (leastWeight squareWeight.generatorWeight (G d) + (d.toNat : ℝ) ^ 2) ≤
          2 * (gamma : ℝ) * (d.toNat : ℝ)) :
    gridResponse G k ≠ 0 ∧
      leastWeight squareWeight.generatorWeight (gridResponse G k) =
        leastWeight squareWeight.generatorWeight (G 0) + (k : ℝ) ^ 2 := by
  classical
  let f : ℤ → CompleteRing := fun d => G d * complete ((k : ℤ) + d)
  have hi : 0 ∈ G.support := Finsupp.mem_support_iff.mpr h0
  have hkpos : 0 < k := by omega
  have hf0 : f 0 ≠ 0 := by
    dsimp [f]
    rw [add_zero]
    exact mul_ne_zero h0 (complete_ne_zero_of_nonneg _ (by omega))
  have hval : ∀ d ∈ G.support,
      monomialValuation squareWeight.generatorWeight (f d) =
        ((leastWeight squareWeight.generatorWeight (G d) +
          ((k : ℝ) + (d.toNat : ℝ)) ^ 2 : ℝ) : WithTop ℝ) := by
    intro d hd
    have hgd := Finsupp.mem_support_iff.mp hd
    have hdn := hpos d hgd
    have hsum : ((k : ℤ) + d).toNat = k + d.toNat := by omega
    dsimp [f]
    rw [monomialValuation_mul, monomialValuation_eq_coe hgd,
      complete_monomialValuation squareWeight _ (by omega)]
    simp only [squareWeight, hsum, Nat.cast_add, WithTop.coe_add, WithTop.coe_pow]
    norm_cast
    simp only [WithTop.coe_add, WithTop.coe_pow, Nat.cast_pow, WithTop.coe_natCast]
  have hmin : ∀ d ∈ G.support, d ≠ 0 →
      monomialValuation squareWeight.generatorWeight (f 0) <
        monomialValuation squareWeight.generatorWeight (f d) := by
    intro d hd hd0
    have hgd := Finsupp.mem_support_iff.mp hd
    have hdn := hpos d hgd
    have hdp : 0 < d := by omega
    have hdpn : 0 < d.toNat := by omega
    have hdR : 0 < (d.toNat : ℝ) := by exact_mod_cast hdpn
    have hkR : (gamma : ℝ) < (k : ℝ) := by exact_mod_cast hk
    have hb := hbound d hgd
    rw [hval 0 hi, hval d hd]
    simp only [Int.toNat_zero, Nat.cast_zero, add_zero]
    apply WithTop.coe_lt_coe.mpr
    nlinarith
  have hsum := initialForm_sum_unique G.support f hi hf0 hmin
  have hnonzero := sum_ne_zero_of_unique_min G.support f hi hf0 hmin
  have he : gridResponse G k = ∑ d ∈ G.support, f d := rfl
  refine ⟨by rwa [he], ?_⟩
  rw [he, hsum.2]
  dsimp [f]
  rw [add_zero, leastWeight_mul h0 (complete_ne_zero_of_nonneg _ (by omega)),
    complete_leastWeight squareWeight _ (by omega)]
  simp only [squareWeight, Int.toNat_natCast]

namespace TranslationEquivalent

/-- Translating both boundaries preserves the actual union-grid cofactor vector. -/
theorem gridDefect_eq_zero {n m : ℕ} {X : Diagram n} {Y : Diagram m}
    (h : TranslationEquivalent X Y) : gridDefect X Y = 0 := by
  obtain ⟨hn, t, ht⟩ := h
  subst m
  have htop : ∀ hn : 0 < n, (X.top : ℤ) = (Y.top : ℤ) + t := by
    intro hn
    rw [X.top_of_pos hn, Y.top_of_pos hn]
    exact (ht ⟨0, hn⟩ ⟨0, hn⟩ rfl).1
  have hrow : ∀ i, X.rowParam i = Y.rowParam i := by
    intro i
    have hn : 0 < n := by have := i.isLt; omega
    have hi := (ht i i rfl).1
    have hh := htop hn
    dsimp [Diagram.rowParam]
    omega
  have hcap : ∀ j, X.capShift j = Y.capShift j := by
    intro j
    by_cases hj : j.val = 0
    · simp only [Diagram.capShift, dite_eq_left hj]
    · have hn : 0 < n := by have := j.isLt; omega
      let i : Fin n := ⟨j.val - 1, by omega⟩
      have hi := (ht i i rfl).2
      have hh := htop hn
      simp only [Diagram.capShift, dite_eq_right hj]
      dsimp [i] at hi
      omega
  have hM : X.capMatrix = Y.capMatrix := by
    apply Matrix.ext
    intro i j
    simp only [Diagram.capMatrix, Matrix.of_apply, hrow i, hcap j]
  have hC : X.cofactor = Y.cofactor := by
    funext j
    unfold Diagram.cofactor
    rw [hM]
  have hvector : X.cofactorGridVector = Y.cofactorGridVector := by
    unfold Diagram.cofactorGridVector
    simp_rw [hcap, hC]
  rw [gridDefect, hvector, sub_self]

end TranslationEquivalent

namespace Diagram

/-- The manuscript's floor criterion excludes two caps, without a common-boundary assumption. -/
theorem two_cap_exclusion {n m : ℕ} (X : Diagram n) (Y : Diagram m)
    (hX : X.Connected) (hY : Y.Connected) (r a b : ℕ) (ha : 0 < a) (hab : a < b)
    (hA : RatioIdentity (gridDefect X Y) r a) (hB : RatioIdentity (gridDefect X Y) r b)
    (hG0 : gridDefect X Y 0 ≠ 0)
    (hbound : ∀ d, gridDefect X Y d ≠ 0 →
      leastWeight squareWeight.generatorWeight (gridDefect X Y 0) -
        (leastWeight squareWeight.generatorWeight (gridDefect X Y d) + (d.toNat : ℝ) ^ 2) ≤
          2 * (ratioVirtualShift r a : ℝ) * (d.toNat : ℝ)) : False := by
  let G := gridDefect X Y
  have hpos : ∀ d, G d ≠ 0 → 0 ≤ d := fun d hd => (gridDefect_shift_bounds X Y d hd).1
  have hb : 0 < b := by omega
  by_cases hr0 : r = 0
  · subst r
    have hz := gridDefect_response_zero X Y hX.1 hY.1
    have hcap := hB
    unfold RatioIdentity at hcap
    rw [Nat.cast_zero, zero_add, hz, mul_zero] at hcap
    have hp := shifted_response_zero_leastWeight G hG0 hpos a b hab
      (by simpa [G, ratioVirtualShift] using hbound)
    exact hp.1 hcap
  · have hr : 0 < r := by omega
    have hg : ratioVirtualShift r a = r := by simp only [ratioVirtualShift, ite_eq_right hr0]
    have hpA := shifted_response_zero_leastWeight G hG0 hpos r (r + a) (by omega)
      (by simpa only [hg] using hbound)
    have hpB := shifted_response_zero_leastWeight G hG0 hpos r (r + b) (by omega)
      (by simpa only [hg] using hbound)
    have heA : gridResponse G ((r + a : ℕ) : ℤ) = complete (a : ℤ) * gridResponse G r := by
      simpa only [RatioIdentity, Nat.cast_add] using hA
    have heB : gridResponse G ((r + b : ℕ) : ℤ) = complete (b : ℤ) * gridResponse G r := by
      simpa only [RatioIdentity, Nat.cast_add] using hB
    have hR : gridResponse G r ≠ 0 := by
      intro hz
      exact hpA.1 (by rw [heA, hz, mul_zero])
    have hla := congrArg (leastWeight squareWeight.generatorWeight) heA
    have hlb := congrArg (leastWeight squareWeight.generatorWeight) heB
    rw [hpA.2, leastWeight_mul (complete_ne_zero_of_nonneg _ (by omega)) hR,
      complete_leastWeight squareWeight _ (by omega)] at hla
    rw [hpB.2, leastWeight_mul (complete_ne_zero_of_nonneg _ (by omega)) hR,
      complete_leastWeight squareWeight _ (by omega)] at hlb
    simp only [squareWeight, Int.toNat_natCast, Nat.cast_add] at hla hlb
    have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
    have habR : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
    nlinarith

/-- Two same-base ratio identities force translation, with neither boundary prescribed. -/
theorem double_cap_kills {n m : ℕ} (X : Diagram n) (Y : Diagram m)
    (hX : X.Connected) (hY : Y.Connected) (r a b : ℕ) (ha : 0 < a) (hab : a < b)
    (hA : RatioIdentity (gridDefect X Y) r a) (hB : RatioIdentity (gridDefect X Y) r b) :
    TranslationEquivalent X Y ∧ gridDefect X Y = 0 := by
  classical
  have hb : 0 < b := by omega
  have ht : TranslationEquivalent X Y := by
    by_cases hr0 : r = 0
    · subst r
      have hEa : (X.extendNortheast a ha).schurFunction =
          (Y.extendNortheast a ha).schurFunction := by
        have hh := ratio_remainders_eq X Y 0 a hA
        simp only [Nat.cast_zero, zero_add] at hh
        rw [X.capPolynomial_zero hX.1, Y.capPolynomial_zero hY.1] at hh
        rw [schurFunction_extendNortheast, schurFunction_extendNortheast]
        simpa only [Nat.cast_zero, zero_add, mul_zero, zero_sub, neg_inj] using hh
      have hEb : (X.extendNortheast b hb).schurFunction =
          (Y.extendNortheast b hb).schurFunction := by
        have hh := ratio_remainders_eq X Y 0 b hB
        simp only [Nat.cast_zero, zero_add] at hh
        rw [X.capPolynomial_zero hX.1, Y.capPolynomial_zero hY.1] at hh
        rw [schurFunction_extendNortheast, schurFunction_extendNortheast]
        simpa only [Nat.cast_zero, zero_add, mul_zero, zero_sub, neg_inj] using hh
      apply (two_positive_extensions X Y hX hY a b a b ha hb ha hb hab.ne hab.ne ?_).1
      simp only [extensionObservations, hEa, hEb]
    · have hr : 0 < r := by omega
      let U := X.extendNortheast r hr
      let V := Y.extendNortheast r hr
      have hU := X.extendNortheast_connected r hr hX
      have hV := Y.extendNortheast_connected r hr hY
      have hEa : (U.extendNortheast a ha).schurFunction =
          (V.extendNortheast a ha).schurFunction := by
        rw [schurFunction_extendNortheast, capPolynomial_extendNortheast,
          schurFunction_extendNortheast, capPolynomial_extendNortheast]
        have hh := ratio_remainders_eq X Y r a hA
        simpa only [U, V, add_comm] using hh
      have hEb : (U.extendNortheast b hb).schurFunction =
          (V.extendNortheast b hb).schurFunction := by
        rw [schurFunction_extendNortheast, capPolynomial_extendNortheast,
          schurFunction_extendNortheast, capPolynomial_extendNortheast]
        have hh := ratio_remainders_eq X Y r b hB
        simpa only [U, V, add_comm] using hh
      have hUV := (two_positive_extensions U V hU hV a b a b ha hb ha hb hab.ne hab.ne
        (by simp only [extensionObservations, hEa, hEb])).1
      simpa only [U, V, deleteFirstRow_extendNortheast] using hUV.deleteFirstRow
  exact ⟨ht, ht.gridDefect_eq_zero⟩

/-- Actual ratio rigidity supplies the floor criterion on every supported union-grid shift. -/
theorem ratio_floor_supplies {n m : ℕ} (X : Diagram n) (Y : Diagram m)
    (hX : X.Connected) (hY : Y.Connected)
    (hinner : ∀ (i : Fin n) (j : Fin m), i.val = j.val → X.inner i = Y.inner j)
    (hG : gridDefect X Y ≠ 0) (r a : ℕ) (ha : 0 < a)
    (h : RatioIdentity (gridDefect X Y) r a) :
    gridDefect X Y 0 ≠ 0 ∧ ∀ d, gridDefect X Y d ≠ 0 →
      leastWeight squareWeight.generatorWeight (gridDefect X Y 0) -
        (leastWeight squareWeight.generatorWeight (gridDefect X Y d) + (d.toNat : ℝ) ^ 2) ≤
          2 * (ratioVirtualShift r a : ℝ) * (d.toNat : ℝ) := by
  have hn := rowCount_eq_of_ratioIdentity X Y hX hY r a ha h
  subst m
  have hin : X.inner = Y.inner := funext fun i => hinner i i rfl
  have hnormal := ratioIdentity_fixes_cap X Y hX hY hG r a ha h hinner
  have hgrid : ∀ j, X.capShift j = Y.capShift j := fun j => hnormal.2.2 j j rfl
  obtain ⟨_, _, _, _, _, _, hG0, hbound, _⟩ :=
    ratio_floor_same_count X Y hX hY hin hG r a ha h
  have hzero : gridDefect X Y 0 = cofactorDefect X Y 0 := by
    simpa only [X.capShift_zero] using gridDefect_apply_of_common_grid X Y hgrid 0
  refine ⟨by rwa [hzero], ?_⟩
  intro d hd
  have hex : ∃ j : Fin (n + 1), X.capShift j = d := by
    by_cases hx : X.cofactorGridVector d = 0
    · have hy : Y.cofactorGridVector d ≠ 0 := by
        intro hy
        exact hd (by simp [gridDefect, hx, hy])
      obtain ⟨j, hj⟩ := Y.exists_capShift_of_gridVector_ne_zero d hy
      exact ⟨j, (hgrid j).trans hj⟩
    · exact X.exists_capShift_of_gridVector_ne_zero d hx
  obtain ⟨j, hj⟩ := hex
  have hc : cofactorDefect X Y j ≠ 0 := by
    rw [← hj, gridDefect_apply_of_common_grid X Y hgrid j] at hd
    exact hd
  rw [hzero, ← hj, gridDefect_apply_of_common_grid X Y hgrid j]
  simpa only [squareWeight] using hbound j hc

private theorem same_base_cap_lengths_eq {n m : ℕ} (X : Diagram n) (Y : Diagram m)
    (hX : X.Connected) (hY : Y.Connected) (hG : gridDefect X Y ≠ 0)
    (r a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hA : RatioIdentity (gridDefect X Y) r a)
    (hB : RatioIdentity (gridDefect X Y) r b) : a = b := by
  by_contra hn
  rcases lt_or_gt_of_ne hn with hab | hba
  · exact hG (double_cap_kills X Y hX hY r a b ha hab hA hB).2
  · exact hG (double_cap_kills X Y hX hY r b a hb hba hB hA).2

private theorem zero_and_positive_base_cannot_coexist {n m : ℕ}
    (X : Diagram n) (Y : Diagram m) (hX : X.Connected) (hY : Y.Connected)
    (hG : gridDefect X Y ≠ 0) (gamma b : ℕ) (hgamma : 0 < gamma) (hb : 0 < b)
    (hzero : RatioIdentity (gridDefect X Y) 0 gamma)
    (hpositive : RatioIdentity (gridDefect X Y) gamma b) : False := by
  have hP0 := gridDefect_response_zero X Y hX.1 hY.1
  have hPgamma : gridResponse (gridDefect X Y) gamma = 0 := by
    have h := hzero
    unfold RatioIdentity at h
    simpa only [Nat.cast_zero, zero_add, hP0, mul_zero] using h
  have hPsum : gridResponse (gridDefect X Y) ((gamma + b : ℕ) : ℤ) = 0 := by
    have h := hpositive
    unfold RatioIdentity at h
    simpa only [Nat.cast_add, hPgamma, mul_zero] using h
  have hsumRatio : RatioIdentity (gridDefect X Y) 0 (gamma + b) := by
    unfold RatioIdentity
    simp only [Nat.cast_zero, zero_add, hP0, hPsum, mul_zero]
  exact hG (double_cap_kills X Y hX hY 0 gamma (gamma + b) hgamma (by omega)
    hzero hsumRatio).2

/-- With a common inner boundary, the square gap fixes the entire ratio-identity parameter pair. -/
theorem unique_ratio_same_count {n : ℕ} (X Y : Diagram n)
    (hX : X.Connected) (hY : Y.Connected) (hinner : X.inner = Y.inner)
    (hG : gridDefect X Y ≠ 0) (r a s b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hA : RatioIdentity (gridDefect X Y) r a)
    (hB : RatioIdentity (gridDefect X Y) s b) : r = s ∧ a = b := by
  obtain ⟨v, hv, hgrid, hprefix, hchanged, _⟩ :=
    ratio_rigidity_same_count X Y hX hY hinner hG r a ha hA
  have hgapA := ratio_square_gap_normalized X Y hX hY hgrid r a ha hA v hprefix hchanged
  have hgapB := ratio_square_gap_normalized X Y hX hY hgrid s b hb hB v hprefix hchanged
  have hn : 0 < n := hX.1
  let z : Fin n := ⟨0, hn⟩
  have hz : z.succ = (1 : Fin (n + 1)) := by
    apply Fin.ext
    change 1 = 1 % (n + 1)
    exact (Nat.mod_eq_of_lt (by omega)).symm
  have hdpos : 0 < (X.capShift 1).toNat := by
    have hd : 0 < X.capShift 1 := by rw [← hz]; exact X.capShift_succ_pos z
    omega
  have hdR : 0 < ((X.capShift 1).toNat : ℝ) := by exact_mod_cast hdpos
  have hgammaR : (ratioVirtualShift r a : ℝ) = (ratioVirtualShift s b : ℝ) := by
    nlinarith
  have hgamma : ratioVirtualShift r a = ratioVirtualShift s b := by
    exact_mod_cast hgammaR
  by_cases hr0 : r = 0
  · subst r
    by_cases hs0 : s = 0
    · subst s
      exact ⟨rfl, by simpa [ratioVirtualShift] using hgamma⟩
    · have hs : 0 < s := by omega
      have has : a = s := by
        simpa [ratioVirtualShift, hs0] using hgamma
      subst s
      exact (zero_and_positive_base_cannot_coexist X Y hX hY hG a b ha hb hA hB).elim
  · by_cases hs0 : s = 0
    · subst s
      have hr : 0 < r := by omega
      have hrb : r = b := by
        simpa [ratioVirtualShift, hr0] using hgamma
      subst r
      exact (zero_and_positive_base_cannot_coexist X Y hX hY hG b a hb ha hB hA).elim
    · have hrs : r = s := by
        simpa [ratioVirtualShift, hr0, hs0] using hgamma
      subst s
      exact ⟨rfl, same_base_cap_lengths_eq X Y hX hY hG r a b ha hb hA hB⟩

/-- `cor:unique-ratio`, with normalization and row count derived rather than supplied. -/
theorem unique_ratio {n m : ℕ} (X : Diagram n) (Y : Diagram m)
    (hX : X.Connected) (hY : Y.Connected)
    (hinner : ∀ (i : Fin n) (j : Fin m), i.val = j.val → X.inner i = Y.inner j)
    (hG : gridDefect X Y ≠ 0) (r a s b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hA : RatioIdentity (gridDefect X Y) r a)
    (hB : RatioIdentity (gridDefect X Y) s b) : r = s ∧ a = b := by
  have hn := rowCount_eq_of_ratioIdentity X Y hX hY r a ha hA
  subst m
  exact unique_ratio_same_count X Y hX hY (funext fun i => hinner i i rfl)
    hG r a s b ha hb hA hB

end Diagram
end SkewSchurReconstruction
