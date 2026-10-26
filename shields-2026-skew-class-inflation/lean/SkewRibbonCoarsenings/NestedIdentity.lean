/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
-- TODO-COPIED: skew-ribbon-coarsenings/lean/SkewRibbonCoarsenings/NestedIdentity.lean
import SkewRibbonCoarsenings.NestedTop
import SkewRibbonCoarsenings.NestedBottom

/-!
# The nested marked identity

Formalizes `shields-2026-ribbon-coarsenings.tex`, section `sec:detector` (`eq:deltaH`,
`thm:nested`, `eq:nested-product`).

`deltaFun`, `thetaFun`, `Hfun` are the quantities `Δ`, `θ_i`, `H_y` of `eq:deltaH` (`fY` is `f_y`),
and `NestedData` collects the hypotheses `eq:chain`--`eq:layers`.  `nested_identity` is
`thm:nested`: the product formula `eq:nested-product`, the bound `|ΔK| ≤ 2`, and the count of
labels.  Sorry-free.
-/

namespace SkewRibbonCoarsenings

open Finset Nested

section Nested

variable {n : ℕ} {S S' : Finset ℕ} {d e L : ℕ} {p : ℕ → ℕ} {a r s z : ℕ} {y : ℕ → ℕ}

/-- `eq:deltaH`: `Δ = b(a + t) - b(t)`. -/
def deltaFun (n : ℕ) (S : Finset ℕ) (a t : ℕ) : ℤ :=
  cutInd n S ((a + t : ℕ) : ZMod n) - cutInd n S ((t : ℕ) : ZMod n)

/-- `eq:deltaH`: `θ_i = 𝓑_{p_{i+1}}(y_i + y_{i+1}) - 𝓑_{p_{i+1}}(y_i)`. -/
def thetaFun (n : ℕ) (S : Finset ℕ) (p y : ℕ → ℕ) (i : ℕ) : ℤ :=
  maskFun n S (p (i + 1)) ((y i + y (i + 1) : ℕ) : ZMod n) -
    maskFun n S (p (i + 1)) ((y i : ℕ) : ZMod n)

namespace NestedData

variable (D : NestedData n S S' d e L p a r s z y) (h : NormalizedSetting n S S' d e)
include D h

lemma stepFactor_eq_theta [NeZero n] {k : ℕ} (hk1 : 1 ≤ k) (hkL : k < L) :
    stepFactor n S L a y k = thetaFun n S p y (k - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  unfold stepFactor thetaFun
  have hpn : p (j + 1) ∣ n := D.p_dvd_n h hkL.le
  have hy0 : ¬ p (j + 1) ∣ y j := D.ndvd_y j (by omega)
  have hy1 : p (j + 1) ∣ y (j + 1) := D.dvd_y (j + 1) hkL
  have hs : ¬ p (j + 1) ∣ y j + y (j + 1) := fun h' => hy0 ((Nat.dvd_add_left hy1).mp h')
  rw [maskFun_nat_of_ndvd hpn hs, maskFun_nat_of_ndvd hpn hy0]
  simp only [Nat.add_sub_cancel, Nested.lab, if_pos hkL, if_pos (show j < L by omega)]
  rw [add_comm (y (j + 1)) (y j)]

/-- The telescoped contraction of the intermediate steps: for `1 ≤ i ≤ L`,
`𝓙_{y_i}(y_{i-1}, …, y_0, r, s, z) = (∏_{k=1}^{i} θ'_k) 𝓙_{y_0}(r, s, z)`. -/
lemma telescope [NeZero n] : ∀ i, 1 ≤ i → i ≤ L →
    JJ n S (detList L a r s z y) (Nested.lab L a y i) (Jset L i) =
      (∏ k ∈ Finset.Icc 1 i, stepFactor n S L a y k) *
        JJ n S (detList L a r s z y) (Nested.lab L a y 0) (Jset L 0) := by
  intro i
  induction i with
  | zero => intro h0; omega
  | succ i ih =>
    intro _ hiL
    rw [D.step h (i := i + 1) (by omega) hiL, Nat.add_sub_cancel]
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp
    · rw [ih hi (by omega), ← mul_assoc, Finset.prod_Icc_succ_top (by omega), mul_comm
        (stepFactor n S L a y (i + 1))]

/-- The bottom contribution: `𝓙_{y_0}(r, s, z) = -H_{y_0}(r, s, z)`. -/
lemma bottom [NeZero n] :
    JJ n S (detList L a r s z y) (Nested.lab L a y 0) (Jset L 0) =
      - Hfun n S S' d e (y 0) r s z := by
  have hL : 0 < L := D.L_pos
  have hlab : Nested.lab L a y 0 = y 0 := by simp [Nested.lab, hL]
  rw [hlab, Jset_zero]
  have hLD := D.layers h
  have hen : e ∣ n := by simpa [D.p0] using D.p_dvd_n h (Nat.zero_le L)
  have hep : e ∣ p 1 := D.e_dvd_p h hL
  have hper : IsPeriod (maskFun n S e) (p 1) := by
    simpa [D.p0] using D.period 0 hL
  have hp1 : p 1 ∣ y 0 + (r + s + z) := by
    have h1 := hLD.dvd_T (a := a) (r := r) (s := s) (z := z) (y := y) (j := 1) hL
    rwa [sum_Jset (by omega), Finset.sum_range_one, Nested.lab, if_pos hL] at h1
  have hy : e ∣ y 0 := by simpa [D.p0] using D.dvd_y 0 hL
  have := JJ_bottom h (ι := Fin (L + 4)) (rIdx_ne_sIdx (L := L)) (rIdx_ne_zIdx (L := L))
    (sIdx_ne_zIdx (L := L)) (detList L a r s z y) hen h.e_dvd_d hep hper
    (by rw [detList_rIdx, detList_sIdx, detList_zIdx]; exact hp1) hy
    (by rw [detList_rIdx]; exact D.ndvd_r) (by rw [detList_sIdx]; exact D.ndvd_s)
    (by rw [detList_zIdx]; exact D.ndvd_z)
  rw [detList_rIdx, detList_sIdx, detList_zIdx] at this
  exact this

/-- `eq:nested-product` in the chain-sum form: the product of the step factors times the bottom. -/
lemma delta_K_formula [NeZero n] :
    (K S (detList L a r s z y) : ℤ) - (K S' (detList L a r s z y) : ℤ) =
      - vFun n S S' (a : ZMod n) * deltaFun n S a (y (L - 1)) *
        (∏ i ∈ Finset.range (L - 1), thetaFun n S p y i) * Hfun n S S' d e (y 0) r s z := by
  have hL := D.L_pos
  rw [D.delta_K_eq h]
  have hJ : Jset L L = Jset L L := rfl
  have hlabL : Nested.lab L a y L = a := by simp [Nested.lab]
  have hlabL1 : Nested.lab L a y (L - 1) = y (L - 1) := by
    simp [Nested.lab, show L - 1 < L by omega]
  have hT := D.telescope h L hL le_rfl
  rw [hlabL] at hT
  rw [hT, D.bottom h]
  have hprod : ∏ k ∈ Finset.Icc 1 L, stepFactor n S L a y k =
      deltaFun n S a (y (L - 1)) * ∏ i ∈ Finset.range (L - 1), thetaFun n S p y i := by
    obtain ⟨m, rfl⟩ : ∃ m, L = m + 1 := ⟨L - 1, by omega⟩
    rw [Finset.prod_Icc_succ_top (by omega)]
    have : stepFactor n S (m + 1) a y (m + 1) = deltaFun n S a (y (m + 1 - 1)) := by
      unfold stepFactor deltaFun
      simp only [Nat.add_sub_cancel, Nested.lab, lt_irrefl, if_false, lt_add_one, if_true]
    rw [this, Nat.add_sub_cancel, mul_comm]
    congr 1
    have hall : ∀ m' ≤ m, ∏ k ∈ Finset.Icc 1 m', stepFactor n S (m + 1) a y k =
        ∏ i ∈ Finset.range m', thetaFun n S p y i := by
      intro m'
      induction m' with
      | zero => intro _; simp
      | succ m' ih =>
        intro hm'
        rw [Finset.prod_Icc_succ_top (by omega), Finset.prod_range_succ, ih (by omega),
          D.stepFactor_eq_theta h (by omega) (by omega)]
        simp
    exact hall m le_rfl
  rw [hprod]
  ring

end NestedData

lemma neZero_of_setting (h : NormalizedSetting n S S' d e) : NeZero n :=
  ⟨by intro h0; have := h.three_le_ratio; simp [h0] at this⟩

/-- A difference of two `{0, 1}`-valued cut values lies in `{-1, 0, 1}`. -/
lemma cutInd_sub_abs_le (S : Finset ℕ) (x y : ZMod n) : |cutInd n S x - cutInd n S y| ≤ 1 := by
  rcases Nested.cutInd_cases (n := n) S x with a | a <;>
  rcases Nested.cutInd_cases (n := n) S y with b | b <;> simp [a, b]

lemma cutInd_sub_abs_le' (S S' : Finset ℕ) (x : ZMod n) : |cutInd n S x - cutInd n S' x| ≤ 1 := by
  rcases Nested.cutInd_cases (n := n) S x with a | a <;>
  rcases Nested.cutInd_cases (n := n) S' x with b | b <;> simp [a, b]

lemma maskFun_sub_abs_le (S : Finset ℕ) (q : ℕ) (x y : ZMod n) :
    |maskFun n S q x - maskFun n S q y| ≤ 1 := by
  rcases Nested.maskFun_cases (n := n) S q x with a | a <;>
  rcases Nested.maskFun_cases (n := n) S q y with b | b <;> simp [a, b]

/-- `thm:nested` (`eq:nested-product`): under `eq:chain`--`eq:layers`, for the labeled list
`𝐚 = (a, y_{L-1}, …, y_0, r, s, z)` (`detList`, on the `L + 4` positions `Fin (L + 4)`, with total
`n`),
`ΔK = -v(a) Δ (∏_{i=0}^{L-2} θ_i) H_{y_0}(r, s, z)` with `Δ = b(a + t) - b(t)`, `t = y_{L-1}`;
the empty product (`L = 1`) is one; and `|ΔK| ≤ 2`.  Here `ΔK = K_b - K_c`. -/
theorem nested_identity (h : NormalizedSetting n S S' d e)
    (D : NestedData n S S' d e L p a r s z y) :
    ((K S (detList L a r s z y) : ℤ) - (K S' (detList L a r s z y) : ℤ) =
        - vFun n S S' (a : ZMod n) * deltaFun n S a (y (L - 1)) *
          (∏ i ∈ Finset.range (L - 1), thetaFun n S p y i) * Hfun n S S' d e (y 0) r s z) ∧
      |(K S (detList L a r s z y) : ℤ) - (K S' (detList L a r s z y) : ℤ)| ≤ 2 ∧
      Fintype.card (Fin (L + 4)) = L + 4 ∧
      ∑ i, detList L a r s z y i = n := by
  have : NeZero n := neZero_of_setting h
  have hform := D.delta_K_formula h
  refine ⟨hform, ?_, Fintype.card_fin _, D.sum_total h⟩
  rw [hform]
  have hL := D.L_pos
  have hv : |vFun n S S' (a : ZMod n)| ≤ 1 :=
    cutInd_sub_abs_le' (n := n) S S' (a : ZMod n)
  have hΔ : |deltaFun n S a (y (L - 1))| ≤ 1 := by
    unfold deltaFun; exact cutInd_sub_abs_le (n := n) S _ _
  have hθ : |∏ i ∈ Finset.range (L - 1), thetaFun n S p y i| ≤ 1 := by
    rw [Finset.abs_prod]
    refine Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) (fun i _ => ?_)
    unfold thetaFun
    exact maskFun_sub_abs_le S _ _ _
  have hy0 : e ∣ y 0 := by simpa [D.p0] using D.dvd_y 0 hL
  have hen : e ∣ n := by simpa [D.p0] using D.p_dvd_n h (Nat.zero_le L)
  have hH : |Hfun n S S' d e (y 0) r s z| ≤ 2 := by
    unfold Hfun
    exact H_bound_aux _ _ _ _ _ _ (fY_cases S e _ _) (fY_cases S e _ _) (fY_cases S e _ _)
      (wFun_ternary S S' d _) (wFun_ternary S S' d _) (wFun_ternary S S' d _)
      (fY_mul_w h hen hy0 D.ndvd_r) (fY_mul_w h hen hy0 D.ndvd_s) (fY_mul_w h hen hy0 D.ndvd_z)
  rw [show ∀ A B C E : ℤ, -A * B * C * E = -(A * B * C * E) from fun _ _ _ _ => by ring,
    abs_neg, abs_mul, abs_mul, abs_mul]
  have h1 : |vFun n S S' (a : ZMod n)| * |deltaFun n S a (y (L - 1))| ≤ 1 := by
    calc _ ≤ 1 * 1 := mul_le_mul hv hΔ (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have h2 : |vFun n S S' (a : ZMod n)| * |deltaFun n S a (y (L - 1))| *
      |∏ i ∈ Finset.range (L - 1), thetaFun n S p y i| ≤ 1 := by
    calc _ ≤ 1 * 1 := mul_le_mul h1 hθ (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  calc _ ≤ 1 * 2 := mul_le_mul h2 hH (abs_nonneg _) zero_le_one
    _ = 2 := by norm_num

end Nested

end SkewRibbonCoarsenings
