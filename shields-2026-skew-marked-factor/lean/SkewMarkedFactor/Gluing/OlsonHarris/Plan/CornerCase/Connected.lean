/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
-- TODO-COPIED: skew-gluing/lean/SkewGluing/OlsonHarris/Plan/CornerCase/Connected.lean
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.CornerCase.Combinatorics
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.CornerCase.Disconnected
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.CornerCase.HatMark
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.CornerCase.NoRightRibbons
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.MurnaghanNakayama
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.MarkFacts

/-!
# The corner equations for a connected outer

Formalizes `shields-2026-skew-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `eq:gluing-offsets`, `def:gluing-graph`): thesis Lemma 5.5.12, for a legal mark of
case (c) and a connected outer, from the combinatorial inputs of
`SkewMarkedFactor.Gluing.OlsonHarris.Plan.CornerCase.Combinatorics` and Murnaghan–Nakayama in the derivation
form (`pDeriv_cellSchur_left`, `pDeriv_cellSchur_right`).

* `pDeriv_modCompC_connected`: `p_{mq}^⊥` kills the corner modified composition
  (`([D] □_W E) ↼ p_{mq} = 0`);
* `ribbonSum_modCompC_connected`: the two signed ribbon sums agree
  (`p_{mq} ⇀ ([D] □_W E) = ± ((p_m ⇀ [D] - [D] ↼ p_m) □_W E)` and the left half is zero);
* `cornerEq_connected`: `CornerEq ω D m`.

Sorry-free.
-/

namespace SkewMarkedFactor.Gluing

namespace Plan

namespace Corner

open MarkedInner

/-! ### Derivations kill products of killed elements -/

theorem pDeriv_pow_eq_zero {a : Lambda} (k n : ℕ) (h : pDeriv k a = 0) :
    pDeriv k (a ^ n) = 0 := by
  rw [Derivation.leibniz_pow, h]
  simp

theorem pDeriv_mul_eq_zero {a b : Lambda} (k : ℕ) (ha : pDeriv k a = 0) (hb : pDeriv k b = 0) :
    pDeriv k (a * b) = 0 := by
  rw [Derivation.leibniz, ha, hb]
  simp

theorem pDeriv_neg_one_pow (k n : ℕ) : pDeriv k ((-1 : Lambda) ^ n) = 0 := by
  refine pDeriv_pow_eq_zero k n ?_
  rw [map_neg, Derivation.map_one_eq_zero, neg_zero]

/-! ### The corner modified composition of a connected outer -/

theorem modCompC_connected {ω : MarkedInner} {D : Diagram} (hD : IsConnectedSkew D) :
    modCompC ω D = cornerPrefactor ω D * cellSchur (ω.compose D) := by
  unfold modCompC
  rw [edgeComponents_eq_singleton hD.2, Finset.prod_singleton, componentTc_eq]

section Legal

variable {ω : MarkedInner} {D : Diagram}

/-- `p_{mq}^⊥` kills the three factors `s_W`, `s_{\overline W}`, `s_{\overline O}` of the hat
factor, since they have fewer than `q` diagonals (thesis Lemma 5.5.9). -/
theorem pDeriv_hat_shapes (hω : ω.IsLegal) (hc : ω.case = .c) {m : ℕ} (hm : 0 < m) :
    pDeriv (m * ω.period.toNat) (cellSchur ω.W) = 0 ∧
      pDeriv (m * ω.period.toNat) (cellSchur (hatMarkFin ω)) = 0 ∧
      pDeriv (m * ω.period.toNat) (cellSchur (hatMiddleFin ω)) = 0 := by
  have hq := period_toNat_pos hω
  have hcast := hω.period_toNat_cast
  have hN : 0 < m * ω.period.toNat := Nat.mul_pos hm hq
  have hle : ω.period.toNat ≤ m * ω.period.toNat := Nat.le_mul_of_pos_left _ hm
  have hnon := isNonemptyMark_of_case_c hω hc
  have hwidth : ω.width < ω.period.toNat := by
    have := hω.2.2.1.2
    omega
  have hskH := isSkew_hatMarkFin hω hc
  have hskO := hω.isSkew_hatMiddleFin
  refine ⟨?_, ?_, ?_⟩
  · exact pDeriv_cellSchur_eq_zero_of_span_lt (by
      change ω.width < _
      omega)
  · exact pDeriv_cellSchur_eq_zero_of_span_lt (by
      have := MarkedInner.span_hatMarkFin_le ω
      omega)
  · exact pDeriv_cellSchur_eq_zero_of_span_lt (by
      have := corner_span_hatMiddle_lt hω hc
      omega)

/-- **The first corner equation, connected outer** (thesis Lemma 5.5.12, `↼ p_{mq} = 0`). -/
theorem pDeriv_modCompC_connected (hω : ω.IsLegal) (hc : ω.case = .c) (hD : IsConnectedSkew D)
    {m : ℕ} (hm : 0 < m) : pDeriv (m * ω.period.toNat) (modCompC ω D) = 0 := by
  have hN : 0 < m * ω.period.toNat := Nat.mul_pos hm (period_toNat_pos hω)
  obtain ⟨h1, h2, h3⟩ := pDeriv_hat_shapes hω hc hm
  have hF := hω.isConnectedSkew_compose hD
  have hFl : pDeriv (m * ω.period.toNat) (cellSchur (ω.compose D)) = 0 := by
    rw [pDeriv_cellSchur_left hF.1 hN]
    simp [ribbonSumLeft, corner_no_leftRibbons hω hc hD hm]
  rw [modCompC_connected hD]
  unfold cornerPrefactor
  refine pDeriv_mul_eq_zero _ ?_ hFl
  exact pDeriv_mul_eq_zero _ (pDeriv_mul_eq_zero _ (pDeriv_mul_eq_zero _
    (pDeriv_neg_one_pow _ _) (pDeriv_pow_eq_zero _ _ h1)) (pDeriv_pow_eq_zero _ _ h2))
    (pDeriv_pow_eq_zero _ _ h3)

/-- **The second corner equation, connected outer** (thesis Lemma 5.5.12): the signed ribbon
sums on the right and on the left agree.  The ribbons of size `m q` removable on the right from
`D ∘_ω E` are the lifts of the ribbons removable from `D` on the right (sign `+`) and on the left
(sign `-`), and none is removable on the left, so Murnaghan–Nakayama on both sides gives
`σ^m (s_W s_{\overline W} s_{\overline O})^m (R - L) = 0`. -/
theorem ribbonSum_modCompC_connected (hω : ω.IsLegal) (hc : ω.case = .c)
    (hD : IsConnectedSkew D) {m : ℕ} (hm : 0 < m) :
    ribbonSumRight (modCompC ω) D m = ribbonSumLeft (modCompC ω) D m := by
  have hN : 0 < m * ω.period.toNat := Nat.mul_pos hm (period_toNat_pos hω)
  have hF := hω.isConnectedSkew_compose hD
  have hFl : pDeriv (m * ω.period.toNat) (cellSchur (ω.compose D)) = 0 := by
    rw [pDeriv_cellSchur_left hF.1 hN]
    simp [ribbonSumLeft, corner_no_leftRibbons hω hc hD hm]
  have hFr : ribbonSumRight cellSchur (ω.compose D) (m * ω.period.toNat) = 0 := by
    rw [← pDeriv_cellSchur_right hF.1 hN]
    exact hFl
  obtain ⟨σ, hσ, H⟩ := corner_ribbon_lift hω hc
  obtain ⟨liftR, liftL, hset, injR, injL, hdisj, hRid, hLid⟩ := H D hD m hm
  have hcoef : (σ : Lambda) ^ m * hatFactor ω ^ m ≠ 0 := by
    refine mul_ne_zero (pow_ne_zero _ ?_) (pow_ne_zero _ (hatFactor_ne_zero hω))
    rcases hσ with rfl | rfl <;> simp
  have key : (σ : Lambda) ^ m * hatFactor ω ^ m *
      (ribbonSumRight (modCompC ω) D m - ribbonSumLeft (modCompC ω) D m) = 0 := by
    have h0 : cornerPrefactor ω D *
        ribbonSumRight cellSchur (ω.compose D) (m * ω.period.toNat) = 0 := by
      rw [hFr, mul_zero]
    unfold ribbonSumRight at h0
    rw [hset, Finset.sum_union hdisj, Finset.sum_image injR, Finset.sum_image injL,
      mul_add, Finset.mul_sum, Finset.mul_sum] at h0
    have e1 : ∀ A ∈ rightRibbons D m, cornerPrefactor ω D * (((ribbonSign (liftR A) : ℤ) :
        Lambda) * cellSchur (ω.compose D \ liftR A)) =
        (σ : Lambda) ^ m * hatFactor ω ^ m * ((ribbonSign A : Lambda) * modCompC ω (D \ A)) := by
      intro A hA
      rw [← mul_assoc, hRid A hA]
      ring
    have e2 : ∀ A ∈ leftRibbons D m, cornerPrefactor ω D * (((ribbonSign (liftL A) : ℤ) :
        Lambda) * cellSchur (ω.compose D \ liftL A)) =
        -((σ : Lambda) ^ m * hatFactor ω ^ m * ((ribbonSign A : Lambda) *
          modCompC ω (D \ A))) := by
      intro A hA
      rw [← mul_assoc, hLid A hA]
      ring
    rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_neg_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum] at h0
    unfold ribbonSumRight ribbonSumLeft
    rw [mul_sub]
    linear_combination h0
  have := (mul_eq_zero.mp key).resolve_left hcoef
  exact sub_eq_zero.mp this

/-- **The corner equations for a connected outer** (thesis Lemma 5.5.12). -/
theorem cornerEq_connected (hω : ω.IsLegal) (hc : ω.case = .c) (hD : IsConnectedSkew D)
    {m : ℕ} (hm : 0 < m) : CornerEq ω D m :=
  ⟨pDeriv_modCompC_connected hω hc hD hm, ribbonSum_modCompC_connected hω hc hD hm⟩

end Legal

end Corner

end Plan

end SkewMarkedFactor.Gluing
