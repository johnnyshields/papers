/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
-- TODO-COPIED: skew-ribbon-coarsenings/lean/SkewRibbonCoarsenings/NestedStep.lean
import SkewRibbonCoarsenings.NestedJ
import SkewRibbonCoarsenings.NestedCut
import SkewRibbonCoarsenings.NestedSubsets
import SkewRibbonCoarsenings.NestedBottom

/-!
# The intermediate step of the nested marked identity

Formalizes `shields-2026-ribbon-coarsenings.tex`, section `sec:detector` (`thm:nested`, the
intermediate-step contraction `𝓙_{y_i}(y_{i-1}, 𝐑_i) = θ_{i-1} 𝓙_{y_{i-1}}(𝐑_i)`).

`NestedData` bundles the hypotheses `eq:chain`, `eq:detector-list`, `eq:layers` on the integers.
`step` is the contraction for `1 ≤ i ≤ L`, where `lab L = a` so that the case `i = L` is the step
from the full list `(y_{L-1}, …, y_0, r, s, z)` to the list with `y_{L-1}` removed.  Sorry-free.
-/

namespace SkewRibbonCoarsenings

open Finset Nested

/-- The arithmetic hypotheses of `eq:chain`--`eq:layers` for the normalized setting
`h : NormalizedSetting n S S' d e`: `e = p_0 ∣ ⋯ ∣ p_L ∣ d`, `𝓑_{p_i}` is `p_{i+1}`-periodic, the
layers `y_i ∈ p_i ℤ ∖ p_{i+1} ℤ`, `e ∤ r, s, z`, and the total is `n`; `a ∈ supp v` is the field
`a_supp`, with `a > 0`. -/
structure NestedData (n : ℕ) (S S' : Finset ℕ) (d e L : ℕ) (p : ℕ → ℕ) (a r s z : ℕ)
    (y : ℕ → ℕ) : Prop where
  L_pos : 1 ≤ L
  p0 : p 0 = e
  pL_dvd : p L ∣ d
  chain : ∀ i < L, p i ∣ p (i + 1)
  strict : ∀ i < L, p i < p (i + 1)
  period : ∀ i < L, IsPeriod (maskFun n S (p i)) (p (i + 1))
  a_pos : 0 < a
  a_supp : vFun n S S' (a : ZMod n) ≠ 0
  sum_eq : a + ∑ k ∈ Finset.range L, y k + (r + s + z) = n
  dvd_y : ∀ k < L, p k ∣ y k
  ndvd_y : ∀ k < L, ¬ p (k + 1) ∣ y k
  ndvd_r : ¬ e ∣ r
  ndvd_s : ¬ e ∣ s
  ndvd_z : ¬ e ∣ z

section Step

variable {n : ℕ} {S S' : Finset ℕ} {d e L : ℕ} {p : ℕ → ℕ} {a r s z : ℕ} {y : ℕ → ℕ}

namespace NestedData

variable (D : NestedData n S S' d e L p a r s z y) (h : NormalizedSetting n S S' d e)
include D h

/-- `p_L ∣ a`: a support element of `v` lies on the `d`-grid, and `p_L ∣ d`. -/
lemma dvd_a [NeZero n] : p L ∣ a := by
  have hd : d ∣ a := dvd_of_vFun_ne h D.a_supp
  exact D.pL_dvd.trans hd

/-- The layer data of `NestedSubsets` for the hypotheses of `NestedData`. -/
lemma layers [NeZero n] : LayerData L p n a r s z y where
  chain := D.chain
  dvd_a := D.dvd_a h
  dvd_n := D.pL_dvd.trans (d_dvd_n h)
  sum_eq := D.sum_eq
  dvd_y := D.dvd_y
  ndvd_y := D.ndvd_y
  ndvd_r := by rw [D.p0]; exact D.ndvd_r
  ndvd_s := by rw [D.p0]; exact D.ndvd_s
  ndvd_z := by rw [D.p0]; exact D.ndvd_z

lemma p_dvd_n [NeZero n] {k : ℕ} (hk : k ≤ L) : p k ∣ n :=
  (D.layers h).dvd_n_of hk

lemma p_dvd_d [NeZero n] {k : ℕ} (hk : k ≤ L) : p k ∣ d :=
  ((D.layers h).chain_le hk le_rfl).trans D.pL_dvd

lemma e_dvd_p [NeZero n] {k : ℕ} (hk : k ≤ L) : e ∣ p k := by
  have := (D.layers h).chain_le (Nat.zero_le k) hk
  rwa [D.p0] at this

/-- The factor `θ'_i = b(y_i + y_{i-1}) - b(y_{i-1})` of the contraction at level `i`, with
`y_L = a` (`lab`).  For `i = L` it is `Δ`, for `i < L` it is `θ_{i-1}`
(`stepFactor_eq_theta`). -/
def stepFactor (n : ℕ) (S : Finset ℕ) (L a : ℕ) (y : ℕ → ℕ) (i : ℕ) : ℤ :=
  cutInd n S ((lab L a y i + lab L a y (i - 1) : ℕ) : ZMod n) -
    cutInd n S ((lab L a y (i - 1) : ℕ) : ZMod n)

/-- The intermediate-step contraction of `thm:nested`: for `1 ≤ i ≤ L`,
`𝓙_{y_i}(y_{i-1}, 𝐑_i) = θ_{i-1} 𝓙_{y_{i-1}}(𝐑_i)` (with `y_L = a` and `θ_{L-1}` replaced by `Δ`),
in the chain-sum form `JJ` over the positions `Jset L i`. -/
lemma step [NeZero n] {i : ℕ} (hi1 : 1 ≤ i) (hiL : i ≤ L) :
    JJ n S (detList L a r s z y) (lab L a y i) (Jset L i) =
      stepFactor n S L a y i *
        JJ n S (detList L a r s z y) (lab L a y (i - 1)) (Jset L (i - 1)) := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hLD := D.layers h
  have hjL : j ≤ L := by omega
  have hjL' : j < L := by omega
  have hx : yIdx L j ∈ Jset L (j + 1) := by rw [Jset_succ hjL]; exact mem_insert_self _ _
  have herase := Jset_erase (L := L) hjL
  have hmx : detList L a r s z y (yIdx L j) = lab L a y j := detList_yIdx' hjL
  have hne : ((Jset L (j + 1)).erase (yIdx L j)).Nonempty := by
    rw [herase]; exact ⟨rIdx L, Bset_subset_Jset j (by simp [Bset])⟩
  have hpn : p j ∣ n := D.p_dvd_n h hjL
  have hdiff : ∀ X : Finset (Fin (L + 4)), ∅ ⊂ X → X ⊂ Jset L (j + 1) → X ≠ {yIdx L j} →
      X ≠ (Jset L (j + 1)).erase (yIdx L j) →
      cutInd n S ((lab L a y (j + 1) + ∑ i ∈ X, detList L a r s z y i : ℕ) : ZMod n) =
        cutInd n S ((∑ i ∈ X, detList L a r s z y i : ℕ) : ZMod n) := by
    intro X hX1 hX2 hX3 hX4
    have hXne : X.Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.ssubset_iff_subset_ne.mp hX1).2.symm
    have hnd : ¬ p j ∣ ∑ i ∈ X, detList L a r s z y i := by
      intro hd
      have := hLD.grid_step (i := j + 1) (by omega) hiL hX2.subset hXne
        (by simpa using hd)
      simp only [Nat.add_sub_cancel] at this
      rcases this with h' | h' | h'
      · exact hX3 h'
      · exact hX4 (by rw [herase]; exact h')
      · exact hX2.ne h'
    exact cutInd_add_of_period hpn (D.period j hjL') (D.chain j hjL') (hLD.dvd_lab hiL) hnd
  have h1 : cutInd n S ((lab L a y (j + 1) + detList L a r s z y (yIdx L j) : ℕ) : ZMod n) -
      cutInd n S ((detList L a r s z y (yIdx L j) : ℕ) : ZMod n) =
      stepFactor n S L a y (j + 1) := by
    rw [hmx]; simp [stepFactor]
  -- reflection step
  have hpj1 : p (j + 1) ∣ n := D.p_dvd_n h hiL
  have hxz : ¬ p (j + 1) ∣ lab L a y j := by
    rw [lab, if_pos hjL']; exact D.ndvd_y j hjL'
  have hYd : p (j + 1) ∣ lab L a y (j + 1) := hLD.dvd_lab hiL
  have hYx : ¬ p (j + 1) ∣ lab L a y (j + 1) + lab L a y j :=
    fun h' => hxz ((Nat.dvd_add_right hYd).mp h')
  have hU : ∑ i ∈ Jset L j, detList L a r s z y i =
      (∑ k ∈ Finset.range j, lab L a y k) + (r + s + z) := sum_Jset (by omega)
  have hA' : lab L a y (j + 1) + ∑ i ∈ Jset L j, detList L a r s z y i + lab L a y j =
      (∑ k ∈ Finset.range (j + 2), lab L a y k) + (r + s + z) := by
    rw [hU, Finset.sum_range_succ, Finset.sum_range_succ]; ring
  obtain ⟨Q, hper, hpQ, hQA⟩ : ∃ Q, IsPeriod (maskFun n S (p (j + 1))) Q ∧ p (j + 1) ∣ Q ∧
      Q ∣ lab L a y (j + 1) + ∑ i ∈ Jset L j, detList L a r s z y i + lab L a y j := by
    rcases Nat.lt_or_ge (j + 1) L with hlt | hge
    · refine ⟨p (j + 2), D.period (j + 1) hlt, D.chain (j + 1) hlt, ?_⟩
      rw [hA']
      have h2 := hLD.dvd_T (a := a) (r := r) (s := s) (z := z) (y := y) (j := j + 2) (by omega)
      rwa [sum_Jset (by omega)] at h2
    · have hL : j + 1 = L := le_antisymm hiL hge
      refine ⟨n, fun x => by simp, hpj1, ?_⟩
      rw [hA']
      have h2 := hLD.sum_lab
      rw [show j + 2 = L + 1 by omega]
      rw [h2]
  have hy1 : cutInd n S ((lab L a y (j + 1) + ∑ i ∈ Jset L j, detList L a r s z y i : ℕ) :
      ZMod n) = cutInd n S (-((lab L a y j : ℕ) : ZMod n)) := by
    have := cutInd_sub_of_period (n := n) (S := S) hpj1 hper hpQ hQA hxz
    rw [← this]; congr 1; push_cast; ring
  have hy2 : cutInd n S ((∑ i ∈ Jset L j, detList L a r s z y i : ℕ) : ZMod n) =
      cutInd n S (-((lab L a y (j + 1) + lab L a y j : ℕ) : ZMod n)) := by
    have := cutInd_sub_of_period (n := n) (S := S) hpj1 hper hpQ
      (show Q ∣ lab L a y (j + 1) + ∑ i ∈ Jset L j, detList L a r s z y i + lab L a y j from hQA)
      hYx
    rw [← this]; congr 1; push_cast; ring
  have hed : e ∣ d := h.e_dvd_d
  have hep : e ∣ p (j + 1) := D.e_dvd_p h hiL
  have hpd : p (j + 1) ∣ d := D.p_dvd_d h hiL
  have hex : e ∣ lab L a y j := (D.e_dvd_p h hjL).trans (hLD.dvd_lab hjL)
  have heY : e ∣ lab L a y (j + 1) + lab L a y j :=
    Nat.dvd_add (hep.trans hYd) hex
  have n1 := cutInd_neg_eq h hpj1 hep hpd hxz
  have n2 := cutInd_neg_eq h hpj1 hep hpd hYx
  rw [wFun_nat_of_dvd_e h hex] at n1
  rw [wFun_nat_of_dvd_e h heY] at n2
  have h2 : cutInd n S ((lab L a y (j + 1) + ∑ i ∈ Jset L j, detList L a r s z y i : ℕ) :
        ZMod n) - cutInd n S ((∑ i ∈ Jset L j, detList L a r s z y i : ℕ) : ZMod n) =
      -stepFactor n S L a y (j + 1) := by
    rw [hy1, hy2, n1, n2]; simp only [stepFactor, Nat.add_sub_cancel]; ring
  have key := JJ_contract n S (detList L a r s z y) (lab L a y (j + 1)) hx hne
    (stepFactor n S L a y (j + 1)) hdiff h1 (by rw [herase]; exact h2)
  rw [herase, hmx] at key
  exact key

end NestedData

end Step

end SkewRibbonCoarsenings
