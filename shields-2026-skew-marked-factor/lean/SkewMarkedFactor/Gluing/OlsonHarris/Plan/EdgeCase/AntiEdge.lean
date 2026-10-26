/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
-- TODO-COPIED: skew-gluing/lean/SkewGluing/OlsonHarris/Plan/EdgeCase/AntiEdge.lean
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.EdgeCase.AntiHat
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.EdgeCase.Involution
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.EdgeCase.Reduction

/-!
# The edge equations for case (b) from case (a)

Formalizes `shields-2026-skew-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `eq:gluing-offsets`, `eq:gluing-gauge`): thesis Thm. 5.4.9
(`OlsonHarris2024HopfApplications`), for a legal mark of case (b).

The antitransposed mark `ω^{AT}` of a legal mark of case (b) is legal of case (a), with
`modComp ω^{AT} = ι ∘ modComp ω` and `hatFactor ω^{AT} = ι (hatFactor ω)`, and `p_n^⊥ ι =
(-1)^{n-1} ι p_n^⊥`; applying the involutive `ι` to the edge equations of `ω^{AT}` gives those of
`ω`, with the sign of `edgeSign`.

Sorry-free.
-/

set_option linter.style.openClassical false

namespace SkewMarkedFactor.Gluing

open Plan

open scoped Classical

namespace MarkedInner

theorem W_nonempty_of_case_b {ω : MarkedInner} (hω : ω.IsLegal) (hc : ω.case = .b) :
    ω.W.Nonempty := by
  rcases hω.1.2 with hemp | hnon
  · have := hemp.2.2
    rw [hc] at this
    exact absurd this (by simp)
  · exact hnon.1

theorem edgeSign_anti {ω : MarkedInner} (hc : ω.case = .b) (hq : 0 < ω.period) {m : ℕ}
    (hm : 0 < m) :
    edgeSign ω m = (-1) ^ (m * ω.period.toNat - 1) * edgeSign ω.anti m := by
  have hca : ω.anti.case = .a := by rw [anti_case, hc]; rfl
  unfold edgeSign
  rw [hc, hca]
  simp only [anti_v, atVec_fst]
  have hperiod : (ω.period.toNat : ℤ) = ω.v.2 - ω.v.1 := by
    have : ω.period = ω.v.2 - ω.v.1 := rfl
    omega
  have hpar : ((ω.period.toNat + ω.v.1.natAbs + (-ω.v.2).natAbs : ℕ) : ℤ) % 2 = 0 := by omega
  have hev : Even (ω.period.toNat + ω.v.1.natAbs + (-ω.v.2).natAbs) := by
    rw [Nat.even_iff]; omega
  have h1 : (-1 : ℤ) ^ (m * (ω.period.toNat + ω.v.1.natAbs + (-ω.v.2).natAbs)) = 1 := by
    rw [mul_comm, pow_mul, hev.neg_one_pow, one_pow]
  have hn : 0 < m * ω.period.toNat := Nat.mul_pos hm (by omega)
  have e1 : (-1 : ℤ) ^ (m * ω.period.toNat - 1) = -((-1) ^ (m * ω.period.toNat)) := by
    obtain ⟨k, hk⟩ : ∃ k, m * ω.period.toNat = k + 1 := ⟨m * ω.period.toNat - 1, by omega⟩
    rw [hk, Nat.add_sub_cancel, pow_succ]; ring
  rw [e1]
  have e2 : (-1 : ℤ) ^ (m * (ω.period.toNat + ω.v.1.natAbs + (-ω.v.2).natAbs)) =
      (-1) ^ (m * ω.period.toNat) * (-1) ^ (m * ω.v.1.natAbs) *
        (-1) ^ (m * (-ω.v.2).natAbs) := by
    rw [← pow_add, ← pow_add]; congr 1; ring
  rw [e2] at h1
  have hsq : ((-1 : ℤ) ^ (m * ω.v.1.natAbs)) * (-1) ^ (m * ω.v.1.natAbs) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; simp
  linear_combination ((-1 : ℤ) ^ (m * ω.v.1.natAbs)) * h1 -
    ((-1 : ℤ) ^ (m * ω.period.toNat) * (-1) ^ (m * (-ω.v.2).natAbs)) * hsq

theorem ribbonSumLeft_map (F : Diagram → Lambda) (X : Diagram) (m : ℕ) :
    ribbonSumLeft (fun Z => schurInvolution (F Z)) X m =
      schurInvolution (ribbonSumLeft F X m) := by
  unfold ribbonSumLeft
  rw [map_sum]
  refine Finset.sum_congr rfl fun Y _ => ?_
  rw [map_mul, map_intCast]

theorem ribbonSumRight_map (F : Diagram → Lambda) (X : Diagram) (m : ℕ) :
    ribbonSumRight (fun Z => schurInvolution (F Z)) X m =
      schurInvolution (ribbonSumRight F X m) := by
  unfold ribbonSumRight
  rw [map_sum]
  refine Finset.sum_congr rfl fun Y _ => ?_
  rw [map_mul, map_intCast]

/-- Applying the involution `ι` to an equation `p_n^⊥ (ι A) = c ι(P) ι(S)`. -/
theorem iota_transfer {n : ℕ} (hn : 0 < n) {A S P : Lambda} {c : ℤ} {m : ℕ}
    (h : pDeriv n (schurInvolution A) =
      (c : Lambda) * schurInvolution P ^ m * schurInvolution S) :
    pDeriv n A = (((-1 : ℤ) ^ (n - 1) * c : ℤ) : Lambda) * P ^ m * S := by
  rw [pDeriv_schurInvolution hn] at h
  have h2 : schurInvolution ((-1) ^ (n - 1) * pDeriv n A) =
      schurInvolution ((c : Lambda) * P ^ m * S) := by
    rw [map_mul, map_pow, map_neg, map_one, h]
    simp only [map_mul, map_pow, map_intCast]
  have h3 := schurInvolution_involutive.injective h2
  have hsq : ((-1 : Lambda) ^ (n - 1)) * (-1) ^ (n - 1) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; simp
  push_cast
  linear_combination ((-1 : Lambda) ^ (n - 1)) * h3 - (pDeriv n A) * hsq

/-- **The edge equations for a legal mark of case (b)** from those of its antitransposed mark, a
legal mark of case (a). -/
theorem edgeCompat_of_anti {ω : MarkedInner} (hω : ω.IsLegal) (hc : ω.case = .b)
    (h : EdgeCompat ω.anti) : EdgeCompat ω := by
  have hW := W_nonempty_of_case_b hω hc
  have hord : ¬ ω.case.IsMixed := by simp [AttachCase.IsMixed, hc]
  have hq : 0 < ω.period := hω.period_pos
  intro X hX m hm
  obtain ⟨hL, hR⟩ := h X hX m hm
  have hn : 0 < m * ω.period.toNat := Nat.mul_pos hm (by omega)
  have hmod : modComp ω.anti = fun Z => schurInvolution (modComp ω Z) :=
    funext fun Z => modComp_anti hω.1 hω.2.2.1 hW hord Z
  have hhf := hatFactor_anti hω.1 hω.2.2.1 hW
  have hsg := edgeSign_anti hc hq hm
  constructor
  · rw [period_anti, hmod, hhf, ribbonSumLeft_map] at hL
    have := iota_transfer hn (A := modComp ω X) (S := ribbonSumLeft (modComp ω) X m) hL
    rw [this, hsg]
  · rw [period_anti, hmod, hhf, ribbonSumRight_map] at hR
    have := iota_transfer hn (A := modComp ω X) (S := ribbonSumRight (modComp ω) X m) hR
    rw [this, hsg]

end MarkedInner

end SkewMarkedFactor.Gluing
