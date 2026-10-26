/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
-- TODO-COPIED:
-- skew-gluing/lean/SkewGluing/OlsonHarris/Plan/MurnaghanNakayama/RowMoveDet.lean
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.MurnaghanNakayama.Raise
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.MurnaghanNakayama.Beta

/-!
# The Jacobi–Trudi determinant after a row move

Formalizes `shields-2026-skew-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `def:gluing-graph`): thesis §5.1.3 (`OlsonHarris2024HopfApplications`).

* `jtDet_eq_zero_of_lt`: a Jacobi–Trudi determinant `det (h_{a_i - e_j})` with `a`, `e`
  decreasing vanishes when some `e_k` exceeds `a_k`.
* `jtDet_update_eq`, `jtDet_rows_update_eq`: raising the entry `μ_j - j` by `m` gives
  `(-1)^{j - i₁}` times the determinant for the β-numbers `ν_i - i` of the diagram `ν` of a
  `RowMove`, in the column index and in the row index.

Sorry-free.
-/

namespace SkewMarkedFactor.Gluing

namespace Plan

namespace MN

open MvPolynomial

/-- A determinant `det (h_{a_i - e_j})` with `a`, `e` weakly decreasing vanishes when `a_k < e_k`
for some `k`: the rows `i ≥ k` and columns `j ≤ k` form a zero block too large for a
permutation. -/
theorem jtDet_eq_zero_of_lt {M : ℕ} (a e : Fin M → ℤ) (ha : Antitone a) (he : Antitone e)
    (k : Fin M) (hk : a k < e k) : jtDet a e = 0 := by
  unfold jtDet
  rw [Matrix.det_apply]
  refine Finset.sum_eq_zero fun σ _ => ?_
  have hex : ∃ j, j ≤ k ∧ k ≤ σ j := by
    by_contra hcon
    push Not at hcon
    have hmaps : ∀ j ∈ Finset.Iic k, σ j ∈ Finset.Iio k := by
      intro j hj
      exact Finset.mem_Iio.mpr (hcon j (Finset.mem_Iic.mp hj))
    have hcard := Finset.card_le_card_of_injOn σ hmaps (σ.injective.injOn)
    simp only [Fin.card_Iic, Fin.card_Iio] at hcard
    omega
  obtain ⟨j, hj1, hj2⟩ := hex
  have hz : hh (a (σ j) - e j) = 0 := by
    apply hh_of_neg
    have h1 := ha hj2
    have h2 := he hj1
    omega
  simp only [Matrix.of_apply]
  rw [Finset.prod_eq_zero (Finset.mem_univ j) hz, smul_zero]

/-- Raising the entry `μ_j - j` by `m` is the sorted `ν_i - i` after the cycle `(i₁ … j)`. -/
theorem update_eq_comp_cycleIcc {mu nu : YoungDiagram} {M j i1 m : ℕ} (hj : j < M)
    (h : RowMove mu nu j i1 m) :
    haveI : NeZero M := ⟨by omega⟩
    Function.update (fun i : Fin M => (mu.rowLen i : ℤ) - i) ⟨j, hj⟩
        ((mu.rowLen j : ℤ) - j + m) =
      (fun i : Fin M => (nu.rowLen i : ℤ) - i) ∘
        Fin.cycleIcc ⟨i1, by have := h.i1_le; omega⟩ ⟨j, hj⟩ := by
  have : NeZero M := ⟨by omega⟩
  have hi1 : i1 < M := by have := h.i1_le; omega
  set τ : Equiv.Perm (Fin M) := Fin.cycleIcc ⟨i1, hi1⟩ ⟨j, hj⟩ with hτ
  have hle : (⟨i1, hi1⟩ : Fin M) ≤ ⟨j, hj⟩ := Fin.mk_le_mk.mpr h.i1_le
  funext k
  simp only [Function.comp_apply]
  have htop := h.top
  have hjn : ((j - i1 : ℕ) : ℤ) = (j : ℤ) - i1 := by have := h.i1_le; omega
  rw [hjn] at htop
  rcases lt_trichotomy k.val j with hkj | hkj | hkj
  · have hkne : k ≠ ⟨j, hj⟩ := fun e => by rw [e] at hkj; simp at hkj
    rw [Function.update_of_ne hkne]
    by_cases hk1 : k.val < i1
    · have : τ k = k := Fin.cycleIcc_of_lt (by exact hk1)
      rw [this, h.outside k (Or.inl hk1)]
    · have hkk : (⟨i1, hi1⟩ : Fin M) ≤ k := Fin.mk_le_mk.mpr (by omega)
      have : τ k = k + 1 := Fin.cycleIcc_of_ge_of_lt hkk (Fin.mk_lt_mk.mpr hkj)
      have hv : ((k + 1 : Fin M) : ℕ) = k.val + 1 := by
        rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (show 1 < M by omega),
          Nat.mod_eq_of_lt (show k.val + 1 < M by omega)]
      rw [this, hv]
      have := h.inner (k.val + 1) (by omega) (by omega)
      simp only [Nat.add_sub_cancel] at this
      push_cast
      omega
  · have hk : k = ⟨j, hj⟩ := Fin.ext hkj
    subst hk
    have : τ ⟨j, hj⟩ = ⟨i1, hi1⟩ := Fin.cycleIcc_of_last hle
    rw [this, Function.update_self]
    simp only
    omega
  · have hkne : k ≠ ⟨j, hj⟩ := fun e => by rw [e] at hkj; simp at hkj
    rw [Function.update_of_ne hkne]
    have : τ k = k := Fin.cycleIcc_of_gt (Fin.mk_lt_mk.mpr hkj)
    rw [this, h.outside k (Or.inr hkj)]

/-- **The determinant after a row move** (columns). -/
theorem jtDet_update_eq {mu nu : YoungDiagram} {M j i1 m : ℕ} (hj : j < M)
    (h : RowMove mu nu j i1 m) (a : Fin M → ℤ) :
    jtDet a (Function.update (fun i : Fin M => (mu.rowLen i : ℤ) - i) ⟨j, hj⟩
        ((mu.rowLen j : ℤ) - j + m)) =
      (-1) ^ (j - i1) * jtDet a (fun i : Fin M => (nu.rowLen i : ℤ) - i) := by
  have : NeZero M := ⟨by omega⟩
  have hi1 : i1 < M := by have := h.i1_le; omega
  have hle : (⟨i1, hi1⟩ : Fin M) ≤ ⟨j, hj⟩ := Fin.mk_le_mk.mpr h.i1_le
  rw [update_eq_comp_cycleIcc hj h, jtDet_perm, Fin.sign_cycleIcc_of_le hle]
  simp

/-- **The determinant after a row move** (rows). -/
theorem jtDet_rows_update_eq {mu nu : YoungDiagram} {M j i1 m : ℕ} (hj : j < M)
    (h : RowMove mu nu j i1 m) (b : Fin M → ℤ) :
    jtDet (Function.update (fun i : Fin M => (mu.rowLen i : ℤ) - i) ⟨j, hj⟩
        ((mu.rowLen j : ℤ) - j + m)) b =
      (-1) ^ (j - i1) * jtDet (fun i : Fin M => (nu.rowLen i : ℤ) - i) b := by
  have : NeZero M := ⟨by omega⟩
  have hi1 : i1 < M := by have := h.i1_le; omega
  have hle : (⟨i1, hi1⟩ : Fin M) ≤ ⟨j, hj⟩ := Fin.mk_le_mk.mpr h.i1_le
  rw [update_eq_comp_cycleIcc hj h, jtDet_rows_perm, Fin.sign_cycleIcc_of_le hle]
  simp

end MN

end Plan

end SkewMarkedFactor.Gluing
