/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.NormalOpenPrefixCharges
import SkewCornerDescent.Matrix.NormalFirstPrefixCharge
import SkewCornerDescent.FinitePeriodicWindowSums
import SkewCornerDescent.FinitePeriodicWindowProducts

/-!
# Complete normal-prefix charge factorization

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The finite residue period produces every inverse window product. Full normal
word periods supply the onsite and pair multiplicities; both exterior pair
occurrences remain, even at full-period and repeated-wrap boundaries.
The surviving term uses the complete first-normal prefix charge. Sorry-free.
-/

namespace SkewCornerDescent.Matrix
open scoped BigOperators

/-- The full long-interval prefix, with every original residue inverse weight. -/
noncomputable def normalLongPrefixCharge {N : ℕ} {F : Type*} [Field F]
    (M : Matrix (Fin N) (Fin N) (PowerSeries F))
    (δ : PowerSeries F → PowerSeries F) (l T : ℕ) (hT : T ≤ N - (l + 1)) : F :=
  ∑ s : Fin T, PowerSeries.constantCoeff (δ
    (M ⟨s.val, by have := s.isLt; omega⟩
      ⟨s.val + l + 1, by have := s.isLt; omega⟩)) *
    ∏ j : Fin (l + 2), (PowerSeries.constantCoeff
      (M ⟨s.val + j.val, by have := s.isLt; have := j.isLt; omega⟩
        ⟨s.val + j.val, by have := s.isLt; have := j.isLt; omega⟩))⁻¹

/-- Complete onsite first jets at the genuine prefix positions. -/
noncomputable def normalOnsitePrefixCharge {N : ℕ} {F : Type*} [Field F]
    (M : Matrix (Fin N) (Fin N) (PowerSeries F)) (T : ℕ) (hT : T ≤ N) : F :=
  ∑ s : Fin T, PowerSeries.coeff 1
    (M ⟨s.val, s.isLt.trans_le hT⟩ ⟨s.val, s.isLt.trans_le hT⟩) *
    (PowerSeries.constantCoeff
      (M ⟨s.val, s.isLt.trans_le hT⟩ ⟨s.val, s.isLt.trans_le hT⟩))⁻¹

/-- Complete onsite and both exterior pair charges have their exact cyclic
multiplicities. The uniform residue product is supplied here by the actual
finite residue period, not assumed as a coefficient or a frozen inverse. -/
theorem normalOpenPrefixCharge_factor {N T r : ℕ} {F : Type*} [Field F]
    [NeZero T] [NeZero r]
    (M : Matrix (Fin N) (Fin N) (PowerSeries F))
    (δ : PowerSeries F → PowerSeries F) (b γ : F) (l k : ℕ)
    (hk : 0 < k) (hlen : l + 1 = k * r) (hT : T ≤ N - (l + 1))
    (hdiag : ∀ i j : Fin N, j.val = i.val + T → M i i = M j j)
    (hpair : ∀ i j : Fin (N - 1), j.val = i.val + T →
      M ⟨i.val, by have := i.isLt; omega⟩ ⟨i.val + 1, by have := i.isLt; omega⟩ =
      M ⟨j.val, by have := j.isLt; omega⟩ ⟨j.val + 1, by have := j.isLt; omega⟩)
    (hres : ∀ i j : Fin N, j.val = i.val + r →
      PowerSeries.constantCoeff (M i i) = PowerSeries.constantCoeff (M j j)) :
    let hrN : r ≤ N := by
      have ht := NeZero.pos T
      have hnr : l + 1 ≤ N := by omega
      nlinarith
    let Z := (∏ i : Fin r, (PowerSeries.constantCoeff
      (M ⟨i.val, i.isLt.trans_le hrN⟩ ⟨i.val, i.isLt.trans_le hrN⟩))⁻¹)^k
    let long := ∑ s : Fin T,
      PowerSeries.constantCoeff (δ
        (M ⟨s.val, by have := s.isLt; omega⟩
          ⟨s.val + l + 1, by have := s.isLt; omega⟩)) *
      ∏ j : Fin (l + 2), (PowerSeries.constantCoeff
        (M ⟨s.val + j.val, by have := s.isLt; have := j.isLt; omega⟩
          ⟨s.val + j.val, by have := s.isLt; have := j.isLt; omega⟩))⁻¹
    let V := ∑ s : Fin T, PowerSeries.coeff 1
      (M ⟨s.val, by have := s.isLt; omega⟩ ⟨s.val, by have := s.isLt; omega⟩) *
      (PowerSeries.constantCoeff
        (M ⟨s.val, by have := s.isLt; omega⟩ ⟨s.val, by have := s.isLt; omega⟩))⁻¹
    normalOpenOverlapPrefixCharge M δ b γ l T hT =
      (-1 : F)^l * b^l * (-b * long + γ * Z * V -
        γ * ((l + 2 : ℕ) : F) * Z *
          normalFirstPrefixCharge M b T (by omega)) := by
  have hTpos := NeZero.pos T
  have hrpos := NeZero.pos r
  have hrN : r ≤ N := by
    have hnr : l + 1 ≤ N := by omega
    nlinarith
  let w := fun i : Fin N => (PowerSeries.constantCoeff (M i i))⁻¹
  let ν := fun i : Fin N => PowerSeries.coeff 1 (M i i) * w i
  let q := fun i : Fin (N - 1) =>
    PowerSeries.constantCoeff
      (M ⟨i.val, by have := i.isLt; omega⟩ ⟨i.val + 1, by have := i.isLt; omega⟩) *
      w ⟨i.val, by have := i.isLt; omega⟩ * w ⟨i.val + 1, by have := i.isLt; omega⟩
  let Z := (∏ i : Fin r, w ⟨i.val, i.isLt.trans_le hrN⟩)^k
  have hpw : ∀ i j : Fin N, j.val = i.val + r → w i = w j := by
    intro i j hij
    exact congrArg Inv.inv (hres i j hij)
  have hpν : ∀ i j : Fin N, j.val = i.val + T → ν i = ν j := by
    intro i j hij
    simp only [ν, w, hdiag i j hij]
  have hpq : ∀ i j : Fin (N - 1), j.val = i.val + T → q i = q j := by
    intro i j hij
    have hi := hdiag ⟨i.val, by have := i.isLt; omega⟩
      ⟨j.val, by have := j.isLt; omega⟩ hij
    have hj := hdiag ⟨i.val + 1, by have := i.isLt; omega⟩
      ⟨j.val + 1, by have := j.isLt; omega⟩ (by simp only; omega)
    simp only [q, w, hpair i j hij, hi, hj]
  have hprod (s : ℕ) (hs : s + (l + 1) ≤ N) :
      (∏ i : Fin (l + 1), w ⟨s + i.val, by have := i.isLt; omega⟩) = Z := by
    have hs' : s + k * r ≤ N := by omega
    have he := finite_periodic_window_product w hrN hpw k s hs'
    have heq : (∏ i : Fin (l + 1), w ⟨s + i.val, by have := i.isLt; omega⟩) =
        ∏ i : Fin (k * r), w ⟨s + i.val, by have := i.isLt; omega⟩ := by
      apply Fintype.prod_equiv (finCongr hlen)
      intro i
      rfl
    exact heq.trans he
  have hν := finite_periodic_window_sum (fun i : Fin N => M i i)
    (fun p => PowerSeries.coeff 1 p * (PowerSeries.constantCoeff p)⁻¹)
    (show T ≤ N by omega) hdiag (l + 1) (by omega)
  have hq := finite_periodic_window_sum q id (show T ≤ N - 1 by omega)
    hpq l (by omega)
  have hright := finite_periodic_shift_sum q id (show T ≤ N - 1 by omega)
    hpq l (by omega)
  have hprod0 (s : Fin T) :
      (∏ i : Fin (l + 1), w ⟨s.val + i.val, by have := s.isLt; have := i.isLt; omega⟩) = Z :=
    hprod s.val (by have := s.isLt; omega)
  have hprod1 (s : Fin T) :
      (∏ i : Fin (l + 1), w ⟨s.val + i.val + 1, by have := s.isLt; have := i.isLt; omega⟩) = Z := by
    simpa only [Nat.add_assoc, Nat.add_comm 1] using
      hprod (s.val + 1) (by have := s.isLt; omega)
  have hfirst : normalFirstPrefixCharge M b T (by omega) =
      (∑ s : Fin T, ν ⟨s.val, by have := s.isLt; omega⟩) -
        b * ∑ s : Fin T, q ⟨s.val, by have := s.isLt; omega⟩ := by
    dsimp only [normalFirstPrefixCharge]
    congr 1
    congr 1
    apply Finset.sum_congr rfl
    intro s _
    simp only [Fin.isValue, Fin.reduceLast, Finset.prod_inv_distrib,
      Fin.prod_univ_two, mul_inv_rev]
    let i : Fin N := ⟨s.val, by have := s.isLt; omega⟩
    let j : Fin N := ⟨s.val + 1, by have := s.isLt; omega⟩
    change PowerSeries.constantCoeff (M i j) * (w j * w i) =
      PowerSeries.constantCoeff (M i j) * w i * w j
    ring
  rw [hfirst]
  dsimp only [normalOpenOverlapPrefixCharge]
  simp only [contiguousMatrixWindow, Matrix.submatrix_apply,
    Fin.val_zero, Fin.val_last, Fin.val_castSucc, Fin.val_succ, Fin.val_one, Nat.add_zero,
    ← Nat.add_assoc]
  let Lg := ∑ s : Fin T,
    PowerSeries.constantCoeff (δ (M ⟨s.val, by have := s.isLt; omega⟩
      ⟨s.val + l + 1, by have := s.isLt; omega⟩)) *
      ∏ j : Fin (l + 2), w ⟨s.val + j.val, by have := s.isLt; have := j.isLt; omega⟩
  change (-1 : F)^(l + 1) * b^(l + 1) * Lg -
    (-1 : F)^l * b^l * γ *
      (∑ s : Fin T,
        (∏ j : Fin (l + 1), w ⟨s.val + j.val, by have := s.isLt; have := j.isLt; omega⟩) *
          ∑ j : Fin (l + 1), ν ⟨s.val + j.val, by have := s.isLt; have := j.isLt; omega⟩) -
    (-1 : F)^(l + 1) * b^(l + 1) * γ *
      ((∑ s : Fin T,
        (∏ j : Fin (l + 1), w ⟨s.val + j.val, by have := s.isLt; have := j.isLt; omega⟩) *
          ∑ j : Fin l, q ⟨s.val + j.val, by have := s.isLt; have := j.isLt; omega⟩) +
       (∑ s : Fin T,
        (∏ j : Fin (l + 1), w ⟨s.val + j.val + 1, by have := s.isLt; have := j.isLt; omega⟩) *
          q ⟨s.val, by have := s.isLt; omega⟩) +
       (∑ s : Fin T,
        (∏ j : Fin (l + 1), w ⟨s.val + j.val, by have := s.isLt; have := j.isLt; omega⟩) *
          q ⟨s.val + l, by have := s.isLt; omega⟩)) =
    (-1 : F)^l * b^l *
      (-b * Lg + γ * Z * (∑ s : Fin T, ν ⟨s.val, by have := s.isLt; omega⟩) -
        γ * ((l + 2 : ℕ) : F) * Z *
          ((∑ s : Fin T, ν ⟨s.val, by have := s.isLt; omega⟩) -
            b * ∑ s : Fin T, q ⟨s.val, by have := s.isLt; omega⟩))
  simp_rw [hprod0, hprod1]
  simp only [← Finset.mul_sum]
  dsimp only [id] at hq hright
  rw [hν, hq, hright]
  simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  ring

end SkewCornerDescent.Matrix
