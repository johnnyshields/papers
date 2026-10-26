/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.CapRecognition.Matrices
import SkewCoframeRigidity.CapRecognition.Algebra

/-!
# The numerator, its first-row split and the condensation identity

For a weak cap `c`, `num c` is the bordered determinant, `aux c` the same board with the first row
deleted, and `detA c` the determinant of the board itself.  The top label `h_{X_1}` occurs in
`num c` only in the corner entry, so `num c` is linear in it with coefficient `± aux c`
(`num_split`).  Desnanot--Jacobi condensation of the bordered board relates `num c` to the
numerator of the tail cap (`num_dj`).  Sorry-free.
-/

namespace SkewCoframeRigidity.CapRecognition

open SkewCofactorIndependence MvPolynomial

theorem castSucc_le_succAbove' {n : ℕ} (p : Fin (n + 1)) (i : Fin n) :
    i.castSucc ≤ p.succAbove i := by
  unfold Fin.succAbove
  split_ifs
  · exact le_rfl
  · exact Fin.castSucc_lt_succ.le

theorem det_map_ι {n : ℕ} (M : Matrix (Fin n) (Fin n) CompleteRing) :
    (M.map ι).det = ι M.det := (RingHom.map_det ι M).symm

@[simp] theorem Zb_castSucc {n : ℕ} (Xr : Fin n → ℤ) (Yc : Fin (n + 1) → ℤ) (i : Fin n)
    (p : Fin (n + 1)) : Zb Xr Yc i.castSucc p = ι (complete (Xr i - Yc p)) := by
  simp [Zb, zMat]

@[simp] theorem Zb_last {n : ℕ} (Xr : Fin n → ℤ) (Yc : Fin (n + 1) → ℤ) (p : Fin (n + 1)) :
    Zb Xr Yc (Fin.last n) p = zJ ^ (Yc p).toNat := by
  simp [Zb, zMat]

theorem Zb_submatrix_castSucc {n : ℕ} (Xr : Fin n → ℤ) (Yc : Fin (n + 1) → ℤ)
    (s : Fin n → Fin (n + 1)) :
    (Zb Xr Yc).submatrix Fin.castSucc s = (betaBoard Xr (Yc ∘ s)).map ι := by
  ext i j
  simp [betaBoard]

theorem Zb_entry_noLabel {n : ℕ} (Xr : Fin n → ℤ) (Yc : Fin (n + 1) → ℤ) {k : ℤ}
    (hk : ∀ i p, Xr i - Yc p ≠ k) (i p) : NoLabel (Zb Xr Yc i p) k := by
  induction i using Fin.lastCases with
  | last => rw [Zb_last]; exact noLabel_zpow _
  | cast i => rw [Zb_castSucc]; exact noLabel_hJ (hk i p)

theorem Zb_det_noLabel {n : ℕ} (Xr : Fin n → ℤ) (Yc : Fin (n + 1) → ℤ) {k : ℤ}
    (hk : ∀ i p, Xr i - Yc p ≠ k) : NoLabel (Zb Xr Yc).det k :=
  NoLabel.det (Zb_entry_noLabel Xr Yc hk)

namespace WeakCap

variable {r : ℕ} (c : WeakCap r)

/-- The determinant of the board. -/
noncomputable def detA : CompleteRing := (betaBoard c.X c.Y).det

/-- The cap numerator: the bordered board. -/
noncomputable def num : J := (Zb c.X c.cols).det

/-- The board of the cap with column `p` of the bordered board deleted. -/
noncomputable def minor (p : Fin (r + 1)) : CompleteRing :=
  (betaBoard c.X (c.cols ∘ p.succAbove)).det

theorem minor_ne_zero (p : Fin (r + 1)) : c.minor p ≠ 0 := by
  refine betaBoard_det_ne_zero c.X _ c.X_anti
    (c.cols_anti.comp_strictMono (Fin.strictMono_succAbove p)) fun k => ?_
  have h1 := c.cols_anti.antitone (castSucc_le_succAbove' p k)
  have h2 : c.cols k.castSucc ≤ c.X k := by simpa using c.Y_le k
  exact h1.trans h2

theorem minor_last : c.minor (Fin.last r) = c.detA := by
  unfold minor detA
  congr 2
  funext i
  simp

theorem detA_ne_zero : c.detA ≠ 0 := by
  rw [← minor_last]; exact c.minor_ne_zero _

theorem cols_toNat_injective : Function.Injective fun p => (c.cols p).toNat := by
  intro p q h
  have := c.cols_nonneg p
  have := c.cols_nonneg q
  exact c.cols_anti.injective (by simp only at h; omega)

theorem num_eq_sum : c.num = ∑ p : Fin (r + 1),
    zJ ^ (c.cols p).toNat * ι ((-1 : CompleteRing) ^ (r + (p : ℕ)) * c.minor p) := by
  unfold num
  rw [Zb_det]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [map_mul, map_pow, map_neg, map_one, minor]
  ring

theorem coefZ_num (p : Fin (r + 1)) :
    coefZ (c.cols p).toNat c.num = (-1 : CompleteRing) ^ (r + (p : ℕ)) * c.minor p := by
  rw [num_eq_sum]
  exact coefZ_zsum _ c.cols_toNat_injective _ p

theorem coefZ_num_zero : coefZ 0 c.num = c.detA := by
  have := c.coefZ_num (Fin.last r)
  simp only [cols_last, Int.toNat_zero, Fin.val_last, minor_last] at this
  rw [this, ← two_mul, pow_mul]
  simp

theorem coefZ_num_Y (j : Fin r) :
    coefZ (c.Y j).toNat c.num = (-1 : CompleteRing) ^ (r + (j : ℕ)) * c.minor j.castSucc := by
  have := c.coefZ_num j.castSucc
  simpa using this

end WeakCap

namespace WeakCap

variable {m : ℕ} (c : WeakCap (m + 1))

/-- The bordered board with its first row deleted. -/
noncomputable def aux : J := (Zb (n := m) (fun i => c.X i.succ) c.Y).det

theorem Y_toNat_injective : Function.Injective fun p => (c.Y p).toNat := by
  intro p q h
  have := c.Y_pos p
  have := c.Y_pos q
  exact c.Y_anti.injective (by simp only at h; omega)

theorem aux_eq_sum : c.aux = ∑ p : Fin (m + 1), zJ ^ (c.Y p).toNat *
    ι ((-1 : CompleteRing) ^ (m + (p : ℕ)) *
      (betaBoard (fun i : Fin m => c.X i.succ) (c.Y ∘ p.succAbove)).det) := by
  unfold aux
  rw [Zb_det]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [map_mul, map_pow, map_neg, map_one]
  ring

theorem coefZ_aux : coefZ (c.Y 0).toNat c.aux = (-1 : CompleteRing) ^ m * c.tail.detA := by
  rw [aux_eq_sum, coefZ_zsum _ c.Y_toNat_injective _ 0]
  simp [detA, tail]
  rfl

theorem aux_ne_zero : c.aux ≠ 0 := by
  intro h
  have := c.coefZ_aux
  rw [h] at this
  simp only [coefZ, map_zero, Polynomial.coeff_zero] at this
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) c.tail.detA_ne_zero this.symm

/-- The corner-deleted part of the first-row expansion of `num`. -/
noncomputable def rest : J := ∑ p : Fin (m + 1), (-1 : J) ^ (p : ℕ) *
  Zb c.X c.cols 0 p.castSucc *
    ((Zb c.X c.cols).submatrix Fin.succ (p.castSucc).succAbove).det

theorem Zb_submatrix_succ_castSucc :
    (Zb c.X c.cols).submatrix Fin.succ Fin.castSucc = Zb (n := m) (fun i => c.X i.succ) c.Y := by
  ext i q
  induction i using Fin.lastCases with
  | last => simp
  | cast i' =>
    simp only [Matrix.submatrix_apply]
    rw [Fin.succ_castSucc, Zb_castSucc, Zb_castSucc, cols_castSucc]

theorem Zb_submatrix_succ_succ :
    (Zb c.X c.cols).submatrix Fin.succ Fin.succ = Zb c.tail.X c.tail.cols := by
  ext i q
  induction i using Fin.lastCases with
  | last => simp [cols_succ, tail]
  | cast i' =>
    simp only [Matrix.submatrix_apply]
    rw [Fin.succ_castSucc, Zb_castSucc, Zb_castSucc, cols_succ]
    rfl

theorem num_split : c.num = c.rest + (-1 : J) ^ (m + 1) * hJ (c.X 0) * c.aux := by
  unfold num
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_castSucc]
  have hlast : (-1 : J) ^ ((Fin.last (m + 1) : Fin (m + 2)) : ℕ) *
      Zb c.X c.cols 0 (Fin.last (m + 1)) *
      ((Zb c.X c.cols).submatrix Fin.succ (Fin.last (m + 1)).succAbove).det =
      (-1 : J) ^ (m + 1) * hJ (c.X 0) * c.aux := by
    have h0 : (0 : Fin (m + 2)) = (0 : Fin (m + 1)).castSucc := rfl
    rw [Fin.succAbove_last, Zb_submatrix_succ_castSucc, h0, Zb_castSucc]
    simp [hJ, aux]
  rw [hlast]
  rfl

theorem Zb_succ_noLabel {k : ℤ} (hk : ∀ (i' : Fin m) q, c.X i'.succ - c.cols q ≠ k)
    (i : Fin (m + 1)) (q : Fin (m + 2)) : NoLabel (Zb c.X c.cols i.succ q) k := by
  induction i using Fin.lastCases with
  | last => rw [Fin.succ_last, Zb_last]; exact noLabel_zpow _
  | cast i' => rw [Fin.succ_castSucc, Zb_castSucc]; exact noLabel_hJ (hk i' q)

theorem rest_noLabel : NoLabel c.rest (c.X 0) := by
  unfold rest
  refine NoLabel.sum fun p _ => ?_
  refine NoLabel.mul (NoLabel.mul ?_ ?_) (NoLabel.det fun i q => ?_)
  · exact (NoLabel.one (k := c.X 0)).neg.pow (p : ℕ)
  · have h0 : (0 : Fin (m + 2)) = (0 : Fin (m + 1)).castSucc := rfl
    rw [h0, Zb_castSucc]
    refine noLabel_hJ ?_
    have := c.Y_pos p
    simp only [cols_castSucc]
    omega
  · refine c.Zb_succ_noLabel ?_ _ _
    intro i' q
    have h1 : c.X i'.succ < c.X 0 := c.X_anti (Fin.succ_pos i')
    have := c.cols_nonneg q
    omega

theorem aux_noLabel_X0 : NoLabel c.aux (c.X 0) := by
  refine Zb_det_noLabel _ _ fun i' p => ?_
  have h1 : c.X i'.succ < c.X 0 := c.X_anti (Fin.succ_pos i')
  have := c.Y_pos p
  omega

theorem num_dj : c.num * ι c.tail.detA =
    c.tail.num * ι c.detA - c.aux * ι (c.minor 0) := by
  have h := Shields.desnanot_jacobi (Zb c.X c.cols)
  have e1 : (Zb c.X c.cols).submatrix (fun i : Fin m => i.castSucc.succ)
      (fun j : Fin m => j.castSucc.succ) = (betaBoard c.tail.X c.tail.Y).map ι := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.submatrix_apply, Matrix.map_apply, betaBoard, Matrix.of_apply]
    rw [Fin.succ_castSucc, Fin.succ_castSucc, Zb_castSucc, cols_castSucc]
    rfl
  have e2 : (Zb c.X c.cols).submatrix Fin.castSucc Fin.castSucc =
      (betaBoard c.X c.Y).map ι := by
    rw [Zb_submatrix_castSucc]
    congr 2
    funext i
    simp
  have e3 : (Zb c.X c.cols).submatrix Fin.castSucc Fin.succ =
      (betaBoard c.X (c.cols ∘ (0 : Fin (m + 2)).succAbove)).map ι := by
    rw [← Zb_submatrix_castSucc]
    rfl
  rw [e1, e2, e3, Zb_submatrix_succ_succ, Zb_submatrix_succ_castSucc, det_map_ι, det_map_ι,
    det_map_ι] at h
  exact h

end WeakCap

end SkewCoframeRigidity.CapRecognition
