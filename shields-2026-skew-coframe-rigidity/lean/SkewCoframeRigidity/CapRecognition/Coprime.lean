/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.CapRecognition.Cap

/-!
# A common prime factor of the corner coefficient and the remainder is trivial

Write `num c = rest c ± h_{X_1} aux c`.  If a prime `F` divides both `aux c` and `rest c`, then
`F` divides a nonzero polynomial free of `z`.  The proof is an induction along the tail of the
cap: condensation turns the two divisibilities into `F ∣ num (tail c)` unless `F` already divides
`detA c`, and `aux c` is a nonzero multiple of `F` free of the tail's top label, so `F` itself is
free of it and the tail's own coefficient and remainder are divisible by `F`.  Sorry-free.
-/

namespace SkewCoframeRigidity.CapRecognition

open SkewCofactorIndependence MvPolynomial

theorem neg_one_pow_notMem (i : Option ℕ+) (k : ℕ) : i ∉ ((-1 : J) ^ k).vars := by
  intro h
  have := vars_pow (-1 : J) k h
  simp at this

/-- Differentiating `r0 ± x d` in `x` returns `± d` when `r0` and `d` are free of `x`. -/
theorem pderiv_split {i : Option ℕ+} {r0 d : J} (k : ℕ) (h0 : i ∉ r0.vars) (hd : i ∉ d.vars) :
    pderiv i (r0 + (-1 : J) ^ k * X i * d) = (-1 : J) ^ k * d := by
  have hs := pderiv_eq_zero_of_notMem_vars (neg_one_pow_notMem i k)
  rw [map_add, pderiv_eq_zero_of_notMem_vars h0, pderiv_mul, pderiv_mul, hs,
    pderiv_eq_zero_of_notMem_vars hd, pderiv_X_self]
  simp

theorem ι_notMem_none (s : CompleteRing) : none ∉ (ι s).vars := by
  intro h
  obtain ⟨j, -, hj⟩ := mem_vars_rename _ _ h
  exact Option.some_ne_none _ hj

namespace WeakCap

theorem rest_zero (c : WeakCap (0 + 1)) : c.rest = hJ (c.X 0 - c.Y 0) := by
  unfold rest
  rw [Fin.sum_univ_one]
  have h0 : (0 : Fin (0 + 2)) = (0 : Fin (0 + 1)).castSucc := rfl
  rw [h0, Zb_castSucc]
  have hZ : Zb c.X c.cols 1 1 = 1 := by
    show Zb c.X c.cols (Fin.last 1) (Fin.last 1) = 1
    rw [Zb_last, cols_last]
    simp
  have h1 : ((Zb c.X c.cols).submatrix Fin.succ ((0 : Fin (0 + 1)).castSucc).succAbove).det = 1 := by
    rw [Matrix.det_unique]
    simpa using hZ
  have hc : c.cols 0 = c.Y 0 := c.cols_castSucc 0
  rw [h1]
  simp [hJ, hc]

/-- A prime dividing `aux` and `rest` divides a nonzero `z`-free polynomial. -/
theorem exists_zfree_of_dvd :
    ∀ (n : ℕ) (c : WeakCap (n + 1)) (F : J), Prime F → F ∣ c.aux → F ∣ c.rest →
      ∃ P : J, P ≠ 0 ∧ none ∉ P.vars ∧ F ∣ P := by
  intro n
  induction n with
  | zero =>
    intro c F _ _ hr
    refine ⟨c.rest, ?_, ?_, hr⟩
    · rw [rest_zero]
      exact (ι_injective.ne_iff' (map_zero ι)).mpr ((complete_ne_zero_iff _).mpr (by
        have := c.Y_le 0; omega))
    · rw [rest_zero]; exact ι_notMem_none _
  | succ n ih =>
    intro c F hF ha hr
    have hnum : F ∣ c.num := by
      rw [c.num_split]
      exact dvd_add hr (dvd_mul_of_dvd_right ha _)
    have hdj := c.num_dj
    have hprod : F ∣ c.tail.num * ι c.detA := by
      have h1 : F ∣ c.num * ι c.tail.detA := dvd_mul_of_dvd_left hnum _
      have h2 : F ∣ c.aux * ι (c.minor 0) := dvd_mul_of_dvd_left ha _
      have : c.tail.num * ι c.detA = c.num * ι c.tail.detA + c.aux * ι (c.minor 0) := by
        rw [hdj]; ring
      rw [this]
      exact dvd_add h1 h2
    rcases hF.dvd_or_dvd hprod with ht | hd
    · -- descend to the tail
      have hpos : 0 < c.tail.X 0 := c.tail.X_pos 0
      have hfree : NoLabel c.aux (c.tail.X 0) := by
        refine Zb_det_noLabel _ _ fun i' p => ?_
        have hp := c.Y_pos p
        show c.X i'.succ - c.Y p ≠ c.X (0 : Fin (n + 1)).succ
        rcases Fin.eq_zero_or_eq_succ i' with h | ⟨j, rfl⟩
        · subst h; omega
        · have : c.X j.succ.succ < c.X (0 : Fin (n + 1)).succ :=
            c.X_anti (Fin.succ_lt_succ_iff.mpr (Fin.succ_pos j))
          omega
      have hFfree : lvar _ hpos ∉ F.vars :=
        notMem_vars_of_dvd c.aux_ne_zero ha (hfree.notMem hpos)
      -- differentiate `tail.num = tail.rest ± x tail.aux` in `x = h_{tail.X 0}`
      have hsplit := c.tail.num_split
      rw [hJ_eq_X hpos] at hsplit
      have hr0 := c.tail.rest_noLabel.notMem hpos
      have hd0 := c.tail.aux_noLabel_X0.notMem hpos
      obtain ⟨K, hK⟩ := ht
      have hder : pderiv (lvar _ hpos) c.tail.num = (-1 : J) ^ (n + 1) * c.tail.aux := by
        rw [hsplit]; exact pderiv_split _ hr0 hd0
      have hFd : F ∣ c.tail.aux := by
        have : F ∣ (-1 : J) ^ (n + 1) * c.tail.aux := by
          rw [← hder, hK, pderiv_mul_of_notMem_left hFfree]
          exact dvd_mul_right _ _
        exact ((isUnit_one.neg).pow (n + 1)).dvd_mul_left.mp this
      have hFr : F ∣ c.tail.rest := by
        have : c.tail.rest = c.tail.num - (-1 : J) ^ (n + 1) * MvPolynomial.X (lvar _ hpos) * c.tail.aux := by
          rw [hsplit]; ring
        rw [this]
        exact dvd_sub ⟨K, hK⟩ (dvd_mul_of_dvd_right hFd _)
      exact ih c.tail F hF hFd hFr
    · exact ⟨ι c.detA, (map_ne_zero_iff _ ι_injective).mpr c.detA_ne_zero, ι_notMem_none _, hd⟩

end WeakCap

end SkewCoframeRigidity.CapRecognition
