/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.CapRecognition.Coprime
import SkewCoframeRigidity.CapRecognition.Board

/-!
# Irreducibility of the cap numerator

A common factor of all the minors of a nonempty weak cap is a unit: it would divide the
connected board determinant, which is irreducible and carries the fresh top label linearly.
Together with the tail induction of `Coprime`, this makes the corner coefficient and remainder of
the numerator coprime, and the numerator is linear in the corner label, hence irreducible.
Sorry-free.
-/

namespace SkewCoframeRigidity.CapRecognition

open SkewCofactorIndependence MvPolynomial

namespace WeakCap

variable {m : ℕ} (c : WeakCap (m + 1))

theorem topLabel_pos : 0 < c.topLabel := by
  have := c.Y_pos 0
  have := c.Y_le 0
  unfold topLabel; omega

theorem minor_notMem_top (p : Fin (m + 2)) :
    pn c.topLabel c.topLabel_pos ∉ (c.minor p).vars := by
  refine not_mem_vars_det _ _ fun i j h => ?_
  have h1 := (mem_vars_complete_iff _ _).mp h
  rw [pn_coe] at h1
  have h2 : c.X i ≤ c.X 0 := c.X_anti.antitone (Fin.zero_le i)
  have := c.cols_nonneg (p.succAbove j)
  have : c.X 0 < c.topLabel := by
    have := c.Y_pos 0
    unfold topLabel; omega
  simp only [Function.comp] at h1
  omega

/-- A nonunit cannot divide every minor of a nonempty weak cap. -/
theorem not_dvd_minors (f : CompleteRing) (hf : ¬ IsUnit f) (h : ∀ p, f ∣ c.minor p) : False := by
  set T := c.topLabel with hT
  have hTpos : 0 < T := c.topLabel_pos
  set v : ℕ+ := pn T hTpos with hv
  have hdiv : f ∣ c.board.schur := by
    rw [board_schur]
    exact Finset.dvd_sum fun p _ => dvd_mul_of_dvd_right (h p) _
  obtain ⟨k, hk⟩ := hdiv
  have hirr := c.board.schur_irreducible c.board_connected
  have hkunit : IsUnit k := (hirr.isUnit_or_isUnit hk).resolve_left hf
  obtain ⟨q, -, hq⟩ := isUnit_iff_eq_C_of_isReduced.mp hkunit
  -- `f` is free of the top variable
  have hfree : v ∉ f.vars :=
    notMem_vars_of_dvd (c.minor_ne_zero (Fin.last (m + 1))) (h _) (c.minor_notMem_top _)
  have hd1 : pderiv v c.board.schur = 0 := by
    rw [hk, hq, pderiv_mul, pderiv_eq_zero_of_notMem_vars hfree, pderiv_C]
    simp
  rw [board_schur, map_sum, Finset.sum_eq_single (Fin.last (m + 1))] at hd1
  · have hl : complete (T - c.cols (Fin.last (m + 1))) = MvPolynomial.X v := by
      rw [cols_last, sub_zero, complete_of_pos hTpos]
      rfl
    rw [hl, pderiv_mul, pderiv_mul, pderiv_X_self,
      pderiv_eq_zero_of_notMem_vars (c.minor_notMem_top _)] at hd1
    have hs : pderiv v ((-1 : CompleteRing) ^ ((Fin.last (m + 1) : Fin (m + 2)) : ℕ)) = 0 := by
      rw [← C_1, ← C_neg, ← C_pow]; exact pderiv_C
    rw [hs] at hd1
    simp only [zero_add, zero_mul, mul_zero, mul_one, Fin.val_last, add_zero] at hd1
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      (c.minor_ne_zero (Fin.last (m + 1))) hd1
  · intro p _ hp
    apply pderiv_eq_zero_of_notMem_vars
    intro hm
    rcases Finset.mem_union.mp (vars_mul _ _ hm) with hm | hm
    · rcases Finset.mem_union.mp (vars_mul _ _ hm) with hm | hm
      · have := vars_pow (-1 : CompleteRing) (p : ℕ) hm
        simp at this
      · have h1 := (mem_vars_complete_iff _ _).mp hm
        rw [hv, pn_coe] at h1
        have h2 : c.cols p ≠ 0 := by
          intro h0
          exact hp (c.cols_anti.injective (by rw [h0, cols_last]))
        omega
    · exact c.minor_notMem_top p hm
  · simp

theorem dvd_minors_of_dvd_num {F : J} {f : CompleteRing} (hF : F = ι f) (h : F ∣ c.num)
    (p : Fin (m + 2)) : f ∣ c.minor p := by
  obtain ⟨K, hK⟩ := h
  have h1 : Polynomial.C f ∣ φ c.num := by
    rw [hK, map_mul, hF, φ_ι]
    exact dvd_mul_right _ _
  have h2 := (Polynomial.C_dvd_iff_dvd_coeff _ _).mp h1 (c.cols p).toNat
  have h3 : f ∣ (-1 : CompleteRing) ^ (m + 1 + (p : ℕ)) * c.minor p := by
    have := c.coefZ_num p
    simp only [coefZ] at this
    rw [← this]
    exact h2
  exact ((isUnit_one.neg).pow _).dvd_mul_left.mp h3

/-- The numerator of a nonempty weak cap is irreducible in the joint polynomial ring. -/
theorem num_irreducible : Irreducible c.num := by
  have hpos : 0 < c.X 0 := c.X_pos 0
  have hsplit : c.num = c.rest +
      MvPolynomial.X (lvar (c.X 0) hpos) * ((-1 : J) ^ (m + 1) * c.aux) := by
    rw [c.num_split, hJ_eq_X hpos]; ring
  have hunit : IsUnit ((-1 : J) ^ (m + 1)) := (isUnit_one.neg).pow _
  rw [hsplit]
  refine irreducible_linear (c.rest_noLabel.notMem hpos) ?_
    (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) c.aux_ne_zero) ?_
  · intro h
    rcases Finset.mem_union.mp (vars_mul _ _ h) with h | h
    · exact neg_one_pow_notMem _ _ h
    · exact c.aux_noLabel_X0.notMem hpos h
  · intro g hgd hgr
    by_contra hg
    have hg0 : g ≠ 0 := by
      rintro rfl
      exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) c.aux_ne_zero
        (zero_dvd_iff.mp hgd)
    obtain ⟨F, hFirr, hFg⟩ := WfDvdMonoid.exists_irreducible_factor hg hg0
    have hFd : F ∣ c.aux := hunit.dvd_mul_left.mp (hFg.trans hgd)
    have hFr : F ∣ c.rest := hFg.trans hgr
    have hFp : Prime F := UniqueFactorizationMonoid.irreducible_iff_prime.mp hFirr
    by_cases hz : none ∈ F.vars
    · obtain ⟨P, hP0, hPz, hFP⟩ := exists_zfree_of_dvd m c F hFp hFd hFr
      exact notMem_vars_of_dvd hP0 hFP hPz hz
    · have hsub : (↑F.vars : Set (Option ℕ+)) ⊆ Set.range some := by
        intro x hx
        rcases x with _ | y
        · exact absurd hx hz
        · exact ⟨y, rfl⟩
      obtain ⟨f, hf⟩ := exists_rename_eq_of_vars_subset_range F some (Option.some_injective _) hsub
      have hF : F = ι f := hf.symm
      have hfn : ¬ IsUnit f := fun hu => hFirr.not_isUnit (hF ▸ hu.map ι)
      have hFn : F ∣ c.num := by
        rw [c.num_split]
        exact dvd_add hFr (dvd_mul_of_dvd_right hFd _)
      exact c.not_dvd_minors f hfn (c.dvd_minors_of_dvd_num hF hFn)

end WeakCap

end SkewCoframeRigidity.CapRecognition
