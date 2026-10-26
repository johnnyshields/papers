/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.LowNegativeRigidity
import SkewJacobiNegative.EndpointDifferences
import SkewJacobiNegative.HessenbergExpansion

/-! # The non-dense three-row resonance

Actual geometry and determinant identities of `prop:nondense-resonance` and
`eq:nondense-resonance`.  The quadratic corner is a product, not an
irreducible nonlinear component.
-/
namespace SkewJacobiNegative.NonDenseResonance
open Gluing
set_option backward.isDefEq.respectTransparency false

structure Parameters where
  q : ℕ
  b : ℕ
  g : ℕ
  q_pos : 1 ≤ q
  q_lt_b : q < b
  b_lt_g : b < g

def Parameters.s (p : Parameters) : ℕ := p.b - p.q

def profile (p : Parameters) : Profile 2 where
  r := ![p.b, p.s + p.g, p.s + p.g]
  g := ![p.s, p.s]
  r_pos := by
    intro i
    have := p.q_pos; have := p.q_lt_b; have := p.b_lt_g
    fin_cases i <;> simp [Parameters.s] <;> omega
  g_lt_castSucc := by
    intro i
    have := p.q_pos; have := p.q_lt_b; have := p.b_lt_g
    fin_cases i <;> simp [Parameters.s] <;> omega
  g_lt_succ := by
    intro i
    have := p.q_pos; have := p.q_lt_b; have := p.b_lt_g
    fin_cases i <;> simp [Parameters.s] <;> omega

def diagram (p : Parameters) : BetaDiagram 3 := (profile p).toBetaDiagram

theorem connected (p : Parameters) : (diagram p).Connected :=
  (profile p).toBetaDiagram_connected

private theorem beta_lists (p : Parameters) :
    (diagram p).row = ![(p.b : ℤ) + 2 * p.g, (p.s : ℤ) + 2 * p.g, p.s + p.g] ∧
    (diagram p).col = ![2 * (p.g : ℤ), (p.g : ℤ), 0] := by
  constructor <;> funext i <;> fin_cases i <;>
    simp [diagram, Profile.toBetaDiagram, Profile.xi, Profile.zeta, profile,
      Fin.sum_univ_succ] <;> ring

theorem index_matrix (p : Parameters) :
    (fun i j => (diagram p).row i - (diagram p).col j) =
      ![![(p.b : ℤ), p.b + p.g, p.b + 2 * p.g],
        ![(p.s : ℤ), p.s + p.g, p.s + 2 * p.g],
        ![(p.s : ℤ) - p.g, p.s, p.s + p.g]] := by
  obtain ⟨hr, hc⟩ := beta_lists p
  funext i j
  rw [hr, hc]
  fin_cases i <;> fin_cases j <;> simp <;> ring

private theorem s_pos (p : Parameters) : 0 < p.s := by
  have := p.q_lt_b
  simp [Parameters.s]
  omega

private theorem s_lt_g (p : Parameters) : p.s < p.g := by
  have := p.b_lt_g
  simp [Parameters.s]
  omega

theorem negative_mask (p : Parameters) (i j : Fin 3) :
    (diagram p).row i < (diagram p).col j ↔ i = 2 ∧ j = 0 := by
  obtain ⟨hr, hc⟩ := beta_lists p
  have hs := s_pos p; have hg := s_lt_g p
  have hb : 0 < p.b := by have := p.q_pos; have := p.q_lt_b; omega
  rw [hr, hc]
  fin_cases i <;> fin_cases j <;> simp <;> omega

theorem negative_count (p : Parameters) : negativeCount (diagram p) = 1 := by
  classical
  have he : negativeSites (diagram p) = {(2, 0)} := by
    ext x
    simp [negativeSites, negative_mask, Prod.ext_iff]
  rw [negativeCount, he]
  simp

theorem not_dense (p : Parameters) : ¬ (diagram p).Dense := by
  intro h
  have hn := (negative_mask p 2 0).mpr ⟨rfl, rfl⟩
  have hp := h 2 0
  omega

theorem rotation_rigid (p : Parameters) : (diagram p).RotationRigid :=
  (diagram p).one_negative_rigidity (connected p) (by simp [negative_count])

noncomputable def h (k : ℕ) : CompleteRing := complete k

private theorem matrix_eq (p : Parameters) : (diagram p).matrix =
    ![![h p.b, h (p.b+p.g), h (p.b+2*p.g)],
      ![h p.s, h (p.s+p.g), h (p.s+2*p.g)],
      ![0, h p.s, h (p.s+p.g)]] := by
  have hi := index_matrix p
  have hn : (p.s : ℤ) - p.g < 0 := by have := s_lt_g p; omega
  apply Matrix.ext
  intro i j
  change complete ((diagram p).row i - (diagram p).col j) = _
  change complete ((fun i j => (diagram p).row i - (diagram p).col j) i j) = _
  rw [hi]
  fin_cases i <;> fin_cases j <;> simp [h, complete_of_neg hn, Nat.cast_add,
    Nat.cast_mul]

theorem source_expansion (p : Parameters) : (diagram p).schur =
    h p.b * h (p.s+p.g)^2 - h p.b * h p.s * h (p.s+2*p.g) -
    h (p.b+p.g) * h p.s * h (p.s+p.g) + h (p.b+2*p.g) * h p.s^2 := by
  rw [BetaDiagram.schur, matrix_eq, Matrix.det_fin_three]
  simp
  ring

theorem corner_polynomial (p : Parameters) :
    (diagram p).cornerPolynomial = h p.s * h p.s := by
  unfold BetaDiagram.cornerPolynomial BetaDiagram.cornerBoard
  change ((diagram p).matrix.submatrix Fin.succ Fin.castSucc).det = _
  rw [matrix_eq, Matrix.det_fin_two]
  simp [Matrix.submatrix_apply]

/-- The corner consists of two nonzero singleton Schur factors. -/
theorem corner_product_nonzero (p : Parameters) :
    (diagram p).cornerPolynomial = h p.s * h p.s ∧ h p.s ≠ 0 := by
  refine ⟨corner_polynomial p, ?_⟩
  exact (complete_ne_zero_iff _).mpr (by omega)

private theorem top_expansion (p : Parameters) (t : ℤ) (ht : 0 < t) :
    ((diagram p).extendTop t ht).schur =
      complete (p.b+t) * h (p.s+p.g)^2 -
      complete (p.b+t) * h p.s * h (p.s+2*p.g) -
      complete (p.b+p.g+t) * h p.s * h (p.s+p.g) +
      complete (p.b+2*p.g+t) * h p.s^2 := by
  obtain ⟨hr, hc⟩ := beta_lists p
  have hn : (p.s : ℤ) - p.g < 0 := by have := s_lt_g p; omega
  simp [BetaDiagram.schur, BetaDiagram.matrix, BetaDiagram.extendTop, hr, hc,
    Matrix.det_fin_three, h, complete_of_neg hn, Nat.cast_add, Nat.cast_mul]
  ring_nf
  have hz : complete (-(p.g : ℤ) + p.s) = 0 :=
    complete_of_neg (by have := s_lt_g p; omega)
  rw [hz]
  ring

private theorem bottom_expansion (p : Parameters) (t : ℤ) (ht : 0 < t) :
    ((diagram p).extendBottom t ht).schur =
      h p.b * h (p.s+p.g) * complete (p.s+p.g+t) -
      h p.b * h p.s * complete (p.s+2*p.g+t) -
      h (p.b+p.g) * h p.s * complete (p.s+p.g+t) +
      complete (p.b+2*p.g+t) * h p.s^2 := by
  obtain ⟨hr, hc⟩ := beta_lists p
  have hn : (p.s : ℤ) - p.g < 0 := by have := s_lt_g p; omega
  simp [BetaDiagram.schur, BetaDiagram.matrix, BetaDiagram.extendBottom, hr, hc,
    Matrix.det_fin_three, h, complete_of_neg hn, Nat.cast_add, Nat.cast_mul]
  ring_nf
  rw [complete_of_neg hn]
  ring

theorem endpoint_expansion (p : Parameters) :
    (diagram p).endpointDifference p.g (by have := p.b_lt_g; omega) =
      h (p.b+p.g) * h (p.s+p.g)^2 -
      h (p.b+2*p.g) * h p.s * h (p.s+p.g) -
      h p.b * h (p.s+p.g) * h (p.s+2*p.g) +
      h p.b * h p.s * h (p.s+3*p.g) := by
  unfold BetaDiagram.endpointDifference
  rw [top_expansion, bottom_expansion]
  simp only [h, Nat.cast_add, Nat.cast_mul]
  ring_nf

theorem resonance (p : Parameters) :
    h p.b * ((diagram p).extendTop ((p.g : ℤ)-p.q)
      (by have := p.q_lt_b; have := p.b_lt_g; omega)).schur -
      h (p.s+p.g) * (diagram p).schur =
    h p.s * (diagram p).endpointDifference p.g (by have := p.b_lt_g; omega) := by
  rw [top_expansion, source_expansion, endpoint_expansion]
  have hb : (p.b : ℤ) - p.q = p.s := by
    have := p.q_lt_b
    simp [Parameters.s, Int.ofNat_sub (by omega : p.q ≤ p.b)]
  have h1 : (p.b : ℤ) + ((p.g : ℤ)-p.q) = p.s+p.g := by omega
  have h2 : (p.b : ℤ) + p.g + ((p.g : ℤ)-p.q) = p.s+2*p.g := by omega
  have h3 : (p.b : ℤ) + 2*p.g + ((p.g : ℤ)-p.q) = p.s+3*p.g := by omega
  simp only [h1, h2, h3, h, Nat.cast_add, Nat.cast_mul]
  ring_nf

/-- The fixed index below the moving top corner at the resonance level. -/
def kappa (p : Parameters) : ℕ := p.s + 2*p.g

theorem leader_separation (p : Parameters) :
    p.b + 2*p.g < kappa p + p.g ∧ 0 < p.s ∧ p.b+2*p.g ≠ kappa p+p.g := by
  have := p.b_lt_g
  have := s_pos p
  simp only [kappa]
  omega

private theorem derivative_h (k v : ℕ) (hk : 0 < k) (hv : 0 < v) :
    MvPolynomial.pderiv (⟨v, hv⟩ : ℕ+) (h k) =
      if k = v then 1 else 0 := by
  classical
  have he : h k = (MvPolynomial.X (⟨k, hk⟩ : ℕ+) : CompleteRing) := by
    exact complete_nat (⟨k, hk⟩ : ℕ+)
  rw [he, MvPolynomial.pderiv_X]
  by_cases hkv : k = v
  · subst k
    simp
  · simp [Pi.single_apply, Subtype.ext_iff, hkv, Ne.symm hkv]

/-- The endpoint expansion is uniform in the positive shift. -/
theorem endpoint_uniform (p : Parameters) (t : ℕ) (ht : 0 < t) :
    (diagram p).endpointDifference t (by exact_mod_cast ht) =
      h (p.b+t) * h (p.s+p.g)^2 -
      h (p.b+t) * h p.s * h (p.s+2*p.g) -
      h (p.b+p.g+t) * h p.s * h (p.s+p.g) -
      h p.b * h (p.s+p.g) * h (p.s+p.g+t) +
      h p.b * h p.s * h (p.s+2*p.g+t) +
      h (p.b+p.g) * h p.s * h (p.s+p.g+t) := by
  unfold BetaDiagram.endpointDifference
  rw [top_expansion, bottom_expansion]
  simp only [h, Nat.cast_add, Nat.cast_mul]
  ring_nf

/-- The leading index is fixed before choosing the positive shift. -/
theorem fixed_leader_coefficient (p : Parameters) (t : ℕ) (ht : 0 < t) :
    MvPolynomial.pderiv (⟨kappa p+t, by
      have := s_pos p; simp [kappa]; omega⟩ : ℕ+)
      ((diagram p).endpointDifference t (by exact_mod_cast ht)) =
      h p.b * h p.s := by
  have hs := s_pos p
  have hg := p.b_lt_g
  have hb := p.q_pos
  have hqb := p.q_lt_b
  have hsg := s_lt_g p
  rw [endpoint_uniform p t ht]
  simp (disch := omega) [kappa, map_sub, map_add, MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_pow, derivative_h]
  all_goals split_ifs <;> first | omega | ring

theorem source_corner_coefficient (p : Parameters) :
    MvPolynomial.pderiv
      (⟨(diagram p).largestLabel.toNat, by
        have := (diagram p).largestLabel_pos; omega⟩ : ℕ+)
      (diagram p).schur = h p.s * h p.s := by
  rw [BetaDiagram.pderiv_schur_largest, BetaDiagram.cornerCoefficient,
    corner_polynomial]
  norm_num

/-- Removing the actual moving term leaves the lower polynomial. -/
noncomputable def lowerRemainder (p : Parameters) : CompleteRing :=
  (diagram p).endpointDifference p.g (by have := p.b_lt_g; omega) -
    h p.b * h p.s * h (kappa p+p.g)

theorem moving_coefficient (p : Parameters) :
    MvPolynomial.pderiv (⟨kappa p+p.g, by
      have := s_pos p; simp [kappa]; omega⟩ : ℕ+)
      ((diagram p).endpointDifference p.g (by have := p.b_lt_g; omega)) =
    h p.b * h p.s := by
  have hs := s_pos p
  have hg := p.b_lt_g
  have hb := p.q_pos
  have hqb := p.q_lt_b
  have hsg := s_lt_g p
  rw [endpoint_expansion]
  simp (disch := omega) [kappa, map_sub, map_add, MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_pow, derivative_h]
  all_goals split_ifs <;> first | omega | ring

theorem lower_coefficient (p : Parameters) :
    MvPolynomial.pderiv (⟨p.b+2*p.g, by
      have := p.q_pos; have := p.q_lt_b; omega⟩ : ℕ+)
      (lowerRemainder p) = -(h p.s * h (p.s+p.g)) := by
  have hs := s_pos p
  have hg := p.b_lt_g
  have hb := p.q_pos
  have hqb := p.q_lt_b
  have hsg := s_lt_g p
  have hsb : p.s < p.b := by simp [Parameters.s]; omega
  unfold lowerRemainder
  rw [endpoint_expansion]
  simp (disch := omega) [kappa, map_sub, map_add, MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_pow, derivative_h]
  all_goals split_ifs <;> first | omega | ring

theorem lower_remainder_ne_zero (p : Parameters) : lowerRemainder p ≠ 0 := by
  intro hz
  have hd := lower_coefficient p
  rw [hz, map_zero] at hd
  have hs : h p.s ≠ 0 := (complete_ne_zero_iff _).mpr (by omega)
  have hsg : h (p.s+p.g) ≠ 0 := (complete_ne_zero_iff _).mpr (by omega)
  exact (neg_ne_zero.mpr (mul_ne_zero hs hsg)) hd.symm

/-- Each corner component is an actual singleton profile. -/
def singleton (p : Parameters) : Profile 0 where
  r := fun _ => p.s
  g := Fin.elim0
  r_pos := fun _ => s_pos p
  g_lt_castSucc := by intro j; exact j.elim0
  g_lt_succ := by intro j; exact j.elim0

theorem singleton_schur (p : Parameters) :
    (singleton p).toBetaDiagram.schur = h p.s := by
  rw [Profile.toBetaDiagram_schur, Profile.schur_single_interval]
  simpa only [singleton, h] using (complete_eq_hh (p.s : ℤ)).symm

theorem corner_actual_singletons (p : Parameters) :
    (diagram p).cornerPolynomial =
      (singleton p).toBetaDiagram.schur * (singleton p).toBetaDiagram.schur := by
  rw [singleton_schur, corner_polynomial]

theorem source_largest_index (p : Parameters) :
    (diagram p).largestLabel = (p.b : ℤ) + 2*p.g := by
  obtain ⟨hr, hc⟩ := beta_lists p
  simp [BetaDiagram.largestLabel, hr, hc]

end SkewJacobiNegative.NonDenseResonance
