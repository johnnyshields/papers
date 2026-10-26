/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCofactorIndependence.PrivateEntries
import SkewCofactorIndependence.WeightedReadings
import Mathlib.Data.Fin.Parity

/-!
# Private-entry derivatives of signed cofactors

The deletion maps and common signs in `eq:private-derivative`, including the
second private label used in the nonsymmetric proof of `thm:cofactor-relations`.
All polynomials are the actual signed complementary determinants.
-/

namespace SkewCofactorIndependence
open scoped BigOperators
namespace BetaDiagram
variable {n : ℕ}

/-- A label occurring at precisely the specified matrix site. -/
def PrivateLabel (D : BetaDiagram (n + 1)) (r c : Fin (n + 1)) : Prop :=
  ∀ i j, i ≠ r ∨ j ≠ c → D.row i - D.col j ≠ D.row r - D.col c

/-- Dense deletion is dense even for a one-row or empty child. -/
theorem deleteSite_dense (D : BetaDiagram (n + 1)) (hd : D.Dense)
    (r c : Fin (n + 1)) : (D.deleteSite hd r c).Dense :=
  fun _i _j => hd _ _

/-- The positive generator at a dense matrix site. -/
def siteGenerator (D : BetaDiagram (n + 1)) (hd : D.Dense)
    (r c : Fin (n + 1)) : ℕ+ :=
  ⟨(D.row r - D.col c).toNat, by have := hd r c; omega⟩

@[simp] theorem siteGenerator_int (D : BetaDiagram (n + 1)) (hd : D.Dense)
    (r c : Fin (n + 1)) : ((D.siteGenerator hd r c).val : ℤ) =
      D.row r - D.col c := by
  have := hd r c
  change ((D.row r - D.col c).toNat : ℤ) = D.row r - D.col c
  omega

/-- Complete entries differentiate to zero away from their positive label. -/
theorem pderiv_complete_of_index_ne (v : ℕ+) (k : ℤ)
    (hne : k ≠ (v.val : ℤ)) : MvPolynomial.pderiv v (complete k) = 0 := by
  apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
  intro h
  exact hne ((mem_vars_complete_iff k v).mp h).symm

/-- The private-site condition supplies the entrywise derivative producer. -/
theorem PrivateLabel.pderiv_matrix {D : BetaDiagram (n + 1)} {r c : Fin (n + 1)}
    (hp : D.PrivateLabel r c) (hd : D.Dense) (i j : Fin (n + 1))
    (hij : i ≠ r ∨ j ≠ c) :
    MvPolynomial.pderiv (D.siteGenerator hd r c) (D.matrix i j) = 0 := by
  apply pderiv_complete_of_index_ne
  rw [siteGenerator_int]
  exact hp i j hij

/-- The actual dense entry is its specified positive generator. -/
theorem matrix_siteGenerator (D : BetaDiagram (n + 1)) (hd : D.Dense)
    (r c : Fin (n + 1)) : D.matrix r c = MvPolynomial.X (D.siteGenerator hd r c) := by
  exact complete_of_pos (sub_pos.mpr (hd r c))

/-- Both deletion orders give exactly the same ordered double minor. -/
theorem double_delete_matrix (D : BetaDiagram (n + 2)) (hd : D.Dense)
    (r c : Fin (n + 2)) (a b : Fin (n + 1)) :
    ((D.matrix.submatrix (r.succAbove a).succAbove (c.succAbove b).succAbove).submatrix
      (a.predAbove r).succAbove (b.predAbove c).succAbove) =
      (D.deleteSite hd r c).matrix.submatrix a.succAbove b.succAbove := by
  ext i j
  simp only [matrix, deleteSite, Matrix.submatrix_apply, Matrix.of_apply,
    Fin.succAbove_succAbove_succAbove_predAbove]

/-- The two deletion-parity changes cancel; no site-dependent sign remains. -/
theorem double_delete_sign (r c : Fin (n + 2)) (a b : Fin (n + 1)) :
    (-1 : CompleteRing) ^ ((r.succAbove a).val + (c.succAbove b).val) *
      (-1) ^ ((a.predAbove r).val + (b.predAbove c).val) =
      (-1) ^ (r.val + c.val) * (-1) ^ (a.val + b.val) := by
  have hr := Fin.neg_one_pow_succAbove_add_predAbove (R := CompleteRing) r a
  have hc := Fin.neg_one_pow_succAbove_add_predAbove (R := CompleteRing) c b
  simp only [pow_add] at hr hc ⊢
  calc
    _ = ((-1 : CompleteRing) ^ (r.succAbove a).val * (-1) ^ (a.predAbove r).val) *
      ((-1) ^ (c.succAbove b).val * (-1) ^ (b.predAbove c).val) := by ring
    _ = (-(-1 : CompleteRing) ^ r.val * (-1) ^ a.val) *
      (-(-1 : CompleteRing) ^ c.val * (-1) ^ b.val) := by rw [hr, hc]; ring
    _ = _ := by ring

/-- Arbitrary private-site differentiation with exact deletion indices and common sign. -/
theorem cofactor_pderiv_private (D : BetaDiagram (n + 2)) (hd : D.Dense)
    (r c : Fin (n + 2)) (hp : D.PrivateLabel r c) (a b : Fin (n + 1)) :
    MvPolynomial.pderiv (D.siteGenerator hd r c)
      (D.cofactor (r.succAbove a) (c.succAbove b)) =
        (-1) ^ (r.val + c.val) * (D.deleteSite hd r c).cofactor a b := by
  classical
  let i := r.succAbove a
  let j := c.succAbove b
  let v := D.siteGenerator hd r c
  let M := D.matrix.submatrix i.succAbove j.succAbove
  have he : M (a.predAbove r) (b.predAbove c) = MvPolynomial.X v := by
    simp only [M, i, j, Matrix.submatrix_apply, Fin.succAbove_succAbove_predAbove]
    exact D.matrix_siteGenerator hd r c
  have hprivate : ∀ x y, x ≠ a.predAbove r ∨ y ≠ b.predAbove c →
      MvPolynomial.pderiv v (M x y) = 0 := by
    intro x y hxy
    apply hp.pderiv_matrix hd
    rcases hxy with hx | hy
    · left
      intro h
      apply hx
      apply (Fin.succAbove_right_injective (p := i))
      exact h.trans (Fin.succAbove_succAbove_predAbove r a).symm
    · right
      intro h
      apply hy
      apply (Fin.succAbove_right_injective (p := j))
      exact h.trans (Fin.succAbove_succAbove_predAbove c b).symm
  have hs : MvPolynomial.pderiv v ((-1 : CompleteRing) ^ (i.val + j.val)) = 0 := by
    have he : (-1 : CompleteRing) ^ (i.val + j.val) =
        MvPolynomial.C ((-1 : ℚ) ^ (i.val + j.val)) := by simp
    rw [he]
    exact MvPolynomial.pderiv_C
  unfold cofactor
  rw [MvPolynomial.pderiv_mul, hs, zero_mul, zero_add,
    pderiv_det_private_of_derivative_zero M v _ _ he hprivate]
  change (-1 : CompleteRing) ^ (i.val + j.val) *
    ((-1) ^ ((a.predAbove r).val + (b.predAbove c).val) *
      (M.submatrix (a.predAbove r).succAbove (b.predAbove c).succAbove).det) = _
  rw [show M.submatrix (a.predAbove r).succAbove (b.predAbove c).succAbove =
    (D.deleteSite hd r c).matrix.submatrix a.succAbove b.succAbove from
      D.double_delete_matrix hd r c a b, ← mul_assoc, double_delete_sign r c a b]
  ring

/-- Deleting the private entry's row or column annihilates its derivative. -/
theorem cofactor_pderiv_private_boundary (D : BetaDiagram (n + 1)) (hd : D.Dense)
    (r c i j : Fin (n + 1)) (hp : D.PrivateLabel r c) (hij : i = r ∨ j = c) :
    MvPolynomial.pderiv (D.siteGenerator hd r c) (D.cofactor i j) = 0 := by
  unfold cofactor
  rw [MvPolynomial.pderiv_mul]
  have hs : MvPolynomial.pderiv (D.siteGenerator hd r c)
      ((-1 : CompleteRing) ^ (i.val + j.val)) = 0 := by
    have he : (-1 : CompleteRing) ^ (i.val + j.val) =
        MvPolynomial.C ((-1 : ℚ) ^ (i.val + j.val)) := by simp
    rw [he]
    exact MvPolynomial.pderiv_C
  have hm : MvPolynomial.pderiv (D.siteGenerator hd r c)
      (D.matrix.submatrix i.succAbove j.succAbove).det = 0 := by
    apply pderiv_det_eq_zero
    intro a b
    apply hp.pderiv_matrix hd
    rcases hij with h | h
    · left
      subst i
      exact Fin.succAbove_ne _ _
    · right
      subst j
      exact Fin.succAbove_ne _ _
  rw [hs, hm]
  simp

/-- The largest label is private without any symmetry or normalization assumption. -/
theorem corner_private (D : BetaDiagram (n + 1)) : D.PrivateLabel 0 (Fin.last n) := by
  intro i j hij
  exact ne_of_lt (D.index_lt_largestLabel i j hij)

/-- Exact corner identity `eq:private-derivative`, with zero-based child indices. -/
theorem cofactor_pderiv_corner (D : BetaDiagram (n + 2)) (hd : D.Dense)
    (i j : Fin (n + 1)) :
    MvPolynomial.pderiv (D.siteGenerator hd 0 (Fin.last (n + 1)))
      (D.cofactor i.succ j.castSucc) =
        (-1) ^ (n + 1) * (D.deleteSite hd 0 (Fin.last (n + 1))).cofactor i j := by
  simpa only [Fin.zero_succAbove, Fin.succAbove_last, Fin.val_zero, Fin.val_last,
    zero_add] using D.cofactor_pderiv_private hd 0 (Fin.last (n + 1)) D.corner_private i j

/-- A smaller top margin makes the second row's last entry private. -/
theorem second_label_private (D : BetaDiagram (n + 2))
    (hgap : D.row 0 - D.row (0 : Fin (n + 1)).succ <
      D.col (Fin.last n).castSucc - D.col (Fin.last (n + 1))) :
    D.PrivateLabel (0 : Fin (n + 1)).succ (Fin.last (n + 1)) := by
  intro i j hij he
  have hr : D.row i ≤ D.row 0 := D.row_strictAnti.antitone (Fin.zero_le i)
  have hc : D.col (Fin.last (n + 1)) ≤ D.col j :=
    D.col_strictAnti.antitone (Fin.le_last j)
  by_cases hj : j = Fin.last (n + 1)
  · subst j
    have hi := hij.resolve_right (by simp)
    exact hi (D.row_strictAnti.injective (by omega))
  · have hjle : j ≤ (Fin.last n).castSucc := by
      apply Fin.le_iff_val_le_val.mpr
      have := Fin.lt_last_iff_ne_last.mpr hj
      simp only [Fin.lt_def, Fin.val_last] at this
      simp only [Fin.val_castSucc, Fin.val_last]
      omega
    have hc' := D.col_strictAnti.antitone hjle
    by_cases hi : i = 0
    · subst i
      omega
    · have hile : (0 : Fin (n + 1)).succ ≤ i := by
        apply Fin.le_iff_val_le_val.mpr
        have := Fin.pos_iff_ne_zero.mpr hi
        simp only [Fin.lt_def, Fin.val_zero] at this
        simp only [Fin.val_succ, Fin.val_zero]
        omega
      have hr' := D.row_strictAnti.antitone hile
      have hc'' := D.col_strictAnti (Fin.lt_last_iff_ne_last.mpr hj)
      omega

/-- The second-label identity keeps the actual row-deletion map, including row zero. -/
theorem cofactor_pderiv_second (D : BetaDiagram (n + 2)) (hd : D.Dense)
    (hgap : D.row 0 - D.row (0 : Fin (n + 1)).succ <
      D.col (Fin.last n).castSucc - D.col (Fin.last (n + 1)))
    (i j : Fin (n + 1)) :
    MvPolynomial.pderiv (D.siteGenerator hd (0 : Fin (n + 1)).succ (Fin.last (n + 1)))
      (D.cofactor ((0 : Fin (n + 1)).succ.succAbove i) j.castSucc) =
        (-1) ^ (n + 2) *
          (D.deleteSite hd (0 : Fin (n + 1)).succ (Fin.last (n + 1))).cofactor i j := by
  simpa only [Fin.succAbove_last, Fin.val_succ, Fin.val_zero, Fin.val_last,
    Nat.add_comm 1] using D.cofactor_pderiv_private hd
      (0 : Fin (n + 1)).succ (Fin.last (n + 1)) (D.second_label_private hgap) i j

end BetaDiagram
end SkewCofactorIndependence
