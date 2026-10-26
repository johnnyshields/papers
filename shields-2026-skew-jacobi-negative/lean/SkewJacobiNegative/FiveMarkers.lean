/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.FivePrimeObstruction
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid

/-!
# Collected corner markers of the five-negative normal forms

Actual complementary determinants and polynomial coefficient extraction for
`eq:five-marker` in `shields-2026-skew-jacobi-negative.tex`.  A coordinate
with index zero is erased or differentiated as an independent variable.
-/

namespace SkewJacobiNegative.FiveNegative

open MvPolynomial
open scoped BigOperators

/-- Fix a classical normalization for gcds of the actual homogeneous polynomials. -/
noncomputable instance homStrongNormalizationMonoid :
    StrongNormalizationMonoid Gluing.HomLambda :=
  UniqueFactorizationMonoid.strongNormalizationMonoid

noncomputable instance homStrongNormalizedGCDMonoid :
    StrongNormalizedGCDMonoid Gluing.HomLambda :=
  UniqueFactorizationMonoid.toStrongNormalizedGCDMonoid Gluing.HomLambda

private theorem hTilde_eq_X_of_index {z : ℤ} {k : ℕ} (h : z = (k : ℤ)) :
    Gluing.hTilde z = (X k : Gluing.HomLambda) := by
  rw [h,Gluing.hTilde,if_neg (show ¬ (k : ℤ) < 0 by omega),Int.toNat_natCast]

private theorem hTilde_eq_zero_of_index {z : ℤ} (h : z < 0) :
    Gluing.hTilde z = (0 : Gluing.HomLambda) := by simp [Gluing.hTilde,h]

noncomputable def homCofactor (D : BetaDiagram 5) (i j : Fin 5) : Gluing.HomLambda :=
  (-1)^(i.val+j.val) * (D.homMatrix.submatrix i.succAbove j.succAbove).det

noncomputable def C15 (t : Parameters) : Gluing.HomLambda :=
  X t.a * X t.p * B t.u t.v t.tau
noncomputable def C14 (t : Parameters) : Gluing.HomLambda :=
  -(X t.a * X t.b * B t.u t.v t.tau)
noncomputable def C25M (t : Parameters) : Gluing.HomLambda :=
  -(X t.x * X t.p * B t.u t.v t.tau)
noncomputable def C25E (t : Parameters) : Gluing.HomLambda :=
  -(X t.a * X t.p * F t.v t.x t.tau)

/-- The actual maximum matrix label, common to the two displayed parameterizations. -/
def m (t : Parameters) : ℕ := t.x+t.y+t.c+t.b-t.a-t.tau-t.p
def deltaM (t : Parameters) : ℕ := t.x-t.a
def deltaE (t : Parameters) : ℕ := t.x-t.u
def NM (t : Parameters) : ℕ := m t - min t.q (deltaM t)
def NE (t : Parameters) : ℕ := m t - min t.q (deltaE t)

noncomputable def secondM (t : Parameters) : Gluing.HomLambda :=
  (if t.q ≤ deltaM t then C14 t else 0) +
    (if deltaM t ≤ t.q then C25M t else 0)
noncomputable def secondE (t : Parameters) : Gluing.HomLambda :=
  (if t.q ≤ deltaE t then C14 t else 0) +
    (if deltaE t ≤ t.q then C25E t else 0)

/-- Erase a coordinate, not all matrix positions carrying a lower label. -/
noncomputable def eraseOne (j : ℕ) : Gluing.HomLambda →ₐ[ℚ] Gluing.HomLambda :=
  aeval fun k => if k=j then 0 else X k

@[simp] theorem eraseOne_X (j k : ℕ) : eraseOne j (X k) =
    if k=j then 0 else (X k : Gluing.HomLambda) := by simp [eraseOne]

/-- Literal homogeneous middle-pattern matrix. -/
noncomputable def mMatrix (t : Parameters) : Matrix (Fin 5) (Fin 5) Gluing.HomLambda :=
  !![X t.x, X (t.x+t.y-t.a), X (t.x+t.y+t.v-t.a-t.tau),
      X (t.x+t.y+t.c-t.a-t.tau), X (m t);
    X t.a, X t.y, X (t.y+t.v-t.tau), X (t.y+t.c-t.tau),
      X (t.y+t.c+t.b-t.tau-t.p);
    0, X t.u, X t.L, X (t.u+t.c-t.tau), X (t.u+t.c+t.b-t.tau-t.p);
    0, X t.tau, X t.v, X t.c, X (t.c+t.q);
    0, 0, 0, X t.p, X t.b]

/-- Literal homogeneous oriented end-pattern matrix. -/
noncomputable def eMatrix (t : Parameters) : Matrix (Fin 5) (Fin 5) Gluing.HomLambda :=
  !![X t.x, X (t.x+t.v-t.tau), X (t.x+t.y-t.tau),
      X (t.x+t.y+t.c-t.tau-t.a), X (m t);
    X t.u, X t.L, X (t.u+t.y-t.tau), X (t.u+t.y+t.c-t.tau-t.a),
      X (t.u+t.y+t.c+t.b-t.tau-t.a-t.p);
    X t.tau, X t.v, X t.y, X (t.y+t.c-t.a), X (t.y+t.c+t.b-t.a-t.p);
    0, 0, X t.a, X t.c, X (t.c+t.q);
    0, 0, 0, X t.p, X t.b]

theorem M_homMatrix (t : Parameters) (h : ValidM t) : (M t h).homMatrix = mMatrix t := by
  apply Matrix.ext
  intro i j
  change Gluing.hTilde ((M t h).row i-(M t h).col j) = mMatrix t i j
  rw [M_index]
  rcases h with ⟨hu,hv,hb,hx,hy,hc⟩
  have hL : t.L+t.tau=t.u+t.v := by dsimp [Parameters.L]; omega
  fin_cases i <;> fin_cases j <;>
    simp [profileIndex,Fin.sum_univ_succ,mMatrix] <;>
    first
    | exact hTilde_eq_X_of_index rfl
    | apply hTilde_eq_X_of_index <;>
        (dsimp [m,Parameters.q,Parameters.L] at * <;> omega)
    | apply hTilde_eq_zero_of_index <;>
        (dsimp [m,Parameters.q,Parameters.L] at * <;> omega)

theorem E_homMatrix (t : Parameters) (h : ValidE t) : (E t h).homMatrix = eMatrix t := by
  apply Matrix.ext
  intro i j
  change Gluing.hTilde ((E t h).row i-(E t h).col j) = eMatrix t i j
  rw [E_index]
  rcases h with ⟨hu,hv,hb,hx,hy,hc⟩
  have hL : t.L+t.tau=t.u+t.v := by dsimp [Parameters.L]; omega
  fin_cases i <;> fin_cases j <;>
    simp [profileIndex,Fin.sum_univ_succ,eMatrix] <;>
    first
    | exact hTilde_eq_X_of_index rfl
    | apply hTilde_eq_X_of_index <;>
        (dsimp [m,Parameters.q,Parameters.L] at * <;> omega)
    | apply hTilde_eq_zero_of_index <;>
        (dsimp [m,Parameters.q,Parameters.L] at * <;> omega)

private theorem finCons_one {α : Type*} {n : ℕ} (a : α) (v : Fin (n+1) → α) :
    Fin.cons (α := fun _ : Fin (n+2) => α) a v (1 : Fin (n+2))=v 0 := rfl

private theorem finCons_two {α : Type*} {n : ℕ} (a : α) (v : Fin (n+2) → α) :
    Fin.cons (α := fun _ : Fin (n+3) => α) a v (2 : Fin (n+3))=v 1 := rfl

private theorem finCons_three {α : Type*} {n : ℕ} (a : α) (v : Fin (n+3) → α) :
    Fin.cons (α := fun _ : Fin (n+4) => α) a v (3 : Fin (n+4))=v 2 := rfl

private theorem finCons_four {α : Type*} {n : ℕ} (a : α) (v : Fin (n+4) → α) :
    Fin.cons (α := fun _ : Fin (n+5) => α) a v (4 : Fin (n+5))=v 3 := rfl

private theorem castSucc_one {n : ℕ} :
    (1 : Fin (n+2)).castSucc=(1 : Fin (n+3)) := rfl

private theorem castSucc_two {n : ℕ} :
    (2 : Fin (n+3)).castSucc=(2 : Fin (n+4)) := rfl

private theorem castSucc_three {n : ℕ} :
    (3 : Fin (n+4)).castSucc=(3 : Fin (n+5)) := rfl

private theorem det_four_last_row (A : Matrix (Fin 4) (Fin 4) Gluing.HomLambda)
    (h0 : A 3 0=0) (h1 : A 3 1=0) (h2 : A 3 2=0) :
    A.det=A 3 3*(A.submatrix (3 : Fin 4).succAbove (3 : Fin 4).succAbove).det := by
  rw [Matrix.det_succ_row A (3 : Fin 4)]
  rw [Finset.sum_eq_single (3 : Fin 4)]
  · norm_num
  · intro j _ hj
    have hz : A 3 j=0 := by
      fin_cases j
      · exact h0
      · exact h1
      · exact h2
      · exact False.elim (hj rfl)
    rw [hz]
    ring
  · intro h
    exact False.elim (h (Finset.mem_univ 3))

/-- The maximal cofactor is computed from the original middle board. -/
theorem M_C15 (t : Parameters) (h : ValidM t) : homCofactor (M t h) 0 4 = C15 t := by
  unfold homCofactor
  rw [M_homMatrix,det_four_last_row
    ((mMatrix t).submatrix (0 : Fin 5).succAbove (4 : Fin 5).succAbove) rfl rfl rfl,
    Matrix.det_fin_three]
  dsimp only [mMatrix,Matrix.submatrix,Fin.succAbove,Matrix.vecCons,Fin.cons,C15,B,Parameters.L]
  norm_num only [Matrix.of_apply,Equiv.refl_apply,Fin.cons_zero,Fin.cons_succ,Fin.cases,
    Fin.lt_def,Fin.val_castSucc,Fin.val_succ,Fin.val_natCast,Fin.val_zero,
    Fin.coe_ofNat_eq_mod,finCons_one,finCons_two,finCons_three,finCons_four,ite_true,ite_false,
    Fin.castSucc_zero,castSucc_one,castSucc_two,castSucc_three,Equiv.refl]
  ring

theorem E_C15 (t : Parameters) (h : ValidE t) : homCofactor (E t h) 0 4 = C15 t := by
  unfold homCofactor
  rw [E_homMatrix,det_four_last_row
    ((eMatrix t).submatrix (0 : Fin 5).succAbove (4 : Fin 5).succAbove) rfl rfl rfl,
    Matrix.det_fin_three]
  dsimp only [eMatrix,Matrix.submatrix,Fin.succAbove,Matrix.vecCons,Fin.cons,C15,B,Parameters.L]
  norm_num only [Matrix.of_apply,Equiv.refl_apply,Fin.cons_zero,Fin.cons_succ,Fin.cases,
    Fin.lt_def,Fin.val_castSucc,Fin.val_succ,Fin.val_natCast,Fin.val_zero,
    Fin.coe_ofNat_eq_mod,finCons_one,finCons_two,finCons_three,finCons_four,ite_true,ite_false,
    Fin.castSucc_zero,castSucc_one,castSucc_two,castSucc_three,Equiv.refl]
  ring

theorem M_C14 (t : Parameters) (h : ValidM t) : homCofactor (M t h) 0 3 = C14 t := by
  unfold homCofactor
  rw [M_homMatrix,det_four_last_row
    ((mMatrix t).submatrix (0 : Fin 5).succAbove (3 : Fin 5).succAbove) rfl rfl rfl,
    Matrix.det_fin_three]
  dsimp only [mMatrix,Matrix.submatrix,Fin.succAbove,Matrix.vecCons,Fin.cons,C14,B,Parameters.L]
  norm_num only [Matrix.of_apply,Equiv.refl_apply,Fin.cons_zero,Fin.cons_succ,Fin.cases,
    Fin.lt_def,Fin.val_castSucc,Fin.val_succ,Fin.val_natCast,Fin.val_zero,
    Fin.coe_ofNat_eq_mod,finCons_one,finCons_two,finCons_three,finCons_four,ite_true,ite_false,
    Fin.castSucc_zero,castSucc_one,castSucc_two,castSucc_three,Equiv.refl]
  ring

theorem E_C14 (t : Parameters) (h : ValidE t) : homCofactor (E t h) 0 3 = C14 t := by
  unfold homCofactor
  rw [E_homMatrix,det_four_last_row
    ((eMatrix t).submatrix (0 : Fin 5).succAbove (3 : Fin 5).succAbove) rfl rfl rfl,
    Matrix.det_fin_three]
  dsimp only [eMatrix,Matrix.submatrix,Fin.succAbove,Matrix.vecCons,Fin.cons,C14,B,Parameters.L]
  norm_num only [Matrix.of_apply,Equiv.refl_apply,Fin.cons_zero,Fin.cons_succ,Fin.cases,
    Fin.lt_def,Fin.val_castSucc,Fin.val_succ,Fin.val_natCast,Fin.val_zero,
    Fin.coe_ofNat_eq_mod,finCons_one,finCons_two,finCons_three,finCons_four,ite_true,ite_false,
    Fin.castSucc_zero,castSucc_one,castSucc_two,castSucc_three,Equiv.refl]
  ring

theorem M_C25 (t : Parameters) (h : ValidM t) : homCofactor (M t h) 1 4 = C25M t := by
  unfold homCofactor
  rw [M_homMatrix,det_four_last_row
    ((mMatrix t).submatrix (1 : Fin 5).succAbove (4 : Fin 5).succAbove) rfl rfl rfl,
    Matrix.det_fin_three]
  dsimp only [mMatrix,Matrix.submatrix,Fin.succAbove,Matrix.vecCons,Fin.cons,C25M,B,Parameters.L]
  norm_num only [Matrix.of_apply,Equiv.refl_apply,Fin.cons_zero,Fin.cons_succ,Fin.cases,
    Fin.lt_def,Fin.val_castSucc,Fin.val_succ,Fin.val_natCast,Fin.val_zero,
    Fin.coe_ofNat_eq_mod,finCons_one,finCons_two,finCons_three,finCons_four,ite_true,ite_false,
    Fin.castSucc_zero,castSucc_one,castSucc_two,castSucc_three,Equiv.refl]
  ring

theorem E_C25 (t : Parameters) (h : ValidE t) : homCofactor (E t h) 1 4 = C25E t := by
  unfold homCofactor
  rw [E_homMatrix,det_four_last_row
    ((eMatrix t).submatrix (1 : Fin 5).succAbove (4 : Fin 5).succAbove) rfl rfl rfl,
    Matrix.det_fin_three]
  dsimp only [eMatrix,Matrix.submatrix,Fin.succAbove,Matrix.vecCons,Fin.cons,C25E,F]
  norm_num only [Matrix.of_apply,Equiv.refl_apply,Fin.cons_zero,Fin.cons_succ,Fin.cases,
    Fin.lt_def,Fin.val_castSucc,Fin.val_succ,Fin.val_natCast,Fin.val_zero,
    Fin.coe_ofNat_eq_mod,finCons_one,finCons_two,finCons_three,finCons_four,ite_true,ite_false,
    Fin.castSucc_zero,castSucc_one,castSucc_two,castSucc_three,Equiv.refl]
  ring

theorem C15_ne_zero (t : Parameters) (hu : t.tau<t.u) (hv : t.tau<t.v) : C15 t ≠ 0 :=
  mul_ne_zero (mul_ne_zero (X_ne_zero _) (X_ne_zero _)) (B_irreducible _ _ _ hu hv).ne_zero

theorem C14_ne_zero (t : Parameters) (hu : t.tau<t.u) (hv : t.tau<t.v) : C14 t ≠ 0 :=
  neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (X_ne_zero _) (X_ne_zero _))
    (B_irreducible _ _ _ hu hv).ne_zero)

theorem C25M_ne_zero (t : Parameters) (hu : t.tau<t.u) (hv : t.tau<t.v) : C25M t ≠ 0 :=
  neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (X_ne_zero _) (X_ne_zero _))
    (B_irreducible _ _ _ hu hv).ne_zero)

theorem C25E_ne_zero (t : Parameters) (h : ValidE t) : C25E t ≠ 0 := by
  rcases h with ⟨hu,hv,hb,hx,hy,hc⟩
  exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (X_ne_zero _) (X_ne_zero _))
    (F_irreducible _ _ _ hv (by omega)).ne_zero)

theorem secondM_strict_q (t : Parameters) (h : t.q<deltaM t) : secondM t=C14 t := by
  simp [secondM,h.le,not_le.mpr h]
theorem secondM_strict_delta (t : Parameters) (h : deltaM t<t.q) : secondM t=C25M t := by
  simp [secondM,h.le,not_le.mpr h]
theorem secondM_tied (t : Parameters) (h : t.q=deltaM t) :
    secondM t=C14 t+C25M t := by simp [secondM,h]
theorem secondE_strict_q (t : Parameters) (h : t.q<deltaE t) : secondE t=C14 t := by
  simp [secondE,h.le,not_le.mpr h]
theorem secondE_strict_delta (t : Parameters) (h : deltaE t<t.q) : secondE t=C25E t := by
  simp [secondE,h.le,not_le.mpr h]
theorem secondE_tied (t : Parameters) (h : t.q=deltaE t) :
    secondE t=C14 t+C25E t := by simp [secondE,h]

noncomputable def endTieParenthesis (t : Parameters) : Gluing.HomLambda :=
  X t.b * B t.u t.v t.tau + X t.p * F t.v t.x t.tau

theorem B_not_dvd_X (u v tau j : ℕ) (hu : tau<u) (hv : tau<v) :
    ¬ B u v tau ∣ (X j : Gluing.HomLambda) := by
  intro hd
  have ht := totalDegree_le_of_dvd_of_isDomain hd (X_ne_zero j)
  rw [B_totalDegree _ _ _ hu hv,totalDegree_X] at ht
  omega

/-- The end-pattern quadratic is genuinely different from the opening quadratic. -/
theorem B_not_dvd_F (u v tau x : ℕ) (hu : tau<u) (hv : tau<v) (hx : u<x) :
    ¬ B u v tau ∣ F v x tau := by
  classical
  let j := x+v-tau
  have hjx : x≠j := by dsimp [j]; omega
  have hjv : v≠j := by dsimp [j]; omega
  have hju : u≠j := by dsimp [j]; omega
  have hjtau : tau≠j := by dsimp [j]; omega
  have hjL : u+v-tau≠j := by dsimp [j]; omega
  have hB : pderiv j (B u v tau)=0 := by
    simp [B,pderiv_mul,Pi.single_apply,hju,hjv,hjtau,hjL]
  have hF : pderiv j (F v x tau)=-(X tau : Gluing.HomLambda) := by
    change pderiv j (X v*X x-X tau*X j)=-(X tau : Gluing.HomLambda)
    simp only [map_sub,pderiv_mul,pderiv_X_of_ne hjv,pderiv_X_of_ne hjx,
      pderiv_X_of_ne hjtau,pderiv_X_self,zero_mul,mul_zero,mul_one,zero_add]
    ring
  rintro ⟨r,hr⟩
  have hd := congrArg (pderiv j) hr
  rw [hF,pderiv_mul,hB] at hd
  have hdiv : B u v tau ∣ -(X tau : Gluing.HomLambda) := ⟨pderiv j r,by simpa using hd⟩
  exact B_not_dvd_X _ _ _ _ hu hv (by simpa using hdiv)

theorem coordinate_gcd_one (i j : ℕ) (h : i≠j) :
    gcd (X i : Gluing.HomLambda) (X j)=1 := by
  apply (X_prime (R := ℚ) (i := i)).irreducible.gcd_eq_one_iff.mpr
  simpa only [X_dvd_X] using h

theorem endTie_coordinate_not_dvd (t : Parameters) (h : ValidE t) :
    ¬ (X t.p : Gluing.HomLambda) ∣ endTieParenthesis t := by
  rcases h with ⟨hu,hv,hb,hx,hy,hc⟩
  intro hd
  have hpf : (X t.p : Gluing.HomLambda) ∣ X t.p * F t.v t.x t.tau :=
    dvd_mul_right _ _
  have hpb : (X t.p : Gluing.HomLambda) ∣ X t.b * B t.u t.v t.tau := by
    have hh := dvd_sub hd hpf
    simpa [endTieParenthesis] using hh
  rcases (X_prime (R := ℚ) (i := t.p)).dvd_mul.mp hpb with he | he
  · have he' := X_dvd_X.mp he
    omega
  · exact B_coordinate_not_dvd _ _ _ _ hu hv he

theorem endTie_B_not_dvd (t : Parameters) (h : ValidE t) :
    ¬ B t.u t.v t.tau ∣ endTieParenthesis t := by
  rcases h with ⟨hu,hv,hb,hx,hy,hc⟩
  intro hd
  have hbb : B t.u t.v t.tau ∣ X t.b * B t.u t.v t.tau := dvd_mul_left _ _
  have hpf : B t.u t.v t.tau ∣ X t.p * F t.v t.x t.tau := by
    have hh := dvd_sub hd hbb
    simpa [endTieParenthesis] using hh
  rcases (B_irreducible _ _ _ hu hv).prime.dvd_mul.mp hpf with he | he
  · exact B_not_dvd_X _ _ _ _ hu hv he
  · exact B_not_dvd_F _ _ _ _ hu hv hx he

private theorem gcd_product_one (a b c : Gluing.HomLambda)
    (hb : gcd a b=1) (hc : gcd a c=1) : gcd a (b*c)=1 := by
  have hd := gcd_mul_dvd_mul_gcd a b c
  rw [hb,hc,one_mul] at hd
  have he := gcd_eq_normalize hd (one_dvd (gcd a (b*c)))
  simpa using he

-- Classical normalization of an infinite-variable UFD makes the generic gcd transport expensive.
set_option maxHeartbeats 300000 in
theorem E_gcd_strict_q (t : Parameters) (h : ValidE t) (hr : t.q<deltaE t) :
    Associated (gcd (C15 t) (secondE t)) (X t.a * B t.u t.v t.tau) := by
  rcases h with ⟨hu,hv,hb,hx,hy,hc⟩
  rw [secondE_strict_q t hr]
  have h15 : C15 t=(X t.a * B t.u t.v t.tau)*X t.p := by unfold C15; ring
  have h14 : C14 t=-((X t.a * B t.u t.v t.tau)*X t.b) := by unfold C14; ring
  rw [h15,h14,gcd_neg]
  have hg := coordinate_gcd_one t.p t.b (by omega)
  have hm := gcd_mul_left' (X t.a * B t.u t.v t.tau) (X t.p) (X t.b)
  rw [hg,mul_one] at hm
  exact hm

-- Classical normalization of an infinite-variable UFD makes the generic gcd transport expensive.
set_option maxHeartbeats 300000 in
theorem E_gcd_strict_delta (t : Parameters) (h : ValidE t) (hr : deltaE t<t.q) :
    Associated (gcd (C15 t) (secondE t)) (X t.a * X t.p) := by
  rcases h with ⟨hu,hv,hb,hx,hy,hc⟩
  rw [secondE_strict_delta t hr]
  unfold C15 C25E
  rw [gcd_neg]
  have hg : gcd (B t.u t.v t.tau) (F t.v t.x t.tau)=1 :=
    (B_irreducible _ _ _ hu hv).gcd_eq_one_iff.mpr (B_not_dvd_F _ _ _ _ hu hv hx)
  have hm := gcd_mul_left' (X t.a * X t.p)
    (B t.u t.v t.tau) (F t.v t.x t.tau)
  rw [hg,mul_one] at hm
  exact hm

-- Classical normalization of an infinite-variable UFD makes the generic gcd transport expensive.
set_option maxHeartbeats 300000 in
theorem E_gcd_tied (t : Parameters) (h : ValidE t) (hr : t.q=deltaE t) :
    Associated (gcd (C15 t) (secondE t)) (X t.a : Gluing.HomLambda) := by
  have hp : gcd (X t.p : Gluing.HomLambda) (endTieParenthesis t)=1 :=
    (X_prime (R := ℚ) (i := t.p)).irreducible.gcd_eq_one_iff.mpr
      (endTie_coordinate_not_dvd t h)
  have hB : gcd (B t.u t.v t.tau) (endTieParenthesis t)=1 :=
    (B_irreducible _ _ _ h.1 h.2.1).gcd_eq_one_iff.mpr (endTie_B_not_dvd t h)
  have hg : gcd (X t.p * B t.u t.v t.tau) (endTieParenthesis t)=1 := by
    rw [gcd_comm]
    exact gcd_product_one _ _ _ (by simpa [gcd_comm] using hp)
      (by simpa [gcd_comm] using hB)
  have hs : secondE t=-(X t.a * endTieParenthesis t) := by
    rw [secondE_tied t hr]
    unfold C14 C25E endTieParenthesis
    ring
  have h15 : C15 t=X t.a * (X t.p * B t.u t.v t.tau) := by unfold C15; ring
  rw [hs,h15,gcd_neg]
  have hm := gcd_mul_left' (X t.a) (X t.p * B t.u t.v t.tau) (endTieParenthesis t)
  rw [hg,mul_one] at hm
  exact hm

private theorem associated_degree (a b : Gluing.HomLambda)
    (h : Associated a b) (ha : a≠0) (hb : b≠0) : a.totalDegree=b.totalDegree :=
  le_antisymm (totalDegree_le_of_dvd_of_isDomain h.dvd hb)
    (totalDegree_le_of_dvd_of_isDomain h.symm.dvd ha)

theorem E_gcd_degree_strict_q (t : Parameters) (h : ValidE t) (hr : t.q<deltaE t) :
    (gcd (C15 t) (secondE t)).totalDegree=3 := by
  have hg := E_gcd_strict_q t h hr
  have hn : gcd (C15 t) (secondE t)≠0 := by
    intro hz
    have hd := gcd_dvd_left (C15 t) (secondE t)
    rw [hz] at hd
    exact C15_ne_zero t h.1 h.2.1 (zero_dvd_iff.mp hd)
  rw [associated_degree _ _ hg hn
    (mul_ne_zero (X_ne_zero _) (B_irreducible _ _ _ h.1 h.2.1).ne_zero),
    totalDegree_mul_of_isDomain (X_ne_zero _) (B_irreducible _ _ _ h.1 h.2.1).ne_zero,
    totalDegree_X,B_totalDegree _ _ _ h.1 h.2.1]

theorem E_gcd_degree_strict_delta (t : Parameters) (h : ValidE t)
    (hr : deltaE t<t.q) : (gcd (C15 t) (secondE t)).totalDegree=2 := by
  have hn : gcd (C15 t) (secondE t)≠0 := by
    intro hz
    have hd := gcd_dvd_left (C15 t) (secondE t)
    rw [hz] at hd
    exact C15_ne_zero t h.1 h.2.1 (zero_dvd_iff.mp hd)
  rw [associated_degree _ _ (E_gcd_strict_delta t h hr) hn
    (mul_ne_zero (X_ne_zero _) (X_ne_zero _)),
    totalDegree_mul_of_isDomain (X_ne_zero _) (X_ne_zero _),totalDegree_X,totalDegree_X]

theorem E_gcd_degree_tied (t : Parameters) (h : ValidE t) (hr : t.q=deltaE t) :
    (gcd (C15 t) (secondE t)).totalDegree=1 := by
  have hn : gcd (C15 t) (secondE t)≠0 := by
    intro hz
    have hd := gcd_dvd_left (C15 t) (secondE t)
    rw [hz] at hd
    exact C15_ne_zero t h.1 h.2.1 (zero_dvd_iff.mp hd)
  rw [associated_degree _ _ (E_gcd_tied t h hr) hn (X_ne_zero _),totalDegree_X]

theorem secondE_ne_zero (t : Parameters) (h : ValidE t) : secondE t≠0 := by
  rcases lt_trichotomy t.q (deltaE t) with hr | hr | hr
  · rw [secondE_strict_q t hr]; exact C14_ne_zero t h.1 h.2.1
  · have hs : secondE t=-(X t.a * endTieParenthesis t) := by
      rw [secondE_tied t hr]; unfold C14 C25E endTieParenthesis; ring
    rw [hs]
    apply neg_ne_zero.mpr
    apply mul_ne_zero (X_ne_zero _)
    intro hz
    exact endTie_coordinate_not_dvd t h (hz ▸ dvd_zero _)
  · rw [secondE_strict_delta t hr]; exact C25E_ne_zero t h

/-- Algebraic division by `B` followed by evaluation at one retains tied multiplicity. -/
noncomputable def middleSecondQuotient (t : Parameters) : Gluing.HomLambda :=
  (if t.q≤deltaM t then -(X t.a * X t.b) else 0) +
    (if deltaM t≤t.q then -(X t.x * X t.p) else 0)

theorem secondM_factor (t : Parameters) :
    secondM t=B t.u t.v t.tau * middleSecondQuotient t := by
  unfold secondM middleSecondQuotient C14 C25M
  split_ifs <;> ring

theorem middleSecondQuotient_eval_one (t : Parameters) :
    eval (fun _ : ℕ => (1 : ℚ)) (middleSecondQuotient t) =
      if t.q=deltaM t then -2 else -1 := by
  classical
  rcases lt_trichotomy t.q (deltaM t) with hr | hr | hr
  · simp [middleSecondQuotient,hr.le,not_le.mpr hr,ne_of_lt hr]
  · norm_num [middleSecondQuotient,hr]
  · simp [middleSecondQuotient,hr.le,not_le.mpr hr,ne_of_gt hr]

theorem secondM_ne_zero (t : Parameters) (h : ValidM t) : secondM t≠0 := by
  rw [secondM_factor]
  apply mul_ne_zero (B_irreducible _ _ _ h.1 h.2.1).ne_zero
  intro hz
  have hv := middleSecondQuotient_eval_one t
  rw [hz,map_zero] at hv
  split_ifs at hv <;> norm_num at hv

private theorem hom_pderiv_prod_zero {ι : Type*} (s : Finset ι)
    (f : ι → Gluing.HomLambda) (v : ℕ) (h : ∀ i∈s,pderiv v (f i)=0) :
    pderiv v (∏ i∈s,f i)=0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi,pderiv_mul,h i (Finset.mem_insert_self _ _),
      ih (fun j hj => h j (Finset.mem_insert_of_mem hj))]
    simp

private theorem hom_pderiv_det_zero {n : ℕ}
    (A : Matrix (Fin n) (Fin n) Gluing.HomLambda) (v : ℕ)
    (h : ∀ i j,pderiv v (A i j)=0) : pderiv v A.det=0 := by
  classical
  rw [AlgebraicCombinatorics.Det.det_eq_sum_sign_prod_textbook,map_sum]
  apply Finset.sum_eq_zero
  intro σ _
  have hp := hom_pderiv_prod_zero Finset.univ (fun i => A i (σ i)) v (fun i _ => h i (σ i))
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · simpa [hs] using hp
  · simpa [hs] using congrArg Neg.neg hp

private theorem hom_pderiv_private {n : ℕ}
    (A : Matrix (Fin (n+1)) (Fin (n+1)) Gluing.HomLambda)
    (v : ℕ) (r c : Fin (n+1)) (he : A r c=X v)
    (hp : ∀ i j,i≠r ∨ j≠c → pderiv v (A i j)=0) :
    pderiv v A.det=(-1)^(r.val+c.val)*(A.submatrix r.succAbove c.succAbove).det := by
  classical
  rw [Matrix.det_succ_row A r,map_sum]
  have hm (j : Fin (n+1)) : pderiv v (A.submatrix r.succAbove j.succAbove).det=0 := by
    apply hom_pderiv_det_zero
    intro a b
    exact hp _ _ (Or.inl (Fin.succAbove_ne r a))
  have hs (j : Fin (n+1)) : pderiv v ((-1 : Gluing.HomLambda)^(r.val+j.val))=0 := by
    have he : (-1 : Gluing.HomLambda)^(r.val+j.val)=C ((-1 : ℚ)^(r.val+j.val)) := by simp
    rw [he]
    exact pderiv_C
  rw [Finset.sum_eq_single c]
  · rw [pderiv_mul,pderiv_mul,hs,hm,he,pderiv_X_self]
    ring
  · intro j _ hj
    rw [pderiv_mul,pderiv_mul,hs,hm,hp r j (Or.inr hj)]
    ring
  · intro hh
    exact False.elim (hh (Finset.mem_univ c))

private theorem pderiv_hTilde_of_ne (v : ℕ) (k : ℤ) (h : k≠(v:ℤ)) :
    pderiv v (Gluing.hTilde k)=0 := by
  by_cases hk : k<0
  · simp [Gluing.hTilde,hk]
  · simp [Gluing.hTilde,hk,pderiv_X_of_ne (show k.toNat≠v by omega)]

private theorem eraseOne_hTilde_of_ne (v : ℕ) (k : ℤ) (h : k≠(v:ℤ)) :
    eraseOne v (Gluing.hTilde k)=Gluing.hTilde k := by
  by_cases hk : k<0
  · simp [Gluing.hTilde,hk]
  · simp [Gluing.hTilde,hk,show k.toNat≠v by omega]

private theorem top_index_pos (D : BetaDiagram 5) :
    0<D.row 0-D.col 4 := by
  have hr := D.row_strictAnti.antitone (show (0 : Fin 5)≤4 by decide)
  have hd := D.row_nonempty 4
  omega

/-- The top-right matrix site is the unique maximum, independently of repeated lower labels. -/
theorem top_index_unique (D : BetaDiagram 5) (i j : Fin 5)
    (h : i≠0 ∨ j≠4) : D.row i-D.col j<D.row 0-D.col 4 := by
  have hr := D.row_strictAnti.antitone (Fin.zero_le i)
  have hc := D.col_strictAnti.antitone (Fin.le_last j)
  rcases h with hi | hj
  · have hi' : (0 : Fin 5) < i := by
      have := i.isLt
      simp only [Fin.lt_def]
      omega
    have hs := D.row_strictAnti hi'
    change D.col 4≤D.col j at hc
    omega
  · have hj' : j < (4 : Fin 5) := by
      have := j.isLt
      simp only [Fin.lt_def]
      omega
    have hs := D.col_strictAnti hj'
    omega

private theorem hom_top_entry (D : BetaDiagram 5) :
    D.homMatrix 0 4=X (D.row 0-D.col 4).toNat := by
  change Gluing.hTilde (D.row 0-D.col 4)=X (D.row 0-D.col 4).toNat
  apply hTilde_eq_X_of_index
  have hpos := top_index_pos D
  omega

theorem hom_maximum_coefficient (D : BetaDiagram 5) :
    pderiv (D.row 0-D.col 4).toNat D.homSchur=homCofactor D 0 4 := by
  unfold BetaDiagram.homSchur homCofactor
  apply hom_pderiv_private
  · exact hom_top_entry D
  · intro i j hij
    apply pderiv_hTilde_of_ne
    have hlt := top_index_unique D i j hij
    have hpos := top_index_pos D
    omega

theorem hom_top_erasure (D : BetaDiagram 5) :
    eraseOne (D.row 0-D.col 4).toNat D.homSchur =
      (FiveOpening.zeroPosition D.homMatrix 0 4).det := by
  rw [BetaDiagram.homSchur,AlgHom.map_det]
  congr 1
  apply Matrix.ext
  intro i j
  simp only [AlgHom.mapMatrix_apply,Matrix.map_apply,FiveOpening.zeroPosition_apply]
  by_cases hij : i=0 ∧ j=4
  · rcases hij with ⟨rfl,rfl⟩
    simp only [eq_self_iff_true,true_and,ite_true]
    rw [hom_top_entry D,eraseOne_X]
    simp
  · rw [if_neg hij]
    change eraseOne (D.row 0-D.col 4).toNat (Gluing.hTilde (D.row i-D.col j)) =
      Gluing.hTilde (D.row i-D.col j)
    apply eraseOne_hTilde_of_ne
    have hlt := top_index_unique D i j (not_and_or.mp hij)
    have hpos := top_index_pos D
    omega

theorem hom_top_removal (D : BetaDiagram 5) :
    eraseOne (D.row 0-D.col 4).toNat D.homSchur =
      D.homSchur-X (D.row 0-D.col 4).toNat*homCofactor D 0 4 := by
  rw [hom_top_erasure]
  have hh := FiveOpening.det_zeroPosition D.homMatrix 0 4
  have he := hom_top_entry D
  rw [he] at hh
  change _=D.homMatrix.det-X (D.row 0-D.col 4).toNat*homCofactor D 0 4
  unfold homCofactor
  linear_combination -hh

theorem M_maximum_index (t : Parameters) (h : ValidM t) :
    (M t h).row 0-(M t h).col 4=(m t : ℤ) := by
  rcases h with ⟨hu,hv,hb,hx,hy,hc⟩
  have hh := M_index t ⟨hu,hv,hb,hx,hy,hc⟩ 0 4
  have hL : t.L+t.tau=t.u+t.v := by dsimp [Parameters.L]; omega
  simp [profileIndex,Fin.sum_univ_succ] at hh
  dsimp [m]
  omega

theorem E_maximum_index (t : Parameters) (h : ValidE t) :
    (E t h).row 0-(E t h).col 4=(m t : ℤ) := by
  rcases h with ⟨hu,hv,hb,hx,hy,hc⟩
  have hh := E_index t ⟨hu,hv,hb,hx,hy,hc⟩ 0 4
  have hL : t.L+t.tau=t.u+t.v := by dsimp [Parameters.L]; omega
  simp [profileIndex,Fin.sum_univ_succ] at hh
  dsimp [m]
  omega

theorem M_top_coefficient (t : Parameters) (h : ValidM t) :
    pderiv (m t) (M t h).homSchur=C15 t := by
  have hh := hom_maximum_coefficient (M t h)
  simpa [M_maximum_index t h,M_C15 t h] using hh

theorem E_top_coefficient (t : Parameters) (h : ValidE t) :
    pderiv (m t) (E t h).homSchur=C15 t := by
  have hh := hom_maximum_coefficient (E t h)
  simpa [E_maximum_index t h,E_C15 t h] using hh

theorem M_top_erasure (t : Parameters) (h : ValidM t) :
    eraseOne (m t) (M t h).homSchur=(M t h).homSchur-X (m t)*C15 t := by
  simpa [M_maximum_index t h,M_C15 t h] using hom_top_removal (M t h)

theorem E_top_erasure (t : Parameters) (h : ValidE t) :
    eraseOne (m t) (E t h).homSchur=(E t h).homSchur-X (m t)*C15 t := by
  simpa [E_maximum_index t h,E_C15 t h] using hom_top_removal (E t h)

private noncomputable def topZero (A : Matrix (Fin 5) (Fin 5) Gluing.HomLambda) :=
  FiveOpening.zeroPosition A 0 4
private noncomputable def twoZero (A : Matrix (Fin 5) (Fin 5) Gluing.HomLambda) :=
  FiveOpening.zeroPosition (topZero A) 0 3
private noncomputable def threeZero (A : Matrix (Fin 5) (Fin 5) Gluing.HomLambda) :=
  FiveOpening.zeroPosition (twoZero A) 1 4

private theorem topZero_minor_row_zero
    (A : Matrix (Fin 5) (Fin 5) Gluing.HomLambda) (j : Fin 5) :
    (topZero A).submatrix (0 : Fin 5).succAbove j.succAbove =
      A.submatrix (0 : Fin 5).succAbove j.succAbove := by
  apply Matrix.ext
  intro i k
  simp [topZero, Matrix.submatrix_apply, FiveOpening.zeroPosition_apply]

private theorem twoZero_minor25_det
    (A : Matrix (Fin 5) (Fin 5) Gluing.HomLambda)
    (h0 : A 4 0=0) (h1 : A 4 1=0) (h2 : A 4 2=0) :
    ((twoZero A).submatrix (1 : Fin 5).succAbove (4 : Fin 5).succAbove).det =
      (A.submatrix (1 : Fin 5).succAbove (4 : Fin 5).succAbove).det := by
  let f : Fin 4 → Fin 5 := (1 : Fin 5).succAbove
  let g : Fin 4 → Fin 5 := (4 : Fin 5).succAbove
  let R := (twoZero A).submatrix f g
  let Q := A.submatrix f g
  have hR0 : R 3 0=0 := by
    change twoZero A 4 0=0
    simp [twoZero,topZero,FiveOpening.zeroPosition_apply,h0]
  have hR1 : R 3 1=0 := by
    change twoZero A 4 1=0
    simp [twoZero,topZero,FiveOpening.zeroPosition_apply,h1]
  have hR2 : R 3 2=0 := by
    change twoZero A 4 2=0
    simp [twoZero,topZero,FiveOpening.zeroPosition_apply,h2]
  have hQ0 : Q 3 0=0 := by change A 4 0=0; exact h0
  have hQ1 : Q 3 1=0 := by change A 4 1=0; exact h1
  have hQ2 : Q 3 2=0 := by change A 4 2=0; exact h2
  change R.det=Q.det
  rw [det_four_last_row R hR0 hR1 hR2,det_four_last_row Q hQ0 hQ1 hQ2]
  have hcell : R 3 3=Q 3 3 := by
    change twoZero A 4 3=A 4 3
    simp [twoZero,topZero,FiveOpening.zeroPosition_apply]
  rw [hcell]
  apply congrArg (fun p : Gluing.HomLambda => Q 3 3*p)
  apply congrArg Matrix.det
  apply Matrix.ext
  intro i j
  have hn3 : g ((3 : Fin 4).succAbove j)≠(3 : Fin 5) := by
    fin_cases j <;> decide
  have hn4 : g ((3 : Fin 4).succAbove j)≠(4 : Fin 5) := by
    fin_cases j <;> decide
  change twoZero A (f ((3 : Fin 4).succAbove i)) (g ((3 : Fin 4).succAbove j)) =
    A (f ((3 : Fin 4).succAbove i)) (g ((3 : Fin 4).succAbove j))
  simp only [twoZero,topZero,FiveOpening.zeroPosition_apply]
  rw [if_neg (by intro hh; exact hn3 hh.2),if_neg (by intro hh; exact hn4 hh.2)]

private theorem second_derivative_identity
    (A : Matrix (Fin 5) (Fin 5) Gluing.HomLambda) (v : ℕ)
    (c14 c25 : Gluing.HomLambda)
    (h14 : (-1 : Gluing.HomLambda)^3*
      ((topZero A).submatrix (0 : Fin 5).succAbove (3 : Fin 5).succAbove).det=c14)
    (h25 : (-1 : Gluing.HomLambda)^5*
      ((twoZero A).submatrix (1 : Fin 5).succAbove (4 : Fin 5).succAbove).det=c25)
    (hz : ∀ i j,pderiv v (threeZero A i j)=0)
    (hc14 : pderiv v c14=0) (hc25 : pderiv v c25=0) :
    pderiv v (topZero A).det=pderiv v (A 0 3)*c14+pderiv v (A 1 4)*c25 := by
  have h₁ := FiveOpening.det_zeroPosition (topZero A) 0 3
  have h₂ := FiveOpening.det_zeroPosition (twoZero A) 1 4
  change (topZero A).det=(twoZero A).det+(topZero A) 0 3*
    ((-1)^3*((topZero A).submatrix (0 : Fin 5).succAbove (3 : Fin 5).succAbove).det) at h₁
  change (twoZero A).det=(threeZero A).det+(twoZero A) 1 4*
    ((-1)^5*((twoZero A).submatrix (1 : Fin 5).succAbove (4 : Fin 5).succAbove).det) at h₂
  rw [h14] at h₁
  rw [h25] at h₂
  rw [h₁,h₂,map_add,map_add,pderiv_mul,pderiv_mul,
    hom_pderiv_det_zero _ _ hz,hc14,hc25]
  simp [topZero,twoZero,FiveOpening.zeroPosition_apply,add_comm]

private theorem M_second_bounds (t : Parameters) (h : ValidM t) :
    t.x<NM t ∧ t.b<NM t ∧ t.a<NM t ∧ t.p<NM t ∧
    t.u<NM t ∧ t.v<NM t ∧ t.tau<NM t ∧ t.L<NM t := by
  rcases h with ⟨hu,hv,hb,hx,hy,hc⟩
  dsimp [NM,m,deltaM,Parameters.q,Parameters.L]
  omega

private theorem E_second_bounds (t : Parameters) (h : ValidE t) :
    t.b<NE t ∧ t.a<NE t ∧ t.p<NE t ∧ t.u<NE t ∧ t.v<NE t ∧
    t.tau<NE t ∧ t.L<NE t ∧ t.x<NE t ∧ t.x+t.v-t.tau<NE t := by
  rcases h with ⟨hu,hv,hb,hx,hy,hc⟩
  dsimp [NE,m,deltaE,Parameters.q,Parameters.L]
  omega

private theorem M_threeZero_derivative (t : Parameters) (h : ValidM t) :
    ∀ i j,pderiv (NM t) (threeZero (mMatrix t) i j)=0 := by
  classical
  rcases h with ⟨hu,hv,hb,hx,hy,hc⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [threeZero,twoZero,topZero,FiveOpening.zeroPosition_apply,mMatrix,
      pderiv_X,Pi.single_apply] <;>
    dsimp [NM,m,deltaM,Parameters.q,Parameters.L] at * <;> omega

private theorem E_threeZero_derivative (t : Parameters) (h : ValidE t) :
    ∀ i j,pderiv (NE t) (threeZero (eMatrix t) i j)=0 := by
  classical
  rcases h with ⟨hu,hv,hb,hx,hy,hc⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [threeZero,twoZero,topZero,FiveOpening.zeroPosition_apply,eMatrix,
      pderiv_X,Pi.single_apply] <;>
    dsimp [NE,m,deltaE,Parameters.q,Parameters.L] at * <;> omega

private theorem M_second_factor_derivatives (t : Parameters) (h : ValidM t) :
    pderiv (NM t) (C14 t)=0 ∧ pderiv (NM t) (C25M t)=0 := by
  classical
  rcases M_second_bounds t h with ⟨hx,hb,ha,hp,hu,hv,ht,hL⟩
  have hnL : t.u+t.v-t.tau≠NM t := by
    simpa only [Parameters.L] using ne_of_lt hL
  simp [C14,C25M,B,ne_of_lt hx,ne_of_lt hb,ne_of_lt ha,ne_of_lt hp,
    ne_of_lt hu,ne_of_lt hv,ne_of_lt ht,hnL]

private theorem E_second_factor_derivatives (t : Parameters) (h : ValidE t) :
    pderiv (NE t) (C14 t)=0 ∧ pderiv (NE t) (C25E t)=0 := by
  classical
  rcases E_second_bounds t h with ⟨hb,ha,hp,hu,hv,ht,hL,hx,hF⟩
  have hnL : t.u+t.v-t.tau≠NE t := by
    simpa only [Parameters.L] using ne_of_lt hL
  simp [C14,C25E,B,F,ne_of_lt hx,ne_of_lt hb,ne_of_lt ha,ne_of_lt hp,
    ne_of_lt hu,ne_of_lt hv,ne_of_lt ht,ne_of_lt hF,hnL]

theorem M_second_coefficient (t : Parameters) (h : ValidM t) :
    pderiv (NM t) (eraseOne (m t) (M t h).homSchur)=secondM t := by
  classical
  have he := hom_top_erasure (M t h)
  simp only [M_maximum_index t h,Int.toNat_natCast,M_homMatrix] at he
  rw [he]
  have h14 : (-1 : Gluing.HomLambda)^3*
      ((topZero (mMatrix t)).submatrix (0 : Fin 5).succAbove (3 : Fin 5).succAbove).det=C14 t := by
    rw [topZero_minor_row_zero]
    have hm := M_C14 t h
    change (-1 : Gluing.HomLambda)^3*
      ((M t h).homMatrix.submatrix (0 : Fin 5).succAbove (3 : Fin 5).succAbove).det=C14 t at hm
    rw [M_homMatrix t h] at hm
    exact hm
  have h25 : (-1 : Gluing.HomLambda)^5*
      ((twoZero (mMatrix t)).submatrix (1 : Fin 5).succAbove (4 : Fin 5).succAbove).det=C25M t := by
    rw [twoZero_minor25_det (mMatrix t) rfl rfl rfl]
    have hm := M_C25 t h
    change (-1 : Gluing.HomLambda)^5*
      ((M t h).homMatrix.submatrix (1 : Fin 5).succAbove (4 : Fin 5).succAbove).det=C25M t at hm
    rw [M_homMatrix t h] at hm
    exact hm
  change pderiv (NM t) (topZero (mMatrix t)).det=_
  rw [second_derivative_identity _ _ _ _ h14 h25 (M_threeZero_derivative t h)
    (M_second_factor_derivatives t h).1 (M_second_factor_derivatives t h).2]
  rcases h with ⟨hu,hv,hb,hx,hy,hc⟩
  have e03 : t.x+t.y+t.c-t.a-t.tau=NM t ↔ t.q≤deltaM t := by
    dsimp [NM,m,deltaM,Parameters.q]; omega
  have e14 : t.y+t.c+t.b-t.tau-t.p=NM t ↔ deltaM t≤t.q := by
    dsimp [NM,m,deltaM,Parameters.q]; omega
  simp [mMatrix,pderiv_X,Pi.single_apply,e03,e14,secondM]

theorem E_second_coefficient (t : Parameters) (h : ValidE t) :
    pderiv (NE t) (eraseOne (m t) (E t h).homSchur)=secondE t := by
  classical
  have he := hom_top_erasure (E t h)
  simp only [E_maximum_index t h,Int.toNat_natCast,E_homMatrix] at he
  rw [he]
  have h14 : (-1 : Gluing.HomLambda)^3*
      ((topZero (eMatrix t)).submatrix (0 : Fin 5).succAbove (3 : Fin 5).succAbove).det=C14 t := by
    rw [topZero_minor_row_zero]
    have hm := E_C14 t h
    change (-1 : Gluing.HomLambda)^3*
      ((E t h).homMatrix.submatrix (0 : Fin 5).succAbove (3 : Fin 5).succAbove).det=C14 t at hm
    rw [E_homMatrix t h] at hm
    exact hm
  have h25 : (-1 : Gluing.HomLambda)^5*
      ((twoZero (eMatrix t)).submatrix (1 : Fin 5).succAbove (4 : Fin 5).succAbove).det=C25E t := by
    rw [twoZero_minor25_det (eMatrix t) rfl rfl rfl]
    have hm := E_C25 t h
    change (-1 : Gluing.HomLambda)^5*
      ((E t h).homMatrix.submatrix (1 : Fin 5).succAbove (4 : Fin 5).succAbove).det=C25E t at hm
    rw [E_homMatrix t h] at hm
    exact hm
  change pderiv (NE t) (topZero (eMatrix t)).det=_
  rw [second_derivative_identity _ _ _ _ h14 h25 (E_threeZero_derivative t h)
    (E_second_factor_derivatives t h).1 (E_second_factor_derivatives t h).2]
  rcases h with ⟨hu,hv,hb,hx,hy,hc⟩
  have e03 : t.x+t.y+t.c-t.tau-t.a=NE t ↔ t.q≤deltaE t := by
    dsimp [NE,m,deltaE,Parameters.q]; omega
  have e14 : t.u+t.y+t.c+t.b-t.tau-t.a-t.p=NE t ↔ deltaE t≤t.q := by
    dsimp [NE,m,deltaE,Parameters.q]; omega
  simp [eMatrix,pderiv_X,Pi.single_apply,e03,e14,secondE]

/-- Full coefficient of a generator to the first power: differentiate, then erase that generator. -/
noncomputable def coefficientOne (j : ℕ) (p : Gluing.HomLambda) : Gluing.HomLambda :=
  eraseOne j (pderiv j p)

theorem M_second_coefficient_erasure (t : Parameters) (h : ValidM t) :
    eraseOne (NM t) (secondM t)=secondM t := by
  rcases M_second_bounds t h with ⟨hx,hb,ha,hp,hu,hv,ht,hL⟩
  unfold secondM
  split_ifs <;>
    simp [C14,C25M,B,show t.a≠NM t by omega,show t.b≠NM t by omega,
      show t.x≠NM t by omega,show t.p≠NM t by omega,show t.u≠NM t by omega,
      show t.v≠NM t by omega,show t.tau≠NM t by omega,
      show t.u+t.v-t.tau≠NM t by simpa [Parameters.L] using ne_of_lt hL]

theorem E_second_coefficient_erasure (t : Parameters) (h : ValidE t) :
    eraseOne (NE t) (secondE t)=secondE t := by
  rcases E_second_bounds t h with ⟨hb,ha,hp,hu,hv,ht,hL,hx,hF⟩
  unfold secondE
  split_ifs <;>
    simp [C14,C25E,B,F,Nat.add_comm,show t.a≠NE t by omega,show t.b≠NE t by omega,
      show t.x≠NE t by omega,show t.p≠NE t by omega,show t.u≠NE t by omega,
      show t.v≠NE t by omega,show t.tau≠NE t by omega,
      show t.u+t.v-t.tau≠NE t by simpa [Parameters.L] using ne_of_lt hL,
      show t.x+t.v-t.tau≠NE t by omega]

theorem M_marker (t : Parameters) (h : ValidM t) :
    coefficientOne (NM t) ((M t h).homSchur-X (m t)*C15 t)=secondM t := by
  rw [← M_top_erasure t h]
  unfold coefficientOne
  rw [M_second_coefficient t h,M_second_coefficient_erasure t h]

theorem E_marker (t : Parameters) (h : ValidE t) :
    coefficientOne (NE t) ((E t h).homSchur-X (m t)*C15 t)=secondE t := by
  rw [← E_top_erasure t h]
  unfold coefficientOne
  rw [E_second_coefficient t h,E_second_coefficient_erasure t h]

private theorem hom_not_mem_vars_sum {ι : Type*} (s : Finset ι)
    (f : ι → Gluing.HomLambda) (v : ℕ) (h : ∀ i∈s,v∉(f i).vars) :
    v∉(∑ i∈s,f i).vars := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    intro hv
    rcases Finset.mem_union.mp (vars_add_subset _ _ hv) with hv | hv
    · exact h i (Finset.mem_insert_self _ _) hv
    · exact ih (fun j hj => h j (Finset.mem_insert_of_mem hj)) hv

private theorem hom_not_mem_vars_prod {ι : Type*} (s : Finset ι)
    (f : ι → Gluing.HomLambda) (v : ℕ) (h : ∀ i∈s,v∉(f i).vars) :
    v∉(∏ i∈s,f i).vars := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi]
    intro hv
    rcases Finset.mem_union.mp (vars_mul _ _ hv) with hv | hv
    · exact h i (Finset.mem_insert_self _ _) hv
    · exact ih (fun j hj => h j (Finset.mem_insert_of_mem hj)) hv

private theorem hom_not_mem_vars_det {n : ℕ}
    (A : Matrix (Fin n) (Fin n) Gluing.HomLambda) (v : ℕ)
    (h : ∀ i j,v∉(A i j).vars) : v∉A.det.vars := by
  classical
  rw [AlgebraicCombinatorics.Det.det_eq_sum_sign_prod_textbook]
  apply hom_not_mem_vars_sum
  intro σ _
  have hp := hom_not_mem_vars_prod Finset.univ (fun i => A i (σ i)) v
    (fun i _ => h i (σ i))
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · simpa [hs] using hp
  · simpa [hs] using hp

private theorem hom_det_variables_le {n : ℕ}
    (A : Matrix (Fin n) (Fin n) Gluing.HomLambda) (bound : ℕ)
    (h : ∀ i j k,k∈(A i j).vars → k≤bound) :
    ∀ k,k∈A.det.vars → k≤bound := by
  intro k hk
  by_contra hn
  exact hom_not_mem_vars_det A k (fun i j hmem => hn (h i j k hmem)) hk

/-- The maximal marker is an occurring generator, not just the largest formal matrix index. -/
theorem M_largest_variable (t : Parameters) (h : ValidM t) :
    m t ∈ (M t h).homSchur.vars ∧ ∀ k, k ∈ (M t h).homSchur.vars → k ≤ m t := by
  classical
  refine ⟨?_,?_⟩
  · by_contra hn
    have hd := pderiv_eq_zero_of_notMem_vars hn
    rw [M_top_coefficient] at hd
    exact C15_ne_zero t h.1 h.2.1 hd
  · rw [BetaDiagram.homSchur,M_homMatrix]
    apply hom_det_variables_le
    intro i j k hk
    rcases h with ⟨hu,hv,hb,hx,hy,hc⟩
    fin_cases i <;> fin_cases j <;> simp [mMatrix] at hk <;>
      dsimp [m,Parameters.q,Parameters.L] at * <;> omega

theorem E_largest_variable (t : Parameters) (h : ValidE t) :
    m t ∈ (E t h).homSchur.vars ∧ ∀ k, k ∈ (E t h).homSchur.vars → k ≤ m t := by
  classical
  refine ⟨?_,?_⟩
  · by_contra hn
    have hd := pderiv_eq_zero_of_notMem_vars hn
    rw [E_top_coefficient] at hd
    exact C15_ne_zero t h.1 h.2.1 hd
  · rw [BetaDiagram.homSchur,E_homMatrix]
    apply hom_det_variables_le
    intro i j k hk
    rcases h with ⟨hu,hv,hb,hx,hy,hc⟩
    fin_cases i <;> fin_cases j <;> simp [eMatrix] at hk <;>
      dsimp [m,Parameters.q,Parameters.L] at * <;> omega

/-- Erasing the maximal generator leaves exactly the next occurring marker, including a tie. -/
theorem M_next_variable (t : Parameters) (h : ValidM t) :
    NM t∈(eraseOne (m t) (M t h).homSchur).vars ∧
      ∀ k,k∈(eraseOne (m t) (M t h).homSchur).vars → k≤NM t := by
  classical
  refine ⟨?_,?_⟩
  · by_contra hn
    have hd := pderiv_eq_zero_of_notMem_vars hn
    rw [M_second_coefficient] at hd
    exact secondM_ne_zero t h hd
  · have he := hom_top_erasure (M t h)
    simp only [M_maximum_index t h,Int.toNat_natCast,M_homMatrix] at he
    rw [he]
    apply hom_det_variables_le
    intro i j k hk
    rcases h with ⟨hu,hv,hb,hx,hy,hc⟩
    fin_cases i <;> fin_cases j <;>
      simp [FiveOpening.zeroPosition_apply,mMatrix] at hk <;>
      dsimp [NM,m,deltaM,Parameters.q,Parameters.L] at * <;> omega

theorem E_next_variable (t : Parameters) (h : ValidE t) :
    NE t∈(eraseOne (m t) (E t h).homSchur).vars ∧
      ∀ k,k∈(eraseOne (m t) (E t h).homSchur).vars → k≤NE t := by
  classical
  refine ⟨?_,?_⟩
  · by_contra hn
    have hd := pderiv_eq_zero_of_notMem_vars hn
    rw [E_second_coefficient] at hd
    exact secondE_ne_zero t h hd
  · have he := hom_top_erasure (E t h)
    simp only [E_maximum_index t h,Int.toNat_natCast,E_homMatrix] at he
    rw [he]
    apply hom_det_variables_le
    intro i j k hk
    rcases h with ⟨hu,hv,hb,hx,hy,hc⟩
    fin_cases i <;> fin_cases j <;>
      simp [FiveOpening.zeroPosition_apply,eMatrix] at hk <;>
      dsimp [NE,m,deltaE,Parameters.q,Parameters.L] at * <;> omega

private theorem no_second_pair
    (A : Matrix (Fin 5) (Fin 5) Gluing.HomLambda)
    (h4 : ∀ j,j≠3 → j≠4 → A 4 j=0)
    (σ : Equiv.Perm (Fin 5)) (hs : ∀ i,A i (σ i)≠0) :
    ¬ (σ 0=3 ∧ σ 1=4) := by
  rintro ⟨h03,h14⟩
  have h43 : σ 4≠3 := by
    intro hh
    have he := σ.injective (hh.trans h03.symm)
    norm_num at he
  have h44 : σ 4≠4 := by
    intro hh
    have he := σ.injective (hh.trans h14.symm)
    norm_num at he
  exact hs 4 (h4 (σ 4) h43 h44)

/-- The two second-marker positions cannot occur in one supported determinant term. -/
theorem M_no_second_pair (t : Parameters) (h : ValidM t)
    (σ : Equiv.Perm (Fin 5)) (hs : ∀ i,(M t h).homMatrix i (σ i)≠0) :
    ¬ (σ 0=3 ∧ σ 1=4) := by
  rw [M_homMatrix] at hs
  apply no_second_pair (mMatrix t) _ σ hs
  intro j h3 h4
  fin_cases j <;> simp_all [mMatrix]

theorem E_no_second_pair (t : Parameters) (h : ValidE t)
    (σ : Equiv.Perm (Fin 5)) (hs : ∀ i,(E t h).homMatrix i (σ i)≠0) :
    ¬ (σ 0=3 ∧ σ 1=4) := by
  rw [E_homMatrix] at hs
  apply no_second_pair (eMatrix t) _ σ hs
  intro j h3 h4
  fin_cases j <;> simp_all [eMatrix]

end SkewJacobiNegative.FiveNegative
