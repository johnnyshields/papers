/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.FiveNormalForms

/-!
# Prime obstruction for the five-negative opening

`lem:five-prime` of `shields-2026-skew-jacobi-negative.tex`, including
index-zero generators and all coincidences among the remaining labels.
The two erasures are followed by rational evaluations.  Giving a surviving
label `j` the value `j+1` separates the two surviving monomials without
requiring their labels to be distinct individually.
-/

namespace SkewJacobiNegative.FiveNegative

open MvPolynomial

/-- The two-term difference in the prime obstruction. -/
noncomputable def primeDifference (u v b p c : ℕ) : Gluing.HomLambda :=
  X u * T b p c - X v * T b p (c+u-v)

/-- Erase precisely two independent coordinates, retaining `H₀` in the same way. -/
noncomputable def eraseTwo (i j : ℕ) : Gluing.HomLambda →ₐ[ℚ] Gluing.HomLambda :=
  aeval fun k => if k=i ∨ k=j then 0 else X k

@[simp] theorem eraseTwo_X (i j k : ℕ) :
    eraseTwo i j (X k) = if k=i ∨ k=j then 0 else (X k : Gluing.HomLambda) := by
  simp [eraseTwo]

/-- A scalar test after the first two-coordinate erasure. -/
private def firstValue (u tau j : ℕ) : ℚ :=
  if j=u ∨ j=tau then 0 else (j:ℚ)+1

/-- A scalar test after the other two-coordinate erasure. -/
private def secondValue (v tau j : ℕ) : ℚ :=
  if j=v ∨ j=tau then 0 else 1

/-- Uniform prime obstruction, with no comparison between `b` and `c+u-v`. -/
theorem five_prime_obstruction (u v tau b p c : ℕ)
    (hu : v < u) (hv : tau < v) (hb : p < b) (hc : v+p < c) :
    ¬ B u v tau ∣ primeDifference u v b p c := by
  let d : ℕ := c+u-v
  let q : ℕ := b-p
  have hd : u+p < d := by dsimp [d]; omega
  have hdU : d ≠ u := by omega
  have hdTau : d ≠ tau := by omega
  have hdqU : d+q ≠ u := by omega
  have hdqTau : d+q ≠ tau := by omega
  have hvU : v ≠ u := by omega
  have hvTau : v ≠ tau := by omega
  have huTau : u ≠ tau := by omega
  let e₁ : Gluing.HomLambda →+* ℚ := eval (firstValue u tau)
  let e₂ : Gluing.HomLambda →+* ℚ := eval (secondValue v tau)
  have e₁B : e₁ (B u v tau) = 0 := by simp [e₁,B,firstValue]
  have e₂B : e₂ (B u v tau) = 0 := by simp [e₂,B,secondValue]
  intro hdiv
  have h₁ : e₁ (primeDifference u v b p c) = 0 := by
    have hh := map_dvd e₁ hdiv
    rw [e₁B] at hh
    exact zero_dvd_iff.mp hh
  have h₂ : e₂ (primeDifference u v b p c) = 0 := by
    have hh := map_dvd e₂ hdiv
    rw [e₂B] at hh
    exact zero_dvd_iff.mp hh
  have hfirst : e₁ (primeDifference u v b p c) =
      ((v:ℚ)+1) * (firstValue u tau p * ((d+q:ℕ):ℚ) + firstValue u tau p -
        firstValue u tau b * ((d:ℕ):ℚ) - firstValue u tau b) := by
    have eu : firstValue u tau u = 0 := by simp [firstValue]
    have ev : firstValue u tau v = (v : ℚ) + 1 := by
      simp only [firstValue,if_neg (show ¬ (v=u ∨ v=tau) by omega)]
    have ed : firstValue u tau d = (d : ℚ) + 1 := by
      simp only [firstValue,if_neg (show ¬ (d=u ∨ d=tau) by omega)]
    have edq : firstValue u tau (d+q) = ((d+q : ℕ) : ℚ) + 1 := by
      simp only [firstValue,if_neg (show ¬ (d+q=u ∨ d+q=tau) by omega)]
    simp only [e₁,primeDifference,T,map_sub,map_mul,eval_X,eu,ev,zero_mul,zero_sub]
    change -(((v : ℚ) + 1) * (firstValue u tau b * firstValue u tau d -
      firstValue u tau p * firstValue u tau (d+q))) = _
    rw [ed,edq]
    ring
  have hvpos : 0 < (v:ℚ)+1 := by positivity
  have hterms : firstValue u tau p * (((d+q:ℕ):ℚ)+1) =
      firstValue u tau b * (((d:ℕ):ℚ)+1) := by
    rw [hfirst] at h₁
    have ht := (mul_eq_zero.mp h₁).resolve_left (ne_of_gt hvpos)
    linear_combination ht
  have hboth : (p=u ∨ p=tau) ∧ (b=u ∨ b=tau) := by
    by_cases hp : p=u ∨ p=tau
    · refine ⟨hp,?_⟩
      by_contra hbn
      simp only [firstValue,if_pos hp,if_neg hbn,zero_mul] at hterms
      have hpB : 0 < (b:ℚ)+1 := by positivity
      have hpD : 0 < (d:ℚ)+1 := by positivity
      exact (ne_of_gt (mul_pos hpB hpD)) hterms.symm
    · by_cases hbn : b=u ∨ b=tau
      · simp only [firstValue,if_neg hp,if_pos hbn,zero_mul] at hterms
        have hpP : 0 < (p:ℚ)+1 := by positivity
        have hpD : 0 < ((d+q:ℕ):ℚ)+1 := by positivity
        exact False.elim ((ne_of_gt (mul_pos hpP hpD)) hterms)
      · simp only [firstValue,if_neg hp,if_neg hbn] at hterms
        have hqb : (b:ℚ) = (p:ℚ)+(q:ℚ) := by
          exact_mod_cast (show b=p+q by dsimp [q]; omega)
        have hqpos : 0 < (q:ℚ) := by
          exact_mod_cast (show 0<q by dsimp [q]; omega)
        have hdp : (p:ℚ) < (d:ℚ) := by exact_mod_cast (show p<d by omega)
        push_cast at hterms
        nlinarith [mul_pos hqpos (sub_pos.mpr hdp)]
  have hp : p=tau := by rcases hboth with ⟨hp,hbb⟩; rcases hp with hp | hp <;>
    rcases hbb with hbb | hbb <;> omega
  have hbu : b=u := by rcases hboth.2 with h | h <;> omega
  have hcV : c ≠ v := by omega
  have hcTau : c ≠ tau := by omega
  have hone : e₂ (primeDifference u v b p c) = 1 := by
    simp [e₂,primeDifference,T,secondValue,hp,hbu,huTau,Ne.symm hvU,hcV,hcTau]
  rw [hone] at h₂
  norm_num at h₂

/-- The displayed form, without the abbreviation for the polynomial difference. -/
theorem B_not_dvd_T_difference (u v tau b p c : ℕ)
    (hu : v < u) (hv : tau < v) (hb : p < b) (hc : v+p < c) :
    ¬ B u v tau ∣ (X u * T b p c - X v * T b p (c+u-v)) :=
  five_prime_obstruction u v tau b p c hu hv hb hc

end SkewJacobiNegative.FiveNegative
