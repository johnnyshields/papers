/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.StaircaseFiveFamilies
import SkewJacobiNegative.ContactQuadraticOperator
import SkewJacobiNegative.StaircaseCubicMatching
import SkewJacobiNegative.StaircaseFirstJets
import SkewJacobiNegative.EndpointLeaders
import SkewJacobiNegative.ConstantGapFiveClassification
import SkewJacobiNegative.StaircaseSafeCuts

/-!
# Exact five-row placement comparisons

The polynomial differences in `lem:staircase-seam-crossing`,
`lem:staircase-a2`, `lem:staircase-four-plus-one`, and
`lem:staircase-interior` of `shields-2026-skew-jacobi-negative.tex`.
Every identity uses the full sixteen-term interval expansion and permits
coincident numerical labels.  Ordered interior-tail recovery uses the actual
contact-blind operator, including support at the contact generator.
-/

namespace SkewJacobiNegative.StaircaseFivePlacements

open Gluing HessenbergExpansion StaircaseFiveFamilies
attribute [local simp] Polynomial.coeff_X Polynomial.coeff_one

/-- The two-row full interval polynomial. -/
def two {R : Type*} [CommRing R] (h : ℤ → R) (r a b : ℤ) : R :=
  h a * h b - h r * h (a+b-r)

/-- The exact end-to-interior defect after the first two seam matches. -/
theorem crossing_defect {R : Type*} [CommRing R] (h : ℤ → R) (q b c r : ℤ) :
    interval h q b c b (b+q-r) r r r q -
      interval h q b (b+q-r) c b r q r r =
    -h r * h q *
      (h (2*b+q-2*r) * two h r b c -
       h (b+c+q-2*r) * two h r b b +
       h (b+q-r) * (h b * h (b+c-r) - h c * h (2*b-r))) := by
  unfold interval two
  ring_nf <;> ring

/-- A2's exact defect before its remaining middle row is reconstructed. -/
theorem a2_defect {R : Type*} [CommRing R] (h : ℤ → R) (q b d z : ℤ) :
    interval h q b b d (b+q-z) z z q q -
      interval h q b d (b+q-z) b z q q z =
    -h z * h q *
      (-h (2*b+q-2*z) * two h q b d +
       h (b+d-z) * two h q b (b+q-z) +
       h (b+q-z) * (h d * h (2*b-z) - h (b+q-z) * h (b+d-q))) := by
  unfold interval two
  ring_nf <;> ring

/-- Endpoint cubic-lift difference, with both internal gap orientations retained. -/
def terminalPsi {R : Type*} [CommRing R] (h : ℤ → R)
    (q b c e r v : ℤ) : R :=
  h v * (h (b+c+q-r-v) * two h r b e -
    h (b+c-v) * two h q (b+q-r) e -
    h (b+c+e-r-v) * two h r q b)

theorem terminal_cubic_defect {R : Type*} [CommRing R] (h : ℤ → R)
    (q b c e r s t : ℤ) :
    interval h q b c (b+q-r) e r s t q -
      interval h q b c (b+q-r) e r t s q =
      h q * (terminalPsi h q b c e r s - terminalPsi h q b c e r t) := by
  unfold interval terminalPsi two
  ring_nf <;> ring

/-- The second minimum-gap layer for the interior seam word `(z,q,z,z)`. -/
def interiorLayer {R : Type*} [CommRing R] (h : ℤ → R)
    (a b c d e q z : ℤ) : R :=
  h e * two h q (a+b-z) (c+d-z) +
  h (d+e-z) * two h q (a+b-z) c +
  h a * two h q b (c+d+e-2*z)

/-- Complete minimum-gap grouping of the sixteen terms. -/
theorem interior_layers {R : Type*} [CommRing R] (h : ℤ → R)
    (a b c d e q z : ℤ) :
    interval h a b c d e z q z z =
      h a * h d * h e * two h q b c +
      h z *
        (-h (a+b-z) * h d * h e * h c -
         h a * h b * h (c+d-z) * h e -
         h a * h b * h c * h (d+e-z) +
         h q * h (a+b+c-z-q) * h d * h e +
         h a * h q * h (b+c+d-q-z) * h e +
         h a * h q * h (b+c-q) * h (d+e-z)) +
      h z ^ 2 * interiorLayer h a b c d e q z -
      h z ^ 3 * two h q (a+b-z) (c+d+e-2*z) := by
  unfold interval interiorLayer two
  ring_nf <;> ring

/-- The three candidate allocations in the ordered-top-pair branch have exact
second-layer differences; no distinctness of the remaining row is imposed. -/
theorem interior_t1_defect {R : Type*} [CommRing R] (h : ℤ → R)
    (p m t q z : ℤ) (hq : h q = 0) :
    interiorLayer h p m p m t q z - interiorLayer h m p m p t q z =
      h (p+m-z) * (h p * h (m+t-z) - h m * h (p+t-z)) := by
  unfold interiorLayer two
  simp only [hq, zero_mul, sub_zero]
  ring_nf <;> ring

/-- The sole surviving ordered allocation yields the exact commutation equation. -/
theorem interior_t2_defect {R : Type*} [CommRing R] (h : ℤ → R)
    (p m t q z : ℤ) :
    interiorLayer h p m p t m q z - interiorLayer h m p m t p q z =
      h q * (h (p+2*m-q-z) * h (p+t-z) -
        h (2*p+m-q-z) * h (m+t-z)) := by
  unfold interiorLayer two
  ring_nf <;> ring

/-- The swapped-top-pair branch ends with this untied full second-layer defect. -/
theorem interior_swapped_defect {R : Type*} [CommRing R] (h : ℤ → R)
    (b c d q z : ℤ) :
    interiorLayer h (d+q-z) b c d q q z -
      interiorLayer h (d+q-z) c b d q q z =
      h q * (h (b+d+q-2*z) * h (c+d-z) -
        h (b+d-z) * h (c+d+q-2*z)) := by
  unfold interiorLayer two
  ring_nf <;> ring

/-- The tail's two unit masses.  Repeated numerical positions are added. -/
noncomputable def tailMeasure (d e z : ℤ) : ℤ →₀ ℚ :=
  Finsupp.single e 1 + Finsupp.single (d+e-z) 1

private theorem quadratic_linear (μ : ℤ →₀ ℚ) (N : ℤ) :
    ContactQuadraticOperator.quadratic μ N =
      Finsupp.linearCombination ℚ (fun s : ℤ => complete s * complete (N-s)) μ := by
  classical
  simp only [ContactQuadraticOperator.quadratic, Finsupp.linearCombination_apply,
    Finsupp.sum, MvPolynomial.smul_eq_C_mul]

private theorem quadratic_add (μ ν : ℤ →₀ ℚ) (N : ℤ) :
    ContactQuadraticOperator.quadratic (μ+ν) N =
      ContactQuadraticOperator.quadratic μ N + ContactQuadraticOperator.quadratic ν N := by
  simp only [quadratic_linear, map_add]

private theorem quadratic_sub (μ ν : ℤ →₀ ℚ) (N : ℤ) :
    ContactQuadraticOperator.quadratic (μ-ν) N =
      ContactQuadraticOperator.quadratic μ N - ContactQuadraticOperator.quadratic ν N := by
  simp only [quadratic_linear, map_sub]

/-- The recovered tail layer is exactly the actual contact-blind operator. -/
theorem tail_layer_eq_operator (x c d e q z : ℤ) :
    complete e * two complete q x (c+d-z) +
      complete (d+e-z) * two complete q x c =
      ContactQuadraticOperator.contactOperator (tailMeasure d e z) x q (c+d+e-z) := by
  unfold ContactQuadraticOperator.contactOperator tailMeasure
  rw [quadratic_add, quadratic_add]
  simp only [ContactQuadraticOperator.quadratic_single, map_one, one_mul]
  unfold two
  ring_nf <;> ring

/-- Thickness supplies every strict support inequality, including a possible
support point equal to `q`. -/
theorem ordered_tail_reconstruction (x c d e D E q z : ℤ)
    (hq : 1 ≤ q) (hz : 1 ≤ z) (hx : q < x) (hc : q+z < c)
    (hd : 2*z < d) (he : z < e) (hD : 2*z < D) (hE : z < E)
    (htotal : d+e = D+E)
    (hlayer : complete e * two complete q x (c+d-z) +
        complete (d+e-z) * two complete q x c =
      complete E * two complete q x (c+D-z) +
        complete (D+E-z) * two complete q x c) : d = D ∧ e = E := by
  classical
  let μ := tailMeasure d e z - tailMeasure D E z
  have hsupport : ∀ s ∈ μ.support, 0 < s ∧ s < c+d+e-z-q := by
    intro s hs
    have hchoices : s = e ∨ s = d+e-z ∨ s = E ∨ s = D+E-z := by
      by_contra hn
      push_neg at hn
      have hzero : μ s = 0 := by
        simp only [μ, tailMeasure, Finsupp.sub_apply, Finsupp.add_apply]
        simp [Finsupp.single_apply, hn.1, hn.2.1, hn.2.2.1, hn.2.2.2,
          Ne.symm hn.1, Ne.symm hn.2.1, Ne.symm hn.2.2.1, Ne.symm hn.2.2.2]
      exact (Finsupp.mem_support_iff.mp hs) hzero
    rcases hchoices with rfl | rfl | rfl | rfl <;> constructor <;> omega
  have hOp : ContactQuadraticOperator.contactOperator μ x q (c+d+e-z) = 0 := by
    rw [tail_layer_eq_operator, tail_layer_eq_operator] at hlayer
    have hK : c+D+E-z = c+d+e-z := by omega
    rw [hK] at hlayer
    unfold ContactQuadraticOperator.contactOperator μ
    rw [quadratic_sub, quadratic_sub]
    unfold ContactQuadraticOperator.contactOperator at hlayer
    linear_combination hlayer
  have hμ := ContactQuadraticOperator.contact_blind_injective μ x q (c+d+e-z)
    hq hx (by omega) hsupport hOp
  have hmeas : tailMeasure d e z = tailMeasure D E z := sub_eq_zero.mp hμ
  have heE : e = E := by
    rcases lt_trichotomy e E with hlt | heq | hgt
    · have hval := congrArg (fun ν : ℤ →₀ ℚ => ν e) hmeas
      have hne1 : e ≠ d+e-z := by omega
      have hne2 : e ≠ E := by omega
      have hne3 : e ≠ D+E-z := by omega
      simp [tailMeasure, Finsupp.single_apply, hne1, hne2, hne3,
        Ne.symm hne1, Ne.symm hne2, Ne.symm hne3] at hval
    · exact heq
    · have hval := congrArg (fun ν : ℤ →₀ ℚ => ν E) hmeas
      have hne1 : E ≠ D+E-z := by omega
      have hne2 : E ≠ e := by omega
      have hne3 : E ≠ d+e-z := by omega
      simp [tailMeasure, Finsupp.single_apply, hne1, hne2, hne3,
        Ne.symm hne1, Ne.symm hne2, Ne.symm hne3] at hval
  exact ⟨by omega, heE⟩

/-- The three-generator skew endpoint commutator. -/
def endpointCommutator {R : Type*} [CommRing R] (h : ℤ → R)
    (a b q t u v : ℤ) : R :=
  h (a+t) * (h (u+q) * h v - h u * h (v+q)) -
  h a * (h (u+q+t) * h v - h u * h (v+q+t)) +
  h b * (h (u+q+t) * h (v+q) - h (u+q) * h (v+q+t))

/-- The entire tied-exterior endpoint difference, before any maximum is selected.
In particular the internal-span tie is not discarded. -/
theorem tied_endpoint_difference {R : Type*} [CommRing R] (h : ℤ → R)
    (a x y v b c d t : ℤ) :
    interval h (a+t) x y v a b c d b -
      interval h a x y v (a+t) b c d b =
      h b * (h y * endpointCommutator h a b (a-b) t x v -
        h c * endpointCommutator h a b (a-b) t (x+y-c) v -
        h d * endpointCommutator h a b (a-b) t x (y+v-d)) := by
  unfold interval endpointCommutator
  ring_nf <;> ring

/-- A genuine two-row determinant cannot vanish, including a zero gap. -/
theorem two_ne_zero (r a b : ℤ) (hr : 0 ≤ r) (ha : r < a) (hb : r < b) :
    two complete r a b ≠ 0 := by
  let v : ℕ+ := ⟨(a+b-r).toNat, by omega⟩
  have hv : (v.val : ℤ) = a+b-r := by dsimp [v]; omega
  have hd : MvPolynomial.pderiv v (two complete r a b) = -complete r := by
    simp only [two, map_sub, MvPolynomial.pderiv_mul,
      Staircase.residual_pderiv_complete, hv,
      if_neg (show a ≠ a+b-r by omega),
      if_neg (show b ≠ a+b-r by omega),
      if_neg (show r ≠ a+b-r by omega), if_pos rfl]
    simp only [ite_true,ite_false,mul_zero,zero_mul,mul_one,one_mul,sub_zero,zero_sub] <;> ring
  intro he
  have hh := congrArg (MvPolynomial.pderiv v) he
  rw [hd, map_zero, neg_eq_zero] at hh
  exact ((complete_ne_zero_iff r).mpr hr) hh

/-- Once the A2 cut matching has recovered the four fixed rows, the remaining
row is forced on the whole thick domain, without a parameter census. -/
theorem a2_remaining_row_iff (q b d z : ℤ)
    (hz : 1 ≤ z) (hq : z < q) (hb : q+z < b) (hd : 2*q < d) :
    interval complete q b b d (b+q-z) z z q q =
      interval complete q b d (b+q-z) b z q q z ↔ d = b+q-z := by
  constructor
  · intro he
    have he0 : interval complete q b b d (b+q-z) z z q q -
        interval complete q b d (b+q-z) b z q q z = 0 := sub_eq_zero.mpr he
    rcases lt_trichotomy d (b+q-z) with hlt | heq | hgt
    · let v : ℕ+ := ⟨(2*b+q-2*z).toNat, by omega⟩
      have hv : (v.val : ℤ) = 2*b+q-2*z := by dsimp [v]; omega
      have hderiv (k : ℤ) (hk : k < 2*b+q-2*z) :
          MvPolynomial.pderiv v (complete k) = 0 := by
        rw [Staircase.residual_pderiv_complete, if_neg (by omega)]
      have hself : MvPolynomial.pderiv v (complete (2*b+q-2*z)) = 1 := by
        rw [Staircase.residual_pderiv_complete, if_pos hv.symm]
      have hcoeff :
          MvPolynomial.pderiv v
            (interval complete q b b d (b+q-z) z z q q -
             interval complete q b d (b+q-z) b z q q z) =
            complete z * complete q * two complete q b d := by
        rw [a2_defect]
        simp only [two, map_sub, map_neg, map_add, MvPolynomial.pderiv_mul,
          hself, hderiv z (by omega), hderiv q (by omega),
          hderiv b (by omega), hderiv d (by omega),
          hderiv (b+d-z) (by omega), hderiv (b+q-z) (by omega),
          hderiv (b+d-q) (by omega), hderiv (2*b-z) (by omega),
          hderiv (b+(b+q-z)-q) (by omega)]
        ring
      have hzero := congrArg (MvPolynomial.pderiv v) he0
      rw [hcoeff, map_zero] at hzero
      exact False.elim ((mul_ne_zero
        (mul_ne_zero ((complete_ne_zero_iff z).mpr (by omega))
          ((complete_ne_zero_iff q).mpr (by omega)))
        (two_ne_zero q b d (by omega) (by omega) (by omega))) hzero)
    · exact heq
    · let v : ℕ+ := ⟨(b+d-z).toNat, by omega⟩
      have hv : (v.val : ℤ) = b+d-z := by dsimp [v]; omega
      have hderiv (k : ℤ) (hk : k < b+d-z) :
          MvPolynomial.pderiv v (complete k) = 0 := by
        rw [Staircase.residual_pderiv_complete, if_neg (by omega)]
      have hself : MvPolynomial.pderiv v (complete (b+d-z)) = 1 := by
        rw [Staircase.residual_pderiv_complete, if_pos hv.symm]
      have hcoeff :
          MvPolynomial.pderiv v
            (interval complete q b b d (b+q-z) z z q q -
             interval complete q b d (b+q-z) b z q q z) =
            -complete z * complete q * two complete q b (b+q-z) := by
        rw [a2_defect]
        simp only [two, map_sub, map_neg, map_add, MvPolynomial.pderiv_mul,
          hself, hderiv z (by omega), hderiv q (by omega),
          hderiv b (by omega), hderiv d (by omega),
          hderiv (2*b+q-2*z) (by omega), hderiv (b+q-z) (by omega),
          hderiv (b+d-q) (by omega), hderiv (2*b-z) (by omega),
          hderiv (b+(b+q-z)-q) (by omega)]
        ring
      have hzero := congrArg (MvPolynomial.pderiv v) he0
      rw [hcoeff, map_zero] at hzero
      exact False.elim ((mul_ne_zero
        (mul_ne_zero (neg_ne_zero.mpr ((complete_ne_zero_iff z).mpr (by omega)))
          ((complete_ne_zero_iff q).mpr (by omega)))
        (two_ne_zero q b (b+q-z) (by omega) (by omega) (by omega))) hzero)
  · intro heq
    subst d
    exact a2_identity complete q b z

/-- The last unreconstructed row in the end/interior branch is forced by a
private largest generator, including every contact among smaller labels. -/
theorem crossing_remaining_row_iff (q b c z : ℤ)
    (hz : 1 ≤ z) (hq : z < q) (hb : q+z < b) (hc : 2*z < c) :
    interval complete q b c b (b+q-z) z z z q =
      interval complete q b (b+q-z) c b z q z z ↔ c = b := by
  constructor
  · intro he
    have he0 : interval complete q b c b (b+q-z) z z z q -
        interval complete q b (b+q-z) c b z q z z = 0 := sub_eq_zero.mpr he
    rcases lt_trichotomy c b with hlt | heq | hgt
    · let v : ℕ+ := ⟨(2*b+q-2*z).toNat, by omega⟩
      have hv : (v.val : ℤ) = 2*b+q-2*z := by dsimp [v]; omega
      have hderiv (k : ℤ) (hk : k < 2*b+q-2*z) :
          MvPolynomial.pderiv v (complete k) = 0 := by
        rw [Staircase.residual_pderiv_complete, if_neg (by omega)]
      have hself : MvPolynomial.pderiv v (complete (2*b+q-2*z)) = 1 := by
        rw [Staircase.residual_pderiv_complete, if_pos hv.symm]
      have hcoeff :
          MvPolynomial.pderiv v
            (interval complete q b c b (b+q-z) z z z q -
             interval complete q b (b+q-z) c b z q z z) =
            -complete z * complete q * two complete z b c := by
        rw [crossing_defect]
        simp only [two, map_sub, map_neg, map_add, MvPolynomial.pderiv_mul,
          hself, hderiv z (by omega), hderiv q (by omega),
          hderiv b (by omega), hderiv c (by omega),
          hderiv (b+c+q-2*z) (by omega), hderiv (b+q-z) (by omega),
          hderiv (b+c-z) (by omega), hderiv (b+b-z) (by omega),
          hderiv (2*b-z) (by omega)]
        ring
      have hzero := congrArg (MvPolynomial.pderiv v) he0
      rw [hcoeff, map_zero] at hzero
      exact False.elim ((mul_ne_zero
        (mul_ne_zero (neg_ne_zero.mpr ((complete_ne_zero_iff z).mpr (by omega)))
          ((complete_ne_zero_iff q).mpr (by omega)))
        (two_ne_zero z b c (by omega) (by omega) (by omega))) hzero)
    · exact heq
    · let v : ℕ+ := ⟨(b+c+q-2*z).toNat, by omega⟩
      have hv : (v.val : ℤ) = b+c+q-2*z := by dsimp [v]; omega
      have hderiv (k : ℤ) (hk : k < b+c+q-2*z) :
          MvPolynomial.pderiv v (complete k) = 0 := by
        rw [Staircase.residual_pderiv_complete, if_neg (by omega)]
      have hself : MvPolynomial.pderiv v (complete (b+c+q-2*z)) = 1 := by
        rw [Staircase.residual_pderiv_complete, if_pos hv.symm]
      have hcoeff :
          MvPolynomial.pderiv v
            (interval complete q b c b (b+q-z) z z z q -
             interval complete q b (b+q-z) c b z q z z) =
            complete z * complete q * two complete z b b := by
        rw [crossing_defect]
        simp only [two, map_sub, map_neg, map_add, MvPolynomial.pderiv_mul,
          hself, hderiv z (by omega), hderiv q (by omega),
          hderiv b (by omega), hderiv c (by omega),
          hderiv (2*b+q-2*z) (by omega), hderiv (b+q-z) (by omega),
          hderiv (b+c-z) (by omega), hderiv (b+b-z) (by omega),
          hderiv (2*b-z) (by omega)]
        ring
      have hzero := congrArg (MvPolynomial.pderiv v) he0
      rw [hcoeff, map_zero] at hzero
      exact False.elim ((mul_ne_zero
        (mul_ne_zero ((complete_ne_zero_iff z).mpr (by omega))
          ((complete_ne_zero_iff q).mpr (by omega)))
        (two_ne_zero z b b (by omega) (by omega) (by omega))) hzero)
  · intro heq
    subst c
    exact a1_identity complete q b z

/-- Two near-concatenations give the complete adjacent-exchange difference. -/
theorem adjacent_exchange_defect {R : Type*} [CommRing R] (h : ℤ → R)
    (a b c d e r s t u : ℤ) :
    interval h a b c d e r s t u - interval h b a c d e r s t u =
      -h s * (h a * threeInterval h (b+c-s) d e t u -
        h b * threeInterval h (a+c-s) d e t u) := by
  unfold interval threeInterval
  ring_nf <;> ring

private theorem adjacent_exchange_ne_of_gt (a b c d e r s t u : ℤ)
    (hF : Domain a b c d e r s t u) (hH : Domain b a c d e r s t u)
    (hab : b < a) :
    interval complete a b c d e r s t u ≠
      interval complete b a c d e r s t u := by
  rcases hF with ⟨hr, hs, ht, hu, ha, hb, hc, hd, he⟩
  rcases hH with ⟨_, _, _, _, _, ha', _, _, _⟩
  let v : ℕ+ := ⟨(a+c+d+e-s-t-u).toNat, by omega⟩
  have hv : (v.val : ℤ) = a+c+d+e-s-t-u := by dsimp [v]; omega
  have hderiv (k : ℤ) (hk : k < a+c+d+e-s-t-u) :
      MvPolynomial.pderiv v (complete k) = 0 := by
    rw [Staircase.residual_pderiv_complete, if_neg (by omega)]
  have hself : MvPolynomial.pderiv v (complete ((a+c-s)+d+e-t-u)) = 1 := by
    rw [Staircase.residual_pderiv_complete, if_pos (by omega)]
  have hcoeff :
      MvPolynomial.pderiv v
        (interval complete a b c d e r s t u -
          interval complete b a c d e r s t u) =
      complete s * complete b * complete t * complete u := by
    rw [adjacent_exchange_defect]
    simp only [threeInterval, map_sub, map_neg, map_add, MvPolynomial.pderiv_mul,
      hself, hderiv s (by omega), hderiv a (by omega), hderiv b (by omega),
      hderiv t (by omega), hderiv u (by omega), hderiv d (by omega),
      hderiv e (by omega), hderiv (b+c-s) (by omega),
      hderiv (a+c-s) (by omega), hderiv ((b+c-s)+d-t) (by omega),
      hderiv ((a+c-s)+d-t) (by omega), hderiv (d+e-u) (by omega),
      hderiv ((b+c-s)+d+e-t-u) (by omega)]
    ring
  intro heq
  have hzero := congrArg (MvPolynomial.pderiv v) (sub_eq_zero.mpr heq)
  rw [hcoeff, map_zero] at hzero
  exact (mul_ne_zero
    (mul_ne_zero (mul_ne_zero ((complete_ne_zero_iff s).mpr hs)
      ((complete_ne_zero_iff b).mpr (by omega)))
      ((complete_ne_zero_iff t).mpr ht))
    ((complete_ne_zero_iff u).mpr hu)) hzero

/-- The five-row adjacent endpoint exchange is rigid on the entire actual
Hessenberg domain, including zero seams. -/
theorem adjacent_exchange_iff (a b c d e r s t u : ℤ)
    (hF : Domain a b c d e r s t u) (hH : Domain b a c d e r s t u) :
    interval complete a b c d e r s t u =
      interval complete b a c d e r s t u ↔ a = b := by
  constructor
  · intro heq
    rcases lt_trichotomy a b with hlt | he | hgt
    · exact False.elim (adjacent_exchange_ne_of_gt b a c d e r s t u hH hF hlt heq.symm)
    · exact he
    · exact False.elim (adjacent_exchange_ne_of_gt a b c d e r s t u hF hH hgt heq)
  · intro he
    subst b
    rfl

/-- Actual profile determinants, not formal interval surrogates, in A2's
remaining-row comparison. -/
theorem a2_profile_remaining_row_iff (q b d z : ℤ) (hz : 1 ≤ z) (hq : z < q)
    (hF : Domain q b b d (b+q-z) z z q q)
    (hH : Domain q b d (b+q-z) b z q q z) :
    (profile q b b d (b+q-z) z z q q hF).toBetaDiagram.schur =
      (profile q b d (b+q-z) b z q q z hH).toBetaDiagram.schur ↔
      d = b+q-z := by
  have hb : q+z < b := by rcases hF with ⟨_, _, _, _, _, _, hb, _, _⟩; omega
  have hd : 2*q < d := by rcases hF with ⟨_, _, _, _, _, _, _, hd, _⟩; omega
  rw [profile_schur, profile_schur]
  simpa only [interval, complete_eq_hh] using a2_remaining_row_iff q b d z hz hq hb hd

theorem crossing_profile_remaining_row_iff (q b c z : ℤ)
    (hz : 1 ≤ z) (hq : z < q)
    (hF : Domain q b c b (b+q-z) z z z q)
    (hH : Domain q b (b+q-z) c b z q z z) :
    (profile q b c b (b+q-z) z z z q hF).toBetaDiagram.schur =
      (profile q b (b+q-z) c b z q z z hH).toBetaDiagram.schur ↔ c = b := by
  have hb : q+z < b := by rcases hF with ⟨_, _, _, _, _, _, _, hb, _⟩; omega
  have hc : 2*z < c := by rcases hF with ⟨_, _, _, _, _, _, hc, _, _⟩; omega
  rw [profile_schur, profile_schur]
  simpa only [interval, complete_eq_hh] using crossing_remaining_row_iff q b c z hz hq hb hc

theorem adjacent_profile_exchange_iff (a b c d e r s t u : ℤ)
    (hF : Domain a b c d e r s t u) (hH : Domain b a c d e r s t u) :
    (profile a b c d e r s t u hF).toBetaDiagram.schur =
      (profile b a c d e r s t u hH).toBetaDiagram.schur ↔ a = b := by
  rw [profile_schur, profile_schur]
  simpa only [interval, complete_eq_hh] using adjacent_exchange_iff a b c d e r s t u hF hH

/-- The genuine consecutive tail, with its dimension fixed before taking
another cut or contraction. -/
def endpointTail {n : ℕ} (P : Profile (n+1)) : Profile n :=
  GeneralHessenberg.slice P 1 n (by omega)

private theorem endpointTail_row {n : ℕ} (P : Profile (n+1)) (i : Fin (n+1)) :
    (endpointTail P).r i = P.r i.succ := by
  change P.r ⟨1+i.val,_⟩ = P.r i.succ
  apply congrArg P.r
  apply Fin.ext
  simp only [Fin.val_succ]
  omega

private theorem endpointTail_gap {n : ℕ} (P : Profile (n+1)) (j : Fin n) :
    (endpointTail P).g j = P.g j.succ := by
  change P.g ⟨1+j.val,_⟩ = P.g j.succ
  apply congrArg P.g
  apply Fin.ext
  simp only [Fin.val_succ]
  omega

private theorem endpointTail_first_row {n : ℕ} (P : Profile (n+1)) :
    (endpointTail P).r 0 = P.r 1 := by
  rw [endpointTail_row]
  apply congrArg P.r
  apply Fin.ext
  simp

private theorem endpointTail_second_row {n : ℕ} (P : Profile (n+2)) :
    (endpointTail P).r 1 = P.r 2 := by
  rw [endpointTail_row]
  apply congrArg P.r
  apply Fin.ext
  simp

private theorem endpointTail_first_gap {n : ℕ} (P : Profile (n+2)) :
    (endpointTail P).g 0 = P.g 1 := by
  rw [endpointTail_gap]
  apply congrArg P.g
  apply Fin.ext
  simp

private theorem endpointTail_thick {n : ℕ} {P : Profile (n+1)}
    (hP : Staircase.Thick P) : Staircase.Thick (endpointTail P) :=
  GeneralHessenberg.slice_thick hP 1 n (by omega)

private theorem contract_zero_tail {n : ℕ} (P : Profile (n+1)) (j : Fin n) :
    (GeneralHessenberg.contract P 0).r j.succ = P.r j.succ.succ := by
  obtain ⟨hx,hz⟩ := GeneralHessenberg.contract_beta P 0
  have hr := (GeneralHessenberg.contract P 0).xi_sub_zeta j.succ
  rw [hx,hz] at hr
  dsimp only at hr
  have hi : (0 : Fin (n+1)).succ.succAbove j.succ = j.succ.succ := by
    apply Fin.ext
    simp [Fin.succAbove]
  have hj : (0 : Fin (n+1)).castSucc.succAbove j.succ = j.succ.succ := by
    apply Fin.ext
    simp [Fin.succAbove]
  rw [hi,hj,P.xi_sub_zeta] at hr
  exact_mod_cast hr.symm

private theorem contract_zero_gap {n : ℕ} (P : Profile (n+1)) (j : Fin n) :
    (GeneralHessenberg.contract P 0).g j = P.g j.succ := by
  rw [GeneralHessenberg.contract_gap]
  apply congrArg P.g
  apply Fin.ext
  simp [Fin.succAbove]

private theorem contract_zero_joined {n : ℕ} (P : Profile (n+1)) :
    ((GeneralHessenberg.contract P 0).r 0 : ℤ) = (P.r 0 : ℤ)+P.r 1-P.g 0 := by
  have h := GeneralHessenberg.contract_joined_row P 0
  have h0 : P.r (Fin.castSucc (0 : Fin (n+1))) = P.r 0 :=
    congrArg P.r (Fin.ext (by simp))
  have h1 : P.r (Fin.succ (0 : Fin (n+1))) = P.r 1 :=
    congrArg P.r (Fin.ext (by simp))
  rw [h0,h1] at h
  exact h

private theorem left_zero_schur {n : ℕ} (P : Profile (n+1)) :
    (GeneralHessenberg.leftOfSeam P 0).toBetaDiagram.schur = complete (P.r 0) := by
  have hr : (GeneralHessenberg.leftOfSeam P 0).r 0 = P.r 0 := rfl
  rw [Profile.toBetaDiagram_schur]
  exact (Profile.schur_single_interval (GeneralHessenberg.leftOfSeam P 0)).trans
    ((complete_eq_hh _).symm.trans (congrArg (fun k : ℕ => complete (k : ℤ)) hr))

private theorem join_zero {n : ℕ} (P : Profile (n+1)) (hP : Staircase.Thick P) :
    P.toBetaDiagram.schur = complete (P.r 0)*(endpointTail P).toBetaDiagram.schur-
      complete (P.g 0)*(GeneralHessenberg.contract P 0).toBetaDiagram.schur := by
  have h := GeneralHessenberg.schur_join_formula P hP 0
  rw [left_zero_schur] at h
  simpa only [endpointTail,GeneralHessenberg.rightOfSeam,Fin.val_zero,
    Nat.zero_add,Nat.sub_zero] using h

private theorem equal_tail_zeta {n : ℕ} (P Q : Profile n)
    (hr : ∀ j : Fin n, P.r j.succ = Q.r j.succ) (hg : P.g = Q.g) :
    P.zeta = Q.zeta := by
  funext i
  unfold Profile.zeta
  apply Finset.sum_congr rfl
  intro j _
  rw [hr j,hg]

/-- The two first endpoint rows are exchanged, and every remaining row and
every seam is literally unchanged. -/
def FirstTwoExchanged {n : ℕ} (P Q : Profile (n+2)) : Prop :=
  P.r 0 = Q.r 1 ∧ P.r 1 = Q.r 0 ∧
    (∀ i : Fin (n+1), P.r i.succ.succ = Q.r i.succ.succ) ∧ P.g = Q.g

private theorem first_contract_eq {n : ℕ} {P Q : Profile (n+2)}
    (h : FirstTwoExchanged P Q) :
    GeneralHessenberg.contract P 0 = GeneralHessenberg.contract Q 0 := by
  obtain ⟨h0,h1,ht,hg⟩ := h
  apply Profile.ext
  · funext i
    cases i using Fin.cases with
    | zero =>
      have hp := contract_zero_joined P
      have hq := contract_zero_joined Q
      have hg0 := congrFun hg 0
      exact_mod_cast (show ((GeneralHessenberg.contract P 0).r 0 : ℤ) =
        (GeneralHessenberg.contract Q 0).r 0 by omega)
    | succ j => rw [contract_zero_tail,contract_zero_tail,ht j]
  · funext j
    simp only [GeneralHessenberg.contract_gap,hg]

private theorem twice_tail_eq {n : ℕ} {P Q : Profile (n+2)}
    (h : FirstTwoExchanged P Q) : endpointTail (endpointTail P) = endpointTail (endpointTail Q) := by
  apply Profile.ext
  · funext i
    rw [endpointTail_row,endpointTail_row,endpointTail_row,endpointTail_row,h.2.2.1 i]
  · funext j
    simp only [endpointTail_gap,h.2.2.2]

private theorem tail_joined {n : ℕ} (P : Profile (n+2)) :
    ((GeneralHessenberg.contract (endpointTail P) 0).r 0 : ℤ) =
      (P.r 1 : ℤ)+P.r 2-P.g 1 := by
  have h := contract_zero_joined (endpointTail P)
  simpa only [endpointTail_first_row,endpointTail_second_row,endpointTail_first_gap] using h

/-- The all-order adjacent-exchange formula uses genuine contracted tails. -/
theorem adjacent_endpoint_defect {n : ℕ} (P Q : Profile (n+2))
    (hP : Staircase.Thick P) (hQ : Staircase.Thick Q) (h : FirstTwoExchanged P Q) :
    P.toBetaDiagram.schur-Q.toBetaDiagram.schur = -complete (P.g 1)*
      (complete (P.r 0)*(GeneralHessenberg.contract (endpointTail P) 0).toBetaDiagram.schur-
       complete (P.r 1)*(GeneralHessenberg.contract (endpointTail Q) 0).toBetaDiagram.schur) := by
  have hp := join_zero P hP
  have hq := join_zero Q hQ
  have htp := join_zero (endpointTail P) (endpointTail_thick hP)
  have htq := join_zero (endpointTail Q) (endpointTail_thick hQ)
  simp only [endpointTail_first_row,endpointTail_first_gap] at htp htq
  rw [first_contract_eq h] at hp
  rw [twice_tail_eq h] at htp
  have hg0 := congrFun h.2.2.2 0
  have hg1 := congrFun h.2.2.2 1
  rw [← h.2.1,← hg0] at hq
  rw [← h.1,← hg1] at htq
  rw [hp,hq,htp,htq]
  ring

private theorem adjacent_endpoint_ne_of_gt {n : ℕ} (P Q : Profile (n+2))
    (hP : Staircase.Thick P) (hQ : Staircase.Thick Q) (h : FirstTwoExchanged P Q)
    (hab : P.r 1 < P.r 0) : P.toBetaDiagram.schur ≠ Q.toBetaDiagram.schur := by
  have h0 := h.1
  have h1 := h.2.1
  have hg1 := congrFun h.2.2.2 1
  have ht2 : P.r 2 = Q.r 2 := by simpa using h.2.2.1 0
  let A := GeneralHessenberg.contract (endpointTail P) 0
  let B := GeneralHessenberg.contract (endpointTail Q) 0
  have hA : Staircase.Thick A := GeneralHessenberg.contract_thick (endpointTail_thick hP) 0
  have hB : Staircase.Thick B := GeneralHessenberg.contract_thick (endpointTail_thick hQ) 0
  have ht : ∀ j : Fin n, A.r j.succ = B.r j.succ := by
    intro j
    simpa only [A,B,contract_zero_tail,endpointTail_row] using h.2.2.1 j.succ
  have hg : A.g = B.g := by
    funext j
    simp only [A,B,contract_zero_gap,endpointTail_gap,h.2.2.2]
  have hABz := equal_tail_zeta A B ht hg
  have hAr : (A.r 0 : ℤ) = (P.r 1 : ℤ)+P.r 2-P.g 1 := tail_joined P
  have hBr : (B.r 0 : ℤ) = (P.r 0 : ℤ)+P.r 2-P.g 1 := by
    have hh : (B.r 0 : ℤ) = (Q.r 1 : ℤ)+Q.r 2-Q.g 1 := tail_joined Q
    omega
  have hfull : Staircase.fullIndex A < Staircase.fullIndex B := by
    have hz := congrFun hABz 0
    have hzA := A.zeta_last
    have hzB := B.zeta_last
    have hxA := A.xi_sub_zeta 0
    have hxB := B.xi_sub_zeta 0
    change A.xi 0-A.zeta (Fin.last n) < B.xi 0-B.zeta (Fin.last n)
    omega
  have hfullB : (B.r 0 : ℤ) ≤ Staircase.fullIndex B := by
    have hz := B.zeta_nonneg 0
    have hlast := B.zeta_last
    have hx := B.xi_sub_zeta 0
    change (B.r 0 : ℤ) ≤ B.xi 0-B.zeta (Fin.last n)
    omega
  have hp1 : P.g 1 < P.r 1 := P.g_lt_castSucc 1
  have hc2 : P.g 1 < P.r 2 := P.g_lt_succ 1
  let v := Staircase.fullGenerator B
  have hv : (v.val : ℤ) = Staircase.fullIndex B := by
    dsimp [v,Staircase.fullGenerator]
    have := B.toBetaDiagram.largestLabel_pos
    omega
  have hderiv (k : ℤ) (hk : k < Staircase.fullIndex B) :
      MvPolynomial.pderiv v (complete k) = 0 := by
    rw [Staircase.residual_pderiv_complete,if_neg (by omega)]
  have hAd : MvPolynomial.pderiv v A.toBetaDiagram.schur = 0 :=
    MvPolynomial.pderiv_eq_zero_of_notMem_vars
      (Staircase.not_mem_schur_above_full A v (by rw [hv]; exact hfull))
  have hBd : MvPolynomial.pderiv v B.toBetaDiagram.schur =
      (-1 : CompleteRing)^n*Staircase.gapMonomial B := by
    calc
      MvPolynomial.pderiv v B.toBetaDiagram.schur =
          B.toBetaDiagram.cornerCoefficient := B.toBetaDiagram.pderiv_schur_largest
      _ = (-1 : CompleteRing)^n*Staircase.gapMonomial B := by
        rw [BetaDiagram.cornerCoefficient,Staircase.cornerPolynomial_eq_gapMonomial hB]
  have hcoeff :
      MvPolynomial.pderiv v (P.toBetaDiagram.schur-Q.toBetaDiagram.schur) =
        complete (P.g 1)*complete (P.r 1)*
          ((-1 : CompleteRing)^n*Staircase.gapMonomial B) := by
    rw [adjacent_endpoint_defect P Q hP hQ h]
    change MvPolynomial.pderiv v
      (-complete (P.g 1)*(complete (P.r 0)*A.toBetaDiagram.schur-
        complete (P.r 1)*B.toBetaDiagram.schur)) = _
    simp only [map_sub,map_neg,MvPolynomial.pderiv_mul,hAd,hBd,
      hderiv (P.g 1) (by omega),hderiv (P.r 0) (by omega),hderiv (P.r 1) (by omega)]
    ring
  intro he
  have hzero := congrArg (MvPolynomial.pderiv v) (sub_eq_zero.mpr he)
  rw [hcoeff,map_zero] at hzero
  exact (mul_ne_zero
    (mul_ne_zero ((complete_ne_zero_iff _).mpr (by positivity))
      ((complete_ne_zero_iff _).mpr (by positivity)))
    (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      (Staircase.gapMonomial_ne_zero B))) hzero

/-- Adjacent endpoint exchange at every finite order of at least three rows.
The unchanged coordinate data are standing profile data, not certificates. -/
theorem adjacent_endpoint_exchange {n : ℕ} (P Q : Profile (n+2))
    (hP : Staircase.Thick P) (hQ : Staircase.Thick Q) (h : FirstTwoExchanged P Q)
    (he : P.toBetaDiagram.schur = Q.toBetaDiagram.schur) : P.r 0 = P.r 1 := by
  rcases lt_trichotomy (P.r 0) (P.r 1) with hlt | heq | hgt
  · have hrev : FirstTwoExchanged Q P :=
      ⟨h.2.1.symm, h.1.symm, fun i => (h.2.2.1 i).symm, h.2.2.2.symm⟩
    have hqgt : Q.r 1 < Q.r 0 := by rw [← h.1, ← h.2.1]; exact hlt
    exact False.elim (adjacent_endpoint_ne_of_gt Q P hQ hP hrev hqgt he.symm)
  · exact heq
  · exact False.elim (adjacent_endpoint_ne_of_gt P Q hP hQ h hgt he)

/-- Rotation reverses both words in the actual full interval polynomial. -/
theorem interval_reverse {R : Type*} [CommRing R] (h : ℤ → R)
    (a b c d e r s t u : ℤ) :
    interval h e d c b a u t s r = interval h a b c d e r s t u := by
  unfold interval
  ring_nf <;> ring

/-- The full derivative at the largest possible tied-exterior endpoint label.
The equality branch retains both contributions. -/
theorem tied_endpoint_derivative (a x y v b c d t : ℤ)
    (hDom : Domain a x y v a b c d b) (ht : 0 < t)
    (w : ℕ+) (hw : (w.val : ℤ) = max (x+y-c) (y+v-d)+a-b+t) :
    MvPolynomial.pderiv w
      (interval complete (a+t) x y v a b c d b -
       interval complete a x y v (a+t) b c d b) =
      if x+y-c < y+v-d then
        -complete b * complete d * two complete b a x
      else if y+v-d < x+y-c then
        complete b * complete c * two complete b a v
      else complete b *
        (complete c * two complete b a v - complete d * two complete b a x) := by
  rcases hDom with ⟨hb, hc, hd, _, ha, hx, hy, hv, _⟩
  rw [tied_endpoint_difference]
  simp only [endpointCommutator, two, map_add, map_sub, map_neg,
    MvPolynomial.pderiv_mul, Staircase.residual_pderiv_complete]
  rcases lt_trichotomy (x+y-c) (y+v-d) with hlt | heq | hgt
  · rw [max_eq_right hlt.le] at hw
    simp (disch := omega) only [if_pos, if_neg]
    ring
  · rw [heq, max_self] at hw
    simp (disch := omega) only [if_pos, if_neg]
    ring
  · rw [max_eq_left hgt.le] at hw
    simp (disch := omega) only [if_pos, if_neg]
    ring

/-- At the interior-span tie, a second private generator separates nonsymmetric
data.  Coincident same-sign monomials are not discarded. -/
theorem tied_endpoint_coefficient_ne_zero (a x y v b c d : ℤ)
    (hDom : Domain a x y v a b c d b) (htie : x+y-c = y+v-d)
    (hns : x ≠ v ∨ c ≠ d) :
    complete b * (complete c * two complete b a v -
      complete d * two complete b a x) ≠ 0 := by
  rcases hDom with ⟨hb, hc, hd, _, ha, hx, hy, hv, _⟩
  have hxv : x ≠ v := by intro he; apply hns.elim (fun h => h he) (fun h => h (by omega))
  let w : ℕ+ := ⟨(max x v+a-b).toNat, by have := le_max_left x v; omega⟩
  have hw : (w.val : ℤ) = max x v+a-b := by
    dsimp [w]
    have := le_max_left x v
    omega
  have hderiv :
      MvPolynomial.pderiv w
        (complete b * (complete c * two complete b a v -
          complete d * two complete b a x)) =
      if x < v then -complete b * complete c * complete b
      else complete b * complete d * complete b := by
    simp only [two, map_sub, map_neg, MvPolynomial.pderiv_mul,
      Staircase.residual_pderiv_complete]
    rcases lt_or_gt_of_ne hxv with hlt | hgt
    · rw [max_eq_right hlt.le] at hw
      simp (disch := omega) only [if_pos, if_neg]
      ring
    · rw [max_eq_left hgt.le] at hw
      simp (disch := omega) only [if_pos, if_neg]
      ring
  intro he
  have hzero := congrArg (MvPolynomial.pderiv w) he
  rw [hderiv, map_zero] at hzero
  split_ifs at hzero
  · exact (mul_ne_zero
      (mul_ne_zero (neg_ne_zero.mpr ((complete_ne_zero_iff b).mpr hb))
        ((complete_ne_zero_iff c).mpr hc))
      ((complete_ne_zero_iff b).mpr hb)) hzero
  · exact (mul_ne_zero
      (mul_ne_zero ((complete_ne_zero_iff b).mpr hb)
        ((complete_ne_zero_iff d).mpr hd))
      ((complete_ne_zero_iff b).mpr hb)) hzero

/-- The tied-exterior five-row endpoint comparison on every thick domain,
including units, contacts, and the interior-span tie. -/
theorem tied_endpoint_iff (a x y v b c d t : ℤ)
    (hDom : Domain a x y v a b c d b) (ht : 0 < t) :
    interval complete (a+t) x y v a b c d b =
      interval complete a x y v (a+t) b c d b ↔ x = v ∧ c = d := by
  constructor
  · intro he
    by_contra hns
    have hnon : x ≠ v ∨ c ≠ d := by tauto
    have hb := hDom.1
    have hc := hDom.2.1
    have hd := hDom.2.2.1
    have ha := hDom.2.2.2.2.1
    have hx := hDom.2.2.2.2.2.1
    have hy := hDom.2.2.2.2.2.2.1
    have hv := hDom.2.2.2.2.2.2.2.1
    let w : ℕ+ := ⟨(max (x+y-c) (y+v-d)+a-b+t).toNat, by
      have := le_max_left (x+y-c) (y+v-d); omega⟩
    have hw : (w.val : ℤ) = max (x+y-c) (y+v-d)+a-b+t := by
      dsimp [w]; have := le_max_left (x+y-c) (y+v-d); omega
    have hzero := congrArg (MvPolynomial.pderiv w) (sub_eq_zero.mpr he)
    rw [tied_endpoint_derivative a x y v b c d t hDom ht w hw, map_zero] at hzero
    rcases lt_trichotomy (x+y-c) (y+v-d) with hlt | heq | hgt
    · rw [if_pos hlt] at hzero
      exact (mul_ne_zero
        (mul_ne_zero (neg_ne_zero.mpr ((complete_ne_zero_iff b).mpr hb))
          ((complete_ne_zero_iff d).mpr hd))
        (two_ne_zero b a x hb ha (by omega))) hzero
    · rw [if_neg (by omega), if_neg (by omega)] at hzero
      exact tied_endpoint_coefficient_ne_zero a x y v b c d hDom heq hnon hzero
    · rw [if_neg (by omega), if_pos hgt] at hzero
      exact (mul_ne_zero
        (mul_ne_zero ((complete_ne_zero_iff b).mpr hb)
          ((complete_ne_zero_iff c).mpr hc))
        (two_ne_zero b a v hb ha (by omega))) hzero
  · rintro ⟨rfl, rfl⟩
    exact interval_reverse complete a x y x (a+t) b c c b

/-- The intrinsic thick profile supplies the complete nine-parameter domain. -/
theorem domain_of_profile (P : Profile 4) (hP : Staircase.Thick P) :
    Domain (P.r 0) (P.r 1) (P.r 2) (P.r 3) (P.r 4)
      (P.g 0) (P.g 1) (P.g 2) (P.g 3) := by
  have ha := P.g_lt_castSucc 0
  have he := P.g_lt_succ 3
  have hb := hP 0 1 (by rfl)
  have hc := hP 1 2 (by rfl)
  have hd := hP 2 3 (by rfl)
  norm_num at ha he hb hc hd
  refine ⟨by positivity, by positivity, by positivity, by positivity,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast ha
  · exact_mod_cast hb
  · exact_mod_cast hc
  · exact_mod_cast hd
  · exact_mod_cast he

private theorem normalized_profile_row {n : ℕ} (D : BetaDiagram (n+1))
    (hD : D.Connected) (i : Fin (n+1)) :
    ((D.toProfile hD).r i : ℤ) = D.row i-D.col i := by
  have h := (D.toProfile hD).xi_sub_zeta i
  rw [D.toProfile_xi hD,D.toProfile_zeta hD] at h
  dsimp only at h
  omega

private theorem normalized_profile_gap {n : ℕ} (D : BetaDiagram (n+1))
    (hD : D.Connected) (j : Fin n) :
    ((D.toProfile hD).g j : ℤ) = D.row j.succ-D.col j.castSucc := by
  have h := (D.toProfile hD).xi_succ_sub_zeta_castSucc j
  rw [D.toProfile_xi hD,D.toProfile_zeta hD] at h
  dsimp only at h
  omega

/-- Endpoint extension is evaluated on the full actual beta matrix. -/
theorem profile_endpoint_intervals (P : Profile 4) (hP : P.Hessenberg)
    (t : ℤ) (ht : 0 < t) :
    (P.toBetaDiagram.extendTop t ht).schur =
      interval complete ((P.r 0 : ℤ)+t) (P.r 1) (P.r 2) (P.r 3) (P.r 4)
        (P.g 0) (P.g 1) (P.g 2) (P.g 3) ∧
    (P.toBetaDiagram.extendBottom t ht).schur =
      interval complete (P.r 0) (P.r 1) (P.r 2) (P.r 3) ((P.r 4 : ℤ)+t)
        (P.g 0) (P.g 1) (P.g 2) (P.g 3) := by
  let D := P.toBetaDiagram
  let A := D.extendTop t ht
  let B := D.extendBottom t ht
  have hD : D.Connected := Profile.toBetaDiagram_connected P
  let hA : A.Connected := D.extendTop_connected hD t ht
  let hB : B.Connected := D.extendBottom_connected hD t ht
  let T := A.toProfile hA
  let U := B.toProfile hB
  have hTr (i : Fin 5) :
      (T.r i : ℤ) = (P.r i : ℤ)+(if i = 0 then t else 0) := by
    rw [normalized_profile_row]
    have hp := P.xi_sub_zeta i
    by_cases hi : i = 0
    · subst i
      simp only [A,D,BetaDiagram.extendTop,Profile.toBetaDiagram,ite_true]
      omega
    · simp only [A,D,BetaDiagram.extendTop,Profile.toBetaDiagram,if_neg hi]
      omega
  have hTg (j : Fin 4) : (T.g j : ℤ) = P.g j := by
    rw [normalized_profile_gap]
    simpa only [A,D,BetaDiagram.extendTop,Profile.toBetaDiagram,
      if_neg (Fin.succ_ne_zero j)] using P.xi_succ_sub_zeta_castSucc j
  have hUr (i : Fin 5) :
      (U.r i : ℤ) = (P.r i : ℤ)+(if i = Fin.last 4 then t else 0) := by
    rw [normalized_profile_row]
    have hp := P.xi_sub_zeta i
    by_cases hi : i = Fin.last 4
    · subst i
      simp only [B,D,BetaDiagram.extendBottom,Profile.toBetaDiagram,ite_true]
      omega
    · simp only [B,D,BetaDiagram.extendBottom,Profile.toBetaDiagram,if_neg hi]
      omega
  have hUg (j : Fin 4) : (U.g j : ℤ) = P.g j := by
    rw [normalized_profile_gap]
    simpa only [B,D,BetaDiagram.extendBottom,Profile.toBetaDiagram,
      if_neg (Fin.castSucc_ne_last j)] using P.xi_succ_sub_zeta_castSucc j
  have hTH : T.Hessenberg := by
    intro i j hij
    have hi : i ≠ 0 := by intro hi; subst i; simp at hij
    have hp := hP i j hij
    dsimp only [T]
    rw [A.toProfile_xi hA,A.toProfile_zeta hA]
    simp only [A,D,BetaDiagram.extendTop,Profile.toBetaDiagram,if_neg hi]
    omega
  have hUH : U.Hessenberg := by
    intro i j hij
    have hj : j ≠ Fin.last 4 := by
      intro hj
      subst j
      simp only [Fin.val_last] at hij
      have := i.isLt
      omega
    have hp := hP i j hij
    dsimp only [U]
    rw [B.toProfile_xi hB,B.toProfile_zeta hB]
    simp only [B,D,BetaDiagram.extendBottom,Profile.toBetaDiagram,if_neg hj]
    omega
  constructor
  · change A.schur = _
    rw [← A.toProfile_schur hA,schur_interval T hTH]
    simp [interval,← complete_eq_hh,hTr,hTg]
  · change B.schur = _
    rw [← B.toProfile_schur hB,schur_interval U hUH]
    simp [interval,← complete_eq_hh,hUr,hUg]

private theorem five_rows_eq_of_cast (P Q : Profile 4)
    (h0 : (P.r 0 : ℤ) = Q.r 0) (h1 : (P.r 1 : ℤ) = Q.r 1)
    (h2 : (P.r 2 : ℤ) = Q.r 2) (h3 : (P.r 3 : ℤ) = Q.r 3)
    (h4 : (P.r 4 : ℤ) = Q.r 4) : P.r = Q.r := by
  funext i
  fin_cases i
  · exact_mod_cast h0
  · exact_mod_cast h1
  · exact_mod_cast h2
  · exact_mod_cast h3
  · exact_mod_cast h4

-- TODO-COPIED: skew-jacobi-negative/lean/SkewJacobiNegative/FiveOpeningComparisons.lean
private theorem five_row_multiset (P : Profile 4) :
    P.rowMultiset = {P.r 0,P.r 1,P.r 2,P.r 3,P.r 4} := by
  have hv : (Finset.univ : Finset (Fin 5)).val = {0,1,2,3,4} := by decide
  rw [Profile.rowMultiset,hv]
  simp

/-- Opposite endpoint extensions can be equal only when the endpoint rows
already have the same length.  This is the actual row multiset reading. -/
theorem profile_endpoint_rows_eq (P : Profile 4) (hP : Staircase.Thick P)
    (t : ℤ) (ht : 0 < t)
    (he : (P.toBetaDiagram.extendTop t ht).schur =
      (P.toBetaDiagram.extendBottom t ht).schur) : P.r 0 = P.r 4 := by
  have hdom := domain_of_profile P hP
  have htop : Domain ((P.r 0 : ℤ)+t) (P.r 1) (P.r 2) (P.r 3) (P.r 4)
      (P.g 0) (P.g 1) (P.g 2) (P.g 3) := by
    rcases hdom with ⟨hr, hs, hu, hv, ha, hb, hc, hd, he⟩
    exact ⟨hr, hs, hu, hv, by omega, hb, hc, hd, he⟩
  have hbottom : Domain (P.r 0) (P.r 1) (P.r 2) (P.r 3) ((P.r 4 : ℤ)+t)
      (P.g 0) (P.g 1) (P.g 2) (P.g 3) := by
    rcases hdom with ⟨hr, hs, hu, hv, ha, hb, hc, hd, he⟩
    exact ⟨hr, hs, hu, hv, ha, hb, hc, hd, by omega⟩
  let T := profile ((P.r 0 : ℤ)+t) (P.r 1) (P.r 2) (P.r 3) (P.r 4)
    (P.g 0) (P.g 1) (P.g 2) (P.g 3) htop
  let B := profile (P.r 0) (P.r 1) (P.r 2) (P.r 3) ((P.r 4 : ℤ)+t)
    (P.g 0) (P.g 1) (P.g 2) (P.g 3) hbottom
  have hinterval := profile_endpoint_intervals P hP.hessenberg t ht
  rw [hinterval.1, hinterval.2] at he
  have hprof : T.schur = B.schur := by
    rw [← Profile.toBetaDiagram_schur, ← Profile.toBetaDiagram_schur]
    simp only [T, B, profile_schur]
    simpa only [interval, complete_eq_hh] using he
  have hrows := (Profile.rows_eq_of_schur_eq hprof).2
  rw [five_row_multiset, five_row_multiset] at hrows
  have hsum := congrArg (fun M : Multiset ℕ => (M.map (fun x => (x : ℤ)^2)).sum) hrows
  simp [Multiset.map_cons,Multiset.map_zero,Multiset.sum_cons,
    Multiset.sum_zero,T,B,profile_row] at hsum
  have hprod : t*((P.r 0 : ℤ)-P.r 4) = 0 := by nlinarith [hsum]
  have heq := (mul_eq_zero.mp hprod).resolve_left (ne_of_gt ht)
  exact_mod_cast (sub_eq_zero.mp heq)

private theorem profile_topMargin (P : Profile 4) :
    P.toBetaDiagram.topMargin = (P.r 0 : ℤ)-P.g 0 := by
  have hr := P.xi_sub_zeta 0
  have hg := P.xi_succ_sub_zeta_castSucc 0
  norm_num at hg
  change P.xi 0-P.xi 1 = _
  omega

private theorem profile_bottomMargin (P : Profile 4) :
    P.toBetaDiagram.bottomMargin = (P.r 4 : ℤ)-P.g 3 := by
  have hz := P.zeta_castSucc 3
  norm_num at hz
  change P.zeta 3-P.zeta 4 = _
  omega

/-- The five-row endpoint isolation theorem for an actual zero-free thick
profile, proved by the full endpoint coefficient and the tied-exterior table. -/
theorem five_endpoint_rotate (P : Profile 4) (hP : Staircase.Thick P)
    (hg : ∀ j, 0 < P.g j) (t : ℤ) (ht : 0 < t)
    (he : (P.toBetaDiagram.extendTop t ht).schur =
      (P.toBetaDiagram.extendBottom t ht).schur) : P = P.rotate := by
  have hends := profile_endpoint_rows_eq P hP t ht he
  have hcorner : P.toBetaDiagram.PositiveCorner := by
    intro j
    change P.zeta j.castSucc < P.xi j.succ
    have hj := P.xi_succ_sub_zeta_castSucc j
    have hp := hg j
    omega
  have hzero : P.toBetaDiagram.endpointDifference t ht = 0 := sub_eq_zero.mpr he
  have hcoeff : P.toBetaDiagram.endpointCoefficient = 0 := by
    have hd := P.toBetaDiagram.endpointDifference_pderiv t ht
    rw [hzero, map_zero] at hd
    exact hd.symm
  have hmargin : P.toBetaDiagram.topMargin = P.toBetaDiagram.bottomMargin := by
    by_contra hn
    exact P.toBetaDiagram.endpointCoefficient_ne_zero_untied hcorner hn hcoeff
  rw [profile_topMargin, profile_bottomMargin] at hmargin
  have hgap : P.g 0 = P.g 3 := by omega
  have hinterval := profile_endpoint_intervals P hP.hessenberg t ht
  rw [hinterval.1, hinterval.2, ← hends, ← hgap] at he
  have hdom : Domain (P.r 0) (P.r 1) (P.r 2) (P.r 3) (P.r 0)
      (P.g 0) (P.g 1) (P.g 2) (P.g 0) := by
    simpa only [← hends, ← hgap] using domain_of_profile P hP
  have hmiddle := (tied_endpoint_iff (P.r 0) (P.r 1) (P.r 2) (P.r 3)
    (P.g 0) (P.g 1) (P.g 2) t hdom ht).mp he
  have hr : P.r 1 = P.r 3 := by exact_mod_cast hmiddle.1
  have hgg : P.g 1 = P.g 2 := by exact_mod_cast hmiddle.2
  apply Profile.ext
  · funext i
    fin_cases i <;> simp [Profile.rotate, Fin.rev, hends, hr]
  · funext j
    fin_cases j <;> simp [Profile.rotate, Fin.rev, hgap, hgg]

/-- Common beta normalization commutes with both actual endpoint polynomials. -/
theorem normalized_endpoint_polynomials {n : ℕ} (D : BetaDiagram (n+1))
    (hD : D.Connected) (t : ℤ) (ht : 0 < t) :
    ((D.toProfile hD).toBetaDiagram.extendTop t ht).schur =
      (D.extendTop t ht).schur ∧
    ((D.toProfile hD).toBetaDiagram.extendBottom t ht).schur =
      (D.extendBottom t ht).schur := by
  constructor
  all_goals apply congrArg Matrix.det
  all_goals apply Matrix.ext
  all_goals intro i j
  · simp only [BetaDiagram.matrix, BetaDiagram.extendTop, Profile.toBetaDiagram,
      D.toProfile_xi hD, D.toProfile_zeta hD, Matrix.of_apply]
    split_ifs <;> apply congrArg complete <;> ring
  · simp only [BetaDiagram.matrix, BetaDiagram.extendBottom, Profile.toBetaDiagram,
      D.toProfile_xi hD, D.toProfile_zeta hD, Matrix.of_apply]
    split_ifs <;> apply congrArg complete <;> ring

/-- A symmetric normalized profile gives symmetry of the original full board,
with the common beta translation restored. -/
theorem symmetric_of_profile_rotate {n : ℕ} (D : BetaDiagram (n+1))
    (hD : D.Connected) (hrot : D.toProfile hD = (D.toProfile hD).rotate) :
    D.Symmetric := by
  let P := D.toProfile hD
  refine ⟨P.xi 0+2*D.col (Fin.last n), ?_, ?_⟩
  · intro i
    have he := congrArg (fun R : Profile n => R.xi i) hrot
    rw [Profile.xi_rotate, D.toProfile_xi hD, D.toProfile_zeta hD] at he
    have h0 := congrFun (D.toProfile_xi hD) 0
    change P.xi 0 = _ at h0
    dsimp only at he h0
    omega
  · intro i
    have he := congrArg (fun R : Profile n => R.zeta i) hrot
    rw [Profile.zeta_rotate, D.toProfile_xi hD, D.toProfile_zeta hD] at he
    have h0 := congrFun (D.toProfile_xi hD) 0
    change P.xi 0 = _ at h0
    dsimp only at he h0
    omega

/-- Gamma doubles the actual top extension length without changing row count. -/
theorem gamma_top_extension_polynomial {n : ℕ} (D : BetaDiagram (n+1))
    (t : ℤ) (ht : 0 < t) :
    (D.extendTop t ht).gamma.schur =
      (D.gamma.extendTop (2*t) (by omega)).schur := by
  apply congrArg Matrix.det
  apply Matrix.ext
  intro i j
  simp only [BetaDiagram.matrix, BetaDiagram.extendTop, BetaDiagram.gamma,
    Matrix.of_apply]
  split_ifs <;> apply congrArg complete <;> ring

/-- The same covariance holds at the bottom endpoint, including original units. -/
theorem gamma_bottom_extension_polynomial {n : ℕ} (D : BetaDiagram (n+1))
    (t : ℤ) (ht : 0 < t) :
    (D.extendBottom t ht).gamma.schur =
      (D.gamma.extendBottom (2*t) (by omega)).schur := by
  apply congrArg Matrix.det
  apply Matrix.ext
  intro i j
  simp only [BetaDiagram.matrix, BetaDiagram.extendBottom, BetaDiagram.gamma,
    Matrix.of_apply]
  split_ifs <;> apply congrArg complete <;> ring

private theorem gap_word_ext (g : Fin 4 → ℕ) (a b c d : ℕ) :
    g = ![a,b,c,d] ↔ g 0 = a ∧ g 1 = b ∧ g 2 = c ∧ g 3 = d := by
  constructor
  · rintro rfl
    exact ⟨rfl,rfl,rfl,rfl⟩
  · rintro ⟨h0,h1,h2,h3⟩
    funext j
    fin_cases j <;> simp [h0,h1,h2,h3]

/-- Minimum multiplicity is read from the actual unordered gap multiset. -/
theorem minimumMultiplicity_eq_count (P : Profile 4) (z : ℕ+) :
    Staircase.minimumMultiplicity P z = P.gapMultiset.count z.val := by
  rw [Profile.gapMultiset,Multiset.count_map]
  change (∑ j : Fin 4, if P.g j = z.val then 1 else 0) =
    (Finset.univ.filter (fun j : Fin 4 => z.val = P.g j)).card
  rw [Finset.card_eq_sum_ones,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : P.g j = z.val
  · simp [hj]
  · simp [hj,Ne.symm hj]

/-- Equality preserves the minimum multiplicity without recovering an ordered
gap word or assuming separation. -/
theorem minimumMultiplicity_eq_of_schur_eq (P Q : Profile 4) (z : ℕ+)
    (he : P.schur = Q.schur) :
    Staircase.minimumMultiplicity P z = Staircase.minimumMultiplicity Q z := by
  rw [minimumMultiplicity_eq_count, minimumMultiplicity_eq_count,
    Profile.gaps_eq_of_schur_eq he]

/-- The exact four-word inventory with three occurrences of the minimum. -/
theorem three_minimum_gap_words (P : Profile 4) (z : ℕ+)
    (hmin : ∀ j, z.val ≤ P.g j) (hm : Staircase.minimumMultiplicity P z = 3) :
    ∃ q : ℕ, z.val < q ∧
      (P.g = ![q,z.val,z.val,z.val] ∨ P.g = ![z.val,q,z.val,z.val] ∨
       P.g = ![z.val,z.val,q,z.val] ∨ P.g = ![z.val,z.val,z.val,q]) := by
  have h0 := hmin 0; have h1 := hmin 1
  have h2 := hmin 2; have h3 := hmin 3
  refine ⟨P.g 0+P.g 1+P.g 2+P.g 3-3*z.val,?_⟩
  simp only [gap_word_ext]
  simp only [Staircase.minimumMultiplicity,Fin.sum_univ_four] at hm
  split_ifs at hm <;> omega

/-- Two minima have exactly six positional words, which are the four
rotation-normalized placements P, Q, R, S and the reversals of P and Q.
The two upper gaps may coincide. -/
theorem two_minimum_gap_words (P : Profile 4) (z : ℕ+)
    (hmin : ∀ j, z.val ≤ P.g j) (hm : Staircase.minimumMultiplicity P z = 2) :
    ∃ r q : ℕ, z.val < r ∧ z.val < q ∧
      (P.g = ![z.val,z.val,r,q] ∨ P.g = ![z.val,r,z.val,q] ∨
       P.g = ![z.val,r,q,z.val] ∨ P.g = ![r,z.val,z.val,q] ∨
       P.g = ![q,z.val,r,z.val] ∨ P.g = ![q,r,z.val,z.val]) := by
  have h0 := hmin 0; have h1 := hmin 1
  have h2 := hmin 2; have h3 := hmin 3
  simp only [gap_word_ext]
  simp only [Staircase.minimumMultiplicity,Fin.sum_univ_four] at hm
  split_ifs at hm
  all_goals first
    | (exfalso; omega)
    | exact ⟨P.g 2,P.g 3,by omega,by omega,by omega⟩
    | exact ⟨P.g 1,P.g 3,by omega,by omega,by omega⟩
    | exact ⟨P.g 1,P.g 2,by omega,by omega,by omega⟩
    | exact ⟨P.g 0,P.g 3,by omega,by omega,by omega⟩
    | exact ⟨P.g 2,P.g 0,by omega,by omega,by omega⟩
    | exact ⟨P.g 1,P.g 0,by omega,by omega,by omega⟩

/-- Four minima force a literal constant gap word, not just an unordered
four-part multiset with an unproved orientation. -/
theorem four_minimum_gap_word (P : Profile 4) (z : ℕ+)
    (hm : Staircase.minimumMultiplicity P z = 4) : ∀ j, P.g j = z.val := by
  have h : P.g 0 = z.val ∧ P.g 1 = z.val ∧ P.g 2 = z.val ∧ P.g 3 = z.val := by
    simp only [Staircase.minimumMultiplicity,Fin.sum_univ_four] at hm
    split_ifs at hm <;> omega
  intro j
  fin_cases j <;> simp [h.1,h.2.1,h.2.2.1,h.2.2.2]

/-- The four-minimum branch uses the completed actual constant-gap producer.
The mate's constant gap word is derived from full Schur equality. -/
theorem four_minima_full_class (P Q : Profile 4)
    (hP : Staircase.Thick P) (hQ : Staircase.Thick Q) (z : ℕ+)
    (hm : Staircase.minimumMultiplicity P z = 4) :
    P.schur = Q.schur ↔ ConstantGapFiveClassification.ClassifiedAt z.val P Q :=
  ConstantGapFiveClassification.constant_gap_full_class P Q hP hQ z.val z.pos
    (four_minimum_gap_word P z hm)

/-- The B family's same-direction top extension difference. -/
noncomputable def bTopDefect (p m z w t : ℤ) : CompleteRing :=
  interval complete (p+t) m p (p+m-w) m z w z z -
    interval complete (p+t) (p+m-w) m p m z z w z

/-- Its bottom extension difference. -/
noncomputable def bBottomDefect (p m z w t : ℤ) : CompleteRing :=
  interval complete p m p (p+m-w) (m+t) z w z z -
    interval complete p (p+m-w) m p (m+t) z z w z

/-- Complete top-extension coefficient, after cancellation of all shared
larger intervals; zero gaps are retained as actual units. -/
theorem b_top_coefficient (p m z w t : ℤ)
    (hz : 0 ≤ z) (hw : 0 ≤ w) (hp : z+w < p) (hm : z+w < m) (ht : 0 < t)
    (v : ℕ+) (hv : (v.val : ℤ) = 2*p+2*m-2*z-w+t) :
    MvPolynomial.pderiv v (bTopDefect p m z w t) =
      -(complete z ^ 2) * two complete z p m := by
  unfold bTopDefect interval two
  ring_nf
  simp (disch := omega) [map_add, map_neg, MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_pow, Staircase.residual_pderiv_complete, hv, if_pos, if_neg]
  <;> ring

theorem b_bottom_coefficient (p m z w t : ℤ)
    (hz : 0 ≤ z) (hw : 0 ≤ w) (hp : z+w < p) (hm : z+w < m) (ht : 0 < t)
    (v : ℕ+) (hv : (v.val : ℤ) = 2*p+2*m-2*z-w+t) :
    MvPolynomial.pderiv v (bBottomDefect p m z w t) =
      complete z ^ 2 * two complete z p m := by
  unfold bBottomDefect interval two
  ring_nf
  simp (disch := omega) [map_add, map_neg, MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_pow, Staircase.residual_pderiv_complete, hv, if_pos, if_neg]
  <;> ring

/-- Every positive same-direction extension separates the two B orbits. -/
theorem b_directional_defects_ne_zero (p m z w t : ℤ)
    (hz : 0 ≤ z) (hw : 0 ≤ w) (hp : z+w < p) (hm : z+w < m) (ht : 0 < t) :
    bTopDefect p m z w t ≠ 0 ∧ bBottomDefect p m z w t ≠ 0 := by
  let v : ℕ+ := ⟨(2*p+2*m-2*z-w+t).toNat, by omega⟩
  have hv : (v.val : ℤ) = 2*p+2*m-2*z-w+t := by dsimp [v]; omega
  have hbin := two_ne_zero z p m hz (by omega) (by omega)
  have hz0 := (complete_ne_zero_iff z).mpr hz
  constructor
  · intro he
    have hd := congrArg (MvPolynomial.pderiv v) he
    rw [b_top_coefficient p m z w t hz hw hp hm ht v hv, map_zero] at hd
    exact (mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 hz0)) hbin) hd
  · intro he
    have hd := congrArg (MvPolynomial.pderiv v) he
    rw [b_bottom_coefficient p m z w t hz hw hp hm ht v hv, map_zero] at hd
    exact (mul_ne_zero (pow_ne_zero 2 hz0) hbin) hd

private theorem shifted_pair_ne_zero (p m t : ℤ)
    (hp : 0 < p) (hm : 0 < m) (ht : 0 < t) (hne : p ≠ m) :
    complete (p+t)*complete m-complete p*complete (m+t) ≠ 0 := by
  let v : ℕ+ := ⟨(max p m+t).toNat, by have := le_max_left p m; omega⟩
  have hv : (v.val : ℤ) = max p m+t := by dsimp [v]; have := le_max_left p m; omega
  have hd :
      MvPolynomial.pderiv v
        (complete (p+t)*complete m-complete p*complete (m+t)) =
      if p < m then -complete p else complete m := by
    simp only [map_sub, MvPolynomial.pderiv_mul, Staircase.residual_pderiv_complete]
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · rw [max_eq_right hlt.le] at hv
      simp (disch := omega) only [if_pos, if_neg]
      <;> ring
    · rw [max_eq_left hgt.le] at hv
      simp (disch := omega) only [if_pos, if_neg]
      <;> ring
  intro he
  have hzero := congrArg (MvPolynomial.pderiv v) he
  rw [hd, map_zero] at hzero
  split_ifs at hzero
  · exact (neg_ne_zero.mpr ((complete_ne_zero_iff p).mpr hp.le)) hzero
  · exact ((complete_ne_zero_iff m).mpr hm.le) hzero

/-- All three regimes of the tied-border B coefficient.  At the transition
both contributions are collected before differentiation. -/
theorem b_tied_coefficient (p m z w t : ℤ)
    (hz : 0 ≤ z) (hw : 0 ≤ w) (hp : z+w < p) (hm : z+w < m)
    (ht : 0 < t) (hne : p ≠ m)
    (v : ℕ+) (hv : (v.val : ℤ) =
      max (2*p+2*m-2*z-w) (2*p+2*m-2*z-w+t-(min p m-z))) :
    MvPolynomial.pderiv v (bTopDefect p m z w t+bBottomDefect p m z w t) =
      if t < min p m-z then
        complete z ^ 2 * (complete (p+t)*complete m-complete p*complete (m+t))
      else if min p m-z < t then
        (if m < p then complete m*complete z*two complete z p m
         else -complete p*complete z*two complete z p m)
      else
        (if m < p then complete p*complete z*two complete z m m
         else -complete m*complete z*two complete z p p) := by
  unfold bTopDefect bBottomDefect interval two
  ring_nf
  rcases lt_or_gt_of_ne hne with hpm | hmp
  · rw [min_eq_left hpm.le] at hv ⊢
    rcases lt_trichotomy t (p-z) with hlt | heq | hgt
    · rw [max_eq_left (by omega)] at hv
      simp (disch := omega) [map_add, map_neg, MvPolynomial.pderiv_mul,
        MvPolynomial.pderiv_pow, Staircase.residual_pderiv_complete, hv, if_pos, if_neg]
      <;> ring
    · rw [max_eq_left (by omega)] at hv
      simp (disch := omega) [map_add, map_neg, MvPolynomial.pderiv_mul,
        MvPolynomial.pderiv_pow, Staircase.residual_pderiv_complete, hv, if_pos, if_neg]
      simp only [show p+t = 2*p-z by omega,show t+m = p+m-z by omega,
        show p*2-z = 2*p-z by ring]
      <;> ring
    · rw [max_eq_right (by omega)] at hv
      simp (disch := omega) [map_add, map_neg, MvPolynomial.pderiv_mul,
        MvPolynomial.pderiv_pow, Staircase.residual_pderiv_complete, hv, if_pos, if_neg]
      <;> ring
  · rw [min_eq_right hmp.le] at hv ⊢
    rcases lt_trichotomy t (m-z) with hlt | heq | hgt
    · rw [max_eq_left (by omega)] at hv
      simp (disch := omega) [map_add, map_neg, MvPolynomial.pderiv_mul,
        MvPolynomial.pderiv_pow, Staircase.residual_pderiv_complete, hv, if_pos, if_neg]
      <;> ring
    · rw [max_eq_left (by omega)] at hv
      simp (disch := omega) [map_add, map_neg, MvPolynomial.pderiv_mul,
        MvPolynomial.pderiv_pow, Staircase.residual_pderiv_complete, hv, if_pos, if_neg]
      simp only [show p+t = p+m-z by omega,show t+m = 2*m-z by omega,
        show m*2-z = 2*m-z by ring]
      <;> ring
    · rw [max_eq_right (by omega)] at hv
      simp (disch := omega) [map_add, map_neg, MvPolynomial.pderiv_mul,
        MvPolynomial.pderiv_pow, Staircase.residual_pderiv_complete, hv, if_pos, if_neg]
      <;> ring

/-- The B tied-border obstruction is nonzero throughout the full parameter
domain, including zero gaps and the largest-index transition. -/
theorem b_tied_defect_ne_zero (p m z w t : ℤ)
    (hz : 0 ≤ z) (hw : 0 ≤ w) (hp : z+w < p) (hm : z+w < m)
    (ht : 0 < t) (hne : p ≠ m) :
    bTopDefect p m z w t+bBottomDefect p m z w t ≠ 0 := by
  let L : ℤ := max (2*p+2*m-2*z-w) (2*p+2*m-2*z-w+t-(min p m-z))
  have hL : 0 < L := by
    have hbase : 0 < 2*p+2*m-2*z-w := by omega
    exact lt_of_lt_of_le hbase (le_max_left _ _)
  let v : ℕ+ := ⟨L.toNat,by omega⟩
  have hv : (v.val : ℤ) = L := by dsimp [v]; omega
  have hz0 := (complete_ne_zero_iff z).mpr hz
  have hp0 := (complete_ne_zero_iff p).mpr (by omega)
  have hm0 := (complete_ne_zero_iff m).mpr (by omega)
  have hbin := two_ne_zero z p m hz (by omega) (by omega)
  have hpp := two_ne_zero z p p hz (by omega) (by omega)
  have hmm := two_ne_zero z m m hz (by omega) (by omega)
  intro he
  have hzero := congrArg (MvPolynomial.pderiv v) he
  rw [b_tied_coefficient p m z w t hz hw hp hm ht hne v hv, map_zero] at hzero
  split_ifs at hzero
  · exact (mul_ne_zero (pow_ne_zero 2 hz0)
      (shifted_pair_ne_zero p m t (by omega) (by omega) ht hne)) hzero
  · exact (mul_ne_zero (mul_ne_zero hm0 hz0) hbin) hzero
  · exact (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hp0) hz0) hbin) hzero
  · exact (mul_ne_zero (mul_ne_zero hp0 hz0) hmm) hzero
  · exact (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hm0) hz0) hpp) hzero

/-- A tied positive border has precisely two sites at its second marker.
The corner is strictly above it and every old core entry is strictly below it. -/
theorem tied_border_index_iff {n : ℕ} (D : BetaDiagram (n+1))
    (q : ℤ) (hq : 0 < q) (i j : Fin (n+2)) :
    (D.positiveBorder q q hq hq).row i -
        (D.positiveBorder q q hq hq).col j = D.largestLabel+q ↔
      (i = 0 ∧ j = (Fin.last n).castSucc) ∨
      (i = (0 : Fin (n+1)).succ ∧ j = Fin.last (n+1)) := by
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.lastCases with
    | last =>
      simp only [BetaDiagram.positiveBorder, Fin.cons_zero, Fin.snoc_last,
        BetaDiagram.largestLabel, Fin.ext_iff, Fin.val_zero, Fin.val_last,
        Fin.val_castSucc, Fin.val_succ]
      omega
    | cast j =>
      have he : (D.row 0+q-D.col j = D.row 0-D.col (Fin.last n)+q) ↔
          j = Fin.last n := by
        constructor
        · intro hj
          apply D.col_strictAnti.injective
          omega
        · rintro rfl; ring
      simpa [BetaDiagram.positiveBorder,BetaDiagram.largestLabel,
        Ne.symm (Fin.succ_ne_zero (0 : Fin (n+1)))] using he
  | succ i =>
    cases j using Fin.lastCases with
    | last =>
      have he : (D.row i-(D.col (Fin.last n)-q) =
          D.row 0-D.col (Fin.last n)+q) ↔ i = 0 := by
        constructor
        · intro hi
          apply D.row_strictAnti.injective
          omega
        · rintro rfl; ring
      simpa only [BetaDiagram.positiveBorder, Fin.cons_succ, Fin.snoc_last,
        BetaDiagram.largestLabel, Fin.succ_ne_zero, false_and,
        Fin.succ_inj, and_true, false_or] using he
    | cast j =>
      have hr := D.row_strictAnti.antitone (Fin.zero_le i)
      have hc := D.col_strictAnti.antitone (Fin.le_last j)
      have hn : D.row i-D.col j ≠ D.largestLabel+q := by
        dsimp [BetaDiagram.largestLabel]
        omega
      simpa only [BetaDiagram.positiveBorder, Fin.cons_succ, Fin.snoc_castSucc,
        Fin.succ_ne_zero, false_and, Fin.castSucc_ne_last,
        and_false, or_self, iff_false] using hn

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem det_six_two_site_derivative
    (M : Matrix (Fin 6) (Fin 6) CompleteRing) (v : ℕ+)
    (hM : ∀ i j, MvPolynomial.pderiv v (M i j) =
      if (i = 0 ∧ j = 4) ∨ (i = 1 ∧ j = 5) then 1 else 0) :
    MvPolynomial.pderiv v M.det =
      (M.submatrix (0 : Fin 6).succAbove (4 : Fin 6).succAbove).det +
      (M.submatrix (1 : Fin 6).succAbove (5 : Fin 6).succAbove).det := by
  norm_num [Matrix.det_succ_row_zero, Matrix.det_unique, Matrix.submatrix_apply,
    Fin.sum_univ_succ, Fin.succAbove]
  simp only [map_add, map_sub, map_neg, MvPolynomial.pderiv_mul, hM]
  norm_num
  ring

/-- First differentiation of an actual tied six-row border is the sum of the
two full endpoint extensions, without erasing a contact generator. -/
theorem tied_five_border_derivative (D : BetaDiagram 5)
    (q : ℤ) (hq : 0 < q) (v : ℕ+) (hv : (v.val : ℤ) = D.largestLabel+q) :
    MvPolynomial.pderiv v (D.positiveBorder q q hq hq).schur =
      (D.extendBottom q hq).schur + (D.extendTop q hq).schur := by
  let P := D.positiveBorder q q hq hq
  have hM (i j : Fin 6) :
      MvPolynomial.pderiv v (P.matrix i j) =
        if (i = 0 ∧ j = 4) ∨ (i = 1 ∧ j = 5) then 1 else 0 := by
    change MvPolynomial.pderiv v (complete (P.row i-P.col j)) = _
    have hs : (P.row i-P.col j = (v.val : ℤ)) ↔
        (i = 0 ∧ j = 4) ∨ (i = 1 ∧ j = 5) := by
      rw [hv]
      simpa [P] using tied_border_index_iff D q hq i j
    by_cases hsite : (i = 0 ∧ j = 4) ∨ (i = 1 ∧ j = 5)
    · simp [Staircase.residual_pderiv_complete,hs,hsite]
    · simp [Staircase.residual_pderiv_complete,hs,hsite]
  have hd := det_six_two_site_derivative P.matrix v hM
  change MvPolynomial.pderiv v P.schur =
    P.unsignedMinor 0 4 + P.unsignedMinor 1 5 at hd
  have hP := D.positiveBorder_positiveCorner q q hq hq
  have htop := P.endpoint_top_minor hP
  have hbottom := P.endpoint_bottom_minor hP
  change P.unsignedMinor 0 4 =
    ((P.cornerDiagram hP).extendBottom P.bottomMargin P.bottomMargin_pos).schur at htop
  change P.unsignedMinor 1 5 =
    ((P.cornerDiagram hP).extendTop P.topMargin P.topMargin_pos).schur at hbottom
  rw [htop,hbottom] at hd
  simpa only [P, BetaDiagram.positiveBorder_cornerDiagram,
    BetaDiagram.positiveBorder_bottomMargin, BetaDiagram.positiveBorder_topMargin] using hd

private theorem bF_domain (p m z w : ℤ) (hz : 0 ≤ z) (hw : 0 ≤ w)
    (hp : z+w < p) (hm : z+w < m) :
    Domain p m p (p+m-w) m z w z z := by
  dsimp [Domain]
  omega

private theorem bH_domain (p m z w : ℤ) (hz : 0 ≤ z) (hw : 0 ≤ w)
    (hp : z+w < p) (hm : z+w < m) :
    Domain p (p+m-w) m p m z z w z := by
  dsimp [Domain]
  omega

/-- The actual B source profile, with no separation or positive-gap side condition. -/
def bProfileF (p m z w : ℤ) (hz : 0 ≤ z) (hw : 0 ≤ w)
    (hp : z+w < p) (hm : z+w < m) : Profile 4 :=
  profile p m p (p+m-w) m z w z z (bF_domain p m z w hz hw hp hm)

/-- The actual B companion. -/
def bProfileH (p m z w : ℤ) (hz : 0 ≤ z) (hw : 0 ≤ w)
    (hp : z+w < p) (hm : z+w < m) : Profile 4 :=
  profile p (p+m-w) m p m z z w z (bH_domain p m z w hz hw hp hm)

theorem b_profiles_thick (p m z w : ℤ) (hz : 0 ≤ z) (hw : 0 ≤ w)
    (hp : z+w < p) (hm : z+w < m) :
    Staircase.Thick (bProfileF p m z w hz hw hp hm) ∧
      Staircase.Thick (bProfileH p m z w hz hw hp hm) :=
  ⟨profile_thick _ _ _ _ _ _ _ _ _ (bF_domain p m z w hz hw hp hm),
   profile_thick _ _ _ _ _ _ _ _ _ (bH_domain p m z w hz hw hp hm)⟩

theorem b_profiles_schur_eq (p m z w : ℤ) (hz : 0 ≤ z) (hw : 0 ≤ w)
    (hp : z+w < p) (hm : z+w < m) :
    (bProfileF p m z w hz hw hp hm).toBetaDiagram.schur =
      (bProfileH p m z w hz hw hp hm).toBetaDiagram.schur := by
  unfold bProfileF bProfileH
  rw [profile_schur, profile_schur]
  exact b_identity hh p m z w

/-- The full sum of opposite actual endpoint extensions. -/
noncomputable def endpointSum (D : BetaDiagram 5) (t : ℤ) (ht : 0 < t) : CompleteRing :=
  (D.extendTop t ht).schur+(D.extendBottom t ht).schur

/-- The actual B endpoint sums are separated at every positive shift. -/
theorem b_endpoint_sum_ne (p m z w : ℤ) (hz : 0 ≤ z) (hw : 0 ≤ w)
    (hp : z+w < p) (hm : z+w < m) (hne : p ≠ m) (t : ℤ) (ht : 0 < t) :
    endpointSum (bProfileF p m z w hz hw hp hm).toBetaDiagram t ht ≠
      endpointSum (bProfileH p m z w hz hw hp hm).toBetaDiagram t ht := by
  have hThick := b_profiles_thick p m z w hz hw hp hm
  have hF := profile_endpoint_intervals (bProfileF p m z w hz hw hp hm)
    hThick.1.hessenberg t ht
  have hH := profile_endpoint_intervals (bProfileH p m z w hz hw hp hm)
    hThick.2.hessenberg t ht
  intro he
  unfold endpointSum at he
  rw [hF.1,hF.2,hH.1,hH.2] at he
  simp [bProfileF,bProfileH,profile_row,profile_gap] at he
  apply b_tied_defect_ne_zero p m z w t hz hw hp hm ht hne
  unfold bTopDefect bBottomDefect
  linear_combination he

/-- The two actual same-direction B extensions are unequal independently
of contacts or unit seams. -/
theorem b_same_endpoint_extensions_ne (p m z w : ℤ) (hz : 0 ≤ z) (hw : 0 ≤ w)
    (hp : z+w < p) (hm : z+w < m) (t : ℤ) (ht : 0 < t) :
    ((bProfileF p m z w hz hw hp hm).toBetaDiagram.extendTop t ht).schur ≠
      ((bProfileH p m z w hz hw hp hm).toBetaDiagram.extendTop t ht).schur ∧
    ((bProfileF p m z w hz hw hp hm).toBetaDiagram.extendBottom t ht).schur ≠
      ((bProfileH p m z w hz hw hp hm).toBetaDiagram.extendBottom t ht).schur := by
  have hThick := b_profiles_thick p m z w hz hw hp hm
  have hF := profile_endpoint_intervals (bProfileF p m z w hz hw hp hm)
    hThick.1.hessenberg t ht
  have hH := profile_endpoint_intervals (bProfileH p m z w hz hw hp hm)
    hThick.2.hessenberg t ht
  have hne := b_directional_defects_ne_zero p m z w t hz hw hp hm ht
  constructor
  · intro he
    rw [hF.1,hH.1] at he
    simp only [bProfileF,bProfileH,profile_row,profile_gap] at he
    exact hne.1 (sub_eq_zero.mpr he)
  · intro he
    rw [hF.2,hH.2] at he
    simp only [bProfileF,bProfileH,profile_row,profile_gap] at he
    exact hne.2 (sub_eq_zero.mpr he)

private theorem initialForm_scalar (w : ℕ+ → ℝ) (a : ℚ) (ha : a ≠ 0)
    (p : CompleteRing) :
    Base.initialForm w (MvPolynomial.C a*p) =
      MvPolynomial.C a*Base.initialForm w p := by
  have hs : (MvPolynomial.C a*p).support = p.support := by
    rw [← MvPolynomial.smul_eq_C_mul]
    exact MvPolynomial.support_smul_eq ha p
  have hl : Base.leastWeight w (MvPolynomial.C a*p) = Base.leastWeight w p := by
    unfold Base.leastWeight
    rw [hs]
  unfold Base.initialForm
  rw [hl, MvPolynomial.weightedHomogeneousComponent_C_mul]

private theorem positive_product_monomial {ι : Type*} (s : Finset ι) (k : ι → ℤ)
    (hk : ∀ i ∈ s, 0 < k i) :
    ∃ e : ℕ+ →₀ ℕ, (∏ i ∈ s, complete (k i)) = MvPolynomial.monomial e 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨e, he⟩ := ih (fun j hj => hk j (Finset.mem_insert_of_mem hj))
    let v : ℕ+ := ⟨(k i).toNat, by have := hk i (Finset.mem_insert_self i s); omega⟩
    refine ⟨Finsupp.single v 1+e, ?_⟩
    rw [Finset.prod_insert hi, complete_of_pos (hk i (Finset.mem_insert_self i s)), he]
    change MvPolynomial.monomial (Finsupp.single v 1) (1 : ℚ) *
      MvPolynomial.monomial e 1 = _
    rw [MvPolynomial.monomial_mul_monomial]
    simp

/-- The square initial form of every full beta determinant is a single
coefficient-one monomial, irrespective of connectivity or common betas. -/
theorem full_initial_monomial {n : ℕ} (D : BetaDiagram n) :
    ∃ e : ℕ+ →₀ ℕ, Base.initialForm Base.squareWeight.generatorWeight D.schur =
      MvPolynomial.monomial e 1 := by
  rw [D.square_initialForm]
  exact positive_product_monomial Finset.univ (fun i => D.row i-D.col i)
    (fun i _ => sub_pos.mpr (D.row_nonempty i))

/-- Rational units cannot change the normalization of an actual Schur
determinant.  Thus full connected factors recovered by unique factorization
are literal polynomials, not factors known only up to association. -/
theorem full_schur_associated_eq {n m : ℕ} (D : BetaDiagram n) (E : BetaDiagram m)
    (h : Associated D.schur E.schur) : D.schur = E.schur := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨a, ha, hua⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp u.isUnit
  have he : MvPolynomial.C a*D.schur = E.schur := by
    simpa only [hua, mul_comm] using hu
  obtain ⟨e, hD⟩ := full_initial_monomial D
  obtain ⟨f, hE⟩ := full_initial_monomial E
  have hi := congrArg (Base.initialForm Base.squareWeight.generatorWeight) he
  rw [initialForm_scalar _ a ha.ne_zero D.schur, hD, hE] at hi
  have ha1 := Staircase.scalar_eq_one_of_monomial_eq a ha.ne_zero e f hi
  simpa only [ha1, map_one, one_mul] using he

/-- Equal products of two actual connected component polynomials match the
two full factors, including all repeated factors and either ordering. -/
theorem connected_two_factor_reading {a b c d : ℕ}
    (A : BetaDiagram a) (B : BetaDiagram b) (C : BetaDiagram c) (D : BetaDiagram d)
    (hA : A.Connected) (hB : B.Connected) (hC : C.Connected) (hD : D.Connected)
    (he : A.schur*B.schur = C.schur*D.schur) :
    (A.schur = C.schur ∧ B.schur = D.schur) ∨
      (A.schur = D.schur ∧ B.schur = C.schur) := by
  have hAi := A.schur_irreducible hA
  have hCi := C.schur_irreducible hC
  have hDi := D.schur_irreducible hD
  have hAp := UniqueFactorizationMonoid.irreducible_iff_prime.mp hAi
  have hdvd : A.schur ∣ C.schur*D.schur := by
    rw [← he]
    exact dvd_mul_right _ _
  rcases hAp.dvd_or_dvd hdvd with hAC | hAD
  · have hAC := full_schur_associated_eq A C (hAi.associated_of_dvd hCi hAC)
    left
    refine ⟨hAC, ?_⟩
    apply mul_left_cancel₀ A.schur_ne_zero
    rw [he, hAC]
  · have hAD := full_schur_associated_eq A D (hAi.associated_of_dvd hDi hAD)
    right
    refine ⟨hAD, ?_⟩
    apply mul_left_cancel₀ A.schur_ne_zero
    rw [he, hAD, mul_comm C.schur]

/-- Actual thickness and arithmetic absence exclude a contact generator from
the full determinant, not from a separately supplied polynomial. -/
theorem erase_schur_eq_self_of_no_contact {n : ℕ} (P : Profile n)
    (hP : Staircase.Thick P) (z : ℕ+)
    (hr : ∀ i, z.val < P.r i) (hg : ∀ j, P.g j ≠ z.val) :
    eraseGenerator z P.toBetaDiagram.schur = P.toBetaDiagram.schur := by
  apply eraseGenerator_eq_self
  apply not_mem_vars_det
  intro i j
  change z ∉ (complete (P.xi i-P.zeta j)).vars
  rw [mem_vars_complete_iff]
  intro he
  by_cases hij : i ≤ j
  · have hz := P.zeta_strictAnti.antitone hij
    have hrow := P.xi_sub_zeta i
    have hri := hr i
    omega
  · by_cases hfar : j.val+1 < i.val
    · have hn := hP.hessenberg i j hfar
      have hp := z.pos
      omega
    · let s : Fin n := ⟨j.val, by have := i.isLt; omega⟩
      have hi : i = s.succ := by apply Fin.ext; dsimp [s]; omega
      have hj : j = s.castSucc := by apply Fin.ext; rfl
      rw [hi,hj,P.xi_succ_sub_zeta_castSucc] at he
      exact hg s (by exact_mod_cast he.symm)

/-- Cutting a unique minimum seam gives the actual unspecialized left and
right full Schur factors, including singleton components. -/
theorem unique_minimum_cut (P : Profile 4) (hP : Staircase.Thick P)
    (z : ℕ+) (hmin : ∀ j, z.val ≤ P.g j) (c : Fin 4)
    (hunique : ∀ j, P.g j = z.val ↔ j = c) :
    eraseGenerator z P.toBetaDiagram.schur =
      (GeneralHessenberg.leftOfSeam P c).toBetaDiagram.schur *
      (GeneralHessenberg.rightOfSeam P c).toBetaDiagram.schur := by
  have hocc : ∃ j, P.g j = z.val := ⟨c,(hunique c).mpr rfl⟩
  have hrows := GeneralHessenberg.row_gt_minimum P z hmin hocc
  have hL := GeneralHessenberg.slice_thick hP 0 c.val (by omega)
  have hR := GeneralHessenberg.slice_thick hP (c.val+1) (3-c.val) (by have := c.isLt; omega)
  have hrL : ∀ i, z.val < (GeneralHessenberg.leftOfSeam P c).r i := by
    intro i
    exact hrows _
  have hrR : ∀ i, z.val < (GeneralHessenberg.rightOfSeam P c).r i := by
    intro i
    exact hrows _
  have hgL : ∀ j, (GeneralHessenberg.leftOfSeam P c).g j ≠ z.val := by
    intro j he
    let k : Fin 4 := ⟨j.val, by have := j.isLt; have := c.isLt; omega⟩
    have hk : P.g k = z.val := by
      simpa only [GeneralHessenberg.leftOfSeam, GeneralHessenberg.slice,
        Nat.zero_add, k] using he
    have hv := congrArg Fin.val ((hunique k).mp hk)
    have hj := j.isLt
    dsimp [k] at hv
    omega
  have hgR : ∀ j, (GeneralHessenberg.rightOfSeam P c).g j ≠ z.val := by
    intro j he
    let k : Fin 4 := ⟨c.val+1+j.val, by have := j.isLt; have := c.isLt; omega⟩
    have hk : P.g k = z.val := by
      simpa only [GeneralHessenberg.rightOfSeam, GeneralHessenberg.slice,k] using he
    have hv := congrArg Fin.val ((hunique k).mp hk)
    dsimp [k] at hv
    omega
  have heL := erase_schur_eq_self_of_no_contact
    (GeneralHessenberg.leftOfSeam P c) hL z hrL hgL
  have heR := erase_schur_eq_self_of_no_contact
    (GeneralHessenberg.rightOfSeam P c) hR z hrR hgR
  rw [GeneralHessenberg.schur_join_formula P hP c, map_sub, map_mul, map_mul,
    heL, heR, (hunique c).mpr rfl]
  simp [eraseGenerator_complete]

/-- A unique minimum cannot move between an end and an interior seam.  Both
the uniqueness of the mate's minimum and its two factor readings are produced
from actual full Schur equality and the gap invariant. -/
theorem unique_minimum_placement (P Q : Profile 4)
    (hP : Staircase.Thick P) (hQ : Staircase.Thick Q)
    (z : ℕ+) (hmin : ∀ j, z.val ≤ P.g j) (c : Fin 4)
    (hunique : ∀ j, P.g j = z.val ↔ j = c)
    (he : P.toBetaDiagram.schur = Q.toBetaDiagram.schur) :
    ∃ d : Fin 4, (∀ j, Q.g j = z.val ↔ j = d) ∧
      (c = d ∨ c.val+d.val = 3) := by
  have heProfile : P.schur = Q.schur := by
    simpa only [Profile.toBetaDiagram_schur] using he
  have hgm := Profile.gaps_eq_of_schur_eq heProfile
  have hminQ : ∀ j, z.val ≤ Q.g j := by
    intro j
    have hm : Q.g j ∈ Q.gapMultiset :=
      Multiset.mem_map.mpr ⟨j,Finset.mem_univ j,rfl⟩
    rw [← hgm] at hm
    obtain ⟨k,_,hk⟩ := Multiset.mem_map.mp hm
    have hv := hmin k
    omega
  have hmP : Staircase.minimumMultiplicity P z = 1 := by
    simp only [Staircase.minimumMultiplicity,hunique,Finset.sum_ite_eq',
      Finset.mem_univ,ite_true]
  have hmQ : Staircase.minimumMultiplicity Q z = 1 := by
    rw [← minimumMultiplicity_eq_of_schur_eq P Q z heProfile]
    exact hmP
  have hcard : (Finset.univ.filter (fun j => Q.g j = z.val)).card = 1 := by
    rw [Finset.card_filter]
    exact hmQ
  obtain ⟨d, hd⟩ := Finset.card_eq_one.mp hcard
  have huniqQ : ∀ j, Q.g j = z.val ↔ j = d := by
    intro j
    have hi : j ∈ Finset.univ.filter (fun j => Q.g j = z.val) ↔ j ∈ ({d} : Finset (Fin 4)) := by
      rw [hd]
    simpa only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton] using hi
  have heCut := congrArg (eraseGenerator z) he
  rw [unique_minimum_cut P hP z hmin c hunique,
    unique_minimum_cut Q hQ z hminQ d huniqQ] at heCut
  have hread := connected_two_factor_reading
    (GeneralHessenberg.leftOfSeam P c).toBetaDiagram
    (GeneralHessenberg.rightOfSeam P c).toBetaDiagram
    (GeneralHessenberg.leftOfSeam Q d).toBetaDiagram
    (GeneralHessenberg.rightOfSeam Q d).toBetaDiagram
    (Profile.toBetaDiagram_connected _) (Profile.toBetaDiagram_connected _)
    (Profile.toBetaDiagram_connected _) (Profile.toBetaDiagram_connected _) heCut
  refine ⟨d,huniqQ,?_⟩
  rcases hread with hread | hread
  · have hn := (GeneralHessenberg.leftOfSeam P c).toBetaDiagram.row_count_of_schur_eq
      (GeneralHessenberg.leftOfSeam Q d).toBetaDiagram hread.1
    left
    apply Fin.ext
    omega
  · have hn := (GeneralHessenberg.leftOfSeam P c).toBetaDiagram.row_count_of_schur_eq
      (GeneralHessenberg.rightOfSeam Q d).toBetaDiagram hread.1
    right
    have := d.isLt
    omega

/-- Positive extension of the last actual profile row, preserving every seam. -/
def bumpLast {n : ℕ} (P : Profile n) (t : ℕ) : Profile n where
  r i := P.r i+if i = Fin.last n then t else 0
  g := P.g
  r_pos i := lt_of_lt_of_le (P.r_pos i) (Nat.le_add_right _ _)
  g_lt_castSucc j := lt_of_lt_of_le (P.g_lt_castSucc j) (Nat.le_add_right _ _)
  g_lt_succ j := lt_of_lt_of_le (P.g_lt_succ j) (Nat.le_add_right _ _)

theorem bumpLast_thick {n : ℕ} {P : Profile n} (hP : Staircase.Thick P) (t : ℕ) :
    Staircase.Thick (bumpLast P t) := by
  intro j k hjk
  exact lt_of_lt_of_le (hP j k hjk) (Nat.le_add_right _ _)

theorem bumpLast_injective {n : ℕ} (t : ℕ) :
    Function.Injective (fun P : Profile n => bumpLast P t) := by
  intro P Q he
  apply Profile.ext
  · funext i
    have hi := congrArg (fun R : Profile n => R.r i) he
    simp only [bumpLast] at hi
    omega
  · have hg := congrArg (fun R : Profile n => R.g) he
    exact hg

private def orientThree (P : Profile 3) (rev : Bool) : Profile 3 :=
  if rev then P.rotate else P

private theorem orientThree_hessenberg (P : Profile 3) (hP : P.Hessenberg) (rev : Bool) :
    (orientThree P rev).Hessenberg := by
  cases rev
  · exact hP
  · exact P.hessenberg_rotate hP

/-- No nonrotation four-row full class persists through equal positive terminal
extensions.  The arithmetic proof uses the actual completed four-row class. -/
theorem four_family_terminal_ne (w b c : ℕ) (hcw : c < w) (hb : c+w < b)
    (revF revH : Bool) (t : ℕ) (ht : 0 < t) :
    (bumpLast (orientThree (FourRowHessenberg.familyF w b c hcw hb) revF) t).schur ≠
      (bumpLast (orientThree (FourRowHessenberg.familyH w b c hcw hb) revH) t).schur := by
  intro he
  have hF := orientThree_hessenberg _ (FourRowHessenberg.familyF_hessenberg w b c hcw hb) revF
  have hH := orientThree_hessenberg _ (FourRowHessenberg.familyH_hessenberg w b c hcw hb) revH
  have hFb := (bumpLast_thick (GeneralHessenberg.hessenberg_thick _ hF) t).hessenberg
  have hHb := (bumpLast_thick (GeneralHessenberg.hessenberg_thick _ hH) t).hessenberg
  have hclass := FourRowHessenberg.hessenberg_classification _ _ hFb hHb he
  rcases hclass with heq | hrot | hfamily
  · have hg := congrArg (fun R : Profile 3 => R.g 1) heq
    cases revF <;> cases revH <;>
      simp [orientThree,bumpLast,Profile.rotate,FourRowHessenberg.familyF,
        FourRowHessenberg.familyH] at hg <;> omega
  · have hg := congrArg (fun R : Profile 3 => R.g 1) hrot
    cases revF <;> cases revH <;>
      simp [orientThree,bumpLast,Profile.rotate,FourRowHessenberg.familyF,
        FourRowHessenberg.familyH] at hg <;> omega
  · obtain ⟨w',b',c',hcw',hb',hfamily⟩ := hfamily
    rcases hfamily with ⟨hmember,_⟩ | ⟨hmember,_⟩
    all_goals rcases hmember with hmember | hmember
    all_goals
      have hg0 := congrArg (fun R : Profile 3 => R.g 0) hmember
      have hg1 := congrArg (fun R : Profile 3 => R.g 1) hmember
      have hg2 := congrArg (fun R : Profile 3 => R.g 2) hmember
      have hr0 := congrArg (fun R : Profile 3 => R.r 0) hmember
      have hr1 := congrArg (fun R : Profile 3 => R.r 1) hmember
      have hr3 := congrArg (fun R : Profile 3 => R.r 3) hmember
      cases revF <;> simp [orientThree,bumpLast,Profile.rotate,
        FourRowHessenberg.familyF,FourRowHessenberg.familyH]
        at hg0 hg1 hg2 hr0 hr1 hr3 <;> omega

private theorem orientThree_of_member (P F : Profile 3) (h : P = F ∨ P = F.rotate) :
    ∃ rev : Bool, P = orientThree F rev := by
  rcases h with h | h
  · exact ⟨false,h⟩
  · exact ⟨true,h⟩

/-- Full four-row equality and equal positive last-row extensions recover the
literal component, including exceptional families and symmetric components. -/
theorem terminal_four_reconstruction (P Q : Profile 3)
    (hP : P.Hessenberg) (hQ : Q.Hessenberg)
    (t : ℕ) (ht : 0 < t) (he : P.schur = Q.schur)
    (hext : (bumpLast P t).schur = (bumpLast Q t).schur) : P = Q := by
  have hclass := FourRowHessenberg.hessenberg_classification P Q hP hQ he
  rcases hclass with heq | hrot | hfamily
  · exact heq
  · have hPb := (bumpLast_thick (GeneralHessenberg.hessenberg_thick P hP) t).hessenberg
    have hQb := (bumpLast_thick (GeneralHessenberg.hessenberg_thick Q hQ) t).hessenberg
    have hclass' := FourRowHessenberg.hessenberg_classification _ _ hPb hQb hext
    rcases hclass' with hb | hb | hf
    · exact bumpLast_injective t hb
    · have hr := congrArg (fun R : Profile 3 => R.r 0) hb
      have hr' := congrArg (fun R : Profile 3 => R.r 0) hrot
      simp [bumpLast,Profile.rotate] at hr hr'
      omega
    · obtain ⟨w,b,c,hcw,hb,hf⟩ := hf
      have hgap : (bumpLast P t).g 1 = (bumpLast Q t).g 1 := by
        have hg := congrArg (fun R : Profile 3 => R.g 1) hrot
        simpa [bumpLast,Profile.rotate] using hg
      rcases hf with ⟨hF,hH⟩ | ⟨hH,hF⟩
      all_goals rcases hF with hF | hF
      all_goals rcases hH with hH | hH
      all_goals
        have hgF := congrArg (fun R : Profile 3 => R.g 1) hF
        have hgH := congrArg (fun R : Profile 3 => R.g 1) hH
        simp [FourRowHessenberg.familyF,FourRowHessenberg.familyH,
          Profile.rotate] at hgF hgH
        omega
  · obtain ⟨w,b,c,hcw,hb,hfamily⟩ := hfamily
    rcases hfamily with ⟨hF,hH⟩ | ⟨hH,hF⟩
    · obtain ⟨r,hr⟩ := orientThree_of_member P _ hF
      obtain ⟨s,hs⟩ := orientThree_of_member Q _ hH
      rw [hr,hs] at hext
      exact False.elim (four_family_terminal_ne w b c hcw hb r s t ht hext)
    · obtain ⟨r,hr⟩ := orientThree_of_member Q _ hF
      obtain ⟨s,hs⟩ := orientThree_of_member P _ hH
      rw [hr,hs] at hext
      exact False.elim (four_family_terminal_ne w b c hcw hb r s t ht hext.symm)

private theorem terminal_singleton (P : Profile 4) :
    (GeneralHessenberg.rightOfSeam P 3).toBetaDiagram.schur = complete (P.r 4) := by
  rw [Profile.toBetaDiagram_schur,Profile.schur_single_interval]
  change hh (P.r 4) = complete (P.r 4)
  exact (complete_eq_hh _).symm

/-- The terminal seam contraction is exactly a positive last-row extension
of the literal four-row component. -/
theorem terminal_contract_bump (P : Profile 4) :
    GeneralHessenberg.contract P 3 =
      bumpLast (GeneralHessenberg.leftOfSeam P 3) (P.r 4-P.g 3) := by
  have hp := P.g_lt_succ 3
  norm_num at hp
  apply Profile.ext
  · funext i
    obtain ⟨hx,hz⟩ := GeneralHessenberg.contract_beta P 3
    have hr := (GeneralHessenberg.contract P 3).xi_sub_zeta i
    rw [hx,hz] at hr
    fin_cases i
    all_goals simp [bumpLast,GeneralHessenberg.leftOfSeam,GeneralHessenberg.slice,
      GeneralHessenberg.sliceEmbedding]
    all_goals first
      | (norm_num [Fin.succAbove] at hr; rw [P.xi_sub_zeta] at hr; exact_mod_cast hr.symm)
      | (have hj := GeneralHessenberg.contract_joined_row P 3; norm_num at hj; omega)
  · funext j
    fin_cases j <;> simp [bumpLast,GeneralHessenberg.contract_gap,
      GeneralHessenberg.leftOfSeam,GeneralHessenberg.slice,Fin.succAbove]

private theorem gap_minimum_preserved (P Q : Profile 4) (z : ℕ+)
    (hmin : ∀ j, z.val ≤ P.g j) (he : P.toBetaDiagram.schur = Q.toBetaDiagram.schur) :
    ∀ j, z.val ≤ Q.g j := by
  have he' : P.schur = Q.schur := by simpa only [Profile.toBetaDiagram_schur] using he
  have hg := Profile.gaps_eq_of_schur_eq he'
  intro j
  have hm : Q.g j ∈ Q.gapMultiset :=
    Multiset.mem_map.mpr ⟨j,Finset.mem_univ j,rfl⟩
  rw [← hg] at hm
  obtain ⟨k,_,hk⟩ := Multiset.mem_map.mp hm
  have h := hmin k
  omega

/-- Equal profiles with their unique minimum seams terminal on both sides
are literally equal.  The four-row exception is eliminated by its actual
positive terminal contraction, not by residual-degree assumptions. -/
theorem terminal_minimum_aligned (P Q : Profile 4)
    (hP : Staircase.Thick P) (hQ : Staircase.Thick Q)
    (z : ℕ+) (hmin : ∀ j, z.val ≤ P.g j)
    (huniqueP : ∀ j, P.g j = z.val ↔ j = 3)
    (huniqueQ : ∀ j, Q.g j = z.val ↔ j = 3)
    (he : P.toBetaDiagram.schur = Q.toBetaDiagram.schur) : P = Q := by
  have hminQ := gap_minimum_preserved P Q z hmin he
  have hcut := congrArg (eraseGenerator z) he
  rw [unique_minimum_cut P hP z hmin 3 huniqueP,
    unique_minimum_cut Q hQ z hminQ 3 huniqueQ] at hcut
  have hread := connected_two_factor_reading
    (GeneralHessenberg.leftOfSeam P 3).toBetaDiagram
    (GeneralHessenberg.rightOfSeam P 3).toBetaDiagram
    (GeneralHessenberg.leftOfSeam Q 3).toBetaDiagram
    (GeneralHessenberg.rightOfSeam Q 3).toBetaDiagram
    (Profile.toBetaDiagram_connected _) (Profile.toBetaDiagram_connected _)
    (Profile.toBetaDiagram_connected _) (Profile.toBetaDiagram_connected _) hcut
  have hordered :
      (GeneralHessenberg.leftOfSeam P 3).toBetaDiagram.schur =
        (GeneralHessenberg.leftOfSeam Q 3).toBetaDiagram.schur ∧
      (GeneralHessenberg.rightOfSeam P 3).toBetaDiagram.schur =
        (GeneralHessenberg.rightOfSeam Q 3).toBetaDiagram.schur := by
    rcases hread with hread | hread
    · exact hread
    · have hn := (GeneralHessenberg.leftOfSeam P 3).toBetaDiagram.row_count_of_schur_eq
        (GeneralHessenberg.rightOfSeam Q 3).toBetaDiagram hread.1
      norm_num at hn
  have heSingle : (GeneralHessenberg.rightOfSeam P 3).schur =
      (GeneralHessenberg.rightOfSeam Q 3).schur := by
    simpa only [Profile.toBetaDiagram_schur] using hordered.2
  have hrows := (Profile.rows_eq_of_schur_eq heSingle).2
  have heRow : P.r 4 = Q.r 4 := by
    simpa [Profile.rowMultiset,GeneralHessenberg.rightOfSeam,GeneralHessenberg.slice,
      GeneralHessenberg.sliceEmbedding] using hrows
  have hpz := (huniqueP 3).mpr rfl
  have hqz := (huniqueQ 3).mpr rfl
  have hmult : complete z.val*(GeneralHessenberg.contract P 3).toBetaDiagram.schur =
      complete z.val*(GeneralHessenberg.contract Q 3).toBetaDiagram.schur := by
    rw [GeneralHessenberg.schur_join_formula P hP 3,
      GeneralHessenberg.schur_join_formula Q hQ 3,terminal_singleton,terminal_singleton,
      hpz,hqz,hordered.1,heRow] at he
    linear_combination -he
  have hext := mul_left_cancel₀ ((complete_ne_zero_iff z.val).mpr (by positivity)) hmult
  rw [terminal_contract_bump P,terminal_contract_bump Q,
    Profile.toBetaDiagram_schur,Profile.toBetaDiagram_schur,hpz,hqz,← heRow] at hext
  have hthickP := GeneralHessenberg.slice_thick hP 0 3 (by omega)
  have hthickQ := GeneralHessenberg.slice_thick hQ 0 3 (by omega)
  have hcore := terminal_four_reconstruction
    (GeneralHessenberg.leftOfSeam P 3) (GeneralHessenberg.leftOfSeam Q 3)
    hthickP.hessenberg hthickQ.hessenberg (P.r 4-z.val)
    (by have hp := P.g_lt_succ 3; norm_num at hp; omega)
    (by simpa only [Profile.toBetaDiagram_schur] using hordered.1) hext
  apply Profile.ext
  · funext i
    by_cases hi : i.val < 4
    · let j : Fin 4 := ⟨i.val,hi⟩
      have h := congrArg (fun R : Profile 3 => R.r j) hcore
      have hij : GeneralHessenberg.sliceEmbedding (n := 4) 0 3 (by omega) j = i := by
        apply Fin.ext
        change 0+j.val = i.val
        dsimp only [j]
        omega
      change P.r (GeneralHessenberg.sliceEmbedding 0 3 (by omega) j) =
        Q.r (GeneralHessenberg.sliceEmbedding 0 3 (by omega) j) at h
      simpa only [hij] using h
    · have hi4 : i = 4 := by
        apply Fin.ext
        change i.val = 4
        omega
      subst i
      exact heRow
  · funext i
    by_cases hi : i.val < 3
    · let j : Fin 3 := ⟨i.val,hi⟩
      have h := congrArg (fun R : Profile 3 => R.g j) hcore
      have heij : j.castSucc = i := by apply Fin.ext; rfl
      simpa only [GeneralHessenberg.leftOfSeam,GeneralHessenberg.slice,
        Nat.zero_add,heij] using h
    · have hi3 : i = 3 := by fin_omega
      subst i
      exact hpz.trans hqz.symm

/-- Rotation preserves the arithmetic thickness inequalities at every order. -/
theorem thick_rotate {n : ℕ} {P : Profile n} (hP : Staircase.Thick P) :
    Staircase.Thick P.rotate := by
  intro j k hjk
  have hv := congrArg Fin.val hjk
  simp only [Fin.val_succ,Fin.val_castSucc] at hv
  have hrev : k.rev.succ = j.rev.castSucc := by
    apply Fin.ext
    simp only [Fin.val_rev,Fin.val_succ,Fin.val_castSucc]
    have := j.isLt; have := k.isLt
    omega
  have hr : j.succ.rev = k.rev.succ := by
    apply Fin.ext
    simp only [Fin.val_rev,Fin.val_succ]
    have := j.isLt; have := k.isLt
    omega
  have h := hP k.rev j.rev hrev
  change P.g j.rev+P.g k.rev < P.r j.succ.rev
  rw [hr]
  simpa only [Nat.add_comm] using h

/-- Common translation of normalized full profile diagrams is literal equality. -/
theorem profile_eq_of_translation {n : ℕ} (P Q : Profile n)
    (h : P.toBetaDiagram.TranslationEquivalent Q.toBetaDiagram) : P = Q := by
  obtain ⟨c,hr,hc⟩ := h
  have hlast := hc (Fin.last n)
  change P.zeta (Fin.last n) = Q.zeta (Fin.last n)+c at hlast
  rw [P.zeta_last,Q.zeta_last] at hlast
  have hc0 : c = 0 := by omega
  apply Profile.eq_of_beta_eq
  · funext i
    have hi := hr i
    change P.xi i = Q.xi i+c at hi
    simpa only [hc0,add_zero] using hi
  · funext i
    have hi := hc i
    change P.zeta i = Q.zeta i+c at hi
    simpa only [hc0,add_zero] using hi

/-- Reflection of full profile diagrams is literal reversal after normalization. -/
theorem profile_eq_rotate_of_rotation {n : ℕ} (P Q : Profile n)
    (h : P.toBetaDiagram.RotationEquivalent Q.toBetaDiagram) : P = Q.rotate := by
  obtain ⟨c,hr,hc⟩ := h
  have hlast := hc (Fin.last n)
  change P.zeta (Fin.last n) = c-Q.xi (Fin.last n).rev at hlast
  rw [P.zeta_last,Fin.rev_last] at hlast
  have hconstant : c = Q.xi 0 := by omega
  apply Profile.eq_of_beta_eq
  · funext i
    rw [Q.xi_rotate]
    have hi := hr i
    change P.xi i = c-Q.zeta i.rev at hi
    simpa only [hconstant] using hi
  · funext i
    rw [Q.zeta_rotate]
    have hi := hc i
    change P.zeta i = c-Q.xi i.rev at hi
    simpa only [hconstant] using hi

/-- The actual small-row theorem fixes each full two- or three-row safe-cut
component up to its literal reversal. -/
theorem small_profile_rigidity {n : ℕ} (P Q : Profile n) (hn : n+1 ≤ 3)
    (he : P.toBetaDiagram.schur = Q.toBetaDiagram.schur) : P = Q ∨ P = Q.rotate := by
  have h := P.toBetaDiagram.small_rows_rigidity_same_order Q.toBetaDiagram
    P.toBetaDiagram_connected Q.toBetaDiagram_connected hn he
  rcases h with h | h
  · exact Or.inl (profile_eq_of_translation P Q h)
  · exact Or.inr (profile_eq_rotate_of_rotation P Q h)

/-- Complete unique-terminal-minimum rigidity against every actual thick
five-row mate.  Its minimum seam position and the rotation alignment are
consequences of the full polynomial equality. -/
theorem terminal_minimum_rigidity (P Q : Profile 4)
    (hP : Staircase.Thick P) (hQ : Staircase.Thick Q)
    (z : ℕ+) (hmin : ∀ j, z.val ≤ P.g j)
    (hunique : ∀ j, P.g j = z.val ↔ j = 3)
    (he : P.toBetaDiagram.schur = Q.toBetaDiagram.schur) :
    P = Q ∨ P = Q.rotate := by
  obtain ⟨d,huniqQ,hpos⟩ := unique_minimum_placement P Q hP hQ z hmin 3 hunique he
  have hd : d = 3 ∨ d = 0 := by
    rcases hpos with hpos | hpos
    · exact Or.inl hpos.symm
    · right; apply Fin.ext; omega
  rcases hd with rfl | rfl
  · exact Or.inl (terminal_minimum_aligned P Q hP hQ z hmin hunique huniqQ he)
  · have huniqQr : ∀ j, Q.rotate.g j = z.val ↔ j = 3 := by
      intro j
      change Q.g j.rev = z.val ↔ j = 3
      rw [huniqQ]
      fin_cases j <;> decide
    have he' : P.toBetaDiagram.schur = Q.rotate.toBetaDiagram.schur := by
      simpa only [Profile.toBetaDiagram_schur,Profile.schur_rotate] using he
    exact Or.inr (terminal_minimum_aligned P Q.rotate hP (thick_rotate hQ)
      z hmin hunique huniqQr he')

/-- The two literal safe-cut components may each be reversed.  This predicate
records only the original row and gap words, not polynomial conclusions. -/
def InteriorFlip (P Q : Profile 4) (leftRev tailRev : Bool) : Prop :=
  Q.r = ![if leftRev then P.r 1 else P.r 0,
          if leftRev then P.r 0 else P.r 1,
          if tailRev then P.r 4 else P.r 2,
          P.r 3,if tailRev then P.r 2 else P.r 4] ∧
  Q.g = ![P.g 0,P.g 1,if tailRev then P.g 3 else P.g 2,
    if tailRev then P.g 2 else P.g 3]

/-- The actual merged-row reading of an interior contraction. -/
@[simp] theorem interior_contract_row (P : Profile 4) (i : Fin 4) :
    ((GeneralHessenberg.contract P 1).r i : ℤ) =
      ![(P.r 0 : ℤ),(P.r 1 : ℤ)+P.r 2-P.g 1,(P.r 3 : ℤ),(P.r 4 : ℤ)] i := by
  obtain ⟨hx,hz⟩ := GeneralHessenberg.contract_beta P 1
  have hr := (GeneralHessenberg.contract P 1).xi_sub_zeta i
  rw [hx,hz] at hr
  fin_cases i
  all_goals first
    | (norm_num [Fin.succAbove] at hr; rw [P.xi_sub_zeta] at hr; simpa using hr.symm)
    | (have hj := GeneralHessenberg.contract_joined_row P 1; simpa using hj)

@[simp] theorem interior_contract_gap (P : Profile 4) (j : Fin 3) :
    (GeneralHessenberg.contract P 1).g j = ![P.g 0,P.g 2,P.g 3] j := by
  fin_cases j <;> simp [GeneralHessenberg.contract_gap,Fin.succAbove]

/-- Once the minimum seams are aligned in the interior, full safe-cut
factorization produces all four component-reversal candidates. -/
theorem interior_minimum_candidates (P Q : Profile 4)
    (hP : Staircase.Thick P) (hQ : Staircase.Thick Q)
    (z : ℕ+) (hmin : ∀ j, z.val ≤ P.g j)
    (huniqueP : ∀ j, P.g j = z.val ↔ j = 1)
    (huniqueQ : ∀ j, Q.g j = z.val ↔ j = 1)
    (he : P.toBetaDiagram.schur = Q.toBetaDiagram.schur) :
    ∃ leftRev tailRev : Bool, InteriorFlip P Q leftRev tailRev := by
  have hminQ := gap_minimum_preserved P Q z hmin he
  have hcut := congrArg (eraseGenerator z) he
  rw [unique_minimum_cut P hP z hmin 1 huniqueP,
    unique_minimum_cut Q hQ z hminQ 1 huniqueQ] at hcut
  have hread := connected_two_factor_reading
    (GeneralHessenberg.leftOfSeam P 1).toBetaDiagram
    (GeneralHessenberg.rightOfSeam P 1).toBetaDiagram
    (GeneralHessenberg.leftOfSeam Q 1).toBetaDiagram
    (GeneralHessenberg.rightOfSeam Q 1).toBetaDiagram
    (Profile.toBetaDiagram_connected _) (Profile.toBetaDiagram_connected _)
    (Profile.toBetaDiagram_connected _) (Profile.toBetaDiagram_connected _) hcut
  have hordered :
      (GeneralHessenberg.leftOfSeam P 1).toBetaDiagram.schur =
        (GeneralHessenberg.leftOfSeam Q 1).toBetaDiagram.schur ∧
      (GeneralHessenberg.rightOfSeam P 1).toBetaDiagram.schur =
        (GeneralHessenberg.rightOfSeam Q 1).toBetaDiagram.schur := by
    rcases hread with hread | hread
    · exact hread
    · have hn := (GeneralHessenberg.leftOfSeam P 1).toBetaDiagram.row_count_of_schur_eq
        (GeneralHessenberg.rightOfSeam Q 1).toBetaDiagram hread.1
      norm_num at hn
  have hL := small_profile_rigidity (GeneralHessenberg.leftOfSeam P 1)
    (GeneralHessenberg.leftOfSeam Q 1) (by decide) hordered.1
  have hR := small_profile_rigidity (GeneralHessenberg.rightOfSeam P 1)
    (GeneralHessenberg.rightOfSeam Q 1) (by decide) hordered.2
  have hpz := (huniqueP 1).mpr rfl
  have hqz := (huniqueQ 1).mpr rfl
  rcases hL with hL | hL
  all_goals rcases hR with hR | hR
  · refine ⟨false,false,?_,?_⟩
    all_goals funext i; fin_cases i
    all_goals first
      | (have h := congrArg (fun R : Profile 1 => R.r 0) hL; simpa [GeneralHessenberg.leftOfSeam,GeneralHessenberg.slice,GeneralHessenberg.sliceEmbedding] using h.symm)
      | (have h := congrArg (fun R : Profile 1 => R.r 1) hL; simpa [GeneralHessenberg.leftOfSeam,GeneralHessenberg.slice,GeneralHessenberg.sliceEmbedding] using h.symm)
      | (have h := congrArg (fun R : Profile 2 => R.r 0) hR; simpa [GeneralHessenberg.rightOfSeam,GeneralHessenberg.slice,GeneralHessenberg.sliceEmbedding] using h.symm)
      | (have h := congrArg (fun R : Profile 2 => R.r 1) hR; simpa [GeneralHessenberg.rightOfSeam,GeneralHessenberg.slice,GeneralHessenberg.sliceEmbedding] using h.symm)
      | (have h := congrArg (fun R : Profile 2 => R.r 2) hR; simpa [GeneralHessenberg.rightOfSeam,GeneralHessenberg.slice,GeneralHessenberg.sliceEmbedding] using h.symm)
      | (have h := congrArg (fun R : Profile 1 => R.g 0) hL; simpa [GeneralHessenberg.leftOfSeam,GeneralHessenberg.slice] using h.symm)
      | exact hqz.trans hpz.symm
      | (have h := congrArg (fun R : Profile 2 => R.g 0) hR; simpa [GeneralHessenberg.rightOfSeam,GeneralHessenberg.slice] using h.symm)
      | (have h := congrArg (fun R : Profile 2 => R.g 1) hR; simpa [GeneralHessenberg.rightOfSeam,GeneralHessenberg.slice] using h.symm)
  · refine ⟨false,true,?_,?_⟩
    all_goals funext i; fin_cases i
    all_goals first
      | (have h := congrArg (fun R : Profile 1 => R.r 0) hL; simpa [GeneralHessenberg.leftOfSeam,GeneralHessenberg.slice,GeneralHessenberg.sliceEmbedding] using h.symm)
      | (have h := congrArg (fun R : Profile 1 => R.r 1) hL; simpa [GeneralHessenberg.leftOfSeam,GeneralHessenberg.slice,GeneralHessenberg.sliceEmbedding] using h.symm)
      | (have h := congrArg (fun R : Profile 2 => R.r 0) hR; simpa [Profile.rotate,GeneralHessenberg.rightOfSeam,GeneralHessenberg.slice,GeneralHessenberg.sliceEmbedding] using h.symm)
      | (have h := congrArg (fun R : Profile 2 => R.r 1) hR; simpa [Profile.rotate,GeneralHessenberg.rightOfSeam,GeneralHessenberg.slice,GeneralHessenberg.sliceEmbedding] using h.symm)
      | (have h := congrArg (fun R : Profile 2 => R.r 2) hR; simpa [Profile.rotate,GeneralHessenberg.rightOfSeam,GeneralHessenberg.slice,GeneralHessenberg.sliceEmbedding] using h.symm)
      | (have h := congrArg (fun R : Profile 1 => R.g 0) hL; simpa [GeneralHessenberg.leftOfSeam,GeneralHessenberg.slice] using h.symm)
      | exact hqz.trans hpz.symm
      | (have h := congrArg (fun R : Profile 2 => R.g 0) hR; simpa [Profile.rotate,GeneralHessenberg.rightOfSeam,GeneralHessenberg.slice] using h.symm)
      | (have h := congrArg (fun R : Profile 2 => R.g 1) hR; simpa [Profile.rotate,GeneralHessenberg.rightOfSeam,GeneralHessenberg.slice] using h.symm)
  · refine ⟨true,false,?_,?_⟩
    all_goals funext i; fin_cases i
    all_goals first
      | (have h := congrArg (fun R : Profile 1 => R.r 0) hL; simpa [Profile.rotate,GeneralHessenberg.leftOfSeam,GeneralHessenberg.slice,GeneralHessenberg.sliceEmbedding] using h.symm)
      | (have h := congrArg (fun R : Profile 1 => R.r 1) hL; simpa [Profile.rotate,GeneralHessenberg.leftOfSeam,GeneralHessenberg.slice,GeneralHessenberg.sliceEmbedding] using h.symm)
      | (have h := congrArg (fun R : Profile 2 => R.r 0) hR; simpa [GeneralHessenberg.rightOfSeam,GeneralHessenberg.slice,GeneralHessenberg.sliceEmbedding] using h.symm)
      | (have h := congrArg (fun R : Profile 2 => R.r 1) hR; simpa [GeneralHessenberg.rightOfSeam,GeneralHessenberg.slice,GeneralHessenberg.sliceEmbedding] using h.symm)
      | (have h := congrArg (fun R : Profile 2 => R.r 2) hR; simpa [GeneralHessenberg.rightOfSeam,GeneralHessenberg.slice,GeneralHessenberg.sliceEmbedding] using h.symm)
      | (have h := congrArg (fun R : Profile 1 => R.g 0) hL; simpa [Profile.rotate,GeneralHessenberg.leftOfSeam,GeneralHessenberg.slice] using h.symm)
      | exact hqz.trans hpz.symm
      | (have h := congrArg (fun R : Profile 2 => R.g 0) hR; simpa [GeneralHessenberg.rightOfSeam,GeneralHessenberg.slice] using h.symm)
      | (have h := congrArg (fun R : Profile 2 => R.g 1) hR; simpa [GeneralHessenberg.rightOfSeam,GeneralHessenberg.slice] using h.symm)
  · refine ⟨true,true,?_,?_⟩
    all_goals funext i; fin_cases i
    all_goals first
      | (have h := congrArg (fun R : Profile 1 => R.r 0) hL; simpa [Profile.rotate,GeneralHessenberg.leftOfSeam,GeneralHessenberg.slice,GeneralHessenberg.sliceEmbedding] using h.symm)
      | (have h := congrArg (fun R : Profile 1 => R.r 1) hL; simpa [Profile.rotate,GeneralHessenberg.leftOfSeam,GeneralHessenberg.slice,GeneralHessenberg.sliceEmbedding] using h.symm)
      | (have h := congrArg (fun R : Profile 2 => R.r 0) hR; simpa [Profile.rotate,GeneralHessenberg.rightOfSeam,GeneralHessenberg.slice,GeneralHessenberg.sliceEmbedding] using h.symm)
      | (have h := congrArg (fun R : Profile 2 => R.r 1) hR; simpa [Profile.rotate,GeneralHessenberg.rightOfSeam,GeneralHessenberg.slice,GeneralHessenberg.sliceEmbedding] using h.symm)
      | (have h := congrArg (fun R : Profile 2 => R.r 2) hR; simpa [Profile.rotate,GeneralHessenberg.rightOfSeam,GeneralHessenberg.slice,GeneralHessenberg.sliceEmbedding] using h.symm)
      | (have h := congrArg (fun R : Profile 1 => R.g 0) hL; simpa [Profile.rotate,GeneralHessenberg.leftOfSeam,GeneralHessenberg.slice] using h.symm)
      | exact hqz.trans hpz.symm
      | (have h := congrArg (fun R : Profile 2 => R.g 0) hR; simpa [Profile.rotate,GeneralHessenberg.rightOfSeam,GeneralHessenberg.slice] using h.symm)
      | (have h := congrArg (fun R : Profile 2 => R.g 1) hR; simpa [Profile.rotate,GeneralHessenberg.rightOfSeam,GeneralHessenberg.slice] using h.symm)

/-- The standing arithmetic parameters of a thick B class. -/
structure BParameters where
  p : ℤ
  m : ℤ
  z : ℤ
  w : ℤ
  z_pos : 1 ≤ z
  w_pos : 1 ≤ w
  p_gt : z+w < p
  m_gt : z+w < m
  p_ne_m : p ≠ m

def BParameters.F (X : BParameters) : Profile 4 :=
  bProfileF X.p X.m X.z X.w (by have := X.z_pos; omega)
    (by have := X.w_pos; omega) X.p_gt X.m_gt

def BParameters.H (X : BParameters) : Profile 4 :=
  bProfileH X.p X.m X.z X.w (by have := X.z_pos; omega)
    (by have := X.w_pos; omega) X.p_gt X.m_gt

/-- Membership in the actual rotation quadruple, not a supplied certificate. -/
def BMember (P : Profile 4) (X : BParameters) : Prop :=
  P = X.F ∨ P = X.F.rotate ∨ P = X.H ∨ P = X.H.rotate

def BRelation (P Q : Profile 4) : Prop :=
  ∃ X : BParameters, BMember P X ∧ BMember Q X

private theorem quartet_member_schur {n : ℕ} (F H P : Profile n)
    (he : F.toBetaDiagram.schur = H.toBetaDiagram.schur)
    (hm : P = F ∨ P = F.rotate ∨ P = H ∨ P = H.rotate) :
    P.toBetaDiagram.schur = F.toBetaDiagram.schur := by
  have he' : F.schur = H.schur := by
    simpa only [Profile.toBetaDiagram_schur] using he
  rcases hm with rfl | rfl | rfl | rfl
  all_goals simp only [Profile.toBetaDiagram_schur,Profile.schur_rotate]
  all_goals first | rfl | exact he'.symm

/-- Every member of the actual B quadruple has the same full Schur polynomial. -/
theorem b_relation_schur_eq {P Q : Profile 4} (h : BRelation P Q) :
    P.toBetaDiagram.schur = Q.toBetaDiagram.schur := by
  obtain ⟨X,hP,hQ⟩ := h
  have he : X.F.toBetaDiagram.schur = X.H.toBetaDiagram.schur :=
    b_profiles_schur_eq X.p X.m X.z X.w _ _ X.p_gt X.m_gt
  exact (quartet_member_schur X.F X.H P he hP).trans
    (quartet_member_schur X.F X.H Q he hQ).symm

private theorem interior_flip_no_four_exception (P Q : Profile 4) (leftRev : Bool)
    (hshape : InteriorFlip P Q leftRev true)
    (hsmall : P.g 1 < P.g 0 ∧ P.g 1 < P.g 2 ∧ P.g 1 < P.g 3)
    (hf : FourRowHessenberg.FamilyRelation
      (GeneralHessenberg.contract P 1) (GeneralHessenberg.contract Q 1)) : False := by
  obtain ⟨w,b,c,hcw,hb,hf⟩ := hf
  have hsub : ((b+w-c : ℕ) : ℤ) = (b : ℤ)+w-c := by omega
  rcases hf with ⟨hF,hH⟩ | ⟨hH,hF⟩
  all_goals rcases hF with hF | hF
  all_goals rcases hH with hH | hH
  all_goals
    have hF0 := congrArg (fun R : Profile 3 => (R.r 0 : ℤ)) hF
    have hF1 := congrArg (fun R : Profile 3 => (R.r 1 : ℤ)) hF
    have hF2 := congrArg (fun R : Profile 3 => (R.r 2 : ℤ)) hF
    have hF3 := congrArg (fun R : Profile 3 => (R.r 3 : ℤ)) hF
    have hFg0 := congrArg (fun R : Profile 3 => R.g 0) hF
    have hFg1 := congrArg (fun R : Profile 3 => R.g 1) hF
    have hFg2 := congrArg (fun R : Profile 3 => R.g 2) hF
    have hH0 := congrArg (fun R : Profile 3 => (R.r 0 : ℤ)) hH
    have hH1 := congrArg (fun R : Profile 3 => (R.r 1 : ℤ)) hH
    have hH2 := congrArg (fun R : Profile 3 => (R.r 2 : ℤ)) hH
    have hH3 := congrArg (fun R : Profile 3 => (R.r 3 : ℤ)) hH
    have hHg0 := congrArg (fun R : Profile 3 => R.g 0) hH
    have hHg1 := congrArg (fun R : Profile 3 => R.g 1) hH
    have hHg2 := congrArg (fun R : Profile 3 => R.g 2) hH
    cases leftRev <;>
      simp [interior_contract_row,interior_contract_gap,hshape.1,hshape.2,
        Profile.rotate,Fin.succAbove,FourRowHessenberg.familyF,FourRowHessenberg.familyH,
        hsub,Nat.cast_add] at hF0 hF1 hF2 hF3 hFg0 hFg1 hFg2 hH0 hH1 hH2 hH3 hHg0 hHg1 hHg2 <;> omega

private theorem interior_flip_reconstruction (P Q : Profile 4)
    (hP : Staircase.Thick P) (hQ : Staircase.Thick Q)
    (leftRev : Bool) (hshape : InteriorFlip P Q leftRev true)
    (hsmall : P.g 1 < P.g 0 ∧ P.g 1 < P.g 2 ∧ P.g 1 < P.g 3)
    (hminpos : 0 < P.g 1)
    (hext : (GeneralHessenberg.contract P 1).toBetaDiagram.schur =
      (GeneralHessenberg.contract Q 1).toBetaDiagram.schur) :
    P = Q ∨ BRelation P Q := by
  have hcp := GeneralHessenberg.contract_thick hP 1
  have hcq := GeneralHessenberg.contract_thick hQ 1
  have he' : (GeneralHessenberg.contract P 1).schur =
      (GeneralHessenberg.contract Q 1).schur := by
    simpa only [Profile.toBetaDiagram_schur] using hext
  have hclass := FourRowHessenberg.hessenberg_classification _ _ hcp.hessenberg hcq.hessenberg he'
  rcases hclass with hdir | hrot | hf
  · have hr0 := congrArg (fun R : Profile 3 => (R.r 0 : ℤ)) hdir
    have hr1 := congrArg (fun R : Profile 3 => (R.r 1 : ℤ)) hdir
    have hr3 := congrArg (fun R : Profile 3 => (R.r 3 : ℤ)) hdir
    have hg1 := congrArg (fun R : Profile 3 => R.g 1) hdir
    simp [interior_contract_row,interior_contract_gap,hshape.1,hshape.2,
      Fin.succAbove] at hr0 hr1 hr3 hg1
    left
    cases leftRev <;> simp at hr0 hr1 hr3 hg1
    all_goals apply Profile.ext
    all_goals funext i; fin_cases i <;> simp [hshape.1,hshape.2] <;> omega
  · have hr0 := congrArg (fun R : Profile 3 => (R.r 0 : ℤ)) hrot
    have hr1 := congrArg (fun R : Profile 3 => (R.r 1 : ℤ)) hrot
    have hr2 := congrArg (fun R : Profile 3 => (R.r 2 : ℤ)) hrot
    have hr3 := congrArg (fun R : Profile 3 => (R.r 3 : ℤ)) hrot
    have hg0 := congrArg (fun R : Profile 3 => R.g 0) hrot
    have hg1 := congrArg (fun R : Profile 3 => R.g 1) hrot
    have hg2 := congrArg (fun R : Profile 3 => R.g 2) hrot
    simp [interior_contract_row,interior_contract_gap,hshape.1,hshape.2,
      Profile.rotate,Fin.succAbove] at hr0 hr1 hr2 hr3 hg0 hg1 hg2
    cases leftRev with
    | false =>
      simp at hr0 hr1 hr2 hr3 hg0 hg1 hg2
      left
      apply Profile.ext
      all_goals funext i; fin_cases i <;> simp [hshape.1,hshape.2] <;> omega
    | true =>
      simp at hr0 hr1 hr2 hr3 hg0 hg1 hg2
      by_cases hsame : P.r 0 = P.r 1
      · left
        apply Profile.ext
        all_goals funext i; fin_cases i <;> simp [hshape.1,hshape.2] <;> omega
      · have hb := hP 0 1 (by rfl)
        have hc := hP 1 2 (by rfl)
        norm_num at hb hc
        let X : BParameters :=
          { p := P.r 0
            m := P.r 1
            z := P.g 0
            w := P.g 1
            z_pos := by omega
            w_pos := by omega
            p_gt := by omega
            m_gt := by omega
            p_ne_m := by omega }
        right
        refine ⟨X,Or.inl ?_,Or.inr (Or.inr (Or.inr ?_))⟩
        · apply Profile.ext
          all_goals funext i; fin_cases i <;>
            simp [X,BParameters.F,bProfileF,profile] <;> omega
        · apply Profile.ext
          all_goals funext i; fin_cases i <;>
            simp [X,BParameters.H,bProfileH,Profile.rotate,profile,
              hshape.1,hshape.2] <;> omega
  · exact False.elim (interior_flip_no_four_exception P Q leftRev hshape hsmall hf)

/-- The unique interior minimum branch has only literal equality and the B
commutation quadruple.  Every cut, contraction, and component reversal is
produced from the actual full Schur equality. -/
theorem interior_minimum_aligned (P Q : Profile 4)
    (hP : Staircase.Thick P) (hQ : Staircase.Thick Q)
    (z : ℕ+) (hmin : ∀ j, z.val ≤ P.g j)
    (huniqueP : ∀ j, P.g j = z.val ↔ j = 1)
    (huniqueQ : ∀ j, Q.g j = z.val ↔ j = 1)
    (he : P.toBetaDiagram.schur = Q.toBetaDiagram.schur) :
    P = Q ∨ BRelation P Q := by
  have hpz := (huniqueP 1).mpr rfl
  have hqz := (huniqueQ 1).mpr rfl
  have hminQ := gap_minimum_preserved P Q z hmin he
  have hcut := congrArg (eraseGenerator z) he
  rw [unique_minimum_cut P hP z hmin 1 huniqueP,
    unique_minimum_cut Q hQ z hminQ 1 huniqueQ] at hcut
  have hmult : complete z.val*(GeneralHessenberg.contract P 1).toBetaDiagram.schur =
      complete z.val*(GeneralHessenberg.contract Q 1).toBetaDiagram.schur := by
    rw [GeneralHessenberg.schur_join_formula P hP 1,
      GeneralHessenberg.schur_join_formula Q hQ 1,hpz,hqz,hcut] at he
    linear_combination -he
  have hext := mul_left_cancel₀ ((complete_ne_zero_iff z.val).mpr (by positivity)) hmult
  have hsmall : P.g 1 < P.g 0 ∧ P.g 1 < P.g 2 ∧ P.g 1 < P.g 3 := by
    have h0 := hmin 0; have h2 := hmin 2; have h3 := hmin 3
    have hn0 : P.g 0 ≠ z.val := fun h => by have := (huniqueP 0).mp h; norm_num at this
    have hn2 : P.g 2 ≠ z.val := fun h => by have := (huniqueP 2).mp h; norm_num at this
    have hn3 : P.g 3 ≠ z.val := fun h => by have := (huniqueP 3).mp h; norm_num at this
    omega
  obtain ⟨leftRev,tailRev,hshape⟩ :=
    interior_minimum_candidates P Q hP hQ z hmin huniqueP huniqueQ he
  cases tailRev with
  | true =>
    exact interior_flip_reconstruction P Q hP hQ leftRev hshape hsmall
      (by have := z.pos; omega) hext
  | false =>
    cases leftRev with
    | false =>
      left
      apply Profile.ext
      all_goals funext i; fin_cases i <;> simp [hshape.1,hshape.2]
    | true =>
      have hswap : FirstTwoExchanged P Q := by
        refine ⟨?_,?_,?_,?_⟩
        · simp [hshape.1]
        · simp [hshape.1]
        · intro i; fin_cases i <;> simp [hshape.1]
        · funext i
          fin_cases i <;> simp [hshape.2]
      have hrows := adjacent_endpoint_exchange P Q hP hQ hswap he
      left
      apply Profile.ext
      all_goals funext i; fin_cases i <;> simp [hshape.1,hshape.2,hrows]

theorem b_relation_symm {P Q : Profile 4} (h : BRelation P Q) : BRelation Q P := by
  obtain ⟨X,hP,hQ⟩ := h
  exact ⟨X,hQ,hP⟩

private theorem b_member_unrotate {P : Profile 4} {X : BParameters}
    (h : BMember P.rotate X) : BMember P X := by
  rcases h with h | h | h | h
  · right; left
    have hh := congrArg Profile.rotate h
    simpa using hh
  · left
    have hh := congrArg Profile.rotate h
    simpa using hh
  · right; right; right
    have hh := congrArg Profile.rotate h
    simpa using hh
  · right; right; left
    have hh := congrArg Profile.rotate h
    simpa using hh

theorem b_relation_rotate_right {P Q : Profile 4} (h : BRelation P Q.rotate) :
    BRelation P Q := by
  obtain ⟨X,hP,hQ⟩ := h
  exact ⟨X,hP,b_member_unrotate hQ⟩

theorem b_relation_rotate_left {P Q : Profile 4} (h : BRelation P.rotate Q) :
    BRelation P Q :=
  b_relation_symm (b_relation_rotate_right (b_relation_symm h))

/-- Full unique-interior-minimum classification against arbitrary thick
five-row mates, without an assumed mate seam position. -/
theorem interior_minimum_rigidity (P Q : Profile 4)
    (hP : Staircase.Thick P) (hQ : Staircase.Thick Q)
    (z : ℕ+) (hmin : ∀ j, z.val ≤ P.g j)
    (hunique : ∀ j, P.g j = z.val ↔ j = 1)
    (he : P.toBetaDiagram.schur = Q.toBetaDiagram.schur) :
    P = Q ∨ P = Q.rotate ∨ BRelation P Q := by
  obtain ⟨d,huniqQ,hpos⟩ := unique_minimum_placement P Q hP hQ z hmin 1 hunique he
  have hd : d = 1 ∨ d = 2 := by
    rcases hpos with hpos | hpos
    · exact Or.inl hpos.symm
    · right; apply Fin.ext; omega
  rcases hd with rfl | rfl
  · rcases interior_minimum_aligned P Q hP hQ z hmin hunique huniqQ he with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  · have huniqQr : ∀ j, Q.rotate.g j = z.val ↔ j = 1 := by
      intro j
      change Q.g j.rev = z.val ↔ j = 1
      rw [huniqQ]
      fin_cases j <;> decide
    have he' : P.toBetaDiagram.schur = Q.rotate.toBetaDiagram.schur := by
      simpa only [Profile.toBetaDiagram_schur,Profile.schur_rotate] using he
    rcases interior_minimum_aligned P Q.rotate hP (thick_rotate hQ)
        z hmin hunique huniqQr he' with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (b_relation_rotate_right h))

/-- Complete minimum-multiplicity-one branch, with both necessity and
sufficiency and every permitted component reversal retained. -/
theorem one_minimum_full_class (P Q : Profile 4)
    (hP : Staircase.Thick P) (hQ : Staircase.Thick Q)
    (z : ℕ+) (hmin : ∀ j, z.val ≤ P.g j)
    (hm : Staircase.minimumMultiplicity P z = 1) :
    P.toBetaDiagram.schur = Q.toBetaDiagram.schur ↔
      P = Q ∨ P = Q.rotate ∨ BRelation P Q := by
  constructor
  · intro he
    have hcard : (Finset.univ.filter (fun j => P.g j = z.val)).card = 1 := by
      rw [Finset.card_filter]
      exact hm
    obtain ⟨c,hc⟩ := Finset.card_eq_one.mp hcard
    have huniq : ∀ j, P.g j = z.val ↔ j = c := by
      intro j
      have hi : j ∈ Finset.univ.filter (fun j => P.g j = z.val) ↔ j ∈ ({c} : Finset (Fin 4)) := by rw [hc]
      simpa only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton] using hi
    fin_cases c
    · have hminR : ∀ j, z.val ≤ P.rotate.g j := fun j => hmin j.rev
      have huniqR : ∀ j, P.rotate.g j = z.val ↔ j = 3 := by
        intro j
        change P.g j.rev = z.val ↔ j = 3
        rw [huniq]
        fin_cases j <;> decide
      have heR : P.rotate.toBetaDiagram.schur = Q.toBetaDiagram.schur := by
        simpa only [Profile.toBetaDiagram_schur,Profile.schur_rotate] using he
      rcases terminal_minimum_rigidity P.rotate Q (thick_rotate hP) hQ z hminR huniqR heR with h | h
      · right; left; simpa using congrArg Profile.rotate h
      · left; simpa using congrArg Profile.rotate h
    · exact interior_minimum_rigidity P Q hP hQ z hmin huniq he
    · have hminR : ∀ j, z.val ≤ P.rotate.g j := fun j => hmin j.rev
      have huniqR : ∀ j, P.rotate.g j = z.val ↔ j = 1 := by
        intro j
        change P.g j.rev = z.val ↔ j = 1
        rw [huniq]
        fin_cases j <;> decide
      have heR : P.rotate.toBetaDiagram.schur = Q.toBetaDiagram.schur := by
        simpa only [Profile.toBetaDiagram_schur,Profile.schur_rotate] using he
      rcases interior_minimum_rigidity P.rotate Q (thick_rotate hP) hQ z hminR huniqR heR with h | h | h
      · right; left; simpa using congrArg Profile.rotate h
      · left; simpa using congrArg Profile.rotate h
      · right; right; exact b_relation_rotate_left h
    · rcases terminal_minimum_rigidity P Q hP hQ z hmin huniq he with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  · rintro (rfl | h | h)
    · rfl
    · rw [h,Profile.toBetaDiagram_schur,Profile.toBetaDiagram_schur,Profile.schur_rotate]
    · exact b_relation_schur_eq h

/-- The third ordered allocation has this complete q-erased layer difference. -/
theorem interior_t3_defect {R : Type*} [CommRing R] (h : ℤ → R)
    (p m t q z : ℤ) (hq : h q = 0) :
    interiorLayer h p m p m t q z-interiorLayer h m p m t p q z =
      h (p+m-z)*(h (p+m-z)*h t-h m*h (p+t-z)) := by
  unfold interiorLayer two
  simp only [hq,zero_mul,sub_zero]
  ring_nf <;> ring

theorem erase_interiorLayer (v : ℕ+) (a b c d e q z : ℤ) :
    eraseGenerator v (interiorLayer complete a b c d e q z) =
      interiorLayer (fun k => eraseGenerator v (complete k)) a b c d e q z := by
  unfold interiorLayer two
  simp only [map_add,map_mul,map_sub]

theorem erase_complete_of_lt (v : ℕ+) (k : ℤ) (hk : (v.val : ℤ) < k) :
    eraseGenerator v (complete k) = complete k := by
  rw [eraseGenerator_complete,if_neg (by omega)]

/-- The surviving ordered allocation forces the exact commutation row,
without excluding any contact of the remaining row with q. -/
theorem interior_t2_iff (p m t q z : ℤ) (hz : 1 ≤ z) (hzq : z < q)
    (hp : q+z < p) (hm : q+z < m) (ht : 2*z < t) (hpm : p ≠ m) :
    interiorLayer complete p m p t m q z =
      interiorLayer complete m p m t p q z ↔ t = p+m-q := by
  have hkey := interior_t2_defect complete p m t q z
  constructor
  · intro he
    rw [he,sub_self] at hkey
    have hbr := (mul_eq_zero.mp hkey.symm).resolve_left
      ((complete_ne_zero_iff q).mpr (by omega))
    have hprod := sub_eq_zero.mp hbr
    rcases complete_two_product_reading (by omega) (by omega) (by omega) (by omega)
      hprod with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · exact (hpm (by omega)).elim
    · omega
  · intro ht'
    have hzero : complete (p+2*m-q-z)*complete (p+t-z)-
        complete (2*p+m-q-z)*complete (m+t-z) = 0 := by
      rw [show p+t-z = 2*p+m-q-z by omega,show m+t-z = p+2*m-q-z by omega]
      ring
    exact sub_eq_zero.mp (by rw [interior_t2_defect,hzero,mul_zero])

/-- The first ordered allocation cannot survive actual q-erasure. -/
theorem t1_erased_ne_zero (p m t q z : ℤ) (v : ℕ+) (hv : (v.val : ℤ) = q)
    (hz : 1 ≤ z) (hzq : z < q) (hp : q+z < p) (hm : q+z < m)
    (ht : z < t) (hpm : p ≠ m) :
    eraseGenerator v (interiorLayer complete p m p m t q z-
      interiorLayer complete m p m p t q z) ≠ 0 := by
  have hq0 : (fun k => eraseGenerator v (complete k)) q = 0 := by
    change eraseGenerator v (complete q) = 0
    rw [eraseGenerator_complete,if_pos hv.symm]
  rw [map_sub,erase_interiorLayer,erase_interiorLayer,
    interior_t1_defect (fun k => eraseGenerator v (complete k)) p m t q z hq0]
  rw [erase_complete_of_lt v (p+m-z) (by omega),erase_complete_of_lt v p (by omega),
    erase_complete_of_lt v (m+t-z) (by omega),erase_complete_of_lt v m (by omega),
    erase_complete_of_lt v (p+t-z) (by omega)]
  refine mul_ne_zero ((complete_ne_zero_iff (p+m-z)).mpr (by omega)) ?_
  intro hb
  have hprod := sub_eq_zero.mp hb
  rcases complete_two_product_reading (by omega) (by omega) (by omega) (by omega)
    hprod with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> omega

theorem t3_erased_defect (p m t q z : ℤ) (v : ℕ+) (hv : (v.val : ℤ) = q) :
    eraseGenerator v (interiorLayer complete p m p m t q z-
      interiorLayer complete m p m t p q z) =
      eraseGenerator v (complete (p+m-z))*
        (eraseGenerator v (complete (p+m-z))*eraseGenerator v (complete t)-
          eraseGenerator v (complete m)*eraseGenerator v (complete (p+t-z))) := by
  have hq0 : (fun k => eraseGenerator v (complete k)) q = 0 := by
    change eraseGenerator v (complete q) = 0
    rw [eraseGenerator_complete,if_pos hv.symm]
  rw [map_sub,erase_interiorLayer,erase_interiorLayer]
  exact interior_t3_defect (fun k => eraseGenerator v (complete k)) p m t q z hq0

/-- The third allocation's erased equality forces t=m.  The contact t=q
is retained and contradicted by its nonzero surviving monomial. -/
theorem t3_erased_eq_imp (p m t q z : ℤ) (v : ℕ+) (hv : (v.val : ℤ) = q)
    (hz : 1 ≤ z) (hzq : z < q) (hp : q+z < p) (hm : q+z < m) (ht : 2*z < t)
    (heq : eraseGenerator v (interiorLayer complete p m p m t q z) =
      eraseGenerator v (interiorLayer complete m p m t p q z)) : t = m := by
  have hd : eraseGenerator v (interiorLayer complete p m p m t q z-
      interiorLayer complete m p m t p q z) = 0 := by
    rw [map_sub,heq,sub_self]
  rw [t3_erased_defect p m t q z v hv,
    erase_complete_of_lt v (p+m-z) (by omega),erase_complete_of_lt v m (by omega),
    erase_complete_of_lt v (p+t-z) (by omega)] at hd
  by_cases htq : t = q
  · have ht0 : eraseGenerator v (complete t) = 0 := by
      rw [eraseGenerator_complete,if_pos (by omega)]
    rw [ht0,mul_zero,zero_sub] at hd
    have hb := (mul_eq_zero.mp hd).resolve_left
      ((complete_ne_zero_iff (p+m-z)).mpr (by omega))
    exact False.elim ((mul_ne_zero ((complete_ne_zero_iff m).mpr (by omega))
      ((complete_ne_zero_iff (p+t-z)).mpr (by omega))) (neg_eq_zero.mp hb))
  · have htv : eraseGenerator v (complete t) = complete t := by
      rw [eraseGenerator_complete,if_neg (by omega)]
    rw [htv] at hd
    have hb := (mul_eq_zero.mp hd).resolve_left
      ((complete_ne_zero_iff (p+m-z)).mpr (by omega))
    have hprod := sub_eq_zero.mp hb
    rcases complete_two_product_reading (by omega) (by omega) (by omega) (by omega)
      hprod with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · omega
    · exact h2

/-- First minimum-layer comparison for the first P/R singleton allocation. -/
noncomputable def a2FirstComparison (a b c d e q z : ℤ) : CompleteRing :=
  complete (a+b-z)*threeInterval complete c d e q q+
  complete a*threeInterval complete (b+c-z) d e q q-
  complete b*threeInterval complete e d e q q-
  complete a*threeInterval complete c d (e+b-z) q q

/-- The two candidates for the largest first-layer index are retained
together at their tie, with no restriction on lower label collisions. -/
theorem a2_first_derivative (a b c d e q z : ℤ)
    (hz : 1 ≤ z) (hq : z < q) (ha : z < a) (hb : z < b)
    (hc : q+z < c) (hd : 2*q < d) (he : e = a+c-z)
    (v : ℕ+) (hv : (v.val : ℤ) = max (2*e+d-2*q) (d+e+b-z-q)) :
    MvPolynomial.pderiv v (a2FirstComparison a b c d e q z) =
      if 2*e+d-2*q < d+e+b-z-q then complete a*complete c*complete q
      else if d+e+b-z-q < 2*e+d-2*q then -(complete b*complete q*complete q)
      else complete q*(complete a*complete c-complete b*complete q) := by
  unfold a2FirstComparison threeInterval
  ring_nf
  rcases lt_trichotomy (2*e+d-2*q) (d+e+b-z-q) with hlt | heq | hgt
  · rw [max_eq_right hlt.le] at hv
    simp (disch := omega) [map_add,map_sub,map_neg,MvPolynomial.pderiv_mul,
      MvPolynomial.pderiv_pow,Staircase.residual_pderiv_complete,hv,if_pos,if_neg]
    <;> ring
  · rw [heq,max_self] at hv
    simp (disch := omega) [map_add,map_sub,map_neg,MvPolynomial.pderiv_mul,
      MvPolynomial.pderiv_pow,Staircase.residual_pderiv_complete,hv,if_pos,if_neg]
    <;> ring
  · rw [max_eq_left hgt.le] at hv
    simp (disch := omega) [map_add,map_sub,map_neg,MvPolynomial.pderiv_mul,
      MvPolynomial.pderiv_pow,Staircase.residual_pderiv_complete,hv,if_pos,if_neg]
    <;> ring

/-- The actual first layer forces the endpoint contact and the repeated row
in the P/R comparison.  It does not assume a specialized primitive class. -/
theorem a2_first_condition (a b c d e q z : ℤ)
    (hz : 1 ≤ z) (hq : z < q) (ha : z < a) (hb : z < b)
    (hc : q+z < c) (hd : 2*q < d) (he : e = a+c-z)
    (hG : a2FirstComparison a b c d e q z = 0) : a = q ∧ c = b := by
  let L := max (2*e+d-2*q) (d+e+b-z-q)
  let v : ℕ+ := ⟨L.toNat, by
    dsimp [L]; have := le_max_left (2*e+d-2*q) (d+e+b-z-q); omega⟩
  have hv : (v.val : ℤ) = L := by
    dsimp [v,L]; have := le_max_left (2*e+d-2*q) (d+e+b-z-q); omega
  have hzero := congrArg (MvPolynomial.pderiv v) hG
  rw [a2_first_derivative a b c d e q z hz hq ha hb hc hd he v hv,map_zero] at hzero
  split_ifs at hzero
  · exact False.elim ((mul_ne_zero
      (mul_ne_zero ((complete_ne_zero_iff a).mpr (by omega))
        ((complete_ne_zero_iff c).mpr (by omega)))
      ((complete_ne_zero_iff q).mpr (by omega))) hzero)
  · exact False.elim ((neg_ne_zero.mpr (mul_ne_zero
      (mul_ne_zero ((complete_ne_zero_iff b).mpr (by omega))
        ((complete_ne_zero_iff q).mpr (by omega)))
      ((complete_ne_zero_iff q).mpr (by omega)))) hzero)
  · have hbr := (mul_eq_zero.mp hzero).resolve_left
      ((complete_ne_zero_iff q).mpr (by omega))
    have hprod := sub_eq_zero.mp hbr
    rcases complete_two_product_reading (by omega) (by omega) (by omega) (by omega)
      hprod with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · omega
    · exact ⟨h1,h2⟩

/-- The second P/R singleton allocation has a private shifted three-row
interval and therefore cannot satisfy its full first minimum-layer equation. -/
theorem a2_second_condition_ne_zero (a b c d e q z : ℤ)
    (hz : 1 ≤ z) (hq : z < q) (ha : z < a) (hb : z < b)
    (hc : q+z < c) (hd : 2*q < d) (he : e = b+c-z) :
    complete (a+b-z)*threeInterval complete c d e q q-
      complete b*threeInterval complete c d (e+a-z) q q ≠ 0 := by
  let v : ℕ+ := ⟨(c+d+e+a-z-2*q).toNat,by omega⟩
  have hv : (v.val : ℤ) = c+d+e+a-z-2*q := by dsimp [v]; omega
  have hderiv :
      MvPolynomial.pderiv v
        (complete (a+b-z)*threeInterval complete c d e q q-
          complete b*threeInterval complete c d (e+a-z) q q) =
      -(complete b*complete q*complete q) := by
    unfold threeInterval
    simp (disch := omega) [map_add,map_sub,map_neg,MvPolynomial.pderiv_mul,
      Staircase.residual_pderiv_complete,hv,if_pos,if_neg]
    <;> ring
  intro hG
  have hzero := congrArg (MvPolynomial.pderiv v) hG
  rw [hderiv,map_zero] at hzero
  exact (neg_ne_zero.mpr (mul_ne_zero
    (mul_ne_zero ((complete_ne_zero_iff b).mpr (by omega))
      ((complete_ne_zero_iff q).mpr (by omega)))
    ((complete_ne_zero_iff q).mpr (by omega)))) hzero

/-- Marking a generator in the actual five-row determinant preserves every
numerical index, including contacts and repeated indices. -/
theorem five_marked_interval (P : Gluing.Profile 4) (hP : P.Hessenberg) (z : ℕ+) :
    Staircase.minimumPolynomial z P.toBetaDiagram.schur =
      interval (fun k => if k = (z.val : ℤ) then Polynomial.X else
        Polynomial.C (complete k))
        (P.r 0) (P.r 1) (P.r 2) (P.r 3) (P.r 4)
        (P.g 0) (P.g 1) (P.g 2) (P.g 3) := by
  rw [Gluing.Profile.toBetaDiagram_schur,schur_interval P hP]
  simp only [interval,← complete_eq_hh,map_add,map_sub,map_mul,
    Staircase.minimumPolynomial_complete]

/-- All three minimum-generator layers of the P placement. -/
theorem a2_P_marked (a b c d e q : ℤ) (z : ℕ+)
    (hq : (z.val : ℤ) < q)
    (hDom : Domain a b c d e z.val z.val q q) :
    Staircase.minimumPolynomial z (interval complete a b c d e z.val z.val q q) =
      Polynomial.C (complete a*complete b*threeInterval complete c d e q q)+
      Polynomial.X*Polynomial.C
        (-(complete (a+b-z.val)*threeInterval complete c d e q q+
          complete a*threeInterval complete (b+c-z.val) d e q q))+
      Polynomial.X^2*Polynomial.C
        (threeInterval complete (a+b+c-2*z.val) d e q q) := by
  rcases hDom with ⟨hz0,_,hq0,_,ha,hb,hc,hd,he⟩
  have hz := z.pos
  simp (disch := omega) [interval,threeInterval,map_add,map_sub,map_mul,map_neg,
    Staircase.minimumPolynomial_complete,if_pos,if_neg]
  <;> ring_nf

/-- The R placement's three exact minimum-generator layers. -/
theorem a2_R_marked (a b c d e q : ℤ) (z : ℕ+)
    (hq : (z.val : ℤ) < q)
    (hDom : Domain a b c d e z.val q q z.val) :
    Staircase.minimumPolynomial z (interval complete a b c d e z.val q q z.val) =
      Polynomial.C (complete a*threeInterval complete b c d q q*complete e)+
      Polynomial.X*Polynomial.C
        (-(threeInterval complete (a+b-z.val) c d q q*complete e+
          complete a*threeInterval complete b c (d+e-z.val) q q))+
      Polynomial.X^2*Polynomial.C
        (threeInterval complete (a+b-z.val) c (d+e-z.val) q q) := by
  rcases hDom with ⟨hz0,hq0,_,_,ha,hb,hc,hd,he⟩
  have hz := z.pos
  simp (disch := omega) [interval,threeInterval,map_add,map_sub,map_mul,map_neg,
    Staircase.minimumPolynomial_complete,if_pos,if_neg]
  <;> ring_nf

/-- Actual first minimum coefficient in the P placement. -/
theorem a2_P_first (a b c d e q : ℤ) (z : ℕ+)
    (hq : (z.val : ℤ) < q)
    (hDom : Domain a b c d e z.val z.val q q) :
    Staircase.firstCoefficient z (interval complete a b c d e z.val z.val q q) =
      -(complete (a+b-z.val)*threeInterval complete c d e q q+
        complete a*threeInterval complete (b+c-z.val) d e q q) := by
  have h := congrArg (fun f : Polynomial CompleteRing => f.coeff 1)
    (a2_P_marked a b c d e q z hq hDom)
  rw [Staircase.minimumPolynomial_coeff_one] at h
  norm_num at h
  simpa using h

theorem a2_R_first (a b c d e q : ℤ) (z : ℕ+)
    (hq : (z.val : ℤ) < q)
    (hDom : Domain a b c d e z.val q q z.val) :
    Staircase.firstCoefficient z (interval complete a b c d e z.val q q z.val) =
      -(threeInterval complete (a+b-z.val) c d q q*complete e+
        complete a*threeInterval complete b c (d+e-z.val) q q) := by
  have h := congrArg (fun f : Polynomial CompleteRing => f.coeff 1)
    (a2_R_marked a b c d e q z hq hDom)
  rw [Staircase.minimumPolynomial_coeff_one] at h
  norm_num at h
  simpa using h

theorem a2_P_top (a b c d e q : ℤ) (z : ℕ+)
    (hq : (z.val : ℤ) < q)
    (hDom : Domain a b c d e z.val z.val q q) :
    (Staircase.minimumPolynomial z
      (interval complete a b c d e z.val z.val q q)).coeff 2 =
      threeInterval complete (a+b+c-2*z.val) d e q q := by
  have h := congrArg (fun f : Polynomial CompleteRing => f.coeff 2)
    (a2_P_marked a b c d e q z hq hDom)
  norm_num at h
  simpa using h

theorem a2_R_top (a b c d e q : ℤ) (z : ℕ+)
    (hq : (z.val : ℤ) < q)
    (hDom : Domain a b c d e z.val q q z.val) :
    (Staircase.minimumPolynomial z
      (interval complete a b c d e z.val q q z.val)).coeff 2 =
      threeInterval complete (a+b-z.val) c (d+e-z.val) q q := by
  have h := congrArg (fun f : Polynomial CompleteRing => f.coeff 2)
    (a2_R_marked a b c d e q z hq hDom)
  norm_num at h
  simpa using h

/-- The complete-generator expansion of an actual three-row thick profile. -/
theorem schur_three_complete (P : Gluing.Profile 2)
    (hP : P.g 0+P.g 1 < P.r 1) :
    P.toBetaDiagram.schur = threeInterval complete (P.r 0) (P.r 1) (P.r 2)
      (P.g 0) (P.g 1) := by
  have hm : (Matrix.of fun i j : Fin 3 => hh (P.xi i-P.zeta j)) =
      (threeIndices (P.r 0) (P.r 1) (P.r 2) (P.g 0) (P.g 1)).map hh := by
    rw [← P.indices_three]
    rfl
  rw [Gluing.Profile.toBetaDiagram_schur,Gluing.Profile.schur,hm,
    three_indices_det hh (fun k hk => hh_of_neg hk) _ _ _ _ _
      (by exact_mod_cast hP)]
  simp only [threeInterval,complete_eq_hh]

private def threeConstantProfile (a b c q : ℤ) (hq : 0 ≤ q)
    (ha : q < a) (hb : 2*q < b) (hc : q < c) : Gluing.Profile 2 where
  r i := (![a,b,c] i).toNat
  g _ := q.toNat
  r_pos := by intro i; fin_cases i <;> simp <;> omega
  g_lt_castSucc := by intro j; fin_cases j <;> simp <;> omega
  g_lt_succ := by intro j; fin_cases j <;> simp <;> omega

private theorem threeConstantProfile_schur (a b c q : ℤ) (hq : 0 ≤ q)
    (ha : q < a) (hb : 2*q < b) (hc : q < c) :
    (threeConstantProfile a b c q hq ha hb hc).toBetaDiagram.schur =
      threeInterval complete a b c q q := by
  have hra : ((a.toNat : ℕ) : ℤ) = a := by omega
  have hrb : ((b.toNat : ℕ) : ℤ) = b := by omega
  have hrc : ((c.toNat : ℕ) : ℤ) = c := by omega
  have hrq : ((q.toNat : ℕ) : ℤ) = q := by omega
  rw [schur_three_complete _ (by simp [threeConstantProfile]; omega)]
  simp [threeConstantProfile,hra,hrb,hrc,hrq]

/-- Constant-gap three-row equality is actual profile equality or reversal,
including all repeated row lengths and all numerical interval contacts. -/
theorem three_constant_rigidity (a b c A B C q : ℤ) (hq : 0 ≤ q)
    (ha : q < a) (hb : 2*q < b) (hc : q < c)
    (hA : q < A) (hB : 2*q < B) (hC : q < C)
    (he : threeInterval complete a b c q q = threeInterval complete A B C q q) :
    (a = A ∧ b = B ∧ c = C) ∨ (a = C ∧ b = B ∧ c = A) := by
  let P := threeConstantProfile a b c q hq ha hb hc
  let Q := threeConstantProfile A B C q hq hA hB hC
  have he' : P.toBetaDiagram.schur = Q.toBetaDiagram.schur := by
    rw [threeConstantProfile_schur,threeConstantProfile_schur]
    exact he
  have h := small_profile_rigidity P Q (by decide) he'
  rcases h with h | h
  · have h0 := congrArg (fun R : Gluing.Profile 2 => (R.r 0 : ℤ)) h
    have h1 := congrArg (fun R : Gluing.Profile 2 => (R.r 1 : ℤ)) h
    have h2 := congrArg (fun R : Gluing.Profile 2 => (R.r 2 : ℤ)) h
    simp [P,Q,threeConstantProfile] at h0 h1 h2
    left
    exact ⟨by omega,by omega,by omega⟩
  · have h0 := congrArg (fun R : Gluing.Profile 2 => (R.r 0 : ℤ)) h
    have h1 := congrArg (fun R : Gluing.Profile 2 => (R.r 1 : ℤ)) h
    have h2 := congrArg (fun R : Gluing.Profile 2 => (R.r 2 : ℤ)) h
    simp [P,Q,threeConstantProfile,Gluing.Profile.rotate] at h0 h1 h2
    right
    exact ⟨by omega,by omega,by omega⟩

/-- The first P/R singleton allocation is exactly A2 on its entire actual
profile domain.  Necessity uses the top and first minimum layers. -/
theorem a2_H1_polynomial_iff (a b c d e q : ℤ) (z : ℕ+)
    (hq : (z.val : ℤ) < q)
    (hF : Domain a b c d e z.val z.val q q)
    (hH : Domain a c d e b z.val q q z.val) :
    interval complete a b c d e z.val z.val q q =
      interval complete a c d e b z.val q q z.val ↔
      a = q ∧ c = b ∧ d = b+q-z.val ∧ e = b+q-z.val := by
  have hz := z.pos
  have ha : (z.val : ℤ) < a := hF.2.2.2.2.1
  have hb : 2*(z.val : ℤ) < b := by have := hF.2.2.2.2.2.1; omega
  have hc : q+z.val < c := by have := hF.2.2.2.2.2.2.1; omega
  have hd : 2*q < d := by have := hF.2.2.2.2.2.2.2.1; omega
  have heq : q+z.val < e := by have := hH.2.2.2.2.2.2.2.1; omega
  constructor
  · intro he
    have htop := congrArg (fun p : CompleteRing => (Staircase.minimumPolynomial z p).coeff 2) he
    rw [a2_P_top a b c d e q z hq hF,a2_R_top a c d e b q z hq hH] at htop
    have hrows := three_constant_rigidity
      (a+b+c-2*z.val) d e (a+c-z.val) d (e+b-z.val) q (by omega)
      (by omega) hd (by omega) (by omega) hd (by omega) htop
    have hrel : e = a+c-z.val := by
      rcases hrows with ⟨h0,h1,h2⟩ | ⟨h0,h1,h2⟩
      · omega
      · exact h2
    have hfirst := congrArg (Staircase.firstCoefficient z) he
    rw [a2_P_first a b c d e q z hq hF,a2_R_first a c d e b q z hq hH] at hfirst
    rw [← hrel] at hfirst
    have hG : a2FirstComparison a b c d e q z.val = 0 := by
      unfold a2FirstComparison
      linear_combination -hfirst
    obtain ⟨haq,hcb⟩ := a2_first_condition a b c d e q z.val (by exact_mod_cast hz)
      hq ha (by omega) hc hd hrel hG
    have heu : e = b+q-z.val := by omega
    have heNormalized : interval complete q b b d (b+q-z.val) z.val z.val q q =
        interval complete q b d (b+q-z.val) b z.val q q z.val := by
      simpa only [haq,hcb,heu] using he
    have hdu : d = b+q-z.val :=
      (a2_remaining_row_iff q b d z.val (by exact_mod_cast hz) hq (by omega) hd).mp heNormalized
    exact ⟨haq,hcb,hdu,heu⟩
  · rintro ⟨haq,hcb,hd',he'⟩
    rw [haq,hcb,hd',he']
    exact a2_identity complete q b z.val

/-- The second P/R singleton allocation is uniformly impossible, including
the endpoint-contact and all top-index tie boundaries. -/
theorem a2_H2_polynomial_ne (a b c d e q : ℤ) (z : ℕ+)
    (hq : (z.val : ℤ) < q)
    (hF : Domain a b c d e z.val z.val q q)
    (hH : Domain b c d e a z.val q q z.val) :
    interval complete a b c d e z.val z.val q q ≠
      interval complete b c d e a z.val q q z.val := by
  have hz := z.pos
  have ha : (z.val : ℤ) < a := hF.2.2.2.2.1
  have hb : 2*(z.val : ℤ) < b := by have := hF.2.2.2.2.2.1; omega
  have hc : q+z.val < c := by have := hF.2.2.2.2.2.2.1; omega
  have hd : 2*q < d := by have := hF.2.2.2.2.2.2.2.1; omega
  have heq : q+z.val < e := by have := hH.2.2.2.2.2.2.2.1; omega
  intro he
  have htop := congrArg (fun p : CompleteRing => (Staircase.minimumPolynomial z p).coeff 2) he
  rw [a2_P_top a b c d e q z hq hF,a2_R_top b c d e a q z hq hH] at htop
  have hrows := three_constant_rigidity
    (a+b+c-2*z.val) d e (b+c-z.val) d (e+a-z.val) q (by omega)
    (by omega) hd (by omega) (by omega) hd (by omega) htop
  have hrel : e = b+c-z.val := by
    rcases hrows with ⟨h0,h1,h2⟩ | ⟨h0,h1,h2⟩
    · omega
    · exact h2
  have hfirst := congrArg (Staircase.firstCoefficient z) he
  rw [a2_P_first a b c d e q z hq hF,a2_R_first b c d e a q z hq hH] at hfirst
  apply a2_second_condition_ne_zero a b c d e q z.val (by exact_mod_cast hz)
    hq ha (by omega) hc hd hrel
  linear_combination -hfirst

/-- The normalized A2 allocation comparison is a full actual determinant
statement, not just a comparison of its layers. -/
theorem a2_H1_profile_iff (a b c d e q : ℤ) (z : ℕ+)
    (hq : (z.val : ℤ) < q)
    (hF : Domain a b c d e z.val z.val q q)
    (hH : Domain a c d e b z.val q q z.val) :
    (profile a b c d e z.val z.val q q hF).toBetaDiagram.schur =
      (profile a c d e b z.val q q z.val hH).toBetaDiagram.schur ↔
      a = q ∧ c = b ∧ d = b+q-z.val ∧ e = b+q-z.val := by
  rw [profile_schur,profile_schur]
  simpa only [interval,complete_eq_hh] using a2_H1_polynomial_iff a b c d e q z hq hF hH

private theorem one_connected (D : BetaDiagram 1) : D.Connected := by
  refine ⟨by decide,?_⟩
  intro i hi
  have := i.isLt
  omega

/-- A three-row irreducible factor cannot match either singleton in a
singleton/triple/singleton safe cut.  The two remaining singletons are
recovered without ordering or distinctness assumptions. -/
theorem singleton_triple_factor_reading (A B D F : BetaDiagram 1) (C E : BetaDiagram 3)
    (hC : C.Connected) (hE : E.Connected)
    (he : A.schur*B.schur*C.schur = D.schur*E.schur*F.schur) :
    C.schur = E.schur ∧
      ((A.schur = D.schur ∧ B.schur = F.schur) ∨
       (A.schur = F.schur ∧ B.schur = D.schur)) := by
  have hCi := C.schur_irreducible hC
  have hCp := UniqueFactorizationMonoid.irreducible_iff_prime.mp hCi
  have hdiv : C.schur ∣ D.schur*E.schur*F.schur := by
    rw [← he]
    refine ⟨A.schur*B.schur,?_⟩
    ring
  have hCE : C.schur = E.schur := by
    rcases hCp.dvd_or_dvd hdiv with hDE | hCF
    · rcases hCp.dvd_or_dvd hDE with hCD | hCE
      · have hp := full_schur_associated_eq C D
          (hCi.associated_of_dvd (D.schur_irreducible (one_connected D)) hCD)
        have hn := C.row_count_of_schur_eq D hp
        norm_num at hn
      · exact full_schur_associated_eq C E
          (hCi.associated_of_dvd (E.schur_irreducible hE) hCE)
    · have hp := full_schur_associated_eq C F
        (hCi.associated_of_dvd (F.schur_irreducible (one_connected F)) hCF)
      have hn := C.row_count_of_schur_eq F hp
      norm_num at hn
  have hends : A.schur*B.schur = D.schur*F.schur := by
    apply mul_right_cancel₀ C.schur_ne_zero
    rw [he,← hCE]
    ring
  exact ⟨hCE,connected_two_factor_reading A B D F
    (one_connected A) (one_connected B) (one_connected D) (one_connected F) hends⟩

private def scalarSingleton (a : ℤ) (ha : 0 < a) : Gluing.Profile 0 where
  r _ := a.toNat
  g j := Fin.elim0 j
  r_pos _ := by omega
  g_lt_castSucc j := Fin.elim0 j
  g_lt_succ j := Fin.elim0 j

private theorem scalarSingleton_schur (a : ℤ) (ha : 0 < a) :
    (scalarSingleton a ha).toBetaDiagram.schur = complete a := by
  rw [Gluing.Profile.toBetaDiagram_schur,Gluing.Profile.schur_single_interval]
  have hc : ((a.toNat : ℕ) : ℤ) = a := by omega
  simpa only [scalarSingleton,hc] using (complete_eq_hh a).symm

/-- Full zero-layer factorization recovers the middle triple and the two
singletons of the P/R comparison, including repeated singleton lengths. -/
theorem a2_zero_layer_reading (a b c d e A B C D E q : ℤ)
    (ha : 0 < a) (hb : 0 < b) (hA : 0 < A) (hE : 0 < E) (hq : 0 ≤ q)
    (hc : q < c) (hd : 2*q < d) (he : q < e)
    (hB : q < B) (hC : 2*q < C) (hD : q < D)
    (hzero : complete a*complete b*threeInterval complete c d e q q =
      complete A*threeInterval complete B C D q q*complete E) :
    ((c = B ∧ d = C ∧ e = D) ∨ (c = D ∧ d = C ∧ e = B)) ∧
      ((a = A ∧ b = E) ∨ (a = E ∧ b = A)) := by
  let aP := (scalarSingleton a ha).toBetaDiagram
  let bP := (scalarSingleton b hb).toBetaDiagram
  let AP := (scalarSingleton A hA).toBetaDiagram
  let EP := (scalarSingleton E hE).toBetaDiagram
  let cP := (threeConstantProfile c d e q hq hc hd he).toBetaDiagram
  let CP := (threeConstantProfile B C D q hq hB hC hD).toBetaDiagram
  have hpoly : aP.schur*bP.schur*cP.schur = AP.schur*CP.schur*EP.schur := by
    rw [scalarSingleton_schur,scalarSingleton_schur,scalarSingleton_schur,
      scalarSingleton_schur,threeConstantProfile_schur,threeConstantProfile_schur]
    exact hzero
  obtain ⟨hcore,hends⟩ := singleton_triple_factor_reading aP bP AP EP cP CP
    (Gluing.Profile.toBetaDiagram_connected _) (Gluing.Profile.toBetaDiagram_connected _) hpoly
  have htriple : threeInterval complete c d e q q = threeInterval complete B C D q q := by
    simpa only [cP,CP,threeConstantProfile_schur] using hcore
  refine ⟨three_constant_rigidity c d e B C D q hq hc hd he hB hC hD htriple,?_⟩
  rcases hends with ⟨h1,h2⟩ | ⟨h1,h2⟩
  all_goals
    simp only [aP,bP,AP,EP,scalarSingleton_schur] at h1 h2
  · exact Or.inl ⟨complete_injective_nonnegative ha.le hA.le h1,
      complete_injective_nonnegative hb.le hE.le h2⟩
  · exact Or.inr ⟨complete_injective_nonnegative ha.le hE.le h1,
      complete_injective_nonnegative hb.le hA.le h2⟩

theorem a2_P_zero (a b c d e q : ℤ) (z : ℕ+)
    (hq : (z.val : ℤ) < q)
    (hDom : Domain a b c d e z.val z.val q q) :
    eraseGenerator z (interval complete a b c d e z.val z.val q q) =
      complete a*complete b*threeInterval complete c d e q q := by
  have h := congrArg (fun f : Polynomial CompleteRing => f.coeff 0)
    (a2_P_marked a b c d e q z hq hDom)
  rw [Staircase.minimumPolynomial_coeff_zero] at h
  norm_num at h
  simpa using h

theorem a2_R_zero (a b c d e q : ℤ) (z : ℕ+)
    (hq : (z.val : ℤ) < q)
    (hDom : Domain a b c d e z.val q q z.val) :
    eraseGenerator z (interval complete a b c d e z.val q q z.val) =
      complete a*threeInterval complete b c d q q*complete e := by
  have h := congrArg (fun f : Polynomial CompleteRing => f.coeff 0)
    (a2_R_marked a b c d e q z hq hDom)
  rw [Staircase.minimumPolynomial_coeff_zero] at h
  norm_num at h
  simpa using h

/-- Complete P/R cross-pattern necessity.  The middle triple and singleton
allocation are derived from the actual zero layer before any row is matched. -/
theorem a2_cross_pattern_polynomial (a b c d e A B C D E q : ℤ) (z : ℕ+)
    (hq : (z.val : ℤ) < q)
    (hF : Domain a b c d e z.val z.val q q)
    (hH : Domain A B C D E z.val q q z.val)
    (he : interval complete a b c d e z.val z.val q q =
      interval complete A B C D E z.val q q z.val) :
    a = q ∧ c = b ∧ d = b+q-z.val ∧ e = b+q-z.val ∧
      ((A = q ∧ B = b ∧ C = b+q-z.val ∧ D = b+q-z.val ∧ E = b) ∨
       (A = b ∧ B = b+q-z.val ∧ C = b+q-z.val ∧ D = b ∧ E = q)) := by
  have hz := z.pos
  have hzero := congrArg (eraseGenerator z) he
  rw [a2_P_zero a b c d e q z hq hF,a2_R_zero A B C D E q z hq hH] at hzero
  have ha := hF.2.2.2.2.1
  have hb := hF.2.2.2.2.2.1
  have hc := hF.2.2.2.2.2.2.1
  have hd := hF.2.2.2.2.2.2.2.1
  have heq := hF.2.2.2.2.2.2.2.2
  have hA := hH.2.2.2.2.1
  have hB := hH.2.2.2.2.2.1
  have hC := hH.2.2.2.2.2.2.1
  have hD := hH.2.2.2.2.2.2.2.1
  have hE := hH.2.2.2.2.2.2.2.2
  obtain ⟨htriple,hends⟩ := a2_zero_layer_reading a b c d e A B C D E q
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) heq (by omega) (by omega) (by omega) hzero
  rcases htriple with ⟨hBc,hCd,hDe⟩ | ⟨hDc,hCd,hBe⟩
  · have hB' : B = c := hBc.symm
    have hC' : C = d := hCd.symm
    have hD' : D = e := hDe.symm
    subst B
    subst C
    subst D
    rcases hends with ⟨hAa,hEb⟩ | ⟨hEa,hAb⟩
    · have hA' : A = a := hAa.symm
      have hE' : E = b := hEb.symm
      subst A
      subst E
      obtain ⟨haq,hcb,hdu,heu⟩ := (a2_H1_polynomial_iff a b c d e q z hq hF hH).mp he
      exact ⟨haq,hcb,hdu,heu,Or.inl ⟨haq,hcb,hdu,heu,rfl⟩⟩
    · have hA' : A = b := hAb.symm
      have hE' : E = a := hEa.symm
      subst A
      subst E
      exact False.elim (a2_H2_polynomial_ne a b c d e q z hq hF hH he)
  · have hB' : B = e := hBe.symm
    have hC' : C = d := hCd.symm
    have hD' : D = c := hDc.symm
    subst B
    subst C
    subst D
    rcases hends with ⟨hAa,hEb⟩ | ⟨hEa,hAb⟩
    · have hA' : A = a := hAa.symm
      have hE' : E = b := hEb.symm
      subst A
      subst E
      have hRev : Domain b c d e a z.val q q z.val := by
        rcases hH with ⟨hz0,hq0,_,_,ha',he',hd',hc',hb'⟩
        dsimp [Domain]
        omega
      have heRev : interval complete a b c d e z.val z.val q q =
          interval complete b c d e a z.val q q z.val :=
        he.trans (interval_reverse complete b c d e a z.val q q z.val)
      exact False.elim (a2_H2_polynomial_ne a b c d e q z hq hF hRev heRev)
    · have hA' : A = b := hAb.symm
      have hE' : E = a := hEa.symm
      subst A
      subst E
      have hRev : Domain a c d e b z.val q q z.val := by
        rcases hH with ⟨hz0,hq0,_,_,hb',he',hd',hc',ha'⟩
        dsimp [Domain]
        omega
      have heRev : interval complete a b c d e z.val z.val q q =
          interval complete a c d e b z.val q q z.val :=
        he.trans (interval_reverse complete a c d e b z.val q q z.val)
      obtain ⟨haq,hcb,hdu,heu⟩ := (a2_H1_polynomial_iff a b c d e q z hq hF hRev).mp heRev
      exact ⟨haq,hcb,hdu,heu,Or.inr ⟨rfl,heu,hdu,hcb,haq⟩⟩

/-- Actual four-member contact classes A1 and A2, in the manuscript's M3/M4
coordinates.  The parameter object contains only standing arithmetic data. -/
def ContactMember (second : Bool) (P : Gluing.Profile 4)
    (X : StaircaseFiveFamilies.ContactParameters) : Prop :=
  if second then
    P = StaircaseFiveFamilies.m4F X ∨ P = (StaircaseFiveFamilies.m4F X).rotate ∨
    P = StaircaseFiveFamilies.m4H X ∨ P = (StaircaseFiveFamilies.m4H X).rotate
  else
    P = StaircaseFiveFamilies.m3F X ∨ P = (StaircaseFiveFamilies.m3F X).rotate ∨
    P = StaircaseFiveFamilies.m3H X ∨ P = (StaircaseFiveFamilies.m3H X).rotate

def ContactRelation (second : Bool) (P Q : Gluing.Profile 4) : Prop :=
  ∃ X : StaircaseFiveFamilies.ContactParameters, ContactMember second P X ∧ ContactMember second Q X

theorem contact_relation_schur_eq {P Q : Gluing.Profile 4} {second : Bool}
    (h : ContactRelation second P Q) : P.toBetaDiagram.schur = Q.toBetaDiagram.schur := by
  obtain ⟨X,hP,hQ⟩ := h
  cases second
  · simp only [ContactMember,if_false] at hP hQ
    exact (quartet_member_schur _ _ P (StaircaseFiveFamilies.m3_schur_eq X) hP).trans
      (quartet_member_schur _ _ Q (StaircaseFiveFamilies.m3_schur_eq X) hQ).symm
  · simp only [ContactMember,if_true] at hP hQ
    exact (quartet_member_schur _ _ P (StaircaseFiveFamilies.m4_schur_eq X) hP).trans
      (quartet_member_schur _ _ Q (StaircaseFiveFamilies.m4_schur_eq X) hQ).symm

/-- `lem:staircase-a2` for arbitrary actual rows in both cross-patterns.
The complete A2 class is produced, not supplied as a factorization premise. -/
theorem a2_cross_pattern (P Q : Gluing.Profile 4)
    (hP : Staircase.Thick P) (hQ : Staircase.Thick Q) (z q : ℕ+)
    (hzq : z.val < q.val)
    (hPg : P.g = ![z.val,z.val,q.val,q.val])
    (hQg : Q.g = ![z.val,q.val,q.val,z.val])
    (he : P.toBetaDiagram.schur = Q.toBetaDiagram.schur) : ContactRelation true P Q := by
  have hF : Domain (P.r 0) (P.r 1) (P.r 2) (P.r 3) (P.r 4)
      z.val z.val q.val q.val := by simpa [hPg] using domain_of_profile P hP
  have hH : Domain (Q.r 0) (Q.r 1) (Q.r 2) (Q.r 3) (Q.r 4)
      z.val q.val q.val z.val := by simpa [hQg] using domain_of_profile Q hQ
  have he' : interval complete (P.r 0) (P.r 1) (P.r 2) (P.r 3) (P.r 4)
      z.val z.val q.val q.val =
      interval complete (Q.r 0) (Q.r 1) (Q.r 2) (Q.r 3) (Q.r 4)
      z.val q.val q.val z.val := by
    rw [Gluing.Profile.toBetaDiagram_schur,Gluing.Profile.toBetaDiagram_schur,
      schur_interval P hP.hessenberg,schur_interval Q hQ.hessenberg] at he
    simpa [interval,complete_eq_hh,hPg,hQg] using he
  obtain ⟨hp0,hp2,hp3,hp4,hqs⟩ := a2_cross_pattern_polynomial
    (P.r 0) (P.r 1) (P.r 2) (P.r 3) (P.r 4)
    (Q.r 0) (Q.r 1) (Q.r 2) (Q.r 3) (Q.r 4) q.val z (by exact_mod_cast hzq) hF hH he'
  have hb : (q.val : ℤ)+z.val < P.r 1 := by
    have h := hP 1 2 (by rfl)
    simp [hPg] at h
    omega
  let X := StaircaseFiveFamilies.aParameters q.val (P.r 1) z.val
    (by positivity) (by exact_mod_cast hzq) hb
  refine ⟨X,Or.inl ?_,?_⟩
  · apply Gluing.Profile.ext
    all_goals funext i; fin_cases i <;>
      simp [X,StaircaseFiveFamilies.aParameters,StaircaseFiveFamilies.m4F,
        StaircaseFiveFamilies.profile,hPg] <;> omega
  · rcases hqs with ⟨h0,h1,h2,h3,h4⟩ | ⟨h0,h1,h2,h3,h4⟩
    · right; right; left
      apply Gluing.Profile.ext
      all_goals funext i; fin_cases i <;>
        simp [X,StaircaseFiveFamilies.aParameters,StaircaseFiveFamilies.m4H,
          StaircaseFiveFamilies.profile,hQg] <;> omega
    · right; right; right
      apply Gluing.Profile.ext
      all_goals funext i; fin_cases i <;>
        simp [X,StaircaseFiveFamilies.aParameters,StaircaseFiveFamilies.m4H,
          StaircaseFiveFamilies.profile,Gluing.Profile.rotate,hQg] <;> omega

/-- The two contact-family top-extension defects in their actual bare coordinates. -/
noncomputable def contactTopDefect (second : Bool) (p m z t : ℤ) : CompleteRing :=
  if second then
    interval complete (p+t) m m (m+p-z) (m+p-z) z z p p-
      interval complete (p+t) m (m+p-z) (m+p-z) m z p p z
  else
    interval complete (p+t) m m m (m+p-z) z z z p-
      interval complete (p+t) m (m+p-z) m m z p z z

noncomputable def contactBottomDefect (second : Bool) (p m z t : ℤ) : CompleteRing :=
  if second then
    interval complete p m m (m+p-z) (m+p-z+t) z z p p-
      interval complete p m (m+p-z) (m+p-z) (m+t) z p p z
  else
    interval complete p m m m (m+p-z+t) z z z p-
      interval complete p m (m+p-z) m (m+t) z p z z

/-- The private top coefficient of each contact family, including z=0. -/
theorem contact_top_coefficient (second : Bool) (p m z t : ℤ)
    (hz : 0 ≤ z) (hp : z < p) (hm : p+z < m) (ht : 0 < t)
    (v : ℕ+) (hv : (v.val : ℤ) = p+3*m-3*z+t) :
    MvPolynomial.pderiv v (contactTopDefect second p m z t) =
      if second then complete p*complete z*two complete z p m
      else complete z^2*two complete z p m := by
  cases second
  all_goals unfold contactTopDefect interval two
  all_goals ring_nf
  all_goals
    simp (disch := omega) [map_add,map_sub,map_neg,MvPolynomial.pderiv_mul,
      MvPolynomial.pderiv_pow,Staircase.residual_pderiv_complete,hv,if_pos,if_neg]
    <;> ring

theorem contact_top_defect_ne_zero (second : Bool) (p m z t : ℤ)
    (hz : 0 ≤ z) (hp : z < p) (hm : p+z < m) (ht : 0 < t) :
    contactTopDefect second p m z t ≠ 0 := by
  let v : ℕ+ := ⟨(p+3*m-3*z+t).toNat,by omega⟩
  have hv : (v.val : ℤ) = p+3*m-3*z+t := by dsimp [v]; omega
  have hz0 := (complete_ne_zero_iff z).mpr hz
  have hp0 := (complete_ne_zero_iff p).mpr (by omega)
  have hbin := two_ne_zero z p m hz hp (by omega)
  intro he
  have hd := congrArg (MvPolynomial.pderiv v) he
  rw [contact_top_coefficient second p m z t hz hp hm ht v hv,map_zero] at hd
  cases second
  · exact (mul_ne_zero (pow_ne_zero 2 hz0) hbin) hd
  · exact (mul_ne_zero (mul_ne_zero hp0 hz0) hbin) hd

/-- At the margin forced by the actual parent row multiset, both contact
families have a nonzero fixed coefficient below the outer marker. -/
theorem contact_tied_coefficient (second : Bool) (p m z : ℤ)
    (hz : 0 ≤ z) (hp : z < p) (hm : p+z < m)
    (v : ℕ+) (hv : (v.val : ℤ) = 4*m-3*z) :
    MvPolynomial.pderiv v
      (contactTopDefect second p m z (m-z)+contactBottomDefect second p m z (m-z)) =
      if second then complete p^2*two complete z p m
      else complete p*complete z*two complete z p m := by
  cases second
  all_goals unfold contactTopDefect contactBottomDefect interval two
  all_goals ring_nf
  all_goals
    simp (disch := omega) [map_add,map_sub,map_neg,MvPolynomial.pderiv_mul,
      MvPolynomial.pderiv_pow,Staircase.residual_pderiv_complete,hv,if_pos,if_neg]
    <;> ring

theorem contact_tied_defect_ne_zero (second : Bool) (p m z : ℤ)
    (hz : 0 ≤ z) (hp : z < p) (hm : p+z < m) :
    contactTopDefect second p m z (m-z)+contactBottomDefect second p m z (m-z) ≠ 0 := by
  let v : ℕ+ := ⟨(4*m-3*z).toNat,by omega⟩
  have hv : (v.val : ℤ) = 4*m-3*z := by dsimp [v]; omega
  have hz0 := (complete_ne_zero_iff z).mpr hz
  have hp0 := (complete_ne_zero_iff p).mpr (by omega)
  have hbin := two_ne_zero z p m hz hp (by omega)
  intro he
  have hd := congrArg (MvPolynomial.pderiv v) he
  rw [contact_tied_coefficient second p m z hz hp hm v hv,map_zero] at hd
  cases second
  · exact (mul_ne_zero (mul_ne_zero hp0 hz0) hbin) hd
  · exact (mul_ne_zero (pow_ne_zero 2 hp0) hbin) hd

def contactProfileF (second : Bool) (p m z : ℤ)
    (hz : 0 ≤ z) (hp : z < p) (hm : p+z < m) : Gluing.Profile 4 :=
  let X := StaircaseFiveFamilies.aParameters p m z hz hp hm
  if second then StaircaseFiveFamilies.m4F X else StaircaseFiveFamilies.m3F X

def contactProfileH (second : Bool) (p m z : ℤ)
    (hz : 0 ≤ z) (hp : z < p) (hm : p+z < m) : Gluing.Profile 4 :=
  let X := StaircaseFiveFamilies.aParameters p m z hz hp hm
  if second then StaircaseFiveFamilies.m4H X else StaircaseFiveFamilies.m3H X

theorem contact_profiles_thick (second : Bool) (p m z : ℤ)
    (hz : 0 ≤ z) (hp : z < p) (hm : p+z < m) :
    Staircase.Thick (contactProfileF second p m z hz hp hm) ∧
      Staircase.Thick (contactProfileH second p m z hz hp hm) := by
  cases second <;> constructor
  all_goals dsimp [contactProfileF,contactProfileH,StaircaseFiveFamilies.m3F,
    StaircaseFiveFamilies.m3H,StaircaseFiveFamilies.m4F,StaircaseFiveFamilies.m4H]
  all_goals apply profile_thick

theorem contact_profiles_schur_eq (second : Bool) (p m z : ℤ)
    (hz : 0 ≤ z) (hp : z < p) (hm : p+z < m) :
    (contactProfileF second p m z hz hp hm).toBetaDiagram.schur =
      (contactProfileH second p m z hz hp hm).toBetaDiagram.schur := by
  cases second
  · exact StaircaseFiveFamilies.m3_schur_eq _
  · exact StaircaseFiveFamilies.m4_schur_eq _

/-- The actual contact-family endpoint sum obstruction at its forced margin. -/
theorem contact_endpoint_sum_ne (second : Bool) (p m z : ℤ)
    (hz : 0 ≤ z) (hp : z < p) (hm : p+z < m) :
    endpointSum (contactProfileF second p m z hz hp hm).toBetaDiagram
      (m-z) (by omega) ≠
    endpointSum (contactProfileH second p m z hz hp hm).toBetaDiagram
      (m-z) (by omega) := by
  have hThick := contact_profiles_thick second p m z hz hp hm
  have hF := profile_endpoint_intervals _ hThick.1.hessenberg (m-z) (by omega)
  have hH := profile_endpoint_intervals _ hThick.2.hessenberg (m-z) (by omega)
  intro he
  unfold endpointSum at he
  rw [hF.1,hF.2,hH.1,hH.2] at he
  apply contact_tied_defect_ne_zero second p m z hz hp hm
  cases second <;>
    simp [contactProfileF,contactProfileH,StaircaseFiveFamilies.aParameters,
      StaircaseFiveFamilies.m3F,StaircaseFiveFamilies.m3H,StaircaseFiveFamilies.m4F,
      StaircaseFiveFamilies.m4H,StaircaseFiveFamilies.profile_row,
      StaircaseFiveFamilies.profile_gap,contactTopDefect,contactBottomDefect] at he ⊢
  all_goals ring_nf at he ⊢
  all_goals linear_combination he

/-- Top endpoint extensions separate both actual contact families at every
positive shift; all other directions are read from their endpoint rows. -/
theorem contact_top_extensions_ne (second : Bool) (p m z t : ℤ)
    (hz : 0 ≤ z) (hp : z < p) (hm : p+z < m) (ht : 0 < t) :
    ((contactProfileF second p m z hz hp hm).toBetaDiagram.extendTop t ht).schur ≠
      ((contactProfileH second p m z hz hp hm).toBetaDiagram.extendTop t ht).schur := by
  have hThick := contact_profiles_thick second p m z hz hp hm
  have hF := profile_endpoint_intervals _ hThick.1.hessenberg t ht
  have hH := profile_endpoint_intervals _ hThick.2.hessenberg t ht
  intro he
  rw [hF.1,hH.1] at he
  apply contact_top_defect_ne_zero second p m z t hz hp hm ht
  cases second <;>
    simp [contactProfileF,contactProfileH,StaircaseFiveFamilies.aParameters,
      StaircaseFiveFamilies.m3F,StaircaseFiveFamilies.m3H,StaircaseFiveFamilies.m4F,
      StaircaseFiveFamilies.m4H,StaircaseFiveFamilies.profile_row,
      StaircaseFiveFamilies.profile_gap,contactTopDefect] at he ⊢
  all_goals ring_nf at he ⊢
  all_goals linear_combination he

private theorem nonlinear_not_dvd_singleton {n : ℕ} (D : BetaDiagram (n+2))
    (hD : D.Connected) (S : BetaDiagram 1) : ¬ D.schur ∣ S.schur := by
  intro hd
  have he := full_schur_associated_eq D S
    ((D.schur_irreducible hD).associated_of_dvd (S.schur_irreducible (one_connected S)) hd)
  have hn := D.row_count_of_schur_eq S he
  omega

private theorem nonlinear_not_dvd_singletons {n : ℕ} (D : BetaDiagram (n+2))
    (hD : D.Connected) (L : List (BetaDiagram 1)) :
    ¬ D.schur ∣ (L.map (fun S => S.schur)).prod := by
  have hpr := UniqueFactorizationMonoid.irreducible_iff_prime.mp (D.schur_irreducible hD)
  induction L with
  | nil =>
    intro hd
    have hu : IsUnit D.schur := isUnit_of_dvd_one (by simpa using hd)
    exact (D.schur_irreducible hD).not_isUnit hu
  | cons S L ih =>
    intro hd
    simp only [List.map_cons,List.prod_cons] at hd
    rcases hpr.dvd_or_dvd hd with hd | hd
    · exact nonlinear_not_dvd_singleton D hD S hd
    · exact ih hd

/-- Any number of actual singleton factors cannot absorb an actual connected
nonlinear factor.  The recovered factors are equal, not merely associated. -/
theorem connected_nonlinear_factor_reading {n m : ℕ}
    (D : BetaDiagram (n+2)) (E : BetaDiagram (m+2))
    (hD : D.Connected) (hE : E.Connected) (L M : List (BetaDiagram 1))
    (he : (L.map (fun S => S.schur)).prod*D.schur =
      (M.map (fun S => S.schur)).prod*E.schur) : D.schur = E.schur := by
  have hDi := D.schur_irreducible hD
  have hDp := UniqueFactorizationMonoid.irreducible_iff_prime.mp hDi
  have hd : D.schur ∣ (M.map (fun S => S.schur)).prod*E.schur := by
    rw [← he]
    refine ⟨(L.map (fun S => S.schur)).prod,?_⟩
    ring
  rcases hDp.dvd_or_dvd hd with hd | hd
  · exact False.elim (nonlinear_not_dvd_singletons D hD M hd)
  · exact full_schur_associated_eq D E (hDi.associated_of_dvd (E.schur_irreducible hE) hd)

private def twoScalarProfile (a b q : ℤ) (hq : 0 ≤ q) (ha : q < a) (hb : q < b) :
    Gluing.Profile 1 where
  r i := (![a,b] i).toNat
  g _ := q.toNat
  r_pos := by intro i; fin_cases i <;> simp <;> omega
  g_lt_castSucc := by intro i; fin_cases i <;> simp <;> omega
  g_lt_succ := by intro i; fin_cases i <;> simp <;> omega

private theorem twoScalarProfile_schur (a b q : ℤ) (hq : 0 ≤ q) (ha : q < a) (hb : q < b) :
    (twoScalarProfile a b q hq ha hb).toBetaDiagram.schur = two complete q a b := by
  have hra : ((a.toNat : ℕ) : ℤ) = a := by omega
  have hrb : ((b.toNat : ℕ) : ℤ) = b := by omega
  have hrq : ((q.toNat : ℕ) : ℤ) = q := by omega
  rw [Gluing.Profile.toBetaDiagram_schur,Gluing.Profile.schur_two_interval]
  simp [twoScalarProfile,complete_eq_hh,two,hra,hrb,hrq]
  ring

/-- The full two-row polynomial determines its two actual row lengths up to
reversal, including coincident rows and zero gaps. -/
theorem two_scalar_rigidity (a b A B q : ℤ) (hq : 0 ≤ q)
    (ha : q < a) (hb : q < b) (hA : q < A) (hB : q < B)
    (he : two complete q a b = two complete q A B) :
    (a = A ∧ b = B) ∨ (a = B ∧ b = A) := by
  let P := twoScalarProfile a b q hq ha hb
  let Q := twoScalarProfile A B q hq hA hB
  have he' : P.toBetaDiagram.schur = Q.toBetaDiagram.schur := by
    rw [twoScalarProfile_schur,twoScalarProfile_schur]
    exact he
  rcases small_profile_rigidity P Q (by decide) he' with h | h
  · have h0 := congrArg (fun R : Gluing.Profile 1 => (R.r 0 : ℤ)) h
    have h1 := congrArg (fun R : Gluing.Profile 1 => (R.r 1 : ℤ)) h
    simp [P,Q,twoScalarProfile] at h0 h1
    exact Or.inl ⟨by omega,by omega⟩
  · have h0 := congrArg (fun R : Gluing.Profile 1 => (R.r 0 : ℤ)) h
    have h1 := congrArg (fun R : Gluing.Profile 1 => (R.r 1 : ℤ)) h
    simp [P,Q,twoScalarProfile,Gluing.Profile.rotate] at h0 h1
    exact Or.inr ⟨by omega,by omega⟩

/-- Zero-layer recovery of the unique q-connected pair in the three-minimum
case.  The three singleton positions need not be distinct or ordered. -/
theorem terminal_zero_pair_reading (a b c d e A B C D E q : ℤ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hq : 0 ≤ q)
    (hd : q < d) (he : q < e) (hD : q < D) (hE : q < E)
    (hzero : complete a*complete b*complete c*two complete q d e =
      complete A*complete B*complete C*two complete q D E) :
    (d = D ∧ e = E) ∨ (d = E ∧ e = D) := by
  let L := [(scalarSingleton a ha).toBetaDiagram,
    (scalarSingleton b hb).toBetaDiagram,(scalarSingleton c hc).toBetaDiagram]
  let M := [(scalarSingleton A hA).toBetaDiagram,
    (scalarSingleton B hB).toBetaDiagram,(scalarSingleton C hC).toBetaDiagram]
  let P := (twoScalarProfile d e q hq hd he).toBetaDiagram
  let Q := (twoScalarProfile D E q hq hD hE).toBetaDiagram
  have hprod : (L.map (fun S => S.schur)).prod*P.schur =
      (M.map (fun S => S.schur)).prod*Q.schur := by
    simpa [L,M,P,Q,scalarSingleton_schur,twoScalarProfile_schur,mul_assoc] using hzero
  have hpair := connected_nonlinear_factor_reading P Q
    (Gluing.Profile.toBetaDiagram_connected _) (Gluing.Profile.toBetaDiagram_connected _) L M hprod
  apply two_scalar_rigidity d e D E q hq hd he hD hE
  simpa only [P,Q,twoScalarProfile_schur] using hpair

/-- Equality version of the actual contact-blind injectivity theorem.  Support
at q is allowed on both sides and is retained in the difference measure. -/
theorem contact_operator_measure_eq (μ ν : ℤ →₀ ℚ) (e q K : ℤ)
    (hq : 1 ≤ q) (he : q < e) (hK : q < K)
    (hμ : ∀ s ∈ μ.support, 0 < s ∧ s < K-q)
    (hν : ∀ s ∈ ν.support, 0 < s ∧ s < K-q)
    (hOp : ContactQuadraticOperator.contactOperator μ e q K =
      ContactQuadraticOperator.contactOperator ν e q K) : μ = ν := by
  let δ := μ-ν
  have hs : ∀ s ∈ δ.support, 0 < s ∧ s < K-q := by
    intro s hs
    have hδ := Finsupp.mem_support_iff.mp hs
    by_cases hm : μ s = 0
    · have hn : ν s ≠ 0 := by
        intro hn
        exact hδ (by simp [δ,Finsupp.sub_apply,hm,hn])
      exact hν s (Finsupp.mem_support_iff.mpr hn)
    · exact hμ s (Finsupp.mem_support_iff.mpr hm)
  have hzero : ContactQuadraticOperator.contactOperator δ e q K = 0 := by
    unfold ContactQuadraticOperator.contactOperator δ
    rw [quadratic_sub,quadratic_sub]
    unfold ContactQuadraticOperator.contactOperator at hOp
    linear_combination hOp
  exact sub_eq_zero.mp
    (ContactQuadraticOperator.contact_blind_injective δ e q K hq he hK hs hzero)

/-- Two positive, increasing unit masses recover the original two rows;
no total-sum certificate is needed in this measure reading. -/
theorem tail_measure_rows_eq (d e D E z : ℤ) (hz : 0 ≤ z)
    (hd : 2*z < d) (he : z < e) (hD : 2*z < D) (hE : z < E)
    (hm : tailMeasure d e z = tailMeasure D E z) : d = D ∧ e = E := by
  classical
  have heE : e = E := by
    rcases lt_trichotomy e E with hlt | heq | hgt
    · have h := congrArg (fun μ : ℤ →₀ ℚ => μ e) hm
      have hn1 : e ≠ d+e-z := by omega
      have hn2 : e ≠ E := by omega
      have hn3 : e ≠ D+E-z := by omega
      simp [tailMeasure,Finsupp.single_apply,hn1,hn2,hn3,
        Ne.symm hn1,Ne.symm hn2,Ne.symm hn3] at h
    · exact heq
    · have h := congrArg (fun μ : ℤ →₀ ℚ => μ E) hm
      have hn1 : E ≠ D+E-z := by omega
      have hn2 : E ≠ e := by omega
      have hn3 : E ≠ d+e-z := by omega
      simp [tailMeasure,Finsupp.single_apply,hn1,hn2,hn3,
        Ne.symm hn1,Ne.symm hn2,Ne.symm hn3] at h
  subst E
  have hdD : d = D := by
    by_contra hn
    have h := congrArg (fun μ : ℤ →₀ ℚ => μ (d+e-z)) hm
    have hn1 : d+e-z ≠ e := by omega
    have hn2 : d+e-z ≠ D+e-z := by omega
    simp [tailMeasure,Finsupp.single_apply,hn1,hn2,Ne.symm hn1,Ne.symm hn2] at h
  exact ⟨hdD,rfl⟩

/-- The second minimum layer of a profile whose unique larger seam is terminal. -/
noncomputable def terminalLayer (a b c d e q z : ℤ) : CompleteRing :=
  complete (a+b+c-2*z)*two complete q d e+
  complete (a+b-z)*two complete q (c+d-z) e+
  complete a*two complete q (b+c+d-2*z) e

/-- The remaining terminal layer is exactly a contact-blind quadratic
operator on the two prefix masses, including masses at q. -/
theorem terminal_layer_operator (a b c d e q z : ℤ) :
    terminalLayer a b c d e q z =
      complete (a+b+c-2*z)*two complete q d e+
        ContactQuadraticOperator.contactOperator (tailMeasure b a z) e q (a+b+c+d-2*z) := by
  unfold terminalLayer ContactQuadraticOperator.contactOperator tailMeasure
  rw [quadratic_add,quadratic_add]
  simp only [ContactQuadraticOperator.quadratic_single,map_one,one_mul]
  unfold two
  ring_nf <;> ring

/-- Exact minimum marking of the three-minimum terminal placement. -/
theorem terminal_marked (a b c d e q : ℤ) (z : ℕ+)
    (hq : (z.val : ℤ) < q)
    (hDom : Domain a b c d e z.val z.val z.val q) :
    Staircase.minimumPolynomial z (interval complete a b c d e z.val z.val z.val q) =
      Polynomial.C (complete a*complete b*complete c*two complete q d e)+
      Polynomial.X*Polynomial.C
        (-(complete (a+b-z.val)*complete c*two complete q d e+
          complete a*complete (b+c-z.val)*two complete q d e+
          complete a*complete b*two complete q (c+d-z.val) e))+
      Polynomial.X^2*Polynomial.C (terminalLayer a b c d e q z.val)-
      Polynomial.X^3*Polynomial.C (two complete q (a+b+c+d-3*z.val) e) := by
  rcases hDom with ⟨hz0,_,_,hq0,ha,hb,hc,hd,he⟩
  have hz := z.pos
  simp (disch := omega) [interval,terminalLayer,two,map_add,map_sub,map_mul,map_neg,
    Staircase.minimumPolynomial_complete,if_pos,if_neg]
  <;> ring_nf

theorem terminal_zero (a b c d e q : ℤ) (z : ℕ+)
    (hq : (z.val : ℤ) < q)
    (hDom : Domain a b c d e z.val z.val z.val q) :
    eraseGenerator z (interval complete a b c d e z.val z.val z.val q) =
      complete a*complete b*complete c*two complete q d e := by
  have h := congrArg (fun f : Polynomial CompleteRing => f.coeff 0)
    (terminal_marked a b c d e q z hq hDom)
  rw [Staircase.minimumPolynomial_coeff_zero] at h
  norm_num at h
  simpa using h

theorem terminal_second (a b c d e q : ℤ) (z : ℕ+)
    (hq : (z.val : ℤ) < q)
    (hDom : Domain a b c d e z.val z.val z.val q) :
    (Staircase.minimumPolynomial z
      (interval complete a b c d e z.val z.val z.val q)).coeff 2 =
      terminalLayer a b c d e q z.val := by
  have h := congrArg (fun f : Polynomial CompleteRing => f.coeff 2)
    (terminal_marked a b c d e q z hq hDom)
  norm_num at h
  simpa using h

theorem terminal_top (a b c d e q : ℤ) (z : ℕ+)
    (hq : (z.val : ℤ) < q)
    (hDom : Domain a b c d e z.val z.val z.val q) :
    (Staircase.minimumPolynomial z
      (interval complete a b c d e z.val z.val z.val q)).coeff 3 =
      -two complete q (a+b+c+d-3*z.val) e := by
  have h := congrArg (fun f : Polynomial CompleteRing => f.coeff 3)
    (terminal_marked a b c d e q z hq hDom)
  norm_num at h
  simpa using h

theorem tail_measure_support (d e z s : ℤ) (hs : s ∈ (tailMeasure d e z).support) :
    s = e ∨ s = d+e-z := by
  classical
  by_contra hn
  push_neg at hn
  have hm := Finsupp.mem_support_iff.mp hs
  apply hm
  simp [tailMeasure,Finsupp.single_apply,hn.1,hn.2,Ne.symm hn.1,Ne.symm hn.2]

/-- End/end reconstruction in the three-minimum branch.  The actual
contact-blind operator recovers all three singleton rows, including any of
them that equal q and the balanced top pair. -/
theorem terminal_large_seam_polynomial (a b c d e A B C D E q : ℤ) (z : ℕ+)
    (hq : (z.val : ℤ) < q)
    (hF : Domain a b c d e z.val z.val z.val q)
    (hH : Domain A B C D E z.val z.val z.val q)
    (he : interval complete a b c d e z.val z.val z.val q =
      interval complete A B C D E z.val z.val z.val q) :
    a = A ∧ b = B ∧ c = C ∧ d = D ∧ e = E := by
  have hz := z.pos
  have ha := hF.2.2.2.2.1
  have hb := hF.2.2.2.2.2.1
  have hc := hF.2.2.2.2.2.2.1
  have hd := hF.2.2.2.2.2.2.2.1
  have heq := hF.2.2.2.2.2.2.2.2
  have hA := hH.2.2.2.2.1
  have hB := hH.2.2.2.2.2.1
  have hC := hH.2.2.2.2.2.2.1
  have hD := hH.2.2.2.2.2.2.2.1
  have hE := hH.2.2.2.2.2.2.2.2
  have hzero := congrArg (eraseGenerator z) he
  rw [terminal_zero a b c d e q z hq hF,terminal_zero A B C D E q z hq hH] at hzero
  have hpairs := terminal_zero_pair_reading a b c d e A B C D E q
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) heq (by omega) hE hzero
  let P := profile a b c d e z.val z.val z.val q hF
  let Q := profile A B C D E z.val z.val z.val q hH
  have hbeta : P.toBetaDiagram.schur = Q.toBetaDiagram.schur := by
    rw [profile_schur,profile_schur]
    simpa only [interval,complete_eq_hh] using he
  have hspan := P.toBetaDiagram.largestLabel_eq_of_schur_eq Q.toBetaDiagram
    P.toBetaDiagram_connected Q.toBetaDiagram_connected hbeta
  simp [P,Q,BetaDiagram.largestLabel,Gluing.Profile.toBetaDiagram,Gluing.Profile.xi,
    Gluing.Profile.zeta,Fin.sum_univ_succ,profile_row,profile_gap] at hspan
  have hsum : a+b+c = A+B+C := by
    rcases hpairs with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> omega
  have htop := congrArg (fun p : CompleteRing => (Staircase.minimumPolynomial z p).coeff 3) he
  rw [terminal_top a b c d e q z hq hF,terminal_top A B C D E q z hq hH] at htop
  have htop' : two complete q (a+b+c+d-3*z.val) e =
      two complete q (A+B+C+D-3*z.val) E := by linear_combination -htop
  have ht := two_scalar_rigidity
    (a+b+c+d-3*z.val) e (A+B+C+D-3*z.val) E q (by omega)
    (by omega) heq (by omega) hE htop'
  have hcore : d = D ∧ e = E := by
    rcases hpairs with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · exact ⟨h1,h2⟩
    · rcases ht with ⟨ht1,ht2⟩ | ⟨ht1,ht2⟩ <;> constructor <;> omega
  have hsecond := congrArg (fun p : CompleteRing => (Staircase.minimumPolynomial z p).coeff 2) he
  rw [terminal_second a b c d e q z hq hF,terminal_second A B C D E q z hq hH,
    terminal_layer_operator,terminal_layer_operator] at hsecond
  have hcommon : complete (a+b+c-2*z.val)*two complete q d e =
      complete (A+B+C-2*z.val)*two complete q D E := by
    rw [hcore.1,hcore.2,show a+b+c-2*z.val = A+B+C-2*z.val by omega]
  have hK : a+b+c+d-2*z.val = A+B+C+D-2*z.val := by omega
  have hright :
      ContactQuadraticOperator.contactOperator (tailMeasure B A z.val) E q (A+B+C+D-2*z.val) =
      ContactQuadraticOperator.contactOperator (tailMeasure B A z.val) e q (a+b+c+d-2*z.val) := by
    rw [← hcore.2,← hK]
  rw [← hcommon,hright] at hsecond
  have hop := add_left_cancel hsecond
  have hμ : ∀ s ∈ (tailMeasure b a z.val).support, 0 < s ∧ s < a+b+c+d-2*z.val-q := by
    intro s hs
    rcases tail_measure_support b a z.val s hs with rfl | rfl <;> constructor <;> omega
  have hν : ∀ s ∈ (tailMeasure B A z.val).support, 0 < s ∧ s < a+b+c+d-2*z.val-q := by
    intro s hs
    rcases tail_measure_support B A z.val s hs with rfl | rfl <;> constructor <;> omega
  have hmeasure := contact_operator_measure_eq (tailMeasure b a z.val) (tailMeasure B A z.val)
    e q (a+b+c+d-2*z.val) (by omega) heq (by omega) hμ hν hop
  obtain ⟨hbB,haA⟩ := tail_measure_rows_eq b a B A z.val (by positivity)
    (by omega) ha (by omega) hA hmeasure
  exact ⟨haA,hbB,by omega,hcore.1,hcore.2⟩

/-- Actual profiles with a terminal larger seam and three equal smaller seams
are recovered literally from their full Schur equality. -/
theorem terminal_large_seam_rigidity (P Q : Gluing.Profile 4)
    (hP : Staircase.Thick P) (hQ : Staircase.Thick Q) (z q : ℕ+)
    (hzq : z.val < q.val)
    (hPg : P.g = ![z.val,z.val,z.val,q.val])
    (hQg : Q.g = ![z.val,z.val,z.val,q.val])
    (he : P.toBetaDiagram.schur = Q.toBetaDiagram.schur) : P = Q := by
  have hF : Domain (P.r 0) (P.r 1) (P.r 2) (P.r 3) (P.r 4)
      z.val z.val z.val q.val := by simpa [hPg] using domain_of_profile P hP
  have hH : Domain (Q.r 0) (Q.r 1) (Q.r 2) (Q.r 3) (Q.r 4)
      z.val z.val z.val q.val := by simpa [hQg] using domain_of_profile Q hQ
  have he' : interval complete (P.r 0) (P.r 1) (P.r 2) (P.r 3) (P.r 4)
      z.val z.val z.val q.val =
      interval complete (Q.r 0) (Q.r 1) (Q.r 2) (Q.r 3) (Q.r 4)
      z.val z.val z.val q.val := by
    rw [Gluing.Profile.toBetaDiagram_schur,Gluing.Profile.toBetaDiagram_schur,
      schur_interval P hP.hessenberg,schur_interval Q hQ.hessenberg] at he
    simpa [interval,complete_eq_hh,hPg,hQg] using he
  obtain ⟨h0,h1,h2,h3,h4⟩ := terminal_large_seam_polynomial
    (P.r 0) (P.r 1) (P.r 2) (P.r 3) (P.r 4)
    (Q.r 0) (Q.r 1) (Q.r 2) (Q.r 3) (Q.r 4) q.val z (by exact_mod_cast hzq) hF hH he'
  apply Gluing.Profile.ext
  · exact five_rows_eq_of_cast P Q h0 h1 h2 h3 h4
  · exact hPg.trans hQg.symm

/-- The complete marked polynomial of an interior larger seam. -/
theorem interior_marked (a b c d e q : ℤ) (z : ℕ+)
    (hq : (z.val : ℤ) < q)
    (hDom : Domain a b c d e z.val q z.val z.val) :
    Staircase.minimumPolynomial z (interval complete a b c d e z.val q z.val z.val) =
      Polynomial.C (complete a*complete d*complete e*two complete q b c)+
      Polynomial.X*Polynomial.C
        (-complete (a+b-z.val)*complete d*complete e*complete c-
         complete a*complete b*complete (c+d-z.val)*complete e-
         complete a*complete b*complete c*complete (d+e-z.val)+
         complete q*complete (a+b+c-z.val-q)*complete d*complete e+
         complete a*complete q*complete (b+c+d-q-z.val)*complete e+
         complete a*complete q*complete (b+c-q)*complete (d+e-z.val))+
      Polynomial.X^2*Polynomial.C (interiorLayer complete a b c d e q z.val)-
      Polynomial.X^3*Polynomial.C (two complete q (a+b-z.val) (c+d+e-2*z.val)) := by
  rcases hDom with ⟨hz0,hq0,_,_,ha,hb,hc,hd,he⟩
  have hz := z.pos
  simp (disch := omega) [interval,interiorLayer,two,map_add,map_sub,map_mul,map_neg,
    Staircase.minimumPolynomial_complete,if_pos,if_neg]
  <;> ring_nf

theorem interior_zero (a b c d e q : ℤ) (z : ℕ+)
    (hq : (z.val : ℤ) < q)
    (hDom : Domain a b c d e z.val q z.val z.val) :
    eraseGenerator z (interval complete a b c d e z.val q z.val z.val) =
      complete a*complete d*complete e*two complete q b c := by
  have h := congrArg (fun f : Polynomial CompleteRing => f.coeff 0)
    (interior_marked a b c d e q z hq hDom)
  rw [Staircase.minimumPolynomial_coeff_zero] at h
  norm_num at h
  simpa using h

theorem interior_second (a b c d e q : ℤ) (z : ℕ+)
    (hq : (z.val : ℤ) < q)
    (hDom : Domain a b c d e z.val q z.val z.val) :
    (Staircase.minimumPolynomial z
      (interval complete a b c d e z.val q z.val z.val)).coeff 2 =
      interiorLayer complete a b c d e q z.val := by
  have h := congrArg (fun f : Polynomial CompleteRing => f.coeff 2)
    (interior_marked a b c d e q z hq hDom)
  norm_num at h
  simpa using h

theorem interior_top (a b c d e q : ℤ) (z : ℕ+)
    (hq : (z.val : ℤ) < q)
    (hDom : Domain a b c d e z.val q z.val z.val) :
    (Staircase.minimumPolynomial z
      (interval complete a b c d e z.val q z.val z.val)).coeff 3 =
      -two complete q (a+b-z.val) (c+d+e-2*z.val) := by
  have h := congrArg (fun f : Polynomial CompleteRing => f.coeff 3)
    (interior_marked a b c d e q z hq hDom)
  norm_num at h
  simpa using h

/-- A positive anchor below all six row labels reduces the full monomial
reading to the six structural permutations, with multiplicities retained. -/
theorem anchored_triple_reading (a d e A D E z : ℤ)
    (hz : 0 < z) (ha : z < a) (hd : z < d) (he : z < e)
    (hA : z < A) (hD : z < D) (hE : z < E)
    (hprod : complete a*complete d*complete e = complete A*complete D*complete E) :
    FourRowHessenberg.tripleMatch a d e A D E := by
  have hfour : complete z*complete a*complete d*complete e =
      complete z*complete A*complete D*complete E := by
    linear_combination complete z*hprod
  have h := FourRowHessenberg.four_product_reading hz (by omega) (by omega) (by omega)
    hz (by omega) (by omega) (by omega) hfour
  rcases h with ⟨h0,h⟩ | ⟨h0,h⟩ | ⟨h0,h⟩ | ⟨h0,h⟩
  · exact h
  all_goals omega

/-- Complete zero/top/second-layer data for interior-to-interior equality.
The row allocations and the top-pair orientation are derived from the actual
full polynomial, including balanced top pairs. -/
theorem interior_equality_readings (a b c d e A B C D E q : ℤ) (z : ℕ+)
    (hq : (z.val : ℤ) < q)
    (hF : Domain a b c d e z.val q z.val z.val)
    (hH : Domain A B C D E z.val q z.val z.val)
    (he : interval complete a b c d e z.val q z.val z.val =
      interval complete A B C D E z.val q z.val z.val) :
    ((b = B ∧ c = C) ∨ (b = C ∧ c = B)) ∧
    FourRowHessenberg.tripleMatch a d e A D E ∧
    (((a+b-z.val = A+B-z.val) ∧ (c+d+e-2*z.val = C+D+E-2*z.val)) ∨
     ((a+b-z.val = C+D+E-2*z.val) ∧ (c+d+e-2*z.val = A+B-z.val))) ∧
    interiorLayer complete a b c d e q z.val =
      interiorLayer complete A B C D E q z.val := by
  have hz := z.pos
  have ha := hF.2.2.2.2.1
  have hb := hF.2.2.2.2.2.1
  have hc := hF.2.2.2.2.2.2.1
  have hd := hF.2.2.2.2.2.2.2.1
  have he' := hF.2.2.2.2.2.2.2.2
  have hA := hH.2.2.2.2.1
  have hB := hH.2.2.2.2.2.1
  have hC := hH.2.2.2.2.2.2.1
  have hD := hH.2.2.2.2.2.2.2.1
  have hE := hH.2.2.2.2.2.2.2.2
  have hzero := congrArg (eraseGenerator z) he
  rw [interior_zero a b c d e q z hq hF,interior_zero A B C D E q z hq hH] at hzero
  have hpairs := terminal_zero_pair_reading a d e b c A D E B C q
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) hzero
  have hpairPoly : two complete q b c = two complete q B C := by
    rcases hpairs with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · rw [h1,h2]
    · rw [h1,h2]
      unfold two
      ring_nf <;> ring
  have hsingle : complete a*complete d*complete e = complete A*complete D*complete E := by
    have hz' := hzero
    rw [hpairPoly] at hz'
    exact mul_right_cancel₀ (two_ne_zero q B C (by omega) (by omega) (by omega)) hz'
  have hsingles := anchored_triple_reading a d e A D E z.val (by exact_mod_cast hz)
    ha (by omega) he' hA (by omega) hE hsingle
  have htop := congrArg (fun p : CompleteRing => (Staircase.minimumPolynomial z p).coeff 3) he
  rw [interior_top a b c d e q z hq hF,interior_top A B C D E q z hq hH] at htop
  have htop' : two complete q (a+b-z.val) (c+d+e-2*z.val) =
      two complete q (A+B-z.val) (C+D+E-2*z.val) := by linear_combination -htop
  have ht := two_scalar_rigidity (a+b-z.val) (c+d+e-2*z.val)
    (A+B-z.val) (C+D+E-2*z.val) q (by omega)
    (by omega) (by omega) (by omega) (by omega) htop'
  have hsecond := congrArg (fun p : CompleteRing => (Staircase.minimumPolynomial z p).coeff 2) he
  rw [interior_second a b c d e q z hq hF,interior_second A B C D E q z hq hH] at hsecond
  exact ⟨hpairs,hsingles,ht,hsecond⟩

/-- The q-cut keeps the complete two-row and three-row specializations,
including every row or interval contact with q. -/
theorem interior_q_cut {R : Type*} [CommRing R] (h : ℤ → R)
    (a b c d e q z : ℤ) (hq : h q = 0) :
    interval h a b c d e z q z z =
      two h z a b*threeInterval h c d e z z := by
  unfold interval two threeInterval
  simp only [hq,zero_mul,mul_zero,add_zero,zero_add,sub_zero]
  ring_nf <;> ring

theorem erased_complete_zero_iff (q : ℕ+) (k : ℤ) (hk : 0 < k) :
    eraseGenerator q (complete k) = 0 ↔ k = (q.val : ℤ) := by
  rw [eraseGenerator_complete]
  by_cases h : k = (q.val : ℤ)
  · simp [h]
  · simp [h,(complete_ne_zero_iff k).mpr hk.le]

/-- Augmentation counts surviving monomials with their actual coefficients,
including multiplicity at coincident same-sign monomials. -/
theorem erased_complete_augmentation (q : ℕ+) (k : ℤ) (hk : 0 < k) :
    Staircase.residualAugmentation (eraseGenerator q (complete k)) =
      if k = (q.val : ℤ) then 0 else 1 := by
  rw [eraseGenerator_complete]
  split_ifs
  · simp
  · exact Staircase.residualAugmentation_complete hk

/-- q-erasure precedes the second-layer maximum extraction.  Both top-pair
contributions are kept when the pair is balanced. -/
theorem interior_second_q_derivative (a b c d e q z : ℤ)
    (hDom : Domain a b c d e z q z z) (hz : 1 ≤ z) (hzq : z < q)
    (Q V : ℕ+) (hQ : (Q.val : ℤ) = q)
    (hV : (V.val : ℤ) = max (a+b-z) (c+d+e-2*z)) :
    MvPolynomial.pderiv V (eraseGenerator Q (interiorLayer complete a b c d e q z)) =
      (if a+b-z = max (a+b-z) (c+d+e-2*z) then
        eraseGenerator Q (complete e)*complete (c+d-z)+
        eraseGenerator Q (complete (d+e-z))*complete c else 0)+
      (if c+d+e-2*z = max (a+b-z) (c+d+e-2*z) then
        eraseGenerator Q (complete a)*complete b else 0) := by
  rcases hDom with ⟨hz0,hq0,_,_,ha,hb,hc,hd,he⟩
  have hx := le_max_left (a+b-z) (c+d+e-2*z)
  have hy := le_max_right (a+b-z) (c+d+e-2*z)
  have hVQ : V ≠ Q := by
    intro h
    have hv := congrArg (fun v : ℕ+ => (v.val : ℤ)) h
    omega
  have hpd (k : ℤ) :
      MvPolynomial.pderiv V (eraseGenerator Q (complete k)) =
        if k = (V.val : ℤ) then 1 else 0 :=
    Staircase.residual_pderiv_bar Q V hVQ k
  have hq0' : eraseGenerator Q (complete q) = 0 := by
    rw [eraseGenerator_complete,if_pos hQ.symm]
  rw [erase_interiorLayer]
  unfold interiorLayer two
  dsimp only
  rw [hq0']
  simp only [zero_mul,mul_zero,sub_zero]
  rw [erase_complete_of_lt Q (a+b-z) (by omega),
    erase_complete_of_lt Q (c+d-z) (by omega),erase_complete_of_lt Q c (by omega),
    erase_complete_of_lt Q b (by omega),erase_complete_of_lt Q (c+d+e-2*z) (by omega)]
  simp only [map_add,MvPolynomial.pderiv_mul,hpd,Staircase.residual_pderiv_complete,hV]
  simp (disch := omega) only [if_neg,zero_mul,mul_zero,zero_add,add_zero,mul_one,one_mul]
  split_ifs <;> ring

/-- A terminal second layer has no generator at the full four-row prefix
after q-erasure, whenever the bottom singleton lies below that index. -/
theorem terminal_second_q_derivative (a b c d e q z : ℤ)
    (hDom : Domain a b c d e z z z q) (hz : 1 ≤ z) (hzq : z < q)
    (helt : e < a+b+c+d-3*z)
    (Q V : ℕ+) (hQ : (Q.val : ℤ) = q)
    (hV : (V.val : ℤ) = a+b+c+d-3*z) :
    MvPolynomial.pderiv V (eraseGenerator Q (terminalLayer a b c d e q z)) = 0 := by
  rcases hDom with ⟨hz0,_,_,hq0,ha,hb,hc,hd,he⟩
  have hVQ : V ≠ Q := by
    intro h
    have hv := congrArg (fun v : ℕ+ => (v.val : ℤ)) h
    omega
  have hpd (k : ℤ) :
      MvPolynomial.pderiv V (eraseGenerator Q (complete k)) =
        if k = (V.val : ℤ) then 1 else 0 :=
    Staircase.residual_pderiv_bar Q V hVQ k
  have hq0' : eraseGenerator Q (complete q) = 0 := by
    rw [eraseGenerator_complete,if_pos hQ.symm]
  unfold terminalLayer two
  simp only [map_add,map_sub,map_mul]
  rw [hq0']
  simp only [zero_mul,mul_zero,sub_zero]
  simp only [map_add,MvPolynomial.pderiv_mul,hpd,hV]
  simp (disch := omega) only [if_neg,zero_mul,mul_zero,zero_add,add_zero]

/-- The final swapped-top allocation is separated by its full second layer. -/
theorem interior_swapped_layer_ne (b c d q z : ℤ)
    (hz : 1 ≤ z) (hzq : z < q) (hb : q+z < b) (hc : q+z < c)
    (hd : 2*z < d) (hbc : b ≠ c) :
    interiorLayer complete (d+q-z) b c d q q z ≠
      interiorLayer complete (d+q-z) c b d q q z := by
  intro he
  have h := interior_swapped_defect complete b c d q z
  rw [he,sub_self] at h
  have hbr := (mul_eq_zero.mp h.symm).resolve_left
    ((complete_ne_zero_iff q).mpr (by omega))
  have hprod := sub_eq_zero.mp hbr
  rcases complete_two_product_reading (by omega) (by omega) (by omega) (by omega)
    hprod with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> omega

/-- The actual zero, top, and second minimum layers in an end/interior
comparison.  No specialized four-row residual classification is assumed. -/
theorem terminal_interior_readings (a b c d e A B C D E q : ℤ) (z : ℕ+)
    (hq : (z.val : ℤ) < q)
    (hF : Domain a b c d e z.val z.val z.val q)
    (hH : Domain A B C D E z.val q z.val z.val)
    (he : interval complete a b c d e z.val z.val z.val q =
      interval complete A B C D E z.val q z.val z.val) :
    ((d = B ∧ e = C) ∨ (d = C ∧ e = B)) ∧
    FourRowHessenberg.tripleMatch a b c A D E ∧
    (((a+b+c+d-3*z.val = A+B-z.val) ∧ (e = C+D+E-2*z.val)) ∨
     ((a+b+c+d-3*z.val = C+D+E-2*z.val) ∧ (e = A+B-z.val))) ∧
    terminalLayer a b c d e q z.val = interiorLayer complete A B C D E q z.val := by
  have hz := z.pos
  have ha := hF.2.2.2.2.1; have hb := hF.2.2.2.2.2.1
  have hc := hF.2.2.2.2.2.2.1; have hd := hF.2.2.2.2.2.2.2.1
  have he' := hF.2.2.2.2.2.2.2.2
  have hA := hH.2.2.2.2.1; have hB := hH.2.2.2.2.2.1
  have hC := hH.2.2.2.2.2.2.1; have hD := hH.2.2.2.2.2.2.2.1
  have hE := hH.2.2.2.2.2.2.2.2
  have hzero := congrArg (eraseGenerator z) he
  rw [terminal_zero a b c d e q z hq hF,interior_zero A B C D E q z hq hH] at hzero
  have hpairs := terminal_zero_pair_reading a b c d e A D E B C q
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) he' (by omega) (by omega) hzero
  have hpairPoly : two complete q d e = two complete q B C := by
    rcases hpairs with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · rw [h1,h2]
    · rw [h1,h2]; unfold two; ring_nf
  have hsingle : complete a*complete b*complete c = complete A*complete D*complete E := by
    have h := hzero
    rw [hpairPoly] at h
    exact mul_right_cancel₀ (two_ne_zero q B C (by omega) (by omega) (by omega)) h
  have hsingles := anchored_triple_reading a b c A D E z.val (by exact_mod_cast hz)
    ha (by omega) (by omega) hA (by omega) hE hsingle
  have htop := congrArg (fun p : CompleteRing => (Staircase.minimumPolynomial z p).coeff 3) he
  rw [terminal_top a b c d e q z hq hF,interior_top A B C D E q z hq hH] at htop
  have htop' : two complete q (a+b+c+d-3*z.val) e =
      two complete q (A+B-z.val) (C+D+E-2*z.val) := by linear_combination -htop
  have ht := two_scalar_rigidity (a+b+c+d-3*z.val) e
    (A+B-z.val) (C+D+E-2*z.val) q (by omega)
    (by omega) he' (by omega) (by omega) htop'
  have hsecond := congrArg (fun p : CompleteRing => (Staircase.minimumPolynomial z p).coeff 2) he
  rw [terminal_second a b c d e q z hq hF,interior_second A B C D E q z hq hH] at hsecond
  exact ⟨hpairs,hsingles,ht,hsecond⟩

/-- End/interior equality forces the first interior-side row to be q.  The
other top-pair orientation is excluded by a positive two-monomial coefficient,
including coincident monomials and row/interval contacts. -/
theorem terminal_interior_mate_contact (a b c d e A B C D E q : ℤ) (z : ℕ+)
    (hq : (z.val : ℤ) < q)
    (hF : Domain a b c d e z.val z.val z.val q)
    (hH : Domain A B C D E z.val q z.val z.val)
    (he : interval complete a b c d e z.val z.val z.val q =
      interval complete A B C D E z.val q z.val z.val) :
    A = q ∧ B = d ∧ C = e ∧ e = q+d-z.val ∧
      a+b+c+d-3*z.val = e+D+E-2*z.val ∧
      FourRowHessenberg.tripleMatch a b c q D E := by
  have hz := z.pos
  have ha := hF.2.2.2.2.1; have hb := hF.2.2.2.2.2.1
  have hc := hF.2.2.2.2.2.2.1; have hd := hF.2.2.2.2.2.2.2.1
  have he' := hF.2.2.2.2.2.2.2.2
  have hA := hH.2.2.2.2.1; have hB := hH.2.2.2.2.2.1
  have hC := hH.2.2.2.2.2.2.1; have hD := hH.2.2.2.2.2.2.2.1
  have hE := hH.2.2.2.2.2.2.2.2
  obtain ⟨hpairs,hsingle,htop,hsecond⟩ :=
    terminal_interior_readings a b c d e A B C D E q z hq hF hH he
  let Qtag : ℕ+ := ⟨q.toNat,by omega⟩
  have hQtag : (Qtag.val : ℤ) = q := by dsimp [Qtag]; omega
  let x := a+b+c+d-3*z.val
  let V : ℕ+ := ⟨x.toNat,by dsimp [x]; omega⟩
  have hV : (V.val : ℤ) = x := by dsimp [V,x]; omega
  rcases hpairs with ⟨hBd,hCe⟩ | ⟨hCd,hBe⟩
  · have hB' : B = d := hBd.symm
    have hC' : C = e := hCe.symm
    subst B
    subst C
    have hrel : e = A+d-z.val ∧ x = e+D+E-2*z.val := by
      rcases htop with ⟨h1,h2⟩ | ⟨h1,h2⟩
      · dsimp [x]; omega
      · exact ⟨h2,h1⟩
    have hxe : e < x := by omega
    have hFder := terminal_second_q_derivative a b c d e q z.val hF
      (by exact_mod_cast hz) hq hxe Qtag V hQtag hV
    have hHV : (V.val : ℤ) = max (A+d-z.val) (e+D+E-2*z.val) := by
      rw [← hrel.1,← hrel.2,max_eq_right hxe.le]
      exact hV
    have hHder := interior_second_q_derivative A d e D E q z.val hH
      (by exact_mod_cast hz) hq Qtag V hQtag hHV
    have hmax : max (A+d-z.val) (e+D+E-2*z.val) = x := by
      rw [← hrel.1,← hrel.2,max_eq_right hxe.le]
    rw [hmax,← hrel.1,← hrel.2] at hHder
    simp [if_neg (ne_of_lt hxe),if_pos rfl] at hHder
    have hEq := congrArg (fun p : CompleteRing => MvPolynomial.pderiv V (eraseGenerator Qtag p)) hsecond
    rw [hFder,hHder] at hEq
    have hAzero : eraseGenerator Qtag (complete A) = 0 :=
      (mul_eq_zero.mp hEq.symm).resolve_right ((complete_ne_zero_iff d).mpr (by omega))
    have hAq : A = q := by
      have h := (erased_complete_zero_iff Qtag A (by omega)).mp hAzero
      omega
    refine ⟨hAq,rfl,rfl,by omega,hrel.2,?_⟩
    simpa only [hAq] using hsingle
  · have hB' : B = e := hBe.symm
    have hC' : C = d := hCd.symm
    subst B
    subst C
    have hrel : e = d+D+E-2*z.val ∧ x = A+e-z.val := by
      rcases htop with ⟨h1,h2⟩ | ⟨h1,h2⟩
      · exact ⟨h2,h1⟩
      · dsimp [x]; omega
    have hxe : e < x := by omega
    have hFder := terminal_second_q_derivative a b c d e q z.val hF
      (by exact_mod_cast hz) hq hxe Qtag V hQtag hV
    have hHV : (V.val : ℤ) = max (A+e-z.val) (d+D+E-2*z.val) := by
      rw [← hrel.2,← hrel.1,max_eq_left hxe.le]
      exact hV
    have hHder := interior_second_q_derivative A e d D E q z.val hH
      (by exact_mod_cast hz) hq Qtag V hQtag hHV
    have hmax : max (A+e-z.val) (d+D+E-2*z.val) = x := by
      rw [← hrel.2,← hrel.1,max_eq_left hxe.le]
    rw [hmax,← hrel.2,← hrel.1] at hHder
    simp [if_pos rfl,if_neg (ne_of_lt hxe)] at hHder
    have hEq := congrArg (fun p : CompleteRing => MvPolynomial.pderiv V (eraseGenerator Qtag p)) hsecond
    rw [hFder,hHder] at hEq
    have haug := congrArg Staircase.residualAugmentation hEq
    simp only [map_zero,map_add,map_mul,
      erased_complete_augmentation Qtag E (by omega),
      erased_complete_augmentation Qtag (D+E-z.val) (by omega),
      Staircase.residualAugmentation_complete (show 0 < d+D-z.val by omega),
      Staircase.residualAugmentation_complete (show 0 < d by omega),hQtag,mul_one] at haug
    by_cases hEq' : E = q
    · have hn : D+E-z.val ≠ q := by omega
      simp only [if_pos hEq',if_neg hn] at haug
      norm_num at haug
    · by_cases hDE : D+E-z.val = q <;> norm_num [hEq',hDE] at haug

private def qTripleProfile (a b c : ℤ) (z q : ℕ+) (hzq : z.val < q.val)
    (ha : (z.val : ℤ) < a) (hb : 2*(z.val : ℤ) < b)
    (hc : (q.val : ℤ)+z.val < c) : Gluing.Profile 2 :=
  threeConstantProfile a b c z.val (by positivity) ha hb (by omega)

private theorem qTriple_component (a b c : ℤ) (z q : ℕ+) (hzq : z.val < q.val)
    (ha : (z.val : ℤ) < a) (hb : 2*(z.val : ℤ) < b)
    (hc : (q.val : ℤ)+z.val < c) :
    Staircase.QComponent q (qTripleProfile a b c z q hzq ha hb hc) where
  thick := by
    intro j k h
    fin_cases j <;> fin_cases k <;> norm_num at h
    all_goals simp [qTripleProfile,threeConstantProfile]; omega
  gap_pos := by intro j; simpa [qTripleProfile,threeConstantProfile] using z.pos
  gap_ne := by intro j; simpa [qTripleProfile,threeConstantProfile] using (ne_of_lt hzq)
  bottom := by
    simp [Staircase.lastGap,qTripleProfile,threeConstantProfile,Fin.sum_univ_succ]
    omega

private theorem qTriple_schur (a b c : ℤ) (z q : ℕ+) (hzq : z.val < q.val)
    (ha : (z.val : ℤ) < a) (hb : 2*(z.val : ℤ) < b)
    (hc : (q.val : ℤ)+z.val < c) :
    (qTripleProfile a b c z q hzq ha hb hc).toBetaDiagram.schur =
      threeInterval complete a b c z.val z.val :=
  threeConstantProfile_schur a b c z.val (by positivity) ha hb (by omega)

private theorem qTriple_content (a b c : ℤ) (z q : ℕ+) (hzq : z.val < q.val)
    (ha : (z.val : ℤ) < a) (hb : 2*(z.val : ℤ) < b)
    (hc : (q.val : ℤ)+z.val < c) :
    Staircase.monicContent (qTriple_component a b c z q hzq ha hb hc) =
      if a = (q.val : ℤ) then complete z.val else
      if b = (q.val : ℤ) then complete z.val else 1 := by
  have hz := z.pos
  have haeq : a.toNat = q.val ↔ a = (q.val : ℤ) := by omega
  have hbeq : b.toNat = q.val ↔ b = (q.val : ℤ) := by omega
  have hane : a.toNat ≠ z.val := by omega
  rw [Staircase.three_content]
  simp [qTripleProfile,threeConstantProfile,haeq,hbeq,hane]

private theorem qTriple_row (a b c : ℤ) (z q : ℕ+) (hzq : z.val < q.val)
    (ha : (z.val : ℤ) < a) (hb : 2*(z.val : ℤ) < b)
    (hc : (q.val : ℤ)+z.val < c) (i : Fin 3) :
    ((qTripleProfile a b c z q hzq ha hb hc).r i : ℤ) = ![a,b,c] i := by
  have hz := z.pos
  fin_cases i
  · change ((a.toNat : ℕ) : ℤ) = a
    omega
  · change ((b.toNat : ℕ) : ℤ) = b
    omega
  · change ((c.toNat : ℕ) : ℤ) = c
    omega

private theorem qTriple_gap (a b c : ℤ) (z q : ℕ+) (hzq : z.val < q.val)
    (ha : (z.val : ℤ) < a) (hb : 2*(z.val : ℤ) < b)
    (hc : (q.val : ℤ)+z.val < c) (j : Fin 2) :
    (qTripleProfile a b c z q hzq ha hb hc).g j = z.val := rfl

private theorem qTriple_endpoint_restriction (a b c : ℤ) (z q : ℕ+)
    (hzq : z.val < q.val) (ha : (z.val : ℤ) < a) (hb : 2*(z.val : ℤ) < b)
    (hc : (q.val : ℤ)+z.val < c) (haq : a = (q.val : ℤ)) :
    Staircase.restriction q (qTripleProfile a b c z q hzq ha hb hc) =
      complete z.val*Staircase.quadraticB z.val (a+b-z.val) c := by
  let P := qTripleProfile a b c z q hzq ha hb hc
  let hP := qTriple_component a b c z q hzq ha hb hc
  have hfirst : P.r 0 = q.val := by change a.toNat = q.val; omega
  have hrec := Staircase.monicContent_mul_canonicalPrimitive hP
  rw [Staircase.three_content_first_row hP hfirst,
    Staircase.canonical_three_endpoint_B hP hfirst] at hrec
  simpa [P,qTriple_row,qTriple_gap] using hrec.symm

private theorem qTriple_middle_restriction (a b c : ℤ) (z q : ℕ+)
    (hzq : z.val < q.val) (ha : (z.val : ℤ) < a) (hb : 2*(z.val : ℤ) < b)
    (hc : (q.val : ℤ)+z.val < c) (han : a ≠ (q.val : ℤ))
    (hbq : b = (q.val : ℤ)) :
    Staircase.restriction q (qTripleProfile a b c z q hzq ha hb hc) =
      complete z.val*Staircase.quadraticM q.val z.val a c := by
  let P := qTripleProfile a b c z q hzq ha hb hc
  let hP := qTriple_component a b c z q hzq ha hb hc
  have hfirst : P.r 0 ≠ q.val := by change a.toNat ≠ q.val; omega
  have hmiddle : P.r 1 = q.val := by change b.toNat = q.val; omega
  have hsame : P.g 0 = P.g 1 := rfl
  have hcontent : Staircase.monicContent hP = complete z.val := by
    rw [qTriple_content,if_neg han,if_pos hbq]
  have hrec := Staircase.monicContent_mul_canonicalPrimitive hP
  rw [hcontent,Staircase.canonical_three_middle_M hP hfirst hmiddle hsame] at hrec
  simpa [P,qTriple_row,qTriple_gap] using hrec.symm

private theorem qTriple_full_of_large_first (a b c : ℤ) (z q : ℕ+)
    (hzq : z.val < q.val) (ha : (q.val : ℤ)+z.val < a)
    (hb : 2*(z.val : ℤ) < b) (hc : (q.val : ℤ)+z.val < c)
    (hbn : b ≠ (q.val : ℤ)) :
    Staircase.restriction q (qTripleProfile a b c z q hzq (by omega) hb hc) =
      threeInterval complete a b c z.val z.val := by
  have hz := z.pos
  let P := qTripleProfile a b c z q hzq (by omega) hb hc
  let hP := qTriple_component a b c z q hzq (by omega) hb hc
  have hfirst : P.r 0 ≠ q.val := by change a.toNat ≠ q.val; omega
  have hmiddle : P.r 1 ≠ q.val := by change b.toNat ≠ q.val; omega
  have h0 : (P.r 0 : ℤ) = a := by simpa [P] using qTriple_row a b c z q hzq (by omega) hb hc 0
  have h1 : (P.r 1 : ℤ) = b := by simpa [P] using qTriple_row a b c z q hzq (by omega) hb hc 1
  have hg : P.g 0 = z.val := qTriple_gap a b c z q hzq (by omega) hb hc 0
  have hmerge : (P.r 0 : ℤ)+P.r 1-P.g 0 ≠ q.val := by rw [h0,h1,hg]; omega
  rw [Staircase.restriction_eq_full_of_no_entry_contact
    (Staircase.three_no_contact_of_first_indices hP hfirst hmiddle hmerge)]
  exact qTriple_schur a b c z q hzq (by omega) hb hc

private theorem qTriple_canonical_of_content_one (a b c : ℤ) (z q : ℕ+)
    (hzq : z.val < q.val) (ha : (z.val : ℤ) < a) (hb : 2*(z.val : ℤ) < b)
    (hc : (q.val : ℤ)+z.val < c) (han : a ≠ (q.val : ℤ)) (hbn : b ≠ (q.val : ℤ)) :
    Staircase.canonicalPrimitive (qTriple_component a b c z q hzq ha hb hc) =
      Staircase.restriction q (qTripleProfile a b c z q hzq ha hb hc) := by
  have h := Staircase.monicContent_mul_canonicalPrimitive
    (qTriple_component a b c z q hzq ha hb hc)
  rw [qTriple_content,if_neg han,if_neg hbn] at h
  norm_num at h
  exact h

private theorem qTriple_canonical_degree_three (a b c : ℤ) (z q : ℕ+)
    (hzq : z.val < q.val) (ha : (z.val : ℤ) < a) (hb : 2*(z.val : ℤ) < b)
    (hc : (q.val : ℤ)+z.val < c) (han : a ≠ (q.val : ℤ)) (hbn : b ≠ (q.val : ℤ)) :
    (Staircase.canonicalPrimitive (qTriple_component a b c z q hzq ha hb hc)).totalDegree = 3 := by
  rw [qTriple_canonical_of_content_one a b c z q hzq ha hb hc han hbn]
  exact Staircase.restriction_totalDegree (qTriple_component a b c z q hzq ha hb hc)

private theorem qTriple_no_gap_divisor (a b c : ℤ) (z q : ℕ+)
    (hzq : z.val < q.val) (ha : (z.val : ℤ) < a) (hb : 2*(z.val : ℤ) < b)
    (hc : (q.val : ℤ)+z.val < c) (han : a ≠ (q.val : ℤ)) (hbn : b ≠ (q.val : ℤ)) :
    ¬ complete z.val ∣ Staircase.restriction q (qTripleProfile a b c z q hzq ha hb hc) := by
  let P := qTripleProfile a b c z q hzq ha hb hc
  let hP := qTriple_component a b c z q hzq ha hb hc
  have hcon : Staircase.monicContent hP = 1 := by
    rw [qTriple_content,if_neg han,if_neg hbn]
  have hrest := Staircase.restriction_eq_monicContent_mul hP
  rw [hcon,one_mul] at hrest
  have hn := Staircase.gap_variable_not_dvd_monicPrimitive hP (0 : Fin 2)
  dsimp only at hn
  have hv : (⟨P.g 0,hP.gap_pos 0⟩ : ℕ+) = z := by
    apply Subtype.ext
    simp [P,qTripleProfile,threeConstantProfile] <;> rfl
  rw [hv] at hn
  intro hd
  apply hn
  rw [← hrest,← complete_nat z]
  exact hd

private theorem singleton_not_dvd_connected {n : ℕ} (S : BetaDiagram 1)
    (D : BetaDiagram (n+2)) (hD : D.Connected) : ¬ S.schur ∣ D.schur := by
  intro hd
  have he := full_schur_associated_eq S D
    ((S.schur_irreducible (one_connected S)).associated_of_dvd (D.schur_irreducible hD) hd)
  have hn := S.row_count_of_schur_eq D he
  omega

private theorem gap_not_dvd_three_full (a b c : ℤ) (z : ℕ+)
    (ha : (z.val : ℤ) < a) (hb : 2*(z.val : ℤ) < b) (hc : (z.val : ℤ) < c) :
    ¬ complete z.val ∣ threeInterval complete a b c z.val z.val := by
  let S := (scalarSingleton z.val (by have := z.pos; exact_mod_cast this)).toBetaDiagram
  let P := (threeConstantProfile a b c z.val (by positivity) ha hb hc).toBetaDiagram
  have h := singleton_not_dvd_connected S P (Gluing.Profile.toBetaDiagram_connected _)
  simpa only [S,P,scalarSingleton_schur,threeConstantProfile_schur] using h

/-- The positive second-layer count forces the source's first singleton to
be q as well.  Repeated q rows and merged-interval contacts are retained. -/
theorem terminal_interior_source_contact (a b c d e A B C D E q : ℤ) (z : ℕ+)
    (hq : (z.val : ℤ) < q)
    (hF : Domain a b c d e z.val z.val z.val q)
    (hH : Domain A B C D E z.val q z.val z.val)
    (he : interval complete a b c d e z.val z.val z.val q =
      interval complete A B C D E z.val q z.val z.val) :
    a = q ∧ A = q ∧ B = d ∧ C = e ∧ e = q+d-z.val ∧
      ((D = b ∧ E = c) ∨ (D = c ∧ E = b)) := by
  obtain ⟨hAq,hBd,hCe,herel,hx,htrip⟩ :=
    terminal_interior_mate_contact a b c d e A B C D E q z hq hF hH he
  subst A
  subst B
  subst C
  have hz := z.pos
  have ha := hF.2.2.2.2.1; have hb := hF.2.2.2.2.2.1
  have hc := hF.2.2.2.2.2.2.1; have hd := hF.2.2.2.2.2.2.2.1
  have he' := hF.2.2.2.2.2.2.2.2
  have hD := hH.2.2.2.2.2.2.2.1; have hE := hH.2.2.2.2.2.2.2.2
  have hsecond := congrArg (fun p : CompleteRing => (Staircase.minimumPolynomial z p).coeff 2) he
  rw [terminal_second a b c d e q z hq hF,interior_second q d e D E q z hq hH] at hsecond
  let Qtag : ℕ+ := ⟨q.toNat,by omega⟩
  have hQtag : (Qtag.val : ℤ) = q := by dsimp [Qtag]; omega
  have haq : a = q := by
    by_contra han
    have hbc : b = q ∨ c = q := by
      rcases htrip with ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩ |
        ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩ <;> omega
    by_cases hbq : b = q
    · subst b
      have haug := congrArg
        (fun p : CompleteRing => Staircase.residualAugmentation (eraseGenerator Qtag p)) hsecond
      unfold terminalLayer interiorLayer two at haug
      simp only [map_add,map_sub,map_mul,map_neg] at haug
      simp (disch := omega) only [erased_complete_augmentation] at haug
      simp only [hQtag] at haug
      simp (disch := omega) only [if_pos,if_neg,zero_mul,mul_zero,add_zero,zero_add,
        sub_zero,zero_sub,one_mul,mul_one] at haug
      split_ifs at haug <;> norm_num at haug
    · have hcq : c = q := hbc.resolve_left hbq
      subst c
      have hEn : E ≠ q := by
        intro heq
        rcases htrip with ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩ |
          ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩ <;> omega
      have hsum : D+E-z.val = a+b-z.val := by omega
      have haug := congrArg
        (fun p : CompleteRing => Staircase.residualAugmentation (eraseGenerator Qtag p)) hsecond
      unfold terminalLayer interiorLayer two at haug
      simp only [map_add,map_sub,map_mul,map_neg] at haug
      simp (disch := omega) only [erased_complete_augmentation] at haug
      simp only [hQtag] at haug
      rw [hsum] at haug
      simp (disch := omega) only [if_pos,if_neg,zero_mul,mul_zero,add_zero,zero_add,
        sub_zero,zero_sub,one_mul,mul_one] at haug
      split_ifs at haug <;> norm_num at haug
  have hends : (D = b ∧ E = c) ∨ (D = c ∧ E = b) := by
    rw [haq] at htrip
    rcases htrip with ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩ |
      ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩ <;> omega
  exact ⟨haq,rfl,rfl,rfl,herel,hends⟩

theorem erase_interval (q : ℕ+) (a b c d e r s t u : ℤ) :
    eraseGenerator q (interval complete a b c d e r s t u) =
      interval (fun k => eraseGenerator q (complete k)) a b c d e r s t u := by
  unfold interval
  simp only [map_add,map_sub,map_mul]

theorem terminal_contact_q_cut {R : Type*} [CommRing R] (h : ℤ → R)
    (b c d e q z : ℤ) (hq : h q = 0) :
    interval h q b c d e z z z q =
      -h z*h e*threeInterval h (q+b-z) c d z z := by
  unfold interval threeInterval
  simp only [hq,zero_mul,mul_zero,zero_add,add_zero,sub_zero,zero_sub]
  ring_nf

theorem interior_contact_q_cut {R : Type*} [CommRing R] (h : ℤ → R)
    (d D E q z : ℤ) (hq : h q = 0) :
    interval h q d (q+d-z) D E z q z z =
      -h z*h (q+d-z)*threeInterval h (q+d-z) D E z z := by
  rw [interior_q_cut h q d (q+d-z) D E q z hq]
  unfold two
  simp only [hq,zero_mul,zero_sub]
  ring_nf

theorem three_contact_end {R : Type*} [CommRing R] (h : ℤ → R)
    (a b q z : ℤ) (hq : h q = 0) :
    threeInterval h a b q z z = -h z*two h z a (b+q-z) := by
  unfold threeInterval two
  simp only [hq,zero_mul,mul_zero,zero_sub,sub_zero]
  ring_nf

theorem three_contact_middle {R : Type*} [CommRing R] (h : ℤ → R)
    (a c q z : ℤ) (hq : h q = 0) :
    threeInterval h a q c z z =
      h z*(h z*h (a+c+q-2*z)-h (a+q-z)*h c-h a*h (c+q-z)) := by
  unfold threeInterval
  simp only [hq,zero_mul,mul_zero,zero_sub,sub_zero]
  ring_nf

private theorem terminal_restriction_three (b c d e D E : ℤ) (z q : ℕ+)
    (hzq : z.val < q.val)
    (hF : Domain q.val b c d e z.val z.val z.val q.val)
    (hH : Domain q.val d e D E z.val q.val z.val z.val)
    (herel : e = (q.val : ℤ)+d-z.val)
    (he : interval complete q.val b c d e z.val z.val z.val q.val =
      interval complete q.val d e D E z.val q.val z.val z.val) :
    Staircase.restriction q (qTripleProfile ((q.val : ℤ)+b-z.val) c d z q hzq
      (by rcases hF with ⟨_,_,_,_,_,hb',_,_,_⟩; have := z.pos; omega)
      (by have h := hF.2.2.2.2.2.2.1; omega)
      (by have h := hF.2.2.2.2.2.2.2.1; omega)) =
    Staircase.restriction q (qTripleProfile E D e z q hzq
      (by exact hH.2.2.2.2.2.2.2.2)
      (by have h := hH.2.2.2.2.2.2.2.1; omega)
      (by have h := hF.2.2.2.2.2.2.2.1; have := z.pos; omega)) := by
  have hz := z.pos
  have hq : (z.val : ℤ) < q.val := by exact_mod_cast hzq
  have hed : (q.val : ℤ) < e := hF.2.2.2.2.2.2.2.2
  let bar := fun k : ℤ => eraseGenerator q (complete k)
  have hq0 : bar q.val = 0 := by simp [bar,eraseGenerator_complete]
  have heq := congrArg (eraseGenerator q) he
  rw [erase_interval,erase_interval] at heq
  rw [terminal_contact_q_cut,herel,interior_contact_q_cut] at heq
  all_goals try exact hq0
  rw [← herel] at heq
  have hzbar : bar z.val = complete z.val := by
    simp [bar,eraseGenerator_complete,show (z.val : ℤ) ≠ q.val by omega]
  have hebar : bar e = complete e := erase_complete_of_lt q e hed
  have hcoef : -bar z.val*bar e ≠ 0 := by
    rw [hzbar,hebar]
    exact mul_ne_zero (neg_ne_zero.mpr ((complete_ne_zero_iff z.val).mpr (by positivity)))
      ((complete_ne_zero_iff e).mpr (by omega))
  have htr := mul_left_cancel₀ hcoef heq
  have hrev := threeInterval_reverse bar e D E z.val z.val
  have htr' : threeInterval bar ((q.val : ℤ)+b-z.val) c d z.val z.val =
      threeInterval bar E D e z.val z.val := htr.trans hrev.symm
  unfold Staircase.restriction
  rw [qTriple_schur,qTriple_schur]
  simpa only [threeInterval,map_add,map_sub,map_mul,bar] using htr'

/-- A1 end/interior necessity for every actual row tuple in the three-minimum
patterns.  The first-contact and every cubic/quadratic degeneration are
produced from the full polynomial and the actual three-row content table. -/
theorem a1_cross_pattern_polynomial (a b c d e A B C D E : ℤ) (z q : ℕ+)
    (hzq : z.val < q.val)
    (hF : Domain a b c d e z.val z.val z.val q.val)
    (hH : Domain A B C D E z.val q.val z.val z.val)
    (he : interval complete a b c d e z.val z.val z.val q.val =
      interval complete A B C D E z.val q.val z.val z.val) :
    a = (q.val : ℤ) ∧ b = d ∧ c = d ∧ e = (q.val : ℤ)+d-z.val ∧
      A = (q.val : ℤ) ∧ B = d ∧ C = e ∧ D = d ∧ E = d := by
  obtain ⟨haq,hAq,hBd,hCe,herel,hends⟩ :=
    terminal_interior_source_contact a b c d e A B C D E q.val z
      (by exact_mod_cast hzq) hF hH he
  subst a
  subst A
  subst B
  subst C
  have hz := z.pos
  have hb := hF.2.2.2.2.2.1
  have hc : 2*(z.val : ℤ) < c := by have h := hF.2.2.2.2.2.2.1; omega
  have hd := hF.2.2.2.2.2.2.2.1
  have he' := hF.2.2.2.2.2.2.2.2
  have hD : 2*(z.val : ℤ) < D := by have h := hH.2.2.2.2.2.2.2.1; omega
  have hE := hH.2.2.2.2.2.2.2.2
  let u := (q.val : ℤ)+b-z.val
  have hu : (q.val : ℤ)+z.val < u := by dsimp [u]; omega
  have heq : (q.val : ℤ)+z.val < e := by omega
  let P := qTripleProfile u c d z q hzq (by omega) hc (by omega)
  let R := qTripleProfile E D e z q hzq hE hD heq
  let hP := qTriple_component u c d z q hzq (by omega) hc (by omega)
  let hR := qTriple_component E D e z q hzq hE hD heq
  have hrestr : Staircase.restriction q P = Staircase.restriction q R :=
    terminal_restriction_three b c d e D E z q hzq hF hH herel he
  by_cases hcq : c = (q.val : ℤ)
  · have hq2 : 2*(z.val : ℤ) < q.val := by omega
    have hsrc : Staircase.restriction q P =
        complete z.val*Staircase.quadraticM q.val z.val u d := by
      simpa only [P] using qTriple_middle_restriction u c d z q hzq
        (by omega) hc (by omega) (by omega) hcq
    rcases hends with ⟨hDb,hEq⟩ | ⟨hDq,hEb⟩
    · have hDb' : D = b := hDb
      have hEq' : E = q.val := by omega
      have hmateRaw := qTriple_endpoint_restriction E D e z q hzq hE hD heq hEq'
      have hmate : Staircase.restriction q R =
          complete z.val*Staircase.quadraticB z.val ((q.val : ℤ)+b-z.val) e :=
        hmateRaw.trans (by rw [hEq',hDb'])
      have hpoly : Staircase.quadraticM q.val z.val u d =
          Staircase.quadraticB z.val ((q.val : ℤ)+b-z.val) e := by
        apply mul_left_cancel₀ ((complete_ne_zero_iff z.val).mpr (by positivity))
        exact hsrc.symm.trans (hrestr.trans hmate)
      have haug := congrArg Staircase.residualAugmentation hpoly
      rw [Staircase.quadraticM_augmentation _ _ _ _ (by exact_mod_cast hz) hq2 (by omega) (by omega),
        Staircase.quadraticB_augmentation _ _ _ (by exact_mod_cast hz) (by omega) (by omega)] at haug
      norm_num at haug
    · have hDq' : D = q.val := by omega
      have hEb' : E = b := hEb
      by_cases hbq : b = (q.val : ℤ)
      · have hEq' : E = q.val := by omega
        have hmateRaw := qTriple_endpoint_restriction E D e z q hzq hE hD heq hEq'
        have hmate : Staircase.restriction q R =
            complete z.val*Staircase.quadraticB z.val (b+q.val-z.val) e :=
          hmateRaw.trans (by rw [hEq',hDq',hbq])
        have hpoly : Staircase.quadraticM q.val z.val u d =
            Staircase.quadraticB z.val (b+q.val-z.val) e := by
          apply mul_left_cancel₀ ((complete_ne_zero_iff z.val).mpr (by positivity))
          exact hsrc.symm.trans (hrestr.trans hmate)
        have haug := congrArg Staircase.residualAugmentation hpoly
        rw [Staircase.quadraticM_augmentation _ _ _ _ (by exact_mod_cast hz) hq2 (by omega) (by omega),
          Staircase.quadraticB_augmentation _ _ _ (by exact_mod_cast hz) (by omega) (by omega)] at haug
        norm_num at haug
      · have hEn' : E ≠ (q.val : ℤ) := by omega
        have hmateRaw := qTriple_middle_restriction E D e z q hzq hE hD heq hEn' hDq'
        have hmate : Staircase.restriction q R =
            complete z.val*Staircase.quadraticM q.val z.val b e :=
          hmateRaw.trans (by rw [hEb'])
        have hpoly : Staircase.quadraticM q.val z.val u d =
            Staircase.quadraticM q.val z.val b e := by
          apply mul_left_cancel₀ ((complete_ne_zero_iff z.val).mpr (by positivity))
          exact hsrc.symm.trans (hrestr.trans hmate)
        have hkeys := (Staircase.quadraticM_eq_iff q.val z.val u d z.val b e
          (by exact_mod_cast hz) hq2 (by omega) (by omega)
          (by exact_mod_cast hz) hq2 (by omega) (by omega)).mp hpoly
        have hbd : b = d := by rcases hkeys.2 with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> dsimp [u] at h1 <;> omega
        have heu : e = b+q.val-z.val := by omega
        have hecross : interval complete q.val b q.val b (b+q.val-z.val)
            z.val z.val z.val q.val =
            interval complete q.val b (b+q.val-z.val) q.val b z.val q.val z.val z.val := by
          simpa only [hbd,hcq,heu,hDq',hEb'] using he
        have hcb := (crossing_remaining_row_iff q.val b q.val z.val
          (by exact_mod_cast hz) (by exact_mod_cast hzq) (by omega) hq2).mp hecross
        omega
  · have hsrcFull : Staircase.restriction q P = threeInterval complete u c d z.val z.val := by
      simpa only [P] using qTriple_full_of_large_first u c d z q hzq hu hc (by omega) hcq
    have hEn : E ≠ (q.val : ℤ) := by
      intro hEq
      have hcon : Staircase.monicContent hR = complete z.val := by
        rw [qTriple_content,if_pos hEq]
      have hdiv : complete z.val ∣ Staircase.restriction q R := by
        refine ⟨Staircase.monicPrimitive hR,?_⟩
        rw [← hcon]
        exact Staircase.restriction_eq_monicContent_mul hR
      have hdivSrc : complete z.val ∣ threeInterval complete u c d z.val z.val := by
        rw [← hsrcFull,hrestr]
        exact hdiv
      exact gap_not_dvd_three_full u c d z (by omega) hc (by omega) hdivSrc
    have hDn : D ≠ (q.val : ℤ) := by
      intro hDq
      have hcon : Staircase.monicContent hR = complete z.val := by
        rw [qTriple_content,if_neg hEn,if_pos hDq]
      have hdiv : complete z.val ∣ Staircase.restriction q R := by
        refine ⟨Staircase.monicPrimitive hR,?_⟩
        rw [← hcon]
        exact Staircase.restriction_eq_monicContent_mul hR
      have hdivSrc : complete z.val ∣ threeInterval complete u c d z.val z.val := by
        rw [← hsrcFull,hrestr]
        exact hdiv
      exact gap_not_dvd_three_full u c d z (by omega) hc (by omega) hdivSrc
    have hPcon : Staircase.monicContent hP = 1 := by
      rw [qTriple_content,if_neg (show u ≠ (q.val : ℤ) by omega),if_neg hcq]
    have hRcon : Staircase.monicContent hR = 1 := by
      rw [qTriple_content,if_neg hEn,if_neg hDn]
    have hcanon := Staircase.canonical_eq_of_content_and_restriction_eq hP hR
      (by rw [hPcon,hRcon]) hrestr
    have hprofiles := Staircase.three_primitive_cubic_rigidity hP hR
      (qTriple_canonical_degree_three u c d z q hzq (by omega) hc (by omega)
        (by omega) hcq)
      (qTriple_canonical_degree_three E D e z q hzq hE hD heq hEn hDn) hcanon
    have hbd : b = d ∧ D = c ∧ E = d := by
      rcases hprofiles with h | h
      all_goals
        have h0 := congrArg (fun S : Gluing.Profile 2 => (S.r 0 : ℤ)) h
        have h1 := congrArg (fun S : Gluing.Profile 2 => (S.r 1 : ℤ)) h
        have h2 := congrArg (fun S : Gluing.Profile 2 => (S.r 2 : ℤ)) h
        simp [P,R,qTripleProfile,threeConstantProfile,Gluing.Profile.rotate] at h0 h1 h2
        dsimp [u] at h0 h1 h2
        exact ⟨by omega,by omega,by omega⟩
    have heu : e = b+q.val-z.val := by omega
    have hecross : interval complete q.val b c b (b+q.val-z.val)
        z.val z.val z.val q.val =
        interval complete q.val b (b+q.val-z.val) c b z.val q.val z.val z.val := by
      simpa only [← hbd.1,hbd.2.1,hbd.2.2,heu] using he
    have hcb := (crossing_remaining_row_iff q.val b c z.val
      (by exact_mod_cast hz) (by exact_mod_cast hzq) (by omega) hc).mp hecross
    exact ⟨rfl,hbd.1,by omega,herel,rfl,rfl,rfl,by omega,by omega⟩

/-- Full actual A1 end/interior classification in the three-minimum patterns,
including every endpoint row contact and all constant-gap degenerations. -/
theorem a1_cross_pattern (P Q : Gluing.Profile 4)
    (hP : Staircase.Thick P) (hQ : Staircase.Thick Q) (z q : ℕ+)
    (hzq : z.val < q.val)
    (hPg : P.g = ![z.val,z.val,z.val,q.val])
    (hQg : Q.g = ![z.val,q.val,z.val,z.val])
    (he : P.toBetaDiagram.schur = Q.toBetaDiagram.schur) : ContactRelation false P Q := by
  have hF : Domain (P.r 0) (P.r 1) (P.r 2) (P.r 3) (P.r 4)
      z.val z.val z.val q.val := by simpa [hPg] using domain_of_profile P hP
  have hH : Domain (Q.r 0) (Q.r 1) (Q.r 2) (Q.r 3) (Q.r 4)
      z.val q.val z.val z.val := by simpa [hQg] using domain_of_profile Q hQ
  have he' : interval complete (P.r 0) (P.r 1) (P.r 2) (P.r 3) (P.r 4)
      z.val z.val z.val q.val =
      interval complete (Q.r 0) (Q.r 1) (Q.r 2) (Q.r 3) (Q.r 4)
      z.val q.val z.val z.val := by
    rw [Gluing.Profile.toBetaDiagram_schur,Gluing.Profile.toBetaDiagram_schur,
      schur_interval P hP.hessenberg,schur_interval Q hQ.hessenberg] at he
    simpa [interval,complete_eq_hh,hPg,hQg] using he
  obtain ⟨hp0,hp1,hp2,hp4,hq0,hq1,hq2,hq3,hq4⟩ := a1_cross_pattern_polynomial
    (P.r 0) (P.r 1) (P.r 2) (P.r 3) (P.r 4)
    (Q.r 0) (Q.r 1) (Q.r 2) (Q.r 3) (Q.r 4) z q hzq hF hH he'
  have hm : (q.val : ℤ)+z.val < P.r 3 := by
    have h := hP 2 3 (by rfl)
    simp [hPg] at h
    omega
  let X := StaircaseFiveFamilies.aParameters q.val (P.r 3) z.val
    (by positivity) (by exact_mod_cast hzq) hm
  refine ⟨X,Or.inl ?_,Or.inr (Or.inr (Or.inl ?_))⟩
  · apply Gluing.Profile.ext
    all_goals funext i; fin_cases i <;>
      simp [X,StaircaseFiveFamilies.aParameters,StaircaseFiveFamilies.m3F,
        StaircaseFiveFamilies.profile,hPg] <;> omega
  · apply Gluing.Profile.ext
    all_goals funext i; fin_cases i <;>
      simp [X,StaircaseFiveFamilies.aParameters,StaircaseFiveFamilies.m3H,
        StaircaseFiveFamilies.profile,hQg] <;> omega

private def OrderedInteriorFamily (a b c d e A B C D E q z : ℤ) : Prop :=
  a = c ∧ A = b ∧ B = a ∧ C = b ∧ e = b ∧ E = a ∧ d = D ∧
    d = a+b-q ∧ a ≠ b ∧ q+z < a ∧ q+z < b

private theorem interior_ordered_top_polynomial (a b c d e A B C D E : ℤ)
    (z q : ℕ+) (hzq : z.val < q.val)
    (hF : Domain a b c d e z.val q.val z.val z.val)
    (hH : Domain A B C D E z.val q.val z.val z.val)
    (he : interval complete a b c d e z.val q.val z.val z.val =
      interval complete A B C D E z.val q.val z.val z.val)
    (hX : a+b-z.val = A+B-z.val)
    (hY : c+d+e-2*z.val = C+D+E-2*z.val) :
    (a = A ∧ b = B ∧ c = C ∧ d = D ∧ e = E) ∨
      OrderedInteriorFamily a b c d e A B C D E q.val z.val := by
  have hz := z.pos
  have hq : (z.val : ℤ) < q.val := by exact_mod_cast hzq
  have ha := hF.2.2.2.2.1; have hb := hF.2.2.2.2.2.1
  have hc := hF.2.2.2.2.2.2.1
  have hd : 2*(z.val : ℤ) < d := by have h := hF.2.2.2.2.2.2.2.1; omega
  have he' := hF.2.2.2.2.2.2.2.2
  have hA := hH.2.2.2.2.1; have hB := hH.2.2.2.2.2.1
  have hC := hH.2.2.2.2.2.2.1
  have hD : 2*(z.val : ℤ) < D := by have h := hH.2.2.2.2.2.2.2.1; omega
  have hE := hH.2.2.2.2.2.2.2.2
  obtain ⟨hcore,hsingles,_,hlayer⟩ :=
    interior_equality_readings a b c d e A B C D E q.val z hq hF hH he
  by_cases hBb : B = b
  · have hCc : C = c := by rcases hcore with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> omega
    have hAa : A = a := by omega
    subst A
    subst B
    subst C
    have htotal : d+e = D+E := by omega
    have htail : complete e*two complete q.val (a+b-z.val) (c+d-z.val)+
        complete (d+e-z.val)*two complete q.val (a+b-z.val) c =
      complete E*two complete q.val (a+b-z.val) (c+D-z.val)+
        complete (D+E-z.val)*two complete q.val (a+b-z.val) c := by
      unfold interiorLayer at hlayer
      rw [hY] at hlayer
      exact add_right_cancel hlayer
    obtain ⟨hdD,heE⟩ := ordered_tail_reconstruction (a+b-z.val) c d e D E q.val z.val
      (by have := q.pos; exact_mod_cast this) (by exact_mod_cast hz) (by omega)
      (by omega) hd he' hD hE htotal htail
    exact Or.inl ⟨rfl,rfl,rfl,hdD,heE⟩
  · have hBc : B = c := by rcases hcore with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> omega
    have hCb : C = b := by rcases hcore with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> omega
    have hAne : A ≠ a := by omega
    have hAlloc : A = d ∨ A = e := by
      rcases hsingles with ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩ |
        ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩ <;> omega
    let x := a+b-z.val
    let y := c+d+e-2*z.val
    have hxy : x < y := by
      rcases hAlloc with hAlloc | hAlloc <;> dsimp [x,y] <;> omega
    let V : ℕ+ := ⟨y.toNat,by dsimp [y]; omega⟩
    have hV : (V.val : ℤ) = y := by dsimp [V,y]; omega
    have hVF : (V.val : ℤ) = max (a+b-z.val) (c+d+e-2*z.val) := by
      change (V.val : ℤ) = max x y
      rw [max_eq_right hxy.le]
      exact hV
    have hVH : (V.val : ℤ) = max (A+B-z.val) (C+D+E-2*z.val) := by
      rw [← hX,← hY]
      exact hVF
    have hpdF := interior_second_q_derivative a b c d e q.val z.val hF
      (by exact_mod_cast hz) hq q V rfl hVF
    have hpdH := interior_second_q_derivative A B C D E q.val z.val hH
      (by exact_mod_cast hz) hq q V rfl hVH
    have hmax : max (a+b-z.val) (c+d+e-2*z.val) = y := max_eq_right hxy.le
    rw [hmax] at hpdF
    rw [← hX,← hY,hmax] at hpdH
    have hxn : a+b-z.val ≠ y := ne_of_lt hxy
    have hyy : c+d+e-2*z.val = y := rfl
    simp only [if_neg hxn,if_pos hyy,ite_true,ite_false,zero_add] at hpdF hpdH
    have hmono := congrArg (fun p : CompleteRing => MvPolynomial.pderiv V (eraseGenerator q p)) hlayer
    rw [hpdF,hpdH,hBc] at hmono
    have han : a ≠ (q.val : ℤ) := by
      intro haq
      have hzero : eraseGenerator q (complete a) = 0 := by rw [haq]; simp [eraseGenerator_complete]
      rw [hzero,zero_mul] at hmono
      have hAz : eraseGenerator q (complete A) = 0 :=
        (mul_eq_zero.mp hmono.symm).resolve_right ((complete_ne_zero_iff c).mpr (by omega))
      have hAq := (erased_complete_zero_iff q A (by omega)).mp hAz
      exact hAne (by omega)
    have hAn : A ≠ (q.val : ℤ) := by
      intro hAq
      have hzero : eraseGenerator q (complete A) = 0 := by rw [hAq]; simp [eraseGenerator_complete]
      rw [hzero,zero_mul] at hmono
      have haz : eraseGenerator q (complete a) = 0 :=
        (mul_eq_zero.mp hmono).resolve_right ((complete_ne_zero_iff b).mpr (by omega))
      exact han ((erased_complete_zero_iff q a (by omega)).mp haz)
    rw [eraseGenerator_complete,if_neg han,eraseGenerator_complete,if_neg hAn] at hmono
    have hrows := complete_two_product_reading (by omega) (by omega) (by omega) (by omega) hmono
    have hac : c = a ∧ A = b := by
      rcases hrows with ⟨h1,h2⟩ | ⟨h1,h2⟩
      · omega
      · exact ⟨h1.symm,h2.symm⟩
    have hCa : c = a := hac.1
    have hAb : A = b := hac.2
    subst c
    subst A
    have hBa : B = a := by omega
    have hCb' : C = b := by omega
    subst B
    subst C
    have hab : a ≠ b := by omega
    have hap : (q.val : ℤ)+z.val < a := by omega
    have hbp : (q.val : ℤ)+z.val < b := by omega
    rcases hsingles with ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩ |
      ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩
    · omega
    · omega
    · have hDb : d = b := h2
      have hDa : D = a := h1.symm
      have hEe : E = e := h3.symm
      subst d
      subst D
      subst E
      have hzero : eraseGenerator q (interiorLayer complete a b a b e q.val z.val-
          interiorLayer complete b a b a e q.val z.val) = 0 := by
        rw [map_sub,hlayer,sub_self]
      exact False.elim (t1_erased_ne_zero a b e q.val z.val q rfl
        (by exact_mod_cast hz) hq hap hbp he' hab hzero)
    · have heB : e = b := h3
      have hDa : D = a := h1.symm
      have hEd : E = d := h2.symm
      subst e
      subst D
      subst E
      have hEq := (congrArg (eraseGenerator q) hlayer).symm
      have htm := t3_erased_eq_imp b a d q.val z.val q rfl
        (by exact_mod_cast hz) hq hbp hap hd hEq
      subst d
      have ht := (interior_t2_iff a b a q.val z.val
        (by exact_mod_cast hz) hq hap hbp (by omega) hab).mp hlayer
      omega
    · have hDb : d = b := h2
      have hEa : E = a := h1.symm
      have hDe : D = e := h3.symm
      subst d
      subst E
      subst D
      have hte : 2*(z.val : ℤ) < e := hD
      have hEq := congrArg (eraseGenerator q) hlayer
      have hem := t3_erased_eq_imp a b e q.val z.val q rfl
        (by exact_mod_cast hz) hq hap hbp hte hEq
      subst e
      have ht := (interior_t2_iff a b b q.val z.val
        (by exact_mod_cast hz) hq hap hbp (by omega) hab).mp hlayer
      omega
    · have heB : e = b := h3
      have hEa : E = a := h1.symm
      have hDd : D = d := h2.symm
      subst e
      subst E
      subst D
      have ht := (interior_t2_iff a b d q.val z.val
        (by exact_mod_cast hz) hq hap hbp hd hab).mp hlayer
      exact Or.inr ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,ht,hab,hap,hbp⟩

private theorem two_q_untouched (q : ℕ+) (r a b : ℤ)
    (hr : r ≠ (q.val : ℤ)) (ha : a ≠ (q.val : ℤ)) (hb : b ≠ (q.val : ℤ))
    (hab : a+b-r ≠ (q.val : ℤ)) :
    two (fun k => eraseGenerator q (complete k)) r a b = two complete r a b := by
  unfold two
  dsimp only
  rw [eraseGenerator_complete,if_neg ha,eraseGenerator_complete,if_neg hb,
    eraseGenerator_complete,if_neg hr,eraseGenerator_complete,if_neg hab]

private theorem three_q_untouched (q : ℕ+) (a b c r s : ℤ)
    (ha : a ≠ (q.val : ℤ)) (hb : b ≠ (q.val : ℤ)) (hc : c ≠ (q.val : ℤ))
    (hr : r ≠ (q.val : ℤ)) (hs : s ≠ (q.val : ℤ))
    (hu : a+b-r ≠ (q.val : ℤ)) (hv : b+c-s ≠ (q.val : ℤ))
    (hw : a+b+c-r-s ≠ (q.val : ℤ)) :
    threeInterval (fun k => eraseGenerator q (complete k)) a b c r s =
      threeInterval complete a b c r s := by
  unfold threeInterval
  dsimp only
  rw [eraseGenerator_complete,if_neg ha,eraseGenerator_complete,if_neg hb,
    eraseGenerator_complete,if_neg hc,eraseGenerator_complete,if_neg hu,
    eraseGenerator_complete,if_neg hr,eraseGenerator_complete,if_neg hv,
    eraseGenerator_complete,if_neg hs,eraseGenerator_complete,if_neg hw]

private theorem interior_full_q_specialization (a b c d e A B C D E z : ℤ) (q : ℕ+)
    (he : interval complete a b c d e z q.val z z =
      interval complete A B C D E z q.val z z) :
    two (fun k => eraseGenerator q (complete k)) z a b*
      threeInterval (fun k => eraseGenerator q (complete k)) c d e z z =
    two (fun k => eraseGenerator q (complete k)) z A B*
      threeInterval (fun k => eraseGenerator q (complete k)) C D E z z := by
  have h := congrArg (eraseGenerator q) he
  rw [erase_interval,erase_interval] at h
  have hq0 : (fun k => eraseGenerator q (complete k)) q.val = 0 := by
    simp [eraseGenerator_complete]
  rw [interior_q_cut _ a b c d e q.val z hq0,
    interior_q_cut _ A B C D E q.val z hq0] at h
  exact h

private theorem associated_totalDegree_eq (f g : CompleteRing)
    (hf : f ≠ 0) (h : Associated f g) : f.totalDegree = g.totalDegree := by
  obtain ⟨u,hu⟩ := h
  have hd : ((u : CompleteRing)).totalDegree = 0 :=
    (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp u.isUnit).2
  have he := congrArg MvPolynomial.totalDegree hu
  rw [MvPolynomial.totalDegree_mul_of_isDomain hf u.isUnit.ne_zero,hd,Nat.add_zero] at he
  exact he

private theorem associated_augmentation_zero (f g : CompleteRing)
    (h : Associated f g) (hf : Staircase.residualAugmentation f = 0) :
    Staircase.residualAugmentation g = 0 := by
  obtain ⟨u,hu⟩ := h
  have he := congrArg Staircase.residualAugmentation hu
  rw [map_mul,hf,zero_mul] at he
  exact he.symm

private theorem two_augmentation (z a b : ℤ) (hz : 0 < z) (ha : z < a) (hb : z < b) :
    Staircase.residualAugmentation (two complete z a b) = 0 := by
  simp only [two,map_sub,map_mul,Staircase.residualAugmentation_complete hz,
    Staircase.residualAugmentation_complete (show 0 < a by omega),
    Staircase.residualAugmentation_complete (show 0 < b by omega),
    Staircase.residualAugmentation_complete (show 0 < a+b-z by omega)]
  norm_num

/-- The interval-contact cubic is the actual canonical primitive of its
three-row component.  Irreducibility is proved after restriction, not assumed
to survive a specialization. -/
theorem interval_contact_cubic_data (c d e : ℤ) (z q : ℕ+)
    (hzq : z.val < q.val) (hc : (q.val : ℤ)+z.val < c)
    (hd : 2*(z.val : ℤ) < d) (he : (z.val : ℤ) < e)
    (hde : d+e-z.val = q.val) :
    eraseGenerator q (threeInterval complete c d e z.val z.val) =
      Staircase.intervalContactCubic q.val e d c z.val z.val ∧
    Irreducible (Staircase.intervalContactCubic q.val e d c z.val z.val) ∧
    (Staircase.intervalContactCubic q.val e d c z.val z.val).totalDegree = 3 := by
  have hz := z.pos
  let P := qTripleProfile e d c z q hzq he hd hc
  let hP := qTriple_component e d c z q hzq he hd hc
  have hen : e ≠ (q.val : ℤ) := by omega
  have hdn : d ≠ (q.val : ℤ) := by omega
  have hu : ((P.r 0 : ℤ)+P.r 1-P.g 0) = q.val := by
    simp [P,qTripleProfile,threeConstantProfile]
    omega
  have has : P.r 0 ≠ P.g 1 := by
    simp [P,qTripleProfile,threeConstantProfile]
    omega
  have hec : ((e.toNat : ℕ) : ℤ) = e := by omega
  have hdc : ((d.toNat : ℕ) : ℤ) = d := by omega
  have hcc : ((c.toNat : ℕ) : ℤ) = c := by omega
  have hcanon : Staircase.canonicalPrimitive hP =
      Staircase.intervalContactCubic q.val e d c z.val z.val := by
    have h := Staircase.canonical_three_interval_cubic hP hu has
    simpa [P,qTripleProfile,threeConstantProfile,hec,hdc,hcc] using h
  have hrest := qTriple_canonical_of_content_one e d c z q hzq he hd hc hen hdn
  have hrest' : Staircase.restriction q P =
      Staircase.intervalContactCubic q.val e d c z.val z.val := hrest.symm.trans hcanon
  have herase : eraseGenerator q (threeInterval complete c d e z.val z.val) =
      Staircase.intervalContactCubic q.val e d c z.val z.val := by
    unfold Staircase.restriction at hrest'
    rw [qTriple_schur,threeInterval_reverse complete c d e z.val z.val] at hrest'
    exact hrest'
  refine ⟨herase,?_,?_⟩
  · rw [← hcanon]
    exact Staircase.canonicalPrimitive_irreducible hP
  · rw [← hcanon]
    exact qTriple_canonical_degree_three e d c z q hzq he hd hc hen hdn

private theorem quadratic_not_dvd_generator_times_cubic (D : BetaDiagram 2) (X : BetaDiagram 1)
    (hD : D.Connected) (f : CompleteRing) (hf : Irreducible f) (hd : f.totalDegree = 3) :
    ¬ D.schur ∣ X.schur*f := by
  have hDi := D.schur_irreducible hD
  have hDp := UniqueFactorizationMonoid.irreducible_iff_prime.mp hDi
  intro hdiv
  rcases hDp.dvd_or_dvd hdiv with hX | hF
  · exact nonlinear_not_dvd_singleton D hD X hX
  · have ha := hDi.associated_of_dvd hf hF
    have hdeg := associated_totalDegree_eq D.schur f D.schur_ne_zero ha
    rw [D.schur_totalDegree,hd] at hdeg
    norm_num at hdeg

private theorem M_not_dvd_B_product (q z a c A B C D : ℤ)
    (hz : 0 < z) (hq : 2*z < q) (ha : z < a) (hc : z < c)
    (hA : z < A) (hB : z < B) (hC : z < C) (hD : z < D) :
    ¬ Staircase.quadraticM q z a c ∣ two complete z A B*two complete z C D := by
  have hMi := Staircase.quadraticM_irreducible q z a c hz hq ha hc
  have hMp := UniqueFactorizationMonoid.irreducible_iff_prime.mp hMi
  have hMag := Staircase.quadraticM_augmentation q z a c hz hq ha hc
  have hR1 : Irreducible (two complete z A B) := by
    let P := twoScalarProfile A B z hz.le hA hB
    simpa only [P,twoScalarProfile_schur] using P.toBetaDiagram.schur_irreducible P.toBetaDiagram_connected
  have hR2 : Irreducible (two complete z C D) := by
    let P := twoScalarProfile C D z hz.le hC hD
    simpa only [P,twoScalarProfile_schur] using P.toBetaDiagram.schur_irreducible P.toBetaDiagram_connected
  intro hdiv
  rcases hMp.dvd_or_dvd hdiv with h1 | h2
  · have hAssoc := hMi.associated_of_dvd hR1 h1
    have hzero := associated_augmentation_zero _ _ hAssoc.symm (two_augmentation z A B hz hA hB)
    rw [hMag] at hzero
    norm_num at hzero
  · have hAssoc := hMi.associated_of_dvd hR2 h2
    have hzero := associated_augmentation_zero _ _ hAssoc.symm (two_augmentation z C D hz hC hD)
    rw [hMag] at hzero
    norm_num at hzero

/-- The q-erased full second layer produces the two swapped-top contact
alternatives and excludes simultaneous vanishing of both positive terms. -/
theorem interior_swapped_contacts (a b c d e A B C D E : ℤ) (z q : ℕ+)
    (hzq : z.val < q.val)
    (hF : Domain a b c d e z.val q.val z.val z.val)
    (hH : Domain A B C D E z.val q.val z.val z.val)
    (he : interval complete a b c d e z.val q.val z.val z.val =
      interval complete A B C D E z.val q.val z.val z.val)
    (hxy : c+d+e-2*z.val < a+b-z.val)
    (hX : a+b-z.val = C+D+E-2*z.val)
    (hY : c+d+e-2*z.val = A+B-z.val) :
    A ≠ (q.val : ℤ) ∧
      (e = (q.val : ℤ) ∨ d+e-z.val = q.val) ∧
      (eraseGenerator q (complete e)*complete (c+d-z.val)+
        eraseGenerator q (complete (d+e-z.val))*complete c =
        eraseGenerator q (complete A)*complete B) := by
  have hz := z.pos
  have ha := hF.2.2.2.2.1; have hb := hF.2.2.2.2.2.1
  have hc := hF.2.2.2.2.2.2.1
  have hd : 2*(z.val : ℤ) < d := by have h := hF.2.2.2.2.2.2.2.1; omega
  have he' := hF.2.2.2.2.2.2.2.2
  have hA := hH.2.2.2.2.1; have hB := hH.2.2.2.2.2.1
  let V : ℕ+ := ⟨(a+b-z.val).toNat,by omega⟩
  have hV : (V.val : ℤ) = a+b-z.val := by dsimp [V]; omega
  have hVF : (V.val : ℤ) = max (a+b-z.val) (c+d+e-2*z.val) := by
    rw [max_eq_left hxy.le]
    exact hV
  have hVH : (V.val : ℤ) = max (A+B-z.val) (C+D+E-2*z.val) := by
    rw [← hX,← hY,max_eq_right hxy.le]
    exact hV
  have hdF := interior_second_q_derivative a b c d e q.val z.val hF
    (by exact_mod_cast hz) (by exact_mod_cast hzq) q V rfl hVF
  have hdH := interior_second_q_derivative A B C D E q.val z.val hH
    (by exact_mod_cast hz) (by exact_mod_cast hzq) q V rfl hVH
  rw [max_eq_left hxy.le] at hdF
  rw [← hX,← hY,max_eq_right hxy.le] at hdH
  simp only [if_pos rfl,if_neg (ne_of_lt hxy),ite_true,ite_false,add_zero,zero_add] at hdF hdH
  have hlayer := (interior_equality_readings a b c d e A B C D E q.val z
    (by exact_mod_cast hzq) hF hH he).2.2.2
  have hmono := congrArg (fun p : CompleteRing => MvPolynomial.pderiv V (eraseGenerator q p)) hlayer
  rw [hdF,hdH] at hmono
  have haug := congrArg Staircase.residualAugmentation hmono
  simp only [map_add,map_mul,
    erased_complete_augmentation q e (by omega),
    erased_complete_augmentation q (d+e-z.val) (by omega),
    erased_complete_augmentation q A (by omega),
    Staircase.residualAugmentation_complete (show 0 < c+d-z.val by omega),
    Staircase.residualAugmentation_complete (show 0 < c by omega),
    Staircase.residualAugmentation_complete (show 0 < B by omega),mul_one] at haug
  have hcon : A ≠ (q.val : ℤ) ∧ (e = (q.val : ℤ) ∨ d+e-z.val = q.val) := by
    by_cases heq : e = (q.val : ℤ) <;>
      by_cases hdeq : d+e-z.val = q.val <;> by_cases hAq : A = (q.val : ℤ)
    all_goals norm_num [heq,hdeq,hAq] at haug
    all_goals constructor <;> try assumption
    all_goals first | exact Or.inl heq | exact Or.inr hdeq | omega
  exact ⟨hcon.1,hcon.2,hmono⟩

private theorem interior_swapped_interval_false (a b c d e A B C D E : ℤ)
    (z q : ℕ+) (hzq : z.val < q.val)
    (hF : Domain a b c d e z.val q.val z.val z.val)
    (hH : Domain A B C D E z.val q.val z.val z.val)
    (he : interval complete a b c d e z.val q.val z.val z.val =
      interval complete A B C D E z.val q.val z.val z.val)
    (hxy : c+d+e-2*z.val < a+b-z.val)
    (hX : a+b-z.val = C+D+E-2*z.val)
    (hY : c+d+e-2*z.val = A+B-z.val)
    (hde : d+e-z.val = q.val) : False := by
  have hz := z.pos
  have ha := hF.2.2.2.2.1; have hb := hF.2.2.2.2.2.1
  have hc := hF.2.2.2.2.2.2.1
  have hd : 2*(z.val : ℤ) < d := by have h := hF.2.2.2.2.2.2.2.1; omega
  have he' := hF.2.2.2.2.2.2.2.2
  have hA := hH.2.2.2.2.1; have hB := hH.2.2.2.2.2.1
  have hC := hH.2.2.2.2.2.2.1
  have hD : 2*(z.val : ℤ) < D := by have h := hH.2.2.2.2.2.2.2.1; omega
  have hE := hH.2.2.2.2.2.2.2.2
  obtain ⟨han,_,hmono⟩ := interior_swapped_contacts a b c d e A B C D E z q
    hzq hF hH he hxy hX hY
  obtain ⟨hcore,hsingle,_,_⟩ := interior_equality_readings a b c d e A B C D E q.val z
    (by exact_mod_cast hzq) hF hH he
  have hen : e ≠ (q.val : ℤ) := by omega
  rw [eraseGenerator_complete,if_neg hen,eraseGenerator_complete,if_pos hde,
    zero_mul,add_zero,eraseGenerator_complete,if_neg han] at hmono
  have hp := complete_two_product_reading (by omega) (by omega) (by omega) (by omega) hmono
  have hAB : A = e ∧ B = c+d-z.val := by
    rcases hp with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · exact ⟨h1.symm,h2.symm⟩
    · omega
  have hBb : B = b ∧ C = c := by
    rcases hcore with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> constructor <;> omega
  have hAe : A = e := hAB.1
  have hB' : B = b := hBb.1
  have hC' : C = c := hBb.2
  subst A
  subst B
  subst C
  have hae : e < a := by omega
  have hDE : (D = a ∧ E = d) ∨ (D = d ∧ E = a) := by
    rcases hsingle with ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩ |
      ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩ <;> omega
  obtain ⟨hIbar,hIi,hId⟩ := interval_contact_cubic_data c d e z q hzq
    (by omega) hd he' hde
  let I := Staircase.intervalContactCubic q.val e d c z.val z.val
  let bar := fun k : ℤ => eraseGenerator q (complete k)
  have hbarI : threeInterval bar c d e z.val z.val = I := by
    simpa only [I,bar,threeInterval,map_add,map_sub,map_mul] using hIbar
  have hbarz : bar z.val = complete z.val := by
    simp [bar,eraseGenerator_complete,show (z.val : ℤ) ≠ q.val by omega]
  have hbarq : bar q.val = 0 := by simp [bar,eraseGenerator_complete]
  have hRight : two bar z.val e b = two complete z.val e b :=
    two_q_untouched q z.val e b (by omega) (by omega) (by omega) (by omega)
  have hcut := interior_full_q_specialization a b c d e e b c D E z.val q he
  rw [hbarI,hRight] at hcut
  by_cases haq : a = (q.val : ℤ)
  · subst a
    have hLeft : two bar z.val q.val b =
        -complete z.val*complete ((q.val : ℤ)+b-z.val) := by
      unfold two
      rw [hbarq,hbarz,show bar ((q.val : ℤ)+b-z.val) =
        complete ((q.val : ℤ)+b-z.val) from erase_complete_of_lt q _ (by omega)]
      ring
    rw [hLeft] at hcut
    have hTailDiv : complete z.val ∣ threeInterval bar c D E z.val z.val := by
      rcases hDE with ⟨hDq,hEd⟩ | ⟨hDd,hEq⟩
      · rw [hDq,three_contact_middle bar c E q.val z.val hbarq,hbarz]
        exact dvd_mul_right _ _
      · rw [hEq,three_contact_end bar c D q.val z.val hbarq,hbarz]
        refine ⟨-two bar z.val c (D+q.val-z.val),?_⟩
        ring
    obtain ⟨K,hK⟩ := hTailDiv
    rw [hK] at hcut
    have hcancel : -complete ((q.val : ℤ)+b-z.val)*I =
        two complete z.val e b*K := by
      apply mul_left_cancel₀ ((complete_ne_zero_iff z.val).mpr (by positivity))
      linear_combination hcut
    have hdiv : two complete z.val e b ∣ complete ((q.val : ℤ)+b-z.val)*I := by
      refine ⟨-K,?_⟩
      linear_combination -hcancel
    let R := (twoScalarProfile e b z.val (by positivity) he' (by omega)).toBetaDiagram
    let X := (scalarSingleton ((q.val : ℤ)+b-z.val) (by omega)).toBetaDiagram
    have hn := quadratic_not_dvd_generator_times_cubic R X
      (Gluing.Profile.toBetaDiagram_connected _) I hIi hId
    apply hn
    simpa only [R,X,twoScalarProfile_schur,scalarSingleton_schur] using hdiv
  · have hLeft : two bar z.val a b = two complete z.val a b :=
      two_q_untouched q z.val a b (by omega) haq (by omega) (by omega)
    have hDn : D ≠ (q.val : ℤ) := by rcases hDE with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> omega
    have hEn : E ≠ (q.val : ℤ) := by rcases hDE with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> omega
    have hsumDE : D+E = a+d := by rcases hDE with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> omega
    have hTail : threeInterval bar c D E z.val z.val =
        threeInterval complete c D E z.val z.val :=
      three_q_untouched q c D E z.val z.val (by omega) hDn hEn (by omega) (by omega)
        (by omega) (by omega) (by omega)
    rw [hLeft,hTail] at hcut
    let R := (twoScalarProfile a b z.val (by positivity) ha (by omega)).toBetaDiagram
    let S := (twoScalarProfile e b z.val (by positivity) he' (by omega)).toBetaDiagram
    let T := (threeConstantProfile c D E z.val (by positivity) (by omega) hD hE).toBetaDiagram
    have hRi := R.schur_irreducible (Gluing.Profile.toBetaDiagram_connected _)
    have hRp := UniqueFactorizationMonoid.irreducible_iff_prime.mp hRi
    have hdiv : R.schur ∣ S.schur*T.schur := by
      rw [twoScalarProfile_schur,twoScalarProfile_schur,threeConstantProfile_schur,← hcut]
      exact dvd_mul_right _ _
    rcases hRp.dvd_or_dvd hdiv with hS | hT
    · have heq := full_schur_associated_eq R S
        (hRi.associated_of_dvd (S.schur_irreducible (Gluing.Profile.toBetaDiagram_connected _)) hS)
      have hpairs := two_scalar_rigidity a b e b z.val (by positivity) ha (by omega) he' (by omega)
        (by simpa only [R,S,twoScalarProfile_schur] using heq)
      rcases hpairs with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> omega
    · have heq := full_schur_associated_eq R T
        (hRi.associated_of_dvd (T.schur_irreducible (Gluing.Profile.toBetaDiagram_connected _)) hT)
      have hn := R.row_count_of_schur_eq T heq
      norm_num at hn

private theorem interior_swapped_row_false (a b c d A B C D E : ℤ)
    (z q : ℕ+) (hzq : z.val < q.val)
    (hF : Domain a b c d q.val z.val q.val z.val z.val)
    (hH : Domain A B C D E z.val q.val z.val z.val)
    (he : interval complete a b c d q.val z.val q.val z.val z.val =
      interval complete A B C D E z.val q.val z.val z.val)
    (hxy : c+d+q.val-2*z.val < a+b-z.val)
    (hX : a+b-z.val = C+D+E-2*z.val)
    (hY : c+d+q.val-2*z.val = A+B-z.val) : False := by
  have hz := z.pos
  have ha := hF.2.2.2.2.1; have hb := hF.2.2.2.2.2.1
  have hc := hF.2.2.2.2.2.2.1
  have hd : 2*(z.val : ℤ) < d := by have h := hF.2.2.2.2.2.2.2.1; omega
  have hA := hH.2.2.2.2.1; have hB := hH.2.2.2.2.2.1
  have hC := hH.2.2.2.2.2.2.1
  have hD : 2*(z.val : ℤ) < D := by have h := hH.2.2.2.2.2.2.2.1; omega
  have hE := hH.2.2.2.2.2.2.2.2
  obtain ⟨hAn,_,hmono⟩ := interior_swapped_contacts a b c d q.val A B C D E z q
    hzq hF hH he hxy hX hY
  obtain ⟨hcore,hsingle,_,hlayer⟩ := interior_equality_readings a b c d q.val A B C D E q.val z
    (by exact_mod_cast hzq) hF hH he
  rw [eraseGenerator_complete,if_pos rfl,zero_mul,zero_add,
    erase_complete_of_lt q (d+q.val-z.val) (by omega),
    eraseGenerator_complete,if_neg hAn] at hmono
  have hp := complete_two_product_reading (by omega) (by omega) (by omega) (by omega) hmono
  have hAgt : (q.val : ℤ) < A := by
    rcases hp with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> omega
  have han : a ≠ (q.val : ℤ) := by
    intro haq
    have hAd : A = d := by
      rcases hsingle with ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩ |
        ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩ <;> omega
    rcases hp with ⟨h1,h2⟩ | ⟨h1,h2⟩
    all_goals rcases hcore with ⟨hc1,hc2⟩ | ⟨hc1,hc2⟩
    all_goals omega
  have hDEq : D = (q.val : ℤ) ∨ E = (q.val : ℤ) := by
    rcases hsingle with ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩ |
      ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩ <;> omega
  let bar := fun k : ℤ => eraseGenerator q (complete k)
  have hbarq : bar q.val = 0 := by simp [bar,eraseGenerator_complete]
  have hbarz : bar z.val = complete z.val := by
    simp [bar,eraseGenerator_complete,show (z.val : ℤ) ≠ q.val by omega]
  have hLeft : two bar z.val a b = two complete z.val a b :=
    two_q_untouched q z.val a b (by omega) han (by omega) (by omega)
  have hRight : two bar z.val A B = two complete z.val A B :=
    two_q_untouched q z.val A B (by omega) hAn (by omega) (by omega)
  have hTail : threeInterval bar c d q.val z.val z.val =
      -complete z.val*two complete z.val c (d+q.val-z.val) := by
    rw [three_contact_end bar c d q.val z.val hbarq,hbarz,
      two_q_untouched q z.val c (d+q.val-z.val) (by omega) (by omega) (by omega) (by omega)]
  have hcut := interior_full_q_specialization a b c d q.val A B C D E z.val q he
  rw [hLeft,hRight,hTail] at hcut
  by_cases hEq : E = (q.val : ℤ)
  · subst E
    have hMate : threeInterval bar C D q.val z.val z.val =
        -complete z.val*two complete z.val C (D+q.val-z.val) := by
      rw [three_contact_end bar C D q.val z.val hbarq,hbarz,
        two_q_untouched q z.val C (D+q.val-z.val) (by omega) (by omega) (by omega) (by omega)]
    rw [hMate] at hcut
    have hprod : two complete z.val a b*two complete z.val c (d+q.val-z.val) =
        two complete z.val A B*two complete z.val C (D+q.val-z.val) := by
      apply mul_left_cancel₀ (neg_ne_zero.mpr ((complete_ne_zero_iff z.val).mpr (by positivity)))
      linear_combination hcut
    let P1 := (twoScalarProfile a b z.val (by positivity) ha (by omega)).toBetaDiagram
    let P2 := (twoScalarProfile c (d+q.val-z.val) z.val (by positivity) (by omega) (by omega)).toBetaDiagram
    let Q1 := (twoScalarProfile A B z.val (by positivity) hA (by omega)).toBetaDiagram
    let Q2 := (twoScalarProfile C (D+q.val-z.val) z.val (by positivity) (by omega) (by omega)).toBetaDiagram
    have hprod' : P1.schur*P2.schur = Q1.schur*Q2.schur := by
      simpa only [P1,P2,Q1,Q2,twoScalarProfile_schur] using hprod
    have hmatch := connected_two_factor_reading P1 P2 Q1 Q2
      (Gluing.Profile.toBetaDiagram_connected _) (Gluing.Profile.toBetaDiagram_connected _)
      (Gluing.Profile.toBetaDiagram_connected _) (Gluing.Profile.toBetaDiagram_connected _) hprod'
    have hp1 :
        (a = C ∧ b = D+q.val-z.val) ∨ (a = D+q.val-z.val ∧ b = C) := by
      rcases hmatch with ⟨h1,h2⟩ | ⟨h1,h2⟩
      · have h := two_scalar_rigidity a b A B z.val (by positivity) ha (by omega) hA (by omega)
          (by simpa only [P1,Q1,twoScalarProfile_schur] using h1)
        rcases h with ⟨h1',h2'⟩ | ⟨h1',h2'⟩ <;> omega
      · exact two_scalar_rigidity a b C (D+q.val-z.val) z.val (by positivity)
          ha (by omega) (by omega) (by omega)
          (by simpa only [P1,Q2,twoScalarProfile_schur] using h1)
    have hp2 :
        (c = A ∧ d+q.val-z.val = B) ∨ (c = B ∧ d+q.val-z.val = A) := by
      rcases hmatch with ⟨h1,h2⟩ | ⟨h1,h2⟩
      · have h := two_scalar_rigidity a b A B z.val (by positivity) ha (by omega) hA (by omega)
          (by simpa only [P1,Q1,twoScalarProfile_schur] using h1)
        rcases h with ⟨h1',h2'⟩ | ⟨h1',h2'⟩ <;> omega
      · exact two_scalar_rigidity c (d+q.val-z.val) A B z.val (by positivity)
          (by omega) (by omega) hA (by omega)
          (by simpa only [P2,Q1,twoScalarProfile_schur] using h2)
    have hAD : (a = A ∧ d = D) ∨ (a = D ∧ d = A) := by
      rcases hsingle with ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩ |
        ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩ <;> omega
    have hmAD : a^2+d^2 = A^2+D^2 := by
      rcases hAD with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> rw [h1,h2] <;> ring
    have hm1 : a^2+b^2 = C^2+(D+q.val-z.val)^2 := by
      rcases hp1 with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> rw [h1,h2] <;> ring
    have hm2 : c^2+(d+q.val-z.val)^2 = A^2+B^2 := by
      rcases hp2 with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> rw [h1,h2] <;> ring
    have hmCore : b^2+c^2 = B^2+C^2 := by
      rcases hcore with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> rw [h1,h2] <;> ring
    have hdelta2 : (2 : ℤ)*(((q.val : ℤ)-z.val)*(d-D)) = 0 := by
      linear_combination hm1+hm2-hmAD-hmCore
    have hdelta : ((q.val : ℤ)-z.val)*(d-D) = 0 :=
      (mul_eq_zero.mp hdelta2).resolve_left (by norm_num)
    have hdD : d = D := sub_eq_zero.mp
      ((mul_eq_zero.mp hdelta).resolve_left (by omega))
    have haA : a = A := by rcases hAD with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> omega
    subst A
    subst D
    have hswap : B = c ∧ C = b := by
      rcases hcore with ⟨h1,h2⟩ | ⟨h1,h2⟩
      · omega
      · exact ⟨h2.symm,h1.symm⟩
    have hBc : B = c := hswap.1
    have hCb : C = b := hswap.2
    subst B
    subst C
    have haq : a = d+q.val-z.val := by
      rcases hp2 with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> omega
    have hbc : b ≠ c := by omega
    rw [haq] at hlayer
    exact interior_swapped_layer_ne b c d q.val z.val (by exact_mod_cast hz)
      (by exact_mod_cast hzq) (by omega) (by omega) hd hbc hlayer
  · have hDq : D = (q.val : ℤ) := hDEq.resolve_right hEq
    subst D
    have hq2 : 2*(z.val : ℤ) < q.val := hD
    have hMate : threeInterval bar C q.val E z.val z.val =
        complete z.val*Staircase.quadraticM q.val z.val C E := by
      rw [three_contact_middle bar C E q.val z.val hbarq,hbarz]
      unfold Staircase.quadraticM
      simp (disch := omega) [bar,eraseGenerator_complete,if_pos,if_neg]
      <;> ring_nf
    rw [hMate] at hcut
    have hnorm : -two complete z.val a b*two complete z.val c (d+q.val-z.val) =
        two complete z.val A B*Staircase.quadraticM q.val z.val C E := by
      apply mul_left_cancel₀ ((complete_ne_zero_iff z.val).mpr (by positivity))
      linear_combination hcut
    have hdiv : Staircase.quadraticM q.val z.val C E ∣
        two complete z.val a b*two complete z.val c (d+q.val-z.val) := by
      refine ⟨-two complete z.val A B,?_⟩
      linear_combination -hnorm
    exact M_not_dvd_B_product q.val z.val C E a b c (d+q.val-z.val)
      (by exact_mod_cast hz) hq2 (by omega) hE ha (by omega) (by omega) (by omega) hdiv

private theorem interior_swapped_top_false (a b c d e A B C D E : ℤ)
    (z q : ℕ+) (hzq : z.val < q.val)
    (hF : Domain a b c d e z.val q.val z.val z.val)
    (hH : Domain A B C D E z.val q.val z.val z.val)
    (he : interval complete a b c d e z.val q.val z.val z.val =
      interval complete A B C D E z.val q.val z.val z.val)
    (hxy : c+d+e-2*z.val < a+b-z.val)
    (hX : a+b-z.val = C+D+E-2*z.val)
    (hY : c+d+e-2*z.val = A+B-z.val) : False := by
  have hc := (interior_swapped_contacts a b c d e A B C D E z q hzq
    hF hH he hxy hX hY).2.1
  rcases hc with heq | hdeq
  · subst e
    exact interior_swapped_row_false a b c d A B C D E z q hzq hF hH he hxy hX hY
  · exact interior_swapped_interval_false a b c d e A B C D E z q hzq
      hF hH he hxy hX hY hdeq

private theorem interior_polynomial_classification (a b c d e A B C D E : ℤ)
    (z q : ℕ+) (hzq : z.val < q.val)
    (hF : Domain a b c d e z.val q.val z.val z.val)
    (hH : Domain A B C D E z.val q.val z.val z.val)
    (he : interval complete a b c d e z.val q.val z.val z.val =
      interval complete A B C D E z.val q.val z.val z.val) :
    (a = A ∧ b = B ∧ c = C ∧ d = D ∧ e = E) ∨
      OrderedInteriorFamily a b c d e A B C D E q.val z.val := by
  have htop := (interior_equality_readings a b c d e A B C D E q.val z
    (by exact_mod_cast hzq) hF hH he).2.2.1
  rcases htop with ⟨hX,hY⟩ | ⟨hX,hY⟩
  · exact interior_ordered_top_polynomial a b c d e A B C D E z q hzq hF hH he hX hY
  · by_cases hbal : a+b-z.val = c+d+e-2*z.val
    · exact interior_ordered_top_polynomial a b c d e A B C D E z q hzq hF hH he
        (by omega) (by omega)
    · rcases lt_or_gt_of_ne hbal with hlt | hgt
      · exact False.elim (interior_swapped_top_false A B C D E a b c d e z q hzq
          hH hF he.symm (by omega) hY.symm hX.symm)
      · exact False.elim (interior_swapped_top_false a b c d e A B C D E z q hzq
          hF hH he hgt hX hY)

/-- `lem:staircase-interior` on actual profiles.  The full q-specialization is
used in addition to the three minimum layers, including balanced top pairs,
row contacts, and simultaneous row/merged-interval contacts. -/
theorem interior_large_seam_classification (P Q : Gluing.Profile 4)
    (hP : Staircase.Thick P) (hQ : Staircase.Thick Q) (z q : ℕ+)
    (hzq : z.val < q.val)
    (hPg : P.g = ![z.val,q.val,z.val,z.val])
    (hQg : Q.g = ![z.val,q.val,z.val,z.val])
    (he : P.toBetaDiagram.schur = Q.toBetaDiagram.schur) : P = Q ∨ BRelation P Q := by
  have hF : Domain (P.r 0) (P.r 1) (P.r 2) (P.r 3) (P.r 4)
      z.val q.val z.val z.val := by simpa [hPg] using domain_of_profile P hP
  have hH : Domain (Q.r 0) (Q.r 1) (Q.r 2) (Q.r 3) (Q.r 4)
      z.val q.val z.val z.val := by simpa [hQg] using domain_of_profile Q hQ
  have he' : interval complete (P.r 0) (P.r 1) (P.r 2) (P.r 3) (P.r 4)
      z.val q.val z.val z.val =
      interval complete (Q.r 0) (Q.r 1) (Q.r 2) (Q.r 3) (Q.r 4)
      z.val q.val z.val z.val := by
    rw [Gluing.Profile.toBetaDiagram_schur,Gluing.Profile.toBetaDiagram_schur,
      schur_interval P hP.hessenberg,schur_interval Q hQ.hessenberg] at he
    simpa [interval,complete_eq_hh,hPg,hQg] using he
  rcases interior_polynomial_classification
      (P.r 0) (P.r 1) (P.r 2) (P.r 3) (P.r 4)
      (Q.r 0) (Q.r 1) (Q.r 2) (Q.r 3) (Q.r 4) z q hzq hF hH he'
      with ⟨h0,h1,h2,h3,h4⟩ | hB
  · left
    apply Gluing.Profile.ext
    · exact five_rows_eq_of_cast P Q h0 h1 h2 h3 h4
    · exact hPg.trans hQg.symm
  · rcases hB with ⟨h02,hA,hB,hC,hE,hQE,hD,hlong,hne,hp,hm⟩
    let X : BParameters :=
      { p := P.r 0
        m := P.r 1
        z := z.val
        w := q.val
        z_pos := by have := z.pos; exact_mod_cast this
        w_pos := by have := q.pos; exact_mod_cast this
        p_gt := by omega
        m_gt := by omega
        p_ne_m := hne }
    right
    refine ⟨X,Or.inl ?_,Or.inr (Or.inr (Or.inr ?_))⟩
    · apply Gluing.Profile.ext
      all_goals funext i; fin_cases i <;>
        simp [X,BParameters.F,bProfileF,profile,hPg] <;> omega
    · apply Gluing.Profile.ext
      all_goals funext i; fin_cases i <;>
        simp [X,BParameters.H,bProfileH,profile,Gluing.Profile.rotate,hQg] <;> omega

theorem contact_relation_symm {second : Bool} {P Q : Gluing.Profile 4}
    (h : ContactRelation second P Q) : ContactRelation second Q P := by
  obtain ⟨X,hP,hQ⟩ := h
  exact ⟨X,hQ,hP⟩

private theorem contact_member_unrotate {second : Bool} {P : Gluing.Profile 4}
    {X : StaircaseFiveFamilies.ContactParameters}
    (h : ContactMember second P.rotate X) : ContactMember second P X := by
  cases second <;> dsimp [ContactMember] at h ⊢
  all_goals rcases h with h | h | h | h
  all_goals first
    | (left; simpa using congrArg Gluing.Profile.rotate h)
    | (right; left; simpa using congrArg Gluing.Profile.rotate h)
    | (right; right; left; simpa using congrArg Gluing.Profile.rotate h)
    | (right; right; right; simpa using congrArg Gluing.Profile.rotate h)

theorem contact_relation_rotate_right {second : Bool} {P Q : Gluing.Profile 4}
    (h : ContactRelation second P Q.rotate) : ContactRelation second P Q := by
  obtain ⟨X,hP,hQ⟩ := h
  exact ⟨X,hP,contact_member_unrotate hQ⟩

theorem contact_relation_rotate_left {second : Bool} {P Q : Gluing.Profile 4}
    (h : ContactRelation second P.rotate Q) : ContactRelation second P Q :=
  contact_relation_symm (contact_relation_rotate_right (contact_relation_symm h))

def profileOrientation {n : ℕ} (P : Gluing.Profile n) (rev : Bool) : Gluing.Profile n :=
  if rev then P.rotate else P

theorem profileOrientation_thick {n : ℕ} (P : Gluing.Profile n)
    (hP : Staircase.Thick P) (rev : Bool) : Staircase.Thick (profileOrientation P rev) := by
  cases rev
  · exact hP
  · exact thick_rotate hP

theorem profileOrientation_schur {n : ℕ} (P : Gluing.Profile n) (rev : Bool) :
    (profileOrientation P rev).toBetaDiagram.schur = P.toBetaDiagram.schur := by
  cases rev <;> simp [profileOrientation,Gluing.Profile.toBetaDiagram_schur,Gluing.Profile.schur_rotate]

private theorem equality_unorient {P Q : Gluing.Profile 4} {r s : Bool}
    (h : profileOrientation P r = profileOrientation Q s) : P = Q ∨ P = Q.rotate := by
  cases r <;> cases s
  · exact Or.inl h
  · exact Or.inr h
  · right; simpa [profileOrientation] using congrArg Gluing.Profile.rotate h
  · left; simpa [profileOrientation] using congrArg Gluing.Profile.rotate h

private theorem b_relation_unorient {P Q : Gluing.Profile 4} {r s : Bool}
    (h : BRelation (profileOrientation P r) (profileOrientation Q s)) : BRelation P Q := by
  cases r <;> cases s
  · exact h
  · exact b_relation_rotate_right h
  · exact b_relation_rotate_left h
  · exact b_relation_rotate_left (b_relation_rotate_right h)

private theorem contact_relation_unorient {second : Bool} {P Q : Gluing.Profile 4} {r s : Bool}
    (h : ContactRelation second (profileOrientation P r) (profileOrientation Q s)) :
    ContactRelation second P Q := by
  cases r <;> cases s
  · exact h
  · exact contact_relation_rotate_right h
  · exact contact_relation_rotate_left h
  · exact contact_relation_rotate_left (contact_relation_rotate_right h)

private theorem normalize_three_minimum_word (P : Gluing.Profile 4) (z q : ℕ)
    (hg : P.g = ![q,z,z,z] ∨ P.g = ![z,q,z,z] ∨
      P.g = ![z,z,q,z] ∨ P.g = ![z,z,z,q]) :
    ∃ rev : Bool, (profileOrientation P rev).g = ![z,z,z,q] ∨
      (profileOrientation P rev).g = ![z,q,z,z] := by
  rcases hg with hg | hg | hg | hg
  · refine ⟨true,Or.inl ?_⟩
    funext j; fin_cases j <;> simp [profileOrientation,Gluing.Profile.rotate,hg]
  · exact ⟨false,Or.inr hg⟩
  · refine ⟨true,Or.inr ?_⟩
    funext j; fin_cases j <;> simp [profileOrientation,Gluing.Profile.rotate,hg]
  · exact ⟨false,Or.inl hg⟩

/-- Three-minimum words on equal actual profiles use the same larger numerical
gap.  This follows from the gap multiset, not from a parameter assignment. -/
theorem common_three_minimum_words (P Q : Gluing.Profile 4) (z : ℕ+)
    (hmin : ∀ j, z.val ≤ P.g j) (hm : Staircase.minimumMultiplicity P z = 3)
    (he : P.toBetaDiagram.schur = Q.toBetaDiagram.schur) :
    ∃ q : ℕ+, z.val < q.val ∧
      (P.g = ![q.val,z.val,z.val,z.val] ∨ P.g = ![z.val,q.val,z.val,z.val] ∨
       P.g = ![z.val,z.val,q.val,z.val] ∨ P.g = ![z.val,z.val,z.val,q.val]) ∧
      (Q.g = ![q.val,z.val,z.val,z.val] ∨ Q.g = ![z.val,q.val,z.val,z.val] ∨
       Q.g = ![z.val,z.val,q.val,z.val] ∨ Q.g = ![z.val,z.val,z.val,q.val]) := by
  have he' : P.schur = Q.schur := by simpa only [Gluing.Profile.toBetaDiagram_schur] using he
  have hgm := Gluing.Profile.gaps_eq_of_schur_eq he'
  have hminQ := gap_minimum_preserved P Q z hmin he
  have hmQ : Staircase.minimumMultiplicity Q z = 3 := by
    rw [← minimumMultiplicity_eq_of_schur_eq P Q z he']
    exact hm
  obtain ⟨q,hq,hPword⟩ := three_minimum_gap_words P z hmin hm
  obtain ⟨r,hr,hQword⟩ := three_minimum_gap_words Q z hminQ hmQ
  have hqmem : q ∈ P.gapMultiset := by
    rcases hPword with h | h | h | h
    · exact Multiset.mem_map.mpr ⟨(0 : Fin 4),by simp,by simp [h]⟩
    · exact Multiset.mem_map.mpr ⟨(1 : Fin 4),by simp,by simp [h]⟩
    · exact Multiset.mem_map.mpr ⟨(2 : Fin 4),by simp,by simp [h]⟩
    · exact Multiset.mem_map.mpr ⟨(3 : Fin 4),by simp,by simp [h]⟩
  rw [hgm] at hqmem
  obtain ⟨k,_,hk⟩ := Multiset.mem_map.mp hqmem
  have hqr : q = r := by
    rcases hQword with h | h | h | h
    all_goals fin_cases k <;> simp [h] at hk <;> omega
  subst r
  exact ⟨⟨q,by have := z.pos; omega⟩,hq,hPword,hQword⟩

/-- The complete three-minimum branch: end/end is literal, end/interior is
A1, and interior/interior is literal or B, including every q-contact case. -/
theorem three_minimum_full_class (P Q : Gluing.Profile 4)
    (hP : Staircase.Thick P) (hQ : Staircase.Thick Q) (z : ℕ+)
    (hmin : ∀ j, z.val ≤ P.g j) (hm : Staircase.minimumMultiplicity P z = 3) :
    P.toBetaDiagram.schur = Q.toBetaDiagram.schur ↔
      P = Q ∨ P = Q.rotate ∨ ContactRelation false P Q ∨ BRelation P Q := by
  constructor
  · intro he
    obtain ⟨q,hzq,hPword,hQword⟩ := common_three_minimum_words P Q z hmin hm he
    obtain ⟨r,hPr⟩ := normalize_three_minimum_word P z.val q.val hPword
    obtain ⟨s,hQs⟩ := normalize_three_minimum_word Q z.val q.val hQword
    have hPrT := profileOrientation_thick P hP r
    have hQsT := profileOrientation_thick Q hQ s
    have he' : (profileOrientation P r).toBetaDiagram.schur =
        (profileOrientation Q s).toBetaDiagram.schur := by
      rw [profileOrientation_schur,profileOrientation_schur]
      exact he
    rcases hPr with hPr | hPr
    all_goals rcases hQs with hQs | hQs
    · have h := terminal_large_seam_rigidity _ _ hPrT hQsT z q hzq hPr hQs he'
      rcases equality_unorient h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · have h := a1_cross_pattern _ _ hPrT hQsT z q hzq hPr hQs he'
      exact Or.inr (Or.inr (Or.inl (contact_relation_unorient h)))
    · have h := a1_cross_pattern _ _ hQsT hPrT z q hzq hQs hPr he'.symm
      exact Or.inr (Or.inr (Or.inl (contact_relation_unorient (contact_relation_symm h))))
    · rcases interior_large_seam_classification _ _ hPrT hQsT z q hzq hPr hQs he' with h | h
      · rcases equality_unorient h with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr (b_relation_unorient h)))
  · rintro (rfl | h | h | h)
    · rfl
    · rw [h,Gluing.Profile.toBetaDiagram_schur,Gluing.Profile.toBetaDiagram_schur,Gluing.Profile.schur_rotate]
    · exact contact_relation_schur_eq h
    · exact b_relation_schur_eq h

/-- The last Q/Q row exchange has this full numerical-label defect. -/
theorem qq_row_exchange_defect (a b c d z q : ℤ) :
    interval complete a b c d b z q z q-interval complete a b d c b z q z q =
      complete z*complete q*
        (complete (a+b+c-q-z)*two complete q b d-
         complete (a+b+d-q-z)*two complete q b c+
         complete (a+b-z)*(complete c*complete (b+d-q)-complete d*complete (b+c-q))) := by
  unfold interval two
  ring_nf

/-- The Q/Q exchange is rigid on its entire thick domain, with no
distinctness restriction on labels below the private largest index. -/
theorem qq_row_exchange_iff (a b c d z q : ℤ) (hz : 1 ≤ z) (hq : z < q)
    (ha : z < a) (hb : q+z < b) (hc : q+z < c) (hd : q+z < d) :
    interval complete a b c d b z q z q = interval complete a b d c b z q z q ↔ c = d := by
  constructor
  · intro he
    by_contra hcd
    rcases lt_or_gt_of_ne hcd with hlt | hgt
    · let v : ℕ+ := ⟨(a+b+d-q-z).toNat,by omega⟩
      have hv : (v.val : ℤ) = a+b+d-q-z := by dsimp [v]; omega
      have hcoeff :
          MvPolynomial.pderiv v
            (interval complete a b c d b z q z q-interval complete a b d c b z q z q) =
          -(complete z*complete q*two complete q b c) := by
        rw [qq_row_exchange_defect]
        unfold two
        simp (disch := omega) [map_add,map_sub,map_neg,MvPolynomial.pderiv_mul,
          Staircase.residual_pderiv_complete,hv,if_pos,if_neg]
        <;> ring
      have hzero := congrArg (MvPolynomial.pderiv v) (sub_eq_zero.mpr he)
      rw [hcoeff,map_zero] at hzero
      exact (neg_ne_zero.mpr (mul_ne_zero
        (mul_ne_zero ((complete_ne_zero_iff z).mpr (by omega))
          ((complete_ne_zero_iff q).mpr (by omega)))
        (two_ne_zero q b c (by omega) (by omega) (by omega)))) hzero
    · let v : ℕ+ := ⟨(a+b+c-q-z).toNat,by omega⟩
      have hv : (v.val : ℤ) = a+b+c-q-z := by dsimp [v]; omega
      have hcoeff :
          MvPolynomial.pderiv v
            (interval complete a b c d b z q z q-interval complete a b d c b z q z q) =
          complete z*complete q*two complete q b d := by
        rw [qq_row_exchange_defect]
        unfold two
        simp (disch := omega) [map_add,map_sub,map_neg,MvPolynomial.pderiv_mul,
          Staircase.residual_pderiv_complete,hv,if_pos,if_neg]
        <;> ring
      have hzero := congrArg (MvPolynomial.pderiv v) (sub_eq_zero.mpr he)
      rw [hcoeff,map_zero] at hzero
      exact (mul_ne_zero
        (mul_ne_zero ((complete_ne_zero_iff z).mpr (by omega))
          ((complete_ne_zero_iff q).mpr (by omega)))
        (two_ne_zero q b d (by omega) (by omega) (by omega))) hzero
  · rintro rfl
    rfl

private theorem qs_q_cut_left {R : Type*} [CommRing R] (h : ℤ → R)
    (a b c d z q : ℤ) (hq : h q = 0) :
    interval h a b c d a z q z q = h a*(two h z a b*two h z c d) := by
  unfold interval two
  simp only [hq]
  ring

private theorem qs_q_cut_right {R : Type*} [CommRing R] (h : ℤ → R)
    (a b c d z q : ℤ) (hq : h q = 0) :
    interval h c b a d a q z z q = h c*threeInterval h b a d z z*h a := by
  unfold interval threeInterval
  simp only [hq]
  ring

/-- The final Q/S allocation is excluded by actual full factors of orders
2+2 against 1+3, not by specialized residual degree certificates. -/
theorem qs_late_allocation_ne (z q : ℕ+) (hzq : z.val < q.val) (a b d : ℤ)
    (ha : (q.val : ℤ) < a) (ha2 : 2*(z.val : ℤ) < a)
    (hb : (q.val : ℤ)+z.val < b) (hd : (q.val : ℤ)+z.val < d) :
    interval complete a b (a+b-z.val) d a z.val q.val z.val q.val ≠
      interval complete (a+b-z.val) b a d a q.val z.val z.val q.val := by
  have hz := z.pos
  let bar := fun k : ℤ => eraseGenerator q (complete k)
  have hq0 : bar q.val = 0 := by simp [bar,eraseGenerator_complete]
  intro he
  have h := congrArg (eraseGenerator q) he
  rw [erase_interval,erase_interval,
    qs_q_cut_left bar a b (a+b-z.val) d z.val q.val hq0,
    qs_q_cut_right bar a b (a+b-z.val) d z.val q.val hq0] at h
  dsimp only [bar] at h
  rw [erase_complete_of_lt q a ha,
    erase_complete_of_lt q (a+b-z.val) (by omega),
    two_q_untouched q z.val a b (by omega) (by omega) (by omega) (by omega),
    two_q_untouched q z.val (a+b-z.val) d (by omega) (by omega) (by omega) (by omega),
    three_q_untouched q b a d z.val z.val
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)] at h
  have hp : two complete z.val a b*two complete z.val (a+b-z.val) d =
      complete (a+b-z.val)*threeInterval complete b a d z.val z.val := by
    apply mul_left_cancel₀ ((complete_ne_zero_iff a).mpr (by omega))
    rw [h]
    ring
  let P1 := (twoScalarProfile a b z.val (by positivity) (by omega) (by omega)).toBetaDiagram
  let P2 := (twoScalarProfile (a+b-z.val) d z.val (by positivity) (by omega) (by omega)).toBetaDiagram
  let Q1 := (scalarSingleton (a+b-z.val) (by omega)).toBetaDiagram
  let Q2 := (threeConstantProfile b a d z.val (by positivity) (by omega) ha2 (by omega)).toBetaDiagram
  have hprod : P1.schur*P2.schur = Q1.schur*Q2.schur := by
    simpa only [P1,P2,Q1,Q2,twoScalarProfile_schur,scalarSingleton_schur,threeConstantProfile_schur] using hp
  have hread := connected_two_factor_reading P1 P2 Q1 Q2
    (Gluing.Profile.toBetaDiagram_connected _) (Gluing.Profile.toBetaDiagram_connected _)
    (one_connected Q1) (Gluing.Profile.toBetaDiagram_connected _) hprod
  rcases hread with ⟨h1,h2⟩ | ⟨h1,h2⟩
  all_goals
    have hn := P1.row_count_of_schur_eq _ h1
    norm_num at hn

/-- Two-row full equality also recovers the gap itself. -/
theorem two_variable_rigidity (a b r A B R : ℤ)
    (hr : 0 ≤ r) (ha : r < a) (hb : r < b)
    (hR : 0 ≤ R) (hA : R < A) (hB : R < B)
    (he : two complete r a b = two complete R A B) :
    r = R ∧ ((a = A ∧ b = B) ∨ (a = B ∧ b = A)) := by
  let P := twoScalarProfile a b r hr ha hb
  let Q := twoScalarProfile A B R hR hA hB
  have he' : P.toBetaDiagram.schur = Q.toBetaDiagram.schur := by
    rw [twoScalarProfile_schur,twoScalarProfile_schur]
    exact he
  rcases small_profile_rigidity P Q (by decide) he' with h | h
  all_goals
    have hg := congrArg (fun S : Gluing.Profile 1 => (S.g 0 : ℤ)) h
    have h0 := congrArg (fun S : Gluing.Profile 1 => (S.r 0 : ℤ)) h
    have h1 := congrArg (fun S : Gluing.Profile 1 => (S.r 1 : ℤ)) h
    simp [P,Q,twoScalarProfile,Gluing.Profile.rotate] at hg h0 h1
  · exact ⟨by omega,Or.inl ⟨by omega,by omega⟩⟩
  · exact ⟨by omega,Or.inr ⟨by omega,by omega⟩⟩

private def threeVariableProfile (a b c r s : ℤ)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (ha : r < a) (hb : r+s < b) (hc : s < c) :
    Gluing.Profile 2 where
  r i := (![a,b,c] i).toNat
  g j := (![r,s] j).toNat
  r_pos := by intro i; fin_cases i <;> simp <;> omega
  g_lt_castSucc := by intro j; fin_cases j <;> simp <;> omega
  g_lt_succ := by intro j; fin_cases j <;> simp <;> omega

private theorem threeVariableProfile_schur (a b c r s : ℤ)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (ha : r < a) (hb : r+s < b) (hc : s < c) :
    (threeVariableProfile a b c r s hr hs ha hb hc).toBetaDiagram.schur =
      threeInterval complete a b c r s := by
  have hra : ((a.toNat : ℕ) : ℤ) = a := by omega
  have hrb : ((b.toNat : ℕ) : ℤ) = b := by omega
  have hrc : ((c.toNat : ℕ) : ℤ) = c := by omega
  have hrr : ((r.toNat : ℕ) : ℤ) = r := by omega
  have hrs : ((s.toNat : ℕ) : ℤ) = s := by omega
  rw [schur_three_complete _ (by simp [threeVariableProfile]; omega)]
  simp [threeVariableProfile,hra,hrb,hrc,hrr,hrs]

/-- Full three-row equality recovers the entire row/gap word up to reversal,
with different and repeated gaps treated in the same actual theorem. -/
theorem three_variable_rigidity (a b c r s A B C R S : ℤ)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (ha : r < a) (hb : r+s < b) (hc : s < c)
    (hR : 0 ≤ R) (hS : 0 ≤ S) (hA : R < A) (hB : R+S < B) (hC : S < C)
    (he : threeInterval complete a b c r s = threeInterval complete A B C R S) :
    (r = R ∧ s = S ∧ a = A ∧ b = B ∧ c = C) ∨
      (r = S ∧ s = R ∧ a = C ∧ b = B ∧ c = A) := by
  let P := threeVariableProfile a b c r s hr hs ha hb hc
  let Q := threeVariableProfile A B C R S hR hS hA hB hC
  have he' : P.toBetaDiagram.schur = Q.toBetaDiagram.schur := by
    rw [threeVariableProfile_schur,threeVariableProfile_schur]
    exact he
  rcases small_profile_rigidity P Q (by decide) he' with h | h
  all_goals
    have hg0 := congrArg (fun T : Gluing.Profile 2 => (T.g 0 : ℤ)) h
    have hg1 := congrArg (fun T : Gluing.Profile 2 => (T.g 1 : ℤ)) h
    have h0 := congrArg (fun T : Gluing.Profile 2 => (T.r 0 : ℤ)) h
    have h1 := congrArg (fun T : Gluing.Profile 2 => (T.r 1 : ℤ)) h
    have h2 := congrArg (fun T : Gluing.Profile 2 => (T.r 2 : ℤ)) h
    simp [P,Q,threeVariableProfile,Gluing.Profile.rotate] at hg0 hg1 h0 h1 h2
  · exact Or.inl ⟨by omega,by omega,by omega,by omega,by omega⟩
  · exact Or.inr ⟨by omega,by omega,by omega,by omega,by omega⟩

/-- Marked P word with two possibly different upper gaps. -/
theorem P_variable_marked (a b c d e r s : ℤ) (z : ℕ+)
    (hr : (z.val : ℤ) < r) (hs : (z.val : ℤ) < s)
    (hDom : Domain a b c d e z.val z.val r s) :
    Staircase.minimumPolynomial z (interval complete a b c d e z.val z.val r s) =
      Polynomial.C (complete a*complete b*threeInterval complete c d e r s)+
      Polynomial.X*Polynomial.C
        (-(complete (a+b-z.val)*threeInterval complete c d e r s+
          complete a*threeInterval complete (b+c-z.val) d e r s))+
      Polynomial.X^2*Polynomial.C (threeInterval complete (a+b+c-2*z.val) d e r s) := by
  rcases hDom with ⟨hz0,_,hr0,hs0,ha,hb,hc,hd,he⟩
  have hz := z.pos
  simp (disch := omega) [interval,threeInterval,map_add,map_sub,map_mul,map_neg,
    Staircase.minimumPolynomial_complete,if_pos,if_neg]
  <;> ring_nf

theorem R_variable_marked (a b c d e r s : ℤ) (z : ℕ+)
    (hr : (z.val : ℤ) < r) (hs : (z.val : ℤ) < s)
    (hDom : Domain a b c d e z.val r s z.val) :
    Staircase.minimumPolynomial z (interval complete a b c d e z.val r s z.val) =
      Polynomial.C (complete a*threeInterval complete b c d r s*complete e)+
      Polynomial.X*Polynomial.C
        (-(threeInterval complete (a+b-z.val) c d r s*complete e+
          complete a*threeInterval complete b c (d+e-z.val) r s))+
      Polynomial.X^2*Polynomial.C (threeInterval complete (a+b-z.val) c (d+e-z.val) r s) := by
  rcases hDom with ⟨hz0,hr0,hs0,_,ha,hb,hc,hd,he⟩
  have hz := z.pos
  simp (disch := omega) [interval,threeInterval,map_add,map_sub,map_mul,map_neg,
    Staircase.minimumPolynomial_complete,if_pos,if_neg]
  <;> ring_nf

theorem Q_variable_marked (a b c d e r s : ℤ) (z : ℕ+)
    (hr : (z.val : ℤ) < r) (hs : (z.val : ℤ) < s)
    (hDom : Domain a b c d e z.val r z.val s) :
    Staircase.minimumPolynomial z (interval complete a b c d e z.val r z.val s) =
      Polynomial.C (complete a*two complete r b c*two complete s d e)+
      Polynomial.X*Polynomial.C
        (-(two complete r (a+b-z.val) c*two complete s d e+
          complete a*threeInterval complete b (c+d-z.val) e r s))+
      Polynomial.X^2*Polynomial.C (threeInterval complete (a+b-z.val) (c+d-z.val) e r s) := by
  rcases hDom with ⟨hz0,hr0,_,hs0,ha,hb,hc,hd,he⟩
  have hz := z.pos
  simp (disch := omega) [interval,threeInterval,two,map_add,map_sub,map_mul,map_neg,
    Staircase.minimumPolynomial_complete,if_pos,if_neg]
  <;> ring_nf

theorem S_variable_marked (a b c d e r s : ℤ) (z : ℕ+)
    (hr : (z.val : ℤ) < r) (hs : (z.val : ℤ) < s)
    (hDom : Domain a b c d e r z.val z.val s) :
    Staircase.minimumPolynomial z (interval complete a b c d e r z.val z.val s) =
      Polynomial.C (two complete r a b*complete c*two complete s d e)+
      Polynomial.X*Polynomial.C
        (-(two complete r a (b+c-z.val)*two complete s d e+
          two complete r a b*two complete s (c+d-z.val) e))+
      Polynomial.X^2*Polynomial.C (threeInterval complete a (b+c+d-2*z.val) e r s) := by
  rcases hDom with ⟨hr0,hz0,_,hs0,ha,hb,hc,hd,he⟩
  have hz := z.pos
  simp (disch := omega) [interval,threeInterval,two,map_add,map_sub,map_mul,map_neg,
    Staircase.minimumPolynomial_complete,if_pos,if_neg]
  <;> ring_nf

private theorem P_diagonal_polynomial (a b c d e A B C D E r s R S : ℤ)
    (z : ℕ+) (hr : (z.val : ℤ) < r) (hs : (z.val : ℤ) < s)
    (hR : (z.val : ℤ) < R) (hS : (z.val : ℤ) < S)
    (hF : Domain a b c d e z.val z.val r s)
    (hH : Domain A B C D E z.val z.val R S)
    (he : interval complete a b c d e z.val z.val r s =
      interval complete A B C D E z.val z.val R S) :
    r = R ∧ s = S ∧ a = A ∧ b = B ∧ c = C ∧ d = D ∧ e = E := by
  have hz := z.pos
  have ha := hF.2.2.2.2.1; have hb := hF.2.2.2.2.2.1
  have hc := hF.2.2.2.2.2.2.1; have hd := hF.2.2.2.2.2.2.2.1
  have he' := hF.2.2.2.2.2.2.2.2
  have hA := hH.2.2.2.2.1; have hB := hH.2.2.2.2.2.1
  have hC := hH.2.2.2.2.2.2.1; have hD := hH.2.2.2.2.2.2.2.1
  have hE := hH.2.2.2.2.2.2.2.2
  have hzero := congrArg (fun p : CompleteRing => (Staircase.minimumPolynomial z p).coeff 0) he
  have htop := congrArg (fun p : CompleteRing => (Staircase.minimumPolynomial z p).coeff 2) he
  rw [P_variable_marked a b c d e r s z hr hs hF,
    P_variable_marked A B C D E R S z hR hS hH] at hzero htop
  norm_num at hzero htop
  let L := [(scalarSingleton a (by omega)).toBetaDiagram,(scalarSingleton b (by omega)).toBetaDiagram]
  let M := [(scalarSingleton A (by omega)).toBetaDiagram,(scalarSingleton B (by omega)).toBetaDiagram]
  let P3 := (threeVariableProfile c d e r s (by omega) (by omega) (by omega) hd he').toBetaDiagram
  let Q3 := (threeVariableProfile C D E R S (by omega) (by omega) (by omega) hD hE).toBetaDiagram
  have hprod : (L.map (fun U => U.schur)).prod*P3.schur =
      (M.map (fun U => U.schur)).prod*Q3.schur := by
    simpa [L,M,P3,Q3,scalarSingleton_schur,threeVariableProfile_schur,mul_assoc] using hzero
  have hcorePoly := connected_nonlinear_factor_reading P3 Q3
    (Gluing.Profile.toBetaDiagram_connected _) (Gluing.Profile.toBetaDiagram_connected _) L M hprod
  have hcore' : threeInterval complete c d e r s = threeInterval complete C D E R S := by
    simpa only [P3,Q3,threeVariableProfile_schur] using hcorePoly
  have hne : threeInterval complete c d e r s ≠ 0 := by
    simpa only [P3,threeVariableProfile_schur] using P3.schur_ne_zero
  have hends : complete a*complete b = complete A*complete B := by
    rw [← hcore'] at hzero
    exact mul_right_cancel₀ hne hzero
  have hpairs := complete_two_product_reading (by omega) (by omega) (by omega) (by omega) hends
  have hcore := three_variable_rigidity c d e r s C D E R S
    (by omega) (by omega) (by omega) hd he'
    (by omega) (by omega) (by omega) hD hE hcore'
  have htopData := three_variable_rigidity (a+b+c-2*z.val) d e r s
    (A+B+C-2*z.val) D E R S
    (by omega) (by omega) (by omega) hd he'
    (by omega) (by omega) (by omega) hD hE htop
  have hrigid : r = R ∧ s = S ∧ c = C ∧ d = D ∧ e = E := by
    rcases hcore with ⟨h1,h2,h3,h4,h5⟩ | ⟨h1,h2,h3,h4,h5⟩
    · exact ⟨h1,h2,h3,h4,h5⟩
    · rcases htopData with ⟨ht1,ht2,ht3,ht4,ht5⟩ | ⟨ht1,ht2,ht3,ht4,ht5⟩
      · exact ⟨by omega,by omega,by omega,h4,by omega⟩
      · omega
  rcases hrigid with ⟨hrR,hsS,hcC,hdD,heE⟩
  subst R
  subst S
  subst C
  subst D
  subst E
  have hab : a = A ∧ b = B := by
    rcases hpairs with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · exact ⟨h1,h2⟩
    · have hAb : A = b := h2.symm
      have hBa : B = a := h1.symm
      subst A
      subst B
      have hsame := (adjacent_exchange_iff a b c d e z.val z.val r s hF hH).mp he
      exact ⟨hsame,hsame.symm⟩
  exact ⟨rfl,rfl,hab.1,hab.2,rfl,rfl,rfl⟩

/-- The diagonal P placement is literal even when the two upper gap labels
are exchanged or coincide on the mate. -/
theorem P_diagonal_rigidity (P Q : Gluing.Profile 4)
    (hP : Staircase.Thick P) (hQ : Staircase.Thick Q) (z r s R S : ℕ+)
    (hr : z.val < r.val) (hs : z.val < s.val)
    (hR : z.val < R.val) (hS : z.val < S.val)
    (hPg : P.g = ![z.val,z.val,r.val,s.val])
    (hQg : Q.g = ![z.val,z.val,R.val,S.val])
    (he : P.toBetaDiagram.schur = Q.toBetaDiagram.schur) : P = Q := by
  have hF : Domain (P.r 0) (P.r 1) (P.r 2) (P.r 3) (P.r 4)
      z.val z.val r.val s.val := by simpa [hPg] using domain_of_profile P hP
  have hH : Domain (Q.r 0) (Q.r 1) (Q.r 2) (Q.r 3) (Q.r 4)
      z.val z.val R.val S.val := by simpa [hQg] using domain_of_profile Q hQ
  have he' : interval complete (P.r 0) (P.r 1) (P.r 2) (P.r 3) (P.r 4)
      z.val z.val r.val s.val =
      interval complete (Q.r 0) (Q.r 1) (Q.r 2) (Q.r 3) (Q.r 4)
      z.val z.val R.val S.val := by
    rw [Gluing.Profile.toBetaDiagram_schur,Gluing.Profile.toBetaDiagram_schur,
      schur_interval P hP.hessenberg,schur_interval Q hQ.hessenberg] at he
    simpa [interval,complete_eq_hh,hPg,hQg] using he
  obtain ⟨hrR,hsS,h0,h1,h2,h3,h4⟩ := P_diagonal_polynomial
    (P.r 0) (P.r 1) (P.r 2) (P.r 3) (P.r 4)
    (Q.r 0) (Q.r 1) (Q.r 2) (Q.r 3) (Q.r 4)
    r.val s.val R.val S.val z
    (by exact_mod_cast hr) (by exact_mod_cast hs) (by exact_mod_cast hR) (by exact_mod_cast hS)
    hF hH he'
  have hrr : r = R := by exact_mod_cast hrR
  have hss : s = S := by exact_mod_cast hsS
  apply Gluing.Profile.ext
  · exact five_rows_eq_of_cast P Q h0 h1 h2 h3 h4
  · rw [hPg,hQg,hrr,hss]

private theorem singleton_variable_triple_reading
    (a b c d e A B C D E r s R S : ℤ)
    (ha : 0 < a) (hb : 0 < b) (hA : 0 < A) (hE : 0 < E)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hc : r < c) (hd : r+s < d) (he : s < e)
    (hR : 0 ≤ R) (hS : 0 ≤ S) (hB : R < B) (hC : R+S < C) (hD : S < D)
    (hzero : complete a*complete b*threeInterval complete c d e r s =
      complete A*threeInterval complete B C D R S*complete E) :
    ((r = R ∧ s = S ∧ c = B ∧ d = C ∧ e = D) ∨
      (r = S ∧ s = R ∧ c = D ∧ d = C ∧ e = B)) ∧
      ((a = A ∧ b = E) ∨ (a = E ∧ b = A)) := by
  let aP := (scalarSingleton a ha).toBetaDiagram
  let bP := (scalarSingleton b hb).toBetaDiagram
  let AP := (scalarSingleton A hA).toBetaDiagram
  let EP := (scalarSingleton E hE).toBetaDiagram
  let P3 := (threeVariableProfile c d e r s hr hs hc hd he).toBetaDiagram
  let Q3 := (threeVariableProfile B C D R S hR hS hB hC hD).toBetaDiagram
  have hp : aP.schur*bP.schur*P3.schur = AP.schur*Q3.schur*EP.schur := by
    simpa only [aP,bP,AP,EP,P3,Q3,scalarSingleton_schur,
      threeVariableProfile_schur] using hzero
  obtain ⟨hcore,hends⟩ := singleton_triple_factor_reading aP bP AP EP P3 Q3
    (Gluing.Profile.toBetaDiagram_connected _) (Gluing.Profile.toBetaDiagram_connected _) hp
  constructor
  · apply three_variable_rigidity c d e r s B C D R S hr hs hc hd he hR hS hB hC hD
    simpa only [P3,Q3,threeVariableProfile_schur] using hcore
  · rcases hends with ⟨h1,h2⟩ | ⟨h1,h2⟩
    all_goals
      simp only [aP,bP,AP,EP,scalarSingleton_schur] at h1 h2
      have h1' := complete_injective_nonnegative ha.le (by omega) h1
      have h2' := complete_injective_nonnegative hb.le (by omega) h2
    · exact Or.inl ⟨h1',h2'⟩
    · exact Or.inr ⟨h1',h2'⟩

/-- Two isolated minimum seams leave the middle triple and the two terminal
singletons.  Their marked top coefficient fixes their only remaining order. -/
theorem R_diagonal_polynomial (a b c d e A B C D E r s R S : ℤ)
    (z : ℕ+) (hr : (z.val : ℤ) < r) (hs : (z.val : ℤ) < s)
    (hR : (z.val : ℤ) < R) (hS : (z.val : ℤ) < S)
    (hF : Domain a b c d e z.val r s z.val)
    (hH : Domain A B C D E z.val R S z.val)
    (heq : interval complete a b c d e z.val r s z.val =
      interval complete A B C D E z.val R S z.val) :
    (r = R ∧ s = S ∧ a = A ∧ b = B ∧ c = C ∧ d = D ∧ e = E) ∨
      (r = S ∧ s = R ∧ a = E ∧ b = D ∧ c = C ∧ d = B ∧ e = A) := by
  have hz := z.pos
  rcases hF with ⟨hz0,hr0,hs0,_,ha,hb,hc,hd,he⟩
  rcases hH with ⟨_,hR0,hS0,_,hA,hB,hC,hD,hE⟩
  have hzero := congrArg (fun p : CompleteRing =>
    (Staircase.minimumPolynomial z p).coeff 0) heq
  have htop := congrArg (fun p : CompleteRing =>
    (Staircase.minimumPolynomial z p).coeff 2) heq
  rw [R_variable_marked a b c d e r s z hr hs
      ⟨hz0,hr0,hs0,hz0,ha,hb,hc,hd,he⟩,
    R_variable_marked A B C D E R S z hR hS
      ⟨hz0,hR0,hS0,hz0,hA,hB,hC,hD,hE⟩] at hzero htop
  norm_num at hzero htop
  have hzero' : complete a*complete e*threeInterval complete b c d r s =
      complete A*threeInterval complete B C D R S*complete E := by
    convert hzero using 1 <;> ring
  obtain ⟨hcore,hends⟩ := singleton_variable_triple_reading
    a e b c d A B C D E r s R S (by omega) (by omega) (by omega) (by omega)
    hr0 hs0 (by omega) hc (by omega) hR0 hS0 (by omega) hC (by omega) hzero'
  have htopData := three_variable_rigidity
    (a+b-z.val) c (d+e-z.val) r s (A+B-z.val) C (D+E-z.val) R S
    hr0 hs0 (by omega) hc (by omega)
    hR0 hS0 (by omega) hC (by omega) htop
  rcases hcore with ⟨h1,h2,h3,h4,h5⟩ | ⟨h1,h2,h3,h4,h5⟩
  all_goals
    rcases hends with ⟨h6,h7⟩ | ⟨h6,h7⟩
    all_goals
      rcases htopData with ⟨ht1,ht2,ht3,ht4,ht5⟩ | ⟨ht1,ht2,ht3,ht4,ht5⟩
      all_goals first
        | exact Or.inl ⟨by omega,by omega,by omega,by omega,by omega,by omega,by omega⟩
        | exact Or.inr ⟨by omega,by omega,by omega,by omega,by omega,by omega,by omega⟩

/-- The P/R crossing can only occur when the two nonminimum gaps coincide.
This compares the full connected three-row factors, not a residual degree. -/
theorem PR_distinct_gaps_ne (a b c d e A B C D E r s R S : ℤ)
    (z : ℕ+) (hr : (z.val : ℤ) < r) (hs : (z.val : ℤ) < s)
    (hR : (z.val : ℤ) < R) (hS : (z.val : ℤ) < S) (hrs : r ≠ s)
    (hF : Domain a b c d e z.val z.val r s)
    (hH : Domain A B C D E z.val R S z.val) :
    interval complete a b c d e z.val z.val r s ≠
      interval complete A B C D E z.val R S z.val := by
  have hz := z.pos
  have ha := hF.2.2.2.2.1; have hb := hF.2.2.2.2.2.1
  have hc := hF.2.2.2.2.2.2.1; have hd := hF.2.2.2.2.2.2.2.1
  have he := hF.2.2.2.2.2.2.2.2
  have hA := hH.2.2.2.2.1; have hB := hH.2.2.2.2.2.1
  have hC := hH.2.2.2.2.2.2.1; have hD := hH.2.2.2.2.2.2.2.1
  have hE := hH.2.2.2.2.2.2.2.2
  intro heq
  have hzero := congrArg (fun p : CompleteRing =>
    (Staircase.minimumPolynomial z p).coeff 0) heq
  have htop := congrArg (fun p : CompleteRing =>
    (Staircase.minimumPolynomial z p).coeff 2) heq
  rw [P_variable_marked a b c d e r s z hr hs hF,
    R_variable_marked A B C D E R S z hR hS hH] at hzero htop
  norm_num at hzero htop
  obtain ⟨hcore,_⟩ := singleton_variable_triple_reading
    a b c d e A B C D E r s R S (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) hd he
    (by omega) (by omega) (by omega) hC (by omega) hzero
  have htopData := three_variable_rigidity
    (a+b+c-2*z.val) d e r s (A+B-z.val) C (D+E-z.val) R S
    (by omega) (by omega) (by omega) hd he
    (by omega) (by omega) (by omega) hC (by omega) htop
  rcases hcore with ⟨h1,h2,h3,h4,h5⟩ | ⟨h1,h2,h3,h4,h5⟩
  all_goals
    rcases htopData with ⟨ht1,ht2,ht3,ht4,ht5⟩ | ⟨ht1,ht2,ht3,ht4,ht5⟩
    all_goals omega

/-- A singleton cannot be exchanged with either connected two-row factor.
Normalization is by the actual full Schur initial monomial. -/
theorem singleton_two_pair_factor_reading (A D : BetaDiagram 1)
    (B C E F : BetaDiagram 2)
    (hB : B.Connected) (hC : C.Connected) (hE : E.Connected) (hF : F.Connected)
    (he : A.schur*B.schur*C.schur = D.schur*E.schur*F.schur) :
    A.schur = D.schur ∧
      ((B.schur = E.schur ∧ C.schur = F.schur) ∨
       (B.schur = F.schur ∧ C.schur = E.schur)) := by
  have hAi := A.schur_irreducible (one_connected A)
  have hAp := UniqueFactorizationMonoid.irreducible_iff_prime.mp hAi
  have hdiv : A.schur ∣ D.schur*E.schur*F.schur := by
    rw [← he]
    exact ⟨B.schur*C.schur,by ring⟩
  have hAD : A.schur = D.schur := by
    rcases hAp.dvd_or_dvd hdiv with hDE | hAF
    · rcases hAp.dvd_or_dvd hDE with hAD | hAE
      · exact full_schur_associated_eq A D
          (hAi.associated_of_dvd (D.schur_irreducible (one_connected D)) hAD)
      · have hp := full_schur_associated_eq A E
          (hAi.associated_of_dvd (E.schur_irreducible hE) hAE)
        have hn := A.row_count_of_schur_eq E hp
        norm_num at hn
    · have hp := full_schur_associated_eq A F
        (hAi.associated_of_dvd (F.schur_irreducible hF) hAF)
      have hn := A.row_count_of_schur_eq F hp
      norm_num at hn
  refine ⟨hAD,connected_two_factor_reading B C E F hB hC hE hF ?_⟩
  apply mul_left_cancel₀ A.schur_ne_zero
  rw [hAD] at he ⊢
  simpa only [mul_assoc] using he

private theorem singleton_two_pair_reading
    (a b c d e A B C D E r s R S : ℤ)
    (ha : 0 < a) (hA : 0 < A)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hb : r < b) (hc : r < c) (hd : s < d) (he : s < e)
    (hR : 0 ≤ R) (hS : 0 ≤ S) (hB : R < B) (hC : R < C) (hD : S < D) (hE : S < E)
    (hzero : complete a*two complete r b c*two complete s d e =
      complete A*two complete R B C*two complete S D E) :
    a = A ∧
      ((r = R ∧ s = S ∧ ((b = B ∧ c = C) ∨ (b = C ∧ c = B)) ∧
        ((d = D ∧ e = E) ∨ (d = E ∧ e = D))) ∨
       (r = S ∧ s = R ∧ ((b = D ∧ c = E) ∨ (b = E ∧ c = D)) ∧
        ((d = B ∧ e = C) ∨ (d = C ∧ e = B)))) := by
  let aP := (scalarSingleton a ha).toBetaDiagram
  let AP := (scalarSingleton A hA).toBetaDiagram
  let bcP := (twoScalarProfile b c r hr hb hc).toBetaDiagram
  let deP := (twoScalarProfile d e s hs hd he).toBetaDiagram
  let BCP := (twoScalarProfile B C R hR hB hC).toBetaDiagram
  let DEP := (twoScalarProfile D E S hS hD hE).toBetaDiagram
  have hp : aP.schur*bcP.schur*deP.schur = AP.schur*BCP.schur*DEP.schur := by
    simpa only [aP,AP,bcP,deP,BCP,DEP,scalarSingleton_schur,
      twoScalarProfile_schur] using hzero
  obtain ⟨hsingle,hpair⟩ := singleton_two_pair_factor_reading aP AP bcP deP BCP DEP
    (Gluing.Profile.toBetaDiagram_connected _) (Gluing.Profile.toBetaDiagram_connected _)
    (Gluing.Profile.toBetaDiagram_connected _) (Gluing.Profile.toBetaDiagram_connected _) hp
  have haA : a = A := by
    apply complete_injective_nonnegative ha.le hA.le
    simpa only [aP,AP,scalarSingleton_schur] using hsingle
  refine ⟨haA,?_⟩
  rcases hpair with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · have hp := two_variable_rigidity b c r B C R hr hb hc hR hB hC
      (by simpa only [bcP,BCP,twoScalarProfile_schur] using h1)
    have hq := two_variable_rigidity d e s D E S hs hd he hS hD hE
      (by simpa only [deP,DEP,twoScalarProfile_schur] using h2)
    exact Or.inl ⟨hp.1,hq.1,hp.2,hq.2⟩
  · have hp := two_variable_rigidity b c r D E S hr hb hc hS hD hE
      (by simpa only [bcP,DEP,twoScalarProfile_schur] using h1)
    have hq := two_variable_rigidity d e s B C R hs hd he hR hB hC
      (by simpa only [deP,BCP,twoScalarProfile_schur] using h2)
    exact Or.inr ⟨hp.1,hq.1,hp.2,hq.2⟩

/-- The two safe-cut size patterns 1+1+3 and 1+2+2 are disjoint.
This is full Schur irreducibility and row count, without residual assumptions. -/
theorem singleton_triple_ne_singleton_two_pair
    (A B D : BetaDiagram 1) (C : BetaDiagram 3) (E F : BetaDiagram 2)
    (hC : C.Connected) (hE : E.Connected) (hF : F.Connected) :
    A.schur*B.schur*C.schur ≠ D.schur*E.schur*F.schur := by
  intro he
  have hCi := C.schur_irreducible hC
  have hCp := UniqueFactorizationMonoid.irreducible_iff_prime.mp hCi
  have hdiv : C.schur ∣ D.schur*E.schur*F.schur := by
    rw [← he]
    exact ⟨A.schur*B.schur,by ring⟩
  rcases hCp.dvd_or_dvd hdiv with hDE | hCF
  · rcases hCp.dvd_or_dvd hDE with hCD | hCE
    · have hp := full_schur_associated_eq C D
        (hCi.associated_of_dvd (D.schur_irreducible (one_connected D)) hCD)
      have hn := C.row_count_of_schur_eq D hp
      norm_num at hn
    · have hp := full_schur_associated_eq C E
        (hCi.associated_of_dvd (E.schur_irreducible hE) hCE)
      have hn := C.row_count_of_schur_eq E hp
      norm_num at hn
  · have hp := full_schur_associated_eq C F
      (hCi.associated_of_dvd (F.schur_irreducible hF) hCF)
    have hn := C.row_count_of_schur_eq F hp
    norm_num at hn

private noncomputable def qsFirst (a b c d e A B D r s z : ℤ) : CompleteRing :=
  two complete r A (B+a-z)*two complete s D e+
  two complete r A B*two complete s (a+D-z) e-
  two complete r (a+b-z) c*two complete s d e-
  complete a*threeInterval complete b (c+d-z) e r s

private theorem qsFirst_eq_zero (a b c d e A B D r s : ℤ) (z : ℕ+)
    (hr : (z.val : ℤ) < r) (hs : (z.val : ℤ) < s)
    (hF : Domain a b c d e z.val r z.val s)
    (hH : Domain A B a D e r z.val z.val s)
    (he : interval complete a b c d e z.val r z.val s =
      interval complete A B a D e r z.val z.val s) :
    qsFirst a b c d e A B D r s z.val = 0 := by
  have h := congrArg (fun p : CompleteRing =>
    (Staircase.minimumPolynomial z p).coeff 1) he
  rw [Q_variable_marked a b c d e r s z hr hs hF,
    S_variable_marked A B a D e r s z hr hs hH] at h
  norm_num at h
  unfold qsFirst
  linear_combination h

private theorem qs_direct_allocation_ne (a b d e r s : ℤ) (z : ℕ+)
    (hr : (z.val : ℤ) < r) (hs : (z.val : ℤ) < s)
    (ha : (z.val : ℤ) < a) (hb : (z.val : ℤ)+r < b)
    (hd : (z.val : ℤ)+s < d) (he : s < e) :
    qsFirst a b (a+b-z.val) d e (a+b-z.val) b d r s z.val ≠ 0 := by
  have hz := z.pos
  let v : ℕ+ := ⟨(a+2*b+d+e-2*z.val-r-s).toNat,by omega⟩
  have hv : (v.val : ℤ) = a+2*b+d+e-2*z.val-r-s := by dsimp [v]; omega
  have hderiv : MvPolynomial.pderiv v
      (qsFirst a b (a+b-z.val) d e (a+b-z.val) b d r s z.val) =
      -(complete a*complete r*complete s) := by
    unfold qsFirst two threeInterval
    simp (disch := omega) [map_add,map_sub,map_neg,MvPolynomial.pderiv_mul,
      Staircase.residual_pderiv_complete,hv,if_pos,if_neg]
    <;> ring
  intro h
  have hzero := congrArg (MvPolynomial.pderiv v) h
  rw [hderiv,map_zero] at hzero
  exact (neg_ne_zero.mpr (mul_ne_zero
    (mul_ne_zero ((complete_ne_zero_iff a).mpr (by omega))
      ((complete_ne_zero_iff r).mpr (by omega)))
    ((complete_ne_zero_iff s).mpr (by omega)))) hzero

private theorem qs_cross_allocation_ne (second : Bool) (a b c q : ℤ) (z : ℕ+)
    (hq : (z.val : ℤ) < q) (ha : (z.val : ℤ) < a)
    (hb : (z.val : ℤ)+q < b) (hc : (z.val : ℤ)+q < c) :
    (if second then
      qsFirst a b c (a+b-z.val) c (a+b-z.val) c b q q z.val
    else qsFirst a b c (a+b-z.val) b (a+b-z.val) b c q q z.val) ≠ 0 := by
  have hz := z.pos
  let α : ℤ := if second then a+2*b+2*c-2*z.val-2*q
    else a+3*b+c-2*z.val-2*q
  let β : ℤ := if second then 2*a+b+c-2*z.val-q
    else 2*a+2*b-2*z.val-q
  let F : CompleteRing := if second then
      qsFirst a b c (a+b-z.val) c (a+b-z.val) c b q q z.val
    else qsFirst a b c (a+b-z.val) b (a+b-z.val) b c q q z.val
  change F ≠ 0
  intro hzero
  rcases lt_trichotomy α β with hlt | heq | hgt
  · let v : ℕ+ := ⟨β.toNat,by cases second <;> simp [β] <;> omega⟩
    have hv : (v.val : ℤ) = β := by
      dsimp [v]
      cases second <;> simp [β] <;> omega
    have hderiv : MvPolynomial.pderiv v F =
        -(complete q*two complete q b c) := by
      cases second
      all_goals
        dsimp [α,β] at hlt hv
        dsimp [F]
        unfold qsFirst two threeInterval
        simp (disch := omega) [map_add,map_sub,map_neg,MvPolynomial.pderiv_mul,
          Staircase.residual_pderiv_complete,hv,if_pos,if_neg]
        <;> ring
    have h := congrArg (MvPolynomial.pderiv v) hzero
    rw [hderiv,map_zero] at h
    exact (neg_ne_zero.mpr (mul_ne_zero ((complete_ne_zero_iff q).mpr (by omega))
      (two_ne_zero q b c (by omega) (by omega) (by omega)))) h
  · have haeq : a = b+c-q := by cases second <;> simp [α,β] at heq <;> omega
    let v : ℕ+ := ⟨α.toNat,by cases second <;> simp [α] <;> omega⟩
    have hv : (v.val : ℤ) = α := by
      dsimp [v]
      cases second <;> simp [α] <;> omega
    have hderiv : MvPolynomial.pderiv v F =
        -(complete q*complete b*complete c) := by
      subst a
      cases second
      all_goals
        dsimp [α] at hv
        dsimp [F]
        unfold qsFirst two threeInterval
        simp (disch := omega) [map_add,map_sub,map_neg,MvPolynomial.pderiv_mul,
          Staircase.residual_pderiv_complete,hv,if_pos,if_neg]
        <;> ring
    have h := congrArg (MvPolynomial.pderiv v) hzero
    rw [hderiv,map_zero] at h
    exact (neg_ne_zero.mpr (mul_ne_zero
      (mul_ne_zero ((complete_ne_zero_iff q).mpr (by omega))
        ((complete_ne_zero_iff b).mpr (by omega)))
      ((complete_ne_zero_iff c).mpr (by omega)))) h
  · let v : ℕ+ := ⟨α.toNat,by cases second <;> simp [α] <;> omega⟩
    have hv : (v.val : ℤ) = α := by
      dsimp [v]
      cases second <;> simp [α] <;> omega
    have hderiv : MvPolynomial.pderiv v F =
        -(complete a*complete q*complete q) := by
      cases second
      all_goals
        dsimp [α,β] at hgt hv
        dsimp [F]
        unfold qsFirst two threeInterval
        simp (disch := omega) [map_add,map_sub,map_neg,MvPolynomial.pderiv_mul,
          Staircase.residual_pderiv_complete,hv,if_pos,if_neg]
        <;> ring
    have h := congrArg (MvPolynomial.pderiv v) hzero
    rw [hderiv,map_zero] at h
    exact (neg_ne_zero.mpr (mul_ne_zero
      (mul_ne_zero ((complete_ne_zero_iff a).mpr (by omega))
        ((complete_ne_zero_iff q).mpr (by omega)))
      ((complete_ne_zero_iff q).mpr (by omega)))) h

private theorem qs_last_allocation_ne (a b d q : ℤ) (z : ℕ+)
    (hq : (z.val : ℤ) < q) (ha : (z.val : ℤ) < a)
    (hb : (z.val : ℤ)+q < b) (hd : (z.val : ℤ)+q < d) :
    qsFirst a b (a+b-z.val) d (a+b-z.val) (a+b-z.val) d b q q z.val ≠ 0 := by
  have hz := z.pos
  let v : ℕ+ := ⟨(2*a+3*b+d-3*z.val-2*q).toNat,by omega⟩
  have hv : (v.val : ℤ) = 2*a+3*b+d-3*z.val-2*q := by dsimp [v]; omega
  have hderiv : MvPolynomial.pderiv v
      (qsFirst a b (a+b-z.val) d (a+b-z.val) (a+b-z.val) d b q q z.val) =
      -(complete a*complete q*complete q) := by
    unfold qsFirst two threeInterval
    simp (disch := omega) [map_add,map_sub,map_neg,MvPolynomial.pderiv_mul,
      Staircase.residual_pderiv_complete,hv,if_pos,if_neg]
    <;> ring
  intro h
  have hzero := congrArg (MvPolynomial.pderiv v) h
  rw [hderiv,map_zero] at hzero
  exact (neg_ne_zero.mpr (mul_ne_zero
    (mul_ne_zero ((complete_ne_zero_iff a).mpr (by omega))
      ((complete_ne_zero_iff q).mpr (by omega)))
    ((complete_ne_zero_iff q).mpr (by omega)))) hzero

/-- Both exterior quadratic factors may reverse at once, but the first
minimum coefficient detects that reversal unless the rows already agree. -/
private theorem qq_double_flip_rigid (a b c q : ℤ) (z : ℕ+)
    (hq : (z.val : ℤ) < q) (ha : (z.val : ℤ) < a)
    (hb : (z.val : ℤ)+q < b) (hc : (z.val : ℤ)+q < c)
    (he : interval complete a b c (a+b-z.val) (a+c-z.val) z.val q z.val q =
      interval complete a c b (a+c-z.val) (a+b-z.val) z.val q z.val q) : b = c := by
  have hz := z.pos
  have hF : Domain a b c (a+b-z.val) (a+c-z.val) z.val q z.val q :=
    ⟨by omega,by omega,by omega,by omega,ha,hb,by omega,by omega,by omega⟩
  have hH : Domain a c b (a+c-z.val) (a+b-z.val) z.val q z.val q :=
    ⟨by omega,by omega,by omega,by omega,ha,hc,by omega,by omega,by omega⟩
  have hfirst := congrArg (fun p : CompleteRing =>
    (Staircase.minimumPolynomial z p).coeff 1) he
  rw [Q_variable_marked a b c (a+b-z.val) (a+c-z.val) q q z hq hq hF,
    Q_variable_marked a c b (a+c-z.val) (a+b-z.val) q q z hq hq hH] at hfirst
  norm_num at hfirst
  have hW1 : c+(a+b-z.val)-z.val = a+b+c-2*z.val := by ring
  have hW2 : b+(a+c-z.val)-z.val = a+b+c-2*z.val := by ring
  simp (failIfUnchanged := false) only [hW1,hW2] at hfirst
  let F : CompleteRing :=
    two complete q (a+b-z.val) c*two complete q (a+b-z.val) (a+c-z.val)+
      complete a*threeInterval complete b (a+b+c-2*z.val) (a+c-z.val) q q-
    (two complete q (a+c-z.val) b*two complete q (a+c-z.val) (a+b-z.val)+
      complete a*threeInterval complete c (a+b+c-2*z.val) (a+b-z.val) q q)
  have hzero : F = 0 := by
    dsimp [F]
    linear_combination -hfirst
  by_contra hbc
  rcases lt_or_gt_of_ne hbc with hlt | hgt
  · let v : ℕ+ := ⟨(2*a+b+2*c-3*z.val-q).toNat,by omega⟩
    have hv : (v.val : ℤ) = 2*a+b+2*c-3*z.val-q := by dsimp [v]; omega
    have hderiv : MvPolynomial.pderiv v F = -(complete a*complete b*complete q) := by
      dsimp [F]
      unfold two threeInterval
      simp (disch := omega) [map_add,map_sub,map_neg,MvPolynomial.pderiv_mul,
        Staircase.residual_pderiv_complete,hv,if_pos,if_neg]
      <;> ring
    have h := congrArg (MvPolynomial.pderiv v) hzero
    rw [hderiv,map_zero] at h
    exact (neg_ne_zero.mpr (mul_ne_zero
      (mul_ne_zero ((complete_ne_zero_iff a).mpr (by omega))
        ((complete_ne_zero_iff b).mpr (by omega)))
      ((complete_ne_zero_iff q).mpr (by omega)))) h
  · let v : ℕ+ := ⟨(2*a+2*b+c-3*z.val-q).toNat,by omega⟩
    have hv : (v.val : ℤ) = 2*a+2*b+c-3*z.val-q := by dsimp [v]; omega
    have hderiv : MvPolynomial.pderiv v F = complete a*complete c*complete q := by
      dsimp [F]
      unfold two threeInterval
      simp (disch := omega) [map_add,map_sub,map_neg,MvPolynomial.pderiv_mul,
        Staircase.residual_pderiv_complete,hv,if_pos,if_neg]
      <;> ring
    have h := congrArg (MvPolynomial.pderiv v) hzero
    rw [hderiv,map_zero] at h
    exact (mul_ne_zero
      (mul_ne_zero ((complete_ne_zero_iff a).mpr (by omega))
        ((complete_ne_zero_iff c).mpr (by omega)))
      ((complete_ne_zero_iff q).mpr (by omega))) h

/-- Exchanging the two quadratic blocks after reversing the contracted
triple is detected at the largest first-coefficient label.  At a tie, two
positive complete products are read exactly; the tie is not discarded. -/
private theorem qq_reverse_blocks_rigid (a b d r s : ℤ) (z : ℕ+)
    (hr : (z.val : ℤ) < r) (hs : (z.val : ℤ) < s)
    (ha : (z.val : ℤ) < a)
    (hb : (z.val : ℤ)+r < b) (hd : (z.val : ℤ)+s < d)
    (he : interval complete a b (a+b-z.val) d (a+d-z.val) z.val r z.val s =
      interval complete a d (a+d-z.val) b (a+b-z.val) z.val s z.val r) :
    b = d ∧ r = s := by
  have hz := z.pos
  have hF : Domain a b (a+b-z.val) d (a+d-z.val) z.val r z.val s :=
    ⟨by omega,by omega,by omega,by omega,ha,hb,by omega,hd,by omega⟩
  have hH : Domain a d (a+d-z.val) b (a+b-z.val) z.val s z.val r :=
    ⟨by omega,by omega,by omega,by omega,ha,hd,by omega,hb,by omega⟩
  have hfirst := congrArg (fun p : CompleteRing =>
    (Staircase.minimumPolynomial z p).coeff 1) he
  rw [Q_variable_marked a b (a+b-z.val) d (a+d-z.val) r s z hr hs hF,
    Q_variable_marked a d (a+d-z.val) b (a+b-z.val) s r z hs hr hH] at hfirst
  norm_num at hfirst
  have hW1 : (a+b-z.val)+d-z.val = a+b+d-2*z.val := by ring
  have hW2 : (a+d-z.val)+b-z.val = a+b+d-2*z.val := by ring
  simp (failIfUnchanged := false) only [hW1,hW2] at hfirst
  let F : CompleteRing :=
    two complete r (a+b-z.val) (a+b-z.val)*two complete s d (a+d-z.val)+
      complete a*threeInterval complete b (a+b+d-2*z.val) (a+d-z.val) r s-
    (two complete s (a+d-z.val) (a+d-z.val)*two complete r b (a+b-z.val)+
      complete a*threeInterval complete d (a+b+d-2*z.val) (a+b-z.val) s r)
  have hzero : F = 0 := by
    dsimp [F]
    linear_combination -hfirst
  let α : ℤ := 2*a+2*b+d-3*z.val-r
  let β : ℤ := 2*a+b+2*d-3*z.val-s
  have hα : 0 < α := by dsimp [α]; omega
  have hβ : 0 < β := by dsimp [β]; omega
  have htie : α = β := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · let v : ℕ+ := ⟨β.toNat,by omega⟩
      have hv : (v.val : ℤ) = β := by dsimp [v]; omega
      have hderiv : MvPolynomial.pderiv v F = -(complete a*complete s*complete b) := by
        dsimp [α,β] at hlt hv
        dsimp [F]
        unfold two threeInterval
        simp (disch := omega) [map_add,map_sub,map_neg,MvPolynomial.pderiv_mul,
          Staircase.residual_pderiv_complete,hv,if_pos,if_neg]
        <;> ring
      have h := congrArg (MvPolynomial.pderiv v) hzero
      rw [hderiv,map_zero] at h
      exact (neg_ne_zero.mpr (mul_ne_zero
        (mul_ne_zero ((complete_ne_zero_iff a).mpr (by omega))
          ((complete_ne_zero_iff s).mpr (by omega)))
        ((complete_ne_zero_iff b).mpr (by omega)))) h
    · let v : ℕ+ := ⟨α.toNat,by omega⟩
      have hv : (v.val : ℤ) = α := by dsimp [v]; omega
      have hderiv : MvPolynomial.pderiv v F = complete a*complete r*complete d := by
        dsimp [α,β] at hgt hv
        dsimp [F]
        unfold two threeInterval
        simp (disch := omega) [map_add,map_sub,map_neg,MvPolynomial.pderiv_mul,
          Staircase.residual_pderiv_complete,hv,if_pos,if_neg]
        <;> ring
      have h := congrArg (MvPolynomial.pderiv v) hzero
      rw [hderiv,map_zero] at h
      exact (mul_ne_zero
        (mul_ne_zero ((complete_ne_zero_iff a).mpr (by omega))
          ((complete_ne_zero_iff r).mpr (by omega)))
        ((complete_ne_zero_iff d).mpr (by omega))) h
  let v : ℕ+ := ⟨α.toNat,by omega⟩
  have hv : (v.val : ℤ) = α := by dsimp [v]; omega
  have hderiv : MvPolynomial.pderiv v F =
      complete a*(complete r*complete d-complete s*complete b) := by
    dsimp [α,β] at htie hv
    dsimp [F]
    unfold two threeInterval
    simp (disch := omega) [map_add,map_sub,map_neg,MvPolynomial.pderiv_mul,
      Staircase.residual_pderiv_complete,hv,if_pos,if_neg]
    <;> ring
  have h := congrArg (MvPolynomial.pderiv v) hzero
  rw [hderiv,map_zero] at h
  have hp : complete r*complete d = complete s*complete b := by
    apply sub_eq_zero.mp
    exact (mul_eq_zero.mp h).resolve_left ((complete_ne_zero_iff a).mpr (by omega))
  rcases complete_two_product_reading (by omega) (by omega) (by omega) (by omega) hp with
    ⟨h1,h2⟩ | ⟨h1,h2⟩
  · exact ⟨h2.symm,h1⟩
  · omega

/-- The diagonal Q placement is rigid.  The factor exchange and the
reversal of the contracted triple are retained through the first jet. -/
theorem Q_diagonal_polynomial (a b c d e A B C D E r s R S : ℤ)
    (z : ℕ+) (hr : (z.val : ℤ) < r) (hs : (z.val : ℤ) < s)
    (hR : (z.val : ℤ) < R) (hS : (z.val : ℤ) < S)
    (hF : Domain a b c d e z.val r z.val s)
    (hH : Domain A B C D E z.val R z.val S)
    (heq : interval complete a b c d e z.val r z.val s =
      interval complete A B C D E z.val R z.val S) :
    r = R ∧ s = S ∧ a = A ∧ b = B ∧ c = C ∧ d = D ∧ e = E := by
  have hz := z.pos
  have ha := hF.2.2.2.2.1; have hb := hF.2.2.2.2.2.1
  have hc := hF.2.2.2.2.2.2.1; have hd := hF.2.2.2.2.2.2.2.1
  have he := hF.2.2.2.2.2.2.2.2
  have hA := hH.2.2.2.2.1; have hB := hH.2.2.2.2.2.1
  have hC := hH.2.2.2.2.2.2.1; have hD := hH.2.2.2.2.2.2.2.1
  have hE := hH.2.2.2.2.2.2.2.2
  have hzero := congrArg (fun p : CompleteRing =>
    (Staircase.minimumPolynomial z p).coeff 0) heq
  have htop := congrArg (fun p : CompleteRing =>
    (Staircase.minimumPolynomial z p).coeff 2) heq
  rw [Q_variable_marked a b c d e r s z hr hs hF,
    Q_variable_marked A B C D E R S z hR hS hH] at hzero htop
  norm_num at hzero htop
  obtain ⟨haA,hpairs⟩ := singleton_two_pair_reading
    a b c d e A B C D E r s R S (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) he
    (by omega) (by omega) (by omega) (by omega) (by omega) hE hzero
  subst A
  have htopData := three_variable_rigidity
    (a+b-z.val) (c+d-z.val) e r s (a+B-z.val) (C+D-z.val) E R S
    (by omega) (by omega) (by omega) (by omega) he
    (by omega) (by omega) (by omega) (by omega) hE htop
  have hcases :
      (r = R ∧ s = S ∧ b = B ∧ c = C ∧ d = D ∧ e = E) ∨
      (r = s ∧ R = r ∧ S = r ∧ e = b ∧ B = b ∧ C = d ∧ D = c ∧ E = b) ∨
      (r = s ∧ R = r ∧ S = r ∧ d = a+b-z.val ∧ e = a+c-z.val ∧
        B = c ∧ C = b ∧ D = e ∧ E = d) ∨
      (R = s ∧ S = r ∧ c = a+b-z.val ∧ e = a+d-z.val ∧
        B = d ∧ C = e ∧ D = b ∧ E = c) := by
    clear hzero htop heq hF hH
    rcases hpairs with ⟨h1,h2,hbc,hde⟩ | ⟨h1,h2,hbc,hde⟩
    all_goals
      rcases hbc with ⟨h3,h4⟩ | ⟨h3,h4⟩
      all_goals
        rcases hde with ⟨h5,h6⟩ | ⟨h5,h6⟩
        all_goals
          rcases htopData with ⟨ht1,ht2,ht3,ht4,ht5⟩ | ⟨ht1,ht2,ht3,ht4,ht5⟩
          all_goals first
            | (left; omega)
            | (right; left; omega)
            | (right; right; left; omega)
            | (right; right; right; omega)
  rcases hcases with h | h | h | h
  · exact ⟨h.1,h.2.1,rfl,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2⟩
  · rcases h with ⟨hrs,hRr,hSr,heb,hBb,hCd,hDc,hEb⟩
    subst s
    subst R
    subst S
    subst e
    subst B
    subst C
    subst D
    subst E
    have hcd := (qq_row_exchange_iff a b c d z.val r
      (by omega) hr ha (by omega) (by omega) (by omega)).mp heq
    exact ⟨rfl,rfl,rfl,rfl,hcd,hcd.symm,rfl⟩
  · rcases h with ⟨hrs,hRr,hSr,hdk,hel,hBc,hCb,hDe,hEd⟩
    subst s
    subst R
    subst S
    subst B
    subst C
    subst D
    subst E
    subst d
    subst e
    have hbc := qq_double_flip_rigid a b c r z hr ha (by omega) (by omega) heq
    subst c
    exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  · rcases h with ⟨hRs,hSr,hck,hel,hBd,hCe,hDb,hEc⟩
    subst R
    subst S
    subst B
    subst C
    subst D
    subst E
    subst c
    subst e
    obtain ⟨hbd,hrs⟩ := qq_reverse_blocks_rigid a b d r s z hr hs ha
      (by omega) (by omega) heq
    subst d
    subst s
    exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- In S/S, the middle singleton and the contracted triple already
determine the two quadratic orientations up to the full rotation. -/
theorem S_diagonal_polynomial (a b c d e A B C D E r s R S : ℤ)
    (z : ℕ+) (hr : (z.val : ℤ) < r) (hs : (z.val : ℤ) < s)
    (hR : (z.val : ℤ) < R) (hS : (z.val : ℤ) < S)
    (hF : Domain a b c d e r z.val z.val s)
    (hH : Domain A B C D E R z.val z.val S)
    (heq : interval complete a b c d e r z.val z.val s =
      interval complete A B C D E R z.val z.val S) :
    (r = R ∧ s = S ∧ a = A ∧ b = B ∧ c = C ∧ d = D ∧ e = E) ∨
      (r = S ∧ s = R ∧ a = E ∧ b = D ∧ c = C ∧ d = B ∧ e = A) := by
  have hz := z.pos
  have ha := hF.2.2.2.2.1; have hb := hF.2.2.2.2.2.1
  have hc := hF.2.2.2.2.2.2.1; have hd := hF.2.2.2.2.2.2.2.1
  have he := hF.2.2.2.2.2.2.2.2
  have hA := hH.2.2.2.2.1; have hB := hH.2.2.2.2.2.1
  have hC := hH.2.2.2.2.2.2.1; have hD := hH.2.2.2.2.2.2.2.1
  have hE := hH.2.2.2.2.2.2.2.2
  have hzero := congrArg (fun p : CompleteRing =>
    (Staircase.minimumPolynomial z p).coeff 0) heq
  have htop := congrArg (fun p : CompleteRing =>
    (Staircase.minimumPolynomial z p).coeff 2) heq
  rw [S_variable_marked a b c d e r s z hr hs hF,
    S_variable_marked A B C D E R S z hR hS hH] at hzero htop
  norm_num at hzero htop
  have hzero' : complete c*two complete r a b*two complete s d e =
      complete C*two complete R A B*two complete S D E := by
    convert hzero using 1 <;> ring
  obtain ⟨hcC,hpairs⟩ := singleton_two_pair_reading
    c a b d e C A B D E r s R S (by omega) (by omega)
    (by omega) (by omega) ha (by omega) (by omega) he
    (by omega) (by omega) hA (by omega) (by omega) hE hzero'
  have htopData := three_variable_rigidity
    a (b+c+d-2*z.val) e r s A (B+C+D-2*z.val) E R S
    (by omega) (by omega) ha (by omega) he
    (by omega) (by omega) hA (by omega) hE htop
  rcases hpairs with ⟨h1,h2,hab,hde⟩ | ⟨h1,h2,hab,hde⟩
  all_goals
    rcases hab with ⟨h3,h4⟩ | ⟨h3,h4⟩
    all_goals
      rcases hde with ⟨h5,h6⟩ | ⟨h5,h6⟩
      all_goals
        rcases htopData with ⟨ht1,ht2,ht3,ht4,ht5⟩ | ⟨ht1,ht2,ht3,ht4,ht5⟩
        all_goals first
          | exact Or.inl ⟨by omega,by omega,by omega,by omega,hcC,by omega,by omega⟩
          | exact Or.inr ⟨by omega,by omega,by omega,by omega,hcC,by omega,by omega⟩

private theorem QS_ordered_top_ne (a b c d e A B C D E r s R S : ℤ)
    (z : ℕ+) (hr : (z.val : ℤ) < r) (hs : (z.val : ℤ) < s)
    (hR : (z.val : ℤ) < R) (hS : (z.val : ℤ) < S)
    (hF : Domain a b c d e z.val r z.val s)
    (hH : Domain A B C D E R z.val z.val S)
    (htr : r = R) (hts : s = S)
    (htA : a+b-z.val = A) (htE : e = E) :
    interval complete a b c d e z.val r z.val s ≠
      interval complete A B C D E R z.val z.val S := by
  have hz := z.pos
  have ha := hF.2.2.2.2.1; have hb := hF.2.2.2.2.2.1
  have hc := hF.2.2.2.2.2.2.1; have hd := hF.2.2.2.2.2.2.2.1
  have he := hF.2.2.2.2.2.2.2.2
  have hA := hH.2.2.2.2.1; have hB := hH.2.2.2.2.2.1
  have hC := hH.2.2.2.2.2.2.1; have hD := hH.2.2.2.2.2.2.2.1
  have hE := hH.2.2.2.2.2.2.2.2
  intro heq
  have hzero := congrArg (fun p : CompleteRing =>
    (Staircase.minimumPolynomial z p).coeff 0) heq
  rw [Q_variable_marked a b c d e r s z hr hs hF,
    S_variable_marked A B C D E R S z hR hS hH] at hzero
  norm_num at hzero
  have hzero' : complete a*two complete r b c*two complete s d e =
      complete C*two complete R A B*two complete S D E := by
    convert hzero using 1 <;> ring
  obtain ⟨haC,hpairs⟩ := singleton_two_pair_reading
    a b c d e C A B D E r s R S (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) he
    (by omega) (by omega) hA (by omega) (by omega) hE hzero'
  subst C
  subst A
  subst E
  subst R
  subst S
  have hfirst := qsFirst_eq_zero a b c d e (a+b-z.val) B D r s z hr hs hF hH heq
  have hcases :
      (c = a+b-z.val ∧ B = b ∧ D = d) ∨
      (r = s ∧ d = a+b-z.val ∧ e = b ∧ B = b ∧ D = c) ∨
      (r = s ∧ d = a+b-z.val ∧ e = c ∧ B = c ∧ D = b) ∨
      (r = s ∧ c = a+b-z.val ∧ e = a+b-z.val ∧ B = d ∧ D = b) := by
    rcases hpairs with ⟨h1,h2,hbc,hde⟩ | ⟨h1,h2,hbc,hde⟩
    all_goals
      rcases hbc with ⟨h3,h4⟩ | ⟨h3,h4⟩
      all_goals
        rcases hde with ⟨h5,h6⟩ | ⟨h5,h6⟩
        all_goals omega
  rcases hcases with ⟨hc',hB',hD'⟩ |
    ⟨hrs,hd',he',hB',hD'⟩ | ⟨hrs,hd',he',hB',hD'⟩ | ⟨hrs,hc',he',hB',hD'⟩
  · subst c
    subst B
    subst D
    exact qs_direct_allocation_ne a b d e r s z hr hs ha hb hd he hfirst
  · subst s
    subst d
    subst e
    subst B
    subst D
    exact qs_cross_allocation_ne false a b c r z hr ha (by omega) (by omega) hfirst
  · subst s
    subst d
    subst e
    subst B
    subst D
    exact qs_cross_allocation_ne true a b c r z hr ha (by omega) (by omega) hfirst
  · subst s
    subst c
    subst e
    subst B
    subst D
    exact qs_last_allocation_ne a b d r z hr ha (by omega) (by omega) hfirst

/-- Q and S never have the same full polynomial, even when their two
nonminimum gap labels coincide or their contracted triple reverses. -/
theorem QS_polynomial_ne (a b c d e A B C D E r s R S : ℤ)
    (z : ℕ+) (hr : (z.val : ℤ) < r) (hs : (z.val : ℤ) < s)
    (hR : (z.val : ℤ) < R) (hS : (z.val : ℤ) < S)
    (hF : Domain a b c d e z.val r z.val s)
    (hH : Domain A B C D E R z.val z.val S) :
    interval complete a b c d e z.val r z.val s ≠
      interval complete A B C D E R z.val z.val S := by
  have hz := z.pos
  have ha := hF.2.2.2.2.1; have hb := hF.2.2.2.2.2.1
  have hc := hF.2.2.2.2.2.2.1; have hd := hF.2.2.2.2.2.2.2.1
  have he := hF.2.2.2.2.2.2.2.2
  have hA := hH.2.2.2.2.1; have hB := hH.2.2.2.2.2.1
  have hC := hH.2.2.2.2.2.2.1; have hD := hH.2.2.2.2.2.2.2.1
  have hE := hH.2.2.2.2.2.2.2.2
  intro heq
  have htop := congrArg (fun p : CompleteRing =>
    (Staircase.minimumPolynomial z p).coeff 2) heq
  rw [Q_variable_marked a b c d e r s z hr hs hF,
    S_variable_marked A B C D E R S z hR hS hH] at htop
  norm_num at htop
  have htopData := three_variable_rigidity
    (a+b-z.val) (c+d-z.val) e r s A (B+C+D-2*z.val) E R S
    (by omega) (by omega) (by omega) (by omega) he
    (by omega) (by omega) hA (by omega) hE htop
  rcases htopData with ⟨h1,h2,h3,_,h5⟩ | ⟨h1,h2,h3,_,h5⟩
  · exact QS_ordered_top_ne a b c d e A B C D E r s R S z hr hs hR hS
      hF hH h1 h2 h3 h5 heq
  · have hHr : Domain E D C B A S z.val z.val R :=
      ⟨by omega,by omega,by omega,by omega,hE,by omega,hC,by omega,hA⟩
    have heqr : interval complete a b c d e z.val r z.val s =
        interval complete E D C B A S z.val z.val R :=
      heq.trans (interval_reverse complete A B C D E R z.val z.val S).symm
    exact QS_ordered_top_ne a b c d e E D C B A r s S R z hr hs hS hR
      hF hHr h1 h2 h3 h5 heqr

private theorem scalar_three_ne_two_pair
    (a b c d e A B C D E r s R S : ℤ)
    (ha : 0 < a) (hb : 0 < b) (hA : 0 < A)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hc : r < c) (hd : r+s < d) (he : s < e)
    (hR : 0 ≤ R) (hS : 0 ≤ S) (hB : R < B) (hC : R < C) (hD : S < D) (hE : S < E) :
    complete a*complete b*threeInterval complete c d e r s ≠
      complete A*two complete R B C*two complete S D E := by
  let aP := (scalarSingleton a ha).toBetaDiagram
  let bP := (scalarSingleton b hb).toBetaDiagram
  let AP := (scalarSingleton A hA).toBetaDiagram
  let P3 := (threeVariableProfile c d e r s hr hs hc hd he).toBetaDiagram
  let P2 := (twoScalarProfile B C R hR hB hC).toBetaDiagram
  let Q2 := (twoScalarProfile D E S hS hD hE).toBetaDiagram
  intro h
  apply singleton_triple_ne_singleton_two_pair aP bP AP P3 P2 Q2
    (Gluing.Profile.toBetaDiagram_connected _) (Gluing.Profile.toBetaDiagram_connected _)
    (Gluing.Profile.toBetaDiagram_connected _)
  simpa only [aP,bP,AP,P3,P2,Q2,scalarSingleton_schur,
    threeVariableProfile_schur,twoScalarProfile_schur] using h

/-- The full zero layer excludes all four crossings between the two
safe-cut component-size patterns.  The booleans choose the actual P/R and
Q/S words, not a separately assumed factorization. -/
theorem triple_pair_placements_ne (pCase qCase : Bool)
    (a b c d e A B C D E r s R S : ℤ) (z : ℕ+)
    (hr : (z.val : ℤ) < r) (hs : (z.val : ℤ) < s)
    (hR : (z.val : ℤ) < R) (hS : (z.val : ℤ) < S)
    (hF : if pCase then Domain a b c d e z.val z.val r s
      else Domain a b c d e z.val r s z.val)
    (hH : if qCase then Domain A B C D E z.val R z.val S
      else Domain A B C D E R z.val z.val S) :
    (if pCase then interval complete a b c d e z.val z.val r s
      else interval complete a b c d e z.val r s z.val) ≠
    (if qCase then interval complete A B C D E z.val R z.val S
      else interval complete A B C D E R z.val z.val S) := by
  have hz := z.pos
  intro heq
  have hzero := congrArg (fun p : CompleteRing =>
    (Staircase.minimumPolynomial z p).coeff 0) heq
  cases pCase <;> cases qCase
  all_goals simp only [Bool.false_eq_true,if_false,if_true] at hF hH heq hzero
  all_goals
    first
      | rw [R_variable_marked _ _ _ _ _ r s z hr hs hF,
          S_variable_marked _ _ _ _ _ R S z hR hS hH] at hzero
      | rw [R_variable_marked _ _ _ _ _ r s z hr hs hF,
          Q_variable_marked _ _ _ _ _ R S z hR hS hH] at hzero
      | rw [P_variable_marked _ _ _ _ _ r s z hr hs hF,
          S_variable_marked _ _ _ _ _ R S z hR hS hH] at hzero
      | rw [P_variable_marked _ _ _ _ _ r s z hr hs hF,
          Q_variable_marked _ _ _ _ _ R S z hR hS hH] at hzero
  all_goals
    norm_num at hzero
    rcases hF with ⟨hf0,hf1,hf2,hf3,hf4,hf5,hf6,hf7,hf8⟩
    rcases hH with ⟨hh0,hh1,hh2,hh3,hh4,hh5,hh6,hh7,hh8⟩
  · apply scalar_three_ne_two_pair a e b c d C A B D E r s R S
      (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    convert hzero using 1 <;> ring
  · apply scalar_three_ne_two_pair a e b c d A B C D E r s R S
      (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    convert hzero using 1 <;> ring
  · apply scalar_three_ne_two_pair a b c d e C A B D E r s R S
      (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    convert hzero using 1 <;> ring
  · apply scalar_three_ne_two_pair a b c d e A B C D E r s R S
      (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    exact hzero

inductive TwoMinimumPlacement where
  | p | q | r | s
  deriving DecidableEq

def TwoMinimumPlacement.word (k : TwoMinimumPlacement) (z r s : ℕ) : Fin 4 → ℕ :=
  match k with
  | .p => ![z,z,r,s]
  | .q => ![z,r,z,s]
  | .r => ![z,r,s,z]
  | .s => ![r,z,z,s]

private theorem profile_schur_interval_complete (P : Gluing.Profile 4)
    (hP : Staircase.Thick P) :
    P.toBetaDiagram.schur = interval complete
      (P.r 0) (P.r 1) (P.r 2) (P.r 3) (P.r 4)
      (P.g 0) (P.g 1) (P.g 2) (P.g 3) := by
  rw [Gluing.Profile.toBetaDiagram_schur,schur_interval P hP.hessenberg]
  simp only [interval,complete_eq_hh]

/-- Rotation normalizes precisely the six words of two minimum seams.
The two remaining gaps are not sorted, so coincident gaps are retained. -/
theorem normalize_two_minimum_word (P : Gluing.Profile 4) (z : ℕ+)
    (hmin : ∀ j, z.val ≤ P.g j) (hm : Staircase.minimumMultiplicity P z = 2) :
    ∃ rev : Bool, ∃ k : TwoMinimumPlacement, ∃ r s : ℕ+,
      z.val < r.val ∧ z.val < s.val ∧
        (profileOrientation P rev).g = k.word z.val r.val s.val := by
  obtain ⟨r,s,hr,hs,hword⟩ := two_minimum_gap_words P z hmin hm
  let R : ℕ+ := ⟨r,by have := z.pos; omega⟩
  let S : ℕ+ := ⟨s,by have := z.pos; omega⟩
  rcases hword with h | h | h | h | h | h
  · exact ⟨false,.p,R,S,hr,hs,h⟩
  · exact ⟨false,.q,R,S,hr,hs,h⟩
  · exact ⟨false,.r,R,S,hr,hs,h⟩
  · exact ⟨false,.s,R,S,hr,hs,h⟩
  · refine ⟨true,.q,R,S,hr,hs,?_⟩
    funext i; fin_cases i <;> simp [profileOrientation,Gluing.Profile.rotate,h,
      TwoMinimumPlacement.word,R,S]
  · refine ⟨true,.p,R,S,hr,hs,?_⟩
    funext i; fin_cases i <;> simp [profileOrientation,Gluing.Profile.rotate,h,
      TwoMinimumPlacement.word,R,S]

private theorem two_upper_gap_pair (P Q : Gluing.Profile 4)
    (k l : TwoMinimumPlacement) (z r s R S : ℕ)
    (hr : z < r) (hs : z < s) (hR : z < R) (hS : z < S)
    (hP : P.g = k.word z r s) (hQ : Q.g = l.word z R S)
    (he : P.toBetaDiagram.schur = Q.toBetaDiagram.schur) :
    (r = R ∧ s = S) ∨ (r = S ∧ s = R) := by
  have he' : P.schur = Q.schur := by
    simpa only [Gluing.Profile.toBetaDiagram_schur] using he
  have hg := Gluing.Profile.gaps_eq_of_schur_eq he'
  have hu : (Finset.univ : Finset (Fin 4)).val = {0,1,2,3} := by decide
  have hsum := congrArg Multiset.sum hg
  have hRmem : R ∈ P.gapMultiset := by
    rw [hg]
    cases l
    · exact Multiset.mem_map.mpr ⟨(2 : Fin 4),by simp,by simp [hQ,TwoMinimumPlacement.word]⟩
    · exact Multiset.mem_map.mpr ⟨(1 : Fin 4),by simp,by simp [hQ,TwoMinimumPlacement.word]⟩
    · exact Multiset.mem_map.mpr ⟨(1 : Fin 4),by simp,by simp [hQ,TwoMinimumPlacement.word]⟩
    · exact Multiset.mem_map.mpr ⟨(0 : Fin 4),by simp,by simp [hQ,TwoMinimumPlacement.word]⟩
  cases k <;> cases l
  all_goals
    simp [Gluing.Profile.gapMultiset,hu,hP,hQ,TwoMinimumPlacement.word] at hsum hRmem
    omega

private theorem PR_full_class (P Q : Gluing.Profile 4)
    (hP : Staircase.Thick P) (hQ : Staircase.Thick Q) (z r s R S : ℕ+)
    (hr : z.val < r.val) (hs : z.val < s.val)
    (hR : z.val < R.val) (hS : z.val < S.val)
    (hPg : P.g = ![z.val,z.val,r.val,s.val])
    (hQg : Q.g = ![z.val,R.val,S.val,z.val])
    (he : P.toBetaDiagram.schur = Q.toBetaDiagram.schur) :
    ContactRelation true P Q := by
  have hpair := two_upper_gap_pair P Q .p .r z.val r.val s.val R.val S.val
    hr hs hR hS hPg hQg he
  by_cases hrs : r = s
  · have hRr : R = r := by
      rcases hpair with ⟨h1,h2⟩ | ⟨h1,h2⟩
      · exact PNat.coe_inj.mp h1.symm
      · exact (PNat.coe_inj.mp h2.symm).trans hrs.symm
    have hSr : S = r := by
      rcases hpair with ⟨h1,h2⟩ | ⟨h1,h2⟩
      · exact (PNat.coe_inj.mp h2.symm).trans hrs.symm
      · exact PNat.coe_inj.mp h1.symm
    subst s
    subst R
    subst S
    exact a2_cross_pattern P Q hP hQ z r hr hPg hQg he
  · have hne : (r.val : ℤ) ≠ s.val := by
      intro h
      apply hrs
      exact_mod_cast h
    have hpoly := (profile_schur_interval_complete P hP).symm.trans
      (he.trans (profile_schur_interval_complete Q hQ))
    have hPD := domain_of_profile P hP
    have hQD := domain_of_profile Q hQ
    simp [hPg,hQg] at hpoly hPD hQD
    exact False.elim (PR_distinct_gaps_ne
      (P.r 0) (P.r 1) (P.r 2) (P.r 3) (P.r 4)
      (Q.r 0) (Q.r 1) (Q.r 2) (Q.r 3) (Q.r 4)
      r.val s.val R.val S.val z (by exact_mod_cast hr) (by exact_mod_cast hs)
      (by exact_mod_cast hR) (by exact_mod_cast hS) hne hPD hQD hpoly)

private theorem normalized_two_minimum_class (P Q : Gluing.Profile 4)
    (hP : Staircase.Thick P) (hQ : Staircase.Thick Q)
    (k l : TwoMinimumPlacement) (z r s R S : ℕ+)
    (hr : z.val < r.val) (hs : z.val < s.val)
    (hR : z.val < R.val) (hS : z.val < S.val)
    (hPg : P.g = k.word z.val r.val s.val)
    (hQg : Q.g = l.word z.val R.val S.val)
    (he : P.toBetaDiagram.schur = Q.toBetaDiagram.schur) :
    P = Q ∨ P = Q.rotate ∨ ContactRelation true P Q := by
  have hpoly := (profile_schur_interval_complete P hP).symm.trans
    (he.trans (profile_schur_interval_complete Q hQ))
  have hPD := domain_of_profile P hP
  have hQD := domain_of_profile Q hQ
  have hr' : (z.val : ℤ) < r.val := by exact_mod_cast hr
  have hs' : (z.val : ℤ) < s.val := by exact_mod_cast hs
  have hR' : (z.val : ℤ) < R.val := by exact_mod_cast hR
  have hS' : (z.val : ℤ) < S.val := by exact_mod_cast hS
  cases k <;> cases l
  all_goals simp [hPg,hQg,TwoMinimumPlacement.word] at hpoly hPD hQD
  · exact Or.inl (P_diagonal_rigidity P Q hP hQ z r s R S hr hs hR hS hPg hQg he)
  · exact False.elim (triple_pair_placements_ne true true
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ z hr' hs' hR' hS' hPD hQD hpoly)
  · exact Or.inr (Or.inr (PR_full_class P Q hP hQ z r s R S hr hs hR hS hPg hQg he))
  · exact False.elim (triple_pair_placements_ne true false
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ z hr' hs' hR' hS' hPD hQD hpoly)
  · exact False.elim (triple_pair_placements_ne true true
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ z hR' hS' hr' hs' hQD hPD hpoly.symm)
  · obtain ⟨hg0,hg1,h0,h1,h2,h3,h4⟩ := Q_diagonal_polynomial
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ z hr' hs' hR' hS' hPD hQD hpoly
    left
    apply Gluing.Profile.ext
    · exact five_rows_eq_of_cast P Q h0 h1 h2 h3 h4
    · have hrr : r = R := by exact_mod_cast hg0
      have hss : s = S := by exact_mod_cast hg1
      rw [hPg,hQg,hrr,hss]
  · exact False.elim (triple_pair_placements_ne false true
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ z hR' hS' hr' hs' hQD hPD hpoly.symm)
  · exact False.elim (QS_polynomial_ne _ _ _ _ _ _ _ _ _ _ _ _ _ _ z
      hr' hs' hR' hS' hPD hQD hpoly)
  · exact Or.inr (Or.inr (contact_relation_symm
      (PR_full_class Q P hQ hP z R S r s hR hS hr hs hQg hPg he.symm)))
  · exact False.elim (triple_pair_placements_ne false true
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ z hr' hs' hR' hS' hPD hQD hpoly)
  · have h := R_diagonal_polynomial _ _ _ _ _ _ _ _ _ _ _ _ _ _ z
      hr' hs' hR' hS' hPD hQD hpoly
    rcases h with ⟨hg0,hg1,h0,h1,h2,h3,h4⟩ | ⟨hg0,hg1,h0,h1,h2,h3,h4⟩
    · left
      apply Gluing.Profile.ext
      · exact five_rows_eq_of_cast P Q h0 h1 h2 h3 h4
      · have hrr : r = R := by exact_mod_cast hg0
        have hss : s = S := by exact_mod_cast hg1
        rw [hPg,hQg,hrr,hss]
    · right; left
      apply Gluing.Profile.ext
      · exact five_rows_eq_of_cast P Q.rotate
          (by simpa [Profile.rotate] using h0) (by simpa [Profile.rotate] using h1)
          (by simpa [Profile.rotate] using h2) (by simpa [Profile.rotate] using h3)
          (by simpa [Profile.rotate] using h4)
      · have hrr : r = S := by exact_mod_cast hg0
        have hss : s = R := by exact_mod_cast hg1
        funext i
        fin_cases i <;> simp [hPg,hQg,TwoMinimumPlacement.word,Profile.rotate,hrr,hss]
  · exact False.elim (triple_pair_placements_ne false false
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ z hr' hs' hR' hS' hPD hQD hpoly)
  · exact False.elim (triple_pair_placements_ne true false
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ z hR' hS' hr' hs' hQD hPD hpoly.symm)
  · exact False.elim (QS_polynomial_ne _ _ _ _ _ _ _ _ _ _ _ _ _ _ z
      hR' hS' hr' hs' hQD hPD hpoly.symm)
  · exact False.elim (triple_pair_placements_ne false false
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ z hR' hS' hr' hs' hQD hPD hpoly.symm)
  · have h := S_diagonal_polynomial _ _ _ _ _ _ _ _ _ _ _ _ _ _ z
      hr' hs' hR' hS' hPD hQD hpoly
    rcases h with ⟨hg0,hg1,h0,h1,h2,h3,h4⟩ | ⟨hg0,hg1,h0,h1,h2,h3,h4⟩
    · left
      apply Gluing.Profile.ext
      · exact five_rows_eq_of_cast P Q h0 h1 h2 h3 h4
      · have hrr : r = R := by exact_mod_cast hg0
        have hss : s = S := by exact_mod_cast hg1
        rw [hPg,hQg,hrr,hss]
    · right; left
      apply Gluing.Profile.ext
      · exact five_rows_eq_of_cast P Q.rotate
          (by simpa [Profile.rotate] using h0) (by simpa [Profile.rotate] using h1)
          (by simpa [Profile.rotate] using h2) (by simpa [Profile.rotate] using h3)
          (by simpa [Profile.rotate] using h4)
      · have hrr : r = S := by exact_mod_cast hg0
        have hss : s = R := by exact_mod_cast hg1
        funext i
        fin_cases i <;> simp [hPg,hQg,TwoMinimumPlacement.word,Profile.rotate,hrr,hss]

/-- Two occurrences of the minimum admit exactly the A2 crossing besides
translation and rotation.  The mate's six-word inventory is derived from
the full polynomial and the gap multiset. -/
theorem two_minimum_full_class (P Q : Gluing.Profile 4)
    (hP : Staircase.Thick P) (hQ : Staircase.Thick Q) (z : ℕ+)
    (hmin : ∀ j, z.val ≤ P.g j) (hm : Staircase.minimumMultiplicity P z = 2) :
    P.toBetaDiagram.schur = Q.toBetaDiagram.schur ↔
      P = Q ∨ P = Q.rotate ∨ ContactRelation true P Q := by
  constructor
  · intro he
    have he' : P.schur = Q.schur := by
      simpa only [Gluing.Profile.toBetaDiagram_schur] using he
    have hminQ := gap_minimum_preserved P Q z hmin he
    have hmQ : Staircase.minimumMultiplicity Q z = 2 := by
      rw [← minimumMultiplicity_eq_of_schur_eq P Q z he']
      exact hm
    obtain ⟨u,k,r,s,hr,hs,hPg⟩ := normalize_two_minimum_word P z hmin hm
    obtain ⟨v,l,R,S,hR,hS,hQg⟩ := normalize_two_minimum_word Q z hminQ hmQ
    have heo : (profileOrientation P u).toBetaDiagram.schur =
        (profileOrientation Q v).toBetaDiagram.schur := by
      rw [profileOrientation_schur,profileOrientation_schur]
      exact he
    have h := normalized_two_minimum_class _ _
      (profileOrientation_thick P hP u) (profileOrientation_thick Q hQ v)
      k l z r s R S hr hs hR hS hPg hQg heo
    rcases h with h | h | h
    · rcases equality_unorient h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · have hr : profileOrientation P u = profileOrientation Q (!v) := by
        cases v <;> simpa [profileOrientation] using h
      rcases equality_unorient hr with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (contact_relation_unorient h))
  · rintro (rfl | h | h)
    · rfl
    · rw [h,Gluing.Profile.toBetaDiagram_schur,Gluing.Profile.toBetaDiagram_schur,
        Gluing.Profile.schur_rotate]
    · exact contact_relation_schur_eq h

private theorem constant_b_member (P : Gluing.Profile 4) (p m : ℤ) (z : ℕ+)
    (hp : 2*(z.val : ℤ) < p) (hm : 2*(z.val : ℤ) < m) (hne : p ≠ m)
    (h : ConstantGapFiveClassification.BMember P p m z.val) :
    BMember P
      { p := p, m := m, z := z.val, w := z.val
        z_pos := by have := z.pos; omega
        w_pos := by have := z.pos; omega
        p_gt := by omega
        m_gt := by omega
        p_ne_m := hne } := by
  let X : BParameters :=
    { p := p, m := m, z := z.val, w := z.val
      z_pos := by have := z.pos; omega
      w_pos := by have := z.pos; omega
      p_gt := by omega
      m_gt := by omega
      p_ne_m := hne }
  change BMember P X
  rcases h with ⟨hg,hr⟩
  rcases hr with hr | hr | hr | hr
  · left
    apply Gluing.Profile.ext
    · funext i; have hi := congrFun hr i
      fin_cases i <;> simp [ConstantGapFiveClassification.rows,X,BParameters.F,bProfileF,profile] at hi ⊢ <;> omega
    · funext j; have hj := hg j
      fin_cases j <;> simpa [X,BParameters.F,bProfileF,profile] using hj
  · right; right; left
    apply Gluing.Profile.ext
    · funext i; have hi := congrFun hr i
      fin_cases i <;> simp [ConstantGapFiveClassification.rows,X,BParameters.H,bProfileH,profile] at hi ⊢ <;> omega
    · funext j; have hj := hg j
      fin_cases j <;> simpa [X,BParameters.H,bProfileH,profile] using hj
  · right; left
    apply Gluing.Profile.ext
    · funext i; have hi := congrFun hr i
      fin_cases i <;> simp [ConstantGapFiveClassification.rows,X,BParameters.F,bProfileF,profile,Gluing.Profile.rotate] at hi ⊢ <;> omega
    · funext j; have hj := hg j
      fin_cases j <;> simpa [X,BParameters.F,bProfileF,profile,Gluing.Profile.rotate] using hj
  · right; right; right
    apply Gluing.Profile.ext
    · funext i; have hi := congrFun hr i
      fin_cases i <;> simp [ConstantGapFiveClassification.rows,X,BParameters.H,bProfileH,profile,Gluing.Profile.rotate] at hi ⊢ <;> omega
    · funext j; have hj := hg j
      fin_cases j <;> simpa [X,BParameters.H,bProfileH,profile,Gluing.Profile.rotate] using hj

/-- All exceptional classes use actual row and gap words. -/
def Classified (P Q : Gluing.Profile 4) : Prop :=
  P = Q ∨ P = Q.rotate ∨ ContactRelation false P Q ∨ ContactRelation true P Q ∨ BRelation P Q

/-- The completed thick five-row classification, partitioned by minimum-gap
multiplicity.  The mate has no prescribed gap placement. -/
theorem thick_five_full_class (P Q : Gluing.Profile 4)
    (hP : Staircase.Thick P) (hQ : Staircase.Thick Q)
    (hgap : ∀ j, 0 < P.g j) :
    P.toBetaDiagram.schur = Q.toBetaDiagram.schur ↔ Classified P Q := by
  constructor
  · intro he
    let z : ℕ+ := ⟨min (P.g 0) (min (P.g 1) (min (P.g 2) (P.g 3))),by
      have h0 := hgap 0; have h1 := hgap 1
      have h2 := hgap 2; have h3 := hgap 3
      omega⟩
    have hmin : ∀ j, z.val ≤ P.g j := by intro j; fin_cases j <;> dsimp [z] <;> omega
    have hocc : ∃ j, P.g j = z.val := by
      dsimp [z]
      by_cases h0 : P.g 0 ≤ min (P.g 1) (min (P.g 2) (P.g 3))
      · exact ⟨0,by omega⟩
      · by_cases h1 : P.g 1 ≤ min (P.g 2) (P.g 3)
        · exact ⟨1,by omega⟩
        · by_cases h2 : P.g 2 ≤ P.g 3
          · exact ⟨2,by omega⟩
          · exact ⟨3,by omega⟩
    have hmRange : 1 ≤ Staircase.minimumMultiplicity P z ∧
        Staircase.minimumMultiplicity P z ≤ 4 := by
      have hmem : z.val ∈ P.gapMultiset := by
        obtain ⟨j,hj⟩ := hocc
        exact Multiset.mem_map.mpr ⟨j,by simp,hj⟩
      have hcard : P.gapMultiset.card = 4 := by simp [Profile.gapMultiset]
      rw [minimumMultiplicity_eq_count]
      exact ⟨Multiset.one_le_count_iff_mem.mpr hmem,
        by simpa only [hcard] using Multiset.count_le_card z.val P.gapMultiset⟩
    have he' : P.schur = Q.schur := by
      simpa only [Gluing.Profile.toBetaDiagram_schur] using he
    by_cases hm1 : Staircase.minimumMultiplicity P z = 1
    · rcases (one_minimum_full_class P Q hP hQ z hmin hm1).mp he with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
    · by_cases hm2 : Staircase.minimumMultiplicity P z = 2
      · rcases (two_minimum_full_class P Q hP hQ z hmin hm2).mp he with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · by_cases hm3 : Staircase.minimumMultiplicity P z = 3
        · rcases (three_minimum_full_class P Q hP hQ z hmin hm3).mp he with h | h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
        · have hm4 : Staircase.minimumMultiplicity P z = 4 := by omega
          have h := (four_minima_full_class P Q hP hQ z hm4).mp he'
          rcases h with h | h | ⟨p,m,hp,hm,hne,hPm,hQm⟩
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Or.inr (Or.inr
              ⟨_,constant_b_member P p m z hp hm hne hPm,
                constant_b_member Q p m z hp hm hne hQm⟩)))
  · rintro (rfl | h | h | h | h)
    · rfl
    · rw [h,Gluing.Profile.toBetaDiagram_schur,Gluing.Profile.toBetaDiagram_schur,
        Gluing.Profile.schur_rotate]
    · exact contact_relation_schur_eq h
    · exact contact_relation_schur_eq h
    · exact b_relation_schur_eq h

/-- The four manuscript schemes retain their full standing parameter domains.
M1 and M2 are intentionally not identified at zero deformation. -/
inductive Scheme where
  | m1 (X : StaircaseFiveFamilies.CommutationParameters)
  | m2 (X : StaircaseFiveFamilies.CommutationParameters)
  | m3 (X : StaircaseFiveFamilies.ContactParameters)
  | m4 (X : StaircaseFiveFamilies.ContactParameters)

def Scheme.first : Scheme → Gluing.Profile 4
  | .m1 X => StaircaseFiveFamilies.m1F X
  | .m2 X => StaircaseFiveFamilies.m2F X
  | .m3 X => StaircaseFiveFamilies.m3F X
  | .m4 X => StaircaseFiveFamilies.m4F X

def Scheme.second : Scheme → Gluing.Profile 4
  | .m1 X => StaircaseFiveFamilies.m1H X
  | .m2 X => StaircaseFiveFamilies.m2H X
  | .m3 X => StaircaseFiveFamilies.m3H X
  | .m4 X => StaircaseFiveFamilies.m4H X

def Scheme.at (X : Scheme) : Fin 4 → Gluing.Profile 4 :=
  ![X.first,X.first.rotate,X.second,X.second.rotate]

def Scheme.Member (X : Scheme) (P : Gluing.Profile 4) : Prop := ∃ i, P = X.at i

theorem Scheme.first_second_schur (X : Scheme) :
    X.first.toBetaDiagram.schur = X.second.toBetaDiagram.schur := by
  cases X with
  | m1 X => exact StaircaseFiveFamilies.m1_schur_eq X
  | m2 X => exact StaircaseFiveFamilies.m2_schur_eq X
  | m3 X => exact StaircaseFiveFamilies.m3_schur_eq X
  | m4 X => exact StaircaseFiveFamilies.m4_schur_eq X

theorem Scheme.at_schur (X : Scheme) (i : Fin 4) :
    (X.at i).toBetaDiagram.schur = X.first.toBetaDiagram.schur := by
  have he := X.first_second_schur
  fin_cases i <;> simp [Scheme.at,Gluing.Profile.toBetaDiagram_schur,
    Gluing.Profile.schur_rotate] at he ⊢ <;> first | exact he.symm | rfl

theorem Scheme.member_schur {X : Scheme} {P Q : Gluing.Profile 4}
    (hP : X.Member P) (hQ : X.Member Q) :
    P.toBetaDiagram.schur = Q.toBetaDiagram.schur := by
  obtain ⟨i,rfl⟩ := hP
  obtain ⟨j,rfl⟩ := hQ
  exact (X.at_schur i).trans (X.at_schur j).symm

theorem Scheme.at_injective (X : Scheme) : Function.Injective X.at := by
  intro i j he
  have h0 := congrArg (fun P : Gluing.Profile 4 => (P.r 0 : ℤ)) he
  have h1 := congrArg (fun P : Gluing.Profile 4 => (P.r 1 : ℤ)) he
  have h3 := congrArg (fun P : Gluing.Profile 4 => (P.r 3 : ℤ)) he
  have h4 := congrArg (fun P : Gluing.Profile 4 => (P.r 4 : ℤ)) he
  cases X
  all_goals
    rename_i X
    first
      | (have hx0 := X.t_nonneg; have hx1 := X.d_nonneg
         have hx2 := X.a_gt; have hx3 := X.b_gt; have hx4 := X.a_ne_b)
      | (have hx0 := X.d_nonneg; have hx1 := X.a_pos; have hx2 := X.b_gt)
    fin_cases i <;> fin_cases j
    all_goals first | rfl |
      (simp [Scheme.at,Scheme.first,Scheme.second,
        StaircaseFiveFamilies.m1F,StaircaseFiveFamilies.m1H,
        StaircaseFiveFamilies.m2F,StaircaseFiveFamilies.m2H,
        StaircaseFiveFamilies.m3F,StaircaseFiveFamilies.m3H,
        StaircaseFiveFamilies.m4F,StaircaseFiveFamilies.m4H,
        Gluing.Profile.rotate,StaircaseFiveFamilies.profile] at h0 h1 h3 h4; omega)

/-- Four distinct normalized profiles are four distinct translation classes. -/
theorem Scheme.at_translation_distinct (X : Scheme) (i j : Fin 4)
    (h : (X.at i).toBetaDiagram.TranslationEquivalent (X.at j).toBetaDiagram) : i = j :=
  X.at_injective (profile_eq_of_translation _ _ h)

private theorem contact_member_scheme (second : Bool)
    (X : StaircaseFiveFamilies.ContactParameters) (P : Gluing.Profile 4)
    (h : ContactMember second P X) :
    (if second then Scheme.m4 X else Scheme.m3 X).Member P := by
  cases second <;> simp only [ContactMember,if_true,if_false] at h ⊢
  all_goals rcases h with h | h | h | h
  all_goals first
    | exact ⟨0,h⟩
    | exact ⟨1,h⟩
    | exact ⟨2,h⟩
    | exact ⟨3,h⟩

private theorem b_member_scheme (X : BParameters) :
    ∃ Y : Scheme, ∀ P, BMember P X → Y.Member P := by
  by_cases hzw : X.w ≤ X.z
  · let Y := StaircaseFiveFamilies.bM1Parameters X.p X.m X.z X.w
      (by have := X.w_pos; omega) hzw X.p_gt X.m_gt X.p_ne_m
    have hw := StaircaseFiveFamilies.b_m1_words X.p X.m X.z X.w
      (by have := X.w_pos; omega) hzw X.p_gt X.m_gt X.p_ne_m
    have hF : X.F = StaircaseFiveFamilies.m1F Y := by
      apply Gluing.Profile.ext
      · funext i; have h := congrFun hw.1 i
        fin_cases i <;> simp [Y,BParameters.F,bProfileF,profile] at h ⊢ <;> omega
      · funext j; have h := congrFun hw.2.1 j
        fin_cases j <;> simp [Y,BParameters.F,bProfileF,profile] at h ⊢ <;> omega
    have hH : X.H = StaircaseFiveFamilies.m1H Y := by
      apply Gluing.Profile.ext
      · funext i; have h := congrFun hw.2.2.1 i
        fin_cases i <;> simp [Y,BParameters.H,bProfileH,profile] at h ⊢ <;> omega
      · funext j; have h := congrFun hw.2.2.2 j
        fin_cases j <;> simp [Y,BParameters.H,bProfileH,profile] at h ⊢ <;> omega
    refine ⟨.m1 Y,?_⟩
    intro P h
    rcases h with rfl | rfl | rfl | rfl
    · exact ⟨0,hF⟩
    · exact ⟨1,congrArg Gluing.Profile.rotate hF⟩
    · exact ⟨2,hH⟩
    · exact ⟨3,congrArg Gluing.Profile.rotate hH⟩
  · let Y := StaircaseFiveFamilies.bM2Parameters X.p X.m X.z X.w
      (by have := X.z_pos; omega) (by omega) X.p_gt X.m_gt X.p_ne_m
    have hw := StaircaseFiveFamilies.b_m2_words X.p X.m X.z X.w
      (by have := X.z_pos; omega) (by omega) X.p_gt X.m_gt X.p_ne_m
    have hF : X.F = StaircaseFiveFamilies.m2F Y := by
      apply Gluing.Profile.ext
      · funext i; have h := congrFun hw.1 i
        fin_cases i <;> simp [Y,BParameters.F,bProfileF,profile] at h ⊢ <;> omega
      · funext j; have h := congrFun hw.2.1 j
        fin_cases j <;> simp [Y,BParameters.F,bProfileF,profile] at h ⊢ <;> omega
    have hH : X.H = StaircaseFiveFamilies.m2H Y := by
      apply Gluing.Profile.ext
      · funext i; have h := congrFun hw.2.2.1 i
        fin_cases i <;> simp [Y,BParameters.H,bProfileH,profile] at h ⊢ <;> omega
      · funext j; have h := congrFun hw.2.2.2 j
        fin_cases j <;> simp [Y,BParameters.H,bProfileH,profile] at h ⊢ <;> omega
    refine ⟨.m2 Y,?_⟩
    intro P h
    rcases h with rfl | rfl | rfl | rfl
    · exact ⟨0,hF⟩
    · exact ⟨1,congrArg Gluing.Profile.rotate hF⟩
    · exact ⟨2,hH⟩
    · exact ⟨3,congrArg Gluing.Profile.rotate hH⟩

theorem thick_five_scheme_class (P Q : Gluing.Profile 4)
    (hP : Staircase.Thick P) (hQ : Staircase.Thick Q)
    (hgap : ∀ j, 0 < P.g j) :
    P.toBetaDiagram.schur = Q.toBetaDiagram.schur ↔
      P = Q ∨ P = Q.rotate ∨ ∃ X : Scheme, X.Member P ∧ X.Member Q := by
  rw [thick_five_full_class P Q hP hQ hgap]
  constructor
  · rintro (h | h | ⟨X,hP,hQ⟩ | ⟨X,hP,hQ⟩ | ⟨X,hP,hQ⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨.m3 X,contact_member_scheme false X P hP,
        contact_member_scheme false X Q hQ⟩)
    · exact Or.inr (Or.inr ⟨.m4 X,contact_member_scheme true X P hP,
        contact_member_scheme true X Q hQ⟩)
    · obtain ⟨Y,hY⟩ := b_member_scheme X
      exact Or.inr (Or.inr ⟨Y,hY P hP,hY Q hQ⟩)
  · rintro (h | h | ⟨X,hP',hQ'⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact (thick_five_full_class P Q hP hQ hgap).mp (Scheme.member_schur hP' hQ')

def Scheme.gamma : Scheme → Scheme
  | .m1 X => .m1 (StaircaseFiveFamilies.gammaCommutation X)
  | .m2 X => .m2 (StaircaseFiveFamilies.gammaCommutation X)
  | .m3 X => .m3 (StaircaseFiveFamilies.gammaContact X)
  | .m4 X => .m4 (StaircaseFiveFamilies.gammaContact X)

theorem Scheme.gamma_at (X : Scheme) (i : Fin 4) :
    X.gamma.at i = (X.at i).lift Gluing.rowShiftTwoOne := by
  cases X <;> fin_cases i <;>
    simp [Scheme.gamma,Scheme.at,Scheme.first,Scheme.second,
      StaircaseFiveFamilies.m1_gamma,StaircaseFiveFamilies.m2_gamma,
      StaircaseFiveFamilies.m3_gamma,StaircaseFiveFamilies.m4_gamma,
      ← Gluing.Profile.lift_rotate]

private theorem hasResidue_of_full_schur_eq {n : ℕ} (P Q : Gluing.Profile n)
    (s : Gluing.RowShift) (hP : P.HasResidue s)
    (he : P.toBetaDiagram.schur = Q.toBetaDiagram.schur) : Q.HasResidue s := by
  have he' : P.schur = Q.schur := by simpa only [Gluing.Profile.toBetaDiagram_schur] using he
  have hr := (Gluing.Profile.rows_eq_of_schur_eq he').2
  have hg := Gluing.Profile.gaps_eq_of_schur_eq he'
  constructor
  · intro i
    have hi : Q.r i ∈ P.rowMultiset := by
      rw [hr]
      exact Multiset.mem_map.mpr ⟨i,Finset.mem_univ i,rfl⟩
    obtain ⟨j,_,hj⟩ := Multiset.mem_map.mp hi
    simpa only [← hj] using hP.1 j
  · intro i
    have hi : Q.g i ∈ P.gapMultiset := by
      rw [hg]
      exact Multiset.mem_map.mpr ⟨i,Finset.mem_univ i,rfl⟩
    obtain ⟨j,_,hj⟩ := Multiset.mem_map.mp hi
    simpa only [← hj] using hP.2 j

/-- A genuine Gamma-image member forces the complete parameter congruences
and hence an actual ungamma scheme, including all original zero gaps. -/
theorem Scheme.ungamma_of_member (X : Scheme) (P : Gluing.Profile 4)
    (hP : X.Member (P.lift Gluing.rowShiftTwoOne)) :
    ∃ Y : Scheme, Y.gamma = X := by
  have hres : X.first.HasResidue Gluing.rowShiftTwoOne :=
    hasResidue_of_full_schur_eq (P.lift Gluing.rowShiftTwoOne) X.first _
      (Gluing.Profile.hasResidue_lift _ P)
      (by obtain ⟨i,hi⟩ := hP; rw [hi]; exact X.at_schur i)
  cases X with
  | m1 X =>
    obtain ⟨ha,hb,ht,hd⟩ := StaircaseFiveFamilies.m1_image_parity X hres
    exact ⟨.m1 (StaircaseFiveFamilies.ungammaCommutation X ha hb ht hd),
      congrArg Scheme.m1 (StaircaseFiveFamilies.gamma_ungamma_commutation X ha hb ht hd)⟩
  | m2 X =>
    obtain ⟨ha,hb,ht,hd⟩ := StaircaseFiveFamilies.m2_image_parity X hres
    exact ⟨.m2 (StaircaseFiveFamilies.ungammaCommutation X ha hb ht hd),
      congrArg Scheme.m2 (StaircaseFiveFamilies.gamma_ungamma_commutation X ha hb ht hd)⟩
  | m3 X =>
    obtain ⟨ha,hb,hd⟩ := StaircaseFiveFamilies.m3_image_parity X hres
    exact ⟨.m3 (StaircaseFiveFamilies.ungammaContact X ha hb hd),
      congrArg Scheme.m3 (StaircaseFiveFamilies.gamma_ungamma_contact X ha hb hd)⟩
  | m4 X =>
    obtain ⟨ha,hb,hd⟩ := StaircaseFiveFamilies.m4_image_parity X hres
    exact ⟨.m4 (StaircaseFiveFamilies.ungammaContact X ha hb hd),
      congrArg Scheme.m4 (StaircaseFiveFamilies.gamma_ungamma_contact X ha hb hd)⟩

theorem Scheme.member_ungamma {X : Scheme} {P : Gluing.Profile 4}
    (h : X.gamma.Member (P.lift Gluing.rowShiftTwoOne)) : X.Member P := by
  obtain ⟨i,hi⟩ := h
  rw [X.gamma_at i] at hi
  exact ⟨i,Gluing.Profile.lift_injective _ hi⟩

set_option maxHeartbeats 0 in
/-- Intersecting schemes have the same four actual profiles.  The proof is
an exact comparison of their row and gap words.  It includes the M1/M2
intersection at zero deformation rather than asserting disjoint schemes. -/
theorem Scheme.intersection (X Y : Scheme) (i j : Fin 4)
    (he : X.at i = Y.at j) (k : Fin 4) : Y.Member (X.at k) := by
  have h0 := congrArg (fun P : Gluing.Profile 4 => (P.r 0 : ℤ)) he
  have h1 := congrArg (fun P : Gluing.Profile 4 => (P.r 1 : ℤ)) he
  have h2 := congrArg (fun P : Gluing.Profile 4 => (P.r 2 : ℤ)) he
  have h3 := congrArg (fun P : Gluing.Profile 4 => (P.r 3 : ℤ)) he
  have h4 := congrArg (fun P : Gluing.Profile 4 => (P.r 4 : ℤ)) he
  have hg0 := congrArg (fun P : Gluing.Profile 4 => (P.g 0 : ℤ)) he
  have hg1 := congrArg (fun P : Gluing.Profile 4 => (P.g 1 : ℤ)) he
  have hg2 := congrArg (fun P : Gluing.Profile 4 => (P.g 2 : ℤ)) he
  have hg3 := congrArg (fun P : Gluing.Profile 4 => (P.g 3 : ℤ)) he
  cases X
  all_goals
    rename_i X
    first
      | (have hx0 := X.t_nonneg; have hx1 := X.d_nonneg
         have hx2 := X.a_gt; have hx3 := X.b_gt; have hx4 := X.a_ne_b)
      | (have hx0 := X.d_nonneg; have hx1 := X.a_pos; have hx2 := X.b_gt)
    cases Y
    all_goals
      rename_i Y
      first
        | (have hy0 := Y.t_nonneg; have hy1 := Y.d_nonneg
           have hy2 := Y.a_gt; have hy3 := Y.b_gt; have hy4 := Y.a_ne_b)
        | (have hy0 := Y.d_nonneg; have hy1 := Y.a_pos; have hy2 := Y.b_gt)
      fin_cases i <;> fin_cases j
      all_goals
        simp [Scheme.at,Scheme.first,Scheme.second,
          StaircaseFiveFamilies.m1F,StaircaseFiveFamilies.m1H,
          StaircaseFiveFamilies.m2F,StaircaseFiveFamilies.m2H,
          StaircaseFiveFamilies.m3F,StaircaseFiveFamilies.m3H,
          StaircaseFiveFamilies.m4F,StaircaseFiveFamilies.m4H,
          Gluing.Profile.rotate,StaircaseFiveFamilies.profile] at h0 h1 h2 h3 h4 hg0 hg1 hg2 hg3
        fin_cases k
        all_goals
          first
            | (refine ⟨0,?_⟩; apply Gluing.Profile.ext
               all_goals funext v; fin_cases v <;>
                 simp [Scheme.at,Scheme.first,Scheme.second,
                   StaircaseFiveFamilies.m1F,StaircaseFiveFamilies.m1H,
                   StaircaseFiveFamilies.m2F,StaircaseFiveFamilies.m2H,
                   StaircaseFiveFamilies.m3F,StaircaseFiveFamilies.m3H,
                   StaircaseFiveFamilies.m4F,StaircaseFiveFamilies.m4H,
                   Gluing.Profile.rotate,StaircaseFiveFamilies.profile] <;> omega)
            | (refine ⟨1,?_⟩; apply Gluing.Profile.ext
               all_goals funext v; fin_cases v <;>
                 simp [Scheme.at,Scheme.first,Scheme.second,
                   StaircaseFiveFamilies.m1F,StaircaseFiveFamilies.m1H,
                   StaircaseFiveFamilies.m2F,StaircaseFiveFamilies.m2H,
                   StaircaseFiveFamilies.m3F,StaircaseFiveFamilies.m3H,
                   StaircaseFiveFamilies.m4F,StaircaseFiveFamilies.m4H,
                   Gluing.Profile.rotate,StaircaseFiveFamilies.profile] <;> omega)
            | (refine ⟨2,?_⟩; apply Gluing.Profile.ext
               all_goals funext v; fin_cases v <;>
                 simp [Scheme.at,Scheme.first,Scheme.second,
                   StaircaseFiveFamilies.m1F,StaircaseFiveFamilies.m1H,
                   StaircaseFiveFamilies.m2F,StaircaseFiveFamilies.m2H,
                   StaircaseFiveFamilies.m3F,StaircaseFiveFamilies.m3H,
                   StaircaseFiveFamilies.m4F,StaircaseFiveFamilies.m4H,
                   Gluing.Profile.rotate,StaircaseFiveFamilies.profile] <;> omega)
            | (refine ⟨3,?_⟩; apply Gluing.Profile.ext
               all_goals funext v; fin_cases v <;>
                 simp [Scheme.at,Scheme.first,Scheme.second,
                   StaircaseFiveFamilies.m1F,StaircaseFiveFamilies.m1H,
                   StaircaseFiveFamilies.m2F,StaircaseFiveFamilies.m2H,
                   StaircaseFiveFamilies.m3F,StaircaseFiveFamilies.m3H,
                   StaircaseFiveFamilies.m4F,StaircaseFiveFamilies.m4H,
                   Gluing.Profile.rotate,StaircaseFiveFamilies.profile] <;> omega)

theorem Scheme.member_rotation {X : Scheme} {P : Gluing.Profile 4}
    (hP : X.Member P) : X.Member P.rotate := by
  obtain ⟨i,rfl⟩ := hP
  fin_cases i
  · exact ⟨1,rfl⟩
  · exact ⟨0,by simp [Scheme.at]⟩
  · exact ⟨3,rfl⟩
  · exact ⟨2,by simp [Scheme.at]⟩

theorem Scheme.same_members {X Y : Scheme} {P : Gluing.Profile 4}
    (hX : X.Member P) (hY : Y.Member P) {Q : Gluing.Profile 4}
    (hQ : X.Member Q) : Y.Member Q := by
  obtain ⟨i,hi⟩ := hX
  obtain ⟨j,hj⟩ := hY
  obtain ⟨k,rfl⟩ := hQ
  exact X.intersection Y i j (hi.symm.trans hj) k

/-- A unique numerical gap is specified in the actual ordered gap word. -/
def UniqueGap (P : Gluing.Profile 4) (q : ℕ) (c : Fin 4) : Prop :=
  ∀ j, P.g j = q ↔ j = c

private theorem a1_terminal_unique_member
    (X : StaircaseFiveFamilies.ContactParameters) (P : Gluing.Profile 4) (q : ℕ)
    (hm : ContactMember false P X) (hu : UniqueGap P q 3) :
    P = StaircaseFiveFamilies.m3F X := by
  have h3 := (hu 3).mpr rfl
  have h0 : P.g 0 ≠ q := by intro h; have := (hu 0).mp h; norm_num at this
  have h1 : P.g 1 ≠ q := by intro h; have := (hu 1).mp h; norm_num at this
  simp only [ContactMember,if_false] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · rfl
  all_goals
    simp [StaircaseFiveFamilies.m3F,StaircaseFiveFamilies.m3H,
      StaircaseFiveFamilies.profile,Gluing.Profile.rotate] at h0 h1 h3
    omega

private theorem a1_interior_unique_member
    (X : StaircaseFiveFamilies.ContactParameters) (P : Gluing.Profile 4) (q : ℕ)
    (hm : ContactMember false P X) (hu : UniqueGap P q 1) :
    P = StaircaseFiveFamilies.m3H X := by
  have h1 := (hu 1).mpr rfl
  have h0 : P.g 0 ≠ q := by intro h; have := (hu 0).mp h; norm_num at this
  have h2 : P.g 2 ≠ q := by intro h; have := (hu 2).mp h; norm_num at this
  simp only [ContactMember,if_false] at hm
  rcases hm with rfl | rfl | rfl | rfl
  all_goals first | rfl |
    (simp [StaircaseFiveFamilies.m3F,StaircaseFiveFamilies.m3H,
      StaircaseFiveFamilies.profile,Gluing.Profile.rotate] at h0 h1 h2; omega)

private theorem a2_no_unique_gap (P Q : Gluing.Profile 4) (q : ℕ) (c : Fin 4)
    (hu : UniqueGap P q c) : ¬ ContactRelation true P Q := by
  rintro ⟨X,hm,_⟩
  have h0 := hu 0; have h1 := hu 1
  have h2 := hu 2; have h3 := hu 3
  simp only [ContactMember,if_true] at hm
  rcases hm with rfl | rfl | rfl | rfl
  all_goals
    fin_cases c
    all_goals
      simp [StaircaseFiveFamilies.m4F,StaircaseFiveFamilies.m4H,
        StaircaseFiveFamilies.profile,Gluing.Profile.rotate] at h0 h1 h2 h3
      omega

private theorem b_no_unique_terminal (P Q : Gluing.Profile 4) (q : ℕ)
    (hu : UniqueGap P q 3) : ¬ BRelation P Q := by
  rintro ⟨X,hm,_⟩
  have h3 := (hu 3).mpr rfl
  have h0 : P.g 0 ≠ q := by intro h; have := (hu 0).mp h; norm_num at this
  rcases hm with rfl | rfl | rfl | rfl
  all_goals
    simp [BParameters.F,BParameters.H,bProfileF,bProfileH,
      StaircaseFiveFamilies.profile,Gluing.Profile.rotate] at h0 h3
    omega

/-- `lem:staircase-four-plus-one`: an arbitrary unique numerical seam,
not necessarily the minimum, cannot give a nontrivial terminal/terminal
match after both seams are oriented last. -/
theorem terminal_unique_gap_rigidity (P Q : Gluing.Profile 4)
    (hP : Staircase.Thick P) (hQ : Staircase.Thick Q) (hgap : ∀ j, 0 < P.g j)
    (q : ℕ) (huP : UniqueGap P q 3) (huQ : UniqueGap Q q 3)
    (he : P.toBetaDiagram.schur = Q.toBetaDiagram.schur) : P = Q := by
  rcases (thick_five_full_class P Q hP hQ hgap).mp he with h | h | h | h | h
  · exact h
  · have hq := (huQ 3).mpr rfl
    have hP0 : P.g 0 = q := by simpa [h,Gluing.Profile.rotate] using hq
    have := (huP 0).mp hP0
    norm_num at this
  · obtain ⟨X,hPX,hQX⟩ := h
    exact (a1_terminal_unique_member X P q hPX huP).trans
      (a1_terminal_unique_member X Q q hQX huQ).symm
  · exact False.elim (a2_no_unique_gap P Q q 3 huP h)
  · exact False.elim (b_no_unique_terminal P Q q huP h)

/-- `lem:staircase-seam-crossing`, with the terminal seam last and the
interior seam second.  The other three gaps are not prescribed. -/
theorem seam_crossing_aligned (P Q : Gluing.Profile 4)
    (hP : Staircase.Thick P) (hQ : Staircase.Thick Q) (hgap : ∀ j, 0 < P.g j)
    (q : ℕ) (huP : UniqueGap P q 3) (huQ : UniqueGap Q q 1)
    (he : P.toBetaDiagram.schur = Q.toBetaDiagram.schur) :
    ∃ X : StaircaseFiveFamilies.ContactParameters,
      1 ≤ X.d ∧ (q : ℤ) = X.a+X.d ∧
      P = StaircaseFiveFamilies.m3F X ∧ Q = StaircaseFiveFamilies.m3H X := by
  rcases (thick_five_full_class P Q hP hQ hgap).mp he with h | h | h | h | h
  · have hq := (huP 3).mpr rfl
    rw [h] at hq
    have := (huQ 3).mp hq
    norm_num at this
  · have hq := (huP 3).mpr rfl
    have hQ0 : Q.g 0 = q := by simpa [h,Gluing.Profile.rotate] using hq
    have := (huQ 0).mp hQ0
    norm_num at this
  · obtain ⟨X,hPX,hQX⟩ := h
    have hPX' := a1_terminal_unique_member X P q hPX huP
    have hQX' := a1_interior_unique_member X Q q hQX huQ
    have hd := hgap 0
    have hq := (huP 3).mpr rfl
    have hdn := X.d_nonneg
    have hap := X.a_pos
    rw [hPX'] at hd hq
    simp [StaircaseFiveFamilies.m3F,StaircaseFiveFamilies.profile] at hd hq
    exact ⟨X,by omega,by omega,hPX',hQX'⟩
  · exact False.elim (a2_no_unique_gap P Q q 3 huP h)
  · exact False.elim (b_no_unique_terminal P Q q huP h)

theorem unique_gap_orientation (P : Gluing.Profile 4) (q : ℕ) (c : Fin 4)
    (hu : UniqueGap P q c) (rev : Bool) :
    UniqueGap (profileOrientation P rev) q (if rev then c.rev else c) := by
  cases rev
  · exact hu
  · intro j
    change P.g j.rev = q ↔ j = c.rev
    rw [hu j.rev]
    constructor
    · intro h
      simpa using congrArg Fin.rev h
    · intro h
      simpa using congrArg Fin.rev h

/-- Independent rotations recover the exact A1/M3 representatives whenever
a unique numerical gap changes end/interior status. -/
theorem staircase_seam_crossing (P Q : Gluing.Profile 4)
    (hP : Staircase.Thick P) (hQ : Staircase.Thick Q) (hgap : ∀ j, 0 < P.g j)
    (q : ℕ) (c d : Fin 4) (hc : c = 0 ∨ c = 3) (hd : d = 1 ∨ d = 2)
    (huP : UniqueGap P q c) (huQ : UniqueGap Q q d)
    (he : P.toBetaDiagram.schur = Q.toBetaDiagram.schur) :
    ∃ r s : Bool, ∃ X : StaircaseFiveFamilies.ContactParameters,
      1 ≤ X.d ∧ (q : ℤ) = X.a+X.d ∧
      profileOrientation P r = StaircaseFiveFamilies.m3F X ∧
      profileOrientation Q s = StaircaseFiveFamilies.m3H X := by
  have hnorm : ∃ r s : Bool, UniqueGap (profileOrientation P r) q 3 ∧
      UniqueGap (profileOrientation Q s) q 1 := by
    rcases hc with rfl | rfl
    all_goals rcases hd with rfl | rfl
    · exact ⟨true,false,by simpa using unique_gap_orientation P q 0 huP true,huQ⟩
    · exact ⟨true,true,by simpa using unique_gap_orientation P q 0 huP true,
        by simpa using unique_gap_orientation Q q 2 huQ true⟩
    · exact ⟨false,false,huP,huQ⟩
    · exact ⟨false,true,huP,by simpa using unique_gap_orientation Q q 2 huQ true⟩
  obtain ⟨r,s,hPr,hQs⟩ := hnorm
  have hg : ∀ j, 0 < (profileOrientation P r).g j := by
    intro j
    cases r
    · exact hgap j
    · exact hgap j.rev
  have heo : (profileOrientation P r).toBetaDiagram.schur =
      (profileOrientation Q s).toBetaDiagram.schur := by
    rw [profileOrientation_schur,profileOrientation_schur]
    exact he
  obtain ⟨X,hXd,hq,hPX,hQX⟩ := seam_crossing_aligned _ _
    (profileOrientation_thick P hP r) (profileOrientation_thick Q hQ s)
    hg q hPr hQs heo
  exact ⟨r,s,X,hXd,hq,hPX,hQX⟩

/-- Two terminal occurrences of the same unique gap are rotation-trivial,
with either endpoint allowed independently on each side. -/
theorem staircase_terminal_cuts (P Q : Gluing.Profile 4)
    (hP : Staircase.Thick P) (hQ : Staircase.Thick Q) (hgap : ∀ j, 0 < P.g j)
    (q : ℕ) (c d : Fin 4) (hc : c = 0 ∨ c = 3) (hd : d = 0 ∨ d = 3)
    (huP : UniqueGap P q c) (huQ : UniqueGap Q q d)
    (he : P.toBetaDiagram.schur = Q.toBetaDiagram.schur) : P = Q ∨ P = Q.rotate := by
  have hnorm : ∃ r s : Bool, UniqueGap (profileOrientation P r) q 3 ∧
      UniqueGap (profileOrientation Q s) q 3 := by
    rcases hc with rfl | rfl
    all_goals rcases hd with rfl | rfl
    · exact ⟨true,true,by simpa using unique_gap_orientation P q 0 huP true,
        by simpa using unique_gap_orientation Q q 0 huQ true⟩
    · exact ⟨true,false,by simpa using unique_gap_orientation P q 0 huP true,huQ⟩
    · exact ⟨false,true,huP,by simpa using unique_gap_orientation Q q 0 huQ true⟩
    · exact ⟨false,false,huP,huQ⟩
  obtain ⟨r,s,hPr,hQs⟩ := hnorm
  have hg : ∀ j, 0 < (profileOrientation P r).g j := by
    intro j
    cases r
    · exact hgap j
    · exact hgap j.rev
  have heo : (profileOrientation P r).toBetaDiagram.schur =
      (profileOrientation Q s).toBetaDiagram.schur := by
    rw [profileOrientation_schur,profileOrientation_schur]
    exact he
  exact equality_unorient (terminal_unique_gap_rigidity _ _
    (profileOrientation_thick P hP r) (profileOrientation_thick Q hQ s)
    hg q hPr hQs heo)

/-- The last-two exchange is the same actual row-word operation viewed
from the other endpoint; no condition on numerical label coincidences is used. -/
def LastTwoExchanged {n : ℕ} (P Q : Gluing.Profile (n+2)) : Prop :=
  FirstTwoExchanged P.rotate Q.rotate

theorem adjacent_last_endpoint_exchange {n : ℕ} (P Q : Gluing.Profile (n+2))
    (hP : Staircase.Thick P) (hQ : Staircase.Thick Q)
    (hswap : LastTwoExchanged P Q)
    (he : P.toBetaDiagram.schur = Q.toBetaDiagram.schur) :
    P.r (Fin.last (n+2)) = P.r (Fin.castSucc (Fin.last (n+1))) := by
  have heo : P.rotate.toBetaDiagram.schur = Q.rotate.toBetaDiagram.schur := by
    simpa only [Gluing.Profile.toBetaDiagram_schur,Gluing.Profile.schur_rotate] using he
  have h := adjacent_endpoint_exchange P.rotate Q.rotate
    (thick_rotate hP) (thick_rotate hQ) hswap heo
  have h0 : (Fin.rev (0 : Fin (n+3))) = Fin.last (n+2) := by apply Fin.ext; simp
  have h1 : (Fin.rev (1 : Fin (n+3))) = Fin.castSucc (Fin.last (n+1)) := by
    apply Fin.ext
    simp [Fin.rev]
  simpa only [Gluing.Profile.rotate,h0,h1] using h

end SkewJacobiNegative.StaircaseFivePlacements
