/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Finsupp.Encodable
import SkewMarkedFactor.Gluing.RowInvariants

/-!
# Primitive coefficient normalization

The coefficient operation in «Recovering the factors» (`sec:extraction`, `lem:primitive`)
uses only the finite support, rational coefficients, denominator LCM, and integer coefficient GCD.
Dividing first by
the coefficient at a least-square-weight monomial fixes the sign and removes rational scaling;
the subsequent denominator clearing and content division produce the primitive integer form.
No diagram or Schur-function recognition enters the definition.
-/

namespace SkewMarkedFactor

open MvPolynomial
open Gluing

/-- Finite exponent vectors indexing monomials in the positive-index generators. -/
abbrev MonomialIndex := ℕ+ →₀ ℕ

/-- All coefficients belong to the image of the integers in the rationals. -/
def IntegralPolynomial (f : Lambda) : Prop :=
  ∀ m, ∃ z : ℤ, f.coeff m = (z : ℚ)

@[instance_reducible]
private def monomialCodeOrder : LinearOrder MonomialIndex :=
  LinearOrder.lift' Encodable.encode Encodable.encode_injective

/-- The least-square-weight support element, breaking ties by the finite exponent-vector code. -/
noncomputable def leastMonomial (s : Finset MonomialIndex) : MonomialIndex := by
  classical
  letI : LinearOrder MonomialIndex := monomialCodeOrder
  exact if hs : s.Nonempty then
    let t := s.filter fun m => sqWeight m = (s.image sqWeight).min' (hs.image sqWeight)
    have ht : t.Nonempty := by
      obtain ⟨m, hm, he⟩ := Finset.mem_image.mp
        (Finset.min'_mem (s.image sqWeight) (hs.image sqWeight))
      exact ⟨m, Finset.mem_filter.mpr ⟨hm, he⟩⟩
    t.min' ht
  else 0

theorem least_monomial_spec {s : Finset MonomialIndex} (hs : s.Nonempty) :
    leastMonomial s ∈ s ∧ ∀ n ∈ s, sqWeight (leastMonomial s) ≤ sqWeight n := by
  classical
  let : LinearOrder MonomialIndex := monomialCodeOrder
  let t := s.filter fun m => sqWeight m = (s.image sqWeight).min' (hs.image sqWeight)
  have ht : t.Nonempty := by
    obtain ⟨m, hm, he⟩ := Finset.mem_image.mp
      (Finset.min'_mem (s.image sqWeight) (hs.image sqWeight))
    exact ⟨m, Finset.mem_filter.mpr ⟨hm, he⟩⟩
  have hc := Finset.mem_filter.mp (Finset.min'_mem t ht)
  have he : leastMonomial s = t.min' ht := by
    simp only [leastMonomial, dite_eq_left hs]
    rfl
  rw [he]
  refine ⟨hc.1, fun n hn => ?_⟩
  rw [hc.2]
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨n, hn, rfl⟩)

theorem least_monomial_eq {f : Lambda} {m : MonomialIndex} (hc : f.coeff m ≠ 0)
    (hm : ∀ n, f.coeff n ≠ 0 → n ≠ m → sqWeight m < sqWeight n) :
    leastMonomial f.support = m := by
  classical
  have hmem : m ∈ f.support := mem_support_iff.mpr hc
  obtain ⟨ha, hmin⟩ := least_monomial_spec ⟨m, hmem⟩
  by_contra hne
  have := hm _ (mem_support_iff.mp ha) hne
  have := hmin m hmem
  omega

/-- Ratios to the selected coefficient; its selected coefficient is positive, namely one. -/
noncomputable def coefficientRatios (f : Lambda) : Lambda :=
  (f.coeff (leastMonomial f.support))⁻¹ • f

/-- The LCM of the reduced denominators of the actual nonzero coefficients. -/
noncomputable def denominatorLcm (f : Lambda) : ℕ := by
  classical
  exact f.support.lcm fun m => (f.coeff m).den

/-- The genuine integer polynomial obtained by denominator clearing. -/
noncomputable def clearDenominators (f : Lambda) : Lambda := (denominatorLcm f : ℚ) • f

/-- The nonnegative GCD of the integer coefficients after denominator clearing. -/
noncomputable def coefficientGcd (f : Lambda) : ℕ := by
  classical
  exact f.support.gcd fun m => ((clearDenominators f).coeff m).num.natAbs

/-- Primitive integer content normalization, with least-square-weight coefficient positive.
The zero polynomial maps to zero. -/
noncomputable def primitive (f : Lambda) : Lambda :=
  (coefficientGcd (coefficientRatios f) : ℚ)⁻¹ •
    clearDenominators (coefficientRatios f)

theorem denominator_lcm_ne_zero (f : Lambda) : denominatorLcm f ≠ 0 := by
  classical
  apply Finset.lcm_ne_zero_iff.mpr
  intro m _
  exact Nat.ne_of_gt (f.coeff m).pos

theorem denominator_dvd_lcm (f : Lambda) (m : MonomialIndex) :
    (f.coeff m).den ∣ denominatorLcm f := by
  classical
  by_cases hm : m ∈ f.support
  · exact Finset.dvd_lcm hm
  · have hc : f.coeff m = 0 := notMem_support_iff.mp hm
    simp [hc]

theorem clear_denominators_integral (f : Lambda) : IntegralPolynomial (clearDenominators f) := by
  intro m
  obtain ⟨k, hk⟩ := denominator_dvd_lcm f m
  refine ⟨(f.coeff m).num * (k : ℤ), ?_⟩
  have hd : ((f.coeff m).den : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (f.coeff m).pos
  have hq := (div_eq_iff hd).mp (Rat.num_div_den (f.coeff m))
  rw [clearDenominators, coeff_smul, smul_eq_mul, hk, Nat.cast_mul]
  push_cast
  calc
    ((f.coeff m).den : ℚ) * (k : ℚ) * f.coeff m =
        (f.coeff m * (f.coeff m).den) * (k : ℚ) := by ring
    _ = ((f.coeff m).num : ℚ) * (k : ℚ) := by rw [← hq]

theorem integral_coefficient_num {f : Lambda} (hf : IntegralPolynomial f) (m : MonomialIndex) :
    ((f.coeff m).num : ℚ) = f.coeff m := by
  obtain ⟨z, hz⟩ := hf m
  simp [hz]

theorem denominator_lcm_of_integral {f : Lambda} (hf : IntegralPolynomial f) :
    denominatorLcm f = 1 := by
  classical
  apply Nat.dvd_one.mp
  apply Finset.lcm_dvd
  intro m _
  obtain ⟨z, hz⟩ := hf m
  simp [hz]

theorem clear_denominators_of_integral {f : Lambda} (hf : IntegralPolynomial f) :
    clearDenominators f = f := by
  simp [clearDenominators, denominator_lcm_of_integral hf]

theorem coefficient_gcd_dvd (f : Lambda) (m : MonomialIndex) :
    coefficientGcd f ∣ ((clearDenominators f).coeff m).num.natAbs := by
  classical
  by_cases hm : m ∈ f.support
  · exact Finset.gcd_dvd hm
  · have hc : f.coeff m = 0 := notMem_support_iff.mp hm
    simp [clearDenominators, hc]

theorem primitive_integral (f : Lambda) : IntegralPolynomial (primitive f) := by
  classical
  let r := coefficientRatios f
  have hi := clear_denominators_integral r
  intro m
  obtain ⟨k, hk⟩ : (coefficientGcd r : ℤ) ∣ ((clearDenominators r).coeff m).num := by
    exact Int.natCast_dvd.mpr (coefficient_gcd_dvd r m)
  by_cases hg : coefficientGcd r = 0
  · refine ⟨0, ?_⟩
    simp [primitive, r, hg]
  · refine ⟨k, ?_⟩
    change ((coefficientGcd r : ℚ)⁻¹ • clearDenominators r).coeff m = _
    rw [coeff_smul, smul_eq_mul, ← integral_coefficient_num hi m, hk]
    push_cast
    have hgq : (coefficientGcd r : ℚ) ≠ 0 := by exact_mod_cast hg
    simp [hgq]

theorem coefficient_ratios_smul (f : Lambda) (q : ℚ) (hq : q ≠ 0) :
    coefficientRatios (q • f) = coefficientRatios f := by
  rw [coefficientRatios, support_smul_eq hq, coeff_smul, smul_eq_mul,
    mul_inv_rev, smul_smul]
  simp [coefficientRatios, mul_comm, hq]

/-- Primitive normalization is invariant under every nonzero rational scaling. -/
theorem primitive_smul (f : Lambda) (q : ℚ) (hq : q ≠ 0) :
    primitive (q • f) = primitive f := by
  simp only [primitive, coefficient_ratios_smul f q hq]

@[simp] theorem primitive_zero : primitive 0 = 0 := by
  simp [primitive, coefficientRatios, clearDenominators]

theorem coefficient_ratios_selected_coeff {f : Lambda} (hf : f ≠ 0) :
    (coefficientRatios f).coeff (leastMonomial f.support) = 1 := by
  have hmem := (least_monomial_spec (support_nonempty.mpr hf)).1
  have hc := mem_support_iff.mp hmem
  simp [coefficientRatios, smul_eq_mul, hc]

theorem coefficient_ratios_ne_zero {f : Lambda} (hf : f ≠ 0) :
    coefficientRatios f ≠ 0 := by
  intro h
  have hc := coefficient_ratios_selected_coeff hf
  simp [h] at hc

theorem coefficient_gcd_ne_zero {f : Lambda} (hf : f ≠ 0) :
    coefficientGcd f ≠ 0 := by
  classical
  obtain ⟨m, hm⟩ := exists_coeff_ne_zero hf
  have hmem : m ∈ f.support := mem_support_iff.mpr hm
  have hd : (denominatorLcm f : ℚ) ≠ 0 := by
    exact_mod_cast denominator_lcm_ne_zero f
  have hc : (clearDenominators f).coeff m ≠ 0 := by
    simpa [clearDenominators, coeff_smul, smul_eq_mul] using mul_ne_zero hd hm
  have hn : ((clearDenominators f).coeff m).num.natAbs ≠ 0 := by
    intro hn
    have hnum : ((clearDenominators f).coeff m).num = 0 := Int.natAbs_eq_zero.mp hn
    have he := integral_coefficient_num (clear_denominators_integral f) m
    exact hc (by simpa [hnum] using he.symm)
  intro hg
  have hz := (Finset.gcd_eq_zero_iff.mp hg) m hmem
  exact hn hz

/-- Content division really produces coefficient GCD one, not merely an integral rescaling. -/
theorem primitive_coefficient_gcd_one {f : Lambda} (hf : f ≠ 0) :
    (primitive f).support.gcd (fun m => ((primitive f).coeff m).num.natAbs) = 1 := by
  classical
  let r := coefficientRatios f
  have hr : r ≠ 0 := coefficient_ratios_ne_zero hf
  have hg := coefficient_gcd_ne_zero hr
  have hgq : (coefficientGcd r : ℚ) ≠ 0 := by exact_mod_cast hg
  have hdq : (denominatorLcm r : ℚ) ≠ 0 := by
    exact_mod_cast denominator_lcm_ne_zero r
  have hs : (primitive f).support = r.support := by
    change ((coefficientGcd r : ℚ)⁻¹ • ((denominatorLcm r : ℚ) • r)).support = _
    rw [support_smul_eq (inv_ne_zero hgq), support_smul_eq hdq]
  have he : clearDenominators r = (coefficientGcd r : ℚ) • primitive f := by
    change clearDenominators r = (coefficientGcd r : ℚ) •
      ((coefficientGcd r : ℚ)⁻¹ • clearDenominators r)
    simp [smul_smul, hgq]
  have hnums : ∀ m, ((clearDenominators r).coeff m).num =
      (coefficientGcd r : ℤ) * ((primitive f).coeff m).num := by
    intro m
    apply Int.cast_injective (α := ℚ)
    push_cast
    rw [integral_coefficient_num (clear_denominators_integral r),
      integral_coefficient_num (primitive_integral f), he, coeff_smul, smul_eq_mul]
  obtain ⟨m, hm⟩ := exists_coeff_ne_zero hr
  have hmem : m ∈ r.support := mem_support_iff.mpr hm
  have hcleared : (clearDenominators r).coeff m ≠ 0 := by
    simpa [clearDenominators, coeff_smul, smul_eq_mul] using mul_ne_zero hdq hm
  have hn : ((clearDenominators r).coeff m).num.natAbs ≠ 0 := by
    intro hn
    have hnum := Int.natAbs_eq_zero.mp hn
    exact hcleared (by
      simpa [hnum] using (integral_coefficient_num (clear_denominators_integral r) m).symm)
  rw [hs]
  apply Finset.extract_gcd' (fun m => ((clearDenominators r).coeff m).num.natAbs)
    (fun m => ((primitive f).coeff m).num.natAbs) ⟨m, hmem, hn⟩
  intro n _
  rw [hnums, Int.natAbs_mul, Int.natAbs_natCast]
  rfl

/-- The sign is fixed by the least-square-weight coefficient,
and that coefficient is positive. -/
theorem primitive_selected_coeff_pos {f : Lambda} (hf : f ≠ 0) :
    0 < (primitive f).coeff (leastMonomial f.support) := by
  have hg : 0 < coefficientGcd (coefficientRatios f) :=
    Nat.pos_of_ne_zero (coefficient_gcd_ne_zero (coefficient_ratios_ne_zero hf))
  have hd : 0 < denominatorLcm (coefficientRatios f) :=
    Nat.pos_of_ne_zero (denominator_lcm_ne_zero _)
  rw [primitive, coeff_smul, clearDenominators, coeff_smul, smul_eq_mul,
    smul_eq_mul, coefficient_ratios_selected_coeff hf, mul_one]
  exact mul_pos (inv_pos.mpr (by exact_mod_cast hg)) (by exact_mod_cast hd)

theorem primitive_eq_smul (f : Lambda) :
    primitive f =
      ((coefficientGcd (coefficientRatios f) : ℚ)⁻¹ *
        (denominatorLcm (coefficientRatios f) : ℚ) *
        (f.coeff (leastMonomial f.support))⁻¹) • f := by
  simp only [primitive, clearDenominators, coefficientRatios, smul_smul, mul_assoc]

theorem primitive_support {f : Lambda} (hf : f ≠ 0) :
    (primitive f).support = f.support := by
  have ha : f.coeff (leastMonomial f.support) ≠ 0 :=
    mem_support_iff.mp (least_monomial_spec (support_nonempty.mpr hf)).1
  have hg : (coefficientGcd (coefficientRatios f) : ℚ) ≠ 0 := by
    exact_mod_cast coefficient_gcd_ne_zero (coefficient_ratios_ne_zero hf)
  have hd : (denominatorLcm (coefficientRatios f) : ℚ) ≠ 0 := by
    exact_mod_cast denominator_lcm_ne_zero (coefficientRatios f)
  rw [primitive_eq_smul, support_smul_eq
    (mul_ne_zero (mul_ne_zero (inv_ne_zero hg) hd) (inv_ne_zero ha))]

/-- A coefficient-one integral polynomial with a unique least-square-weight monomial is already
in primitive normal form. -/
theorem primitive_of_coefficient_one {f : Lambda} (hf : IntegralPolynomial f)
    {m : MonomialIndex} (hc : f.coeff m = 1)
    (hm : ∀ n, f.coeff n ≠ 0 → n ≠ m → sqWeight m < sqWeight n) :
    primitive f = f := by
  classical
  have hcn : f.coeff m ≠ 0 := by rw [hc]; exact one_ne_zero
  have hr : coefficientRatios f = f := by
    simp [coefficientRatios, least_monomial_eq hcn hm, hc]
  have hg : coefficientGcd f = 1 := by
    apply Nat.dvd_one.mp
    have hd := coefficient_gcd_dvd f m
    simpa [clear_denominators_of_integral hf, hc] using hd
  simp [primitive, hr, hg, clear_denominators_of_integral hf]

/-- The public coefficient/content API: no geometry or Schur recognition is assumed. -/
theorem primitive_smul_of_coefficient_one {f : Lambda} (hf : IntegralPolynomial f)
    {m : MonomialIndex} (hc : f.coeff m = 1)
    (hm : ∀ n, f.coeff n ≠ 0 → n ≠ m → sqWeight m < sqWeight n)
    (q : ℚ) (hq : q ≠ 0) : primitive (q • f) = f := by
  rw [primitive_smul f q hq]
  exact primitive_of_coefficient_one hf hc hm

end SkewMarkedFactor
