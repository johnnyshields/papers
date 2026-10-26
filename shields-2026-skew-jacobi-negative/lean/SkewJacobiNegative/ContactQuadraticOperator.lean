/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.CompleteAlgebra
import Mathlib.Data.Finset.Max
import Mathlib.Data.Int.Interval

/-!
# The contact-blind quadratic operator

The actual complete-generator polynomial and the strict support boundary in
`lem:staircase-quadratic-injectivity` of `shields-2026-skew-jacobi-negative.tex`.
The contact index is allowed in the support.  The reflection equations are
consequences of polynomial coefficients, not additional hypotheses.
-/

noncomputable section
namespace SkewJacobiNegative.ContactQuadraticOperator
open scoped BigOperators

/-- The full polynomial, summed over the support of a rational measure. -/
def quadratic (μ : ℤ →₀ ℚ) (N : ℤ) : CompleteRing :=
  ∑ s ∈ μ.support, MvPolynomial.C (μ s) * (complete s * complete (N - s))

/-- The operator whose kernel is trivial below the strict support boundary. -/
def contactOperator (μ : ℤ →₀ ℚ) (e q K : ℤ) : CompleteRing :=
  complete e * quadratic μ K - complete q * quadratic μ (K + e - q)

/-- Interval form used to extract coefficients of the support sum. -/
def returnQuadratic (c : ℤ → ℚ) (b a : ℤ) : CompleteRing :=
  ∑ z ∈ Finset.Ioo b a, c z • (complete (a - z) * complete (z - b))

/-- Equality of quadratic exponents is precisely equality of unordered pairs. -/
theorem pairExponent_eq_iff {α : Type*} (a b c d : α) :
    Finsupp.single a 1 + Finsupp.single b 1 =
      (Finsupp.single c 1 + Finsupp.single d 1 : α →₀ ℕ) ↔
      (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  classical
  constructor
  · intro h
    by_cases hac : a = c
    · subst c
      have he := add_left_cancel h
      have hb := congrArg (fun f : α →₀ ℕ => f b) he
      by_cases hbd : b = d
      · exact Or.inl ⟨rfl, hbd⟩
      · simp [hbd] at hb
    · by_cases had : a = d
      · subst d
        rw [add_comm (Finsupp.single c 1)] at h
        have he := add_left_cancel h
        have hb := congrArg (fun f : α →₀ ℕ => f b) he
        by_cases hbc : b = c
        · exact Or.inr ⟨rfl, hbc⟩
        · simp [hbc] at hb
      · have ha := congrArg (fun f : α →₀ ℕ => f a) h
        have hca : c ≠ a := Ne.symm hac
        have hda : d ≠ a := Ne.symm had
        by_cases hab : a = b
        · subst b
          simp [hca, hda] at ha
        · simp [hca, hda, Ne.symm hab] at ha
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact add_comm _ _

/-- The exponent vector of a positive pair. -/
def returnExponent (b a z : ℤ) (hz : b < z ∧ z < a) : ℕ+ →₀ ℕ :=
  Finsupp.single ⟨(a - z).toNat, by omega⟩ 1 +
    Finsupp.single ⟨(z - b).toNat, by omega⟩ 1

/-- The reflected pair is the only possible monomial collision. -/
theorem returnExponent_eq_iff (b a z w : ℤ)
    (hz : b < z ∧ z < a) (hw : b < w ∧ w < a) :
    returnExponent b a z hz = returnExponent b a w hw ↔
      w = z ∨ w = a + b - z := by
  let az : ℕ+ := ⟨(a - z).toNat, by omega⟩
  let bz : ℕ+ := ⟨(z - b).toNat, by omega⟩
  let aw : ℕ+ := ⟨(a - w).toNat, by omega⟩
  let bw : ℕ+ := ⟨(w - b).toNat, by omega⟩
  change (Finsupp.single az 1 + Finsupp.single bz 1 =
      (Finsupp.single aw 1 + Finsupp.single bw 1 : ℕ+ →₀ ℕ)) ↔ _
  rw [pairExponent_eq_iff az bz aw bw]
  constructor
  · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    · have hh := congrArg (fun j : ℕ+ => (j : ℕ)) h₁
      change (a - z).toNat = (a - w).toNat at hh
      left
      omega
    · have hh := congrArg (fun j : ℕ+ => (j : ℕ)) h₁
      change (a - z).toNat = (w - b).toNat at hh
      right
      omega
  · rintro (rfl | rfl)
    · exact Or.inl ⟨rfl, rfl⟩
    · right
      constructor
      · apply Subtype.ext
        change (a - z).toNat = (a + b - z - b).toNat
        congr 1
        ring
      · apply Subtype.ext
        change (z - b).toNat = (a - (a + b - z)).toNat
        congr 1
        ring

/-- A midpoint contributes once; a distinct reflected pair contributes twice. -/
theorem returnQuadratic_coeff (c : ℤ → ℚ) (b a z : ℤ)
    (hz : b < z ∧ z < a) :
    (returnQuadratic c b a).coeff (returnExponent b a z hz) =
      if 2 * z = a + b then c z else c z + c (a + b - z) := by
  classical
  have hr : a + b - z ∈ Finset.Ioo b a := by simp; omega
  have hz' : z ∈ Finset.Ioo b a := by simpa using hz
  have term (w : ℤ) (hw : w ∈ Finset.Ioo b a) :
      (c w • (complete (a - w) * complete (w - b))).coeff
          (returnExponent b a z hz) =
        if w = z ∨ w = a + b - z then c w else 0 := by
    have hw' := Finset.mem_Ioo.mp hw
    have hm : c w • (complete (a - w) * complete (w - b)) =
        MvPolynomial.monomial (returnExponent b a w hw') (c w) := by
      rw [complete_of_pos (by omega), complete_of_pos (by omega)]
      let aw : ℕ+ := ⟨(a - w).toNat, by omega⟩
      let bw : ℕ+ := ⟨(w - b).toNat, by omega⟩
      change c w •
        ((MvPolynomial.monomial (Finsupp.single aw 1) 1 : CompleteRing) *
          MvPolynomial.monomial (Finsupp.single bw 1) 1) = _
      rw [MvPolynomial.monomial_mul_monomial, MvPolynomial.smul_monomial]
      simp only [smul_eq_mul, mul_one]
      rfl
    rw [hm, MvPolynomial.coeff_monomial]
    have he : returnExponent b a w hw' = returnExponent b a z hz ↔
        w = z ∨ w = a + b - z :=
      eq_comm.trans (returnExponent_eq_iff b a z w hz hw')
    simp only [he]
  rw [returnQuadratic, MvPolynomial.coeff_sum]
  simp_rw [Finset.sum_congr rfl (fun w hw => term w hw)]
  by_cases hmid : 2 * z = a + b
  · have he : a + b - z = z := by omega
    simp [hmid, he, hz']
  · have he : z ≠ a + b - z := by omega
    have hs : (∑ w ∈ Finset.Ioo b a,
        if w = z ∨ w = a + b - z then c w else 0) =
        c z + c (a + b - z) := by
      simp_rw [show ∀ w : ℤ, (if w = z ∨ w = a + b - z then c w else 0) =
        (if w = z then c z else 0) +
          (if w = a + b - z then c (a + b - z) else 0) by
            intro w; by_cases h₁ : w = z <;> by_cases h₂ : w = a + b - z <;>
              simp_all]
      simp [Finset.sum_add_distrib, hz', hr]
    simpa [hmid] using hs

/-- Replacing the support sum by an interval sum introduces only zero terms. -/
theorem quadratic_eq_returnQuadratic (μ : ℤ →₀ ℚ) (N : ℤ)
    (hμ : ∀ s ∈ μ.support, 0 < s ∧ s < N) :
    quadratic μ N = returnQuadratic μ 0 N := by
  classical
  unfold quadratic returnQuadratic
  have hsub : μ.support ⊆ Finset.Ioo 0 N := by
    intro s hs
    exact Finset.mem_Ioo.mpr (hμ s hs)
  calc
    (∑ s ∈ μ.support, MvPolynomial.C (μ s) * (complete s * complete (N - s))) =
        ∑ s ∈ Finset.Ioo 0 N,
          MvPolynomial.C (μ s) * (complete s * complete (N - s)) := by
      apply Finset.sum_subset hsub
      intro s _ hs
      have hz : μ s = 0 := Finsupp.notMem_support_iff.mp hs
      simp [hz]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _
      simp only [sub_zero, MvPolynomial.smul_eq_C_mul]
      rw [mul_comm (complete s)]

/-- A support condition supplies the zero extension at every other integer. -/
theorem measure_eq_zero_outside (μ : ℤ →₀ ℚ) (B s : ℤ)
    (hμ : ∀ t ∈ μ.support, 0 < t ∧ t < B)
    (hs : ¬ (0 < s ∧ s < B)) : μ s = 0 := by
  apply Finsupp.notMem_support_iff.mp
  intro hm
  exact hs (hμ s hm)

/-- Erase just the contact generator, keeping the full polynomial alphabet. -/
def eraseContact (q : ℤ) : CompleteRing →+* CompleteRing :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun i : ℕ+ => if (i.val : ℤ) = q then 0 else MvPolynomial.X i)

@[simp]
theorem eraseContact_C (q : ℤ) (c : ℚ) :
    eraseContact q (MvPolynomial.C c) = MvPolynomial.C c := by
  simp [eraseContact]

set_option backward.isDefEq.respectTransparency false in
theorem eraseContact_complete (q s : ℤ) (hs : 0 < s) :
    eraseContact q (complete s) = if s = q then 0 else complete s := by
  let v : ℕ+ := ⟨s.toNat, by omega⟩
  have hX : complete s = (MvPolynomial.X v : CompleteRing) := complete_of_pos hs
  rw [hX]
  change MvPolynomial.eval₂Hom (MvPolynomial.C : ℚ →+* CompleteRing)
      (fun i : ℕ+ => if (i.val : ℤ) = q then 0 else MvPolynomial.X i)
      (MvPolynomial.X v : CompleteRing) =
    if s = q then 0 else (MvPolynomial.X v : CompleteRing)
  rw [MvPolynomial.eval₂Hom_X']
  change (if (s.toNat : ℤ) = q then (0 : CompleteRing) else MvPolynomial.X v) =
    if s = q then 0 else MvPolynomial.X v
  rw [Int.toNat_of_nonneg hs.le]

/-- The first erasure retains exactly the possibly nonzero contact summand. -/
theorem quadratic_eq_erasure_add_contact (μ : ℤ →₀ ℚ) (q K : ℤ)
    (hq : 0 < q) (hK : q < K)
    (hμ : ∀ s ∈ μ.support, 0 < s ∧ s < K - q) :
    quadratic μ K = eraseContact q (quadratic μ K) +
      MvPolynomial.C (μ q) * (complete q * complete (K - q)) := by
  classical
  have hI : ∀ s ∈ μ.support, 0 < s ∧ s < K := by
    intro s hs
    have := hμ s hs
    constructor <;> omega
  rw [quadratic_eq_returnQuadratic μ K hI]
  have hqI : q ∈ Finset.Ioo 0 K := Finset.mem_Ioo.mpr ⟨hq, hK⟩
  have hterm (s : ℤ) (hs : s ∈ Finset.Ioo 0 K) :
      μ s • (complete (K - s) * complete s) =
        eraseContact q (μ s • (complete (K - s) * complete s)) +
          if s = q then μ q • (complete (K - q) * complete q) else 0 := by
    have hs' := Finset.mem_Ioo.mp hs
    by_cases hsq : s = q
    · subst s
      simp [MvPolynomial.smul_eq_C_mul, eraseContact_complete q q hq,
        eraseContact_complete q (K - q) (by omega)]
    · by_cases hrs : K - s = q
      · have hz : μ s = 0 := measure_eq_zero_outside μ (K - q) s hμ (by omega)
        simp [hz, hsq]
      · simp [MvPolynomial.smul_eq_C_mul, eraseContact_complete q s hs'.1,
          eraseContact_complete q (K - s) (by omega), hsq, hrs]
  have hh := Finset.sum_congr rfl hterm
  rw [Finset.sum_add_distrib] at hh
  simpa [returnQuadratic, map_sum, hqI, MvPolynomial.smul_eq_C_mul,
    mul_comm (complete (K - q))] using hh

/-- Zero quadratics give the actual global reflection equations, including midpoints. -/
theorem quadratic_zero_reflection (μ : ℤ →₀ ℚ) (N : ℤ)
    (hμ : ∀ s ∈ μ.support, 0 < s ∧ s < N)
    (hH : quadratic μ N = 0) : ∀ s : ℤ, μ s + μ (N - s) = 0 := by
  intro s
  by_cases hs : 0 < s ∧ s < N
  · have hc := returnQuadratic_coeff μ 0 N s hs
    rw [← quadratic_eq_returnQuadratic μ N hμ, hH] at hc
    by_cases hm : 2 * s = N
    · have hr : N - s = s := by omega
      have hz : μ s = 0 := by simpa [hm] using hc.symm
      simp [hr, hz]
    · simpa [hm] using hc.symm
  · have hz := measure_eq_zero_outside μ N s hμ hs
    have hr := measure_eq_zero_outside μ N (N - s) hμ (by omega)
    simp [hz, hr]

/-- A finitely supported measure cannot have a nonzero positive period. -/
theorem periodic_finsupp_eq_zero (μ : ℤ →₀ ℚ) (η : ℤ) (hη : 0 < η)
    (hper : ∀ s : ℤ, μ (s + η) = μ s) : μ = 0 := by
  classical
  by_contra hn
  have hne : μ.support.Nonempty := by
    by_contra he
    have hempty : μ.support = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    apply hn
    ext s
    have hs : s ∉ μ.support := by rw [hempty]; simp
    simpa using Finsupp.notMem_support_iff.mp hs
  let m := μ.support.max' hne
  have hm : m ∈ μ.support := Finset.max'_mem μ.support hne
  have hmv : μ m ≠ 0 := Finsupp.mem_support_iff.mp hm
  have ht : m + η ∈ μ.support := Finsupp.mem_support_iff.mpr (by
    rw [hper m]
    exact hmv)
  have hle : m + η ≤ m := Finset.le_max' μ.support (m + η) ht
  omega

/-- The second quadratic coefficient kills the contact summand rather than
assuming that the first erasure killed it. -/
theorem contact_coefficient_eq_zero (μ : ℤ →₀ ℚ) (e q K : ℤ)
    (hq : 0 < q) (heq : q < e) (hK : q < K)
    (hμ : ∀ s ∈ μ.support, 0 < s ∧ s < K - q)
    (hH : quadratic μ (K + e - q) =
      MvPolynomial.C (μ q) * (complete e * complete (K - q))) : μ q = 0 := by
  classical
  by_contra hn
  have hqS : q ∈ μ.support := Finsupp.mem_support_iff.mpr hn
  have hqb := (hμ q hqS).2
  have hI : ∀ s ∈ μ.support, 0 < s ∧ s < K + e - q := by
    intro s hs
    have := hμ s hs
    constructor <;> omega
  have hpair : 0 < q ∧ q < K + e - q := by constructor <;> omega
  have hc := returnQuadratic_coeff μ 0 (K + e - q) q hpair
  rw [← quadratic_eq_returnQuadratic μ (K + e - q) hI, hH] at hc
  have hz : μ (K + e - q - q) = 0 :=
    measure_eq_zero_outside μ (K - q) (K + e - q - q) hμ (by omega)
  have hmid : ¬ 2 * q = K + e - q := by omega
  let a : ℕ+ := ⟨e.toNat, by omega⟩
  let b : ℕ+ := ⟨(K - q).toNat, by omega⟩
  let c : ℕ+ := ⟨(K + e - q - q).toNat, by omega⟩
  let d : ℕ+ := ⟨q.toNat, by omega⟩
  have had : a ≠ d := by
    intro h
    have hv := congrArg (fun i : ℕ+ => i.val) h
    change e.toNat = q.toNat at hv
    omega
  have hbd : b ≠ d := by
    intro h
    have hv := congrArg (fun i : ℕ+ => i.val) h
    change (K - q).toNat = q.toNat at hv
    omega
  have hex : Finsupp.single a 1 + Finsupp.single b 1 ≠
      (Finsupp.single c 1 + Finsupp.single d 1 : ℕ+ →₀ ℕ) := by
    intro h
    rcases (pairExponent_eq_iff a b c d).mp h with h | h
    · exact hbd h.2
    · exact had h.1
  have hmon : MvPolynomial.C (μ q) * (complete e * complete (K - q)) =
      MvPolynomial.monomial (Finsupp.single a 1 + Finsupp.single b 1) (μ q) := by
    rw [complete_of_pos (by omega), complete_of_pos (by omega)]
    change MvPolynomial.C (μ q) *
      ((MvPolynomial.monomial (Finsupp.single a 1) 1 : CompleteRing) *
        MvPolynomial.monomial (Finsupp.single b 1) 1) = _
    rw [MvPolynomial.monomial_mul_monomial, MvPolynomial.C_mul_monomial]
    simp
  rw [hmon] at hc
  have hex' : Finsupp.single a 1 + Finsupp.single b 1 ≠
      returnExponent 0 (K + e - q) q hpair := by
    simpa only [returnExponent, sub_zero] using hex
  have hzero : (MvPolynomial.monomial
      (Finsupp.single a 1 + Finsupp.single b 1) (μ q) : CompleteRing).coeff
      (returnExponent 0 (K + e - q) q hpair) = 0 := by
    simp [MvPolynomial.coeff_monomial, hex', Ne.symm hex']
  rw [hzero] at hc
  exact hn (by simpa [hmid, hz] using hc.symm)

/-- The contact-blind lemma on every integer parameter and every finite rational
measure with positive support strictly below `K-q`; support at `q` is allowed. -/
theorem contact_blind_injective (μ : ℤ →₀ ℚ) (e q K : ℤ)
    (hq : 1 ≤ q) (heq : q < e) (hK : q < K)
    (hμ : ∀ s ∈ μ.support, 0 < s ∧ s < K - q)
    (hOp : contactOperator μ e q K = 0) : μ = 0 := by
  have hqp : 0 < q := by omega
  have hep : 0 < e := by omega
  have hrel : complete e * quadratic μ K =
      complete q * quadratic μ (K + e - q) :=
    sub_eq_zero.mp hOp
  have her := congrArg (eraseContact q) hrel
  rw [map_mul, map_mul, eraseContact_complete q e hep,
    eraseContact_complete q q hqp] at her
  have he_ne : e ≠ q := by omega
  simp only [he_ne, ite_false, ite_true, zero_mul] at her
  have hEr : eraseContact q (quadratic μ K) = 0 :=
    (mul_eq_zero.mp her).resolve_left ((complete_ne_zero_iff e).mpr hep.le)
  have hfirst := quadratic_eq_erasure_add_contact μ q K hqp hK hμ
  rw [hEr, zero_add] at hfirst
  have hsecond : quadratic μ (K + e - q) =
      MvPolynomial.C (μ q) * (complete e * complete (K - q)) := by
    apply mul_left_cancel₀ ((complete_ne_zero_iff q).mpr hqp.le)
    rw [← hrel, hfirst]
    ring
  have hcontact := contact_coefficient_eq_zero μ e q K hqp heq hK hμ hsecond
  have hHK : quadratic μ K = 0 := by simp [hfirst, hcontact]
  have hHL : quadratic μ (K + e - q) = 0 := by simp [hsecond, hcontact]
  have hIK : ∀ s ∈ μ.support, 0 < s ∧ s < K := by
    intro s hs
    have := hμ s hs
    constructor <;> omega
  have hIL : ∀ s ∈ μ.support, 0 < s ∧ s < K + e - q := by
    intro s hs
    have := hμ s hs
    constructor <;> omega
  have hRK := quadratic_zero_reflection μ K hIK hHK
  have hRL := quadratic_zero_reflection μ (K + e - q) hIL hHL
  apply periodic_finsupp_eq_zero μ (e - q) (by omega)
  intro s
  have h₁ := hRK s
  have h₂ := hRL (K - s)
  have he : K + e - q - (K - s) = s + (e - q) := by ring
  rw [he] at h₂
  linarith

/-- Function formulation: finite support is the only finiteness assumption. -/
theorem contact_blind_function (μ : ℤ → ℚ) (hfin : (Function.support μ).Finite)
    (e q K : ℤ) (hq : 1 ≤ q) (heq : q < e) (hK : q < K)
    (hμ : ∀ s, μ s ≠ 0 → 0 < s ∧ s < K - q)
    (hOp : contactOperator (Finsupp.ofSupportFinite μ hfin) e q K = 0) :
    μ = 0 := by
  have hz := contact_blind_injective (Finsupp.ofSupportFinite μ hfin) e q K
    hq heq hK (fun s hs => hμ s (Finsupp.mem_support_iff.mp hs)) hOp
  funext s
  exact congrArg (fun ν : ℤ →₀ ℚ => ν s) hz

/-- A singleton measure is evaluated in the actual full polynomial ring. -/
@[simp]
theorem quadratic_single (s N : ℤ) (c : ℚ) :
    quadratic (Finsupp.single s c) N =
      MvPolynomial.C c * (complete s * complete (N - s)) := by
  classical
  change (Finsupp.single s c).sum
      (fun t v => MvPolynomial.C v * (complete t * complete (N - t))) = _
  exact Finsupp.sum_single_index (by simp)

/-- At the forbidden endpoint the nonzero measure `δ_e` lies in the actual
operator kernel; hence the upper bound must remain strict. -/
theorem strict_boundary_counterexample (e q : ℤ) (hq : 1 ≤ q) (heq : q < e) :
    let μ : ℤ →₀ ℚ := Finsupp.single e 1
    let K := q + e
    q < K ∧ μ ≠ 0 ∧
      (∀ s ∈ μ.support, 0 < s ∧ s ≤ K - q) ∧
      ¬ (∀ s ∈ μ.support, 0 < s ∧ s < K - q) ∧
      contactOperator μ e q K = 0 := by
  classical
  dsimp only
  have hep : 0 < e := by omega
  have hmem : e ∈ (Finsupp.single e (1 : ℚ)).support := by simp
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  · intro h
    have hc := congrArg (fun ν : ℤ →₀ ℚ => ν e) h
    norm_num at hc
  · intro s hs
    have hs' : s = e := by simpa using hs
    subst s
    constructor <;> omega
  · intro h
    have := (h e hmem).2
    omega
  · simp only [contactOperator, quadratic_single, map_one, one_mul]
    have h₁ : q + e - e = q := by ring
    have h₂ : q + e + e - q - e = e := by ring
    rw [h₁, h₂]
    ring

end SkewJacobiNegative.ContactQuadraticOperator
