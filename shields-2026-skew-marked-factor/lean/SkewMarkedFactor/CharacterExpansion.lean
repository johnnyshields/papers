/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
import SkewMarkedFactor.PowerCoordinates
import Mathlib.Data.Finsupp.Multiset

/-!
# Character coefficients and the full power-sum expansion

«Recovering the factors» (`eq:character`): partitions are exponent vectors of the
specified weight, not just the support of a particular polynomial.  The character
coefficient is identified with the signed Murnaghan–Nakayama ribbon-removal sum.
The coefficient API also applies to arbitrary homogeneous symmetric functions.
-/

noncomputable section
namespace SkewMarkedFactor
open Gluing Gluing.Plan MvPolynomial
open Gluing.Plan.KernelAux

@[simp] theorem powerSumEquiv_C (c : ℚ) : powerSumEquiv (C c) = C c :=
  powerSumEquiv.commutes c

/-- Finite multiplicities of positive parts indexing a power-sum monomial. -/
abbrev powerExponent := ℕ+ →₀ ℕ

/-- The exponent vector of the all-singleton partition. -/
def oneExponent (a : ℕ) : powerExponent := Finsupp.single 1 a

/-- A positive-index list with exactly the prescribed multiplicities. -/
def positiveWord (d : powerExponent) : List ℕ+ := d.toMultiset.toList

/-- The partition word, in the natural-number indices used by `pDerivWord`. -/
def exponentWord (d : powerExponent) : List ℕ :=
  (positiveWord d).map fun k : ℕ+ => (k : ℕ)

/-- The centralizer factor of a partition. -/
def powerZ (d : powerExponent) : ℚ :=
  ∏ k ∈ d.support, (k : ℚ) ^ d k * (Nat.factorial (d k) : ℚ)

/-- Multiplicities of a list of positive parts. -/
def wordExponent (l : List ℕ+) : powerExponent := Multiset.toFinsupp (l : Multiset ℕ+)

@[simp] theorem wordExponent_nil : wordExponent [] = 0 := by simp [wordExponent]

@[simp] theorem wordExponent_cons (k : ℕ+) (l : List ℕ+) :
    wordExponent (k :: l) = wordExponent l + Finsupp.single k 1 := by
  change Multiset.toFinsupp (({k} : Multiset ℕ+) + (l : Multiset ℕ+)) =
    Multiset.toFinsupp (l : Multiset ℕ+) + Finsupp.single k 1
  rw [map_add, Multiset.toFinsupp_singleton, add_comm]

@[simp] theorem wordExponent_positiveWord (d : powerExponent) :
    wordExponent (positiveWord d) = d := by simp [wordExponent, positiveWord]

theorem exponentWord_positive (d : powerExponent) : ∀ k ∈ exponentWord d, 0 < k := by
  intro k hk
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hk
  exact j.pos

theorem wordExponent_weight (l : List ℕ+) :
    Finsupp.weight degWeight (wordExponent l) = (l.map fun k : ℕ+ => (k : ℕ)).sum := by
  induction l with
  | nil => simp
  | cons k l ih => simp [ih, Finsupp.weight_single, degWeight, add_comm]

theorem exponentWord_sum (d : powerExponent) :
    (exponentWord d).sum = Finsupp.weight degWeight d := by
  calc
    (exponentWord d).sum =
        Finsupp.weight degWeight (wordExponent (positiveWord d)) :=
      (wordExponent_weight (positiveWord d)).symm
    _ = Finsupp.weight degWeight d := by rw [wordExponent_positiveWord]

@[simp] theorem powerZ_zero : powerZ 0 = 1 := by simp [powerZ]

theorem powerZ_nonzero (d : powerExponent) : powerZ d ≠ 0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro k _
  apply mul_ne_zero
  · exact pow_ne_zero _ (by exact_mod_cast k.ne_zero)
  · exact_mod_cast Nat.factorial_ne_zero (d k)

theorem powerZ_eq_prod {d : powerExponent} {s : Finset ℕ+} (hs : d.support ⊆ s) :
    powerZ d = ∏ k ∈ s, (k : ℚ) ^ d k * (Nat.factorial (d k) : ℚ) := by
  classical
  unfold powerZ
  apply Finset.prod_subset hs
  intro k _ hk
  have hz : d k = 0 := Finsupp.notMem_support_iff.mp hk
  simp [hz]

theorem powerZ_add_single (d : powerExponent) (k : ℕ+) :
    powerZ (d + Finsupp.single k 1) = powerZ d * (k : ℚ) * (d k + 1) := by
  classical
  let s := insert k d.support
  have hd : d.support ⊆ s := Finset.subset_insert _ _
  have hadd : (d + Finsupp.single k 1).support ⊆ s := by
    intro j hj
    by_contra h
    have hjd : j ∉ d.support := fun hx => h (Finset.mem_insert_of_mem hx)
    have hjk : j ≠ k := fun hx => h (by simp [s, hx])
    have := Finsupp.mem_support_iff.mp hj
    simp [Finsupp.notMem_support_iff.mp hjd, Finsupp.single_eq_of_ne hjk] at this
  rw [powerZ_eq_prod hadd, powerZ_eq_prod hd]
  have hterm : ∀ j : ℕ+, j ∈ s →
      (j : ℚ) ^ ((d + Finsupp.single k 1 : powerExponent) j) *
          (Nat.factorial ((d + Finsupp.single k 1 : powerExponent) j) : ℚ) =
      ((j : ℚ) ^ d j * (Nat.factorial (d j) : ℚ)) *
        (if j = k then (k : ℚ) * (d k + 1) else 1) := by
    intro j _
    by_cases hj : j = k
    · subst j
      simp only [Finsupp.add_apply, Finsupp.single_eq_same, ↓reduceIte,
        pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      ring
    · simp [hj, Finsupp.single_eq_of_ne hj]
  rw [Finset.prod_congr rfl hterm, Finset.prod_mul_distrib]
  simp [s, mul_assoc]

/-- The set of all exponent vectors of a given weight is finite, including weight zero. -/
theorem finite_partition_exponents (a : ℕ) :
    {d : powerExponent | Finsupp.weight degWeight d = a}.Finite := by
  classical
  let enc : powerExponent → (Fin a → Fin (a + 1)) := fun d i =>
    ⟨d (⟨i + 1, by omega⟩ : ℕ+) % (a + 1), Nat.mod_lt _ (by omega)⟩
  refine Set.Finite.of_injOn (f := enc) (t := Set.univ) (by simp) ?_ Set.finite_univ
  intro d hd e he h
  change Finsupp.weight degWeight d = a at hd
  change Finsupp.weight degWeight e = a at he
  apply Finsupp.ext
  intro k
  by_cases hk : (k : ℕ) ≤ a
  · let i : Fin a := ⟨(k : ℕ) - 1, by have := k.pos; omega⟩
    have hi : (⟨(i : ℕ) + 1, by omega⟩ : ℕ+) = k := by
      apply PNat.coe_injective
      have := k.pos
      simp only [i, PNat.mk_coe]
      omega
    have hd' : d k ≤ a := by
      have ht := Finsupp.le_weight degWeight (by exact k.ne_zero) d
      simpa [hd] using ht
    have he' : e k ≤ a := by
      have ht := Finsupp.le_weight degWeight (by exact k.ne_zero) e
      simpa [he] using ht
    have hh := congrArg (fun f => ((f i : Fin (a + 1)) : ℕ)) h
    simpa [enc, hi, Nat.mod_eq_of_lt (by omega : d k < a + 1),
      Nat.mod_eq_of_lt (by omega : e k < a + 1)] using hh
  · have hd' : d k = 0 := by
      by_contra hn
      have ht := Finsupp.le_weight_of_ne_zero' degWeight hn
      simp only [degWeight, hd] at ht
      omega
    have he' : e k = 0 := by
      by_contra hn
      have ht := Finsupp.le_weight_of_ne_zero' degWeight hn
      simp only [degWeight, he] at ht
      omega
    rw [hd', he']

/-- The full finite partition set of weight `a`. -/
def partitionExponents (a : ℕ) : Finset powerExponent :=
  (finite_partition_exponents a).toFinset

@[simp] theorem mem_partitionExponents (a : ℕ) (d : powerExponent) :
    d ∈ partitionExponents a ↔ Finsupp.weight degWeight d = a := by
  simp [partitionExponents]

@[simp] theorem oneExponent_weight (a : ℕ) :
    Finsupp.weight degWeight (oneExponent a) = a := by
  simp [oneExponent, Finsupp.weight_single, degWeight]

@[simp] theorem exponentWord_oneExponent (a : ℕ) :
    exponentWord (oneExponent a) = List.replicate a 1 := by
  classical
  apply List.eq_replicate_iff.mpr
  constructor
  · simp [exponentWord, positiveWord, oneExponent, Finsupp.toMultiset_single]
  · intro k hk
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hk
    have hj' : j ∈ (oneExponent a).support := by simpa [positiveWord] using hj
    have hj1 : j = (1 : ℕ+) := Finset.mem_singleton.mp
      (Finsupp.support_single_subset hj')
    simp [hj1]

@[simp] theorem powerZ_oneExponent (a : ℕ) :
    powerZ (oneExponent a) = (Nat.factorial a : ℚ) := by
  classical
  unfold oneExponent
  rw [powerZ_eq_prod (s := {1}) Finsupp.support_single_subset]
  simp

@[simp] theorem partitionExponents_zero : partitionExponents 0 = {0} := by
  classical
  ext d
  rw [mem_partitionExponents, Finset.mem_singleton]
  constructor
  · intro hd
    ext k
    have hk := Finsupp.le_weight degWeight (by exact k.ne_zero) d
    simp only [hd] at hk
    simpa using hk
  · rintro rfl; simp

/-- The actual normalized coefficient in power coordinates. -/
def characterCoefficient (f : Lambda) (d : powerExponent) : ℚ :=
  powerZ d * (powerSumEquiv.symm f).coeff d

theorem characterCoefficient_div (f : Lambda) (d : powerExponent) :
    characterCoefficient f d / powerZ d = (powerSumEquiv.symm f).coeff d := by
  apply (div_eq_iff (powerZ_nonzero d)).mpr
  simp [characterCoefficient, mul_comm]

/-- A single diagonal derivation in formal power coordinates. -/
def coordinateDeriv (k : ℕ+) : Derivation ℚ Lambda Lambda := (k : ℚ) • pderiv k

/-- Apply the head derivation first, as in `pDerivWord`. -/
def coordinateWord : List ℕ+ → Lambda →ₗ[ℚ] Lambda
  | [] => LinearMap.id
  | k :: l => (coordinateWord l).comp (coordinateDeriv k).toLinearMap

@[simp] theorem coordinateWord_cons (k : ℕ+) (l : List ℕ+) (f : Lambda) :
    coordinateWord (k :: l) f = coordinateWord l (coordinateDeriv k f) := rfl

theorem coeff_coordinateDeriv (k : ℕ+) (f : Lambda) (d : powerExponent) :
    (coordinateDeriv k f).coeff d =
      (k : ℚ) * f.coeff (d + Finsupp.single k 1) * (d k + 1) := by
  simp [coordinateDeriv, coeff_pderiv, smul_eq_mul, mul_assoc]

theorem pDerivWord_powerSumEquiv (l : List ℕ+) (f : Lambda) :
    pDerivWord (l.map fun k : ℕ+ => (k : ℕ)) (powerSumEquiv f) =
      powerSumEquiv (coordinateWord l f) := by
  induction l generalizing f with
  | nil => rfl
  | cons k l ih =>
    simp only [List.map_cons, Gluing.Plan.KernelAux.pDerivWord_cons, coordinateWord_cons]
    rw [pDeriv_powerSumEquiv, ih]
    congr 2
    simp [coordinateDeriv, Algebra.smul_def]

/-- The factorial coefficient identity, before imposing homogeneity. -/
theorem coeff_zero_coordinateWord (l : List ℕ+) (f : Lambda) :
    (coordinateWord l f).coeff 0 = powerZ (wordExponent l) * f.coeff (wordExponent l) := by
  induction l generalizing f with
  | nil => simp [coordinateWord]
  | cons k l ih =>
    rw [coordinateWord_cons, ih, coeff_coordinateDeriv, wordExponent_cons, powerZ_add_single]
    ring

theorem homogeneous_coordinateDeriv {f : Lambda} {a : ℕ}
    (hf : IsWeightedHomogeneous degWeight f a) (k : ℕ+) :
    IsWeightedHomogeneous degWeight (coordinateDeriv k f) (a - k) := by
  intro d hd
  rw [coeff_coordinateDeriv] at hd
  have hc : f.coeff (d + Finsupp.single k 1) ≠ 0 :=
    right_ne_zero_of_mul (left_ne_zero_of_mul hd)
  have hw := hf hc
  simp only [map_add, Finsupp.weight_single, one_nsmul, degWeight] at hw
  omega

theorem coordinateDeriv_eq_zero_of_weight_lt {f : Lambda} {a : ℕ}
    (hf : IsWeightedHomogeneous degWeight f a) {k : ℕ+} (hk : a < k) :
    coordinateDeriv k f = 0 := by
  ext d
  rw [coeff_coordinateDeriv]
  have hc : f.coeff (d + Finsupp.single k 1) = 0 := by
    apply hf.coeff_eq_zero
    simp only [map_add, Finsupp.weight_single, one_nsmul, degWeight]
    omega
  simp [hc]

theorem homogeneous_coordinateWord {f : Lambda} {a : ℕ}
    (hf : IsWeightedHomogeneous degWeight f a) (l : List ℕ+) :
    IsWeightedHomogeneous degWeight (coordinateWord l f)
      (a - (l.map fun k : ℕ+ => (k : ℕ)).sum) := by
  induction l generalizing f a with
  | nil => simpa [coordinateWord] using hf
  | cons k l ih =>
    simpa [Nat.sub_sub, add_comm] using ih (homogeneous_coordinateDeriv hf k)

theorem coordinateWord_eq_zero_of_weight_lt {f : Lambda} {a : ℕ}
    (hf : IsWeightedHomogeneous degWeight f a) {l : List ℕ+}
    (hl : a < (l.map fun k : ℕ+ => (k : ℕ)).sum) : coordinateWord l f = 0 := by
  induction l generalizing f a with
  | nil => simp at hl
  | cons k l ih =>
    rw [coordinateWord_cons]
    by_cases hk : a < k
    · rw [coordinateDeriv_eq_zero_of_weight_lt hf hk, map_zero]
    · apply ih (homogeneous_coordinateDeriv hf k)
      change a < (k : ℕ) + (l.map fun k : ℕ+ => (k : ℕ)).sum at hl
      omega

theorem homogeneous_zero_eq_C {f : Lambda}
    (hf : IsWeightedHomogeneous degWeight f 0) : f = C (f.coeff 0) := by
  have he : ∀ d : powerExponent, Finsupp.weight degWeight d = 0 → d = 0 := by
    intro d hd
    ext k
    have hk := Finsupp.le_weight degWeight (by exact k.ne_zero) d
    simp only [hd] at hk
    simpa using hk
  simpa using hf.eq_monomial_of_unique_weight he

/-- The algebraic `z_ν` identity for a complete derivative of a homogeneous function. -/
theorem deltaWord_exponentWord_coeff {f : Lambda} {a : ℕ}
    (hf : IsWeightedHomogeneous degWeight f a) {d : powerExponent}
    (hd : Finsupp.weight degWeight d = a) :
    pDerivWord (exponentWord d) f = C (characterCoefficient f d) := by
  let g := powerSumEquiv.symm f
  have hg : IsWeightedHomogeneous degWeight g a := homogeneous_powerSumEquiv_symm hf
  have hl : ((positiveWord d).map fun k : ℕ+ => (k : ℕ)).sum = a := by
    simpa [exponentWord] using (exponentWord_sum d).trans hd
  have hh := homogeneous_coordinateWord hg (positiveWord d)
  rw [hl, Nat.sub_self] at hh
  have he := homogeneous_zero_eq_C hh
  rw [coeff_zero_coordinateWord, wordExponent_positiveWord] at he
  calc
    pDerivWord (exponentWord d) f =
        powerSumEquiv (coordinateWord (positiveWord d) g) := by
      simpa [g, exponentWord] using pDerivWord_powerSumEquiv (positiveWord d) g
    _ = C (characterCoefficient f d) := by rw [he]; simp [characterCoefficient, g]

/-- A Hall word lowers the weighted degree by the sum of its positive parts. -/
theorem homogeneous_deltaWord {f : Lambda} {a : ℕ}
    (hf : IsWeightedHomogeneous degWeight f a) (l : List ℕ+) :
    IsWeightedHomogeneous degWeight
      (pDerivWord (l.map fun k : ℕ+ => (k : ℕ)) f)
      (a - (l.map fun k : ℕ+ => (k : ℕ)).sum) := by
  rw [← powerSumEquiv.apply_symm_apply f, pDerivWord_powerSumEquiv]
  apply homogeneous_powerSumEquiv
  exact homogeneous_coordinateWord (homogeneous_powerSumEquiv_symm hf) l

theorem deltaWord_eq_zero_of_weight_lt {f : Lambda} {a : ℕ}
    (hf : IsWeightedHomogeneous degWeight f a) {l : List ℕ+}
    (hl : a < (l.map fun k : ℕ+ => (k : ℕ)).sum) :
    pDerivWord (l.map fun k : ℕ+ => (k : ℕ)) f = 0 := by
  rw [← powerSumEquiv.apply_symm_apply f, pDerivWord_powerSumEquiv,
    coordinateWord_eq_zero_of_weight_lt (homogeneous_powerSumEquiv_symm hf) hl, map_zero]

theorem homogeneous_pDeriv {f : Lambda} {a k : ℕ}
    (hf : IsWeightedHomogeneous degWeight f a) (hk : 0 < k) :
    IsWeightedHomogeneous degWeight (pDeriv k f) (a - k) := by
  have h := homogeneous_deltaWord hf [⟨k, hk⟩]
  change IsWeightedHomogeneous degWeight (pDerivWord [k] f) (a - [k].sum) at h
  simpa only [pDerivWord, LinearMap.comp_apply, LinearMap.id_apply, Derivation.coeFn_coe,
    List.sum_singleton] using h

theorem pDeriv_eq_zero_of_weight_lt {f : Lambda} {a k : ℕ}
    (hf : IsWeightedHomogeneous degWeight f a) (hk : a < k) : pDeriv k f = 0 := by
  have hk' : 0 < k := by omega
  have h := @deltaWord_eq_zero_of_weight_lt f a hf [⟨k, hk'⟩] (by
    change a < [k].sum
    simpa only [List.sum_singleton] using hk)
  change pDerivWord [k] f = 0 at h
  simpa only [pDerivWord, LinearMap.comp_apply, LinearMap.id_apply, Derivation.coeFn_coe] using h

theorem deltaWord_oneExponent_coeff {f : Lambda} {a : ℕ}
    (hf : IsWeightedHomogeneous degWeight f a) :
    pDerivWord (List.replicate a 1) f = C (characterCoefficient f (oneExponent a)) := by
  simpa using deltaWord_exponentWord_coeff hf (oneExponent_weight a)

theorem powerSumEquiv_monomial_word (l : List ℕ+) :
    powerSumEquiv (monomial (wordExponent l) 1) =
      pProd (l.map fun k : ℕ+ => (k : ℕ)) := by
  induction l with
  | nil => simp [wordExponent, pProd]
  | cons k l ih =>
    have hm : (monomial (wordExponent l + Finsupp.single k 1) 1 : Lambda) =
        monomial (wordExponent l) 1 * X k := by
      simp only [X, monomial_mul_monomial, mul_one]
    rw [wordExponent_cons, hm, map_mul, powerSumEquiv_X, ih]
    simp [pProd, mul_comm]

theorem powerSumEquiv_monomial (d : powerExponent) :
    powerSumEquiv (monomial d 1) = pProd (exponentWord d) := by
  simpa [exponentWord] using powerSumEquiv_monomial_word (positiveWord d)

/-- The full partition expansion, including the empty partition of weight zero. -/
theorem character_expansion {f : Lambda} {a : ℕ}
    (hf : IsWeightedHomogeneous degWeight f a) :
    f = ∑ d ∈ partitionExponents a,
      C (characterCoefficient f d / powerZ d) * pProd (exponentWord d) := by
  classical
  let g := powerSumEquiv.symm f
  have hg : IsWeightedHomogeneous degWeight g a := homogeneous_powerSumEquiv_symm hf
  have hsum : g = ∑ d ∈ partitionExponents a, monomial d (g.coeff d) := by
    ext e
    simp only [coeff_sum, coeff_monomial]
    by_cases he : e ∈ partitionExponents a
    · rw [Finset.sum_eq_single e]
      · simp
      · intro d _ hde; simp [hde]
      · exact fun h => (h he).elim
    · have hc : g.coeff e = 0 := hg.coeff_eq_zero e (by simpa using he)
      rw [hc]
      symm
      apply Finset.sum_eq_zero
      intro d hd
      have hde : d ≠ e := fun h => he (h ▸ hd)
      simp [hde]
  have ht := congrArg powerSumEquiv hsum
  simp only [g, AlgEquiv.apply_symm_apply, map_sum] at ht
  calc
    f = ∑ d ∈ partitionExponents a,
        powerSumEquiv (monomial d ((powerSumEquiv.symm f).coeff d)) := ht
    _ = ∑ d ∈ partitionExponents a,
        C (characterCoefficient f d / powerZ d) * pProd (exponentWord d) := by
      apply Finset.sum_congr rfl
      intro d _
      rw [characterCoefficient_div]
      have hm : (monomial d ((powerSumEquiv.symm f).coeff d) : Lambda) =
          C ((powerSumEquiv.symm f).coeff d) * monomial d 1 := by
        rw [C_mul_monomial, mul_one]
      rw [hm, map_mul, powerSumEquiv_monomial, powerSumEquiv_C]

theorem coeff_zero_powerSumEquiv (f : Lambda) :
    (powerSumEquiv f).coeff 0 = f.coeff 0 := by
  change constantCoeff (powerSumEquiv f) = constantCoeff f
  induction f using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg => simp [map_add, hf, hg]
  | mul_X f k hf =>
    rw [map_mul, map_mul, hf, map_mul, constantCoeff_X, mul_zero,
      powerSumEquiv_X]
    have hk : (pPoly k).coeff 0 = 0 :=
      (Gluing.Plan.KernelAux.isWeightedHomogeneous_pPoly k).coeff_eq_zero 0 (by
        simp only [map_zero]; exact Ne.symm k.ne_zero)
    change constantCoeff f * (pPoly k).coeff 0 = 0
    rw [hk, mul_zero]

/-- The constant-term identity holds without assuming homogeneity. -/
theorem characterCoefficient_eq_delta_constant (f : Lambda) (d : powerExponent) :
    characterCoefficient f d = (pDerivWord (exponentWord d) f).coeff 0 := by
  unfold characterCoefficient
  calc
    powerZ d * (powerSumEquiv.symm f).coeff d =
        (coordinateWord (positiveWord d) (powerSumEquiv.symm f)).coeff 0 := by
      symm
      simpa using coeff_zero_coordinateWord (positiveWord d) (powerSumEquiv.symm f)
    _ = (powerSumEquiv
        (coordinateWord (positiveWord d) (powerSumEquiv.symm f))).coeff 0 :=
      (coeff_zero_powerSumEquiv _).symm
    _ = (pDerivWord (exponentWord d) f).coeff 0 := by
      rw [← pDerivWord_powerSumEquiv, powerSumEquiv.apply_symm_apply]
      rfl

/-- Signed complete left-ribbon-removal count.  The empty word contributes one
only for the empty diagram; no normalized-character formula is used here. -/
def ribbonCharacter : Diagram → List ℕ → ℚ
  | D, [] => if D = ∅ then 1 else 0
  | D, m :: l => ∑ R ∈ leftRibbons D m,
      (ribbonSign R : ℚ) * ribbonCharacter (D \ R) l

/-- A Schur function's constant term is exactly the empty-diagram indicator. -/
theorem coeff_zero_cellSchur {D : Diagram} (hD : IsSkew D) :
    (cellSchur D).coeff 0 = if D = ∅ then 1 else 0 := by
  by_cases he : D = ∅
  · subst D; simp
  · rw [ite_eq_right he]
    apply (isWeightedHomogeneous_cellSchur hD).coeff_eq_zero
    simp only [map_zero]
    exact Ne.symm (Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr he))

/-- Murnaghan–Nakayama identifies actual Hall derivatives with signed ribbon
removals, including the empty-word boundary. -/
theorem delta_constant_eq_ribbonCharacter {D : Diagram} (hD : IsSkew D)
    {l : List ℕ} (hl : ∀ m ∈ l, 0 < m) :
    (pDerivWord l (cellSchur D)).coeff 0 = ribbonCharacter D l := by
  induction l generalizing D with
  | nil => simpa [pDerivWord, ribbonCharacter] using coeff_zero_cellSchur hD
  | cons m l ih =>
    have hm := hl m List.mem_cons_self
    have hl' : ∀ k ∈ l, 0 < k := fun k hk => hl k (List.mem_cons_of_mem _ hk)
    rw [Gluing.Plan.KernelAux.pDerivWord_cons, pDeriv_cellSchur_left hD hm]
    unfold ribbonSumLeft
    rw [map_sum]
    simp only [coeff_sum, ribbonCharacter]
    apply Finset.sum_congr rfl
    intro R hR
    rw [← Gluing.Plan.KernelAux.smul_int_eq, map_smul, coeff_smul]
    rw [ih (isSkew_sdiff_of_mem_leftRibbons hD hR) hl']
    rfl

/-- The coefficient-defined character is the signed ribbon character, proved
from Murnaghan–Nakayama rather than supplied as an expansion assumption. -/
theorem characterCoefficient_cellSchur_eq_ribbonCharacter {D : Diagram} (hD : IsSkew D)
    (d : powerExponent) :
    characterCoefficient (cellSchur D) d = ribbonCharacter D (exponentWord d) := by
  rw [characterCoefficient_eq_delta_constant]
  exact delta_constant_eq_ribbonCharacter hD (exponentWord_positive d)

/-- The genuine skew-character expansion of the actual cell Schur function. -/
theorem cellSchur_character_expansion {D : Diagram} (hD : IsSkew D) :
    cellSchur D = ∑ d ∈ partitionExponents D.card,
      C (ribbonCharacter D (exponentWord d) / powerZ d) * pProd (exponentWord d) := by
  have h := character_expansion (isWeightedHomogeneous_cellSchur hD)
  simpa only [characterCoefficient_cellSchur_eq_ribbonCharacter hD] using h

theorem cellSchur_deltaWord_exponentWord {D : Diagram} (hD : IsSkew D)
    {d : powerExponent} (hd : Finsupp.weight degWeight d = D.card) :
    pDerivWord (exponentWord d) (cellSchur D) =
      C (ribbonCharacter D (exponentWord d)) := by
  rw [deltaWord_exponentWord_coeff (isWeightedHomogeneous_cellSchur hD) hd,
    characterCoefficient_cellSchur_eq_ribbonCharacter hD]

end SkewMarkedFactor
