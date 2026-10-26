/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
-- TODO-COPIED: skew-jacobi-negative/lean/SkewJacobiNegative/Gluing/RowInvariants.lean

import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Rat.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import SkewJacobiNegative.Gluing.SchurFunction

/-!
# Row lengths and overlaps are invariants of the skew Schur function

Formalizes `shields-2026-skew-factor-gluing.tex`, «Local common-factor gluing» (`sec:gluing`,
`lem:gluing-row-transport`): the literature input consumed there as the proposition
`ReinerRowInvariants` (Reiner–Shaw–van Willigenburg, Cor. 8.11, row overlap data of a connected
diagram).

Connected profiles with the same Jacobi–Trudi determinant have the same number of rows, the same
multiset of row lengths and the same multiset of adjacent overlaps (`reinerRowInvariants`).

The proof is a direct extremal-monomial argument in `ℚ[h₁, h₂, …]`, with no Littlewood–Richardson
input.  For strictly decreasing `ξ`, `ζ` with `ζ_i ≤ ξ_i`, the monomials of `det (h_{ξ_i - ζ_j})`
are `∏ h_{ξ_{σ i} - ζ_i}`; the weight `∑ k²` of the subscripts is, by the rearrangement
inequality, minimal exactly at the identity permutation, so the monomial `∏ h_{ξ_i - ζ_i}` has
coefficient one and is the unique monomial of least weight (`betaMon_eq_of_betaDet_eq`).  This
recovers the multiset of row lengths.  The top subscript `L = ξ₀` occurs only in the entry
`(0, n)`, so the partial derivative `∂/∂h_L` of the determinant is `(-1)ⁿ` times the complementary
minor, itself a determinant of the same shape with `ξ_{i+1} - ζ_i` on the diagonal; this recovers
the multiset of overlaps minus one.

Sorry-free.
-/

namespace SkewJacobiNegative.Gluing

open MvPolynomial

/-! ### Monomials of the Jacobi–Trudi expansion -/

/-- The exponent vector of `h_a`: the unit vector at `a` for `a ≥ 1`, and `0` for `a = 0`. -/
noncomputable def hExp (a : ℕ) : ℕ+ →₀ ℕ :=
  if h : 0 < a then Finsupp.single (Nat.toPNat a h) 1 else 0

theorem hPos_eq_monomial (a : ℕ) : hPos a = monomial (hExp a) 1 := by
  by_cases h : 0 < a
  · simp only [hPos, hExp, h, dite_true]
    rfl
  · obtain rfl : a = 0 := by omega
    simp [hExp]

theorem hh_eq_monomial {x : ℤ} (hx : 0 ≤ x) : hh x = monomial (hExp x.toNat) 1 := by
  rw [hh, ite_eq_right (by omega), hPos_eq_monomial]

theorem hExp_apply (a : ℕ) (v : ℕ+) : hExp a v = if a = (v : ℕ) then 1 else 0 := by
  by_cases h : 0 < a
  · rw [hExp, dite_eq_left h, Finsupp.single_apply]
    have : Nat.toPNat a h = v ↔ a = (v : ℕ) := ⟨fun e => by rw [← e]; rfl, fun e => PNat.eq e⟩
    simp only [this]
  · obtain rfl : a = 0 := by omega
    have := v.pos
    simp [hExp]
    omega

/-- The weight `∑ k² · (exponent of h_k)` of a monomial in the variables `h_k`. -/
noncomputable def sqWeight : (ℕ+ →₀ ℕ) →+ ℕ :=
  Finsupp.liftAddHom fun k : ℕ+ => AddMonoidHom.mulRight ((k : ℕ) ^ 2)

theorem sqWeight_hExp (a : ℕ) : sqWeight (hExp a) = a ^ 2 := by
  by_cases h : 0 < a
  · rw [hExp, dite_eq_left h]
    simp [sqWeight]
    rfl
  · obtain rfl : a = 0 := by omega
    simp [hExp]

section Expansion

variable {k : ℕ}

/-- The exponent vector of the diagonal monomial `∏ h_{ξ_i - ζ_i}` (zero subscripts dropped). -/
noncomputable def betaMon (ξ ζ : Fin k → ℤ) : ℕ+ →₀ ℕ := ∑ i, hExp (ξ i - ζ i).toNat

/-- The Jacobi–Trudi determinant `det (h_{ξ_i - ζ_j})` of a pair of lists. -/
noncomputable def betaDet (ξ ζ : Fin k → ℤ) : Lambda :=
  (Matrix.of fun i j : Fin k => hh (ξ i - ζ j)).det

theorem prod_hh_eq (x : Fin k → ℤ) :
    ∏ i, hh (x i) =
      if ∀ i, 0 ≤ x i then monomial (∑ i, hExp (x i).toNat) 1 else 0 := by
  by_cases h : ∀ i, 0 ≤ x i
  · rw [ite_eq_left h, monomial_sum_one]
    exact Finset.prod_congr rfl fun i _ => hh_eq_monomial (h i)
  · rw [ite_eq_right h]
    push Not at h
    obtain ⟨i, hi⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (hh_of_neg hi)

/-- The rearrangement inequality for sums of squares: pairing a strictly decreasing `ξ` with a
strictly decreasing `ζ` through any permutation other than the identity strictly increases
`∑ (ξ - ζ)²`. -/
theorem sum_sq_lt {ξ ζ : Fin k → ℤ} (hξ : StrictAnti ξ) (hζ : StrictAnti ζ)
    {σ : Equiv.Perm (Fin k)} (hσ : σ ≠ 1) :
    ∑ i, (ξ i - ζ i) ^ 2 < ∑ i, (ξ (σ i) - ζ i) ^ 2 := by
  have hmono : Monovary ξ ζ := hξ.antitone.monovary hζ.antitone
  have hlt : ∑ i, ξ (σ i) • ζ i < ∑ i, ξ i • ζ i := by
    rw [hmono.sum_comp_perm_smul_lt_sum_smul_iff]
    intro hmv
    apply hσ
    have hsm : StrictMono σ := by
      intro i j hij
      by_contra hcon
      have h1 : σ j ≤ σ i := not_lt.mp hcon
      have h2 : σ j < σ i := lt_of_le_of_ne h1 (fun e => (ne_of_lt hij) (σ.injective e.symm))
      have h4 := hmv (hζ hij)
      have h5 : ξ (σ i) < ξ (σ j) := hξ h2
      simp only [Function.comp] at h4
      omega
    exact Equiv.ext fun i => congrFun hsm.eq_id i
  have e1 : ∑ i, (ξ (σ i)) ^ 2 = ∑ i, (ξ i) ^ 2 := Equiv.sum_comp σ fun i => (ξ i) ^ 2
  have e2 : ∀ τ : Fin k → Fin k, ∑ i, (ξ (τ i) - ζ i) ^ 2 =
      ∑ i, (ξ (τ i)) ^ 2 + ∑ i, (ζ i) ^ 2 - 2 * ∑ i, ξ (τ i) * ζ i := by
    intro τ
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have := e2 σ
  have h3 := e2 id
  simp only [smul_eq_mul, id] at hlt h3
  linarith

/-- For `ζ ≤ ξ` and a permutation `σ`, the weight of the monomial of `∏ h_{ξ_{σ i} - ζ_i}`
equals `∑ (ξ_{σ i} - ζ_i)²` whenever all subscripts are nonnegative. -/
theorem sqWeight_sum_hExp {x : Fin k → ℤ} (hx : ∀ i, 0 ≤ x i) :
    (sqWeight (∑ i, hExp (x i).toNat) : ℤ) = ∑ i, (x i) ^ 2 := by
  rw [map_sum]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sqWeight_hExp]
  have := Int.toNat_of_nonneg (hx i)
  push_cast
  rw [this]

theorem betaDet_eq_sum (ξ ζ : Fin k → ℤ) :
    betaDet ξ ζ = ∑ σ : Equiv.Perm (Fin k),
      (Equiv.Perm.sign σ : ℤ) • ∏ i, hh (ξ (σ i) - ζ i) := by
  unfold betaDet
  rw [Matrix.det_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Matrix.of_apply, Units.smul_def]

theorem coeff_betaDet (ξ ζ : Fin k → ℤ) (m : ℕ+ →₀ ℕ) :
    (betaDet ξ ζ).coeff m = ∑ σ : Equiv.Perm (Fin k),
      (Equiv.Perm.sign σ : ℤ) •
        (if (∀ i, 0 ≤ ξ (σ i) - ζ i) ∧ (∑ i, hExp (ξ (σ i) - ζ i).toNat) = m
          then (1 : ℚ) else 0) := by
  rw [betaDet_eq_sum, coeff_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [coeff_smul, prod_hh_eq]
  congr 1
  by_cases h : ∀ i, 0 ≤ ξ (σ i) - ζ i
  · rw [ite_eq_left h, coeff_monomial]
    by_cases hm : (∑ i, hExp (ξ (σ i) - ζ i).toNat) = m
    · rw [ite_eq_left hm, ite_eq_left ⟨h, hm⟩]
    · rw [ite_eq_right hm, ite_eq_right (fun e => hm e.2)]
  · rw [ite_eq_right h, ite_eq_right (fun e => h e.1)]
    simp

variable {ξ ζ : Fin k → ℤ}

/-- The diagonal monomial of `det (h_{ξ_i - ζ_j})` has coefficient one, and every other monomial
occurring has strictly larger weight. -/
theorem betaDet_extremal (hξ : StrictAnti ξ) (hζ : StrictAnti ζ) (hle : ∀ i, ζ i ≤ ξ i) :
    (betaDet ξ ζ).coeff (betaMon ξ ζ) = 1 ∧
      ∀ m, (betaDet ξ ζ).coeff m ≠ 0 → m ≠ betaMon ξ ζ →
        sqWeight (betaMon ξ ζ) < sqWeight m := by
  have hdiag : ∀ i, 0 ≤ ξ i - ζ i := fun i => by have := hle i; omega
  have hW : (sqWeight (betaMon ξ ζ) : ℤ) = ∑ i, (ξ i - ζ i) ^ 2 := sqWeight_sum_hExp hdiag
  refine ⟨?_, ?_⟩
  · rw [coeff_betaDet, Finset.sum_eq_single (1 : Equiv.Perm (Fin k))]
    · have : (∀ i, 0 ≤ ξ ((1 : Equiv.Perm (Fin k)) i) - ζ i) ∧
          (∑ i, hExp (ξ ((1 : Equiv.Perm (Fin k)) i) - ζ i).toNat) = betaMon ξ ζ :=
        ⟨hdiag, rfl⟩
      rw [ite_eq_left this]
      simp
    · intro σ _ hσ
      rw [ite_eq_right, smul_zero]
      rintro ⟨hnn, hm⟩
      have h1 := sqWeight_sum_hExp hnn
      rw [hm, hW] at h1
      have := sum_sq_lt hξ hζ hσ
      omega
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro m hm hne
    rw [coeff_betaDet] at hm
    obtain ⟨σ, _, hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
    have hc : (∀ i, 0 ≤ ξ (σ i) - ζ i) ∧ (∑ i, hExp (ξ (σ i) - ζ i).toNat) = m := by
      by_contra hcon
      rw [ite_eq_right hcon, smul_zero] at hσ
      exact hσ rfl
    obtain ⟨hnn, hmσ⟩ := hc
    have hσ1 : σ ≠ 1 := by
      rintro rfl
      exact hne hmσ.symm
    have h1 := sqWeight_sum_hExp hnn
    rw [hmσ] at h1
    have := sum_sq_lt hξ hζ hσ1
    have : (sqWeight (betaMon ξ ζ) : ℤ) < sqWeight m := by omega
    exact_mod_cast this

/-- The diagonal monomial is determined by the polynomial `det (h_{ξ_i - ζ_j})`: it is the
unique monomial of least weight. -/
theorem betaMon_eq_of_betaDet_eq {k' : ℕ} {ξ' ζ' : Fin k' → ℤ}
    (hξ : StrictAnti ξ) (hζ : StrictAnti ζ) (hle : ∀ i, ζ i ≤ ξ i)
    (hξ' : StrictAnti ξ') (hζ' : StrictAnti ζ') (hle' : ∀ i, ζ' i ≤ ξ' i)
    (h : betaDet ξ ζ = betaDet ξ' ζ') : betaMon ξ ζ = betaMon ξ' ζ' := by
  obtain ⟨c1, m1⟩ := betaDet_extremal hξ hζ hle
  obtain ⟨c2, m2⟩ := betaDet_extremal hξ' hζ' hle'
  by_contra hne
  have a := m1 (betaMon ξ' ζ') (by rw [h, c2]; exact one_ne_zero) (Ne.symm hne)
  have b := m2 (betaMon ξ ζ) (by rw [← h, c1]; exact one_ne_zero) hne
  omega

end Expansion

/-! ### From monomials to multisets -/

theorem betaMon_apply {k : ℕ} (ξ ζ : Fin k → ℤ) (v : ℕ+) :
    betaMon ξ ζ v =
      Multiset.count (v : ℕ) (Finset.univ.val.map fun i => (ξ i - ζ i).toNat) := by
  simp only [betaMon, Finsupp.coe_finsetSum, Finset.sum_apply, hExp_apply]
  rw [Multiset.count_map]
  rw [Finset.sum_boole, Nat.cast_id]
  change _ = (Finset.univ.filter fun a => (v : ℕ) = (ξ a - ζ a).toNat).card
  simp only [eq_comm]

/-- Two multisets of naturals with the same cardinality and the same multiplicity of every
positive value are equal. -/
theorem multiset_eq_of_count_pnat {s t : Multiset ℕ}
    (hcount : ∀ v : ℕ+, s.count (v : ℕ) = t.count (v : ℕ))
    (hcard : Multiset.card s = Multiset.card t) : s = t := by
  have hz : ∀ u : Multiset ℕ, u.filter (fun a => ¬ 0 < a) = Multiset.replicate (u.count 0) 0 := by
    intro u
    ext a
    rw [Multiset.count_filter, Multiset.count_replicate]
    by_cases ha : a = 0
    · subst ha; simp
    · have : 0 < a := Nat.pos_of_ne_zero ha
      simp [this, Ne.symm ha]
  have hp : s.filter (fun a => 0 < a) = t.filter (fun a => 0 < a) := by
    ext a
    rw [Multiset.count_filter, Multiset.count_filter]
    by_cases ha : 0 < a
    · simp only [ha, ite_true]
      exact hcount ⟨a, ha⟩
    · simp [ha]
  have hs := Multiset.filter_add_not (fun a => 0 < a) s
  have ht := Multiset.filter_add_not (fun a => 0 < a) t
  have c0 : s.count 0 = t.count 0 := by
    have h1 := congrArg Multiset.card hs
    have h2 := congrArg Multiset.card ht
    rw [Multiset.card_add, hz, Multiset.card_replicate] at h1 h2
    rw [hp] at h1
    omega
  ext a
  by_cases ha : a = 0
  · subst ha; exact c0
  · exact hcount ⟨a, Nat.pos_of_ne_zero ha⟩

/-! ### The partial derivative at the top subscript -/

/-- The kernel of the partial derivative `∂/∂h_k`, a subalgebra of `Λ`. -/
noncomputable def derivKer (k : ℕ+) : Subalgebra ℚ Lambda where
  carrier := {p | pderiv k p = 0}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    rw [Derivation.leibniz, ha, hb]
    simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    rw [map_add, ha, hb, add_zero]
  algebraMap_mem' := by
    intro r
    exact Derivation.map_algebraMap _ r

theorem pderiv_det_eq_zero {d : ℕ} (k : ℕ+) (M : Matrix (Fin d) (Fin d) Lambda)
    (hM : ∀ i j, pderiv k (M i j) = 0) : pderiv k M.det = 0 := by
  let M' : Matrix (Fin d) (Fin d) (derivKer k) := fun i j => ⟨M i j, hM i j⟩
  have : M = ((derivKer k).val.toRingHom).mapMatrix M' := by
    ext i j; rfl
  have h2 : M.det = (derivKer k).val M'.det := by
    rw [this, ← RingHom.map_det]; rfl
  rw [h2]
  exact (M'.det).2

theorem pderiv_hh (k : ℕ+) (x : ℤ) : pderiv k (hh x) = if x = ((k : ℕ) : ℤ) then 1 else 0 := by
  by_cases hx : x < 0
  · rw [hh_of_neg hx]
    have : x ≠ ((k : ℕ) : ℤ) := by omega
    simp [this]
  · rw [hh, ite_eq_right hx]
    by_cases h0 : 0 < x.toNat
    · have e : hPos x.toNat = X (Nat.toPNat x.toNat h0) := by
        rw [hPos, dite_eq_left h0]; rfl
      rw [e, pderiv_X, Pi.single_apply]
      have : (Nat.toPNat x.toNat h0 = k) ↔ x = ((k : ℕ) : ℤ) := by
        constructor
        · intro e'
          have : x.toNat = (k : ℕ) := by rw [← e']; rfl
          omega
        · intro e'
          exact PNat.eq (by change x.toNat = (k : ℕ); omega)
      simp [this]
    · have : x.toNat = 0 := by omega
      rw [this, hPos_zero]
      have : x ≠ ((k : ℕ) : ℤ) := by have := k.pos; omega
      simp [this]

theorem pderiv_hh_of_ne {k : ℕ+} {x : ℤ} (h : x ≠ ((k : ℕ) : ℤ)) : pderiv k (hh x) = 0 := by
  rw [pderiv_hh, ite_eq_right h]


namespace Profile

variable {n : ℕ}

/-- The top subscript `ξ₀`, as a positive natural number: the variable `h_{ξ₀}` occurs in
`det (h_{ξ_i - ζ_j})` only in the entry `(0, n)`. -/
noncomputable def topVar (P : Profile n) : ℕ+ := Nat.toPNat (P.xi 0).toNat (by
  have := P.xi_pos 0
  omega)

theorem topVar_coe (P : Profile n) : (((P.topVar : ℕ+) : ℕ) : ℤ) = P.xi 0 := by
  have := P.xi_pos 0
  change (((P.xi 0).toNat : ℕ) : ℤ) = P.xi 0
  omega

/-- The entries of the Jacobi–Trudi matrix of `P` have subscripts at most `ξ₀`, with equality
only at `(0, n)`. -/
theorem xi_sub_zeta_le (P : Profile n) (i j : Fin (n + 1)) : P.xi i - P.zeta j ≤ P.xi 0 := by
  have h1 : P.xi i ≤ P.xi 0 := P.xi_strictAnti.antitone (Fin.zero_le i)
  have h2 := P.zeta_nonneg j
  omega

theorem xi_sub_zeta_eq_top {P : Profile n} {i j : Fin (n + 1)} (h : P.xi i - P.zeta j = P.xi 0) :
    i = 0 ∧ j = Fin.last n := by
  have h1 : P.xi i ≤ P.xi 0 := P.xi_strictAnti.antitone (Fin.zero_le i)
  have h2 := P.zeta_nonneg j
  constructor
  · by_contra hi
    have : P.xi i < P.xi 0 := P.xi_strictAnti (Fin.pos_iff_ne_zero.mpr hi)
    omega
  · by_contra hj
    have hj' : j < Fin.last n := lt_of_le_of_ne (Fin.le_last j) hj
    have := P.zeta_strictAnti hj'
    rw [P.zeta_last] at this
    omega

/-- Above the top subscript, every partial derivative of `s_P` vanishes. -/
theorem pderiv_schur_of_gt (P : Profile n) {k : ℕ+} (hk : P.xi 0 < ((k : ℕ) : ℤ)) :
    pderiv k P.schur = 0 := by
  apply pderiv_det_eq_zero
  intro i j
  have := P.xi_sub_zeta_le i j
  exact pderiv_hh_of_ne (k := k) (x := P.xi i - P.zeta j) (by omega)

/-- **The derivative at the top subscript.** `∂ s_P / ∂ h_{ξ₀}` is `(-1)ⁿ` times the complementary
minor of the entry `(0, n)`, the Jacobi–Trudi determinant with `ξ_{i+1} - ζ_i` on the
diagonal. -/
theorem pderiv_schur_top (P : Profile n) :
    pderiv P.topVar P.schur =
      (-1) ^ n * betaDet (fun i : Fin n => P.xi i.succ) (fun i : Fin n => P.zeta i.castSucc) := by
  have hL := P.topVar_coe
  set A : Matrix (Fin (n + 1)) (Fin (n + 1)) Lambda :=
    Matrix.of fun i j : Fin (n + 1) => hh (P.xi i - P.zeta j) with hA
  have hminor : ∀ j : Fin (n + 1),
      pderiv P.topVar (A.submatrix Fin.succ j.succAbove).det = 0 := by
    intro j
    apply pderiv_det_eq_zero
    intro i j'
    have h1 : P.xi i.succ < P.xi 0 := P.xi_strictAnti (Fin.succ_pos i)
    have h2 := P.zeta_nonneg (j.succAbove j')
    exact pderiv_hh_of_ne (k := P.topVar) (x := P.xi i.succ - P.zeta (j.succAbove j'))
      (by omega)
  have hrow : ∀ j : Fin (n + 1), j ≠ Fin.last n → pderiv P.topVar (A 0 j) = 0 := by
    intro j hj
    apply pderiv_hh_of_ne
    intro h
    exact hj (P.xi_sub_zeta_eq_top (i := 0) (j := j) (by omega)).2
  have hlast : A 0 (Fin.last n) = X P.topVar := by
    simp only [hA, Matrix.of_apply, P.zeta_last, sub_zero]
    have : P.xi 0 = (((P.topVar : ℕ+) : ℕ) : ℤ) := hL.symm
    rw [this, hh_pnat]
  have hsub : A.submatrix Fin.succ (Fin.last n).succAbove =
      Matrix.of fun i j : Fin n => hh (P.xi i.succ - P.zeta j.castSucc) := by
    ext i j
    simp [hA, Fin.succAbove_last]
  change pderiv P.topVar A.det = _
  rw [Matrix.det_succ_row_zero, map_sum, Finset.sum_eq_single (Fin.last n)]
  · rw [hlast, Derivation.leibniz, Derivation.leibniz, hminor, hsub]
    simp only [pderiv_X, Pi.single_eq_same, Fin.val_last, smul_eq_mul]
    simp only [betaDet, mul_comm]
    simp
  · intro j _ hj
    rw [Derivation.leibniz, Derivation.leibniz, hminor, hrow j hj]
    simp
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The Jacobi–Trudi matrix of `P` is the one of its beta lists. -/
theorem schur_eq_betaDet (P : Profile n) : P.schur = betaDet P.xi P.zeta := rfl

theorem betaMon_apply_rows (P : Profile n) (v : ℕ+) :
    betaMon P.xi P.zeta v = P.rowMultiset.count (v : ℕ) := by
  rw [betaMon_apply, rowMultiset]
  congr 2
  funext i
  have := P.xi_sub_zeta i
  omega

end Profile

/-- The number of factors `h_k` (with `k ≥ 1`) of a monomial. -/
noncomputable def factorCount : (ℕ+ →₀ ℕ) →+ ℕ :=
  Finsupp.liftAddHom fun _ : ℕ+ => AddMonoidHom.mulRight 1

theorem factorCount_hExp_of_pos {a : ℕ} (h : 0 < a) : factorCount (hExp a) = 1 := by
  rw [hExp, dite_eq_left h]
  simp [factorCount]

namespace Profile

variable {m n : ℕ}

theorem factorCount_betaMon (P : Profile n) : factorCount (betaMon P.xi P.zeta) = n + 1 := by
  rw [betaMon, map_sum]
  have : ∀ i, factorCount (hExp (P.xi i - P.zeta i).toNat) = 1 := fun i =>
    factorCount_hExp_of_pos (by have := P.r_pos i; have := P.xi_sub_zeta i; omega)
  simp [this]

/-- Schur-equal profiles have the same number of rows and the same multiset of row lengths:
the diagonal monomial `∏ h_{r_i}` is the unique monomial of least weight. -/
theorem rows_eq_of_schur_eq {P : Profile m} {Q : Profile n} (h : P.schur = Q.schur) :
    m = n ∧ P.rowMultiset = Q.rowMultiset := by
  have hmon : betaMon P.xi P.zeta = betaMon Q.xi Q.zeta :=
    betaMon_eq_of_betaDet_eq P.xi_strictAnti P.zeta_strictAnti
      (fun i => by have := P.xi_sub_zeta i; have := P.r_pos i; omega)
      Q.xi_strictAnti Q.zeta_strictAnti
      (fun i => by have := Q.xi_sub_zeta i; have := Q.r_pos i; omega) h
  have hmn : m = n := by
    have := congrArg factorCount hmon
    rw [factorCount_betaMon, factorCount_betaMon] at this
    omega
  subst hmn
  refine ⟨rfl, multiset_eq_of_count_pnat (fun v => ?_) ?_⟩
  · rw [← betaMon_apply_rows, ← betaMon_apply_rows, hmon]
  · simp [rowMultiset]

/-- The complementary minor of the top entry: the beta lists `ξ_{i+1}`, `ζ_i` for `i < n`. -/
theorem minor_strictAnti (P : Profile n) :
    StrictAnti (fun i : Fin n => P.xi i.succ) ∧ StrictAnti (fun i : Fin n => P.zeta i.castSucc) :=
  ⟨P.xi_strictAnti.comp_strictMono (Fin.strictMono_succ),
    P.zeta_strictAnti.comp_strictMono (Fin.strictMono_castSucc)⟩

theorem minor_ne_zero (P : Profile n) :
    betaDet (fun i : Fin n => P.xi i.succ) (fun i : Fin n => P.zeta i.castSucc) ≠ 0 := by
  intro h0
  have := (betaDet_extremal (ξ := fun i : Fin n => P.xi i.succ)
    (ζ := fun i : Fin n => P.zeta i.castSucc) P.minor_strictAnti.1 P.minor_strictAnti.2
    (fun i => P.zeta_le_xi_succ i)).1
  rw [h0] at this
  simp at this

theorem betaMon_apply_gaps (P : Profile n) (v : ℕ+) :
    betaMon (fun i : Fin n => P.xi i.succ) (fun i : Fin n => P.zeta i.castSucc) v
      = P.gapMultiset.count (v : ℕ) := by
  rw [betaMon_apply, gapMultiset]
  congr 2
  funext i
  have := P.xi_succ_sub_zeta_castSucc i
  omega

/-- Schur-equal profiles have the same top subscript `ξ₀`: it is the largest `k` such that
`∂ s_P / ∂ h_k` is nonzero. -/
theorem topVar_eq_of_schur_eq {P Q : Profile n} (h : P.schur = Q.schur) :
    P.topVar = Q.topVar := by
  have key : ∀ {P Q : Profile n}, P.schur = Q.schur → ¬ P.topVar < Q.topVar := by
    intro P Q h hlt
    have hgt : P.xi 0 < (((Q.topVar : ℕ+) : ℕ) : ℤ) := by
      rw [← P.topVar_coe]
      exact_mod_cast hlt
    have h1 := P.pderiv_schur_of_gt hgt
    rw [h, pderiv_schur_top] at h1
    exact Q.minor_ne_zero ((mul_eq_zero.mp h1).resolve_left (pow_ne_zero _ (by simp)))
  exact le_antisymm (not_lt.mp (key h.symm)) (not_lt.mp (key h))

/-- Schur-equal profiles with the same number of rows have the same multiset of overlaps. -/
theorem gaps_eq_of_schur_eq {P Q : Profile n} (h : P.schur = Q.schur) :
    P.gapMultiset = Q.gapMultiset := by
  have htop := topVar_eq_of_schur_eq h
  have h1 := pderiv_schur_top P
  have h2 := pderiv_schur_top Q
  rw [htop, h, h2] at h1
  have hmin := mul_left_cancel₀ (pow_ne_zero n (by simp : (-1 : Lambda) ≠ 0)) h1.symm
  have hmon := betaMon_eq_of_betaDet_eq P.minor_strictAnti.1 P.minor_strictAnti.2
    (fun i => P.zeta_le_xi_succ i) Q.minor_strictAnti.1 Q.minor_strictAnti.2
    (fun i => Q.zeta_le_xi_succ i) hmin
  refine multiset_eq_of_count_pnat (fun v => ?_) ?_
  · rw [← betaMon_apply_gaps, ← betaMon_apply_gaps, hmon]
  · simp [gapMultiset]

end Profile

/-- **`ReinerRowInvariants`** (Reiner–Shaw–van Willigenburg, Cor. 8.11 for connected diagrams):
connected diagrams with the same skew Schur function have the same number of rows, the same
multiset of row lengths and the same multiset of adjacent overlaps.

Proved by the extremal-monomial argument of this module, not by the Littlewood–Richardson
expansion used in the reference. -/
theorem reinerRowInvariants : ReinerRowInvariants := by
  intro m n P Q h
  obtain ⟨hmn, hrows⟩ := Profile.rows_eq_of_schur_eq h
  subst hmn
  exact ⟨rfl, hrows, Profile.gaps_eq_of_schur_eq h⟩

/-! ### Checks on the three-cell diagrams -/

/-- The hook `(2,1)` and its rotation have the same row lengths and overlaps, as the theorem
requires of the equal functions `schur_hook`, `schur_hookRotated`. -/
example : hookProfile.rowMultiset = hookRotatedProfile.rowMultiset ∧
    hookProfile.gapMultiset = hookRotatedProfile.gapMultiset := by
  decide +kernel

/-- The row `(3)` and the column `(1,1,1)` have different functions and different invariants. -/
example : rowProfile.rowMultiset ≠ columnProfile.rowMultiset := by decide +kernel

/-- The top subscript of the hook is `ξ₀ = 3`. -/
example : hookProfile.xi 0 = 3 := by decide

end SkewJacobiNegative.Gluing
