-- TODO-COPIED from skew-factor-gluing/lean/SkewGluing/Irreducibility.lean
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Data.Int.Notation
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Rat.Init
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Common
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import GluingCore.RowInvariants
import Shields.LinearAlgebra.Matrix.DesnanotJacobi

/-!
# Irreducibility of the skew Schur function of a connected diagram

Formalizes `shields-2026-skew-factor-gluing.tex`, «Local common-factor gluing»
(`sec:gluing`) and «Source-minimal fibers» (`sec:minimal-fibers`): the literature input, cited
in the paragraph on profiles and Jacobi--Trudi, that the skew Schur function of a connected
diagram is irreducible in `Λ`.

The proof is the induction on the number of rows of the Barekat--Reiner--van Willigenburg
corrigendum (Thm. 1), run directly over `ℚ`: the Jacobi--Trudi determinant is linear in the
variable `h_L` of largest index `L = ξ_0 - ζ_last`; an irreducible factor free of `h_L` divides
the coefficient and the remainder, hence by Desnanot--Jacobi condensation one of the two
row-deleted determinants, which are irreducible by induction and have larger weighted degree than
the coefficient.  Nonvanishing of the determinants (the coefficient, and the whole determinant)
comes from the monomial `∏ h_{ξ_i - ζ_i}` having coefficient `1` (`betaDet_extremal` of
`GluingCore.RowInvariants`): among the terms of the determinant it is the unique one maximizing
`∑ ξ_{σ i} ζ_i` (rearrangement inequality), so no other term has the same sum of squares of
indices.

* `irreducible_schur`: every `Profile.schur` is irreducible.
* `barekatIrreducibility`: the proposition `BarekatIrreducibility`.

Sorry-free.
-/

namespace GluingCore

open MvPolynomial

/-! ### Weighted degree -/

/-- The weight of the variable `h_k` is `k`. -/
def lambdaWeight : ℕ+ → ℕ := fun k => (k : ℕ)

/-- A weighted homogeneous polynomial of degree `dp` is not divisible by a nonzero weighted
homogeneous polynomial of larger degree. -/
theorem not_dvd_of_weightedDegree_lt {p q : Lambda} {dp dq : ℕ}
    (hp : IsWeightedHomogeneous lambdaWeight p dp) (hq : IsWeightedHomogeneous lambdaWeight q dq)
    (hlt : dp < dq) (hp0 : p ≠ 0) : ¬ q ∣ p := by
  rintro ⟨u, rfl⟩
  apply hp0
  ext d
  show _ = (0 : Lambda).coeff d
  rw [show (0 : Lambda).coeff d = 0 from rfl]
  by_contra hne
  have hw := hp hne
  rw [coeff_mul] at hne
  obtain ⟨x, hx, hx0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have h1 : q.coeff x.1 ≠ 0 := left_ne_zero_of_mul hx0
  have h2 := hq h1
  have hsum : x.1 + x.2 = d := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  have : Finsupp.weight lambdaWeight d =
      Finsupp.weight lambdaWeight x.1 + Finsupp.weight lambdaWeight x.2 := by
    rw [← hsum, map_add]
  omega

/-! ### The entries `h_j` -/

theorem hh_isWeightedHomogeneous (j : ℤ) :
    IsWeightedHomogeneous lambdaWeight (hh j) j.toNat := by
  by_cases hj : j < 0
  · rw [hh_of_neg hj]
    exact isWeightedHomogeneous_zero _ _ _
  · simp only [hh, hj, ite_false, hPos]
    split_ifs with h
    · have := isWeightedHomogeneous_X ℚ lambdaWeight ⟨j.toNat, h⟩
      simpa [lambdaWeight] using this
    · have h0 : j.toNat = 0 := by omega
      rw [h0]
      exact isWeightedHomogeneous_one _ _

/-- `h_j` does not involve the variable `h_L` for `j ≠ L`. -/
theorem hh_mem_supported (j : ℤ) (L : ℕ+) (hj : j ≠ (L : ℕ)) :
    hh j ∈ supported ℚ {k : ℕ+ | k ≠ L} := by
  by_cases hneg : j < 0
  · rw [hh_of_neg hneg]; exact Subalgebra.zero_mem _
  · simp only [hh, hneg, ite_false, hPos]
    split_ifs with h
    · refine (X_mem_supported (R := ℚ)).2 ?_
      intro hk
      apply hj
      have : (L : ℕ) = j.toNat := by rw [← hk]; rfl
      omega
    · exact Subalgebra.one_mem _

/-! ### Jacobi--Trudi matrices of two integer lists -/

/-- The Jacobi--Trudi matrix `(h_{ξ_i - ζ_j})` of two integer lists. -/
noncomputable def jtMatrix {k : ℕ} (ξ ζ : Fin k → ℤ) : Matrix (Fin k) (Fin k) Lambda :=
  Matrix.of fun i j => hh (ξ i - ζ j)

theorem schur_eq_det_jtMatrix {n : ℕ} (P : Profile n) :
    P.schur = (jtMatrix P.xi P.zeta).det := rfl

/-- The determinant of a Jacobi--Trudi matrix is weighted homogeneous of degree
`∑ ξ_i - ∑ ζ_i`. -/
theorem det_jtMatrix_isWeightedHomogeneous {k : ℕ} (ξ ζ : Fin k → ℤ) (d : ℕ)
    (hd : (d : ℤ) = ∑ i, ξ i - ∑ i, ζ i) :
    IsWeightedHomogeneous lambdaWeight (jtMatrix ξ ζ).det d := by
  rw [Matrix.det_apply]
  refine IsWeightedHomogeneous.sum _ _ _ fun σ _ => ?_
  have hprod : IsWeightedHomogeneous lambdaWeight (∏ i, jtMatrix ξ ζ (σ i) i) d := by
    by_cases hneg : ∃ i, ξ (σ i) - ζ i < 0
    · obtain ⟨i, hi⟩ := hneg
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [jtMatrix, hh_of_neg hi])]
      exact isWeightedHomogeneous_zero _ _ _
    · push Not at hneg
      have := IsWeightedHomogeneous.prod Finset.univ (fun i => jtMatrix ξ ζ (σ i) i)
        (fun i => (ξ (σ i) - ζ i).toNat) (fun i _ => hh_isWeightedHomogeneous _)
      have hsum : (d : ℤ) = ∑ i, ((ξ (σ i) - ζ i).toNat : ℤ) := by
        rw [hd, Finset.sum_congr rfl fun i _ => Int.toNat_of_nonneg (hneg i),
          Finset.sum_sub_distrib, Equiv.sum_comp σ ξ]
      have hsum' : d = ∑ i, (ξ (σ i) - ζ i).toNat := by exact_mod_cast hsum
      rw [hsum']
      exact this
  rw [Units.smul_def]
  exact zsmul_mem (K := weightedHomogeneousSubmodule ℚ lambdaWeight d) hprod _

/-! ### Nonvanishing of the determinant -/

/-- The determinant of the Jacobi--Trudi matrix of two strictly decreasing lists with `ζ ≤ ξ` is
nonzero: the diagonal monomial has coefficient one (`betaDet_extremal`). -/
theorem det_jtMatrix_ne_zero {k : ℕ} {ξ ζ : Fin k → ℤ} (hξ : StrictAnti ξ) (hζ : StrictAnti ζ)
    (hle : ∀ i, ζ i ≤ ξ i) : (jtMatrix ξ ζ).det ≠ 0 := by
  intro h
  have h1 := (betaDet_extremal hξ hζ hle).1
  have h2 : betaDet ξ ζ = 0 := h
  rw [h2] at h1
  simp at h1

/-! ### Subalgebra membership of determinants -/

theorem det_mem_subalgebra {k : ℕ} (S : Subalgebra ℚ Lambda) (M : Matrix (Fin k) (Fin k) Lambda)
    (h : ∀ i j, M i j ∈ S) : M.det ∈ S := by
  rw [Matrix.det_apply']
  refine Subalgebra.sum_mem _ fun σ _ => Subalgebra.mul_mem _ (Subalgebra.intCast_mem _ _) ?_
  exact Subalgebra.prod_mem _ fun i _ => h _ _

theorem jtMatrix_submatrix {k l : ℕ} (ξ ζ : Fin k → ℤ) (f g : Fin l → Fin k) :
    (jtMatrix ξ ζ).submatrix f g = jtMatrix (ξ ∘ f) (ζ ∘ g) := rfl

/-! ### The variable of largest index -/

/-- The entries of the Jacobi--Trudi matrix other than the top right corner do not involve the
variable `h_L`, `L = ξ_0 - ζ_last`. -/
theorem jtMatrix_entry_mem {m : ℕ} {ξ ζ : Fin (m + 1) → ℤ} (hξ : StrictAnti ξ) (hζ : StrictAnti ζ)
    (L : ℕ+) (hL : ((L : ℕ) : ℤ) = ξ 0 - ζ (Fin.last m)) (i j : Fin (m + 1))
    (hij : i ≠ 0 ∨ j ≠ Fin.last m) : jtMatrix ξ ζ i j ∈ supported ℚ {k : ℕ+ | k ≠ L} := by
  refine hh_mem_supported _ L ?_
  have h1 : ξ i ≤ ξ 0 := hξ.antitone (Fin.zero_le i)
  have h2 : ζ (Fin.last m) ≤ ζ j := hζ.antitone (Fin.le_last j)
  have h3 : ξ i - ζ j < ξ 0 - ζ (Fin.last m) := by
    rcases hij with h | h
    · have := hξ (Fin.pos_iff_ne_zero.mpr h)
      omega
    · have := hζ (lt_of_le_of_ne (Fin.le_last j) h)
      omega
  omega

/-- The determinant of a Jacobi--Trudi matrix is linear in the variable `h_L` of largest index,
`L = ξ_0 - ζ_last`; the coefficient is the signed minor omitting the first row and last column. -/
theorem det_jtMatrix_decomp {m : ℕ} {ξ ζ : Fin (m + 2) → ℤ} (hξ : StrictAnti ξ)
    (hζ : StrictAnti ζ) (L : ℕ+) (hL : ((L : ℕ) : ℤ) = ξ 0 - ζ (Fin.last (m + 1))) :
    ∃ r ∈ supported ℚ {k : ℕ+ | k ≠ L},
      (jtMatrix ξ ζ).det =
        (-1) ^ (m + 1) * (jtMatrix (ξ ∘ Fin.succ) (ζ ∘ Fin.castSucc)).det * X L + r := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_castSucc]
  refine ⟨∑ j : Fin (m + 1), (-1) ^ (j.castSucc : ℕ) * jtMatrix ξ ζ 0 j.castSucc *
    ((jtMatrix ξ ζ).submatrix Fin.succ j.castSucc.succAbove).det, ?_, ?_⟩
  · refine Subalgebra.sum_mem _ fun j _ => Subalgebra.mul_mem _ (Subalgebra.mul_mem _ ?_ ?_) ?_
    · exact Subalgebra.pow_mem _ (Subalgebra.neg_mem _ (Subalgebra.one_mem _)) _
    · exact jtMatrix_entry_mem hξ hζ L hL 0 _ (Or.inr (Fin.castSucc_lt_last j).ne)
    · refine det_mem_subalgebra _ _ fun i i' => ?_
      exact jtMatrix_entry_mem hξ hζ L hL _ _ (Or.inl (Fin.succ_ne_zero i))
  · have hX : jtMatrix ξ ζ 0 (Fin.last (m + 1)) = X L := by
      have : ξ 0 - ζ (Fin.last (m + 1)) = ((L : ℕ) : ℤ) := hL.symm
      simp only [jtMatrix, Matrix.of_apply, this]
      exact hh_pnat L
    rw [hX, Fin.succAbove_last, jtMatrix_submatrix, Fin.val_last]
    ring

/-! ### Irreducibility of a polynomial linear in one variable -/

theorem notMem_vars_of_mem_supported {p : Lambda} {L : ℕ+}
    (hp : p ∈ supported ℚ {k : ℕ+ | k ≠ L}) : L ∉ p.vars := fun h => by
  have := (mem_supported.mp hp) (Finset.mem_coe.mpr h)
  exact this rfl

/-- If `D = s h_L + r` with `s`, `r` free of `h_L`, and no irreducible polynomial free of `h_L`
divides both `D` and `s`, then `D` is irreducible (provided it is nonzero, not a unit). -/
theorem irreducible_of_linear {L : ℕ+} {s r D : Lambda}
    (hs : s ∈ supported ℚ {k : ℕ+ | k ≠ L}) (hr : r ∈ supported ℚ {k : ℕ+ | k ≠ L})
    (hD : D = s * X L + r) (hD0 : D ≠ 0) (hDu : ¬ IsUnit D)
    (hkey : ∀ f : Lambda, Irreducible f → L ∉ f.vars → f ∣ D → f ∣ s → False) :
    Irreducible D := by
  have hsL : s.degreeOf L = 0 := by
    by_contra h
    exact notMem_vars_of_mem_supported hs (mem_vars_iff_degreeOf_ne_zero.mpr h)
  have hrL : r.degreeOf L = 0 := by
    by_contra h
    exact notMem_vars_of_mem_supported hr (mem_vars_iff_degreeOf_ne_zero.mpr h)
  have hDdeg : D.degreeOf L ≤ 1 := by
    rw [hD]
    refine (degreeOf_add_le _ _ _).trans (max_le ?_ (by omega))
    refine (degreeOf_mul_le _ _ _).trans ?_
    simp [hsL]
  -- a nonunit divisor of `D` free of `h_L` is impossible
  have hfree : ∀ b : Lambda, b ∣ D → ¬ IsUnit b → b.degreeOf L = 0 → False := by
    intro b hbD hbu hb0
    obtain ⟨c, hc⟩ := hbD
    have hb : b ≠ 0 := left_ne_zero_of_mul (hc ▸ hD0)
    obtain ⟨f, hf, hfb⟩ := WfDvdMonoid.exists_irreducible_factor hbu hb
    obtain ⟨e, he⟩ := hfb
    have hf0 : f ≠ 0 := hf.ne_zero
    have he0 : e ≠ 0 := right_ne_zero_of_mul (he ▸ hb)
    have hfL : f.degreeOf L = 0 := by
      have := degreeOf_mul_eq (n := L) hf0 he0
      rw [← he, hb0] at this
      omega
    have hfvars : L ∉ f.vars := fun h => by
      have := mem_vars_iff_degreeOf_ne_zero.mp h
      exact this hfL
    have hfD : f ∣ D := ⟨e * c, by rw [hc, he, mul_assoc]⟩
    refine hkey f hf hfvars hfD ?_
    obtain ⟨g, hg⟩ := hfD
    have hd := congrArg (pderiv L) hg
    rw [Derivation.leibniz, pderiv_eq_zero_of_notMem_vars hfvars] at hd
    have hds : pderiv L D = s := by
      rw [hD, map_add, Derivation.leibniz, pderiv_eq_zero_of_notMem_vars
        (notMem_vars_of_mem_supported hs), pderiv_eq_zero_of_notMem_vars
        (notMem_vars_of_mem_supported hr)]
      simp
    rw [hds] at hd
    refine ⟨pderiv L g, ?_⟩
    rw [hd]
    simp
  rw [irreducible_iff]
  refine ⟨hDu, fun a b hab => ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨hau, hbu⟩ := hcon
  have ha0 : a ≠ 0 := left_ne_zero_of_mul (hab ▸ hD0)
  have hb0 : b ≠ 0 := right_ne_zero_of_mul (hab ▸ hD0)
  have hsum := degreeOf_mul_eq (n := L) ha0 hb0
  rw [← hab] at hsum
  by_cases hbd : b.degreeOf L = 0
  · exact hfree b ⟨a, by rw [hab, mul_comm]⟩ hbu hbd
  · exact hfree a ⟨b, hab⟩ hau (by omega)

/-! ### Removing the first or last row of a profile -/

namespace Profile

variable {m : ℕ}

/-- The profile of the diagram with the first row removed. -/
def dropFirst (P : Profile (m + 1)) : Profile m where
  r i := P.r i.succ
  g j := P.g j.succ
  r_pos i := P.r_pos _
  g_lt_castSucc j := by
    have := P.g_lt_castSucc j.succ
    rwa [← Fin.succ_castSucc] at this
  g_lt_succ j := P.g_lt_succ j.succ

/-- The profile of the diagram with the last row removed. -/
def dropLast (P : Profile (m + 1)) : Profile m where
  r i := P.r i.castSucc
  g j := P.g j.castSucc
  r_pos i := P.r_pos _
  g_lt_castSucc j := P.g_lt_castSucc j.castSucc
  g_lt_succ j := by
    have := P.g_lt_succ j.castSucc
    rwa [Fin.succ_castSucc] at this

theorem xi_zeta_dropFirst (P : Profile (m + 1)) (i : Fin (m + 1)) :
    P.dropFirst.xi i = P.xi i.succ ∧ P.dropFirst.zeta i = P.zeta i.succ := by
  have key := P.dropFirst.eq_beta_of_equations (x := fun i => P.xi i.succ)
    (z := fun i => P.zeta i.succ) (by simpa using P.zeta_last) (fun i => P.xi_sub_zeta i.succ)
    (fun j => by
      have := P.xi_succ_sub_zeta_castSucc j.succ
      rw [← Fin.succ_castSucc] at this
      exact this)
  exact ⟨congrFun key.1.symm i, congrFun key.2.symm i⟩

theorem xi_zeta_dropLast (P : Profile (m + 1)) (i : Fin (m + 1)) :
    P.dropLast.xi i = P.xi i.castSucc - P.zeta (Fin.last m).castSucc ∧
      P.dropLast.zeta i = P.zeta i.castSucc - P.zeta (Fin.last m).castSucc := by
  have key := P.dropLast.eq_beta_of_equations
    (x := fun i => P.xi i.castSucc - P.zeta (Fin.last m).castSucc)
    (z := fun i => P.zeta i.castSucc - P.zeta (Fin.last m).castSucc) (by simp)
    (fun i => by have := P.xi_sub_zeta i.castSucc; simp only [dropLast]; omega)
    (fun j => by
      have := P.xi_succ_sub_zeta_castSucc j.castSucc
      rw [Fin.succ_castSucc] at this
      simp only [dropLast]
      omega)
  exact ⟨congrFun key.1.symm i, congrFun key.2.symm i⟩

theorem schur_dropFirst (P : Profile (m + 1)) :
    P.dropFirst.schur = ((jtMatrix P.xi P.zeta).submatrix Fin.succ Fin.succ).det := by
  rw [schur_eq_det_jtMatrix, jtMatrix_submatrix]
  congr 1
  ext i j
  simp [jtMatrix, (xi_zeta_dropFirst P i).1, (xi_zeta_dropFirst P j).2]

theorem schur_dropLast (P : Profile (m + 1)) :
    P.dropLast.schur = ((jtMatrix P.xi P.zeta).submatrix Fin.castSucc Fin.castSucc).det := by
  rw [schur_eq_det_jtMatrix, jtMatrix_submatrix]
  congr 1
  ext i j
  simp only [jtMatrix, Matrix.of_apply, Function.comp_apply, (xi_zeta_dropLast P i).1,
    (xi_zeta_dropLast P j).2, sub_sub_sub_cancel_right]

end Profile

/-! ### The induction on the number of rows -/

/-- The determinant of a Jacobi--Trudi matrix with `ζ ≤ ξ` entrywise on the diagonal is weighted
homogeneous of degree `∑ ξ_i - ∑ ζ_i`. -/
theorem det_jtMatrix_isWeightedHomogeneous_toNat {k : ℕ} (ξ ζ : Fin k → ℤ)
    (hle : ∀ i, ζ i ≤ ξ i) :
    IsWeightedHomogeneous lambdaWeight (jtMatrix ξ ζ).det (∑ i, ξ i - ∑ i, ζ i).toNat := by
  refine det_jtMatrix_isWeightedHomogeneous ξ ζ _ ?_
  have : 0 ≤ ∑ i, ξ i - ∑ i, ζ i := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_nonneg fun i _ => by have := hle i; omega
  omega

theorem irreducible_schur_succ (m : ℕ) (ih : ∀ Q : Profile m, Irreducible Q.schur)
    (P : Profile (m + 1)) : Irreducible P.schur := by
  have hξ := P.xi_strictAnti
  have hζ := P.zeta_strictAnti
  have hle : ∀ i, P.zeta i ≤ P.xi i := fun i => by
    have := P.xi_sub_zeta i
    have := P.r_pos i
    omega
  have hξs : StrictAnti (P.xi ∘ Fin.succ) := hξ.comp_strictMono (Fin.strictMono_succ)
  have hζc : StrictAnti (P.zeta ∘ Fin.castSucc) := hζ.comp_strictMono (Fin.strictMono_castSucc)
  have hxpos := P.xi_pos 0
  have hz0 := P.zeta_last
  set L : ℕ+ := Nat.toPNat (P.xi 0).toNat (by omega) with hLdef
  have hL : ((L : ℕ) : ℤ) = P.xi 0 - P.zeta (Fin.last (m + 1)) := by
    rw [hz0]
    have : ((L : ℕ) : ℤ) = ((P.xi 0).toNat : ℤ) := rfl
    omega
  obtain ⟨r, hr, hD⟩ := det_jtMatrix_decomp (m := m) hξ hζ L hL
  set A := jtMatrix P.xi P.zeta with hA
  set M := (jtMatrix (P.xi ∘ Fin.succ) (P.zeta ∘ Fin.castSucc)).det with hM
  have hMmem : M ∈ supported ℚ {k : ℕ+ | k ≠ L} := by
    refine det_mem_subalgebra _ _ fun i j => ?_
    exact jtMatrix_entry_mem hξ hζ L hL i.succ j.castSucc (Or.inl (Fin.succ_ne_zero i))
  have hM0 : M ≠ 0 :=
    det_jtMatrix_ne_zero hξs hζc fun i => P.zeta_le_xi_succ i
  have hD0 : A.det ≠ 0 := det_jtMatrix_ne_zero hξ hζ hle
  have hsmem : (-1 : Lambda) ^ (m + 1) * M ∈ supported ℚ {k : ℕ+ | k ≠ L} :=
    Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (Subalgebra.neg_mem _ (Subalgebra.one_mem _)) _)
      hMmem
  -- degrees
  have hsumξ : ∑ i, P.xi i = P.xi 0 + ∑ i : Fin (m + 1), P.xi i.succ := Fin.sum_univ_succ _
  have hsumζ : ∑ i, P.zeta i = P.zeta 0 + ∑ i : Fin (m + 1), P.zeta i.succ := Fin.sum_univ_succ _
  have hsumξ' : ∑ i, P.xi i = ∑ i : Fin (m + 1), P.xi i.castSucc + P.xi (Fin.last (m + 1)) :=
    Fin.sum_univ_castSucc _
  have hsumζ' : ∑ i, P.zeta i
      = ∑ i : Fin (m + 1), P.zeta i.castSucc + P.zeta (Fin.last (m + 1)) :=
    Fin.sum_univ_castSucc _
  have hζ01 : P.zeta (Fin.last (m + 1)) < P.zeta 0 :=
    hζ (Fin.pos_iff_ne_zero.mpr (Fin.last_pos).ne')
  have hξ01 : P.xi (Fin.last (m + 1)) < P.xi 0 := hξ (Fin.last_pos)
  have hMhom := det_jtMatrix_isWeightedHomogeneous_toNat (P.xi ∘ Fin.succ)
    (P.zeta ∘ Fin.castSucc) fun i => P.zeta_le_xi_succ i
  have hEhom := det_jtMatrix_isWeightedHomogeneous_toNat (P.xi ∘ Fin.succ) (P.zeta ∘ Fin.succ)
    fun i => hle i.succ
  have hFhom := det_jtMatrix_isWeightedHomogeneous_toNat (P.xi ∘ Fin.castSucc)
    (P.zeta ∘ Fin.castSucc) fun i => hle i.castSucc
  have hDhom := det_jtMatrix_isWeightedHomogeneous_toNat P.xi P.zeta hle
  simp only [Function.comp_apply] at hMhom hEhom hFhom
  have hnonneg1 : 0 ≤ ∑ i : Fin (m + 1), P.xi i.succ - ∑ i : Fin (m + 1), P.zeta i.castSucc := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_nonneg fun i _ => by have := P.zeta_le_xi_succ i; omega
  have hnonneg2 : 0 ≤ ∑ i : Fin (m + 1), P.xi i.succ - ∑ i : Fin (m + 1), P.zeta i.succ := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_nonneg fun i _ => by have := hle i.succ; omega
  have hnonneg3 : 0 ≤ ∑ i : Fin (m + 1), P.xi i.castSucc
      - ∑ i : Fin (m + 1), P.zeta i.castSucc := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_nonneg fun i _ => by have := hle i.castSucc; omega
  have hlt_E : (∑ i : Fin (m + 1), P.xi i.succ - ∑ i : Fin (m + 1), P.zeta i.castSucc).toNat
      < (∑ i : Fin (m + 1), P.xi i.succ - ∑ i : Fin (m + 1), P.zeta i.succ).toNat := by omega
  have hlt_F : (∑ i : Fin (m + 1), P.xi i.succ - ∑ i : Fin (m + 1), P.zeta i.castSucc).toNat
      < (∑ i : Fin (m + 1), P.xi i.castSucc - ∑ i : Fin (m + 1), P.zeta i.castSucc).toNat := by
    omega
  have hDpos : 0 < (∑ i, P.xi i - ∑ i, P.zeta i).toNat := by
    have : 0 < ∑ i, P.xi i - ∑ i, P.zeta i := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_pos (fun i _ => by have := P.r_pos i; have := P.xi_sub_zeta i; omega)
        Finset.univ_nonempty
    omega
  have hDnu : ¬ IsUnit A.det := by
    intro hu
    exact not_dvd_of_weightedDegree_lt (isWeightedHomogeneous_one ℚ lambdaWeight) hDhom hDpos
      one_ne_zero hu.dvd
  rw [schur_eq_det_jtMatrix]
  refine irreducible_of_linear hsmem hr hD hD0 hDnu ?_
  intro f hf hfvars hfD hfs
  have hfM : f ∣ M := by
    have hu : IsUnit ((-1 : Lambda) ^ (m + 1)) := (isUnit_one.neg).pow _
    exact (hu.dvd_mul_left).mp hfs
  have hDJ := Shields.desnanot_jacobi A
  have hfEF : f ∣ (A.submatrix Fin.succ Fin.succ).det * (A.submatrix Fin.castSucc Fin.castSucc).det
      := by
    have : (A.submatrix Fin.succ Fin.succ).det * (A.submatrix Fin.castSucc Fin.castSucc).det
        = A.det * (A.submatrix (fun i : Fin m => i.castSucc.succ)
          fun j : Fin m => j.castSucc.succ).det
          + (A.submatrix Fin.succ Fin.castSucc).det * (A.submatrix Fin.castSucc Fin.succ).det := by
      linear_combination -hDJ
    rw [this]
    exact dvd_add (hfD.mul_right _) (hfM.mul_right _)
  have hfprime := (UniqueFactorizationMonoid.irreducible_iff_prime.mp hf)
  rcases hfprime.dvd_or_dvd hfEF with hfE | hfF
  · have hEirr := ih P.dropFirst
    rw [Profile.schur_dropFirst] at hEirr
    have hass := hf.associated_of_dvd hEirr hfE
    refine not_dvd_of_weightedDegree_lt hMhom hEhom hlt_E hM0 ?_
    exact hass.symm.dvd.trans hfM
  · have hFirr := ih P.dropLast
    rw [Profile.schur_dropLast] at hFirr
    have hass := hf.associated_of_dvd hFirr hfF
    refine not_dvd_of_weightedDegree_lt hMhom hFhom hlt_F hM0 ?_
    exact hass.symm.dvd.trans hfM

/-- A one-row profile gives the variable `h_r`, which is irreducible. -/
theorem irreducible_schur_zero (P : Profile 0) : Irreducible P.schur := by
  have h0 : P.zeta 0 = 0 := P.zeta_last
  have h1 : P.xi 0 = P.r 0 := by have := P.xi_sub_zeta 0; omega
  have hpos := P.r_pos 0
  have : P.schur = X (Nat.toPNat (P.r 0) hpos) := by
    rw [schur_eq_det_jtMatrix, Matrix.det_fin_one]
    simp only [jtMatrix, Matrix.of_apply, h0, h1, sub_zero]
    exact hh_pnat (Nat.toPNat (P.r 0) hpos)
  rw [this]
  exact (X_prime).irreducible

/-- **The skew Schur function of a connected diagram is irreducible in `Λ`**
(Barekat--Reiner--van Willigenburg corrigendum, Thm. 1): by induction on the number of rows,
through the Jacobi--Trudi determinant.  The determinant is linear in the variable `h_L`
of largest index `L = ξ_0 - ζ_last`; a common irreducible factor of the coefficient and the
remainder would divide one of the two row-deleted minors by Desnanot--Jacobi condensation, and
the minors are irreducible by induction while having larger weighted degree than the
coefficient.  The statement over `ℚ` is proved directly, with no transfer from `ℤ`. -/
theorem irreducible_schur : ∀ (n : ℕ) (P : Profile n), Irreducible P.schur
  | 0, P => irreducible_schur_zero P
  | n + 1, P => irreducible_schur_succ n (irreducible_schur n) P

/-- **`BarekatIrreducibility` holds.** -/
theorem barekatIrreducibility : BarekatIrreducibility := irreducible_schur

/-- Non-vacuity check: the hook `(2,1)` has irreducible skew Schur function `h₁ h₂ - h₃`. -/
example : Irreducible hookProfile.schur := irreducible_schur 1 hookProfile

end GluingCore
