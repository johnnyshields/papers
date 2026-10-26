import SkewGluing.IntegralSchur

/-!
# Connected skew Schur irreducibility over arbitrary fields

Supports `shields-2026-skew-corner-descent.tex`, «Corner cofactors and common cores»
(`sec:corner`, `lem:cofactor`).
TODO-COPIED: the row-induction argument is adapted from
`skew-factor-gluing/lean/SkewGluing/Irreducibility.lean`.
-/

namespace SkewGluing

open MvPolynomial

/-- The profile determinant specialized to an arbitrary coefficient ring. -/
noncomputable def Profile.fieldSchur {K : Type*} [CommRing K] {n : ℕ} (P : Profile n) :
    MvPolynomial ℕ+ K := map (Int.castRingHom K) P.integralSchur

namespace FieldSchur

variable {K : Type*} [Field K]

local notation "Poly" => MvPolynomial ℕ+ K

noncomputable section

/-- Positive-index generators over the chosen field. -/
def hPos (k : ℕ) : Poly := if h : 0 < k then X ⟨k, h⟩ else 1

/-- Jacobi--Trudi entry, including the zero and negative conventions. -/
def hh (j : ℤ) : Poly := if j < 0 then 0 else hPos j.toNat

@[simp]
theorem hh_of_neg {j : ℤ} (hj : j < 0) : (hh j : Poly) = 0 := by simp [hh, hj]

theorem hh_pnat (k : ℕ+) : (hh (k : ℤ) : Poly) = X k := by
  have hn : ¬ ((k : ℕ) : ℤ) < 0 := by omega
  simp only [hh, hPos, k.pos, hn, ite_false, Int.toNat_natCast, dite_true]
  rfl

/-- Integral and native field entries coincide, also in positive characteristic. -/
theorem map_integralHH (x : ℤ) :
    map (Int.castRingHom K) (SkewGluing.integralHH x) = (hh x : Poly) := by
  by_cases hx : x < 0
  · simp [SkewGluing.integralHH, hh, hx]
  · by_cases hp : 0 < x.toNat
    · simp only [SkewGluing.integralHH, hx, ite_false, map_monomial, hh, hPos,
        hExp, hp, dite_true, map_one]
      rfl
    · have hz : x.toNat = 0 := by omega
      simp [SkewGluing.integralHH, hx, hz, hExp, hh, hPos]

/-- Field Jacobi--Trudi matrix. -/
def jtMatrix {k : ℕ} (ξ ζ : Fin k → ℤ) : Matrix (Fin k) (Fin k) Poly :=
  Matrix.of fun i j => hh (ξ i - ζ j)

theorem fieldSchur_eq_det_jtMatrix {n : ℕ} (P : Profile n) :
    P.fieldSchur (K := K) = (jtMatrix P.xi P.zeta).det := by
  rw [SkewGluing.Profile.fieldSchur, SkewGluing.Profile.integralSchur,
    integralBetaDet, RingHom.map_det]
  congr 1
  funext i j
  exact map_integralHH _

/-- Nonzero in every characteristic, by the integral coefficient-one monomial. -/
theorem det_jtMatrix_ne_zero {k : ℕ} {ξ ζ : Fin k → ℤ}
    (hξ : StrictAnti ξ) (hζ : StrictAnti ζ) (hle : ∀ i, ζ i ≤ ξ i) :
    (jtMatrix ξ ζ : Matrix _ _ Poly).det ≠ 0 := by
  have he : map (Int.castRingHom K) (integralBetaDet ξ ζ) =
      (jtMatrix ξ ζ : Matrix _ _ Poly).det := by
    rw [integralBetaDet, RingHom.map_det]
    congr 1
    funext i j
    exact map_integralHH _
  rw [← he]
  exact map_integralBetaDet_ne_zero hξ hζ hle

/-- A weighted homogeneous polynomial of degree `dp` is not divisible by a nonzero weighted
homogeneous polynomial of larger degree. -/
theorem not_dvd_of_weightedDegree_lt {p q : Poly} {dp dq : ℕ}
    (hp : IsWeightedHomogeneous lambdaWeight p dp) (hq : IsWeightedHomogeneous lambdaWeight q dq)
    (hlt : dp < dq) (hp0 : p ≠ 0) : ¬ q ∣ p := by
  rintro ⟨u, rfl⟩
  apply hp0
  ext d
  change _ = (0 : Poly).coeff d
  rw [show (0 : Poly).coeff d = 0 from rfl]
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
    IsWeightedHomogeneous lambdaWeight (hh j : Poly) j.toNat := by
  by_cases hj : j < 0
  · rw [hh_of_neg hj]
    exact isWeightedHomogeneous_zero _ _ _
  · simp only [hh, hj, ite_false, hPos]
    split_ifs with h
    · have := isWeightedHomogeneous_X K lambdaWeight ⟨j.toNat, h⟩
      simpa [lambdaWeight] using this
    · have h0 : j.toNat = 0 := by omega
      rw [h0]
      exact isWeightedHomogeneous_one _ _

/-- `h_j` does not involve the variable `h_L` for `j ≠ L`. -/
theorem hh_mem_supported (j : ℤ) (L : ℕ+) (hj : j ≠ (L : ℕ)) :
    hh j ∈ supported K {k : ℕ+ | k ≠ L} := by
  by_cases hneg : j < 0
  · rw [hh_of_neg hneg]; exact Subalgebra.zero_mem _
  · simp only [hh, hneg, ite_false, hPos]
    split_ifs with h
    · refine (X_mem_supported (R := K)).2 ?_
      intro hk
      apply hj
      have : (L : ℕ) = j.toNat := by rw [← hk]; rfl
      omega
    · exact Subalgebra.one_mem _

/-- The determinant of a Jacobi--Trudi matrix is weighted homogeneous of degree
`∑ ξ_i - ∑ ζ_i`. -/
theorem det_jtMatrix_isWeightedHomogeneous {k : ℕ} (ξ ζ : Fin k → ℤ) (d : ℕ)
    (hd : (d : ℤ) = ∑ i, ξ i - ∑ i, ζ i) :
    IsWeightedHomogeneous lambdaWeight (jtMatrix (K := K) ξ ζ).det d := by
  rw [Matrix.det_apply]
  refine IsWeightedHomogeneous.sum _ _ _ fun σ _ => ?_
  have hprod : IsWeightedHomogeneous lambdaWeight (∏ i, jtMatrix (K := K) ξ ζ (σ i) i) d := by
    by_cases hneg : ∃ i, ξ (σ i) - ζ i < 0
    · obtain ⟨i, hi⟩ := hneg
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [jtMatrix, hh_of_neg hi])]
      exact isWeightedHomogeneous_zero _ _ _
    · push Not at hneg
      have := IsWeightedHomogeneous.prod Finset.univ (fun i => jtMatrix (K := K) ξ ζ (σ i) i)
        (fun i => (ξ (σ i) - ζ i).toNat) (fun i _ => hh_isWeightedHomogeneous _)
      have hsum : (d : ℤ) = ∑ i, ((ξ (σ i) - ζ i).toNat : ℤ) := by
        rw [hd, Finset.sum_congr rfl fun i _ => Int.toNat_of_nonneg (hneg i),
          Finset.sum_sub_distrib, Equiv.sum_comp σ ξ]
      have hsum' : d = ∑ i, (ξ (σ i) - ζ i).toNat := by exact_mod_cast hsum
      rw [hsum']
      exact this
  rw [Units.smul_def]
  exact zsmul_mem (K := weightedHomogeneousSubmodule K lambdaWeight d) hprod _

/-! ### Subalgebra membership of determinants -/

theorem det_mem_subalgebra {k : ℕ} (S : Subalgebra K Poly) (M : Matrix (Fin k) (Fin k) Poly)
    (h : ∀ i j, M i j ∈ S) : M.det ∈ S := by
  rw [Matrix.det_apply']
  refine Subalgebra.sum_mem _ fun σ _ => Subalgebra.mul_mem _ (Subalgebra.intCast_mem _ _) ?_
  exact Subalgebra.prod_mem _ fun i _ => h _ _

theorem jtMatrix_submatrix {k l : ℕ} (ξ ζ : Fin k → ℤ) (f g : Fin l → Fin k) :
    (jtMatrix (K := K) ξ ζ).submatrix f g = jtMatrix (ξ ∘ f) (ζ ∘ g) := rfl

/-! ### The variable of largest index -/

/-- The entries of the Jacobi--Trudi matrix other than the top right corner do not involve the
variable `h_L`, `L = ξ_0 - ζ_last`. -/
theorem jtMatrix_entry_mem {m : ℕ} {ξ ζ : Fin (m + 1) → ℤ} (hξ : StrictAnti ξ) (hζ : StrictAnti ζ)
    (L : ℕ+) (hL : ((L : ℕ) : ℤ) = ξ 0 - ζ (Fin.last m)) (i j : Fin (m + 1))
    (hij : i ≠ 0 ∨ j ≠ Fin.last m) : jtMatrix ξ ζ i j ∈ supported K {k : ℕ+ | k ≠ L} := by
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
    ∃ r ∈ supported K {k : ℕ+ | k ≠ L},
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
  · have hX : jtMatrix (K := K) ξ ζ 0 (Fin.last (m + 1)) = X L := by
      have : ξ 0 - ζ (Fin.last (m + 1)) = ((L : ℕ) : ℤ) := hL.symm
      simp only [jtMatrix, Matrix.of_apply, this]
      exact hh_pnat L
    rw [hX, Fin.succAbove_last, jtMatrix_submatrix, Fin.val_last]
    ring

/-! ### Irreducibility of a polynomial linear in one variable -/

theorem notMem_vars_of_mem_supported {p : Poly} {L : ℕ+}
    (hp : p ∈ supported K {k : ℕ+ | k ≠ L}) : L ∉ p.vars := fun h => by
  have := (mem_supported.mp hp) (Finset.mem_coe.mpr h)
  exact this rfl

/-- If `D = s h_L + r` with `s`, `r` free of `h_L`, and no irreducible polynomial free of `h_L`
divides both `D` and `s`, then `D` is irreducible (provided it is nonzero, not a unit). -/
theorem irreducible_of_linear {L : ℕ+} {s r D : Poly}
    (hs : s ∈ supported K {k : ℕ+ | k ≠ L}) (hr : r ∈ supported K {k : ℕ+ | k ≠ L})
    (hD : D = s * X L + r) (hD0 : D ≠ 0) (hDu : ¬ IsUnit D)
    (hkey : ∀ f : Poly, Irreducible f → L ∉ f.vars → f ∣ D → f ∣ s → False) :
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
  have hfree : ∀ b : Poly, b ∣ D → ¬ IsUnit b → b.degreeOf L = 0 → False := by
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

namespace Profile

variable {m : ℕ}


theorem fieldSchur_dropFirst (P : Profile (m + 1)) :
    P.dropFirst.fieldSchur (K := K) =
      ((jtMatrix P.xi P.zeta).submatrix Fin.succ Fin.succ).det := by
  rw [fieldSchur_eq_det_jtMatrix, jtMatrix_submatrix]
  congr 1
  funext i j
  simp [jtMatrix, (SkewGluing.Profile.xi_zeta_dropFirst P i).1,
    (SkewGluing.Profile.xi_zeta_dropFirst P j).2]

theorem fieldSchur_dropLast (P : Profile (m + 1)) :
    P.dropLast.fieldSchur (K := K) =
      ((jtMatrix P.xi P.zeta).submatrix Fin.castSucc Fin.castSucc).det := by
  rw [fieldSchur_eq_det_jtMatrix, jtMatrix_submatrix]
  congr 1
  funext i j
  simp only [jtMatrix, Matrix.of_apply, Function.comp_apply,
    (SkewGluing.Profile.xi_zeta_dropLast P i).1,
    (SkewGluing.Profile.xi_zeta_dropLast P j).2, sub_sub_sub_cancel_right]


end Profile


/-! ### The induction on the number of rows -/

/-- The determinant of a Jacobi--Trudi matrix with `ζ ≤ ξ` entrywise on the diagonal is weighted
homogeneous of degree `∑ ξ_i - ∑ ζ_i`. -/
theorem det_jtMatrix_isWeightedHomogeneous_toNat {k : ℕ} (ξ ζ : Fin k → ℤ)
    (hle : ∀ i, ζ i ≤ ξ i) :
    IsWeightedHomogeneous lambdaWeight (jtMatrix (K := K) ξ ζ).det
      (∑ i, ξ i - ∑ i, ζ i).toNat := by
  refine det_jtMatrix_isWeightedHomogeneous ξ ζ _ ?_
  have : 0 ≤ ∑ i, ξ i - ∑ i, ζ i := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_nonneg fun i _ => by have := hle i; omega
  omega

theorem irreducible_schur_succ (m : ℕ) (ih : ∀ Q : Profile m, Irreducible (Q.fieldSchur (K := K)))
    (P : Profile (m + 1)) : Irreducible (P.fieldSchur (K := K)) := by
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
  obtain ⟨r, hr, hD⟩ := det_jtMatrix_decomp (K := K) (m := m) hξ hζ L hL
  set A := jtMatrix (K := K) P.xi P.zeta with hA
  set M := (jtMatrix (K := K) (P.xi ∘ Fin.succ) (P.zeta ∘ Fin.castSucc)).det with hM
  have hMmem : M ∈ supported K {k : ℕ+ | k ≠ L} := by
    refine det_mem_subalgebra _ _ fun i j => ?_
    exact jtMatrix_entry_mem hξ hζ L hL i.succ j.castSucc (Or.inl (Fin.succ_ne_zero i))
  have hM0 : M ≠ 0 :=
    det_jtMatrix_ne_zero hξs hζc fun i => P.zeta_le_xi_succ i
  have hD0 : A.det ≠ 0 := det_jtMatrix_ne_zero hξ hζ hle
  have hsmem : (-1 : Poly) ^ (m + 1) * M ∈ supported K {k : ℕ+ | k ≠ L} :=
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
  have hMhom := det_jtMatrix_isWeightedHomogeneous_toNat (K := K) (P.xi ∘ Fin.succ)
    (P.zeta ∘ Fin.castSucc) fun i => P.zeta_le_xi_succ i
  have hEhom := det_jtMatrix_isWeightedHomogeneous_toNat (K := K)
    (P.xi ∘ Fin.succ) (P.zeta ∘ Fin.succ) fun i => hle i.succ
  have hFhom := det_jtMatrix_isWeightedHomogeneous_toNat (K := K) (P.xi ∘ Fin.castSucc)
    (P.zeta ∘ Fin.castSucc) fun i => hle i.castSucc
  have hDhom := det_jtMatrix_isWeightedHomogeneous_toNat (K := K) P.xi P.zeta hle
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
    exact not_dvd_of_weightedDegree_lt (isWeightedHomogeneous_one K lambdaWeight) hDhom hDpos
      one_ne_zero hu.dvd
  rw [fieldSchur_eq_det_jtMatrix]
  refine irreducible_of_linear hsmem hr hD hD0 hDnu ?_
  intro f hf hfvars hfD hfs
  have hfM : f ∣ M := by
    have hu : IsUnit ((-1 : Poly) ^ (m + 1)) := (isUnit_one.neg).pow _
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
    rw [Profile.fieldSchur_dropFirst] at hEirr
    have hass := hf.associated_of_dvd hEirr hfE
    refine not_dvd_of_weightedDegree_lt hMhom hEhom hlt_E hM0 ?_
    exact hass.symm.dvd.trans hfM
  · have hFirr := ih P.dropLast
    rw [Profile.fieldSchur_dropLast] at hFirr
    have hass := hf.associated_of_dvd hFirr hfF
    refine not_dvd_of_weightedDegree_lt hMhom hFhom hlt_F hM0 ?_
    exact hass.symm.dvd.trans hfM

/-- A one-row profile gives the variable `h_r`, which is irreducible. -/
theorem irreducible_schur_zero (P : Profile 0) : Irreducible (P.fieldSchur (K := K)) := by
  have h0 : P.zeta 0 = 0 := P.zeta_last
  have h1 : P.xi 0 = P.r 0 := by have := P.xi_sub_zeta 0; omega
  have hpos := P.r_pos 0
  have : (P.fieldSchur (K := K)) = X (Nat.toPNat (P.r 0) hpos) := by
    rw [fieldSchur_eq_det_jtMatrix, Matrix.det_fin_one]
    simp only [jtMatrix, Matrix.of_apply, h0, h1, sub_zero]
    exact hh_pnat (Nat.toPNat (P.r 0) hpos)
  rw [this]
  exact (X_prime).irreducible
/-- **Differs from the paper's route.** Induction on row count, rather than area,
uses Desnanot--Jacobi and the strictly smaller weighted degree of the complementary minor.
No characteristic-zero hypothesis is used. -/
theorem irreducible_schur : ∀ (n : ℕ) (P : SkewGluing.Profile n),
    Irreducible (P.fieldSchur (K := K))
  | 0, P => irreducible_schur_zero P
  | n + 1, P => irreducible_schur_succ n (irreducible_schur n) P

end

end FieldSchur

/-- Connected diagrams remain irreducible after specialization to any field. -/
theorem irreducible_integralConnectedSchur {K : Type*} [Field K]
    (D : Diagram) (hD : IsConnectedSkew D) :
    Irreducible (map (Int.castRingHom K) (integralConnectedSchur D hD)) :=
  FieldSchur.irreducible_schur _ _

end SkewGluing
