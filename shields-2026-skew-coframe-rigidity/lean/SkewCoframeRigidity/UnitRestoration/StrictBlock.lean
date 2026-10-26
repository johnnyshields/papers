/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.UnitRestoration.Bordered
import SkewCoframeRigidity.RowDegree
import SkewCoframeRigidity.Splice
import SkewCofactorIndependence.WeightedReadings
import SkewCoframeRigidity.Coframe.Defs
import SkewCoframeRigidity.UnitRestoration.UnitExpansion

/-!
# The strict-block step of the linearized fixed-cap induction

Formalizes the algebra of the strict-block case in the proof of `sc:linearized-cap` in
`shields-2026-skew-coframe-rigidity.tex`.  The differentiated top equation of a strict block
`E` with numerator `N = K_E ◁ E` reads `s_E ṡ_N = s_N ṡ_E`.  Here `s_E` and `s_N` are connected
skew Schur functions of different spans, hence coprime, so `s_E ∣ ṡ_E`; the quotient would have
weighted degree zero and ordinary degree one in positive-weight letters, which forces
`ṡ_E = 0` and then `ṡ_N = 0`.

* `eq_zero_of_mul_homogeneous` is the degree argument, for a weight in which every letter has
  weight at least two (the weight `k + 1` of the letter `h_k` counts the factor itself).
* `schur_isWeightedHomogeneous_of_zeroFree` and `dotS_isWeightedHomogeneous` supply the two
  degrees: `s_E` has weight `area + rows`, and a restoration `ṡ^{(b)}` at a genuine vacancy has
  weight `area + rows + 1`.
* `schur_isRelPrime_of_span_lt` is the coprimality of connected skew Schur functions of
  different spans.
* `strict_block_vanishing` is the step itself.

Sorry-free.
-/

namespace SkewCoframeRigidity.UnitRestoration

open MvPolynomial SkewCofactorIndependence

section Scaling

variable {σ : Type*} [DecidableEq σ]

/-- Scale the variable `X k` by `t ^ v k`. -/
noncomputable def scaleHom (v : σ → ℕ) (t : ℚ) : MvPolynomial σ ℚ →ₐ[ℚ] MvPolynomial σ ℚ :=
  aeval fun k => C (t ^ v k) * X k

theorem scaleHom_monomial (v : σ → ℕ) (t : ℚ) (u : σ →₀ ℕ) (a : ℚ) :
    scaleHom v t (monomial u a) = monomial u (a * t ^ Finsupp.weight v u) := by
  rw [scaleHom, aeval_monomial]
  have h1 : (u.prod fun i k => (C (t ^ v i) * X i : MvPolynomial σ ℚ) ^ k) =
      C (t ^ Finsupp.weight v u) * u.prod fun i k => (X i : MvPolynomial σ ℚ) ^ k := by
    simp only [mul_pow, Finsupp.prod_mul, ← map_pow, ← pow_mul]
    congr 1
    rw [← map_finsuppProd, Finsupp.weight_apply, Finsupp.sum, Finsupp.prod]
    congr 1
    rw [← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [smul_eq_mul, mul_comm, pow_mul]
  rw [h1, monomial_eq, algebraMap_eq]
  rw [← mul_assoc, ← C_mul]

theorem coeff_scaleHom (v : σ → ℕ) (t : ℚ) (p : MvPolynomial σ ℚ) (d : σ →₀ ℕ) :
    (scaleHom v t p).coeff d = p.coeff d * t ^ Finsupp.weight v d := by
  induction p using MvPolynomial.induction_on' with
  | monomial u a =>
    rw [scaleHom_monomial, coeff_monomial, coeff_monomial]
    by_cases h : u = d
    · subst h; simp
    · simp [h]
  | add p q hp hq =>
    have hadd : ∀ x y : MvPolynomial σ ℚ, (x + y).coeff d = x.coeff d + y.coeff d :=
      fun _ _ => rfl
    rw [map_add, hadd, hadd, hp, hq, add_mul]

theorem scaleHom_of_isWeightedHomogeneous (v : σ → ℕ) (t : ℚ) {p : MvPolynomial σ ℚ} {m : ℕ}
    (hp : IsWeightedHomogeneous v p m) : scaleHom v t p = C (t ^ m) * p := by
  ext d
  rw [coeff_scaleHom, coeff_C_mul]
  by_cases h : p.coeff d = 0
  · simp [h]
  · rw [hp h]; ring

/-- If a nonzero homogeneous `f` of weight `a` times `c` is homogeneous of weight `a + 1`, and
every letter has weight at least two, then `c = 0`: the quotient would be homogeneous of
weight one. -/
theorem eq_zero_of_mul_homogeneous (v : σ → ℕ) (hv : ∀ k, 2 ≤ v k) {f c : MvPolynomial σ ℚ}
    {a : ℕ} (hf : IsWeightedHomogeneous v f a) (hf0 : f ≠ 0)
    (hg : IsWeightedHomogeneous v (f * c) (a + 1)) : c = 0 := by
  have h1 : scaleHom v 2 (f * c) = scaleHom v 2 f * scaleHom v 2 c := map_mul _ _ _
  rw [scaleHom_of_isWeightedHomogeneous v 2 hg, scaleHom_of_isWeightedHomogeneous v 2 hf] at h1
  have e : C ((2 : ℚ) ^ (a + 1)) = (C ((2 : ℚ) ^ a) * C 2 : MvPolynomial σ ℚ) := by
    rw [← C_mul, pow_succ]
  have h2 : f * (C (2 ^ a) * scaleHom v 2 c - C (2 ^ a) * C 2 * c) = 0 := by
    rw [e] at h1
    linear_combination (-1 : MvPolynomial σ ℚ) * h1
  have h3 := (mul_eq_zero.mp h2).resolve_left hf0
  ext d
  have h4 := congrArg (fun q => q.coeff d) h3
  simp only [coeff_sub, mul_assoc, coeff_C_mul, coeff_scaleHom] at h4
  change c.coeff d = 0
  change _ - _ = (0 : MvPolynomial σ ℚ).coeff d at h4
  change _ = (0 : ℚ) at h4
  by_contra hne
  have h5 : (2 : ℚ) ^ Finsupp.weight v d = 2 := by
    have h6 : (2 : ℚ) ^ a * (c.coeff d * (2 ^ Finsupp.weight v d - 2)) = 0 := by
      linear_combination h4
    have := (mul_eq_zero.mp h6).resolve_left (pow_ne_zero a (by norm_num))
    have := (mul_eq_zero.mp this).resolve_left hne
    linarith
  by_cases hd : d = 0
  · subst hd; simp at h5
  · have hw : 2 ≤ Finsupp.weight v d := by
      obtain ⟨k, hk⟩ := Finsupp.ne_iff.mp hd
      rw [Finsupp.weight_apply, Finsupp.sum]
      have hkmem : k ∈ d.support := by simpa using hk
      have h1k : 1 ≤ d k := Nat.one_le_iff_ne_zero.mpr (by simpa using hk)
      calc 2 ≤ v k := hv k
        _ ≤ d k • v k := by simpa using Nat.mul_le_mul_right (v k) h1k
        _ ≤ ∑ i ∈ d.support, d i • v i :=
          Finset.single_le_sum (f := fun i => d i • v i) (fun i _ => Nat.zero_le _) hkmem
    have : (2 : ℚ) ^ 2 ≤ 2 ^ Finsupp.weight v d := pow_le_pow_right₀ (by norm_num) hw
    rw [h5] at this
    norm_num at this

end Scaling


section Homogeneity

/-- The weight in which the letter `h_k` counts `k + 1`: the index plus one for the letter
itself, so a degree-`r` form of index sum `a` has weight `a + r`. -/
def letterWeight (k : ℕ+) : ℕ := (k : ℕ) + 1

theorem two_le_letterWeight (k : ℕ+) : 2 ≤ letterWeight k := by
  have := k.pos
  unfold letterWeight
  omega

theorem complete_isWeightedHomogeneous_pos {k : ℤ} (hk : 0 < k) :
    IsWeightedHomogeneous letterWeight (complete k) (k.toNat + 1) := by
  rw [complete_of_pos hk]
  exact isWeightedHomogeneous_X ℚ letterWeight _

/-- A determinant of letters `h_{r i - c j}`, each index positive or the entry zero, is
homogeneous of weight `∑ r - ∑ c + card`. -/
theorem det_isWeightedHomogeneous {ι : Type*} [Fintype ι] [DecidableEq ι] (r c : ι → ℤ)
    (A : Matrix ι ι CompleteRing)
    (hA : ∀ i j, A i j = 0 ∨ (A i j = complete (r i - c j) ∧ 0 < r i - c j)) :
    IsWeightedHomogeneous letterWeight A.det
      ((∑ i, r i - ∑ i, c i + Fintype.card ι).toNat) := by
  rw [Matrix.det_apply]
  refine IsWeightedHomogeneous.sum _ _ _ fun σ _ => ?_
  by_cases hz : ∃ i, A (σ i) i = 0
  · obtain ⟨i, hi⟩ := hz
    have : ∏ i, A (σ i) i = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hi
    rw [this, smul_zero]
    exact isWeightedHomogeneous_zero ℚ letterWeight _
  · push Not at hz
    have hpos : ∀ i, 0 < r (σ i) - c i ∧ A (σ i) i = complete (r (σ i) - c i) := fun i =>
      ⟨((hA (σ i) i).resolve_left (hz i)).2, ((hA (σ i) i).resolve_left (hz i)).1⟩
    have hp := IsWeightedHomogeneous.prod Finset.univ (fun i => A (σ i) i)
      (fun i => (r (σ i) - c i).toNat + 1) (w := letterWeight) (fun i _ => by
        rw [(hpos i).2]; exact complete_isWeightedHomogeneous_pos (hpos i).1)
    have hsum : (∑ i, ((r (σ i) - c i).toNat + 1) : ℕ) =
        (∑ i, r i - ∑ i, c i + Fintype.card ι).toNat := by
      have h1 : ((∑ i, ((r (σ i) - c i).toNat + 1) : ℕ) : ℤ) =
          ∑ i, (r (σ i) - c i + 1) := by
        push_cast
        refine Finset.sum_congr rfl fun i _ => ?_
        have := (hpos i).1
        rw [Int.toNat_of_nonneg this.le]
      have h2 : ∑ i, (r (σ i) - c i + 1) = ∑ i, r i - ∑ i, c i + Fintype.card ι := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Equiv.sum_comp σ r]
        simp
      have h3 : 0 ≤ ∑ i, (r (σ i) - c i + 1) :=
        Finset.sum_nonneg fun i _ => by have := (hpos i).1; omega
      omega
    rw [hsum] at hp
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simp [hs]
    · exact hp
    · exact hp.neg

/-- A diagram with no common beta: no row beta equals a column beta. -/
def ZeroFree {n : ℕ} (D : BetaDiagram n) : Prop := ∀ i j, D.row i ≠ D.col j

theorem BetaDiagram_entry {n : ℕ} (D : BetaDiagram n) (hD : ZeroFree D) (i j : Fin n) :
    D.matrix i j = 0 ∨ (D.matrix i j = complete (D.row i - D.col j) ∧ 0 < D.row i - D.col j) := by
  have hne : D.row i - D.col j ≠ 0 := sub_ne_zero.mpr (hD i j)
  by_cases h : 0 < D.row i - D.col j
  · exact Or.inr ⟨rfl, h⟩
  · left
    exact complete_of_neg (by omega)

/-- The sum of row betas minus the sum of column betas is the area; a zero-free diagram's
Schur function has weight `area + rows`. -/
theorem schur_isWeightedHomogeneous {n : ℕ} (D : BetaDiagram n) (hD : ZeroFree D) :
    IsWeightedHomogeneous letterWeight D.schur (D.area + n).toNat := by
  have := det_isWeightedHomogeneous D.row D.col D.matrix (BetaDiagram_entry D hD)
  simpa [BetaDiagram.schur, BetaDiagram.area] using this

end Homogeneity


section Restoration

open SkewCoframeRigidity.Coframe Matrix

variable {n : ℕ}

/-- The column `a_b = (h_{X_i - b})_i` of the bordered matrix at a restored position `b`. -/
noncomputable def restoreCol (D : BetaDiagram n) (b : ℤ) : Fin n → CompleteRing :=
  fun i => complete (D.row i - b)

/-- The row `b_b = (h_{b - Y_j})_j` of the bordered matrix at a restored position `b`. -/
noncomputable def restoreRow (D : BetaDiagram n) (b : ℤ) : Fin n → CompleteRing :=
  fun j => complete (b - D.col j)

/-- The first-order restoration polynomial `ṡ_D^{(b)} = -b_b adj(M_D) a_b`
(`sc:restoration-polynomial`). -/
noncomputable def dotS (D : BetaDiagram n) (b : ℤ) : CompleteRing :=
  -(restoreRow D b ⬝ᵥ (D.matrix.adjugate *ᵥ restoreCol D b))

/-- The weighted first variation `ṡ_D = ∑_b ρ_b ṡ_D^{(b)}` for constant weights `ρ`. -/
noncomputable def dotW (D : BetaDiagram n) (ρ : ℤ →₀ ℚ) : CompleteRing :=
  ρ.sum fun b r => C r * dotS D b

/-- A genuine vacancy of a diagram of span `m`: a position strictly between the ends that is
neither a row beta nor a column beta. -/
def IsVacancy {m : ℕ} (D : BetaDiagram (m + 1)) (b : ℤ) : Prop :=
  0 < b ∧ b < D.largestLabel ∧ (∀ i, D.row i ≠ b) ∧ ∀ j, D.col j ≠ b

/-- `ṡ^{(b)}` is the determinant of the matrix bordered at `b` with corner zero. -/
theorem dotS_eq_det (D : BetaDiagram n) (b : ℤ) :
    dotS D b = (bordered D.matrix (restoreCol D b) (restoreRow D b) 0).det := by
  rw [det_bordered, zero_mul, zero_sub]
  rfl

theorem area_ge_card (D : BetaDiagram n) : (n : ℤ) ≤ D.area := by
  have : ∀ i, 1 ≤ D.row i - D.col i := fun i => by have := D.row_nonempty i; omega
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => this i)
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at h
  unfold BetaDiagram.area
  exact h

theorem dotS_isWeightedHomogeneous (D : BetaDiagram n) (hD : ZeroFree D) {b : ℤ}
    (hr : ∀ i, D.row i ≠ b) (hc : ∀ j, D.col j ≠ b) :
    IsWeightedHomogeneous letterWeight (dotS D b) (D.area + n + 1).toNat := by
  rw [dotS_eq_det]
  have h := det_isWeightedHomogeneous (ι := Fin n ⊕ Unit)
    (Sum.elim D.row fun _ => b) (Sum.elim D.col fun _ => b)
    (bordered D.matrix (restoreCol D b) (restoreRow D b) 0) (by
      rintro (i | u) (j | v)
      · simpa [bordered] using BetaDiagram_entry D hD i j
      · by_cases hp : 0 < D.row i - b
        · right; simp [bordered, restoreCol]; omega
        · left; simp only [bordered, fromBlocks_apply₁₂, replicateCol_apply, restoreCol]
          exact complete_of_neg (by have := hr i; omega)
      · by_cases hp : 0 < b - D.col j
        · right; simp [bordered, restoreRow]; omega
        · left; simp only [bordered, fromBlocks_apply₂₁, replicateRow_apply, restoreRow]
          exact complete_of_neg (by have := hc j; omega)
      · left; simp [bordered])
  have hsum : (∑ i : Fin n ⊕ Unit, Sum.elim D.row (fun _ => b) i -
      ∑ i : Fin n ⊕ Unit, Sum.elim D.col (fun _ => b) i +
      (Fintype.card (Fin n ⊕ Unit) : ℤ)) = D.area + n + 1 := by
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.sum_const,
      Finset.card_univ, Fintype.card_unit, Fintype.card_sum, Fintype.card_fin]
    unfold BetaDiagram.area
    push_cast
    ring
  rw [hsum] at h
  exact h

theorem dotW_isWeightedHomogeneous (D : BetaDiagram n) (hD : ZeroFree D) (ρ : ℤ →₀ ℚ)
    (hρ : ∀ b ∈ ρ.support, (∀ i, D.row i ≠ b) ∧ ∀ j, D.col j ≠ b) :
    IsWeightedHomogeneous letterWeight (dotW D ρ) (D.area + n + 1).toNat := by
  unfold dotW Finsupp.sum
  refine IsWeightedHomogeneous.sum _ _ _ fun b hb => ?_
  have := (dotS_isWeightedHomogeneous D hD (hρ b hb).1 (hρ b hb).2).C_mul (ρ b)
  exact this

end Restoration


section StrictBlock

variable {e k : ℕ}

theorem largestLabel_of_norm {m : ℕ} (D : BetaDiagram (m + 1)) (hD : IsNorm D) :
    D.largestLabel = D.row 0 := by
  have : D.col (Fin.last m) = 0 := hD
  unfold BetaDiagram.largestLabel
  rw [this, sub_zero]

set_option backward.isDefEq.respectTransparency false in
/-- Divisibility of connected Schur functions forces equal spans: an irreducible multiple of a
nonunit is an associate, and associates have the same variables. -/
theorem largestLabel_eq_of_schur_dvd {m n : ℕ} {D : BetaDiagram (m + 1)} {F : BetaDiagram (n + 1)}
    (hD : D.Connected) (hF : F.Connected) (hdvd : D.schur ∣ F.schur) :
    D.largestLabel = F.largestLabel := by
  classical
  obtain ⟨c, hc⟩ := hdvd
  have hFirr : Irreducible F.schur := F.schur_irreducible hF
  have hunit := hFirr.isUnit_or_isUnit hc
  have hDnu : ¬ IsUnit D.schur := D.schur_not_isUnit (by omega)
  have hcu : IsUnit c := hunit.resolve_left hDnu
  obtain ⟨u, rfl⟩ := hcu
  obtain ⟨r, -, hr⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp u.isUnit
  obtain ⟨r', -, hr'⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp u⁻¹.isUnit
  have hD' : D.schur = F.schur * ↑u⁻¹ := by
    rw [hc, mul_assoc, Units.mul_inv, mul_one]
  have hpos1 := D.largestLabel_pos
  have hpos2 := F.largestLabel_pos
  have hmemD := D.largest_mem_vars hD
  have hmemF := F.largest_mem_vars hF
  rw [hD', hr'] at hmemD
  rw [hc, hr] at hmemF
  have hsubD := MvPolynomial.vars_mul F.schur (C r' : MvPolynomial ℕ+ ℚ)
  have hsubF := MvPolynomial.vars_mul D.schur (C r : MvPolynomial ℕ+ ℚ)
  rw [MvPolynomial.vars_C, Finset.union_empty] at hsubD hsubF
  have h1 := F.vars_le_largestLabel
    (⟨D.largestLabel.toNat, by omega⟩ : ℕ+) (hsubD hmemD)
  have h2 := D.vars_le_largestLabel
    (⟨F.largestLabel.toNat, by omega⟩ : ℕ+) (hsubF hmemF)
  have h3 : ((D.largestLabel.toNat : ℕ) : ℤ) ≤ F.largestLabel := h1
  have h4 : ((F.largestLabel.toNat : ℕ) : ℤ) ≤ D.largestLabel := h2
  omega

/-- **The strict-block step** of `sc:linearized-cap`.  For an actual connected zero-free block `E`
and an actual connected cap `K_E`, put `N = K_E ◁ E`.  If the differentiated top equation
`s_E ṡ_N - s_N ṡ_E = 0` holds for constant weights on genuine vacancies of `E`, then
`ṡ_E = 0` and `ṡ_N = 0`: `s_E` divides `ṡ_E`, and the quotient would have weighted degree zero
and ordinary degree one. -/
theorem strict_block_vanishing (E : BetaDiagram (e + 1)) (KE : BetaDiagram (k + 1))
    (hE : IsNorm E) (hKE : IsNorm KE) (hEc : E.Connected) (hKc : KE.Connected)
    (hEz : ZeroFree E) (ρ : ℤ →₀ ℚ)
    (hρ : ∀ b ∈ ρ.support, (∀ i, E.row i ≠ b) ∧ ∀ j, E.col j ≠ b)
    (h : E.schur * dotW (splice KE E hKE hE) ρ = (splice KE E hKE hE).schur * dotW E ρ) :
    dotW E ρ = 0 ∧ dotW (splice KE E hKE hE) ρ = 0 := by
  have hNc := splice_connected KE E hKE hE hKc hEc
  have hspan : E.largestLabel < (splice KE E hKE hE).largestLabel := by
    rw [largestLabel_of_norm _ (splice_norm KE E hKE hE), largestLabel_of_norm E hE,
      splice_span KE E hKE hE]
    have := top_pos KE hKE
    omega
  have hprime : Prime E.schur := (E.schur_irreducible hEc).prime
  have hdvd : E.schur ∣ (splice KE E hKE hE).schur * dotW E ρ := ⟨_, h.symm⟩
  have hdvd' : E.schur ∣ dotW E ρ := (hprime.dvd_or_dvd hdvd).resolve_left (fun hd =>
    absurd (largestLabel_eq_of_schur_dvd hEc hNc hd) (ne_of_lt hspan))
  obtain ⟨c, hcE⟩ := hdvd'
  have hEn := area_ge_card E
  have hEh : IsWeightedHomogeneous letterWeight E.schur (E.area + (e + 1 : ℕ)).toNat :=
    schur_isWeightedHomogeneous E hEz
  have hdh := dotW_isWeightedHomogeneous E hEz ρ hρ
  have hnat : (E.area + ((e + 1 : ℕ) : ℤ) + 1).toNat = (E.area + (e + 1 : ℕ)).toNat + 1 := by
    omega
  rw [hnat, hcE] at hdh
  have hc0 : c = 0 := eq_zero_of_mul_homogeneous letterWeight two_le_letterWeight hEh
    E.schur_ne_zero hdh
  have hE0 : dotW E ρ = 0 := by rw [hcE, hc0, mul_zero]
  refine ⟨hE0, ?_⟩
  rw [hE0, mul_zero] at h
  exact (mul_eq_zero.mp h).resolve_left E.schur_ne_zero

end StrictBlock

end SkewCoframeRigidity.UnitRestoration
