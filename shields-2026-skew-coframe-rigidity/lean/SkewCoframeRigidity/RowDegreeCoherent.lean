/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.RowDegree
import SkewCoframeRigidity.Coframe.Coherent

/-!
# Row degree, proper corners and irreducibility: the coherent forms

Formalizes `shields-2026-skew-coframe-rigidity.tex`, `sc:row-degree`, for the coherent
homogenization `cohSchur D = ϑ^r s_A(H₁/ϑ, H₂/ϑ, …)` in `ℚ[ϑ, H₁, H₂, …]`.

* `cohSchur_posRowDegree`: the positive row degree, the degree in the positive letters with
  `ϑ` a coefficient (weights `0` on `ϑ`, `1` on every `H_k`), is the number of rows.
* `not_theta_dvd_cohSchur`: `ϑ` does not divide the coherent polynomial.
* `cohSchur_irreducible`: for a connected diagram the coherent polynomial is irreducible in
  `ℚ[ϑ, H₁, …]`.  It has positive degree in the positive letters and no factor `ϑ`, so by
  Gauss's lemma over the factorial ring `ℚ[ϑ]` this is the same as primitive over `ℚ[ϑ]` and
  irreducible over `ℚ(ϑ)`; the ring form is the one the later modules consume, since
  `cohSchur` lives in `CohRing`.
* `cohSchur_isRelPrime_cohCorner`: it is relatively prime to the proper corner.
* `rowCount_eq_of_schur_eq`, `cohSchur_eq_of_schur_eq'`: equal physical Schur functions have
  equal row counts and equal coherent homogenizations (the latter is
  `cohSchur_eq_of_schur_eq` once the row counts agree).

The irreducibility argument never factors a homogeneous polynomial into homogeneous parts.
The substitution `H_k ↦ ϑ H_k` multiplies `cohSchur D` by `ϑ^r` times its physical form, and
is injective; a factorization of `cohSchur D` becomes a factorization of `ϑ^r s_A` in a
factorial ring, in which the prime `s_A` and the prime `ϑ` can be read off.
-/

namespace SkewCoframeRigidity.Coframe

open SkewCofactorIndependence MvPolynomial

/-- Weights counting the positive letters: `ϑ = H₀` has weight zero, every `H_k` weight one. -/
def posWeight : ℕ → ℕ := fun k => if k = 0 then 0 else 1

/-- The positive row degree of a coherent polynomial: its degree in the positive letters, with
`ϑ` treated as a coefficient. -/
noncomputable def posRowDegree (p : CohRing) : ℕ := p.weightedTotalDegree posWeight

/-- The retraction of the coherent ring onto the physical ring that sets `ϑ = 0`. -/
noncomputable def physRetract : CohRing →ₐ[ℚ] SkewCofactorIndependence.CompleteRing :=
  aeval fun k => if h : k = 0 then 0 else X ⟨k, Nat.pos_of_ne_zero h⟩

theorem physRetract_physInclude (p : SkewCofactorIndependence.CompleteRing) :
    physRetract (physInclude p) = p := by
  have h : physRetract.comp physInclude =
      AlgHom.id ℚ SkewCofactorIndependence.CompleteRing := by
    apply algHom_ext
    intro k
    have hk : (k : ℕ) ≠ 0 := k.ne_zero
    simp [physRetract, physInclude, hk]
    rfl
  exact congrArg (fun F => F p) h

section Degrees

theorem totalDegree_aeval_le {σ τ : Type*} (s : σ → MvPolynomial τ ℚ) (w : σ → ℕ)
    (hs : ∀ i, (s i).totalDegree ≤ w i) (q : MvPolynomial σ ℚ) :
    (aeval s q).totalDegree ≤ q.weightedTotalDegree w := by
  classical
  rw [aeval_def, eval₂_eq]
  apply totalDegree_finsetSum_le
  intro d hd
  refine (totalDegree_mul _ _).trans ?_
  have h0 : (algebraMap ℚ (MvPolynomial τ ℚ) (q.coeff d)).totalDegree = 0 := totalDegree_C _
  rw [h0, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ i ∈ d.support, (s i ^ d i).totalDegree ≤ ∑ i ∈ d.support, d i * w i :=
        Finset.sum_le_sum fun i _ =>
          (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (hs i))
    _ = Finsupp.weight w d := by
        simp [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul]
    _ ≤ _ := le_weightedTotalDegree w hd

theorem totalDegree_physSpec_le (q : CohRing) :
    (physSpec q).totalDegree ≤ posRowDegree q := by
  refine totalDegree_aeval_le _ posWeight (fun i => ?_) q
  by_cases h : i = 0
  · simp [h, posWeight]
  · simp [h, posWeight, totalDegree_X]

theorem totalDegree_physRetract_le (q : CohRing) :
    (physRetract q).totalDegree ≤ q.totalDegree := by
  rw [← weightedTotalDegree_one q]
  refine totalDegree_aeval_le _ 1 (fun i => ?_) q
  by_cases h : i = 0
  · simp [h]
  · simp only [h, dite_false, Pi.one_apply]
    exact (totalDegree_X _).le

theorem totalDegree_le_physInclude (p : SkewCofactorIndependence.CompleteRing) :
    p.totalDegree ≤ (physInclude p).totalDegree := by
  have := totalDegree_physRetract_le (physInclude p)
  rwa [physRetract_physInclude] at this

theorem posRowDegree_le_totalDegree (q : CohRing) : posRowDegree q ≤ q.totalDegree := by
  unfold posRowDegree weightedTotalDegree totalDegree
  apply Finset.sup_le
  intro d hd
  refine le_trans ?_ (Finset.le_sup hd)
  simp only [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul]
  apply Finset.sum_le_sum
  intro i _
  by_cases h : i = 0 <;> simp [posWeight, h]

theorem isHomogeneous_det {N : ℕ} (M : Matrix (Fin N) (Fin N) CohRing)
    (h : ∀ i j, (M i j).IsHomogeneous 1) : M.det.IsHomogeneous N := by
  rw [Matrix.det_apply']
  refine IsHomogeneous.sum _ _ _ fun σ _ => ?_
  have hp := IsHomogeneous.prod Finset.univ (fun i => M (σ i) i) (fun _ => 1)
    fun i _ => h _ _
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hp
  have e : ((↑(↑(Equiv.Perm.sign σ) : ℤ)) : CohRing) =
      C (((Equiv.Perm.sign σ : ℤ) : ℚ)) := by simp
  rw [e]
  exact hp.C_mul _

theorem isHomogeneous_letterOf (k : ℤ) :
    (letterOf (X : ℕ → CohRing) k).IsHomogeneous 1 := by
  unfold letterOf
  split_ifs
  · exact isHomogeneous_zero _ _ _
  · exact isHomogeneous_X _ _

theorem totalDegree_cohSchur_le {n : ℕ} (D : BetaDiagram n) : (cohSchur D).totalDegree ≤ n := by
  have : (cohSchur D).IsHomogeneous n :=
    isHomogeneous_det _ fun i j => isHomogeneous_letterOf _
  exact this.totalDegree_le

end Degrees

section RowDegree

variable {n : ℕ}

/-- The positive row degree of the coherent homogenization of a skew diagram is its number of
rows (`sc:row-degree`, coherent form). -/
theorem cohSchur_posRowDegree (D : BetaDiagram n) : posRowDegree (cohSchur D) = n := by
  apply le_antisymm
  · exact (posRowDegree_le_totalDegree _).trans (totalDegree_cohSchur_le D)
  · have h1 : D.schur.totalDegree = n := BetaDiagram.rowDegree D
    have h2 := totalDegree_le_physInclude D.schur
    have h3 := totalDegree_physSpec_le (cohSchur D)
    rw [show physSpec (cohSchur D) = physInclude D.schur from physSpec_schurOf D] at h3
    omega

/-- `ϑ` does not divide the coherent homogenization of a skew diagram. -/
theorem not_theta_dvd_cohSchur (D : BetaDiagram n) : ¬ (X 0 : CohRing) ∣ cohSchur D := by
  rintro ⟨q, hq⟩
  have hφ : physSpec (cohSchur D) = physInclude D.schur := physSpec_schurOf D
  have hf0 : cohSchur D ≠ 0 := by
    intro h
    rw [h, map_zero] at hφ
    exact D.schur_ne_zero (physInclude_injective (by rw [← hφ, map_zero]))
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact hf0 (by rw [hq, mul_zero])
  have h1 : D.schur.totalDegree = n := BetaDiagram.rowDegree D
  have h2 := totalDegree_le_physInclude D.schur
  have h3 : physSpec (cohSchur D) = physSpec q := by
    rw [hq, map_mul]
    simp [physSpec]
  have h4 := (totalDegree_physSpec_le q).trans (posRowDegree_le_totalDegree q)
  have h5 : (cohSchur D).totalDegree = 1 + q.totalDegree := by
    rw [hq, totalDegree_mul_of_isDomain (X_ne_zero 0) hq0, totalDegree_X]
  have h6 := totalDegree_cohSchur_le D
  rw [hφ] at h3
  rw [h3] at h2
  omega

end RowDegree

section Irreducible

variable {n : ℕ}

theorem physInclude_irreducible {g : SkewCofactorIndependence.CompleteRing} (hg : Irreducible g) :
    Irreducible (physInclude g) := by
  have hg0 : g ≠ 0 := hg.ne_zero
  have hg'0 : physInclude g ≠ 0 := fun h => hg0 (physInclude_injective (by rw [h, map_zero]))
  have hv : (0 : ℕ) ∉ (physInclude g).vars := by
    intro h
    have := vars_rename (fun k : ℕ+ => (k : ℕ)) g h
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp this
    exact k.ne_zero hk
  -- a factor of a `ϑ`-free polynomial is `ϑ`-free, hence lies in the image of `physInclude`
  have hfree : ∀ a b : CohRing, physInclude g = a * b →
      ∃ a0 : SkewCofactorIndependence.CompleteRing, physInclude a0 = a := by
    intro a b hab
    have ha0 : a ≠ 0 := by rintro rfl; exact hg'0 (by rw [hab, zero_mul])
    have hb0 : b ≠ 0 := by rintro rfl; exact hg'0 (by rw [hab, mul_zero])
    have hd : degreeOf 0 (physInclude g) = 0 := by
      by_contra h
      exact hv (mem_vars_iff_degreeOf_ne_zero.2 h)
    rw [hab, degreeOf_mul_eq ha0 hb0] at hd
    have hda : degreeOf 0 a = 0 := by omega
    refine exists_rename_eq_of_vars_subset_range a (fun k : ℕ+ => (k : ℕ)) PNat.coe_injective ?_
    intro i hi
    have hi' : i ∈ a.vars := hi
    have : i ≠ 0 := by
      rintro rfl
      exact (mem_vars_iff_degreeOf_ne_zero.1 hi') hda
    exact ⟨⟨i, Nat.pos_of_ne_zero this⟩, rfl⟩
  refine ⟨?_, fun a b hab => ?_⟩
  · intro hu
    exact hg.not_isUnit (by simpa [physRetract_physInclude] using hu.map physRetract)
  · obtain ⟨a0, ha⟩ := hfree a b hab
    obtain ⟨b0, hb⟩ := hfree b a (by rw [hab, mul_comm])
    subst ha hb
    have : g = a0 * b0 := physInclude_injective (by rw [hab, map_mul])
    rcases hg.isUnit_or_isUnit this with h | h
    · exact Or.inl (h.map physInclude)
    · exact Or.inr (h.map physInclude)

/-- Coherent substitution of the physical form: `ρ(s_A) = ϑ^r s_A^{phys}`. -/
theorem thetaScale_cohSchur (D : BetaDiagram n) :
    thetaScale (cohSchur D) = X 0 ^ n * physInclude D.schur := by
  have h := thetaScale_det (fullMatrixOf (X : ℕ → CohRing) D) (thetaScale_fullMatrix D)
  change thetaScale (schurOf X D) = _
  unfold schurOf
  rw [h]
  have := physSpec_schurOf D
  unfold schurOf at this
  rw [this]

theorem thetaScale_C (c : ℚ) : thetaScale (C c : CohRing) = C c := by
  simp [thetaScale]

/-- A connected skew Schur polynomial's coherent homogenization is irreducible in
`ℚ[ϑ, H₁, H₂, …]` (`sc:row-degree`, coherent form).  It has positive row degree and no factor
`ϑ`, so by Gauss's lemma it is primitive over `ℚ[ϑ]` and irreducible over `ℚ(ϑ)`. -/
theorem cohSchur_irreducible (D : BetaDiagram (n + 1)) (hD : D.Connected) :
    Irreducible (cohSchur D) := by
  set f := cohSchur D with hf
  set g' : CohRing := physInclude D.schur with hg'
  have hirr : Irreducible g' := physInclude_irreducible (D.schur_irreducible hD)
  have hprime : Prime g' := hirr.prime
  have hθ : Prime (X 0 : CohRing) := X_prime
  have hρ : thetaScale f = X 0 ^ (n + 1) * g' := thetaScale_cohSchur D
  have hnd : ¬ (X 0 : CohRing) ∣ f := not_theta_dvd_cohSchur D
  -- if the physical prime divides `ρ a`, then `b` is a unit
  have aux : ∀ a b : CohRing, f = a * b → g' ∣ thetaScale a → IsUnit b := by
    intro a b hab ⟨q, hq⟩
    have h1 : thetaScale a * thetaScale b = X 0 ^ (n + 1) * g' := by
      rw [← map_mul, ← hab, hρ]
    rw [hq] at h1
    have h2 : q * thetaScale b = X 0 ^ (n + 1) := by
      apply mul_left_cancel₀ hirr.ne_zero
      linear_combination h1
    have h3 : thetaScale b ∣ X 0 ^ (n + 1) := ⟨q, by rw [← h2]; ring⟩
    obtain ⟨i, _, u, hu⟩ := (dvd_prime_pow hθ (n + 1)).1 h3
    obtain ⟨c, _, hc⟩ := isUnit_iff_eq_C_of_isReduced.1 u.isUnit
    have h4 : b * (u : CohRing) = X 0 ^ i := by
      apply thetaScale_injective
      rw [map_mul, hc, thetaScale_C, ← hc, hu]
      simp [thetaScale]
    have h5 : (X 0 : CohRing) ^ i ∣ f := by
      refine ⟨a * ((u⁻¹ : (CohRing)ˣ) : CohRing), ?_⟩
      calc f = a * b := hab
        _ = a * (b * u * (u⁻¹ : (CohRing)ˣ)) := by simp
        _ = _ := by rw [h4]; ring
    have hi : i = 0 := by
      by_contra hne
      exact hnd ((dvd_pow_self _ hne).trans h5)
    rw [hi, pow_zero] at h4
    exact isUnit_iff_exists_inv.2 ⟨u, h4⟩
  refine ⟨?_, fun a b hab => ?_⟩
  · intro hu
    exact hirr.not_isUnit (by
      have := hu.map physSpec
      rwa [show physSpec f = g' from physSpec_schurOf D] at this)
  · have hdv : g' ∣ thetaScale a * thetaScale b := ⟨X 0 ^ (n + 1), by
      rw [← map_mul, ← hab, hρ]; ring⟩
    rcases hprime.dvd_or_dvd hdv with h | h
    · exact Or.inr (aux a b hab h)
    · exact Or.inl (aux b a (by rw [hab, mul_comm]) h)

end Irreducible

section Corner

variable {n : ℕ}

/-- Physical form: a connected Schur polynomial does not divide its proper corner, because the
largest generator occurs in the former and not in the latter. -/
theorem schur_not_dvd_cornerPolynomial (D : BetaDiagram (n + 1)) (hD : D.Connected) :
    ¬ D.schur ∣ D.cornerPolynomial := by
  rintro ⟨h, hh⟩
  have hc := D.cornerPolynomial_ne_zero hD
  have hs : D.schur ≠ 0 := D.schur_ne_zero
  have hh0 : h ≠ 0 := by rintro rfl; exact hc (by rw [hh, mul_zero])
  have hd : degreeOf (⟨D.largestLabel.toNat, by have := D.largestLabel_pos; omega⟩ : ℕ+)
      D.cornerPolynomial = degreeOf (⟨D.largestLabel.toNat, by
        have := D.largestLabel_pos; omega⟩ : ℕ+) D.schur +
      degreeOf (⟨D.largestLabel.toNat, by have := D.largestLabel_pos; omega⟩ : ℕ+) h := by
    rw [hh]; exact degreeOf_mul_eq hs hh0
  have h1 := mem_vars_iff_degreeOf_ne_zero.1 (D.largest_mem_vars hD)
  have h2 : degreeOf (⟨D.largestLabel.toNat, by have := D.largestLabel_pos; omega⟩ : ℕ+)
      D.cornerPolynomial = 0 := by
    by_contra h'
    exact D.largest_not_mem_corner (mem_vars_iff_degreeOf_ne_zero.2 h')
  omega

/-- A connected diagram's coherent homogenization is relatively prime to its proper corner
(`sc:row-degree`, coherent form). -/
theorem cohSchur_isRelPrime_cohCorner (D : BetaDiagram (n + 1)) (hD : D.Connected) :
    IsRelPrime (cohSchur D) (cohCorner D) := by
  refine (cohSchur_irreducible D hD).isRelPrime_iff_not_dvd.2 ?_
  rintro ⟨h, hh⟩
  have e : physSpec (cohCorner D) = (-1) ^ n * physInclude D.cornerPolynomial := by
    unfold cohCorner cornerOf
    rw [map_mul, map_pow, map_neg, map_one, physSpec_properDet]
  have h1 := congrArg physSpec hh
  rw [map_mul, e, show physSpec (cohSchur D) = physInclude D.schur from
    physSpec_schurOf D] at h1
  have h2 := congrArg physRetract h1
  rw [map_mul, map_mul, map_pow, map_neg, map_one, physRetract_physInclude,
    physRetract_physInclude] at h2
  apply schur_not_dvd_cornerPolynomial D hD
  refine ⟨(-1) ^ n * physRetract (physSpec h), ?_⟩
  have h3 : ((-1 : SkewCofactorIndependence.CompleteRing) ^ n) *
      ((-1 : SkewCofactorIndependence.CompleteRing) ^ n) = 1 := by
    rw [← mul_pow]; simp
  calc D.cornerPolynomial
      = ((-1 : SkewCofactorIndependence.CompleteRing) ^ n *
        (-1 : SkewCofactorIndependence.CompleteRing) ^ n) * D.cornerPolynomial := by
        rw [h3, one_mul]
    _ = _ := by rw [mul_assoc, h2]; ring

end Corner

section Equality

/-- Equal physical skew Schur functions have equal row counts. -/
theorem rowCount_eq_of_schur_eq {n m : ℕ} {D : BetaDiagram n} {E : BetaDiagram m}
    (h : D.schur = E.schur) : n = m := by
  rw [← BetaDiagram.rowDegree D, ← BetaDiagram.rowDegree E, h]

/-- Equal physical skew Schur functions have equal coherent homogenizations: the row counts
agree, and `cohSchur_eq_of_schur_eq` applies. -/
theorem cohSchur_eq_of_schur_eq' {n m : ℕ} {D : BetaDiagram n} {E : BetaDiagram m}
    (h : D.schur = E.schur) : cohSchur D = cohSchur E := by
  obtain rfl := rowCount_eq_of_schur_eq h
  exact cohSchur_eq_of_schur_eq h

end Equality

end SkewCoframeRigidity.Coframe
