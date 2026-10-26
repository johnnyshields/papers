/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.UnitRestoration.StrictBlock
import SkewCoframeRigidity.UnitRestoration.Variation
import SkewCoframeRigidity.Coframe.Defs

/-!
# From the physical unit to the coherent letters

`dotS` of `StrictBlock.lean` is the bordered derivative over the polynomial ring in the positive
letters, with the unit equal to one.  `restorationPoly` of `Variation.lean` is the same
expression over the field of the coherent letters `ℚ(ϑ, H₁, H₂, …)`.  Both are the image of one
element `dotSOf X` of `ℚ[ϑ, H₁, …]`, which is homogeneous of degree `n + 1`; a homogeneous
polynomial vanishing at `ϑ = 1` vanishes.  Hence `ṡ_D = 0` at the physical unit gives the
coherent identity `∑ ρ_b restorationPoly = 0` (`restorationSum_eq_zero_of_dotW_eq_zero`).
Sorry-free.
-/

namespace SkewCoframeRigidity.UnitRestoration

open SkewCofactorIndependence SkewCoframeRigidity SkewCoframeRigidity.Coframe Matrix MvPolynomial

variable {n : ℕ}

/-- The bordered derivative `-b_b adj(M_D) a_b` over any commutative ring with a letter family. -/
def dotSOf {R : Type*} [CommRing R] (h : ℕ → R) (D : BetaDiagram n) (b : ℤ) : R :=
  -((fun j => letterOf h (b - D.col j)) ⬝ᵥ
    ((fullMatrixOf h D).adjugate *ᵥ fun i => letterOf h (D.row i - b)))

theorem dotS_eq_dotSOf (D : BetaDiagram n) (b : ℤ) :
    dotS D b = dotSOf (fun k : ℕ => (complete (k : ℤ) : CompleteRing)) D b := by
  have hl : ∀ z : ℤ, letterOf (fun k : ℕ => (complete (k : ℤ) : CompleteRing)) z = complete z := by
    intro z
    unfold letterOf
    split_ifs with h
    · exact (complete_of_neg h).symm
    · show complete ((z.toNat : ℕ) : ℤ) = complete z
      rw [Int.toNat_of_nonneg (by omega)]
  have hM : fullMatrixOf (fun k : ℕ => (complete (k : ℤ) : CompleteRing)) D = D.matrix := by
    refine Matrix.ext fun i j => ?_
    simp only [fullMatrixOf, Matrix.of_apply, hl, BetaDiagram.matrix]
  unfold dotS dotSOf restoreRow restoreCol
  rw [hM]
  simp only [hl]

theorem map_dotSOf {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (h : ℕ → R)
    (D : BetaDiagram n) (b : ℤ) : f (dotSOf h D b) = dotSOf (fun k => f (h k)) D b := by
  have hl : ∀ z : ℤ, f (letterOf h z) = letterOf (fun k => f (h k)) z := by
    intro z; unfold letterOf; split_ifs <;> simp
  have hM : (fullMatrixOf h D).map f = fullMatrixOf (fun k => f (h k)) D := by
    refine Matrix.ext fun i j => ?_
    simp [fullMatrixOf, hl]
  have hadj : ((fullMatrixOf h D).adjugate).map f =
      (fullMatrixOf (fun k => f (h k)) D).adjugate := by
    rw [← hM]
    have := RingHom.map_adjugate f (fullMatrixOf h D)
    simpa [RingHom.mapMatrix_apply] using this
  have hv1 : (f ∘ fun j => letterOf h (b - D.col j)) =
      fun j => letterOf (fun k => f (h k)) (b - D.col j) := funext fun j => hl _
  have hv2 : (f ∘ fun i => letterOf h (D.row i - b)) =
      fun i => letterOf (fun k => f (h k)) (D.row i - b) := funext fun i => hl _
  have hmv : f ∘ ((fullMatrixOf h D).adjugate *ᵥ fun i => letterOf h (D.row i - b)) =
      ((fullMatrixOf h D).adjugate).map f *ᵥ (f ∘ fun i => letterOf h (D.row i - b)) :=
    funext fun i => RingHom.map_mulVec f _ _ i
  unfold dotSOf
  rw [map_neg, RingHom.map_dotProduct, hv1, hmv, hadj, hv2]


section Dehomogenize

/-- The dehomogenization `ϑ ↦ 1`: the coherent letters to the physical letters. -/
noncomputable def deh : MvPolynomial ℕ ℚ →+* CompleteRing :=
  MvPolynomial.eval₂Hom MvPolynomial.C fun k : ℕ => (complete (k : ℤ) : CompleteRing)

theorem deh_X (k : ℕ) : deh (MvPolynomial.X k) = complete (k : ℤ) := by
  simp [deh]

/-- Evaluation of a homogeneous polynomial scales with the degree. -/
theorem eval_smul_of_isHomogeneous {σ : Type*} {p : MvPolynomial σ ℚ} {m : ℕ}
    (hp : p.IsHomogeneous m) (c : ℚ) (r : σ → ℚ) :
    MvPolynomial.eval (c • r) p = c ^ m * MvPolynomial.eval r p := by
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : d.degree = m := by
    rw [Finsupp.degree_eq_weight_one]; exact hp (MvPolynomial.mem_support_iff.mp hd)
  have h1 : ∏ i ∈ d.support, (c • r) i ^ d i = c ^ m * ∏ i ∈ d.support, r i ^ d i := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum]
    congr 2
  rw [h1]; ring

/-- A homogeneous polynomial vanishing at `ϑ = 1` vanishes. -/
theorem eq_zero_of_deh_eq_zero {m : ℕ} {p : MvPolynomial ℕ ℚ} (hp : p.IsHomogeneous m)
    (h : deh p = 0) : p = 0 := by
  have hq : (MvPolynomial.X 0 * p : MvPolynomial ℕ ℚ).IsHomogeneous (1 + m) :=
    (MvPolynomial.isHomogeneous_X ℚ 0).mul hp
  have hq0 : MvPolynomial.X 0 * p = 0 := by
    refine hq.eq_zero_of_forall_eval_eq_zero fun r => ?_
    by_cases hr : r 0 = 0
    · simp [hr]
    · set r' : ℕ → ℚ := (r 0)⁻¹ • r with hr'
      have h1 : MvPolynomial.eval r' p = 0 := by
        have hs : (MvPolynomial.eval fun k : ℕ+ => r' (k : ℕ)).comp deh =
            MvPolynomial.eval r' := by
          refine MvPolynomial.ringHom_ext (fun a => by simp [deh]) (fun k => ?_)
          simp only [RingHom.comp_apply, deh_X, MvPolynomial.eval_X]
          rcases Nat.eq_zero_or_pos k with rfl | hk
          · simp [hr', hr]
          · rw [complete_of_pos (by exact_mod_cast hk)]
            erw [MvPolynomial.eval_X]
            simp
        have := congrArg (fun f => f p) hs
        simp only [RingHom.comp_apply] at this
        rw [← this, h, map_zero]
      have h2 : r = r 0 • r' := by
        rw [hr', smul_smul, mul_inv_cancel₀ hr, one_smul]
      rw [map_mul, h2, MvPolynomial.eval_X, eval_smul_of_isHomogeneous hp, h1]
      simp
  exact (mul_eq_zero.mp hq0).resolve_left (MvPolynomial.X_ne_zero 0)

end Dehomogenize


section Homogeneous

theorem det_isHomogeneous_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (MvPolynomial ℕ ℚ)) (hA : ∀ i j, (A i j).IsHomogeneous 1) :
    A.det.IsHomogeneous (Fintype.card ι) := by
  rw [Matrix.det_apply]
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun σ _ => ?_
  have hp := MvPolynomial.IsHomogeneous.prod Finset.univ (fun i => A (σ i) i) (fun _ => 1)
    (fun i _ => hA _ _)
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at hp
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · simpa [hs] using hp
  · simpa [hs] using hp.neg

theorem letterOf_X_isHomogeneous (z : ℤ) :
    (letterOf (fun k : ℕ => (MvPolynomial.X k : MvPolynomial ℕ ℚ)) z).IsHomogeneous 1 := by
  unfold letterOf
  split_ifs
  · exact MvPolynomial.isHomogeneous_zero _ _ _
  · exact MvPolynomial.isHomogeneous_X _ _

/-- The coherent restoration polynomial is homogeneous of degree `n + 1` in the letters. -/
theorem dotSOf_isHomogeneous (D : BetaDiagram n) (b : ℤ) :
    (dotSOf (fun k : ℕ => (MvPolynomial.X k : MvPolynomial ℕ ℚ)) D b).IsHomogeneous (n + 1) := by
  set h : ℕ → MvPolynomial ℕ ℚ := fun k => MvPolynomial.X k with hh
  have hdet := det_bordered (fullMatrixOf h D) (fun i => letterOf h (D.row i - b))
    (fun j => letterOf h (b - D.col j)) 0
  have hv : dotSOf h D b = (bordered (fullMatrixOf h D) (fun i => letterOf h (D.row i - b))
      (fun j => letterOf h (b - D.col j)) 0).det := by
    rw [hdet, zero_mul, zero_sub]; rfl
  rw [hv]
  have := det_isHomogeneous_one (ι := Fin n ⊕ Unit)
    (bordered (fullMatrixOf h D) (fun i => letterOf h (D.row i - b))
      (fun j => letterOf h (b - D.col j)) 0) (by
      rintro (i | u) (j | v)
      · exact letterOf_X_isHomogeneous _
      · exact letterOf_X_isHomogeneous _
      · exact letterOf_X_isHomogeneous _
      · exact MvPolynomial.isHomogeneous_zero _ _ _)
  simpa using this

end Homogeneous


theorem restorationPoly_eq_dotSOf (D : BetaDiagram n) (b : ℕ) :
    restorationPoly cohLetters D b = dotSOf cohLetters D (b : ℤ) := rfl

/-- **From the physical unit to the coherent letters.**  If `ṡ_D = ∑ ρ_b ṡ_D^{(b)}` vanishes with
the unit equal to one, then `∑ ρ_b ṡ_D^{(b)} = 0` over the field of the coherent letters. -/
theorem restorationSum_eq_zero_of_dotW_eq_zero (D : BetaDiagram n) (ρ : ℤ →₀ ℚ)
    (hρ : ∀ b ∈ ρ.support, 0 ≤ b) (h : dotW D ρ = 0) :
    ∑ b ∈ ρ.support, algebraMap (MvPolynomial ℕ ℚ) CohField (MvPolynomial.C (ρ b)) *
      restorationPoly cohLetters D b.toNat = 0 := by
  set X' : ℕ → MvPolynomial ℕ ℚ := fun k => MvPolynomial.X k with hX'
  set Pσ : MvPolynomial ℕ ℚ := ∑ b ∈ ρ.support, MvPolynomial.C (ρ b) * dotSOf X' D b with hPσ
  have hhom : Pσ.IsHomogeneous (n + 1) :=
    MvPolynomial.IsHomogeneous.sum _ _ _ fun b _ =>
      (dotSOf_isHomogeneous D b).C_mul (ρ b)
  have hdeh : deh Pσ = 0 := by
    rw [hPσ, map_sum, ← h]
    unfold dotW Finsupp.sum
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_mul, map_dotSOf deh X' D b]
    show _ = MvPolynomial.C (ρ b) * dotS D b
    rw [dotS_eq_dotSOf]
    simp only [hX', deh_X]
    congr 1
    simp [deh]
  have h0 := eq_zero_of_deh_eq_zero hhom hdeh
  have h1 := congrArg (algebraMap (MvPolynomial ℕ ℚ) CohField) h0
  rw [hPσ, map_sum, map_zero] at h1
  rw [← h1]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [map_mul, map_dotSOf (algebraMap (MvPolynomial ℕ ℚ) CohField) X' D b,
    restorationPoly_eq_dotSOf, Int.toNat_of_nonneg (hρ b hb)]
  rfl

end SkewCoframeRigidity.UnitRestoration
