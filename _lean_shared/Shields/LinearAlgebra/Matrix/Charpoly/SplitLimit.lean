/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.Topology.Instances.Matrix

/-!
# Coefficientwise limits of split monic polynomials

A monic polynomial that is a coefficientwise limit of polynomials splitting over `ℝ` again splits,
and the characteristic polynomial's coefficients depend continuously on the matrix.

## Main results

* `Shields.CoeffContinuous`: the predicate that each coefficient of a polynomial-valued function is
  continuous, closed under the ring operations and finite products.
* `Shields.coeffContinuous_charpoly`: the characteristic polynomial is coefficient-continuous.
* `Shields.card_roots_of_tendsto_coeff`: if monic degree-`n` polynomials with `n` real roots
  converge coefficientwise, the limit again has `n` real roots.

## Implementation notes

**`import Mathlib` is retained deliberately, and the specific list beneath it is exact.** This
file builds against those modules alone.  What the blanket import still carries is the transitive
Mathlib that *consumers* of this file rely on: dropping it here leaves the shared tree green and
breaks a paper that imports it.  Removing it therefore belongs to a pass that sweeps every
consuming tree's imports in the same change, and a Mathlib PR would carry the specific list only.

Mathlib has the Cauchy root bound (`Polynomial.cauchyBound`) but neither of these; both follow from
`Polynomial.coeff_mul` being a finite sum, so no analysis beyond continuity of `+` and `*` enters.

## Tags

polynomial, characteristic polynomial, roots, continuity, splits
-/

open Filter Topology Polynomial

namespace Shields

/-! ### Coefficientwise continuity

A parametrized family of polynomials is *coefficientwise continuous* when each
coefficient varies continuously with the parameter.  The class is closed under
products because `coeff_mul` is a finite sum. -/

/-- Each coefficient of `p x` varies continuously with `x`. -/
def CoeffContinuous {X : Type*} [TopologicalSpace X] (p : X → Polynomial ℝ) : Prop :=
  ∀ k, Continuous fun x => (p x).coeff k

theorem CoeffContinuous.const {X : Type*} [TopologicalSpace X] (q : Polynomial ℝ) :
    CoeffContinuous fun _ : X => q := fun _ => continuous_const

theorem CoeffContinuous.mul {X : Type*} [TopologicalSpace X] {p q : X → Polynomial ℝ}
    (hp : CoeffContinuous p) (hq : CoeffContinuous q) :
    CoeffContinuous fun x => p x * q x := by
  intro k
  simp only [Polynomial.coeff_mul]
  exact continuous_finsetSum _ fun e _ => (hp e.1).mul (hq e.2)

theorem CoeffContinuous.sub {X : Type*} [TopologicalSpace X] {p q : X → Polynomial ℝ}
    (hp : CoeffContinuous p) (hq : CoeffContinuous q) :
    CoeffContinuous fun x => p x - q x := by
  intro k
  simp only [Polynomial.coeff_sub]
  exact (hp k).sub (hq k)

theorem CoeffContinuous.zsmul {X : Type*} [TopologicalSpace X] {p : X → Polynomial ℝ}
    (hp : CoeffContinuous p) (z : ℤ) : CoeffContinuous fun x => z • p x := by
  intro k
  simp only [Polynomial.coeff_smul]
  exact (hp k).const_smul z

theorem CoeffContinuous.sum {X ι : Type*} [TopologicalSpace X] {p : ι → X → Polynomial ℝ}
    (s : Finset ι) (h : ∀ i ∈ s, CoeffContinuous (p i)) :
    CoeffContinuous fun x => ∑ i ∈ s, p i x := by
  intro k
  simp only [Polynomial.finsetSum_coeff]
  exact continuous_finsetSum _ fun i hi => h i hi k

theorem CoeffContinuous.prod {X ι : Type*} [TopologicalSpace X]
    {p : ι → X → Polynomial ℝ} (s : Finset ι) (h : ∀ i ∈ s, CoeffContinuous (p i)) :
    CoeffContinuous fun x => ∏ i ∈ s, p i x := by
  classical
  induction s using Finset.induction with
  | empty => simpa using CoeffContinuous.const (X := X) 1
  | insert a s ha ih =>
      have hrest : CoeffContinuous fun x => ∏ i ∈ s, p i x :=
        ih fun i hi => h i (Finset.mem_insert_of_mem hi)
      have := (h a (Finset.mem_insert_self a s)).mul hrest
      simpa only [Finset.prod_insert ha] using this

/-- `X - C (r i)` is coefficientwise continuous in `r`. -/
theorem coeffContinuous_X_sub_C {ι : Type*} (i : ι) :
    CoeffContinuous fun r : ι → ℝ => (Polynomial.X - Polynomial.C (r i)) := by
  refine CoeffContinuous.sub (CoeffContinuous.const _) ?_
  intro k
  by_cases hk : k = 0
  · subst hk
    simpa using continuous_apply i
  · simpa [Polynomial.coeff_C, hk] using continuous_const (y := (0 : ℝ)) (X := (ι → ℝ))

/-- **The linear factorization is coefficientwise continuous in its roots.** -/
theorem coeffContinuous_prod_X_sub_C {n : ℕ} :
    CoeffContinuous fun r : Fin n → ℝ => ∏ i, (Polynomial.X - Polynomial.C (r i)) :=
  CoeffContinuous.prod _ fun i _ => coeffContinuous_X_sub_C i

/-! ### The characteristic polynomial

`charpoly M` is the determinant of `X • 1 - C M`, a sum over permutations of
products of entries each of which is linear in one entry of `M`.  So its
coefficients are continuous in `M`. -/

/-- Each entry of the characteristic matrix is coefficientwise continuous. -/
theorem coeffContinuous_charmatrix {n : ℕ} (i j : Fin n) :
    CoeffContinuous fun M : Matrix (Fin n) (Fin n) ℝ => Matrix.charmatrix M i j := by
  have hrw : ∀ M : Matrix (Fin n) (Fin n) ℝ, Matrix.charmatrix M i j
      = (if i = j then (Polynomial.X : Polynomial ℝ) else 0) - Polynomial.C (M i j) := by
    intro M
    by_cases h : i = j
    · subst h; simp [Matrix.charmatrix_apply_eq]
    · simp [Matrix.charmatrix_apply_ne, h]
  simp only [hrw]
  refine CoeffContinuous.sub (CoeffContinuous.const _) ?_
  intro k
  by_cases hk : k = 0
  · subst hk
    simpa [Function.comp_def] using (continuous_apply j).comp (continuous_apply i)
  · simpa [Polynomial.coeff_C, hk] using
      continuous_const (y := (0 : ℝ)) (X := Matrix (Fin n) (Fin n) ℝ)

/-- **The coefficients of the characteristic polynomial are continuous in the
matrix.**  This is what carries an entrywise matrix limit to a coefficientwise
limit of characteristic polynomials. -/
theorem coeffContinuous_charpoly {n : ℕ} :
    CoeffContinuous fun M : Matrix (Fin n) (Fin n) ℝ => M.charpoly := by
  have hrw : (fun M : Matrix (Fin n) (Fin n) ℝ => M.charpoly)
      = fun M => ∑ σ : Equiv.Perm (Fin n),
          Equiv.Perm.sign σ • ∏ i, Matrix.charmatrix M (σ i) i := by
    funext M
    rw [Matrix.charpoly, Matrix.det_apply]
  rw [hrw]
  refine CoeffContinuous.sum _ fun σ _ => ?_
  exact CoeffContinuous.zsmul
    (CoeffContinuous.prod _ fun i _ => coeffContinuous_charmatrix (σ i) i) _

/-! ### The limit -/

/-- The Cauchy bound of a monic polynomial is at most one more than a uniform bound on the
coefficients below its degree, since the leading coefficient it divides by is `1`. -/
theorem cauchyBound_le_of_monic {p : Polynomial ℝ} (hp : p.Monic) {B : NNReal}
    (hB : ∀ k ∈ Finset.range p.natDegree, ‖p.coeff k‖₊ ≤ B) :
    Polynomial.cauchyBound p ≤ B + 1 := by
  simp only [Polynomial.cauchyBound, hp.leadingCoeff, nnnorm_one, div_one]
  exact add_le_add (Finset.sup_le hB) le_rfl


/-- **A coefficientwise limit of split polynomials splits.**  If the monic
degree-`n` polynomials `∏_i (X - C (ρ_m i))` have coefficients converging to
those of `q`, then `q` is itself a product of `n` real linear factors, so its
root multiset has cardinality `n`.

The root vectors `ρ_m` lie in one compact box by Mathlib's `cauchyBound`, a convergent
subsequence has a limit `ρ_∞`, and coefficientwise continuity identifies `q` with
`∏_i (X - C (ρ_∞ i))`. -/
theorem card_roots_of_tendsto_coeff {n : ℕ} {ρ : ℕ → Fin n → ℝ} {q : Polynomial ℝ}
    (h : ∀ k, Tendsto (fun m => (∏ i, (Polynomial.X - Polynomial.C (ρ m i))).coeff k)
      atTop (𝓝 (q.coeff k))) :
    Multiset.card q.roots = n := by
  set p : ℕ → Polynomial ℝ := fun m => ∏ i, (Polynomial.X - Polynomial.C (ρ m i)) with hp
  have hmonic : ∀ m, (p m).Monic := fun m =>
    Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _
  have hdeg : ∀ m, (p m).natDegree = n := by
    intro m
    rw [hp]
    simp [Polynomial.natDegree_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C (ρ m i)]
  -- a uniform bound on the root vectors, from Mathlib's Cauchy bound
  have hbdd : ∀ k, ∃ C : NNReal, ∀ m, ‖(p m).coeff k‖₊ ≤ C := by
    intro k
    obtain ⟨C, hC⟩ := ((h k).abs).bddAbove_range
    refine ⟨⟨max C 0, le_max_right _ _⟩, fun m => NNReal.coe_le_coe.mp ?_⟩
    change ‖(p m).coeff k‖ ≤ max C 0
    rw [Real.norm_eq_abs]
    exact (hC ⟨m, rfl⟩).trans (le_max_left C 0)
  choose C hC using hbdd
  set Bnn : NNReal := ∑ k ∈ Finset.range n, C k with hBnn
  set R : ℝ := (Bnn : ℝ) + 1 with hR
  have hroot : ∀ m i, |ρ m i| ≤ R := by
    intro m i
    have hev : (p m).IsRoot (ρ m i) := by
      rw [Polynomial.IsRoot, hp, Polynomial.eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
    have hcb : Polynomial.cauchyBound (p m) ≤ Bnn + 1 :=
      cauchyBound_le_of_monic (hmonic m) fun k hk => (hC k m).trans
        (Finset.single_le_sum (f := C) (fun _ _ => zero_le) (by rwa [hdeg m] at hk))
    have hlt : ‖ρ m i‖₊ ≤ Bnn + 1 :=
      le_of_lt (lt_of_lt_of_le (hev.norm_lt_cauchyBound (hmonic m).ne_zero) hcb)
    calc |ρ m i| = ((‖ρ m i‖₊ : NNReal) : ℝ) := by rw [coe_nnnorm, Real.norm_eq_abs]
      _ ≤ ((Bnn + 1 : NNReal) : ℝ) := by exact_mod_cast hlt
      _ = R := by rw [hR]; push_cast; ring
  -- extract a convergent subsequence of root vectors
  set K : Set (Fin n → ℝ) := Set.Icc (fun _ => -R) (fun _ => R) with hK
  have hKc : IsCompact K := isCompact_Icc
  have hmem : ∀ m, ρ m ∈ K := fun m =>
    ⟨fun i => (abs_le.mp (hroot m i)).1, fun i => (abs_le.mp (hroot m i)).2⟩
  obtain ⟨rinf, -, φ, hφ, hlim⟩ := hKc.tendsto_subseq hmem
  -- the limit polynomial is the product of the limiting linear factors
  have hq : q = ∏ i, (Polynomial.X - Polynomial.C (rinf i)) := by
    refine Polynomial.ext fun k => ?_
    refine tendsto_nhds_unique ((h k).comp hφ.tendsto_atTop) ?_
    exact ((coeffContinuous_prod_X_sub_C (n := n) k).tendsto rinf).comp hlim
  rw [hq]
  have hrw : (∏ i, (Polynomial.X - Polynomial.C (rinf i)))
      = (((Finset.univ : Finset (Fin n)).val.map rinf).map
          fun a => Polynomial.X - Polynomial.C a).prod := by
    rw [Multiset.map_map]
    rfl
  rw [hrw, Polynomial.roots_multiset_prod_X_sub_C]
  simp


/-! ### Axiom footprint -/

/-- info: 'Shields.coeffContinuous_charpoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms coeffContinuous_charpoly

/-- info: 'Shields.card_roots_of_tendsto_coeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_roots_of_tendsto_coeff

end Shields
