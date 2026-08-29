/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Shields.LinearAlgebra.Matrix.Charpoly.Basic
import Shields.LinearAlgebra.Matrix.GenVandermonde
import Shields.Order.Monotone.TopSelection

/-!
# From the compound spectrum to the eigenvalues

Comparing the Perron roots of the successive compounds `∧^r A` recovers the individual eigenvalues,
which is the Gantmacher--Krein route to reality of the spectrum.

## Main results

* `Shields.perronRoot_compound_eq_prod`: the Perron root of `∧^r A` is the product of the `r`
  eigenvalues of `A` of largest modulus.
* `Shields.exists_charpoly_eq_prod_of_compound_pos`: with every surviving compound entrywise
  positive, the characteristic polynomial splits over `ℝ`.

## Implementation notes

Only strict dominance of the Perron root is used, never algebraic simplicity, so
`Shields.PerronFrobenius` need not supply the latter.

A single triangularization is pulled out in front of every order at once -- comparing orders needs
the *same* triangular form at each `r`, not one per order.

The rearrangement bound the ordering argument runs on is about increasing selections rather than
about matrices, and is `Shields.Order.Monotone.TopSelection`.

## References

* [F. R. Gantmacher and M. G. Krein, *Oscillation Matrices and Kernels and Small Vibrations of
  Mechanical Systems*][GantmacherKrein2002]

## Tags

Gantmacher-Krein, compound matrix, Perron root, eigenvalue, total positivity
-/

namespace Shields

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The Perron root is a root of the characteristic polynomial.** -/
theorem charpoly_eval_perronRoot [Nonempty ι] {A : Matrix ι ι ℝ}
    (hA : ∀ i j, 0 < A i j) : A.charpoly.eval (perronRoot A) = 0 := by
  obtain ⟨-, x, hxpos, hx, heig⟩ := exists_perron_eigenvector A hA
  refine charpoly_eval_eq_zero_of_mulVec (x := x) ?_ heig
  intro h0
  exact absurd (congrFun h0 (Classical.arbitrary ι)) (hxpos _).ne'

/-- The compound commutes with a ring map, since determinants do. -/
theorem compound_map {n : ℕ} {S : Type*} [CommRing S] (r : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ) (φ : ℝ →+* S) :
    compound r (A.map φ) = (compound r A).map φ := by
  ext f g
  simp only [compound_apply, Matrix.map_apply]
  rw [RingHom.map_det]
  rfl

/-- **The Perron root of the `r`-th compound is a product of `r` eigenvalues.**
When the compound has all its entries positive it has a Perron root, and that
root equals `∏_a λ_{f a}` for some increasing selection `f`, where the `λ` are the
diagonal entries of a triangularizing form of `A` over `ℂ` — that is, its
eigenvalues.  The triangular form is passed in rather than produced here, so that
several orders `r` can be compared against one enumeration of the eigenvalues.

This is the step of Gantmacher–Krein that turns the Perron theory into a
statement about the eigenvalues of `A` itself. -/
theorem perronRoot_compound_eq_prod {n r : ℕ} [Nonempty (increasingSelections r n)]
    {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ f g : increasingSelections r n, 0 < compound r A f g)
    {T : Matrix (Fin n) (Fin n) ℂ}
    (hT : (compound r (A.map (algebraMap ℝ ℂ))).charpoly
      = ∏ f : increasingSelections r n,
          (Polynomial.X - Polynomial.C (∏ a, T (f.1 a) (f.1 a)))) :
    ∃ f : increasingSelections r n,
      ((perronRoot (compound r A) : ℝ) : ℂ) = ∏ a, T (f.1 a) (f.1 a) := by
  -- the Perron root is a real root of the compound's characteristic polynomial
  have hroot : (compound r A).charpoly.eval (perronRoot (compound r A)) = 0 :=
    charpoly_eval_perronRoot hA
  have hmap : (compound r (A.map (algebraMap ℝ ℂ))).charpoly
      = ((compound r A).charpoly).map (algebraMap ℝ ℂ) := by
    rw [compound_map, Matrix.charpoly_map]
  have hz : ((compound r A).charpoly.map (algebraMap ℝ ℂ)).eval
      ((perronRoot (compound r A) : ℝ) : ℂ) = 0 := by
    rw [Polynomial.eval_map,
      show ((perronRoot (compound r A) : ℝ) : ℂ)
        = algebraMap ℝ ℂ (perronRoot (compound r A)) from rfl,
      Polynomial.eval₂_hom, hroot, map_zero]
  rw [← hmap, hT, Polynomial.eval_prod] at hz
  obtain ⟨f, -, hf⟩ := Finset.prod_eq_zero_iff.mp hz
  refine ⟨f, ?_⟩
  rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hf
  exact hf

/-! ### Ordering the eigenvalues by modulus

The remaining step of Gantmacher–Krein.  With the eigenvalues sorted by
decreasing modulus, the modulus-maximal `r`-fold product is the product of the
first `r`, so strict dominance of the Perron root of `∧^r A` makes that product
real; the individual eigenvalues are then the successive ratios. -/

/-- Every `r`-fold product of eigenvalues along an increasing selection is a root of the
characteristic polynomial of the `r`-th compound. -/
theorem eval_charpoly_compound_prod {n r : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} {lam : Fin n → ℂ}
    (hT : (compound r M).charpoly
      = ∏ f : increasingSelections r n, (Polynomial.X - Polynomial.C (∏ a, lam (f.1 a))))
    {f : Fin r → Fin n} (hf : StrictMono f) :
    (compound r M).charpoly.eval (∏ x, lam (f x)) = 0 := by
  rw [hT, Polynomial.eval_prod]
  refine Finset.prod_eq_zero
    (Finset.mem_univ (⟨f, mem_increasingSelections.mpr hf⟩ : increasingSelections r n)) ?_
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero]

/-- **A modulus-maximal `r`-fold product of eigenvalues is a nonnegative real.**  The products
`∏_a λ_{u a}` along selections of `r` eigenvalues are the roots of the characteristic polynomial
of `∧^r B`.  When `∧^r B` is nonzero its entries are positive, so its Perron root is the
modulus-largest of those roots and is real and positive; a product attaining that modulus
therefore equals it.  A vanishing product is real outright. -/
theorem nonneg_real_of_maximal_prod {n r : ℕ} (hrn : r ≤ n) {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : compound r B ≠ 0 → ∀ f g : increasingSelections r n, 0 < compound r B f g)
    {T : Matrix (Fin n) (Fin n) ℂ}
    (hTcomp : (compound r (B.map (algebraMap ℝ ℂ))).charpoly
      = ∏ f : increasingSelections r n,
          (Polynomial.X - Polynomial.C (∏ a, T (f.1 a) (f.1 a))))
    {u : Fin r → Fin n} (hu : Function.Injective u)
    (hmax : ∀ f : Fin r → Fin n, StrictMono f →
      ‖∏ x, T (f x) (f x)‖ ≤ ‖∏ x, T (u x) (u x)‖) :
    ∃ v : ℝ, 0 ≤ v ∧ ∏ x, T (u x) (u x) = (v : ℂ) := by
  obtain ⟨g, hg, hgeq⟩ := exists_strictMono_prod_eq hu (fun i => T i i)
  have hroot : (compound r (B.map (algebraMap ℝ ℂ))).charpoly.eval
      (∏ x, T (u x) (u x)) = 0 := by
    rw [hgeq]
    exact eval_charpoly_compound_prod (lam := fun i => T i i) hTcomp hg
  by_cases hz : ∏ x, T (u x) (u x) = 0
  · exact ⟨0, le_refl 0, by simp [hz]⟩
  haveI : Nonempty (increasingSelections r n) := increasingSelections_nonempty hrn
  have hmap : compound r (B.map (algebraMap ℝ ℂ))
      = (compound r B).map (fun x : ℝ => (x : ℂ)) := by
    rw [compound_map]; rfl
  have hMne : compound r B ≠ 0 := fun hc =>
    hz (eq_zero_of_charpoly_zero_root (ι := increasingSelections r n)
      (by rw [show (0 : Matrix (increasingSelections r n) (increasingSelections r n) ℂ)
            = compound r (B.map (algebraMap ℝ ℂ)) by rw [hmap, hc]; ext a b; simp]
          exact hroot))
  have hpos := hB hMne
  have hrho : 0 < perronRoot (compound r B) := (exists_perron_eigenvector _ hpos).1
  obtain ⟨f₀, hf₀⟩ := perronRoot_compound_eq_prod hpos hTcomp
  have hle : perronRoot (compound r B) ≤ ‖∏ x, T (u x) (u x)‖ := by
    have hb := hmax f₀.1 (mem_increasingSelections.mp f₀.2)
    rwa [← hf₀, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrho] at hb
  obtain ⟨z, hzne, heig⟩ := exists_eigenvector_of_charpoly_root hroot
  rw [hmap] at heig
  exact ⟨_, hrho.le, eq_perronRoot_of_norm_eq hpos hzne heig
    (le_antisymm (norm_le_perronRoot hpos hzne heig) hle)⟩

/-- **Gantmacher–Krein reality under the compound dichotomy.**  If every compound
of `B` that is nonzero has all its entries strictly positive, then the
characteristic polynomial of `B` is a product of real linear factors.

Sort the eigenvalues by decreasing modulus.  For each order `r`, the product of
the first `r` is one of the roots of the characteristic polynomial of `∧^r B`,
and by the rearrangement bound it is the one of largest modulus, hence a
nonnegative real.  The individual eigenvalues are the successive ratios. -/
theorem exists_charpoly_eq_prod_of_compound_pos {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : ∀ r, r ≤ n → compound r B ≠ 0 →
      ∀ f g : increasingSelections r n, 0 < compound r B f g) :
    ∃ ν : Fin n → ℝ, B.charpoly = ∏ i, (Polynomial.X - Polynomial.C (ν i)) := by
  obtain ⟨T, hTtri, hTcp, hTcomp⟩ := charpoly_compound_complex (B.map (algebraMap ℝ ℂ))
  obtain ⟨σ, hanti⟩ := exists_perm_norm_antitone (fun i => T i i)
  have hPreal : ∀ r : ℕ, r ≤ n → ∃ v : ℝ, 0 ≤ v ∧
      ∏ c ∈ Finset.univ.filter (fun c : Fin n => (c : ℕ) < r),
        T (σ c) (σ c) = (v : ℂ) := by
    intro r hrn
    rw [prod_filter_val_lt hrn fun c => T (σ c) (σ c)]
    refine nonneg_real_of_maximal_prod hrn (hB r hrn) (hTcomp r)
      (σ.injective.comp (strictMono_topSel hrn).injective) fun f hf => ?_
    simpa using norm_prod_le_norm_prod_topSel hrn (mu := fun c => T (σ c) (σ c)) hanti
      (σ.symm.injective.comp hf.injective)
  have hall : ∀ i : Fin n, ∃ v : ℝ, T i i = (v : ℂ) := fun i => by
    simpa using real_of_prod_initial_real hanti hPreal (σ.symm i)
  choose ν hν using hall
  refine ⟨ν, Polynomial.map_injective (algebraMap ℝ ℂ) (algebraMap ℝ ℂ).injective ?_⟩
  rw [← Matrix.charpoly_map, hTcp, charpoly_eq_prod_diag_of_upperTriangular hTtri,
    Polynomial.map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hν i]
  rfl


/-! ### Axiom footprint -/

/-- info: 'Shields.exists_charpoly_eq_prod_of_compound_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_charpoly_eq_prod_of_compound_pos

end Shields
