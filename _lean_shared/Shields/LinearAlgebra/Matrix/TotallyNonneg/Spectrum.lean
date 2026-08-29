/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Shields.LinearAlgebra.Matrix.GantmacherKrein
import Shields.LinearAlgebra.Matrix.Charpoly.SplitLimit

/-!
# The spectrum of a matrix with nonnegative minors is real

Smoothing by a totally positive kernel, and the reality theorem it yields.

## Main results

* `Shields.gaussKernel`: the kernel `G_t = [t ^ ((i - j) ^ 2)]`, totally positive for `0 < t < 1`.
* `Shields.charpoly_roots_card_of_minorsNonneg`: **a matrix all of whose minors are nonnegative has
  a real spectrum** -- its characteristic polynomial has `n` real roots with multiplicity.

## Implementation notes

**No density theorem is used.** The classical route is Whitney's theorem -- approximate a totally
nonnegative matrix by totally *positive* ones -- which has no upstream Mathlib work and whose
standard proof runs through Neville elimination and a bidiagonal factorization.

Instead, smoothing gives `G_t A G_t`, whose `r`-th compound is `(∧^r G_t) (∧^r A) (∧^r G_t)` by
Cauchy--Binet. The outer factors are entrywise positive and the middle one entrywise nonnegative, so
each compound of `G_t A G_t` is **entrywise positive as soon as it is nonzero**, whatever the rank
of `A`. That dichotomy is all the ordering argument consumes: at each order where the compound
survives, strict dominance of its Perron root forces the product of the `r` eigenvalues of largest
modulus to be real and positive, and where it vanishes that product is zero. Either way the product
is real and the individual eigenvalues are its successive ratios -- so the **singular case is not
separate**.

`G_t` is totally positive because it is a positive diagonal conjugate of `[(q ^ i) ^ j]` with
`q = t ^ (-2)`, covered by `Shields.minorsPos_genVandermonde` directly. No summable Cauchy--Binet
over the expansion of `exp (x * y)` is needed.

## References

* [A. Pinkus, *Totally Positive Matrices*][Pinkus2010], Cor. 5.5

## Tags

total positivity, totally nonnegative, real spectrum, smoothing, compound matrix
-/

open Filter Topology

namespace Shields

variable {n : ℕ}

/-! ### A positive diagonal on either side preserves total positivity -/

/-- Scaling row `i` by `d i` and column `j` by `d j` multiplies every minor by a
positive factor, so it preserves strict positivity of the minors. -/
theorem minorsPos_diagConj {r : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : MinorsPos r A)
    {d : Fin n → ℝ} (hd : ∀ i, 0 < d i) :
    MinorsPos r (Matrix.of fun i j => d i * A i j * d j) := by
  intro f g hf hg
  have hsub : ((Matrix.of fun i j => d i * A i j * d j).submatrix f g)
      = Matrix.of fun a b => d (f a) * ((Matrix.of fun a b => d (g b) * (A.submatrix f g) a b)
          a b) := by
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.of_apply]
    ring
  rw [hsub, Matrix.det_mul_column, Matrix.det_mul_row]
  have h1 : 0 < ∏ a, d (f a) := Finset.prod_pos fun a _ => hd (f a)
  have h2 : 0 < ∏ b, d (g b) := Finset.prod_pos fun b _ => hd (g b)
  have h3 : 0 < (A.submatrix f g).det := hA f g hf hg
  positivity

/-! ### The kernel -/

/-- The Gaussian smoothing kernel `G_t = [t^{(i-j)^2}]`. -/
noncomputable def gaussKernel (n : ℕ) (t : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => t ^ (((i : ℤ) - (j : ℤ)).natAbs ^ 2)

@[simp] theorem gaussKernel_apply (t : ℝ) (i j : Fin n) :
    gaussKernel n t i j = t ^ (((i : ℤ) - (j : ℤ)).natAbs ^ 2) := rfl

/-- The exponent identity `(i-j)^2 + 2ij = i^2 + j^2`, over `ℕ`. -/
theorem natAbs_sub_sq_add (i j : ℕ) :
    ((i : ℤ) - (j : ℤ)).natAbs ^ 2 + 2 * (i * j) = i * i + j * j := by
  rcases le_total i j with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    have hna : ((i : ℤ) - ((i + d : ℕ) : ℤ)).natAbs = d := by push_cast; omega
    rw [hna]
    ring
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    have hna : ((((j + d : ℕ)) : ℤ) - (j : ℤ)).natAbs = d := by push_cast; omega
    rw [hna]
    ring

/-- **The kernel is a positive diagonal conjugate of a generalized Vandermonde
matrix.**  With `q = (t^2)^{-1}`, the `(i,j)` entry is `t^{i^2} (q^i)^j t^{j^2}`. -/
theorem gaussKernel_eq_diagConj {t : ℝ} (ht : 0 < t) :
    gaussKernel n t = Matrix.of fun i j : Fin n =>
      t ^ ((i : ℕ) * (i : ℕ))
        * genVandermonde (fun i : Fin n => ((t ^ 2)⁻¹) ^ (i : ℕ)) (fun j : Fin n => (j : ℕ)) i j
        * t ^ ((j : ℕ) * (j : ℕ)) := by
  ext i j
  have htne : t ≠ 0 := ne_of_gt ht
  have hkey : t ^ (((i : ℤ) - (j : ℤ)).natAbs ^ 2) * t ^ (2 * ((i : ℕ) * j))
      = t ^ ((i : ℕ) * (i : ℕ)) * t ^ ((j : ℕ) * (j : ℕ)) := by
    rw [← pow_add, natAbs_sub_sq_add, pow_add]
  have hpos : (0 : ℝ) < t ^ (2 * ((i : ℕ) * j)) := pow_pos ht _
  rw [gaussKernel_apply, Matrix.of_apply, genVandermonde]
  simp only [Matrix.of_apply, ← pow_mul]
  rw [inv_pow, show ((t ^ 2) ^ ((i : ℕ) * (j : ℕ)) : ℝ) = t ^ (2 * ((i : ℕ) * (j : ℕ))) from
    (pow_mul t 2 ((i : ℕ) * (j : ℕ))).symm]
  field_simp
  linear_combination hkey

/-- **The kernel is strictly totally positive** for `0 < t < 1`. -/
theorem minorsPos_gaussKernel {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (r : ℕ) :
    MinorsPos r (gaussKernel n t) := by
  have hq : (1 : ℝ) < (t ^ 2)⁻¹ := by
    rw [lt_inv_comm₀ (by norm_num) (by positivity)]
    nlinarith
  have hV : MinorsPos r (genVandermonde (fun i : Fin n => ((t ^ 2)⁻¹) ^ (i : ℕ))
      (fun j : Fin n => (j : ℕ))) := by
    refine minorsPos_genVandermonde ?_ (fun i => by positivity) (fun a b hab => hab) r
    intro a b hab
    exact pow_lt_pow_right₀ hq (by exact_mod_cast hab)
  rw [gaussKernel_eq_diagConj ht0]
  exact minorsPos_diagConj hV (fun i => by positivity)

/-! ### The kernel tends to the identity -/

/-- The smoothing parameters `t_m = 1/(m+2)`, a sequence in `(0,1)` tending to `0`. -/
noncomputable def smoothParam (m : ℕ) : ℝ := 1 / (m + 2)

theorem smoothParam_pos (m : ℕ) : 0 < smoothParam m := by
  rw [smoothParam]
  positivity

theorem smoothParam_lt_one (m : ℕ) : smoothParam m < 1 := by
  rw [smoothParam, div_lt_one (by positivity)]
  have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith

theorem tendsto_smoothParam : Tendsto smoothParam atTop (𝓝 0) := by
  have h : Tendsto (fun m : ℕ => (m : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  exact Filter.Tendsto.congr (fun m => by simp [smoothParam, one_div]) h.inv_tendsto_atTop

/-- **The kernel tends entrywise to the identity** along the parameter sequence.
The diagonal entries are `t^0 = 1`; every off-diagonal entry is `t^d` with
`d ≥ 1`. -/
theorem tendsto_gaussKernel (n : ℕ) :
    Tendsto (fun m => gaussKernel n (smoothParam m)) atTop (𝓝 1) := by
  refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
  by_cases hij : i = j
  · subst hij
    simp [Matrix.one_apply_eq]
  · have hd : ((i : ℤ) - (j : ℤ)).natAbs ^ 2 ≠ 0 := by
      refine pow_ne_zero 2 ?_
      simp only [ne_eq, Int.natAbs_eq_zero, sub_eq_zero]
      intro hc
      exact hij (Fin.ext (by exact_mod_cast hc))
    have := tendsto_smoothParam.pow (((i : ℤ) - (j : ℤ)).natAbs ^ 2)
    rw [zero_pow hd] at this
    simpa [Matrix.one_apply_ne hij] using this

/-! ### The compound dichotomy -/

/-- **A nonnegative matrix sandwiched between two positive ones is positive**,
unless it is zero. -/
theorem pos_of_pos_mul_mul_pos {ι : Type*} [Fintype ι]
    {P N Q : Matrix ι ι ℝ} (hP : ∀ i j, 0 < P i j) (hQ : ∀ i j, 0 < Q i j)
    (hN : ∀ i j, 0 ≤ N i j) (hNne : N ≠ 0) (i j : ι) : 0 < (P * N * Q) i j := by
  obtain ⟨k, l, hkl⟩ : ∃ k l, N k l ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hNne (Matrix.ext fun k l => by simp [hc k l])
  have hklpos : 0 < N k l := lt_of_le_of_ne (hN k l) (Ne.symm hkl)
  have hPNnn : ∀ a b, 0 ≤ (P * N) a b := fun a b =>
    Finset.sum_nonneg fun c _ => mul_nonneg (hP a c).le (hN c b)
  have hinner : 0 < (P * N) i l :=
    lt_of_lt_of_le (mul_pos (hP i k) hklpos)
      (Finset.single_le_sum (f := fun c => P i c * N c l)
        (fun c _ => mul_nonneg (hP i c).le (hN c l)) (Finset.mem_univ k))
  refine lt_of_lt_of_le (mul_pos hinner (hQ l j)) ?_
  exact Finset.single_le_sum (f := fun c => (P * N) i c * Q c j)
    (fun c _ => mul_nonneg (hPNnn i c) (hQ c j).le) (Finset.mem_univ l)

/-- **The compound dichotomy.**  Each compound of `G_t A G_t` is entrywise
positive as soon as it is nonzero.  Cauchy–Binet turns `∧^r(G A G)` into
`(∧^r G)(∧^r A)(∧^r G)`; the outer factors are entrywise positive because `G_t`
is totally positive, and the middle one is entrywise nonnegative because `A` is
totally nonnegative. -/
theorem compound_smoothed_pos {r : ℕ} {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : ∀ k, MinorsNonneg k A)
    (hne : compound r (gaussKernel n t * A * gaussKernel n t) ≠ 0)
    (f g : increasingSelections r n) :
    0 < compound r (gaussKernel n t * A * gaussKernel n t) f g := by
  have hfac : compound r (gaussKernel n t * A * gaussKernel n t)
      = compound r (gaussKernel n t) * compound r A * compound r (gaussKernel n t) := by
    rw [compound_mul, compound_mul]
  have hP : ∀ u v : increasingSelections r n, 0 < compound r (gaussKernel n t) u v :=
    fun u v => minorsPos_gaussKernel ht0 ht1 r u.1 v.1 u.2 v.2
  have hN : ∀ u v : increasingSelections r n, 0 ≤ compound r A u v :=
    fun u v => compound_entry_nonneg hA r u v
  have hNne : compound r A ≠ 0 := by
    intro hc
    exact hne (by rw [hfac, hc, Matrix.mul_zero, Matrix.zero_mul])
  rw [hfac]
  exact pos_of_pos_mul_mul_pos hP hP hN hNne f g

/-! ### Reality of totally nonnegative spectra -/

/-- **The characteristic polynomial of a totally nonnegative real matrix splits
over `ℝ`.**  This is the reality half of
Cor. 5.5 of [Pinkus2010]; with `charpoly_roots_nonneg` it is the whole of that
corollary.

`G_t A G_t` is totally nonnegative with the compound dichotomy, so
`GantmacherKrein.exists_charpoly_eq_prod_of_compound_pos` factors its
characteristic polynomial into real linear factors; the matrices converge to `A`,
their characteristic polynomials converge coefficientwise, and
`SplitLimit.card_roots_of_tendsto_coeff` carries the factorization to the limit.
The rank of `A` never enters, so the singular case needs no separate argument. -/
theorem charpoly_roots_card_of_minorsNonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ k, MinorsNonneg k A) :
    Multiset.card A.charpoly.roots = n := by
  set B : ℕ → Matrix (Fin n) (Fin n) ℝ :=
    fun m => gaussKernel n (smoothParam m) * A * gaussKernel n (smoothParam m) with hBdef
  have hsplit : ∀ m, ∃ ν : Fin n → ℝ,
      (B m).charpoly = ∏ i, (Polynomial.X - Polynomial.C (ν i)) := by
    intro m
    refine exists_charpoly_eq_prod_of_compound_pos (B m) fun r _ hne f g => ?_
    exact compound_smoothed_pos (smoothParam_pos m) (smoothParam_lt_one m) hA hne f g
  choose ν hν using hsplit
  have htend : Tendsto B atTop (𝓝 A) := by
    have h1 := tendsto_gaussKernel n
    have h2 := (h1.mul (tendsto_const_nhds (x := A))).mul h1
    simpa [hBdef] using h2
  refine card_roots_of_tendsto_coeff (ρ := ν) (q := A.charpoly) fun k => ?_
  have h3 := ((coeffContinuous_charpoly (n := n) k).tendsto A).comp htend
  simpa [Function.comp_def, hν] using h3

/-- **The reality theorem is not vacuous.**  The generalized Vandermonde matrix
at strictly increasing positive nodes and strictly increasing exponents is
totally nonnegative at every order, so its characteristic polynomial splits over
`ℝ`.  This instantiates the theorem at every size, on a family whose minors are
in fact all strictly positive. -/
theorem genVandermonde_charpoly_roots_card {m : ℕ} {x : Fin m → ℝ} {k : Fin m → ℕ}
    (hx : StrictMono x) (hxpos : ∀ i, 0 < x i) (hk : StrictMono k) :
    Multiset.card (genVandermonde x k).charpoly.roots = m :=
  charpoly_roots_card_of_minorsNonneg _ fun r => minorsNonneg_genVandermonde hx hxpos hk r


/-! ### Axiom footprint -/

/-- info: 'Shields.charpoly_roots_card_of_minorsNonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms charpoly_roots_card_of_minorsNonneg

end Shields
