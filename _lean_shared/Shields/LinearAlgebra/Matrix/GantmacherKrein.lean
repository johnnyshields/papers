/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Shields.LinearAlgebra.Matrix.GenVandermonde

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

## References

* [F. R. Gantmacher and M. G. Krein, *Oscillation Matrices and Kernels and Small Vibrations of
  Mechanical Systems*][GantmacherKrein2002]

## Tags

Gantmacher-Krein, compound matrix, Perron root, eigenvalue, total positivity
-/

namespace Shields

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- An eigenvector in the `mulVec` sense makes its eigenvalue a root of the
characteristic polynomial. -/
theorem charpoly_eval_eq_zero_of_mulVec {A : Matrix ι ι ℝ} {mu : ℝ}
    {x : ι → ℝ} (hx : x ≠ 0) (h : A *ᵥ x = mu • x) : A.charpoly.eval mu = 0 := by
  rw [Matrix.eval_charpoly, ← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨x, hx, ?_⟩
  have hscal : (Matrix.scalar ι mu) *ᵥ x = mu • x := by
    ext i
    simp [Matrix.scalar_apply, Matrix.mulVec, dotProduct, Matrix.diagonal_apply,
      Finset.sum_ite_eq]
  rw [Matrix.sub_mulVec, hscal, h, sub_self]

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

/-! ### From the compound spectrum to the eigenvalues

`TotallyNonneg.charpoly_compound_complex` supplies one triangular form serving
every order at once, which is what the ordering argument needs: it compares
different orders against each other, so the eigenvalue enumeration has to be the
same at each. -/

/-- A root of the characteristic polynomial has an eigenvector. -/
theorem exists_eigenvector_of_charpoly_root {M : Matrix ι ι ℂ} {mu : ℂ}
    (h : M.charpoly.eval mu = 0) : ∃ z : ι → ℂ, z ≠ 0 ∧ M *ᵥ z = mu • z := by
  rw [Matrix.eval_charpoly] at h
  obtain ⟨z, hz, hzero⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  refine ⟨z, hz, ?_⟩
  have hscal : (Matrix.scalar ι mu) *ᵥ z = mu • z := by
    ext i
    simp [Matrix.scalar_apply, Matrix.mulVec, dotProduct, Matrix.diagonal_apply,
      Finset.sum_ite_eq]
  rw [Matrix.sub_mulVec, hscal] at hzero
  exact (sub_eq_zero.mp hzero).symm

/-! ### Ordering the eigenvalues by modulus

The remaining step of Gantmacher–Krein.  With the eigenvalues sorted by
decreasing modulus, the modulus-maximal `r`-fold product is the product of the
first `r`, so strict dominance of the Perron root of `∧^r A` makes that product
real; the individual eigenvalues are then the successive ratios. -/

/-- The first `r` indices of `Fin n`, as a strictly monotone selection.  This is
Mathlib's `Fin.castLE`; the abbreviation names the role it plays below. -/
abbrev topSel {r n : ℕ} (hrn : r ≤ n) : Fin r → Fin n := Fin.castLE hrn

theorem strictMono_topSel {r n : ℕ} (hrn : r ≤ n) : StrictMono (topSel hrn) :=
  Fin.strictMono_castLE hrn

/-- A strictly monotone selection dominates the identity on indices. -/
theorem le_val_of_strictMono {r n : ℕ} {f : Fin r → Fin n} (hf : StrictMono f) :
    ∀ (m : ℕ) (hm : m < r), m ≤ (f ⟨m, hm⟩ : ℕ) := by
  intro m
  induction m with
  | zero => intro _; exact Nat.zero_le _
  | succ p ih =>
      intro hm
      have hp : p < r := Nat.lt_of_succ_lt hm
      have h1 : (f ⟨p, hp⟩ : ℕ) < (f ⟨p + 1, hm⟩ : ℕ) := hf (by simp [Fin.lt_def])
      have h2 := ih hp
      omega

/-- A product over an injective family is a product over the increasing
enumeration of its image. -/
theorem exists_strictMono_prod_eq {M : Type*} [CommMonoid M] {r n : ℕ}
    {u : Fin r → Fin n} (hu : Function.Injective u) (F : Fin n → M) :
    ∃ g : Fin r → Fin n, StrictMono g ∧ ∏ x, F (u x) = ∏ x, F (g x) := by
  have hcard : (Finset.image u Finset.univ).card = r := by
    rw [Finset.card_image_of_injective _ hu, Finset.card_univ, Fintype.card_fin]
  refine ⟨(Finset.image u Finset.univ).orderEmbOfFin hcard,
    (Finset.orderEmbOfFin _ hcard).strictMono, ?_⟩
  have h1 : ∏ b ∈ Finset.image u Finset.univ, F b = ∏ x, F (u x) :=
    Finset.prod_image fun x _ y _ h => hu h
  have h2 : ∏ b ∈ Finset.image ((Finset.image u Finset.univ).orderEmbOfFin hcard)
      Finset.univ, F b = ∏ x, F ((Finset.image u Finset.univ).orderEmbOfFin hcard x) :=
    Finset.prod_image fun x _ y _ h =>
      (Finset.orderEmbOfFin _ hcard).injective h
  rw [← h1, ← h2, Finset.image_orderEmbOfFin_univ]

/-- The first `r` indices, as a `Finset`. -/
theorem prod_filter_val_lt {M : Type*} [CommMonoid M] {r n : ℕ} (hrn : r ≤ n)
    (F : Fin n → M) :
    ∏ c ∈ Finset.univ.filter (fun c : Fin n => (c : ℕ) < r), F c
      = ∏ x : Fin r, F (topSel hrn x) := by
  have himg : (Finset.univ.filter (fun c : Fin n => (c : ℕ) < r))
      = Finset.image (topSel hrn) Finset.univ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hi
      exact ⟨⟨(i : ℕ), hi⟩, rfl⟩
    · rintro ⟨c, rfl⟩
      exact c.2
  rw [himg]
  exact Finset.prod_image fun x _ y _ h =>
    Fin.ext (by simpa [topSel] using congrArg Fin.val h)

/-- **The largest `r`-fold product is the product of the `r` largest.**  For an
antitone nonnegative sequence, no strictly monotone selection of `r` terms beats
the initial segment. -/
theorem prod_le_prod_topSel {n r : ℕ} (hrn : r ≤ n) {a : Fin n → ℝ}
    (hnn : ∀ c, 0 ≤ a c) (hanti : ∀ c d : Fin n, c ≤ d → a d ≤ a c)
    {g : Fin r → Fin n} (hg : StrictMono g) :
    ∏ x, a (g x) ≤ ∏ x, a (topSel hrn x) := by
  refine Finset.prod_le_prod (fun x _ => hnn _) fun x _ => ?_
  refine hanti _ _ ?_
  have := le_val_of_strictMono hg (x : ℕ) x.2
  rw [Fin.le_def]
  simpa [topSel] using this

/-- The characteristic polynomial of the zero matrix has only `0` as a root.
`Matrix.charpoly_zero` gives it as `X ^ card ι` outright; on an empty `ι` that is
the constant `1`, which has no root at all. -/
theorem eq_zero_of_charpoly_zero_root {mu : ℂ}
    (h : (0 : Matrix ι ι ℂ).charpoly.eval mu = 0) : mu = 0 := by
  rw [Matrix.charpoly_zero, Polynomial.eval_pow, Polynomial.eval_X] at h
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with hc | hc
  · rw [hc, pow_zero] at h
    exact absurd h one_ne_zero
  · exact (pow_eq_zero_iff hc.ne').mp h

/-- The characteristic polynomial of a triangular matrix is the product of `X - T i i` over the
diagonal.  Mathlib's `Matrix.charpoly_of_upperTriangular` asks for `BlockTriangular id`; this is
the entrywise form. -/
theorem charpoly_eq_prod_diag_of_upperTriangular {R : Type*} [CommRing R] {m : ℕ}
    {T : Matrix (Fin m) (Fin m) R} (hT : ∀ i j, j < i → T i j = 0) :
    T.charpoly = ∏ i, (Polynomial.X - Polynomial.C (T i i)) :=
  Matrix.charpoly_of_upperTriangular T fun _ _ hij => hT _ _ hij

/-- **Gantmacher–Krein reality under the compound dichotomy.**  If every compound
of `B` that is nonzero has all its entries strictly positive, then the
characteristic polynomial of `B` is a product of real linear factors.

Sort the eigenvalues by decreasing modulus.  For each order `r`, the product of
the first `r` is one of the roots of the characteristic polynomial of `∧^r B`,
and by the rearrangement bound it is the one of largest modulus; when `∧^r B` is
nonzero its Perron root is that maximal modulus, and strict dominance forces the
product itself to equal the Perron root, hence to be real and positive.  When the
product vanishes it is real outright.  The individual eigenvalues are the
successive ratios, and where a ratio is undefined the eigenvalue is zero because
the moduli are decreasing. -/
theorem exists_charpoly_eq_prod_of_compound_pos {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : ∀ r, r ≤ n → compound r B ≠ 0 →
      ∀ f g : increasingSelections r n, 0 < compound r B f g) :
    ∃ ν : Fin n → ℝ, B.charpoly = ∏ i, (Polynomial.X - Polynomial.C (ν i)) := by
  obtain ⟨T, hTtri, hTcp, hTcomp⟩ := charpoly_compound_complex (B.map (algebraMap ℝ ℂ))
  set lam : Fin n → ℂ := fun i => T i i with hlamdef
  have hsplitC : (B.map (algebraMap ℝ ℂ)).charpoly
      = ∏ i, (Polynomial.X - Polynomial.C (lam i)) := by
    rw [hTcp, charpoly_eq_prod_diag_of_upperTriangular hTtri]
  -- the eigenvalues sorted by decreasing modulus
  set σ : Equiv.Perm (Fin n) := Tuple.sort (fun i => -‖lam i‖) with hσdef
  set a : Fin n → ℝ := fun c => ‖lam (σ c)‖ with hadef
  have hann : ∀ c, 0 ≤ a c := fun c => norm_nonneg _
  have hanti : ∀ c d : Fin n, c ≤ d → a d ≤ a c := by
    intro c d hcd
    have hm := Tuple.monotone_sort (fun i => -‖lam i‖) hcd
    simp only [Function.comp_apply] at hm
    simp only [hadef]
    linarith
  -- the product of the `r` largest
  set L : ℕ → Finset (Fin n) := fun r => Finset.univ.filter (fun c : Fin n => (c : ℕ) < r)
    with hLdef
  set P : ℕ → ℂ := fun r => ∏ c ∈ L r, lam (σ c) with hPdef
  have hPtop : ∀ (r : ℕ) (hrn : r ≤ n), P r = ∏ x : Fin r, lam (σ (topSel hrn x)) :=
    fun r hrn => prod_filter_val_lt hrn (fun c => lam (σ c))
  have hPnorm : ∀ (r : ℕ) (hrn : r ≤ n), ‖P r‖ = ∏ x : Fin r, a (topSel hrn x) := by
    intro r hrn
    rw [hPtop r hrn, norm_prod]
  have hinjtop : ∀ (r : ℕ) (hrn : r ≤ n),
      Function.Injective (fun x : Fin r => σ (topSel hrn x)) :=
    fun r hrn => σ.injective.comp (strictMono_topSel hrn).injective
  -- every `r`-fold product along an increasing selection is a root of the compound
  have hrootsel : ∀ (r : ℕ) (f : Fin r → Fin n), StrictMono f →
      (compound r (B.map (algebraMap ℝ ℂ))).charpoly.eval (∏ x, lam (f x)) = 0 := by
    intro r f hf
    rw [hTcomp r, Polynomial.eval_prod]
    refine Finset.prod_eq_zero
      (Finset.mem_univ (⟨f, mem_increasingSelections.mpr hf⟩ : increasingSelections r n)) ?_
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero]
    rfl
  have hProot : ∀ (r : ℕ) (hrn : r ≤ n),
      (compound r (B.map (algebraMap ℝ ℂ))).charpoly.eval (P r) = 0 := by
    intro r hrn
    obtain ⟨g, hg, hgeq⟩ :=
      exists_strictMono_prod_eq (hinjtop r hrn) lam
    rw [hPtop r hrn, hgeq]
    exact hrootsel r g hg
  -- the rearrangement bound
  have hnormle : ∀ (r : ℕ) (hrn : r ≤ n) (f : Fin r → Fin n), StrictMono f →
      ‖∏ x, lam (f x)‖ ≤ ‖P r‖ := by
    intro r hrn f hf
    rw [norm_prod, hPnorm r hrn]
    have hconv : ∀ x : Fin r, ‖lam (f x)‖ = a (σ.symm (f x)) := by
      intro x
      simp [hadef]
    rw [Finset.prod_congr rfl fun x _ => hconv x]
    obtain ⟨g, hg, hgeq⟩ := exists_strictMono_prod_eq
      (u := fun x : Fin r => σ.symm (f x)) (σ.symm.injective.comp hf.injective) a
    rw [hgeq]
    exact prod_le_prod_topSel hrn hann hanti hg
  -- the compound matrix over ℂ is the complexification of the real one
  have hmapfun : ∀ r : ℕ, (compound r (B.map (algebraMap ℝ ℂ)))
      = (compound r B).map (fun x : ℝ => (x : ℂ)) := by
    intro r
    rw [compound_map]
    rfl
  -- each such product is a nonnegative real
  have hPreal : ∀ (r : ℕ), r ≤ n → ∃ v : ℝ, 0 ≤ v ∧ P r = (v : ℂ) := by
    intro r hrn
    by_cases hz : P r = 0
    · exact ⟨0, le_refl 0, by simp [hz]⟩
    haveI : Nonempty (increasingSelections r n) := increasingSelections_nonempty hrn
    -- a vanishing compound would force the product to vanish
    have hMne : compound r B ≠ 0 := by
      intro hc
      refine hz (eq_zero_of_charpoly_zero_root (ι := increasingSelections r n) ?_)
      have h0 : compound r (B.map (algebraMap ℝ ℂ)) = 0 := by
        rw [hmapfun r, hc]
        ext u v
        simp
      rw [← h0]
      exact hProot r hrn
    have hpos : ∀ f g : increasingSelections r n, 0 < compound r B f g := hB r hrn hMne
    set rho := perronRoot (compound r B) with hrhodef
    have hrhopos : 0 < rho := (exists_perron_eigenvector (compound r B) hpos).1
    -- the Perron root is one of the `r`-fold products, so it is at most `‖P r‖`
    obtain ⟨f₀, hf₀⟩ := perronRoot_compound_eq_prod hpos (hTcomp r)
    have hle1 : rho ≤ ‖P r‖ := by
      have hb := hnormle r hrn f₀.1 (mem_increasingSelections.mp f₀.2)
      have hlam : ∏ x, lam (f₀.1 x) = ((rho : ℝ) : ℂ) := hf₀.symm
      rw [hlam, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrhopos] at hb
      exact hb
    obtain ⟨z, hzne, heig⟩ := exists_eigenvector_of_charpoly_root (hProot r hrn)
    rw [hmapfun r] at heig
    have hle2 : ‖P r‖ ≤ rho := norm_le_perronRoot hpos hzne heig
    exact ⟨rho, hrhopos.le, eq_perronRoot_of_norm_eq hpos hzne heig (le_antisymm hle2 hle1)⟩
  -- the sorted eigenvalues are the successive ratios, hence real
  have hlamsorted : ∀ c : Fin n, ∃ v : ℝ, lam (σ c) = (v : ℂ) := by
    intro c
    obtain ⟨v1, -, hv1⟩ := hPreal ((c : ℕ) + 1) c.2
    obtain ⟨v0, -, hv0⟩ := hPreal (c : ℕ) (le_of_lt c.2)
    have hstep : P ((c : ℕ) + 1) = P (c : ℕ) * lam (σ c) := by
      have hins : L ((c : ℕ) + 1) = insert c (L (c : ℕ)) := by
        ext i
        simp only [hLdef, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        constructor
        · intro hi
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
          · exact Or.inr h
          · exact Or.inl (Fin.ext h)
        · rintro (rfl | h)
          · omega
          · omega
      have hnotmem : c ∉ L (c : ℕ) := by simp [hLdef]
      simp only [hPdef]
      rw [hins, Finset.prod_insert hnotmem, mul_comm]
    by_cases hv0z : v0 = 0
    · refine ⟨0, ?_⟩
      have hP0 : P (c : ℕ) = 0 := by rw [hv0, hv0z, Complex.ofReal_zero]
      obtain ⟨i, hi, hlz⟩ := Finset.prod_eq_zero_iff.mp hP0
      have hile : i ≤ c := by
        simp only [hLdef, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        exact le_of_lt (by exact_mod_cast hi)
      have hai : ‖lam (σ i)‖ = 0 := by rw [hlz, norm_zero]
      have h1 : a c ≤ a i := hanti i c hile
      simp only [hadef] at h1
      rw [hai] at h1
      have hac : ‖lam (σ c)‖ = 0 := le_antisymm h1 (norm_nonneg _)
      simpa using norm_eq_zero.mp hac
    · refine ⟨v1 / v0, ?_⟩
      have hv0C : ((v0 : ℝ) : ℂ) ≠ 0 := by simpa using hv0z
      have heq : ((v1 : ℝ) : ℂ) = ((v0 : ℝ) : ℂ) * lam (σ c) := by rw [← hv1, ← hv0, hstep]
      rw [Complex.ofReal_div, eq_div_iff hv0C]
      linear_combination -heq
  -- transport back along the sorting permutation
  have hall : ∀ i : Fin n, ∃ v : ℝ, lam i = (v : ℂ) := by
    intro i
    obtain ⟨v, hv⟩ := hlamsorted (σ.symm i)
    exact ⟨v, by simpa using hv⟩
  choose ν hν using hall
  refine ⟨ν, ?_⟩
  refine Polynomial.map_injective (algebraMap ℝ ℂ) (algebraMap ℝ ℂ).injective ?_
  rw [← Matrix.charpoly_map, hsplitC, Polynomial.map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hν i]
  rfl

end Shields
