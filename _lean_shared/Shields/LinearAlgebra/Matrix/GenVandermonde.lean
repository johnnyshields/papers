/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Algebra.Polynomial.CoeffList
import Mathlib.Algebra.Polynomial.RuleOfSigns
import Mathlib.Data.List.Destutter
import Mathlib.LinearAlgebra.Vandermonde
import Shields.LinearAlgebra.Matrix.PerronFrobenius

/-!
# Generalized Vandermonde determinants are positive

For increasing positive nodes and increasing exponents, `det [x_i ^ k_j] > 0`.

## Main results

* `Shields.det_genVandermonde_ne_zero`: nonsingularity, i.e. the Chebyshev-system property of
  `{x ^ k_1, …, x ^ k_m}` on `(0, ∞)`.
* `Shields.det_genVandermonde_pos`: positivity.
* `Shields.signVariations_lt_card_support`: a nonzero polynomial has fewer sign variations than it
  has nonzero coefficients. Stated separately because it is generally useful and Mathlib lacks it.
* `Shields.minorsPos_genVandermonde`: every minor is positive, so this is a concrete inhabitant of
  the strict total-positivity predicate.

## Implementation notes

Mathlib has `Matrix.det_vandermonde` for *consecutive* exponents only, and no Schur polynomials and
no Jacobi--Trudi; none of the three is in flight. It does have **Descartes' rule of signs**
(`Polynomial.roots_countP_pos_le_signVariations`), and that is enough for nonsingularity: a
nontrivial combination `∑ c_j x ^ k_j` has at most `m` nonzero coefficients, hence at most `m - 1`
sign variations, hence at most `m - 1` positive roots, so it cannot vanish at `m` distinct positive
nodes.

**The sign then comes for free.** The cone of increasing positive nodes is convex, so a continuous
nonvanishing determinant has constant sign there, and one evaluation pins it: at `x_i = 2 ^ i` the
matrix is an ordinary Vandermonde, transposed, with nodes `2 ^ k_j`. No asymptotics and no Schur
positivity.

## Tags

Vandermonde, determinant, Descartes' rule of signs, Chebyshev system, total positivity
-/

open scoped BigOperators
open Polynomial
open scoped Matrix

namespace Shields

theorem signVariations_lt_card_support {P : Polynomial ℝ} (hP : P ≠ 0) :
    signVariations P < P.support.card := by
  set n := P.natDegree + 1 with hn
  have hcl : P.coeffList = (List.range n).reverse.map P.coeff := by
    rw [Polynomial.coeffList]; congr 2
    rw [Polynomial.degree_eq_natDegree hP]; rfl
  have hsupp : P.support = (Finset.range n).filter (fun i => P.coeff i ≠ 0) := by
    ext i
    simp only [Polynomial.mem_support_iff, Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h => ⟨Nat.lt_succ_of_le (Polynomial.le_natDegree_of_ne_zero h), h⟩, fun h => h.2⟩
  have hcard : P.support.card
      = ((List.range n).filter (fun i => decide (P.coeff i ≠ 0))).length := by
    rw [hsupp]; rfl
  have hnz : (((P.coeffList).map SignType.sign).filter (· ≠ 0)).length = P.support.card := by
    rw [hcard, ← List.countP_eq_length_filter, ← List.countP_eq_length_filter,
      List.countP_map, hcl, List.countP_map,
      List.Perm.countP_eq _ (List.range n).reverse_perm]
    apply List.countP_congr
    intro i _
    simp
  have hdest := (List.destutter_sublist (· ≠ ·)
      (((P.coeffList).map SignType.sign).filter (· ≠ 0))).length_le
  have hpos : 0 < P.support.card := Finset.card_pos.mpr (Polynomial.support_nonempty.mpr hP)
  simp only [signVariations]
  omega

variable {m : ℕ}

/-- The polynomial `∑_j c_j X^{k_j}` carrying a combination of the generalized Vandermonde
columns.  Its support has at most `m` elements, so Descartes' rule bounds its positive
roots by `m - 1` and it cannot vanish at `m` distinct positive nodes. -/
noncomputable def expPoly (c : Fin m → ℝ) (k : Fin m → ℕ) : Polynomial ℝ :=
  ∑ j, Polynomial.C (c j) * Polynomial.X ^ (k j)

theorem expPoly_coeff (c : Fin m → ℝ) {k : Fin m → ℕ} (hk : Function.Injective k) (j : Fin m) :
    (expPoly c k).coeff (k j) = c j := by
  rw [expPoly, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (hk.ne hb).symm, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem expPoly_support (c : Fin m → ℝ) (k : Fin m → ℕ) :
    (expPoly c k).support ⊆ Finset.image k Finset.univ := by
  intro N hN
  by_contra hc
  rw [Polynomial.mem_support_iff] at hN
  refine hN ?_
  rw [expPoly, Polynomial.finsetSum_coeff]
  refine Finset.sum_eq_zero fun j _ => ?_
  have : k j ≠ N := fun h => hc (h ▸ Finset.mem_image_of_mem k (Finset.mem_univ j))
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (Ne.symm this), mul_zero]

theorem expPoly_eval (c : Fin m → ℝ) (k : Fin m → ℕ) (y : ℝ) :
    (expPoly c k).eval y = ∑ j, c j * y ^ (k j) := by
  simp [expPoly, Polynomial.eval_finsetSum]

/-- The generalized Vandermonde matrix `[x_i ^ k_j]`. -/
noncomputable def genVandermonde (x : Fin m → ℝ) (k : Fin m → ℕ) :
    Matrix (Fin m) (Fin m) ℝ := Matrix.of fun i j => x i ^ k j

/-- Descartes' rule of signs by term count: a nonzero real polynomial with at most `m` terms has
fewer than `m` positive roots, counted with multiplicity. -/
private theorem countP_roots_pos_lt {P : Polynomial ℝ} (hP : P ≠ 0)
    (hsupp : P.support.card ≤ m) : P.roots.countP (0 < ·) < m := by
  have hsv : signVariations P < m := lt_of_lt_of_le (signVariations_lt_card_support hP) hsupp
  have hdesc := Polynomial.roots_countP_pos_le_signVariations (P := P)
  omega

/-- A nonzero real polynomial vanishing at `m` distinct positive points has at least `m` positive
roots, counted with multiplicity. -/
private theorem le_countP_roots_pos {P : Polynomial ℝ} (hP : P ≠ 0) {x : Fin m → ℝ}
    (hx : StrictMono x) (hxpos : ∀ i, 0 < x i) (hroot : ∀ i, P.eval (x i) = 0) :
    m ≤ P.roots.countP (0 < ·) := by
  have hsub : (Finset.image x Finset.univ).val ≤ P.roots.filter (0 < ·) := by
    rw [Multiset.le_iff_subset (Finset.image x Finset.univ).nodup]
    intro a ha
    rw [Finset.mem_val] at ha
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ha
    rw [Multiset.mem_filter]
    exact ⟨Polynomial.mem_roots'.mpr ⟨hP, hroot i⟩, by simpa using hxpos i⟩
  rw [Multiset.countP_eq_card_filter]
  calc m = (Finset.image x Finset.univ).card := by
        rw [Finset.card_image_of_injective _ hx.injective, Finset.card_univ, Fintype.card_fin]
    _ ≤ _ := Multiset.card_le_card hsub

theorem det_genVandermonde_ne_zero {x : Fin m → ℝ} {k : Fin m → ℕ}
    (hx : StrictMono x) (hxpos : ∀ i, 0 < x i) (hk : StrictMono k) :
    (genVandermonde x k).det ≠ 0 := by
  intro hdet
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  obtain ⟨j0, hj0⟩ : ∃ j, c j ≠ 0 := by
    by_contra h
    push Not at h
    exact hc0 (funext h)
  set P := expPoly c k with hPdef
  have hPne : P ≠ 0 := by
    intro h0
    have hco := expPoly_coeff c hk.injective j0
    rw [← hPdef, h0, Polynomial.coeff_zero] at hco
    exact hj0 hco.symm
  have hroot : ∀ i, P.eval (x i) = 0 := by
    intro i
    rw [hPdef, expPoly_eval]
    have h := congrFun hc i
    simp only [Matrix.mulVec, dotProduct, genVandermonde, Matrix.of_apply, Pi.zero_apply] at h
    rw [← h]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  -- at most `m` terms, so fewer than `m` positive roots -- but `m` distinct positive roots
  have hsupp : P.support.card ≤ m := by
    calc P.support.card ≤ (Finset.image k Finset.univ).card :=
          Finset.card_le_card (by rw [hPdef]; exact expPoly_support c k)
      _ ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_image_le
      _ = m := by simp
  exact absurd (le_countP_roots_pos hPne hx hxpos hroot)
    (not_le.mpr (countP_roots_pos_lt hPne hsupp))

/-- The open cone of strictly increasing positive node vectors. -/
def incCone (m : ℕ) : Set (Fin m → ℝ) := {x | (∀ i, 0 < x i) ∧ StrictMono x}

theorem convex_incCone : Convex ℝ (incCone m) := by
  rintro u ⟨hu0, hu⟩ v ⟨hv0, hv⟩ a b ha hb hab
  -- One weight may vanish, and then the other is `1`; either way the combination is strict.
  have hlt : ∀ p q r t : ℝ, p < q → r < t → a * p + b * r < a * q + b * t := by
    intro p q r t hpq hrt
    rcases lt_or_eq_of_le ha with ha' | ha'
    · nlinarith
    · have hb' : b = 1 := by linarith [ha'.symm]
      nlinarith
  refine ⟨fun i => by simpa using hlt 0 (u i) 0 (v i) (hu0 i) (hv0 i), fun i j hij => ?_⟩
  simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using
    hlt (u i) (u j) (v i) (v j) (hu hij) (hv hij)

theorem continuous_det_genVandermonde (k : Fin m → ℕ) :
    Continuous fun x : Fin m → ℝ => (genVandermonde x k).det := by
  refine Continuous.matrix_det ?_
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact ((continuous_apply i).pow (k j))

/-- **No sign change along a segment of the cone.**  The determinant is continuous and nowhere
zero on the cone, and the cone is convex, so the intermediate value theorem forbids one endpoint
of a segment from being negative while the other is positive. -/
private theorem not_neg_and_pos_of_mem_incCone {k : Fin m → ℕ} (hk : StrictMono k)
    {u v : Fin m → ℝ} (hu : u ∈ incCone m) (hv : v ∈ incCone m)
    (hun : (genVandermonde u k).det < 0) (hvp : 0 < (genVandermonde v k).det) : False := by
  have hcont : ContinuousOn (fun t : ℝ => (genVandermonde ((1 - t) • u + t • v) k).det)
      (Set.Icc 0 1) :=
    (((continuous_det_genVandermonde k).comp
      (((continuous_const.sub continuous_id).smul continuous_const).add
        (continuous_id.smul continuous_const)))).continuousOn
  have hmem : ∀ t ∈ Set.Icc (0 : ℝ) 1, ((1 - t) • u + t • v) ∈ incCone m := fun t ht =>
    convex_incCone hu hv (by linarith [ht.2]) ht.1 (by ring)
  have hzero : (0 : ℝ) ∈ Set.Icc
      ((genVandermonde ((1 - (0 : ℝ)) • u + (0 : ℝ) • v) k).det)
      ((genVandermonde ((1 - (1 : ℝ)) • u + (1 : ℝ) • v) k).det) := by
    simp only [sub_zero, one_smul, zero_smul, add_zero, sub_self, zero_add]
    exact Set.mem_Icc.mpr ⟨hun.le, hvp.le⟩
  obtain ⟨t, ht, hgt⟩ :=
    intermediate_value_Icc (le_of_lt (zero_lt_one : (0 : ℝ) < 1)) hcont hzero
  exact det_genVandermonde_ne_zero (hmem t ht).2 (hmem t ht).1 hk hgt

/-- **The generalized Vandermonde determinant has constant sign on the cone.**
The cone is convex, hence any two node vectors are joined by a segment inside it;
the determinant is continuous and never zero there, so the intermediate value
theorem forbids a sign change. -/
theorem det_genVandermonde_pos_iff {k : Fin m → ℕ} (hk : StrictMono k)
    {x y : Fin m → ℝ} (hx : x ∈ incCone m) (hy : y ∈ incCone m) :
    0 < (genVandermonde x k).det ↔ 0 < (genVandermonde y k).det := by
  have hne : ∀ z ∈ incCone m, (genVandermonde z k).det ≠ 0 :=
    fun z hz => det_genVandermonde_ne_zero hz.2 hz.1 hk
  have key := fun u v hu hv hun hvp => not_neg_and_pos_of_mem_incCone hk (u := u) (v := v)
    hu hv hun hvp
  constructor
  · intro hxp
    rcases lt_trichotomy ((genVandermonde y k).det) 0 with h | h | h
    · exact (key y x hy hx h hxp).elim
    · exact absurd h (hne y hy)
    · exact h
  · intro hyp
    rcases lt_trichotomy ((genVandermonde x k).det) 0 with h | h | h
    · exact (key x y hx hy h hyp).elim
    · exact absurd h (hne x hx)
    · exact h

/-- **Generalized Vandermonde determinants are positive.**  For `0 < x_1 < ⋯ < x_m`
and `k_1 < ⋯ < k_m`, `det[x_i^{k_j}] > 0`.

The sign is constant on the cone, so it is enough to evaluate at one point — and
at `x_i = 2^i` the matrix *is* an ordinary Vandermonde, transposed, with nodes
`2^{k_j}`.  No asymptotics are needed. -/
theorem det_genVandermonde_pos {k : Fin m → ℕ} (hk : StrictMono k)
    {x : Fin m → ℝ} (hx : x ∈ incCone m) : 0 < (genVandermonde x k).det := by
  set p : Fin m → ℝ := fun i => (2 : ℝ) ^ (i : ℕ) with hp
  have hppos : ∀ i, 0 < p i := fun i => by positivity
  have hpmono : StrictMono p := by
    intro i j hij
    exact pow_lt_pow_right₀ (by norm_num) (by exact_mod_cast hij)
  have hpin : p ∈ incCone m := ⟨hppos, hpmono⟩
  refine (det_genVandermonde_pos_iff hk hx hpin).mpr ?_
  -- at these nodes the matrix is a transposed Vandermonde with nodes `2 ^ k j`
  set v : Fin m → ℝ := fun j => (2 : ℝ) ^ (k j) with hv
  have heq : genVandermonde p k = (Matrix.vandermonde v)ᵀ := by
    ext i j
    change ((2 : ℝ) ^ (i : ℕ)) ^ (k j) = ((2 : ℝ) ^ (k j)) ^ (i : ℕ)
    rw [← pow_mul, ← pow_mul, mul_comm]
  have hvmono : StrictMono v := by
    intro i j hij
    exact pow_lt_pow_right₀ (by norm_num) (hk hij)
  rw [heq, Matrix.det_transpose, Matrix.det_vandermonde]
  refine Finset.prod_pos fun i _ => Finset.prod_pos fun j hj => ?_
  exact sub_pos.mpr (hvmono (Finset.mem_Ioi.mp hj))

/-! ### A concrete totally positive family

Every minor of a generalized Vandermonde matrix is *itself* a generalized
Vandermonde determinant — restricting to increasing rows and columns just
restricts the nodes and the exponents, and both stay strictly monotone.  So
positivity of the determinant upgrades at once to **total positivity**.

This is the first strictly totally positive family in the development, and it is
what makes `PerronFrobenius.MinorsPos` and `exists_perron_compound` non-vacuous:
their hypotheses are satisfiable, so the results about them are not statements
about an empty class. -/

/-- A minor of a generalized Vandermonde matrix, on increasing rows and columns,
is the generalized Vandermonde matrix of the restricted nodes and exponents. -/
theorem submatrix_genVandermonde {r : ℕ} (x : Fin m → ℝ) (k : Fin m → ℕ)
    (f g : Fin r → Fin m) :
    (genVandermonde x k).submatrix f g = genVandermonde (x ∘ f) (k ∘ g) := rfl

/-- **The generalized Vandermonde matrix is totally positive.** -/
theorem minorsPos_genVandermonde {x : Fin m → ℝ} {k : Fin m → ℕ}
    (hx : StrictMono x) (hxpos : ∀ i, 0 < x i) (hk : StrictMono k) (r : ℕ) :
    MinorsPos r (genVandermonde x k) := by
  intro f g hf hg
  rw [mem_increasingSelections] at hf hg
  rw [submatrix_genVandermonde]
  exact det_genVandermonde_pos (hk.comp hg) ⟨fun i => hxpos (f i), hx.comp hf⟩

/-- Totally positive implies totally nonnegative, so the spectral results about
`MinorsNonneg` apply to this family as well. -/
theorem minorsNonneg_genVandermonde {x : Fin m → ℝ} {k : Fin m → ℕ}
    (hx : StrictMono x) (hxpos : ∀ i, 0 < x i) (hk : StrictMono k) (r : ℕ) :
    MinorsNonneg r (genVandermonde x k) :=
  fun f g hf hg => (minorsPos_genVandermonde hx hxpos hk r f g hf hg).le

/-- **The totally positive machinery is non-vacuous.**  On a generalized
Vandermonde matrix: every compound has a strictly positive Perron root, and every
real eigenvalue of the matrix itself is nonnegative.

This matters for the same reason `sincInputsWitness` does.  `MinorsPos`,
`exists_perron_compound` and `charpoly_roots_nonneg` are statements *about* a
class, and without an inhabitant they would be statements about an empty one. -/
theorem genVandermonde_perron_nonvacuous {r : ℕ} (hrm : r ≤ m) {x : Fin m → ℝ}
    {k : Fin m → ℕ} (hx : StrictMono x) (hxpos : ∀ i, 0 < x i) (hk : StrictMono k) :
    0 < perronRoot (compound r (genVandermonde x k)) ∧
      ∀ lam ∈ (genVandermonde x k).charpoly.roots, 0 ≤ lam := by
  refine ⟨(exists_perron_compound hrm _ (minorsPos_genVandermonde hx hxpos hk r)).1,
    fun lam hlam => ?_⟩
  exact charpoly_roots_nonneg (fun j => minorsNonneg_genVandermonde hx hxpos hk j) hlam


/-! ### Axiom footprint -/

/-- info: 'Shields.signVariations_lt_card_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms signVariations_lt_card_support

/-- info: 'Shields.minorsPos_genVandermonde' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms minorsPos_genVandermonde

end Shields
