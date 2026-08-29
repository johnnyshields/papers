/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Shields.Analysis.Complex.TriangleEquality
import Shields.LinearAlgebra.Matrix.TotallyNonneg.Compound

/-!
# The Perron root of an entrywise positive matrix

Existence, dominance, uniqueness and strict dominance of the Perron root, by the Collatz--Wielandt
variational characterization.

## Main results

* `Shields.perronRoot`, `Shields.exists_perron_eigenvector`: the Perron root and a strictly positive
  eigenvector for it.
* `Shields.norm_le_perronRoot`: it is the spectral radius -- every complex eigenvalue satisfies
  `‖λ‖ ≤ r`.
* `Shields.perron_eigenvector_unique`: its real eigenspace is the line through that eigenvector.
* `Shields.eq_perronRoot_of_norm_eq`: **strict dominance** -- it is the only eigenvalue of modulus
  `r`.

## Implementation notes

**Collatz--Wielandt, not Brouwer.** The usual proof applies a fixed point theorem on the simplex,
and the pinned Mathlib revision has neither Brouwer nor Schauder (`SchauderBasis` is a homonym, not
the fixed point theorem). None is needed. Take

`r = sup { s ≥ 0 : ∃ x in the simplex with s • x ≤ A *ᵥ x coordinatewise }`,

bounded above by the total entry sum. The witnessing pairs `(s, x)` form a closed subset of a
product of compacts, so the set of such `s` is a continuous image of a compact and contains its own
supremum -- attainment with no fixed point theorem and no subsequence extraction. At the maximizer
`A *ᵥ x - r • x` is nonnegative; were it nonzero, applying `A` once more would make it strictly
positive and produce a strictly larger admissible `s`.

**Algebraic simplicity -- multiplicity one in the characteristic polynomial -- is not proved.**

Mathlib has the irreducibility and primitivity *definitions* (`Matrix.IsIrreducible`,
`Matrix.IsPrimitive`) but no Perron--Frobenius theorem. The theorems are in flight as a PR chain --
#39919 (Collatz--Wielandt function and Perron root bounds, the same route taken here), #39920
(primitive matrices), #39921 (uniqueness of the Perron eigenvector), #39922 (irreducible matrices),
#39925 (simplicity of the Perron root) -- every link of which is labeled `blocked-by-other-PR`.
Every matrix this is applied to is entrywise positive, hence primitive, so that chain would subsume
this module.

## Tags

Perron-Frobenius, Perron root, spectral radius, positive matrix, Collatz-Wielandt
-/

open scoped BigOperators
open Matrix

namespace Shields

variable {ι : Type*} [Fintype ι]

/-! ### The Collatz–Wielandt set -/

/-- The total entry sum, an upper bound for every Collatz–Wielandt scalar. -/
noncomputable def entrySum (A : Matrix ι ι ℝ) : ℝ := ∑ i, ∑ j, A i j

/-- Witness pairs for the Collatz–Wielandt supremum: a scalar `s ∈ [0, M]` and a
simplex vector `x` with `s·x ≤ Ax` coordinatewise. -/
def cwPairs (A : Matrix ι ι ℝ) (M : ℝ) : Set (ℝ × (ι → ℝ)) :=
  {p | p.1 ∈ Set.Icc (0 : ℝ) M ∧ p.2 ∈ stdSimplex ℝ ι ∧
    ∀ i, p.1 * p.2 i ≤ (A *ᵥ p.2) i}

/-- The Collatz–Wielandt scalars themselves. -/
def cwSet (A : Matrix ι ι ℝ) (M : ℝ) : Set ℝ := Prod.fst '' cwPairs A M

/-- **The Perron root**: the Collatz–Wielandt supremum.  For a positive matrix it
is an eigenvalue with a positive eigenvector, and it is the spectral radius. -/
noncomputable def perronRoot (A : Matrix ι ι ℝ) : ℝ := sSup (cwSet A (entrySum A))

theorem continuous_mulVec_apply (A : Matrix ι ι ℝ) (i : ι) :
    Continuous fun p : ℝ × (ι → ℝ) => (A *ᵥ p.2) i := by
  simp only [Matrix.mulVec, dotProduct]
  exact continuous_finsetSum _ fun j _ =>
    continuous_const.mul ((continuous_apply j).comp continuous_snd)

theorem isClosed_cwPairs (A : Matrix ι ι ℝ) (M : ℝ) :
    IsClosed (cwPairs A M) := by
  have heq : cwPairs A M =
      {p : ℝ × (ι → ℝ) | p.1 ∈ Set.Icc (0 : ℝ) M} ∩
        ({p : ℝ × (ι → ℝ) | p.2 ∈ stdSimplex ℝ ι} ∩
          ⋂ i, {p : ℝ × (ι → ℝ) | p.1 * p.2 i ≤ (A *ᵥ p.2) i}) := by
    ext p
    simp only [cwPairs, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [heq]
  exact (isClosed_Icc.preimage continuous_fst).inter
    (((isClosed_stdSimplex ℝ ι).preimage continuous_snd).inter
      (isClosed_iInter fun i => isClosed_le
        (continuous_fst.mul ((continuous_apply i).comp continuous_snd))
        (continuous_mulVec_apply A i)))

theorem isCompact_cwPairs (A : Matrix ι ι ℝ) (M : ℝ) :
    IsCompact (cwPairs A M) :=
  IsCompact.of_isClosed_subset
    (isCompact_Icc.prod (isCompact_stdSimplex (𝕜 := ℝ) (ι := ι)))
    (isClosed_cwPairs A M) (fun _ hp => ⟨hp.1, hp.2.1⟩)

theorem isCompact_cwSet (A : Matrix ι ι ℝ) (M : ℝ) :
    IsCompact (cwSet A M) := (isCompact_cwPairs A M).image continuous_fst

/-! ### The bound and the base point -/

/-- On the simplex every coordinate is at most `1`.  Mathlib's
`mem_Icc_of_mem_stdSimplex` gives both bounds; this names the upper one. -/
theorem stdSimplex_le_one {x : ι → ℝ} (hx : x ∈ stdSimplex ℝ ι) (j : ι) :
    x j ≤ 1 := (mem_Icc_of_mem_stdSimplex hx j).2

/-- A Collatz–Wielandt scalar is at most the total entry sum: summing `s·x ≤ Ax`
over the coordinates gives `s ≤ ∑_j (∑_i A i j) x_j ≤ ∑_{i,j} A i j`. -/
theorem cw_le_entrySum {A : Matrix ι ι ℝ} (hA : ∀ i j, 0 ≤ A i j)
    {s : ℝ} {x : ι → ℝ} (hx : x ∈ stdSimplex ℝ ι)
    (h : ∀ i, s * x i ≤ (A *ᵥ x) i) : s ≤ entrySum A := by
  obtain ⟨hnn, hsum⟩ := hx
  have hstep : s = ∑ i, s * x i := by rw [← Finset.mul_sum, hsum, mul_one]
  have hle : ∑ i, s * x i ≤ ∑ i, (A *ᵥ x) i := Finset.sum_le_sum fun i _ => h i
  refine hstep.le.trans (hle.trans ?_)
  have hswap : ∑ i, (A *ᵥ x) i = ∑ j, (∑ i, A i j) * x j := by
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => by rw [Finset.sum_mul]
  have hES : entrySum A = ∑ j, ∑ i, A i j := by
    simp only [entrySum]; exact Finset.sum_comm
  rw [hswap, hES]
  refine Finset.sum_le_sum fun j _ => ?_
  have hcol : 0 ≤ ∑ i, A i j := Finset.sum_nonneg fun i _ => hA i j
  calc (∑ i, A i j) * x j ≤ (∑ i, A i j) * 1 :=
        mul_le_mul_of_nonneg_left (stdSimplex_le_one ⟨hnn, hsum⟩ j) hcol
    _ = ∑ i, A i j := mul_one _

/-- The uniform vector is in the simplex. -/
theorem uniform_mem_stdSimplex [Nonempty ι] :
    (fun _ : ι => (Fintype.card ι : ℝ)⁻¹) ∈ stdSimplex ℝ ι := by
  have hnR : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  exact ⟨fun _ => by positivity, by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ hnR.ne']⟩

omit [Fintype ι] in
/-- A nonnegative vector that is not identically zero is positive somewhere. -/
theorem exists_pos_of_nonneg_ne_zero {v : ι → ℝ} (hv : ∀ i, 0 ≤ v i) (hne : v ≠ 0) :
    ∃ j, 0 < v j := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
  exact ⟨j, (hv j).lt_of_ne' hj⟩

/-- **A positive matrix sends a nonzero nonnegative vector to a strictly positive one.**
The positive coordinate of `v` meets a positive entry of `A` in every row. -/
theorem mulVec_pos_of_nonneg_ne_zero {A : Matrix ι ι ℝ} (hA : ∀ i j, 0 < A i j)
    {v : ι → ℝ} (hv : ∀ i, 0 ≤ v i) (hne : v ≠ 0) (i : ι) : 0 < (A *ᵥ v) i := by
  obtain ⟨j, hj⟩ := exists_pos_of_nonneg_ne_zero hv hne
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_pos' (fun k _ => mul_nonneg (hA i k).le (hv k))
    ⟨j, Finset.mem_univ j, mul_pos (hA i j) hj⟩

/-- A simplex vector is not zero: its coordinates sum to `1`. -/
theorem ne_zero_of_mem_stdSimplex {x : ι → ℝ} (hx : x ∈ stdSimplex ℝ ι) : x ≠ 0 := by
  intro h
  simpa [h] using hx.2

/-- `Ax` is strictly positive when `A` is and `x` is a simplex vector. -/
theorem mulVec_pos_of_stdSimplex {A : Matrix ι ι ℝ}
    (hA : ∀ i j, 0 < A i j) {x : ι → ℝ} (hx : x ∈ stdSimplex ℝ ι) (i : ι) :
    0 < (A *ᵥ x) i :=
  mulVec_pos_of_nonneg_ne_zero hA hx.1 (ne_zero_of_mem_stdSimplex hx) i

omit [Fintype ι] in
/-- On a nonempty finite index type a strictly positive family dominates a positive multiple of
any other: the least of the ratios `f i / g i` is a scalar that works at every index. -/
theorem exists_pos_forall_mul_le [Finite ι] [Nonempty ι] {f g : ι → ℝ}
    (hf : ∀ i, 0 < f i) (hg : ∀ i, 0 < g i) :
    ∃ c > 0, ∀ i, c * g i ≤ f i := by
  have := Fintype.ofFinite ι
  have hUne : (Finset.univ : Finset ι).Nonempty := Finset.univ_nonempty
  refine ⟨Finset.inf' Finset.univ hUne (fun i => f i / g i), ?_, ?_⟩
  · exact (Finset.lt_inf'_iff _).2 fun i _ => div_pos (hf i) (hg i)
  · intro i
    have hle : Finset.inf' Finset.univ hUne (fun k => f k / g k) ≤ f i / g i :=
      Finset.inf'_le _ (Finset.mem_univ i)
    calc _ ≤ (f i / g i) * g i := mul_le_mul_of_nonneg_right hle (hg i).le
      _ = f i := div_mul_cancel₀ _ (hg i).ne'

/-- **Renormalizing onto the simplex.**  A nonzero nonnegative vector has a positive multiple
on the standard simplex, and the scaling carries a Collatz--Wielandt inequality `s·y ≤ Ay`
along with it -- both sides are homogeneous of degree one in `y`. -/
theorem exists_smul_mem_stdSimplex {A : Matrix ι ι ℝ} {s : ℝ} {y : ι → ℝ}
    (hy : ∀ i, 0 ≤ y i) (hyne : y ≠ 0) (hle : ∀ i, s * y i ≤ (A *ᵥ y) i) :
    ∃ x ∈ stdSimplex ℝ ι, ∀ i, s * x i ≤ (A *ᵥ x) i := by
  obtain ⟨j, hj⟩ := exists_pos_of_nonneg_ne_zero hy hyne
  have hsum : 0 < ∑ i, y i := Finset.sum_pos' (fun i _ => hy i) ⟨j, Finset.mem_univ j, hj⟩
  have hcpos : 0 < (∑ i, y i)⁻¹ := inv_pos.mpr hsum
  refine ⟨(∑ i, y i)⁻¹ • y, ⟨fun i => ?_, ?_⟩, fun i => ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg hcpos.le (hy i)
  · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    exact inv_mul_cancel₀ hsum.ne'
  · rw [Matrix.mulVec_smul]
    simp only [Pi.smul_apply, smul_eq_mul]
    calc s * ((∑ k, y k)⁻¹ * y i) = (∑ k, y k)⁻¹ * (s * y i) := by ring
      _ ≤ (∑ k, y k)⁻¹ * (A *ᵥ y) i := mul_le_mul_of_nonneg_left (hle i) hcpos.le

/-- **A greatest Collatz–Wielandt scalar is an eigenvalue.**  If `s·w ≤ Aw` for a nonnegative
nonzero `w` and no Collatz–Wielandt scalar of `A` exceeds `s`, then `Aw = s·w`.

Were `Aw − s·w` nonzero it would be nonnegative and nonzero, so applying the positive `A` once
more makes it strictly positive; `Aw` renormalized onto the simplex then admits the strictly
larger scalar `s + ε`, where `ε` is the least of the ratios that positivity supplies. -/
theorem mulVec_eq_smul_of_nonneg_of_forall_cwSet_le [Nonempty ι] {A : Matrix ι ι ℝ}
    (hA : ∀ i j, 0 < A i j) {s : ℝ} {w : ι → ℝ} (hs0 : 0 ≤ s)
    (hw : ∀ i, 0 ≤ w i) (hwne : w ≠ 0) (hwle : ∀ i, s * w i ≤ (A *ᵥ w) i)
    (hsup : ∀ t ∈ cwSet A (entrySum A), t ≤ s) :
    A *ᵥ w = s • w := by
  have hAnn : ∀ i j, 0 ≤ A i j := fun i j => (hA i j).le
  have hwpos : ∀ i, 0 < (A *ᵥ w) i := mulVec_pos_of_nonneg_ne_zero hA hw hwne
  by_contra hne'
  set v : ι → ℝ := A *ᵥ w - s • w with hv
  have hvnn : ∀ i, 0 ≤ v i := fun i => sub_nonneg.mpr (hwle i)
  have hvne : v ≠ 0 := fun hc => hne' (sub_eq_zero.mp (hv ▸ hc))
  have hAv : ∀ i, 0 < (A *ᵥ v) i := mulVec_pos_of_nonneg_ne_zero hA hvnn hvne
  set y : ι → ℝ := A *ᵥ w with hydef
  have hy : A *ᵥ y - s • y = A *ᵥ v := by
    rw [hv, Matrix.mulVec_sub, Matrix.mulVec_smul]
  obtain ⟨eps, hepspos, heps⟩ := exists_pos_forall_mul_le hAv hwpos
  -- `y` admits the strictly larger scalar `s + eps`, so does its simplex representative
  have hbase : ∀ i, (s + eps) * y i ≤ (A *ᵥ y) i := by
    intro i
    have hyi : (A *ᵥ y) i - s * y i = (A *ᵥ v) i := by
      have h := congrFun hy i
      simpa [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using h
    have hexp : (s + eps) * y i = s * y i + eps * y i := by ring
    rw [hexp]; linarith [heps i]
  obtain ⟨y', hy'mem, hgain⟩ := exists_smul_mem_stdSimplex (fun i => (hwpos i).le)
    (fun hc => (hwpos (Classical.arbitrary ι)).ne' (congrFun hc _)) hbase
  have hmem : (s + eps) ∈ cwSet A (entrySum A) :=
    ⟨(s + eps, y'), ⟨⟨by linarith, cw_le_entrySum hAnn hy'mem hgain⟩,
      hy'mem, hgain⟩, rfl⟩
  linarith [hsup _ hmem]

/-- **A greatest Collatz–Wielandt scalar is an eigenvalue.**  If `s·x ≤ Ax` on the simplex and no
Collatz–Wielandt scalar of `A` exceeds `s`, then `Ax = s·x`. -/
theorem mulVec_eq_smul_of_forall_cwSet_le [Nonempty ι] {A : Matrix ι ι ℝ}
    (hA : ∀ i j, 0 < A i j) {s : ℝ} {x : ι → ℝ} (hs0 : 0 ≤ s)
    (hx : x ∈ stdSimplex ℝ ι) (hxle : ∀ i, s * x i ≤ (A *ᵥ x) i)
    (hsup : ∀ t ∈ cwSet A (entrySum A), t ≤ s) :
    A *ᵥ x = s • x :=
  mulVec_eq_smul_of_nonneg_of_forall_cwSet_le hA hs0 hx.1 (ne_zero_of_mem_stdSimplex hx) hxle hsup


/-! ### The Perron root -/

/-- **Perron–Frobenius, existence.**  A matrix with all entries strictly positive
has a strictly positive eigenvalue with a strictly positive eigenvector on the
standard simplex.

Proved by Collatz–Wielandt and compactness: the witness pairs form a closed
subset of `[0,M] × Δ`, so the scalars attain their supremum, and at the maximizer
`Ax − rx` cannot be nonzero without producing a strictly larger admissible
scalar.  No fixed point theorem is used. -/
theorem exists_perron_eigenvector [Nonempty ι] (A : Matrix ι ι ℝ)
    (hA : ∀ i j, 0 < A i j) :
    0 < perronRoot A ∧ ∃ x : ι → ℝ, (∀ i, 0 < x i) ∧
      x ∈ stdSimplex ℝ ι ∧ A *ᵥ x = perronRoot A • x := by
  set M := entrySum A with hM
  have hAnn : ∀ i j, 0 ≤ A i j := fun i j => (hA i j).le
  -- The set of Collatz-Wielandt scalars is compact and nonempty.
  have hne : (cwSet A M).Nonempty := by
    refine ⟨0, ⟨(0, fun _ : ι => (Fintype.card ι : ℝ)⁻¹), ⟨?_, uniform_mem_stdSimplex, ?_⟩, rfl⟩⟩
    · exact ⟨le_refl 0, Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hAnn i j⟩
    · exact fun i => by
        rw [zero_mul]; exact (mulVec_pos_of_stdSimplex hA uniform_mem_stdSimplex i).le
  obtain ⟨⟨s, x⟩, ⟨hsIcc, hx, hxle⟩, hsup⟩ := (isCompact_cwSet A M).sSup_mem hne
  have hsup' : s = sSup (cwSet A M) := hsup
  -- Read the projections of the witness pair at their defeq components.
  dsimp only at hsIcc hx hxle
  have hxpos : ∀ i, 0 < (A *ᵥ x) i := fun i => mulVec_pos_of_stdSimplex hA hx i
  -- The supremum is an eigenvalue: otherwise a strictly larger scalar qualifies.
  have heig : A *ᵥ x = s • x :=
    mulVec_eq_smul_of_forall_cwSet_le hA hsIcc.1 hx hxle
      (fun t ht => by rw [hsup']; exact le_csSup (isCompact_cwSet A M).bddAbove ht)
  -- Strict positivity of `x`, then of `s`, from `Ax = sx` and `Ax > 0`.
  have hxi : ∀ i, 0 < x i := fun i => (hx.1 i).lt_of_ne' fun h => by
    have hcon := hxpos i
    rw [heig, Pi.smul_apply, smul_eq_mul, h, mul_zero] at hcon
    exact lt_irrefl 0 hcon
  have hspos : 0 < s := by
    have h0 := hxpos (Classical.arbitrary ι)
    rw [heig, Pi.smul_apply, smul_eq_mul] at h0
    nlinarith [hxi (Classical.arbitrary ι)]
  have hpr : perronRoot A = s := by rw [perronRoot, ← hM]; exact hsup'.symm
  exact ⟨by rw [hpr]; exact hspos, x, hxi, hx, by rw [hpr]; exact heig⟩

/-! ### The Perron root is the spectral radius, and its eigenspace is a line

Two further halves of Perron–Frobenius, both elementary once the root exists.
Dominance is Collatz–Wielandt applied to `|z|`: a complex eigenvector's modulus
vector satisfies `|λ|·|z| ≤ A|z|` by the triangle inequality, so `|λ|` is itself
an admissible scalar.  Simplicity subtracts the right multiple of the positive
eigenvector to create a zero coordinate, then observes that a positive matrix
sends a nonzero nonnegative vector to a strictly positive one. -/

/-- Any admissible Collatz–Wielandt inequality bounds the Perron root from below:
if `s·y ≤ Ay` for some nonzero nonnegative `y` and `s ≥ 0`, then `s ≤ perronRoot A`.
The vector is renormalized onto the simplex, where the supremum is taken. -/
theorem le_perronRoot_of_le [Nonempty ι] {A : Matrix ι ι ℝ} (hA : ∀ i j, 0 ≤ A i j)
    {s : ℝ} (hs : 0 ≤ s) {y : ι → ℝ} (hy : ∀ i, 0 ≤ y i) (hyne : y ≠ 0)
    (hle : ∀ i, s * y i ≤ (A *ᵥ y) i) : s ≤ perronRoot A := by
  obtain ⟨x, hmem, hscaled⟩ := exists_smul_mem_stdSimplex hy hyne hle
  exact le_csSup (isCompact_cwSet A (entrySum A)).bddAbove
    ⟨(s, x), ⟨⟨hs, cw_le_entrySum hA hmem hscaled⟩, hmem, hscaled⟩, rfl⟩

/-- The eigenvalue equation of the complexified matrix, read in coordinates. -/
theorem mulVec_map_coord {A : Matrix ι ι ℝ} {lam : ℂ} {z : ι → ℂ}
    (heig : (A.map (fun a : ℝ => (a : ℂ))) *ᵥ z = lam • z) (i : ι) :
    lam * z i = ∑ j, (A i j : ℂ) * z j := by
  have h := congrFun heig i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply,
    smul_eq_mul] at h
  exact h.symm

/-- Against a nonnegative matrix the row sum of moduli is the matrix acting on the
modulus vector. -/
theorem sum_norm_mul_eq_mulVec_norm {A : Matrix ι ι ℝ} (hA : ∀ i j, 0 ≤ A i j)
    (z : ι → ℂ) (i : ι) :
    ∑ j, ‖(A i j : ℂ) * z j‖ = (A *ᵥ fun k => ‖z k‖) i := by
  simp only [Matrix.mulVec, dotProduct, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact Finset.sum_congr rfl fun j _ => by rw [abs_of_nonneg (hA i j)]

omit [Fintype ι] in
/-- The modulus vector of a nonzero complex vector is nonzero. -/
theorem norm_ne_zero_of_ne_zero {z : ι → ℂ} (hz : z ≠ 0) : (fun i => ‖z i‖) ≠ 0 := by
  intro hc
  exact hz (funext fun i => by simpa using congrFun hc i)

/-- **The modulus inequality.**  For a nonnegative matrix and a complex eigenvector
`Az = λz`, the modulus vector `|z|` is an admissible Collatz--Wielandt vector for `‖λ‖`:
the triangle inequality in row `i` reads `‖λ‖·|z_i| ≤ (A|z|)_i`. -/
theorem norm_smul_le_mulVec_norm {A : Matrix ι ι ℝ} (hA : ∀ i j, 0 ≤ A i j)
    {lam : ℂ} {z : ι → ℂ}
    (heig : (A.map (fun a : ℝ => (a : ℂ))) *ᵥ z = lam • z) (i : ι) :
    ‖lam‖ * ‖z i‖ ≤ (A *ᵥ fun k => ‖z k‖) i :=
  calc ‖lam‖ * ‖z i‖ = ‖lam * z i‖ := (norm_mul _ _).symm
    _ = ‖∑ j, (A i j : ℂ) * z j‖ := by rw [mulVec_map_coord heig]
    _ ≤ ∑ j, ‖(A i j : ℂ) * z j‖ := norm_sum_le _ _
    _ = _ := sum_norm_mul_eq_mulVec_norm hA z i

/-- **The Perron root is the spectral radius.**  Every complex eigenvalue of a
positive real matrix has modulus at most `perronRoot A`.  By the triangle
inequality the modulus vector `|z|` satisfies `|λ|·|z| ≤ A|z|`, so `|λ|` is
itself a Collatz–Wielandt scalar. -/
theorem norm_le_perronRoot [Nonempty ι] {A : Matrix ι ι ℝ} (hA : ∀ i j, 0 < A i j)
    {lam : ℂ} {z : ι → ℂ} (hz : z ≠ 0)
    (heig : (A.map (fun a : ℝ => (a : ℂ))) *ᵥ z = lam • z) :
    ‖lam‖ ≤ perronRoot A :=
  le_perronRoot_of_le (fun i j => (hA i j).le) (norm_nonneg _) (fun _ => norm_nonneg _)
    (norm_ne_zero_of_ne_zero hz) (norm_smul_le_mulVec_norm (fun i j => (hA i j).le) heig)

/-- **The Perron eigenspace is one-dimensional.**  Any real eigenvector for the
Perron root is a multiple of the positive one: subtract the largest multiple of
`x` that keeps `y − t·x` nonnegative, so some coordinate vanishes, and a positive
matrix cannot send a nonzero nonnegative vector to one with a zero coordinate. -/
theorem perron_eigenvector_unique [Nonempty ι] {A : Matrix ι ι ℝ}
    (hA : ∀ i j, 0 < A i j) {x y : ι → ℝ} (hxpos : ∀ i, 0 < x i)
    (hy : A *ᵥ y = perronRoot A • y) (hxeig : A *ᵥ x = perronRoot A • x) :
    ∃ t : ℝ, y = t • x := by
  have hUne : (Finset.univ : Finset ι).Nonempty := Finset.univ_nonempty
  set t : ℝ := Finset.inf' Finset.univ hUne (fun i => y i / x i) with ht
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_inf' hUne (fun i => y i / x i)
  refine ⟨t, ?_⟩
  set w : ι → ℝ := y - t • x with hw
  have hwnn : ∀ i, 0 ≤ w i := by
    intro i
    have hle : t ≤ y i / x i := Finset.inf'_le _ (Finset.mem_univ i)
    simp only [hw, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_nonneg]
    calc t * x i ≤ (y i / x i) * x i := mul_le_mul_of_nonneg_right hle (hxpos i).le
      _ = y i := div_mul_cancel₀ _ (hxpos i).ne'
  have hwj : w j = 0 := by
    have htj : t = y j / x j := by rw [ht]; exact hj
    have hxj : x j ≠ 0 := (hxpos j).ne'
    simp only [hw, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, htj]
    field
  have hweig : A *ᵥ w = perronRoot A • w := by
    rw [hw, Matrix.mulVec_sub, Matrix.mulVec_smul, hy, hxeig, smul_sub, smul_comm]
  have hwzero : w = 0 := by
    by_contra hne
    have hpos := mulVec_pos_of_nonneg_ne_zero hA hwnn hne j
    rw [hweig] at hpos
    simp only [Pi.smul_apply, smul_eq_mul, hwj, mul_zero] at hpos
    exact lt_irrefl 0 hpos
  exact sub_eq_zero.mp (by rw [← hw]; exact hwzero)

/-! ### Strict dominance

The `≤` of `norm_le_perronRoot` sharpens to `<` off the Perron root itself.  Two
inputs.  First, at the root an admissible Collatz–Wielandt inequality is forced
to be an equality — the same argument that produced the eigenvector, isolated.
Second, the equality case of the triangle inequality in `ℂ`: if the norm of a
finite sum equals the sum of the norms, every term is a nonnegative real multiple
of the total.  Together they align every coordinate of a modulus-maximal complex
eigenvector with a single phase, and that phase cancels. -/

/-- **At the Perron root the Collatz–Wielandt inequality is an equality.**  If
`r·y ≤ Ay` with `y` nonnegative and nonzero and `r = perronRoot A`, then
`Ay = r·y`: otherwise `A(Ay − ry)` is strictly positive and `Ay` admits a scalar
above the supremum.  The root is the supremum of the Collatz--Wielandt scalars,
so no scalar exceeds it and the maximality lemma applies at `s = r`. -/
theorem mulVec_eq_perronRoot_smul [Nonempty ι] {A : Matrix ι ι ℝ} (hA : ∀ i j, 0 < A i j)
    {y : ι → ℝ} (hy : ∀ i, 0 ≤ y i) (hyne : y ≠ 0)
    (hle : ∀ i, perronRoot A * y i ≤ (A *ᵥ y) i) :
    A *ᵥ y = perronRoot A • y :=
  mulVec_eq_smul_of_nonneg_of_forall_cwSet_le hA (exists_perron_eigenvector A hA).1.le hy hyne hle
    fun _ ht => le_csSup (isCompact_cwSet A (entrySum A)).bddAbove ht

/-- **The modulus vector of a modulus-maximal eigenvector is a positive Perron eigenvector.**
The triangle inequality makes `|z|` admissible at the Perron root, where the Collatz--Wielandt
inequality is forced to be an equality; a positive matrix then makes `|z|` strictly positive. -/
private theorem mulVec_norm_eq_perronRoot_smul [Nonempty ι] {A : Matrix ι ι ℝ}
    (hA : ∀ i j, 0 < A i j) {lam : ℂ} {z : ι → ℂ} (hz : z ≠ 0)
    (heig : (A.map (fun a : ℝ => (a : ℂ))) *ᵥ z = lam • z) (hnorm : ‖lam‖ = perronRoot A) :
    A *ᵥ (fun i => ‖z i‖) = perronRoot A • (fun i => ‖z i‖) ∧ ∀ i, 0 < ‖z i‖ := by
  have hynn : ∀ i, 0 ≤ ‖z i‖ := fun i => norm_nonneg _
  have hyne : (fun i => ‖z i‖) ≠ 0 := norm_ne_zero_of_ne_zero hz
  have hle : ∀ i, perronRoot A * ‖z i‖ ≤ (A *ᵥ fun i => ‖z i‖) i := by
    rw [← hnorm]
    exact norm_smul_le_mulVec_norm (fun i j => (hA i j).le) heig
  have hyeig := mulVec_eq_perronRoot_smul hA hynn hyne hle
  refine ⟨hyeig, fun i => ?_⟩
  have h1 := mulVec_pos_of_nonneg_ne_zero hA hynn hyne i
  rw [hyeig] at h1
  simp only [Pi.smul_apply, smul_eq_mul] at h1
  nlinarith [hynn i, (exists_perron_eigenvector A hA).1]

/-- **The phases align.**  Where equality holds in the triangle inequality for the `i₀`-th row,
every `z j` is its own modulus times one common complex direction, the row sum `S`. -/
private theorem norm_row_sum_smul_eq [Nonempty ι] {A : Matrix ι ι ℝ} (hA : ∀ i j, 0 < A i j)
    {z : ι → ℂ} {i₀ : ι}
    (hEq : ‖∑ k, (A i₀ k : ℂ) * z k‖ = ∑ k, ‖(A i₀ k : ℂ) * z k‖) (j : ι) :
    (‖∑ k, (A i₀ k : ℂ) * z k‖ : ℂ) * z j
      = ((‖z j‖ : ℝ) : ℂ) * ∑ k, (A i₀ k : ℂ) * z k := by
  have h := norm_smul_eq_of_norm_sum_eq hEq (Finset.mem_univ j)
  rw [show ‖(A i₀ j : ℂ) * z j‖ = A i₀ j * ‖z j‖ from by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hA i₀ j)]] at h
  refine mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (hA i₀ j).ne' :
    ((A i₀ j : ℝ) : ℂ) ≠ 0) ?_
  push_cast at h ⊢
  linear_combination h

/-- **Strict dominance.**  For a positive matrix the Perron root is the *only*
eigenvalue of maximal modulus: if `‖λ‖ = perronRoot A` then `λ = perronRoot A`.

The modulus vector `y = |z|` satisfies `r·y ≤ Ay`, hence `Ay = r·y` and `y > 0`.
Equality then holds in every triangle inequality `‖∑_j A_{ij} z_j‖ ≤ ∑_j A_{ij}‖z_j‖`,
so all the `z_j` share one phase `θ`; that makes `z = θ·y` and `λz = Az = r z`. -/
theorem eq_perronRoot_of_norm_eq [Nonempty ι] {A : Matrix ι ι ℝ} (hA : ∀ i j, 0 < A i j)
    {lam : ℂ} {z : ι → ℂ} (hz : z ≠ 0)
    (heig : (A.map (fun a : ℝ => (a : ℂ))) *ᵥ z = lam • z)
    (hnorm : ‖lam‖ = perronRoot A) :
    lam = (perronRoot A : ℂ) := by
  set r := perronRoot A with hr
  set y : ι → ℝ := fun i => ‖z i‖ with hy
  obtain ⟨hyeig, hypos⟩ := mulVec_norm_eq_perronRoot_smul hA hz heig hnorm
  have hrpos : 0 < r := (exists_perron_eigenvector A hA).1
  have hcoord : ∀ i, lam * z i = ∑ j, (A i j : ℂ) * z j := mulVec_map_coord heig
  have hsumnorm : ∀ i, ∑ j, ‖(A i j : ℂ) * z j‖ = (A *ᵥ y) i :=
    sum_norm_mul_eq_mulVec_norm (fun i j => (hA i j).le) z
  -- Equality in the triangle inequality at a fixed coordinate aligns the phases.
  set i₀ : ι := Classical.arbitrary ι with hi₀
  have hyeig₀ : (A *ᵥ y) i₀ = r * y i₀ := by
    simpa [Pi.smul_apply, smul_eq_mul] using congrFun hyeig i₀
  set S : ℂ := ∑ j, (A i₀ j : ℂ) * z j with hSdef
  have hnormS : ‖S‖ = r * y i₀ := by rw [hSdef, ← hcoord i₀, norm_mul, hnorm]
  have hSn : (0 : ℝ) < ‖S‖ := by rw [hnormS]; exact mul_pos hrpos (hypos i₀)
  have hzform := norm_row_sum_smul_eq hA
    (show ‖S‖ = ∑ j, ‖(A i₀ j : ℂ) * z j‖ by rw [hnormS, ← hyeig₀, hsumnorm i₀])
  -- `λ z = A z = r z` coordinatewise, then cancel a nonzero coordinate.
  have hfinal : lam * z i₀ = (r : ℂ) * z i₀ := by
    refine mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hSn.ne') ?_
    rw [hcoord i₀, ← hSdef,
      show (‖S‖ : ℂ) * ((r : ℂ) * z i₀) = (r : ℂ) * ((‖S‖ : ℂ) * z i₀) from by ring,
      hzform i₀, hnormS]
    push_cast
    ring
  have hz0 : z i₀ ≠ 0 := by rw [← norm_ne_zero_iff]; exact (hypos i₀).ne'
  exact mul_right_cancel₀ hz0 hfinal

/-! ### The compound matrix of a totally positive matrix

The reality half of `\cite[Cor.~5.5]{Pinkus2010}` applies Perron–Frobenius to
each compound `∧^r A`.  With the compound built in `TotallyNonneg` and the Perron
root built above, that step is now available; what the argument additionally
needs, and what is still missing, is **simplicity and strict dominance** of the
Perron root, plus the identification of the spectrum of `∧^r A` with the `r`-fold
products of the eigenvalues of `A`. -/

/-- **The compound of a totally positive matrix has a Perron root.**  Its entries
are the `r × r` minors, all strictly positive, so `exists_perron_eigenvector`
applies verbatim.  This is the step of the reality argument that Perron–Frobenius
was needed for. -/
theorem exists_perron_compound {n r : ℕ} (hrn : r ≤ n) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : MinorsPos r A) :
    0 < perronRoot (compound r A) ∧ ∃ x : increasingSelections r n → ℝ,
      (∀ f, 0 < x f) ∧ x ∈ stdSimplex ℝ (increasingSelections r n) ∧
      compound r A *ᵥ x = perronRoot (compound r A) • x :=
  haveI := increasingSelections_nonempty hrn
  exists_perron_eigenvector (compound r A) fun f g => hA f.1 g.1 f.2 g.2


/-! ### Axiom footprint -/

/-- info: 'Shields.norm_le_perronRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms norm_le_perronRoot

/-- info: 'Shields.perron_eigenvector_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms perron_eigenvector_unique

/-- info: 'Shields.eq_perronRoot_of_norm_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eq_perronRoot_of_norm_eq

end Shields
