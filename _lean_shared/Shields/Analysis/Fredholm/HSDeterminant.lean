/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Shields.Analysis.Matrix.HadamardDeterminant

/-!
# The Fredholm determinant of a kernel with a summable envelope

For a kernel `C : ι → κ → ℂ` on linearly ordered index types, the *minor* on a pair of
equinumerous finite index sets is the determinant of the submatrix listed in increasing
order, and

\[
  \det(\mathrm{Id}+CC^{\mathsf T}) = \sum_{S,T} (\det C[S,T])^{2}
\]

is the Cauchy--Binet expansion, taken here as the definition of `Shields.fredholmDet`.
On a finite index set this is a theorem rather than a definition; the point of the
present file is that the same series converges, and is continuous in `C`, on an infinite
index set, under a product envelope

\[
  |C_{ij}| \le a_i^{2}b_j^{2},\qquad \sum_i a_i^{2}<\infty,\ \sum_j b_j^{2}<\infty .
\]

## Main results

* `Shields.norm_minorDet_le_prod` — the envelope bound on a single minor.  Hadamard's
  inequality is applied twice, once along rows and once along columns, and the two are
  combined by taking a geometric mean: the row bound alone carries no dependence on the
  column set and so is not summable over it.
* `Shields.summable_minorDet_sq` — absolute convergence of the expansion.
* `Shields.tendsto_fredholmDet` — **continuity**.  A sequence of kernels converging
  entrywise under one fixed envelope has convergent Fredholm determinants.  This is the
  statement that a trace-norm formulation would be used for, proved here by dominated
  convergence against the envelope rather than through a Schatten norm.
* `Shields.fredholmDet_eq_sum_of_support` — a kernel supported on a finite rectangle has
  the finite Cauchy--Binet sum for its Fredholm determinant.

## Implementation notes

The envelope is stated with the squares `a_i^2 b_j^2` rather than with a bare product
`a_i b_j` because the geometric mean of the two Hadamard bounds halves the exponent: it
is the square root of the envelope that ends up multiplied over the index sets, and
writing the hypothesis this way keeps the conclusion free of square roots.

## Papers depending on this file

* `growing-rank-edrei` — the collective limit of the excitation determinant.
-/

open Finset Matrix Filter Topology

namespace Shields

variable {ι κ : Type*} [LinearOrder ι] [LinearOrder κ]

/-! ### Minors on a pair of finite index sets -/

/-- The minor of a kernel on a pair of equinumerous finite index sets, both listed in
increasing order; zero when the cardinalities differ. -/
noncomputable def minorDet (C : ι → κ → ℂ) (S : Finset ι) (T : Finset κ) : ℂ :=
  if h : T.card = S.card then
    (Matrix.of fun x y : Fin S.card =>
      C (S.orderEmbOfFin rfl x) (T.orderEmbOfFin h y)).det
  else 0

theorem minorDet_of_card_ne {C : ι → κ → ℂ} {S : Finset ι} {T : Finset κ}
    (h : T.card ≠ S.card) : minorDet C S T = 0 := dif_neg h

@[simp] theorem minorDet_empty (C : ι → κ → ℂ) :
    minorDet C (∅ : Finset ι) (∅ : Finset κ) = 1 := by
  rw [minorDet, dif_pos (by simp)]
  haveI : IsEmpty (Fin (∅ : Finset ι).card) := by
    simp only [Finset.card_empty]; exact Fin.isEmpty'
  exact Matrix.det_isEmpty

/-- A product over the increasing enumeration of a finite set is a product over the set. -/
theorem prod_orderEmbOfFin {M : Type*} [CommMonoid M] (S : Finset ι) {r : ℕ}
    (h : S.card = r) (f : ι → M) :
    ∏ x : Fin r, f (S.orderEmbOfFin h x) = ∏ i ∈ S, f i := by
  rw [← Finset.prod_coe_sort S f]
  refine Fintype.prod_equiv (S.orderIsoOfFin h).toEquiv _ _ fun x => ?_
  simp [Finset.coe_orderIsoOfFin_apply]

/-- A sum over the increasing enumeration of a finite set is a sum over the set. -/
theorem sum_orderEmbOfFin {M : Type*} [AddCommMonoid M] (S : Finset ι) {r : ℕ}
    (h : S.card = r) (f : ι → M) :
    ∑ x : Fin r, f (S.orderEmbOfFin h x) = ∑ i ∈ S, f i := by
  rw [← Finset.sum_coe_sort S f]
  refine Fintype.sum_equiv (S.orderIsoOfFin h).toEquiv _ _ fun x => ?_
  simp [Finset.coe_orderIsoOfFin_apply]

/-- Hadamard's inequality along the rows of a minor. -/
theorem normSq_minorDet_le_rows (C : ι → κ → ℂ) (S : Finset ι) (T : Finset κ) :
    ‖minorDet C S T‖ ^ 2 ≤ ∏ i ∈ S, ∑ j ∈ T, ‖C i j‖ ^ 2 := by
  by_cases hcard : T.card = S.card
  · rw [minorDet, dif_pos hcard]
    refine (Shields.normSq_det_le_prod_row_energy _).trans (le_of_eq ?_)
    rw [← prod_orderEmbOfFin S rfl (fun i => ∑ j ∈ T, ‖C i j‖ ^ 2)]
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [← sum_orderEmbOfFin T hcard (fun j => ‖C (S.orderEmbOfFin rfl x) j‖ ^ 2)]
    rfl
  · rw [minorDet_of_card_ne hcard]
    simpa using Finset.prod_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity

/-- Hadamard's inequality along the columns of a minor. -/
theorem normSq_minorDet_le_cols (C : ι → κ → ℂ) (S : Finset ι) (T : Finset κ) :
    ‖minorDet C S T‖ ^ 2 ≤ ∏ j ∈ T, ∑ i ∈ S, ‖C i j‖ ^ 2 := by
  by_cases hcard : T.card = S.card
  · rw [minorDet, dif_pos hcard]
    refine (Shields.normSq_det_le_prod_col_energy _).trans (le_of_eq ?_)
    rw [← prod_orderEmbOfFin T hcard (fun j => ∑ i ∈ S, ‖C i j‖ ^ 2)]
    refine Finset.prod_congr rfl fun y _ => ?_
    rw [← sum_orderEmbOfFin S rfl (fun i => ‖C i (T.orderEmbOfFin hcard y)‖ ^ 2)]
    rfl
  · rw [minorDet_of_card_ne hcard]
    simpa using Finset.prod_nonneg fun j _ => Finset.sum_nonneg fun i _ => by positivity

/-! ### The envelope bound -/

/-- **The envelope bound on a minor.**  Under `|C_{ij}| ≤ a_i^2 b_j^2` the minor on
`S × T` is at most `∏_S (c a) ∏_T b`, where `c` absorbs the two full sums.  Hadamard
along rows gives a bound independent of `T` and along columns one independent of `S`;
their geometric mean is what decays in both index sets at once. -/
theorem norm_minorDet_le_prod (C : ι → κ → ℂ) {a : ι → ℝ} {b : κ → ℝ} {A B c : ℝ}
    (ha0 : ∀ i, 0 ≤ a i) (hb0 : ∀ j, 0 ≤ b j) (hc0 : 0 ≤ c)
    (hC : ∀ i j, ‖C i j‖ ≤ (a i) ^ 2 * (b j) ^ 2)
    (hA : ∀ S' : Finset ι, ∑ i ∈ S', (a i) ^ 4 ≤ A)
    (hB : ∀ T' : Finset κ, ∑ j ∈ T', (b j) ^ 4 ≤ B)
    (hc : A * B ≤ c ^ 4) (S : Finset ι) (T : Finset κ) :
    ‖minorDet C S T‖ ≤ (∏ i ∈ S, (c * a i)) * ∏ j ∈ T, b j := by
  have hA0 : 0 ≤ A := le_trans (by simp) (hA ∅)
  have hB0 : 0 ≤ B := le_trans (by simp) (hB ∅)
  have hYnn : 0 ≤ (∏ i ∈ S, (c * a i)) * ∏ j ∈ T, b j :=
    mul_nonneg (Finset.prod_nonneg fun i _ => mul_nonneg hc0 (ha0 i))
      (Finset.prod_nonneg fun j _ => hb0 j)
  by_cases hcard : T.card = S.card
  · -- the row bound
    have hrow : ‖minorDet C S T‖ ^ 2 ≤ (∏ i ∈ S, (a i) ^ 4) * B ^ S.card := by
      refine (normSq_minorDet_le_rows C S T).trans ?_
      have hstep : ∀ i ∈ S, (∑ j ∈ T, ‖C i j‖ ^ 2) ≤ (a i) ^ 4 * B := by
        intro i _
        have h1 : (∑ j ∈ T, ‖C i j‖ ^ 2) ≤ ∑ j ∈ T, (a i) ^ 4 * (b j) ^ 4 := by
          refine Finset.sum_le_sum fun j _ => ?_
          have h2 := hC i j
          have h3 : (0 : ℝ) ≤ ‖C i j‖ := norm_nonneg _
          calc ‖C i j‖ ^ 2 ≤ ((a i) ^ 2 * (b j) ^ 2) ^ 2 := by
                exact pow_le_pow_left₀ h3 h2 2
            _ = (a i) ^ 4 * (b j) ^ 4 := by ring
        refine h1.trans ?_
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (hB T) (by positivity)
      calc (∏ i ∈ S, ∑ j ∈ T, ‖C i j‖ ^ 2) ≤ ∏ i ∈ S, ((a i) ^ 4 * B) :=
            Finset.prod_le_prod (fun i _ => Finset.sum_nonneg fun j _ => by positivity) hstep
        _ = (∏ i ∈ S, (a i) ^ 4) * B ^ S.card := by
            rw [Finset.prod_mul_distrib, Finset.prod_const]
    -- the column bound
    have hcol : ‖minorDet C S T‖ ^ 2 ≤ (∏ j ∈ T, (b j) ^ 4) * A ^ T.card := by
      refine (normSq_minorDet_le_cols C S T).trans ?_
      have hstep : ∀ j ∈ T, (∑ i ∈ S, ‖C i j‖ ^ 2) ≤ (b j) ^ 4 * A := by
        intro j _
        have h1 : (∑ i ∈ S, ‖C i j‖ ^ 2) ≤ ∑ i ∈ S, (b j) ^ 4 * (a i) ^ 4 := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h2 := hC i j
          have h3 : (0 : ℝ) ≤ ‖C i j‖ := norm_nonneg _
          calc ‖C i j‖ ^ 2 ≤ ((a i) ^ 2 * (b j) ^ 2) ^ 2 := pow_le_pow_left₀ h3 h2 2
            _ = (b j) ^ 4 * (a i) ^ 4 := by ring
        refine h1.trans ?_
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (hA S) (by positivity)
      calc (∏ j ∈ T, ∑ i ∈ S, ‖C i j‖ ^ 2) ≤ ∏ j ∈ T, ((b j) ^ 4 * A) :=
            Finset.prod_le_prod (fun j _ => Finset.sum_nonneg fun i _ => by positivity) hstep
        _ = (∏ j ∈ T, (b j) ^ 4) * A ^ T.card := by
            rw [Finset.prod_mul_distrib, Finset.prod_const]
    -- combine
    have hprodS : (0 : ℝ) ≤ ∏ i ∈ S, (a i) ^ 4 :=
      Finset.prod_nonneg fun i _ => by positivity
    have hprodT : (0 : ℝ) ≤ ∏ j ∈ T, (b j) ^ 4 :=
      Finset.prod_nonneg fun j _ => by positivity
    have hfour : ‖minorDet C S T‖ ^ 4
        ≤ ((∏ i ∈ S, (a i) ^ 4) * (∏ j ∈ T, (b j) ^ 4)) * (A * B) ^ S.card := by
      have h := mul_le_mul hrow hcol (by positivity) (by positivity)
      calc ‖minorDet C S T‖ ^ 4
          = ‖minorDet C S T‖ ^ 2 * ‖minorDet C S T‖ ^ 2 := by ring
        _ ≤ ((∏ i ∈ S, (a i) ^ 4) * B ^ S.card)
              * ((∏ j ∈ T, (b j) ^ 4) * A ^ T.card) := h
        _ = ((∏ i ∈ S, (a i) ^ 4) * (∏ j ∈ T, (b j) ^ 4)) * (A * B) ^ S.card := by
            rw [hcard, mul_pow]; ring
    have hYpow : ((∏ i ∈ S, (c * a i)) * ∏ j ∈ T, b j) ^ 4
        = ((∏ i ∈ S, (a i) ^ 4) * (∏ j ∈ T, (b j) ^ 4)) * (c ^ 4) ^ S.card := by
      have e1 : (∏ i ∈ S, (c * a i)) ^ 4 = (c ^ 4) ^ S.card * ∏ i ∈ S, (a i) ^ 4 := by
        rw [← Finset.prod_pow]
        simp only [mul_pow]
        rw [Finset.prod_mul_distrib, Finset.prod_const]
      have e2 : (∏ j ∈ T, b j) ^ 4 = ∏ j ∈ T, (b j) ^ 4 := (Finset.prod_pow _ _ _).symm
      rw [mul_pow, e1, e2]
      ring
    have hstep : ‖minorDet C S T‖ ^ 4 ≤ ((∏ i ∈ S, (c * a i)) * ∏ j ∈ T, b j) ^ 4 := by
      rw [hYpow]
      refine hfour.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      exact pow_le_pow_left₀ (by positivity) hc _
    exact le_of_pow_le_pow_left₀ (by norm_num) hYnn hstep
  · rw [minorDet_of_card_ne hcard]
    simpa using hYnn

/-! ### The Fredholm determinant -/

/-- The Fredholm determinant `det(Id + C Cᵀ)` of a kernel, as the Cauchy--Binet series
over pairs of finite index sets. -/
noncomputable def fredholmDet (C : ι → κ → ℂ) : ℂ :=
  ∑' p : Finset ι × Finset κ, (minorDet C p.1 p.2) ^ 2

/-- The envelope majorant of the Cauchy--Binet series. -/
noncomputable def envMajorant (a : ι → ℝ) (b : κ → ℝ) (c : ℝ)
    (p : Finset ι × Finset κ) : ℝ :=
  (∏ i ∈ p.1, (c * a i) ^ 2) * ∏ j ∈ p.2, (b j) ^ 2

omit [LinearOrder ι] [LinearOrder κ] in
theorem summable_envMajorant {a : ι → ℝ} {b : κ → ℝ} {c : ℝ}
    (ha : Summable fun i => (c * a i) ^ 2) (hb : Summable fun j => (b j) ^ 2) :
    Summable (envMajorant a b c) := by
  have h1 : Summable fun S : Finset ι => ∏ i ∈ S, (c * a i) ^ 2 :=
    summable_finsetProd_of_summable_nonneg (fun i => by positivity) ha
  have h2 : Summable fun T : Finset κ => ∏ j ∈ T, (b j) ^ 2 :=
    summable_finsetProd_of_summable_nonneg (fun j => by positivity) hb
  exact h1.mul_of_nonneg h2 (fun S => Finset.prod_nonneg fun i _ => by positivity)
    (fun T => Finset.prod_nonneg fun j _ => by positivity)

/-- The Cauchy--Binet series is dominated termwise by the envelope majorant. -/
theorem norm_minorDet_sq_le_envMajorant (C : ι → κ → ℂ) {a : ι → ℝ} {b : κ → ℝ}
    {A B c : ℝ} (ha0 : ∀ i, 0 ≤ a i) (hb0 : ∀ j, 0 ≤ b j) (hc0 : 0 ≤ c)
    (hC : ∀ i j, ‖C i j‖ ≤ (a i) ^ 2 * (b j) ^ 2)
    (hA : ∀ S' : Finset ι, ∑ i ∈ S', (a i) ^ 4 ≤ A)
    (hB : ∀ T' : Finset κ, ∑ j ∈ T', (b j) ^ 4 ≤ B)
    (hc : A * B ≤ c ^ 4) (p : Finset ι × Finset κ) :
    ‖(minorDet C p.1 p.2) ^ 2‖ ≤ envMajorant a b c p := by
  have h := norm_minorDet_le_prod C ha0 hb0 hc0 hC hA hB hc p.1 p.2
  rw [norm_pow, envMajorant]
  calc ‖minorDet C p.1 p.2‖ ^ 2
      ≤ ((∏ i ∈ p.1, (c * a i)) * ∏ j ∈ p.2, b j) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = (∏ i ∈ p.1, (c * a i) ^ 2) * ∏ j ∈ p.2, (b j) ^ 2 := by
        rw [mul_pow, Finset.prod_pow, Finset.prod_pow]

/-- **Absolute convergence of the Cauchy--Binet expansion** under a summable envelope. -/
theorem summable_minorDet_sq (C : ι → κ → ℂ) {a : ι → ℝ} {b : κ → ℝ} {A B c : ℝ}
    (ha0 : ∀ i, 0 ≤ a i) (hb0 : ∀ j, 0 ≤ b j) (hc0 : 0 ≤ c)
    (ha : Summable fun i => (c * a i) ^ 2) (hb : Summable fun j => (b j) ^ 2)
    (hC : ∀ i j, ‖C i j‖ ≤ (a i) ^ 2 * (b j) ^ 2)
    (hA : ∀ S' : Finset ι, ∑ i ∈ S', (a i) ^ 4 ≤ A)
    (hB : ∀ T' : Finset κ, ∑ j ∈ T', (b j) ^ 4 ≤ B)
    (hc : A * B ≤ c ^ 4) :
    Summable fun p : Finset ι × Finset κ => (minorDet C p.1 p.2) ^ 2 :=
  (summable_envMajorant ha hb).of_norm_bounded
    (norm_minorDet_sq_le_envMajorant C ha0 hb0 hc0 hC hA hB hc)

/-! ### Continuity -/

/-- A minor is continuous in the kernel: it is a polynomial in finitely many entries. -/
theorem tendsto_minorDet {α : Type*} {l : Filter α} (F : α → ι → κ → ℂ) (C : ι → κ → ℂ)
    (hlim : ∀ i j, Tendsto (fun n => F n i j) l (𝓝 (C i j)))
    (S : Finset ι) (T : Finset κ) :
    Tendsto (fun n => minorDet (F n) S T) l (𝓝 (minorDet C S T)) := by
  by_cases hcard : T.card = S.card
  · simp only [minorDet, dif_pos hcard]
    have hentries : Tendsto
        (fun n => (Matrix.of fun x y : Fin S.card =>
          F n (S.orderEmbOfFin rfl x) (T.orderEmbOfFin hcard y))) l
        (𝓝 (Matrix.of fun x y : Fin S.card =>
          C (S.orderEmbOfFin rfl x) (T.orderEmbOfFin hcard y))) := by
      have h : Tendsto (fun n => fun x y : Fin S.card =>
          F n (S.orderEmbOfFin rfl x) (T.orderEmbOfFin hcard y)) l
          (𝓝 (fun x y : Fin S.card =>
            C (S.orderEmbOfFin rfl x) (T.orderEmbOfFin hcard y))) :=
        tendsto_pi_nhds.mpr fun x => tendsto_pi_nhds.mpr fun y => hlim _ _
      exact h
    exact (Continuous.matrix_det continuous_id).continuousAt.tendsto.comp hentries
  · simp only [minorDet_of_card_ne hcard]
    exact tendsto_const_nhds

/-- **Continuity of the Fredholm determinant.**  Kernels converging entrywise under one
fixed summable envelope have convergent Fredholm determinants.  This is what a
trace-norm formulation of the limit would be used for; the envelope replaces the
Schatten norm, and dominated convergence replaces the continuity of `det(Id + ·)` on the
trace class. -/
theorem tendsto_fredholmDet {α : Type*} {l : Filter α} (F : α → ι → κ → ℂ)
    (C : ι → κ → ℂ) {a : ι → ℝ} {b : κ → ℝ} {A B c : ℝ}
    (ha0 : ∀ i, 0 ≤ a i) (hb0 : ∀ j, 0 ≤ b j) (hc0 : 0 ≤ c)
    (ha : Summable fun i => (c * a i) ^ 2) (hb : Summable fun j => (b j) ^ 2)
    (hF : ∀ n i j, ‖F n i j‖ ≤ (a i) ^ 2 * (b j) ^ 2)
    (hA : ∀ S' : Finset ι, ∑ i ∈ S', (a i) ^ 4 ≤ A)
    (hB : ∀ T' : Finset κ, ∑ j ∈ T', (b j) ^ 4 ≤ B)
    (hc : A * B ≤ c ^ 4)
    (hlim : ∀ i j, Tendsto (fun n => F n i j) l (𝓝 (C i j))) :
    Tendsto (fun n => fredholmDet (F n)) l (𝓝 (fredholmDet C)) := by
  refine tendsto_tsum_of_dominated_convergence
    (summable_envMajorant ha hb) (fun p => ?_) (Filter.Eventually.of_forall ?_)
  · exact ((tendsto_minorDet F C hlim p.1 p.2).pow 2)
  · intro n p
    exact norm_minorDet_sq_le_envMajorant (F n) ha0 hb0 hc0 (hF n) hA hB hc p

/-! ### Kernels of finite support -/

/-- A minor vanishes as soon as one of its rows lies outside the support. -/
theorem minorDet_eq_zero_of_row {C : ι → κ → ℂ} {S : Finset ι} {T : Finset κ} {i : ι}
    (hi : i ∈ S) (hrow : ∀ j, C i j = 0) : minorDet C S T = 0 := by
  by_cases hcard : T.card = S.card
  · rw [minorDet, dif_pos hcard]
    obtain ⟨x, hx⟩ : ∃ x : Fin S.card, S.orderEmbOfFin rfl x = i := by
      have hrange := Finset.range_orderEmbOfFin S (rfl : S.card = S.card)
      have hmem : i ∈ Set.range (S.orderEmbOfFin rfl) := by
        rw [hrange]; exact_mod_cast hi
      exact hmem
    refine Matrix.det_eq_zero_of_row_eq_zero x ?_
    intro y
    simp only [Matrix.of_apply, hx]
    exact hrow _
  · exact minorDet_of_card_ne hcard

/-- A minor vanishes as soon as one of its columns lies outside the support. -/
theorem minorDet_eq_zero_of_col {C : ι → κ → ℂ} {S : Finset ι} {T : Finset κ} {j : κ}
    (hj : j ∈ T) (hcol : ∀ i, C i j = 0) : minorDet C S T = 0 := by
  by_cases hcard : T.card = S.card
  · rw [minorDet, dif_pos hcard]
    obtain ⟨y, hy⟩ : ∃ y : Fin S.card, T.orderEmbOfFin hcard y = j := by
      have hrange := Finset.range_orderEmbOfFin T hcard
      have : j ∈ Set.range (T.orderEmbOfFin hcard) := by rw [hrange]; exact_mod_cast hj
      exact this
    refine Matrix.det_eq_zero_of_column_eq_zero y ?_
    intro x
    simp only [Matrix.of_apply, hy]
    exact hcol _
  · exact minorDet_of_card_ne hcard

/-- **A kernel supported on a finite rectangle has a finite Cauchy--Binet expansion.** -/
theorem fredholmDet_eq_sum_of_support (C : ι → κ → ℂ) (P : Finset ι) (Q : Finset κ)
    (hrow : ∀ i, i ∉ P → ∀ j, C i j = 0) (hcol : ∀ j, j ∉ Q → ∀ i, C i j = 0) :
    fredholmDet C = ∑ p ∈ P.powerset ×ˢ Q.powerset, (minorDet C p.1 p.2) ^ 2 := by
  refine tsum_eq_sum ?_
  intro p hp
  rw [Finset.mem_product] at hp
  have : ¬ (p.1 ∈ P.powerset ∧ p.2 ∈ Q.powerset) := by tauto
  rw [not_and_or] at this
  rcases this with h | h
  · rw [Finset.mem_powerset] at h
    obtain ⟨i, hiS, hiP⟩ := Finset.not_subset.mp h
    rw [minorDet_eq_zero_of_row hiS (hrow i hiP), zero_pow (by norm_num)]
  · rw [Finset.mem_powerset] at h
    obtain ⟨j, hjT, hjQ⟩ := Finset.not_subset.mp h
    rw [minorDet_eq_zero_of_col hjT (hcol j hjQ), zero_pow (by norm_num)]

/-! ### Transport along order embeddings -/

/-- The minor of a kernel on two sets of a common known cardinality. -/
theorem minorDet_eq_det {r : ℕ} (C : ι → κ → ℂ) {S : Finset ι} {T : Finset κ}
    (hS : S.card = r) (hT : T.card = r) :
    minorDet C S T
      = (Matrix.of fun x y : Fin r =>
          C (S.orderEmbOfFin hS x) (T.orderEmbOfFin hT y)).det := by
  subst hS
  rw [minorDet, dif_pos hT]

/-- The increasing enumeration of an image under an order embedding is the composite. -/
theorem orderEmbOfFin_map {ι' : Type*} [LinearOrder ι'] (e : ι ↪o ι') (S : Finset ι)
    {r : ℕ} (h : S.card = r) (h' : (S.map e.toEmbedding).card = r) (x : Fin r) :
    (S.map e.toEmbedding).orderEmbOfFin h' x = e (S.orderEmbOfFin h x) := by
  have := Finset.orderEmbOfFin_unique (s := S.map e.toEmbedding) h'
    (f := fun y => e (S.orderEmbOfFin h y))
    (fun y => Finset.mem_map_of_mem _ (Finset.orderEmbOfFin_mem S h y))
    (e.strictMono.comp (S.orderEmbOfFin h).strictMono)
  exact (congrFun this x).symm

/-- **Minors transport along order embeddings.**  Restricting a kernel to the images of
two order embeddings and taking a minor there is the same as taking the minor of the
pulled-back kernel. -/
theorem minorDet_map {ι' κ' : Type*} [LinearOrder ι'] [LinearOrder κ']
    (e : ι ↪o ι') (f : κ ↪o κ') (C : ι' → κ' → ℂ) (S : Finset ι) (T : Finset κ) :
    minorDet C (S.map e.toEmbedding) (T.map f.toEmbedding)
      = minorDet (fun i j => C (e i) (f j)) S T := by
  by_cases hcard : T.card = S.card
  · have hS' : (S.map e.toEmbedding).card = S.card := by simp
    have hT' : (T.map f.toEmbedding).card = S.card := by simp [hcard]
    rw [minorDet_eq_det C hS' hT', minorDet_eq_det (fun i j => C (e i) (f j)) rfl hcard]
    congr 1
    ext x y
    rw [Matrix.of_apply, Matrix.of_apply, orderEmbOfFin_map e S rfl hS',
      orderEmbOfFin_map f T hcard hT']
  · rw [minorDet_of_card_ne (by simpa using hcard), minorDet_of_card_ne hcard]

/-! ### The envelope in summable form -/

omit [LinearOrder ι] in
/-- Partial sums of the squares of a summable nonnegative family are bounded by the
square of its sum. -/
theorem sum_sq_le_tsum_sq {f : ι → ℝ} (hf0 : ∀ i, 0 ≤ f i) (hf : Summable f)
    (S : Finset ι) : ∑ i ∈ S, (f i) ^ 2 ≤ (∑' i, f i) ^ 2 := by
  have hT0 : (0 : ℝ) ≤ ∑' i, f i := tsum_nonneg hf0
  have hle : ∀ i, f i ≤ ∑' j, f j := fun i => by
    simpa using Summable.sum_le_tsum {i} (fun j _ => hf0 j) hf
  calc ∑ i ∈ S, (f i) ^ 2 ≤ ∑ i ∈ S, (∑' j, f j) * f i := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [sq]
        exact mul_le_mul_of_nonneg_right (hle i) (hf0 i)
    _ = (∑' j, f j) * ∑ i ∈ S, f i := by rw [Finset.mul_sum]
    _ ≤ (∑' j, f j) * (∑' j, f j) :=
        mul_le_mul_of_nonneg_left (Summable.sum_le_tsum S (fun i _ => hf0 i) hf) hT0
    _ = (∑' i, f i) ^ 2 := (sq _).symm

/-- **Continuity of the Fredholm determinant under a summable product envelope.**  This
is the form the hypothesis takes in practice: one summable envelope on the rows and one
on the columns, holding for every kernel of the family.  It is the statement of
`Shields.tendsto_fredholmDet` with the four bookkeeping parameters discharged. -/
theorem tendsto_fredholmDet_of_summable_envelope {α : Type*} {l : Filter α}
    (F : α → ι → κ → ℂ) (C : ι → κ → ℂ) {e : ι → ℝ} {g : κ → ℝ}
    (he0 : ∀ i, 0 ≤ e i) (hg0 : ∀ j, 0 ≤ g j) (he : Summable e) (hg : Summable g)
    (hF : ∀ n i j, ‖F n i j‖ ≤ e i * g j)
    (hlim : ∀ i j, Tendsto (fun n => F n i j) l (𝓝 (C i j))) :
    Tendsto (fun n => fredholmDet (F n)) l (𝓝 (fredholmDet C)) := by
  set a : ι → ℝ := fun i => Real.sqrt (e i) with ha_def
  set b : κ → ℝ := fun j => Real.sqrt (g j) with hb_def
  have hasq : ∀ i, (a i) ^ 2 = e i := fun i => Real.sq_sqrt (he0 i)
  have hbsq : ∀ j, (b j) ^ 2 = g j := fun j => Real.sq_sqrt (hg0 j)
  set c : ℝ := Real.sqrt ((∑' i, e i) * ∑' j, g j) with hc_def
  have hE0 : 0 ≤ ∑' i, e i := tsum_nonneg he0
  have hG0 : 0 ≤ ∑' j, g j := tsum_nonneg hg0
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hcsq : c ^ 2 = (∑' i, e i) * ∑' j, g j :=
    Real.sq_sqrt (mul_nonneg hE0 hG0)
  refine tendsto_fredholmDet F C (a := a) (b := b)
    (A := (∑' i, e i) ^ 2) (B := (∑' j, g j) ^ 2) (c := c)
    (fun i => Real.sqrt_nonneg _) (fun j => Real.sqrt_nonneg _) hc0 ?_ ?_ ?_ ?_ ?_ ?_ hlim
  · simp only [mul_pow, hasq]
    exact he.mul_left _
  · simp only [hbsq]
    exact hg
  · intro n i j
    rw [hasq, hbsq]
    exact hF n i j
  · intro S'
    have : ∀ i, (a i) ^ 4 = (e i) ^ 2 := fun i => by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hasq]
    simp only [this]
    exact sum_sq_le_tsum_sq he0 he S'
  · intro T'
    have : ∀ j, (b j) ^ 4 = (g j) ^ 2 := fun j => by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hbsq]
    simp only [this]
    exact sum_sq_le_tsum_sq hg0 hg T'
  · rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hcsq]
    exact le_of_eq (by ring)

end Shields
